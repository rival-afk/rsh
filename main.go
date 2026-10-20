package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/ed25519"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/cookiejar"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"time"

	"golang.org/x/crypto/ssh"
	"golang.org/x/sys/unix"
)

// isExecutable reports whether path is a regular executable file.
// Uses os.Stat (stat syscall) to avoid faccessat2, which Android seccomp blocks.
func isExecutable(path string) bool {
	fi, err := os.Stat(path)
	if err != nil {
		return false
	}
	return !fi.IsDir() && fi.Mode()&0o111 != 0
}

// lookPath finds an executable by name in PATH without using the access(2)
// family of syscalls (blocked by Android's seccomp, causing SIGSYS).
func lookPath(file string) (string, error) {
	if strings.Contains(file, "/") {
		if isExecutable(file) {
			return file, nil
		}
		return "", fmt.Errorf("%s: not executable", file)
	}
	for _, dir := range filepath.SplitList(os.Getenv("PATH")) {
		if dir == "" {
			dir = "."
		}
		p := filepath.Join(dir, file)
		if isExecutable(p) {
			return p, nil
		}
	}
	return "", fmt.Errorf("%s: not found in PATH", file)
}

func sshKeygenPath() string {
	if p, err := lookPath("ssh-keygen"); err == nil {
		return p
	}
	return "ssh-keygen"
}

const defaultAuthURL = "https://auth.rival-afk.com"

type authKey struct {
	priv ed25519.PrivateKey
	pub  string // normalized "ssh-ed25519 AAAA..."
}

type authResp struct {
	Token string   `json:"token"`
	Role  string   `json:"role"`
	Hosts []string `json:"hosts"`
	Exp   int64    `json:"exp"`
}

type sshKeyResp struct {
	Host       string `json:"host"`
	User       string `json:"user"`
	Addr       string `json:"addr"`
	Port       int    `json:"port"`
	PrivateKey string `json:"private_key"`
	Jump       *struct {
		Addr       string `json:"addr"`
		Port       int    `json:"port"`
		User       string `json:"user"`
		PrivateKey string `json:"private_key"`
	} `json:"jump"`
}

func rshDir() string {
	h, _ := os.UserHomeDir()
	return filepath.Join(h, ".rsh")
}

func authURL() string {
	if v := os.Getenv("RSH_AUTH_URL"); v != "" {
		return v
	}
	b, err := os.ReadFile(filepath.Join(rshDir(), "config.json"))
	if err == nil {
		var c struct {
			AuthURL string `json:"auth_url"`
		}
		if json.Unmarshal(b, &c) == nil && c.AuthURL != "" {
			return c.AuthURL
		}
	}
	return defaultAuthURL
}

type rshConfig struct {
	AuthURL  string            `json:"auth_url"`
	NetToken string            `json:"net_token"`
	WoL      map[string]string `json:"wol"`
}

func loadRshConfig() rshConfig {
	var c rshConfig
	b, err := os.ReadFile(filepath.Join(rshDir(), "config.json"))
	if err == nil {
		json.Unmarshal(b, &c)
	}
	return c
}

func netToken() string {
	if v := os.Getenv("RSH_NET_TOKEN"); v != "" {
		return v
	}
	return loadRshConfig().NetToken
}

// authClient is the shared HTTP client for auth-server calls. Its dialer
// rewrites the destination IP for hostnames found in ~/.rsh/hosts (hosts
// file format). This lets rsh reach https://auth.rival-afk.com on Android,
// where Go's pure (cgo-less) resolver cannot do DNS — while the TLS ServerName
// still comes from the URL, so the Let's Encrypt cert keeps validating.
var authClient = newAuthClient()

func newAuthClient() *http.Client {
	hm := hostMap()
	dialer := &net.Dialer{Timeout: 12 * time.Second}
	tr := &http.Transport{
		DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
			if host, port, err := net.SplitHostPort(addr); err == nil {
				if ip, ok := hm[host]; ok {
					addr = net.JoinHostPort(ip, port)
				}
			}
			return dialer.DialContext(ctx, network, addr)
		},
		TLSHandshakeTimeout: 12 * time.Second,
	}
	return &http.Client{Timeout: 20 * time.Second, Transport: tr}
}

// hostMap reads hostname->IP entries from an optional hosts-format file at
// ~/.rsh/hosts so auth.rival-afk.com resolves without a working system DNS.
func hostMap() map[string]string {
	m := map[string]string{}
	b, err := os.ReadFile(filepath.Join(rshDir(), "hosts"))
	if err != nil {
		return m
	}
	for _, line := range strings.Split(string(b), "\n") {
		line = strings.TrimSpace(strings.SplitN(line, "#", 2)[0])
		f := strings.Fields(line)
		if len(f) < 2 {
			continue
		}
		for _, name := range f[1:] {
			m[name] = f[0]
		}
	}
	return m
}

func normalizePubFromSSH(sp ssh.PublicKey) string {
	return strings.TrimSpace(string(ssh.MarshalAuthorizedKey(sp)))
}

func loadAuthKeys() ([]authKey, error) {
	dir := rshDir()
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil, fmt.Errorf("cannot read %s: %v (run `rsh keygen` first)", dir, err)
	}
	names := []string{}
	for _, e := range entries {
		if !e.IsDir() {
			names = append(names, e.Name())
		}
	}
	for _, pref := range []string{"id", "id_ed25519"} {
		for i, n := range names {
			if n == pref {
				names = append(names[:i], names[i+1:]...)
				names = append([]string{pref}, names...)
				break
			}
		}
	}
	var keys []authKey
	for _, n := range names {
		if strings.HasSuffix(n, ".pub") || n == "config.json" || n == "known_hosts" {
			continue
		}
		b, err := os.ReadFile(filepath.Join(dir, n))
		if err != nil {
			continue
		}
		raw, err := ssh.ParseRawPrivateKey(b)
		if err != nil {
			continue
		}
		var priv ed25519.PrivateKey
		switch t := raw.(type) {
		case ed25519.PrivateKey:
			priv = t
		case *ed25519.PrivateKey:
			priv = *t
		default:
			continue
		}
		sshPub, err := ssh.NewPublicKey(priv.Public().(ed25519.PublicKey))
		if err != nil {
			continue
		}
		keys = append(keys, authKey{priv: priv, pub: normalizePubFromSSH(sshPub)})
	}
	if len(keys) == 0 {
		return nil, fmt.Errorf("no usable ed25519 key found in %s (run `rsh keygen`)", dir)
	}
	return keys, nil
}

func doAuth(baseURL string, k authKey) (*authResp, error) {
	ts := time.Now().Unix()
	msg := fmt.Sprintf("rival-auth-v1|%s|%d", k.pub, ts)
	sig := ed25519.Sign(k.priv, []byte(msg))
	body, _ := json.Marshal(map[string]interface{}{
		"pubkey": k.pub,
		"ts":     ts,
		"sig":    hex.EncodeToString(sig),
	})
	resp, err := authClient.Post(baseURL+"/v1/auth", "application/json", bytes.NewReader(body))
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	b, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("auth failed (%d): %s", resp.StatusCode, strings.TrimSpace(string(b)))
	}
	var ar authResp
	if err := json.Unmarshal(b, &ar); err != nil {
		return nil, err
	}
	return &ar, nil
}

func authenticate() (*authResp, error) {
	keys, err := loadAuthKeys()
	if err != nil {
		return nil, err
	}
	base := authURL()
	var lastErr error
	for _, k := range keys {
		ar, err := doAuth(base, k)
		if err == nil {
			return ar, nil
		}
		lastErr = err
	}
	return nil, lastErr
}

func cmdKeygen() {
	dir := rshDir()
	os.MkdirAll(dir, 0o700)
	path := filepath.Join(dir, "id")
	if _, err := os.Stat(path); err == nil {
		fmt.Fprintf(os.Stderr, "already exists: %s\n", path)
		os.Exit(1)
	}
	cmd := exec.Command(sshKeygenPath(), "-t", "ed25519", "-N", "", "-C", "rsh-auth", "-f", path, "-q")
	if out, err := cmd.CombinedOutput(); err != nil {
		fmt.Fprintf(os.Stderr, "keygen: %v %s\n", err, string(out))
		os.Exit(1)
	}
	pub, _ := os.ReadFile(path + ".pub")
	fmt.Printf("generated %s\n", path)
	fmt.Printf("public key (register with `rsh admin add`):\n%s", string(pub))
}

func readPassword(prompt string) (string, error) {
	fmt.Fprint(os.Stderr, prompt)
	fd := int(os.Stdin.Fd())
	old, err := unix.IoctlGetTermios(fd, unix.TCGETS)
	if err != nil {
		r := bufio.NewReader(os.Stdin)
		l, _ := r.ReadString('\n')
		return strings.TrimSpace(l), nil
	}
	noecho := *old
	noecho.Lflag &^= unix.ECHO
	if err := unix.IoctlSetTermios(fd, unix.TCSETS, &noecho); err != nil {
		r := bufio.NewReader(os.Stdin)
		l, _ := r.ReadString('\n')
		return strings.TrimSpace(l), nil
	}
	defer unix.IoctlSetTermios(fd, unix.TCSETS, old)
	r := bufio.NewReader(os.Stdin)
	l, err := r.ReadString('\n')
	fmt.Fprintln(os.Stderr)
	return strings.TrimRight(l, "\r\n"), err
}

func webPost(c *http.Client, base, path, token string, payload interface{}) (int, []byte, error) {
	var rdr io.Reader
	if payload != nil {
		body, _ := json.Marshal(payload)
		rdr = bytes.NewReader(body)
	}
	req, err := http.NewRequest("POST", base+path, rdr)
	if err != nil {
		return 0, nil, err
	}
	if payload != nil {
		req.Header.Set("Content-Type", "application/json")
	}
	if token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
	}
	resp, err := c.Do(req)
	if err != nil {
		return 0, nil, err
	}
	defer resp.Body.Close()
	b, _ := io.ReadAll(resp.Body)
	return resp.StatusCode, b, nil
}

func cmdLogin() {
	cmdLoginFlow(false)
}

func cmdRegister() {
	cmdLoginFlow(true)
}

func cmdLoginFlow(reg bool) {
	base := authURL()
	jar, _ := cookiejar.New(nil)
	c := &http.Client{Timeout: 20 * time.Second, Transport: authClient.Transport, Jar: jar}
	fmt.Fprint(os.Stderr, "username: ")
	un, _ := bufio.NewReader(os.Stdin).ReadString('\n')
	un = strings.ToLower(strings.TrimSpace(un))
	pw, _ := readPassword("password: ")
	if un == "" || pw == "" {
		fmt.Fprintln(os.Stderr, "username and password required")
		os.Exit(1)
	}
	path := "/v1/web/passlogin"
	if reg {
		path = "/v1/web/register"
	}
	code, b, err := webPost(c, base, path, "", map[string]string{"username": un, "password": pw})
	if err != nil {
		fmt.Fprintf(os.Stderr, "login: %v\n", err)
		os.Exit(1)
	}
	var pr struct {
		Error   string `json:"error"`
		Message string `json:"message"`
		Token   string `json:"token"`
	}
	json.Unmarshal(b, &pr)
	if pr.Error != "" || code != 200 {
		fmt.Fprintf(os.Stderr, "%s (%d)\n", strings.TrimSpace(pr.Error), code)
		os.Exit(1)
	}
	if reg {
		fmt.Println(pr.Message)
		os.Exit(0)
	}
	fmt.Println("login ok, binding ~/.rsh key…")

	keys, err := loadAuthKeys()
	if err != nil {
		fmt.Fprintf(os.Stderr, "key: %v\n", err)
		os.Exit(1)
	}
	code, b, err = webPost(c, base, "/v1/web/bindnonce", pr.Token, nil)
	if err != nil || code != 200 {
		fmt.Fprintf(os.Stderr, "bindnonce: %v (%d) %s\n", err, code, strings.TrimSpace(string(b)))
		os.Exit(1)
	}
	var bn struct {
		Nonce string `json:"nonce"`
		Error string `json:"error"`
	}
	if err := json.Unmarshal(b, &bn); err != nil || bn.Error != "" || bn.Nonce == "" {
		fmt.Fprintf(os.Stderr, "bindnonce: %v %s\n", err, bn.Error)
		os.Exit(1)
	}
	msg := fmt.Sprintf("rival-web-v1|%s", bn.Nonce)
	sig := ed25519.Sign(keys[0].priv, []byte(msg))
	f := strings.Fields(keys[0].pub)
	pk := keys[0].pub
	if len(f) >= 2 {
		pk = f[0] + " " + f[1]
	}
	code, b, err = webPost(c, base, "/v1/web/bindkey", pr.Token, map[string]string{
		"pubkey": pk,
		"nonce":  bn.Nonce,
		"sig":    base64.StdEncoding.EncodeToString(sig),
	})
	if err != nil || code != 200 {
		fmt.Fprintf(os.Stderr, "bindkey: %v (%d) %s\n", err, code, strings.TrimSpace(string(b)))
		os.Exit(1)
	}
	var bk struct {
		Error   string `json:"error"`
		Message string `json:"message"`
	}
	json.Unmarshal(b, &bk)
	if bk.Error != "" {
		fmt.Fprintf(os.Stderr, "bindkey: %s\n", bk.Error)
		os.Exit(1)
	}
	fmt.Println("key bound: " + pk)
	if ar, err := authenticate(); err == nil {
		fmt.Printf("role: %s, hosts: %s\n", ar.Role, strings.Join(ar.Hosts, ", "))
	}
	fmt.Println("now run: rsh")
}

func isPrivileged(role string) bool {
	return role == "admin" || role == "owner"
}

func getJWT(base, needRole string) (string, error) {
	ar, err := authenticate()
	if err != nil {
		return "", err
	}
	if needRole == "admin" {
		needRole = "$privileged"
	}
	if needRole == "$privileged" && !isPrivileged(ar.Role) {
		return "", fmt.Errorf("this key has role %q, need admin/owner", ar.Role)
	}
	if needRole != "" && needRole != "$privileged" && ar.Role != needRole {
		return "", fmt.Errorf("this key has role %q, need %q", ar.Role, needRole)
	}
	return ar.Token, nil
}

func apiPost(base, path, token string, payload interface{}) (int, []byte, error) {
	body, _ := json.Marshal(payload)
	req, _ := http.NewRequest("POST", base+path, bytes.NewReader(body))
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer "+token)
	resp, err := authClient.Do(req)
	if err != nil {
		return 0, nil, err
	}
	defer resp.Body.Close()
	b, _ := io.ReadAll(resp.Body)
	return resp.StatusCode, b, nil
}

func apiDo(base, method, path, token string) (int, []byte, error) {
	req, _ := http.NewRequest(method, base+path, nil)
	req.Header.Set("Authorization", "Bearer "+token)
	resp, err := authClient.Do(req)
	if err != nil {
		return 0, nil, err
	}
	defer resp.Body.Close()
	b, _ := io.ReadAll(resp.Body)
	return resp.StatusCode, b, nil
}

func cmdAdminAdd(base string, args []string) {
	var pub, role, hosts, label string
	for i := 0; i < len(args); i++ {
		switch args[i] {
		case "--key":
			i++
			pub = args[i]
		case "--role":
			i++
			role = args[i]
		case "--hosts":
			i++
			hosts = args[i]
		case "--label":
			i++
			label = args[i]
		}
	}
	if pub == "" {
		b, _ := io.ReadAll(os.Stdin)
		pub = strings.TrimSpace(string(b))
	}
	if role == "" {
		role = "user"
	}
	token, err := getJWT(base, "admin")
	if err != nil {
		fmt.Fprintf(os.Stderr, "admin auth: %v\n", err)
		os.Exit(1)
	}
	payload := map[string]interface{}{
		"pubkey": strings.TrimSpace(pub),
		"role":   role,
		"label":  label,
	}
	if hosts != "" {
		payload["hosts"] = strings.Split(hosts, ",")
	}
	code, b, err := apiPost(base, "/v1/admin/keys", token, payload)
	if err != nil {
		fmt.Fprintf(os.Stderr, "request: %v\n", err)
		os.Exit(1)
	}
	if code != 200 {
		fmt.Fprintf(os.Stderr, "add failed (%d): %s\n", code, strings.TrimSpace(string(b)))
		os.Exit(1)
	}
	fmt.Printf("added: %s\n", strings.TrimSpace(string(b)))
}

func cmdAdminList(base string) {
	token, err := getJWT(base, "admin")
	if err != nil {
		fmt.Fprintf(os.Stderr, "admin auth: %v\n", err)
		os.Exit(1)
	}
	code, b, err := apiDo(base, "GET", "/v1/admin/keys", token)
	if err != nil {
		fmt.Fprintf(os.Stderr, "request: %v\n", err)
		os.Exit(1)
	}
	if code != 200 {
		fmt.Fprintf(os.Stderr, "list failed (%d): %s\n", code, strings.TrimSpace(string(b)))
		os.Exit(1)
	}
	var keys []struct {
		ID     string   `json:"id"`
		Pubkey string   `json:"pubkey"`
		Role   string   `json:"role"`
		Hosts  []string `json:"hosts"`
		Label  string   `json:"label"`
	}
	json.Unmarshal(b, &keys)
	fmt.Printf("%-10s %-6s %-20s %-15s %s\n", "ID", "ROLE", "LABEL", "HOSTS", "PUBKEY")
	for _, k := range keys {
		pk := k.Pubkey
		if parts := strings.Fields(pk); len(parts) >= 2 {
			pk = parts[1][:20] + "..."
		}
		fmt.Printf("%-10s %-6s %-20s %-15s %s\n", k.ID, k.Role, k.Label, strings.Join(k.Hosts, ","), pk)
	}
}

func cmdAdminRm(base string, args []string) {
	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, "usage: rsh admin rm <id>")
		os.Exit(1)
	}
	token, err := getJWT(base, "admin")
	if err != nil {
		fmt.Fprintf(os.Stderr, "admin auth: %v\n", err)
		os.Exit(1)
	}
	code, b, err := apiDo(base, "DELETE", "/v1/admin/keys/"+args[0], token)
	if err != nil {
		fmt.Fprintf(os.Stderr, "request: %v\n", err)
		os.Exit(1)
	}
	if code != 200 {
		fmt.Fprintf(os.Stderr, "rm failed (%d): %s\n", code, strings.TrimSpace(string(b)))
		os.Exit(1)
	}
	fmt.Printf("deleted %s\n", args[0])
}

func knownHostsFile() string {
	return filepath.Join(rshDir(), "known_hosts")
}

func ensureKeyFile(name, content string) (string, error) {
	dir := filepath.Join(rshDir(), "ssh")
	os.MkdirAll(dir, 0o700)
	p := filepath.Join(dir, name)
	if err := os.WriteFile(p, []byte(content), 0o600); err != nil {
		return "", err
	}
	return p, nil
}

func connect(base, target string) {
	ar, err := authenticate()
	if err != nil {
		fmt.Fprintf(os.Stderr, "auth: %v\n", err)
		os.Exit(1)
	}
	if !isPrivileged(ar.Role) {
		fmt.Fprintf(os.Stderr, "access denied: role %q cannot open SSH sessions\n", ar.Role)
		os.Exit(1)
	}

	var host string
	if target != "" {
		found := false
		for _, h := range ar.Hosts {
			if h == target {
				found = true
				break
			}
		}
		if !found {
			fmt.Fprintf(os.Stderr, "host %q not available for this key (allowed: %s)\n", target, strings.Join(ar.Hosts, ", "))
			os.Exit(1)
		}
		host = target
	} else {
		if len(ar.Hosts) == 0 {
			fmt.Fprintln(os.Stderr, "no hosts available")
			os.Exit(1)
		}
		fmt.Fprintln(os.Stderr, "available servers:")
		for i, h := range ar.Hosts {
			fmt.Fprintf(os.Stderr, "  %d) %s\n", i+1, h)
		}
		fmt.Fprint(os.Stderr, "select: ")
		var in string
		fmt.Scanln(&in)
		n, err := strconv.Atoi(strings.TrimSpace(in))
		if err != nil || n < 1 || n > len(ar.Hosts) {
			fmt.Fprintln(os.Stderr, "invalid selection")
			os.Exit(1)
		}
		host = ar.Hosts[n-1]
	}

	code, b, err := apiPost(base, "/v1/sshkey", ar.Token, map[string]string{"host": host})
	if err != nil {
		fmt.Fprintf(os.Stderr, "sshkey: %v\n", err)
		os.Exit(1)
	}
	if code != 200 {
		fmt.Fprintf(os.Stderr, "sshkey failed (%d): %s\n", code, strings.TrimSpace(string(b)))
		os.Exit(1)
	}
	var sk sshKeyResp
	if err := json.Unmarshal(b, &sk); err != nil {
		fmt.Fprintf(os.Stderr, "parse: %v\n", err)
		os.Exit(1)
	}

	targetKeyFile, err := ensureKeyFile(host, sk.PrivateKey)
	if err != nil {
		fmt.Fprintf(os.Stderr, "write key: %v\n", err)
		os.Exit(1)
	}

	kh := knownHostsFile()
	sshArgs := []string{
		"-i", targetKeyFile,
		"-o", "IdentitiesOnly=yes",
		"-o", "UserKnownHostsFile=" + kh,
		"-o", "StrictHostKeyChecking=accept-new",
		"-o", "ServerAliveInterval=30",
		"-o", "ServerAliveCountMax=3",
	}

	if sk.Jump != nil {
		jumpKeyFile, err := ensureKeyFile(host+"-jump", sk.Jump.PrivateKey)
		if err != nil {
			fmt.Fprintf(os.Stderr, "write jump key: %v\n", err)
			os.Exit(1)
		}
		proxy := fmt.Sprintf("ssh -i %s -o IdentitiesOnly=yes -o UserKnownHostsFile=%s -o StrictHostKeyChecking=accept-new -W %%h:%%p %s@%s -p %d",
			jumpKeyFile, kh, sk.Jump.User, sk.Jump.Addr, sk.Jump.Port)
		sshArgs = append(sshArgs, "-o", "ProxyCommand="+proxy)
	}

	sshArgs = append(sshArgs, "-p", strconv.Itoa(sk.Port), fmt.Sprintf("%s@%s", sk.User, sk.Addr))

	if os.Getenv("RSH_DUMP") == "1" {
		fmt.Fprintln(os.Stderr, "ssh "+strings.Join(sshArgs, " "))
		return
	}

	sshBin, err := lookPath("ssh")
	if err != nil {
		fmt.Fprintln(os.Stderr, "ssh not found in PATH")
		os.Exit(1)
	}
	argv := append([]string{"ssh"}, sshArgs...)
	syscall.Exec(sshBin, argv, os.Environ())
}

// sshRun mirrors connect() but runs a single remote command (non-interactive),
// reusing the same auth + provisioned key + jump (VPS tunnel) path.
func sshRun(base, target, remoteCmd string) {
	ar, err := authenticate()
	if err != nil {
		fmt.Fprintf(os.Stderr, "auth: %v\n", err)
		os.Exit(1)
	}
	if !isPrivileged(ar.Role) {
		fmt.Fprintf(os.Stderr, "access denied: role %q cannot run commands\n", ar.Role)
		os.Exit(1)
	}
	host := target
	found := false
	for _, h := range ar.Hosts {
		if h == target {
			found = true
			break
		}
	}
	if !found {
		fmt.Fprintf(os.Stderr, "host %q not available (allowed: %s)\n", target, strings.Join(ar.Hosts, ", "))
		os.Exit(1)
	}
	code, b, err := apiPost(base, "/v1/sshkey", ar.Token, map[string]string{"host": host})
	if err != nil || code != 200 {
		fmt.Fprintf(os.Stderr, "sshkey failed: %v %s\n", err, strings.TrimSpace(string(b)))
		os.Exit(1)
	}
	var sk sshKeyResp
	if err := json.Unmarshal(b, &sk); err != nil {
		fmt.Fprintf(os.Stderr, "parse: %v\n", err)
		os.Exit(1)
	}
	targetKeyFile, err := ensureKeyFile(host, sk.PrivateKey)
	if err != nil {
		fmt.Fprintf(os.Stderr, "write key: %v\n", err)
		os.Exit(1)
	}
	kh := knownHostsFile()
	args := []string{
		"-i", targetKeyFile,
		"-o", "IdentitiesOnly=yes",
		"-o", "UserKnownHostsFile=" + kh,
		"-o", "StrictHostKeyChecking=accept-new",
		"-o", "ConnectTimeout=15",
		"-o", "ServerAliveInterval=20",
		"-o", "ServerAliveCountMax=3",
	}
	if sk.Jump != nil {
		jumpKeyFile, err := ensureKeyFile(host+"-jump", sk.Jump.PrivateKey)
		if err != nil {
			fmt.Fprintf(os.Stderr, "write jump key: %v\n", err)
			os.Exit(1)
		}
		proxy := fmt.Sprintf("ssh -i %s -o IdentitiesOnly=yes -o UserKnownHostsFile=%s -o StrictHostKeyChecking=accept-new -W %%h:%%p %s@%s -p %d",
			jumpKeyFile, kh, sk.Jump.User, sk.Jump.Addr, sk.Jump.Port)
		args = append(args, "-o", "ProxyCommand="+proxy)
	}
	args = append(args, "-p", strconv.Itoa(sk.Port), fmt.Sprintf("%s@%s", sk.User, sk.Addr))
	args = append(args, remoteCmd)
	sshBin, err := lookPath("ssh")
	if err != nil {
		fmt.Fprintln(os.Stderr, "ssh not found in PATH")
		os.Exit(1)
	}
	out, err := exec.Command(sshBin, args...).CombinedOutput()
	fmt.Print(string(out))
	if err != nil {
		os.Exit(1)
	}
}

// parseMAC accepts "fc:9d:05:23:95:fa" and returns 6 bytes.
func parseMAC(s string) ([]byte, error) {
	s = strings.ReplaceAll(s, "-", ":")
	parts := strings.Split(s, ":")
	if len(parts) != 6 {
		return nil, fmt.Errorf("bad MAC %q", s)
	}
	b := make([]byte, 6)
	for i, p := range parts {
		v, err := strconv.ParseUint(p, 16, 8)
		if err != nil {
			return nil, fmt.Errorf("bad MAC octet %q", p)
		}
		b[i] = byte(v)
	}
	return b, nil
}

// sendWOL sends Wake-on-LAN magic packets (6x 0xFF + 16x MAC) to broadcasts.
func sendWOL(mac string, port int) error {
	m, err := parseMAC(mac)
	if err != nil {
		return err
	}
	pkt := append(bytes.Repeat([]byte{0xFF}, 6), bytes.Repeat(m, 16)...)
	// limited + subnet broadcasts
	targets := []string{"255.255.255.255"}
	for _, ip := range localIPv4s() {
		if b := subnetBroadcast(ip); b != nil {
			targets = append(targets, b.String())
		}
	}
	seen := map[string]bool{}
	for _, t := range targets {
		if seen[t] {
			continue
		}
		seen[t] = true
		conn, err := net.Dial("udp", net.JoinHostPort(t, strconv.Itoa(port)))
		if err != nil {
			continue
		}
		conn.Write(pkt)
		conn.Close()
	}
	return nil
}

func wolMAC(arg string) string {
	// explicit MAC if it has 5 separators and hex
	if _, err := parseMAC(arg); err == nil {
		return arg
	}
	if m := loadRshConfig().WoL[arg]; m != "" {
		return m
	}
	return ""
}

func cmdWOL(args []string) {
	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, "usage: rsh wol <mac|label> [--port 9]")
		os.Exit(1)
	}
	port := 9
	for i := 1; i < len(args); i++ {
		if args[i] == "--port" && i+1 < len(args) {
			i++
			port, _ = strconv.Atoi(args[i])
		}
	}
	mac := wolMAC(args[0])
	if mac == "" {
		fmt.Fprintf(os.Stderr, "wol: unknown mac/label %q (configure in ~/.rsh/config.json \"wol\":{\"%s\":\"aa:bb:..\"})\n", args[0], args[0])
		os.Exit(1)
	}
	if err := sendWOL(mac, port); err != nil {
		fmt.Fprintf(os.Stderr, "wol: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("sent WoL magic packet to %s (port %d)\n", mac, port)
}

func cmdPC(base string, args []string) {
	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, "usage: rsh pc <on|off|reboot|status|exec ...>")
		os.Exit(1)
	}
	switch args[0] {
	case "on":
		mac := loadRshConfig().WoL["pc"]
		if mac == "" {
			fmt.Fprintln(os.Stderr, "rsh pc on: no WoL MAC configured for 'pc' (see ~/.rsh/config.json \"wol\":{\"pc\":\"...\"})")
			os.Exit(1)
		}
		if err := sendWOL(mac, 9); err != nil {
			fmt.Fprintf(os.Stderr, "wol: %v\n", err)
			os.Exit(1)
		}
		fmt.Printf("wake-on-LAN sent to pc (%s)\n", mac)
	case "off":
		sshRun(base, "pc", `systemctl poweroff 2>/dev/null || poweroff`)
	case "reboot":
		sshRun(base, "pc", `systemctl reboot 2>/dev/null || reboot`)
	case "status":
		sshRun(base, "pc", `echo ON; hostname; uptime -p 2>/dev/null || uptime; if command -v systemctl >/dev/null 2>&1; then systemctl is-active sshd; else rc-service sshd status; fi; true`)
	case "exec":
		if len(args) < 2 {
			fmt.Fprintln(os.Stderr, "usage: rsh pc exec <command>")
			os.Exit(1)
		}
		sshRun(base, "pc", strings.Join(args[1:], " "))
	default:
		fmt.Fprintln(os.Stderr, "usage: rsh pc <on|off|reboot|status|exec ...>")
		os.Exit(1)
	}
}

const (
	netMagicDiscover = "RIVAL-DISCOVER v1"
	netMagicHello    = "RIVAL-HELLO"
	netDefaultPort   = 47800
)

func isPrivateIPv4(ip net.IP) bool {
	ip4 := ip.To4()
	if ip4 == nil {
		return false
	}
	return ip4[0] == 10 ||
		(ip4[0] == 172 && ip4[1] >= 16 && ip4[1] <= 31) ||
		(ip4[0] == 192 && ip4[1] == 168)
}

// netIface is a parsed network interface (from net.Interfaces or ifconfig).
type netIface struct {
	name  string
	ip    net.IP
	mask  net.IPMask
	bcast net.IP
	up    bool
	loop  bool
}

// ifaces returns network interfaces. It first tries net.Interfaces(); on
// Android that fails with "netlinkrib: permission denied", so it falls back
// to parsing `ifconfig` output (which still works unprivileged).
func ifaces() []netIface {
	var out []netIface
	if ifs, err := net.Interfaces(); err == nil {
		for _, iface := range ifs {
			addrs, _ := iface.Addrs()
			for _, a := range addrs {
				ipnet, ok := a.(*net.IPNet)
				if !ok || ipnet.IP == nil {
					continue
				}
				ip4 := ipnet.IP.To4()
				if ip4 == nil {
					continue
				}
				mask := ipnet.Mask
				var bcast net.IP
				if len(mask) == net.IPv4len {
					bcast = make(net.IP, net.IPv4len)
					for i := 0; i < net.IPv4len; i++ {
						bcast[i] = ip4[i] | ^mask[i]
					}
				}
				out = append(out, netIface{
					name: iface.Name, ip: ip4, mask: mask, bcast: bcast,
					up: iface.Flags&net.FlagUp != 0, loop: iface.Flags&net.FlagLoopback != 0,
				})
			}
		}
		if len(out) > 0 {
			return out
		}
	}
	return ifacesFromIfconfig()
}

// ifacesFromIfconfig parses `ifconfig` output. Resolves the binary via the
// custom lookPath so exec.Command does not trigger faccessat2 (Android
// seccomp -> SIGSYS).
func ifacesFromIfconfig() []netIface {
	bin, err := lookPath("ifconfig")
	if err != nil {
		return nil
	}
	b, err := exec.Command(bin).Output()
	if err != nil {
		return nil
	}
	var out []netIface
	var cur *netIface
	for _, line := range strings.Split(string(b), "\n") {
		trimmed := strings.TrimSpace(line)
		// New interface header: "wlan0: flags=...". Indented lines belong to it.
		if !strings.HasPrefix(line, " ") && !strings.HasPrefix(line, "\t") && strings.Contains(trimmed, ":") {
			name := strings.SplitN(trimmed, ":", 2)[0]
			fields := strings.Fields(trimmed)
			up := false
			loop := false
			for _, f := range fields {
				if strings.Contains(f, "UP") {
					up = true
				}
				if strings.Contains(f, "LOOPBACK") {
					loop = true
				}
			}
			out = append(out, netIface{name: name, up: up, loop: loop})
			cur = &out[len(out)-1]
			continue
		}
		if cur == nil {
			continue
		}
		// "inet 192.168.0.128  netmask 255.255.255.0  broadcast 192.168.0.255"
		if strings.Contains(trimmed, "inet ") && !strings.Contains(trimmed, "inet6") {
			f := strings.Fields(trimmed)
			for i := 0; i < len(f); i++ {
				switch f[i] {
				case "inet":
					if i+1 < len(f) {
						if ip4 := net.ParseIP(f[i+1]).To4(); ip4 != nil {
							cur.ip = ip4
						}
					}
				case "netmask":
					if i+1 < len(f) {
						if m := net.ParseIP(f[i+1]).To4(); m != nil {
							cur.mask = net.IPMask(m)
						}
					}
				case "broadcast":
					if i+1 < len(f) {
						if b := net.ParseIP(f[i+1]).To4(); b != nil {
							cur.bcast = b
						}
					}
				}
			}
		}
	}
	return out
}

// localIPv4s returns all non-loopback private IPv4 addresses, preferring
// 192.168/16 then 172.16/12 then 10/8 (WiFi/LAN over cellular).
func localIPv4s() []net.IP {
	var pref192, pref172, pref10 []net.IP
	for _, iface := range ifaces() {
		if !iface.up || iface.loop || iface.ip == nil || !isPrivateIPv4(iface.ip) {
			continue
		}
		switch {
		case iface.ip[0] == 192:
			pref192 = append(pref192, iface.ip)
		case iface.ip[0] == 172:
			pref172 = append(pref172, iface.ip)
		case iface.ip[0] == 10:
			pref10 = append(pref10, iface.ip)
		}
	}
	return append(append(pref192, pref172...), pref10...)
}

func detectLocalIP() net.IP {
	ips := localIPv4s()
	if len(ips) == 0 {
		return nil
	}
	return ips[0]
}

// subnetBroadcast returns the IPv4 broadcast address for an interface IP,
// falling back to the limited broadcast (255.255.255.255).
func subnetBroadcast(ip net.IP) net.IP {
	for _, iface := range ifaces() {
		if iface.ip != nil && iface.ip.Equal(ip) && iface.bcast != nil {
			return iface.bcast
		}
	}
	return net.IPv4bcast
}

func netServe(label string, port int) error {
	if label == "" {
		label = "device"
	}
	addr := &net.UDPAddr{IP: net.IPv4zero, Port: port}
	conn, err := net.ListenUDP("udp", addr)
	if err != nil {
		return err
	}
	defer conn.Close()
	fmt.Fprintf(os.Stderr, "rival-net responder listening on udp/%d as %q\n", port, label)
	buf := make([]byte, 512)
	for {
		n, raddr, err := conn.ReadFromUDP(buf)
		if err != nil {
			continue
		}
		msg := strings.TrimSpace(string(buf[:n]))
		if msg != netMagicDiscover {
			continue
		}
		resp := netMagicHello + " " + label
		conn.WriteToUDP([]byte(resp), raddr)
	}
}

func netDiscover(port int, timeout time.Duration) (map[string]string, error) {
	conn, err := net.ListenUDP("udp", &net.UDPAddr{IP: net.IPv4zero, Port: 0})
	if err != nil {
		return nil, err
	}
	defer conn.Close()
	// broadcast to each local subnet + limited broadcast
	targets := []net.IP{net.IPv4bcast}
	for _, ip := range localIPv4s() {
		if b := subnetBroadcast(ip); b != nil {
			targets = append(targets, b)
		}
	}
	for _, t := range targets {
		conn.WriteToUDP([]byte(netMagicDiscover), &net.UDPAddr{IP: t, Port: port})
	}
	found := map[string]string{}
	deadline := time.Now().Add(timeout)
	conn.SetReadDeadline(deadline)
	buf := make([]byte, 512)
	for {
		n, raddr, err := conn.ReadFromUDP(buf)
		if err != nil {
			break // timeout
		}
		msg := strings.TrimSpace(string(buf[:n]))
		if !strings.HasPrefix(msg, netMagicHello) {
			continue
		}
		label := strings.TrimSpace(strings.TrimPrefix(msg, netMagicHello))
		if label == "" {
			label = "device"
		}
		if ip4 := raddr.IP.To4(); ip4 != nil {
			found[label] = ip4.String()
		}
	}
	return found, nil
}

func netTokenHTTP(method, url string, body []byte) (int, []byte, error) {
	var rdr io.Reader
	if body != nil {
		rdr = bytes.NewReader(body)
	}
	req, _ := http.NewRequest(method, url, rdr)
	req.Header.Set("Authorization", "Bearer "+netToken())
	if body != nil {
		req.Header.Set("Content-Type", "application/json")
	}
	resp, err := authClient.Do(req)
	if err != nil {
		return 0, nil, err
	}
	defer resp.Body.Close()
	b, _ := io.ReadAll(resp.Body)
	return resp.StatusCode, b, nil
}

func cmdNet(args []string) {
	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, "usage: rsh net <ip|serve|discover|announce|find> ...")
		os.Exit(1)
	}
	base := authURL()
	switch args[0] {
	case "ip":
		ip := detectLocalIP()
		if ip == nil {
			fmt.Fprintln(os.Stderr, "no private IPv4 found")
			os.Exit(1)
		}
		fmt.Println(ip.String())
	case "serve":
		label := ""
		port := netDefaultPort
		for i := 1; i < len(args); i++ {
			switch args[i] {
			case "--label":
				i++
				label = args[i]
			case "--port":
				i++
				port, _ = strconv.Atoi(args[i])
			}
		}
		if label == "" {
			if h, err := os.Hostname(); err == nil {
				label = h
			}
		}
		if err := netServe(label, port); err != nil {
			fmt.Fprintf(os.Stderr, "serve: %v\n", err)
			os.Exit(1)
		}
	case "discover":
		port := netDefaultPort
		timeout := 3 * time.Second
		for i := 1; i < len(args); i++ {
			switch args[i] {
			case "--port":
				i++
				port, _ = strconv.Atoi(args[i])
			case "--timeout":
				i++
				ms, _ := strconv.Atoi(args[i])
				timeout = time.Duration(ms) * time.Second
			}
		}
		found, err := netDiscover(port, timeout)
		if err != nil {
			fmt.Fprintf(os.Stderr, "discover: %v\n", err)
			os.Exit(1)
		}
		json.NewEncoder(os.Stdout).Encode(found)
	case "announce":
		label := ""
		for i := 1; i < len(args); i++ {
			if args[i] == "--label" {
				i++
				label = args[i]
			}
		}
		if label == "" {
			if h, err := os.Hostname(); err == nil {
				label = h
			} else {
				label = "device"
			}
		}
		ip := detectLocalIP()
		if ip == nil {
			fmt.Fprintln(os.Stderr, "no private IPv4 to announce")
			os.Exit(1)
		}
		peers, _ := netDiscover(netDefaultPort, 2*time.Second)
		payload, _ := json.Marshal(map[string]interface{}{
			"label": label,
			"ip":    ip.String(),
			"peers": peers,
		})
		code, b, err := netTokenHTTP("POST", base+"/v1/net/announce", payload)
		if err != nil {
			fmt.Fprintf(os.Stderr, "announce: %v\n", err)
			os.Exit(1)
		}
		if code != 200 {
			fmt.Fprintf(os.Stderr, "announce failed (%d): %s\n", code, strings.TrimSpace(string(b)))
			os.Exit(1)
		}
		fmt.Printf("announced %s=%s (peers: %d)\n", label, ip.String(), len(peers))
	case "find":
		if len(args) < 2 {
			fmt.Fprintln(os.Stderr, "usage: rsh net find <label>")
			os.Exit(1)
		}
		ip := findPeer(base, args[1])
		if ip == "" {
			fmt.Fprintf(os.Stderr, "find: unknown peer %s\n", args[1])
			os.Exit(1)
		}
		fmt.Println(ip)
	case "resolve":
		if len(args) < 2 {
			fmt.Fprintln(os.Stderr, "usage: rsh net resolve <label> [--timeout S]")
			os.Exit(1)
		}
		label := args[1]
		timeout := 3 * time.Second
		for i := 2; i < len(args); i++ {
			if args[i] == "--timeout" {
				i++
				ms, _ := strconv.Atoi(args[i])
				timeout = time.Duration(ms) * time.Second
			}
		}
		// 1. UDP broadcast discovery (same LAN, no auth needed)
		if found, err := netDiscover(netDefaultPort, timeout); err == nil {
			if ip := found[label]; ip != "" {
				fmt.Println(ip)
				return
			}
		}
		// 2. query auth (last announced IP)
		if ip := findPeer(base, label); ip != "" {
			fmt.Println(ip)
			return
		}
		// 3. local override file ~/.rsh/<label>_ip
		if b, err := os.ReadFile(filepath.Join(rshDir(), label+"_ip")); err == nil {
			if ip := strings.TrimSpace(string(b)); ip != "" {
				fmt.Println(ip)
				return
			}
		}
		fmt.Fprintf(os.Stderr, "resolve: cannot determine %s ip\n", label)
		os.Exit(1)
	default:
		fmt.Fprintln(os.Stderr, "usage: rsh net <ip|serve|discover|announce|find|resolve> ...")
		os.Exit(1)
	}
}

func findPeer(base, label string) string {
	code, b, err := netTokenHTTP("GET", base+"/v1/net/peer/"+label, nil)
	if err != nil || code != 200 {
		return ""
	}
	var peer struct {
		IP string `json:"ip"`
	}
	json.Unmarshal(b, &peer)
	return peer.IP
}

func usage() {
	fmt.Fprintf(os.Stderr, `rsh - rival ssh gateway

usage:
  rsh                     interactive server picker + connect
  rsh <host>              connect to a host (vps/phone/pc)
  rsh keygen              generate auth keypair in ~/.rsh/
  rsh login               password login (auth.rival-afk.com) + bind ~/.rsh key
  rsh register            create account on auth server (waits for admin approval)
  rsh admin add           register a pubkey (needs admin key)
      --key "<pubkey>" --role user|admin [--hosts vps,phone,pc] [--label name]
  rsh admin list          list registered keys
  rsh admin rm <id>       remove a key
  rsh net ip              print this device's LAN IPv4
  rsh net serve           run UDP broadcast responder (--label, --port)
  rsh net discover        broadcast-probe the LAN, print {label:ip} (--port, --timeout)
  rsh net announce        report own LAN IP (+discovered peers) to auth (--label)
  rsh net find <label>    query auth for a peer's current LAN IP
  rsh net resolve <label> print a peer's IP: discover -> find -> override file
  rsh wol <mac|label>  send Wake-on-LAN magic packet (--port 9)
  rsh pc on            send WoL to the PC (label 'pc' in config.wol)
  rsh pc off|reboot    power off / reboot the PC (via ssh)
  rsh pc status        print PC online? / uptime / sshd via ssh
  rsh pc exec <cmd>    run a command on the PC via ssh

auth endpoint: %s (override: RSH_AUTH_URL or ~/.rsh/config.json auth_url)
`, authURL())
}

func main() {
	base := authURL()
	args := os.Args[1:]
	if len(args) == 0 {
		connect(base, "")
		return
	}
	switch args[0] {
	case "keygen":
		cmdKeygen()
	case "login":
		cmdLogin()
	case "register":
		cmdRegister()
	case "admin":
		if len(args) < 2 {
			usage()
			os.Exit(1)
		}
		switch args[1] {
		case "add":
			cmdAdminAdd(base, args[2:])
		case "list":
			cmdAdminList(base)
		case "rm":
			cmdAdminRm(base, args[2:])
		default:
			usage()
			os.Exit(1)
		}
	case "net":
		cmdNet(args[1:])
	case "wol":
		cmdWOL(args[1:])
	case "pc":
		cmdPC(base, args[1:])
	case "help", "-h", "--help":
		usage()
	default:
		connect(base, args[0])
	}
}
