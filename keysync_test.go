package main

import "testing"

func TestKeysyncRoundTrp(t *testing.T) {
	sec := make([]byte, 32)
	for i := range sec {
		sec[i] = byte(i)
	}
	pubs := []string{
		"ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIEv8LiQVSBDnetQJXrCxY8b3iuOavxPymHVj40XvRvP4 zenoku-vps",
		"ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIIjFoX1U0mbdhyo82rJl6AtubfysUsHPRX7pW9LzKiu2 alpine",
	}
	blob, win, err := keysyncEncrypt(sec, "pc", pubs)
	if err != nil {
		t.Fatalf("encrypt: %v", err)
	}
	if win <= 0 {
		t.Fatalf("win: %d", win)
	}
	p, err := keysyncDecrypt(sec, blob)
	if err != nil {
		t.Fatalf("decrypt: %v", err)
	}
	if p.Host != "pc" || len(p.Pubs) != 2 || p.Pubs[1] != pubs[1] {
		t.Fatalf("payload mismatch: %+v", p)
	}
	// чужой секрет не раскрывает блоб
	other := make([]byte, 32)
	if _, err := keysyncDecrypt(other, blob); err == nil {
		t.Fatal("чужой секрет открыл блоб?!")
	}
	// apply: добавляет недостающее, не дублт
	n, err := keysyncApply(pubs)
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	_ = n
}
