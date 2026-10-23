#!/bin/sh
# pc-recover: восстановление ssh-доступа на пк (zenoku-alpine) одной командой.
#
# Запуск ЛОКАЛЬНО на пк (root):
#   curl -fsSL https://raw.githubusercontent.com/rival-afk/rsh/main/tools/pc-recover.sh | sh
#
# Что делает: см. встроенный akfix (append-only restore authorized_keys,
# PerSourcePenalties no, sshd -t + restart) + полная диагностика (лог и TG-алерт).
set -u

AK=/root/.ssh/authorized_keys
AD=/etc/ssh/sshd_config
LF=/root/.rsh/pc-recover.log

mkdir -p /root/.rsh && chmod 700 /root/.rsh
{
echo "=== pc-recover $(date '+%F %T') ==="
echo "os: $(uname -a 2>&1)"
echo "rsh bin: $(ls -l /root/bin/rsh 2>&1)"
echo "rsh ver: $(/root/bin/rsh version 2>/dev/null || echo n/a)"
echo "go: $(command -v go 2>/dev/null || echo absent)"
echo "autoupdate log tail: $(tail -3 /var/log/rsh-autoupdate.log 2>/dev/null | tr '\n' '|')"
echo "cron: $(crontab -l 2>&1 | tr '\n' '|')"
echo "sshd ver: $(sshd -V 2>&1 || ssh -V 2>&1)"
echo "--- ak BEFORE ---"
cat "$AK" 2>&1
} >>"$LF" 2>&1

# --- сам akfix: восстановление ключей (append-only!), без замены файла ---
NL0=$(grep -c . $AK 2>/dev/null || echo 0)
ap() { grep -qF "$2" $AK 2>/dev/null || echo "$1" >> $AK; }
ap 'ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIACs6CpCYKJtZ+ARIFS7Cc0xLSUgFDRl59rPYmyDEGtt provisioner@vps-rot-20261015-223913' 'AAAAIACs6CpCYKJtZ+ARIFS7Cc0xLSUgFDRl59rPYmyDEGtt'
ap 'ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIEv8LiQVSBDnetQJXrCxY8b3iuOavxPymHVj40XvRvP4 zenoku-vps' 'AAAAIEv8LiQVSBDnetQJXrCxY8b3iuOavxPymHVj40XvRvP4'
ap 'ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIPeCZHCh4VdVC531gy6MMK1ZzPWwKOkmIooAO9CXg2FG rival' 'AAAAIPeCZHCh4VdVC531gy6MMK1ZzPWwKOkmIooAO9CXg2FG'
ap 'ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIIjFoX1U0mbdhyo82rJl6AtubfysUsHPRX7pW9LzKiu2 alpine' 'AAAAIIjFoX1U0mbdhyo82rJl6AtubfysUsHPRX7pW9LzKiu2'
chmod 700 /root /root/.ssh 2>/dev/null
chmod 600 $AK 2>/dev/null

AEF=$(sshd -T 2>/dev/null | grep -i '^authorizedkeysfile ' | head -1)
AEFN=$(echo "$AEF" | sed 's/\.ssh\/authorized_keys2//; s/ *$//' | tr 'A-Z' 'a-z')
PSP=$(sshd -T 2>/dev/null | grep -i '^persourcepenalties' | head -1 | cut -c1-40)
CFG=$(grep -nE '^[[:space:]]*(Match|AuthorizedKeysFile|Include|PerSourcePenalt|StrictModes)' $AD 2>/dev/null | tr '\n' '|')
HP=$(ls -ld /root /root/.ssh $AK 2>&1 | awk '{print $1, $3":"$4, $NF}' | tr '\n' '|')
CHG=

BF=$( [ -f "$AD" ] && cp -f $AD $AD.akfixbak && echo 1 || echo 0 )
if [ -n "$AEFN" ] && [ "$AEFN" != "authorizedkeysfile .ssh/authorized_keys" ]; then
  if ! grep -qi '^AuthorizedKeysFile .ssh/authorized_keys' $AD; then
    printf 'AuthorizedKeysFile .ssh/authorized_keys\n' | cat - $AD > $AD.new 2>>$LF && mv $AD.new $AD && chmod 644 $AD && CHG=$CHG'akf-prepended;'
  fi
fi
if ! grep -qi '^PerSourcePenalties' $AD 2>/dev/null && [ "$BF" = 1 ]; then
  printf 'PerSourcePenalties no\n' >> $AD && CHG=$CHG'psp-off;'
fi
if [ "$(sshd -t 2>>$LF && echo ok)" != ok ]; then
  [ "$BF" = 1 ] && { cp -f $AD.akfixbak $AD; CHG=$CHG'config-reverted;'; }
  echo "AKFIX-BRANCH: sshd config invalid, reverted" >> "$LF"
fi

rc-service sshd restart >/dev/null 2>>$LF || service sshd restart >/dev/null 2>>$LF || systemctl restart sshd >/dev/null 2>&1 || true
sleep 2
LN=$(netstat -ltn 2>/dev/null | awk '$4 ~ /:22$/ && $NF ~ /LISTEN/ {print $4}' | tr '\n' ' ')
NL1=$(grep -c . $AK 2>/dev/null || echo 0)
TLL=$(tail -60 /var/log/messages 2>/dev/null | grep -a sshd | tail -2 | cut -c1-100 | tr '\n' '|')

{
echo "--- result ---"
echo "lines $NL0->$NL1 akf=[$AEFN] psp=[$PSP] chg=$CHG cfg=$CFG"
echo "dir=$HP listen=[$LN] sshdlog=[$TLL]"
echo "sshd -t: $(sshd -t 2>&1 && echo OK)"
} >>"$LF" 2>&1

echo "lines $NL0->$NL1 akf=[$AEFN] psp=[$PSP] chg=$CHG listen=[$LN]"
echo "полный лог: $LF"

# алерт кратким итогом в TG (через штатный релей пк)
msg="AKFIX(pc-recover): lines $NL0->$NL1 akf=[$AEFN] psp=[$PSP] chg=$CHG listen=[$LN]"
/usr/local/bin/zen-alert.sh "$msg" >/dev/null 2>&1 || echo "(алерт в TG не ушёл — см. лог)"
