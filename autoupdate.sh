#!/bin/sh
# rsh auto-update: incremental git pull + rebuild of the rsh binary.
#
# - sources live in RSH_SRC (~/src/rsh by default) and are NEVER re-downloaded:
#   `git fetch` + `git merge --ff-only` fetches only the deltas between runs;
# - the binary is rebuilt only if the repo actually advanced
#   (there are new commits after the merge);
# - on Termux/Alpine set RSH_BIN to the binary path rsh actually uses.
#
# Schedule it with cron/systemd (see etc/rsh-autoupdate.* in the repo) or run
# manually: `sh autoupdate.sh`.
set -u

BRANCH=${RSH_BRANCH:-main}
GIT_URL=${RSH_GIT_URL:-https://github.com/rival-afk/rsh}
SRC=${RSH_SRC:-"$HOME/src/rsh"}
BIN=${RSH_BIN:-"$HOME/bin/rsh"}
LOG="${RSH_LOG:-/dev/null}"

alog() {
	printf '%s rsh-autoupdate: %s\n' "$(date '+%Y-%m-%d %H:%M:%S')" "$*" >>"$LOG"
}

if git -C "$SRC" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
	# existing checkout: fetch only the delta (single branch, shallow-safe)
	git -C "$SRC" fetch --quiet origin "$BRANCH" 2>>"$LOG" || {
		alog "git fetch failed (offline?)"
		exit 1
	}
	BASE_HEAD=$(git -C "$SRC" rev-parse HEAD)
	if git -C "$SRC" merge --quiet --ff-only "origin/$BRANCH" 2>>"$LOG"; then
		NEW_HEAD=$(git -C "$SRC" rev-parse HEAD)
		if [ "$BASE_HEAD" = "$NEW_HEAD" ]; then
			alog "up to date at $NEW_HEAD"
			exit 0
		fi
		alog "updated $BASE_HEAD -> $NEW_HEAD ($(git -C "$SRC" rev-list --count "$BASE_HEAD..$NEW_HEAD") new commits)"
	else
		alog "ff-merge failed (local changes? branch diverged)"
		exit 1
	fi
else
	if ! git clone --quiet --single-branch --branch "$BRANCH" "$GIT_URL" "$SRC" 2>>"$LOG"; then
		alog "git clone failed"
		exit 1
	fi
	alog "cloned $GIT_URL -> $SRC"
fi

command -v go >/dev/null 2>&1 || {
	alog "go not found, skipped build"
	exit 0
}
cd "$SRC" || exit 1
# rebuild unless the binary already exists and is not older than the checkout
# (covers fresh clones and any case where the binary was not rebuilt)
if [ -f "$BIN" ]; then
	BIN_T=$(stat -c %Y "$BIN" 2>/dev/null || echo 0)
	SRC_T=$(git log -1 --format=%ct)
	if [ "$BIN_T" -ge "$SRC_T" ]; then
		alog "up to date at $NEW_HEAD (binary fresh)"
		exit 0
	fi
fi
if go build -o "$BIN.new" . 2>>"$LOG"; then
	mv "$BIN.new" "$BIN" 2>>"$LOG" || exit 1
	chmod +x "$BIN" 2>>"$LOG"
	alog "built $BIN from $(git rev-parse --short HEAD)"
else
	alog "go build failed, keeping previous binary"
	rm -f "$BIN.new"
	exit 1
fi
