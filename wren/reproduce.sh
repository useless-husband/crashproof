#!/usr/bin/env bash
# Reproduces the one observable protocol difference between crashproof and wren-os:
# after a clean commit, crashproof's on-disk header is empty, wren-os's still names the
# committed transaction (it omits the final barrier and relies on a checksum at mount).
# Both recover correctly; see docs/report.md for the assessment. Read-only use of wren-os.
set -euo pipefail
cd "$(dirname "$0")/.."
CP=.lake/build/bin/crashproof
WR=build/wren/wrenlog
[ -x "$CP" ] || { echo "build crashproof first (make build)"; exit 2; }
[ -x "$WR" ] || bash wren/build.sh
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
printf 'begin\nput 0 1\nput 1 2\ncommit\n' > "$d/wl"

echo "== after a single clean commit, before any recovery =="
"$CP" format "$d/cp.img" --log 8  --data 4 >/dev/null; "$CP" run "$d/cp.img" "$d/wl" >/dev/null
"$WR" format "$d/wr.img" --log 64 --data 4 >/dev/null; "$WR" run "$d/wr.img" "$d/wl" >/dev/null
echo "crashproof header: $("$CP" dump "$d/cp.img" | head -1)"
echo "wren-os    header: $("$WR" dump "$d/wr.img" | head -1)"

echo
echo "== both still recover to the committed state (header empty afterwards) =="
for p in "$CP:$d/cp.img" "$WR:$d/wr.img"; do
  bin=${p%%:*}; img=${p#*:}; "$bin" recover "$img" >/dev/null
  echo "$(basename "$bin") after recover: $("$bin" dump "$img" | head -3 | tr '\n' ' ')"
done
