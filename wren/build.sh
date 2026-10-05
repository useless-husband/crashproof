#!/usr/bin/env bash
# Build the wren-os log driver: wren-os's kernel/log.c and lib/crc32c.c, compiled
# exactly as they are, plus wren/shim.c (the host disk model). Read-only use of the
# wren-os repository: nothing in it is modified.
#
# Finds wren-os as a sibling of this project in github-projects; override with WREN=/path.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
proj="$(dirname "$here")"
WREN="${WREN:-$(cd "$proj/.." && pwd)/從零寫的作業系統 wren-os}"

if [ ! -f "$WREN/kernel/log.c" ]; then
    echo "wren-os not found at: $WREN" >&2
    echo "set WREN=/path/to/wren-os and retry (public: github.com/useless-husband/wren-os)" >&2
    exit 2
fi

out="$proj/build/wren"
mkdir -p "$out"
CC="${CC:-cc}"
inc=(-I "$WREN/kernel" -I "$WREN/include" -I "$WREN/lib")
flags=(-std=c11 -O2 -Wall)

commit="$(git -C "$WREN" rev-parse --short HEAD 2>/dev/null || echo unknown)"
echo "building wren-os log driver from $WREN (commit $commit)"
printf 'log.c sha256: ' && shasum -a 256 "$WREN/kernel/log.c" | awk '{print $1}'

"$CC" "${flags[@]}" "${inc[@]}" -c "$WREN/kernel/log.c" -o "$out/log.o"
"$CC" "${flags[@]}" "${inc[@]}" -c "$WREN/lib/crc32c.c" -o "$out/crc32c.o"
"$CC" "${flags[@]}" "${inc[@]}" -c "$here/shim.c" -o "$out/shim.o"
"$CC" "$out/log.o" "$out/crc32c.o" "$out/shim.o" -o "$out/wrenlog"
echo "built $out/wrenlog"
