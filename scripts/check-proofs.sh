#!/usr/bin/env bash
# Proof hygiene: no sorry/admit/native_decide in the verified library, no axiom/unsafe/partial
# definitions in it, a clean build, and only Lean's three standard axioms behind the main
# theorems. Run from the repository root. The App/ and Main code is the unverified shell and
# is not checked here.
set -euo pipefail
fail=0

lib() { echo Crashproof.lean Crashproof/Disk.lean Crashproof/Prog.lean Crashproof/Log.lean \
  Crashproof/Writes.lean Crashproof/LogProofs.lean Crashproof/Theorems.lean Crashproof/Block.lean; }

if grep -nE '\b(sorry|admit|native_decide)\b' $(lib); then
  echo "error: sorry/admit/native_decide found"; fail=1
fi
if grep -nE '^\s*(axiom|unsafe|partial|@\[implemented_by|@\[extern)' $(lib); then
  echo "error: axiom/unsafe/partial/implemented_by/extern declaration in the library"; fail=1
fi
if grep -nE 'set_option\s+debug\.|skipKernelTC' $(lib); then
  echo "error: a debug option that weakens checking is set in the library"; fail=1
fi

log=$(mktemp)
lake build Crashproof 2>&1 | tee "$log"
if grep -qE "declaration uses .sorry." "$log"; then
  echo "error: the build reports a declaration that uses sorry"; fail=1
fi
rm -f "$log"

out=$(lake env lean scripts/axioms.lean)
echo "$out"
n=$(printf '%s\n' "$out" | grep -c "depends on axioms" || true)
if [ "$n" -ne 10 ]; then echo "error: expected 10 axiom reports, got $n"; fail=1; fi
bad=$(printf '%s\n' "$out" | grep "depends on axioms" \
  | sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$bad" ]; then echo "error: non-standard axioms: $bad"; fail=1; fi
if printf '%s\n' "$out" | grep -q sorryAx; then echo "error: sorryAx"; fail=1; fi

if [ "$fail" -ne 0 ]; then exit 1; fi
echo "proof checks passed"
