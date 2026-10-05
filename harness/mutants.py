#!/usr/bin/env python3
"""Mutation checks: one-line protocol bugs must be caught.

Two kinds of mutant:

  proof   - edit one line of the real protocol in Crashproof/Log.lean (in a scratch copy of
            the repository) and run `lake build Crashproof`: the proofs must stop compiling.
  harness - run a deliberately broken protocol from App/Buggy.lean (`--buggy MODE`) through
            harness/crashtest.py with fixed seeds: some run must recover to a wrong state.

usage: harness/mutants.py [--runs N] [--json OUT] [--skip-proofs]
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# (name, what it breaks, exact old text in Crashproof/Log.lean, replacement)
PROOF_MUTANTS = [
    ("no-log-sync", "no barrier between the log slots and the commit-point header",
     "  [.sync] ++                                   -- log slots durable before the commit point",
     "  [] ++"),
    ("no-install-sync", "no barrier between installing and retiring the header",
     "  installOps L t ++                            -- install at home\n  [.sync] ++",
     "  installOps L t ++\n  [] ++"),
    ("no-clear", "the header is never retired after install",
     "  [.write 0 (Codec.encode [])] ++              -- retire the header",
     "  [] ++"),
    ("no-clear-sync", "the retired header is not synced (wren-os's choice, without its CRC)",
     "  [.write 0 (Codec.encode [])] ++              -- retire the header\n  [.sync]",
     "  [.write 0 (Codec.encode [])] ++\n  []"),
    ("hdr-wrong-list", "the header lists only the first logged address",
     "  [.write 0 (Codec.encode (t.map Prod.fst))] ++  -- commit point",
     "  [.write 0 (Codec.encode ((t.map Prod.fst).take 1))] ++"),
    ("rec-no-sync", "recovery retires the header before its replay is durable",
     "  [.sync] ++                                   -- replayed blocks durable before retiring",
     "  [] ++"),
]

HARNESS_MUTANTS = ["no-log-sync", "hdr-first", "no-install-sync", "no-clear", "no-clear-sync",
                   "rec-no-clear", "rec-no-sync"]


def proof_mutant(work: Path, old: str, new: str) -> tuple[bool, str]:
    log = work / "Crashproof" / "Log.lean"
    src = log.read_text()
    if src.count(old) != 1:
        raise SystemExit(f"mutant text not found exactly once: {old!r}")
    log.write_text(src.replace(old, new))
    try:
        r = subprocess.run(["lake", "build", "Crashproof"], cwd=work, capture_output=True,
                           text=True, timeout=1200)
    finally:
        log.write_text(src)
    errs = [ln for ln in (r.stdout + r.stderr).splitlines() if re.match(r"error: \S+\.lean:\d+", ln)]
    first = re.sub(r"^error: ", "", errs[0])[:160] if errs else ""
    return r.returncode != 0, first


def harness_mutant(mode: str, runs: int) -> dict:
    out = Path(tempfile.mkstemp(suffix=".json")[1])
    subprocess.run([sys.executable, str(ROOT / "harness" / "crashtest.py"), "--runs", str(runs),
                    "--quiet", "--jobs", "4", "--buggy", mode, "--json", str(out)],
                   capture_output=True, text=True, timeout=3600)
    d = json.loads(out.read_text())
    out.unlink()
    first = d["failures"][0] if d["failures"] else None
    return {"mode": mode, "runs": d["runs"], "failed": d["failed"],
            "first_seed": first["seed"] if first else None,
            "first_error": first["error"][:200] if first else None}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=1000)
    ap.add_argument("--json", type=Path)
    ap.add_argument("--skip-proofs", action="store_true")
    a = ap.parse_args()
    report: dict = {"proof": [], "harness": []}
    ok = True
    if not a.skip_proofs:
        work = Path(tempfile.mkdtemp(prefix="mutants-"))
        try:
            files = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True,
                                   check=True).stdout.split("\n")
            for f in filter(None, files):
                (work / f).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / f, work / f)
            if (ROOT / ".lake").exists():           # reuse built dependencies of unmutated files
                shutil.copytree(ROOT / ".lake", work / ".lake", symlinks=True)
            for name, what, old, new in PROOF_MUTANTS:
                failed, first = proof_mutant(work, old, new)
                report["proof"].append({"mutant": name, "breaks": what, "proof_fails": failed,
                                        "first_error": first})
                ok &= failed
                print(f"proof   {name:16s} {'proof fails' if failed else 'STILL PROVES (bad)'}"
                      f"  {first}", flush=True)
        finally:
            shutil.rmtree(work, ignore_errors=True)
    for mode in HARNESS_MUTANTS:
        r = harness_mutant(mode, a.runs)
        report["harness"].append(r)
        caught = r["failed"] > 0
        ok &= caught
        print(f"harness {mode:16s} {r['failed']:4d}/{r['runs']} runs wrong"
              f"{'' if caught else '  NOT CAUGHT'}"
              f"{f'  (first: seed {r[chr(102)+chr(105)+chr(114)+chr(115)+chr(116)+chr(95)+chr(115)+chr(101)+chr(101)+chr(100)]})' if caught else ''}",
              flush=True)
    if a.json:
        a.json.write_text(json.dumps(report, indent=1) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
