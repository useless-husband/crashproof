#!/usr/bin/env python3
"""Crash-injection harness: model-based testing of a log executable.

The Lean proofs are about the model of the protocol. This harness checks that the compiled
program behaves like the model on a real file: for each seed it

  1. formats a fresh image and generates a random workload of transactions (with reads
     whose expected results come from an independent Python model);
  2. runs the workload and cuts the power in one of three ways:
       inject - the executable powers off just before block operation N (pending writes
                are kept, lost or reordered at random, per block);
       torn   - the same, and a pending block may be torn at a sector boundary;
       kill   - SIGKILL the process after a random delay (real OS page cache);
  3. optionally crashes the recovery itself up to three times;
  4. recovers, dumps the image and checks that the header is empty and the data equals
     the model's state after every acknowledged transaction, possibly plus the one that was
     in flight -- nothing else.

Any failure prints the seed; rerun one seed with --seeds S.

The same harness drives the wren-os log (backend "wren"): wren-os's kernel/log.c compiled
for the host against a simulated disk (see wren/README.md).

usage: harness/crashtest.py [--backend crashproof|wren] [--bin PATH] [--runs N]
                            [--first-seed S] [--seeds a,b] [--jobs J] [--json OUT]
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BIN = {
    "crashproof": ROOT / ".lake" / "build" / "bin" / "crashproof",
    "wren": ROOT / "build" / "wren" / "wrenlog",
}
CRASH = 99


class Failure(Exception):
    pass


def run(cmd: list[str], ok=(0,), timeout=120) -> subprocess.CompletedProcess:
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if r.returncode not in ok:
        raise Failure(f"{' '.join(cmd[1:3])} exited {r.returncode}\n{r.stdout[-800:]}{r.stderr[-800:]}")
    return r


def make_workload(rnd: random.Random, log_len: int, n_data: int):
    """Return (workload text, list of transactions as dicts addr->tag)."""
    state = {a: 0 for a in range(n_data)}
    lines: list[str] = []
    txns: list[dict[int, int]] = []
    tag = 1
    for _ in range(rnd.randint(2, 7)):
        lines.append("begin")
        txn: dict[int, int] = {}
        for _ in range(rnd.randint(1, min(log_len, 6))):
            a = rnd.randrange(n_data)
            if a not in txn and len(txn) >= log_len:
                continue
            if rnd.random() < 0.3:          # read inside the transaction
                b = rnd.randrange(n_data)
                lines.append(f"get {b} {txn.get(b, state[b])}")
            txn[a] = tag
            lines.append(f"put {a} {tag}")
            tag += 1
        if rnd.random() < 0.5:
            b = rnd.choice(list(txn))
            lines.append(f"get {b} {txn[b]}")
        lines.append("commit")
        txns.append(txn)
        state.update(txn)
        if rnd.random() < 0.3:              # read after commit, outside a transaction
            b = rnd.randrange(n_data)
            lines.append(f"get {b} {state[b]}")
    return "\n".join(lines) + "\n", txns


def states_after(n_data: int, txns: list[dict[int, int]]) -> list[dict[int, int]]:
    s = {a: 0 for a in range(n_data)}
    out = [dict(s)]
    for t in txns:
        s.update(t)
        out.append(dict(s))
    return out


def parse_dump(text: str) -> tuple[str, dict[int, str]]:
    lines = text.strip().splitlines()
    header = lines[0]
    blocks = {}
    for ln in lines[1:]:
        a, d = ln.split(" ", 1)
        blocks[int(a)] = d
    return header, blocks


class Backend:
    def __init__(self, name: str, binary: Path):
        self.name = name
        self.bin = str(binary)

    def format(self, img: Path, log_len: int, n_data: int):
        run([self.bin, "format", str(img), "--log", str(log_len), "--data", str(n_data)])

    def geometry(self, rnd: random.Random) -> tuple[int, int]:
        if self.name == "wren":           # wren-os's log has a fixed 64-slot area
            return 64, rnd.choice([8, 16, 32])
        return rnd.choice([2, 4, 8, 16]), rnd.choice([4, 8, 16, 32])


def one_run(seed: int, be: Backend, tmp: Path) -> dict:
    rnd = random.Random(seed)
    mode = rnd.choice(["inject", "inject", "torn", "kill"])
    log_len, n_data = be.geometry(rnd)
    wl_text, txns = make_workload(rnd, log_len, n_data)
    desc: dict = {"seed": seed, "mode": mode, "log": log_len, "data": n_data, "txns": len(txns)}
    d = tmp / f"s{seed}"
    d.mkdir()
    img, wl = d / "disk.img", d / "workload.txt"
    wl.write_text(wl_text)
    try:
        be.format(img, log_len, n_data)
        # dry run on a copy: how many block operations does the run take?
        shutil.copyfile(img, d / "dry.img")
        r = run([be.bin, "run", str(d / "dry.img"), str(wl), "--no-fsync"])
        total = int(re.search(r"ops (\d+)", r.stdout).group(1))
        dry_acks = len(re.findall(r"^ack ", r.stdout, re.M))
        if dry_acks != len(txns):
            raise Failure(f"dry run acknowledged {dry_acks} of {len(txns)} transactions")
        if mode in ("inject", "torn"):
            k = rnd.randrange(total)
            desc["crash_at"] = k
            cmd = [be.bin, "run", str(img), str(wl), "--crash-at", str(k), "--seed", str(seed),
                   "--no-fsync"] + (["--torn"] if mode == "torn" else [])
            r = run(cmd, ok=(CRASH,))
            out = r.stdout
        else:
            delay_us = 300
            est = total * delay_us / 1e6
            when = rnd.uniform(0, est * 1.2)
            desc["kill_after_s"] = round(when, 4)
            p = subprocess.Popen([be.bin, "run", str(img), str(wl), "--no-fsync",
                                  "--delay-us", str(delay_us)],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            time.sleep(when)
            p.kill()
            out, _ = p.communicate(timeout=60)
            desc["killed"] = p.returncode != 0
            if p.returncode not in (0, -9):
                raise Failure(f"run exited {p.returncode}")
        if "read-mismatch" in out:
            raise Failure("a read inside a transaction returned the wrong block: " + out)
        acks = len(re.findall(r"^ack ", out, re.M))
        desc["acked"] = acks
        before = parse_dump(run([be.bin, "dump", str(img)]).stdout)[0]
        desc["header_after_crash"] = ("committed" if "commits" in before else
                                      "empty" if "empty" in before else "garbage")
        # crash the recovery too, up to three times
        nested = rnd.choice([0, 0, 1, 2, 3])
        desc["recovery_crashes"] = 0
        for i in range(nested):
            shutil.copyfile(img, d / "dryrec.img")
            rr = run([be.bin, "recover", str(d / "dryrec.img"), "--no-fsync"])
            n = int(re.search(r"ops (\d+)", rr.stdout).group(1))
            if n == 0:
                break
            k2 = rnd.randrange(n)
            run([be.bin, "recover", str(img), "--crash-at", str(k2), "--seed", str(seed * 10 + i),
                 "--no-fsync"] + (["--torn"] if mode == "torn" else []), ok=(CRASH,))
            desc["recovery_crashes"] += 1
        run([be.bin, "recover", str(img), "--no-fsync"])
        header, blocks = parse_dump(run([be.bin, "dump", str(img)]).stdout)
        if header != "header empty":
            raise Failure(f"after recovery the header is not empty: {header}")
        allowed = states_after(n_data, txns)
        got = {a: blocks[a] for a in range(n_data)}
        cands = [i for i in (acks, acks + 1) if i < len(allowed)]
        match = [i for i in cands if all(str(allowed[i][a]) == got[a] for a in range(n_data))]
        if not match:
            exp = allowed[acks]
            diff = {a: (exp[a], got[a]) for a in range(n_data) if str(exp[a]) != got[a]}
            raise Failure(f"recovered state is not the state after {acks} or {acks + 1} "
                          f"transactions; differences from {acks} (expected, got): {diff}")
        desc["outcome"] = ("in-flight applied" if match[0] == acks + 1 else
                           "in-flight lost" if acks < len(txns) else "all committed")
        desc["ok"] = True
    except (Failure, subprocess.TimeoutExpired, AttributeError) as e:
        desc["ok"] = False
        desc["error"] = str(e)
    finally:
        shutil.rmtree(d, ignore_errors=True)
    return desc


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--backend", choices=["crashproof", "wren"], default="crashproof")
    ap.add_argument("--bin", type=Path)
    ap.add_argument("--runs", type=int, default=200)
    ap.add_argument("--first-seed", type=int, default=1)
    ap.add_argument("--seeds", default="")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--json", type=Path)
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args()
    binary = a.bin or DEFAULT_BIN[a.backend]
    if not binary.exists():
        print(f"missing {binary}: build it first", file=sys.stderr)
        return 2
    be = Backend(a.backend, binary)
    seeds = [int(s) for s in a.seeds.split(",") if s] or \
        list(range(a.first_seed, a.first_seed + a.runs))
    tmp = Path(tempfile.mkdtemp(prefix="crashtest-"))
    t0 = time.monotonic()
    results = []
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        for d in pool.map(lambda s: one_run(s, be, tmp), seeds):
            results.append(d)
            if not d["ok"]:
                print(f"seed {d['seed']} {d['mode']}: FAILED\n  {d['error']}", flush=True)
            elif not a.quiet:
                where = (f"crash before op {d['crash_at']}" if "crash_at" in d
                         else f"SIGKILL after {d['kill_after_s']} s")
                print(f"seed {d['seed']:5d} {d['mode']:6s} {where:26s} acked {d['acked']}/{d['txns']}"
                      f" header {d['header_after_crash']:9s} recovery crashes {d['recovery_crashes']}"
                      f" -> {d['outcome']}", flush=True)
    shutil.rmtree(tmp, ignore_errors=True)
    fails = [d for d in results if not d["ok"]]
    secs = time.monotonic() - t0
    by_mode: dict[str, int] = {}
    outcomes: dict[str, int] = {}
    headers: dict[str, int] = {}
    for d in results:
        by_mode[d["mode"]] = by_mode.get(d["mode"], 0) + 1
        if d["ok"]:
            outcomes[d["outcome"]] = outcomes.get(d["outcome"], 0) + 1
            headers[d["header_after_crash"]] = headers.get(d["header_after_crash"], 0) + 1
    nested = sum(d.get("recovery_crashes", 0) for d in results)
    print(f"{be.name}: {len(results) - len(fails)}/{len(results)} runs recovered to an allowed "
          f"state ({', '.join(f'{k} {v}' for k, v in sorted(by_mode.items()))}; "
          f"{nested} crashes during recovery) in {secs:.0f} s")
    if a.json:
        a.json.write_text(json.dumps({
            "backend": be.name, "runs": len(results), "failed": len(fails),
            "seeds": [seeds[0], seeds[-1]] if seeds else [], "by_mode": by_mode,
            "outcomes": outcomes, "header_after_crash": headers,
            "recovery_crashes": nested, "seconds": round(secs, 1),
            "failures": [{"seed": d["seed"], "error": d["error"][:300]} for d in fails],
        }, indent=1) + "\n")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
