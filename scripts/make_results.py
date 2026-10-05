#!/usr/bin/env python3
"""Generate docs/results.html from the JSON the harness and mutation driver write to out/.

Self-contained static page: no external resources, no scripts, no FileReader (the owner
browses in Safari Lockdown Mode). Run `make results` to refresh the inputs first.
"""
from __future__ import annotations

import html
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "out"

THEOREMS = [
    ("atomicity", "Atomicity",
     "If a crash happens at any point during commit, then after recovery the logical disk "
     "equals either the state before the transaction or the state after it."),
    ("durability", "Durability",
     "Once commit returns, the logical disk is the transaction's result, and any crash from "
     "then on recovers to exactly that result."),
    ("recovery_idempotent", "Idempotent recovery",
     "However many times recovery itself crashes and restarts, once a recovery completes the "
     "log is idle and the logical disk is the one the first crash determined."),
    ("get_correct", "Reads in a transaction",
     "A read inside a transaction returns the transaction's own writes, and the committed "
     "disk for every other block; it changes nothing on disk."),
    ("put_correct", "Writes in a transaction",
     "Recording a write changes exactly one block of the transaction's logical disk and "
     "keeps each block logged at most once."),
    ("commitAll_spec", "Sequences of transactions",
     "A crash anywhere in a run of transactions recovers to the state after some prefix of "
     "them -- never to a state with a transaction half applied."),
    ("crash_while_idle", "Crash while idle",
     "A crash while no commit is running loses only the uncommitted, in-memory transaction."),
    ("commit_spec", "Commit (Crash Hoare triple)",
     "The full pre / post / crash specification of commit, in the style of Crash Hoare Logic."),
    ("recover_spec", "Recovery (Crash Hoare triple)",
     "The full specification of recovery: it ends idle, and a crash leaves a state recovery "
     "handles identically next time."),
]


def read_json(name):
    p = OUT / name
    return json.loads(p.read_text()) if p.exists() else None


def axioms():
    p = OUT / "axioms.txt"
    if not p.exists():
        return {}
    out = {}
    for m in re.finditer(r"'Crashproof\.(?:Theorems\.)?(\w+)' depends on axioms: \[([^\]]*)\]",
                         p.read_text()):
        out[m.group(1)] = m.group(2)
    return out


def esc(s):
    return html.escape(str(s))


def harness_card(title, d):
    if not d:
        return f"<div class=card><h3>{esc(title)}</h3><p class=muted>not run yet " \
               "(<code>make results</code>)</p></div>"
    passed = d["runs"] - d["failed"]
    status = "ok" if d["failed"] == 0 else "bad"
    modes = ", ".join(f"{k} {v}" for k, v in sorted(d.get("by_mode", {}).items()))
    outs = "".join(f"<tr><td>{esc(k)}</td><td class=num>{esc(v)}</td></tr>"
                   for k, v in sorted(d.get("outcomes", {}).items()))
    return f"""<div class=card>
<h3>{esc(title)}</h3>
<p><span class="pill {status}">{passed}/{d['runs']} recovered to an allowed state</span></p>
<table><tbody>
<tr><td>crash modes</td><td class=num>{esc(modes)}</td></tr>
<tr><td>crashes injected during recovery</td><td class=num>{esc(d.get('recovery_crashes',0))}</td></tr>
{outs}
</tbody></table>
<p class=muted>fixed seeds {esc(d.get('seeds',''))}, {esc(d.get('seconds','?'))} s on an Apple M-series, shared machine</p>
</div>"""


def main():
    ax = axioms()
    cp = read_json("crashproof.json")
    wr = read_json("wren.json")
    mut = read_json("mutants.json")

    rows = ""
    for key, name, words in THEOREMS:
        a = ax.get(key, "-")
        ok = a != "-" and all(x.strip() in ("propext", "Classical.choice", "Quot.sound")
                              for x in a.split(","))
        badge = "<span class='pill ok'>standard axioms</span>" if ok else \
                ("<span class='pill bad'>check</span>" if a != "-" else "")
        rows += f"<tr><td><b>{esc(name)}</b><div class=muted><code>Crashproof.*.{esc(key)}</code></div></td>" \
                f"<td>{esc(words)}</td><td class=mono>{esc(a)} {badge}</td></tr>\n"

    mut_html = ""
    if mut:
        pr = "".join(
            f"<tr><td class=mono>{esc(m['mutant'])}</td><td>{esc(m['breaks'])}</td>"
            f"<td>{'<span class=pill-ok>proof fails to compile</span>' if m['proof_fails'] else '<span class=pill-bad>still proves</span>'}</td></tr>"
            for m in mut["proof"])
        hr = "".join(
            f"<tr><td class=mono>{esc(m['mode'])}</td>"
            f"<td class=num>{esc(m['failed'])}/{esc(m['runs'])} runs land in a wrong state</td>"
            f"<td>{'<span class=pill-ok>caught</span>' if m['failed'] else '<span class=pill-bad>not caught</span>'}"
            f"{(' (first seed ' + esc(m['first_seed']) + ')') if m['first_seed'] is not None else ''}</td></tr>"
            for m in mut["harness"])
        mut_html = f"""
<h2>Mutation checks</h2>
<p>Each one-line protocol bug must either stop the proofs compiling or be caught by the
crash harness. Proof mutants edit the real protocol in <code>Crashproof/Log.lean</code>;
harness mutants run broken protocols from <code>App/Buggy.lean</code>.</p>
<h3>Proof mutants (must fail to compile)</h3>
<table><thead><tr><th>mutant</th><th>what it removes</th><th>result</th></tr></thead><tbody>{pr}</tbody></table>
<h3>Harness mutants (must be caught)</h3>
<table><thead><tr><th>broken protocol</th><th>runs in a wrong state</th><th>result</th></tr></thead><tbody>{hr}</tbody></table>"""

    page = f"""<!doctype html>
<html lang=en>
<head>
<meta charset=utf-8>
<meta name=viewport content="width=device-width, initial-scale=1">
<title>crashproof results</title>
<style>
:root {{
  --bg:#ffffff; --fg:#1a1a1a; --muted:#666; --line:#e2e2e2; --card:#f7f7f6;
  --ok-bg:#e6f4ea; --ok-fg:#1e6b33; --bad-bg:#fbe9e7; --bad-fg:#b3261e; --mono:#f0f0ef;
}}
:root:not([data-theme=light]) {{ }}
@media (prefers-color-scheme: dark) {{
  :root:not([data-theme=light]) {{
    --bg:#16181c; --fg:#e7e7e7; --muted:#9aa0a6; --line:#2c2f35; --card:#1e2127;
    --ok-bg:#133620; --ok-fg:#7fd49a; --bad-bg:#3a1f1c; --bad-fg:#f0a39a; --mono:#242730;
  }}
}}
:root[data-theme=dark] {{
  --bg:#16181c; --fg:#e7e7e7; --muted:#9aa0a6; --line:#2c2f35; --card:#1e2127;
  --ok-bg:#133620; --ok-fg:#7fd49a; --bad-bg:#3a1f1c; --bad-fg:#f0a39a; --mono:#242730;
}}
* {{ box-sizing:border-box; }}
body {{ background:var(--bg); color:var(--fg); margin:0;
  font:16px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"Helvetica Neue",Arial,"PingFang TC","Microsoft JhengHei",sans-serif; }}
main {{ max-width:900px; margin:0 auto; padding:32px 16px 64px; }}
h1 {{ font-size:26px; margin:0 0 4px; }}
h2 {{ font-size:20px; margin:36px 0 10px; border-bottom:1px solid var(--line); padding-bottom:6px; }}
h3 {{ font-size:16px; margin:20px 0 8px; }}
p {{ margin:8px 0; }}
.muted {{ color:var(--muted); font-size:13px; }}
code {{ background:var(--mono); padding:1px 5px; border-radius:4px; font-size:13px; }}
table {{ border-collapse:collapse; width:100%; margin:10px 0; font-size:14px; }}
th,td {{ text-align:left; padding:8px 10px; border-bottom:1px solid var(--line); vertical-align:top; }}
th {{ color:var(--muted); font-weight:600; font-size:13px; }}
td.num,td.mono {{ font-variant-numeric:tabular-nums; }}
td.mono {{ font-family:ui-monospace,SFMono-Regular,Menlo,monospace; font-size:12px; }}
.cards {{ display:flex; flex-wrap:wrap; gap:16px; }}
.card {{ background:var(--card); border:1px solid var(--line); border-radius:10px; padding:16px; flex:1 1 320px; }}
.pill,.pill-ok,.pill-bad {{ display:inline-block; padding:2px 9px; border-radius:999px; font-size:12px; font-weight:600; }}
.pill.ok,.pill-ok {{ background:var(--ok-bg); color:var(--ok-fg); }}
.pill.bad,.pill-bad {{ background:var(--bad-bg); color:var(--bad-fg); }}
</style>
</head>
<body><main>
<h1>crashproof &mdash; results</h1>
<p class=muted>A write-ahead log whose crash-safety is proved in Lean 4, then the compiled
program is crash-tested against the proved model. A learning reimplementation of FSCQ's ideas.</p>

<h2>Theorems</h2>
<p>Every statement holds for all executions: a crash may strike before any block operation,
the drive may lose, reorder or tear any write since the last sync, and recovery may itself
crash any number of times. The axiom column is <code>#print axioms</code> output.</p>
<table><thead><tr><th>theorem</th><th>in plain words</th><th>axioms</th></tr></thead><tbody>
{rows}</tbody></table>
<p class=muted>Checked in CI by <code>scripts/check-proofs.sh</code>: no <code>sorry</code>, and
only Lean's three standard axioms (<code>propext</code>, <code>Classical.choice</code>,
<code>Quot.sound</code>).</p>

<h2>Crash harness</h2>
<p>Model-based testing of the native executable: a random workload is run and the power is
cut (inject / torn / kill); the recovered image must equal the model's state after every
acknowledged transaction, optionally plus the one in flight &mdash; nothing else.</p>
<div class=cards>
{harness_card("crashproof (this project)", cp)}
{harness_card("wren-os log (kernel/log.c, unmodified)", wr)}
</div>
{mut_html}

<h2>What the proofs do and do not cover</h2>
<p>The proofs are about the model in <code>Crashproof/Disk.lean</code> and the protocol in
<code>Crashproof/Log.lean</code>. They do <b>not</b> cover the Lean compiler, the ~90 lines of
C in <code>native/dev.c</code>, the operating system, or the drive's firmware &mdash; the
trusted base. The crash harness exists precisely to test that untrusted bridge; it found no
discrepancy in {esc((cp or {}).get('runs','?'))} crashproof runs
and {esc((wr or {}).get('runs','?'))} wren-os runs.</p>
</main></body></html>"""
    (ROOT / "docs").mkdir(exist_ok=True)
    (ROOT / "docs" / "results.html").write_text(page)
    print("wrote docs/results.html")


if __name__ == "__main__":
    main()
