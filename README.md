# crashproof

**A write-ahead log whose crash-safety is *proved* in Lean 4 — then the compiled program is
crash-tested against the proved model, and differentially tested against a second, independent
log (wren-os).** A learning reimplementation of the ideas in MIT's FSCQ, in a different proof
assistant. Not affiliated with MIT; no novelty is claimed.

Testing can find bugs but can never show a storage layer *never* loses committed data: power
can fail at any of astronomically many instants. A proof can. crashproof states what a crash
may do to a disk with a write cache, implements a log, and proves — with no `sorry` and only
Lean's three standard axioms — that after any crash and recovery the data is either fully there
or fully not, never half-written.

```
$ crashproof demo
formatted a 4-block disk with a 4-slot log; committing tags 1,2 to blocks 0,1
header empty
0 1
1 2
...
now committing tags 3,4 to blocks 0,1 (a child process loses power at block operation 9,
after the commit point, while installing)
crash: power cut before block operation 9

after the crash, before recovery (block 1 is new, block 0 is still old):
header commits 2 blocks [1, 0]
0 1
1 4
after recovery (the header commits the transaction, so the log is replayed):
header empty
0 3
1 4
```

The crash lands *mid-install* — block 1 already holds the new value, block 0 still holds the
old one. Because the crash is past the commit point, recovery replays the log and the
transaction completes atomically.

## What is proved

With `#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound` (checked in CI):

| Theorem | In plain words |
|---|---|
| `atomicity` | A crash at any point of commit, then recovery, leaves the logical disk at the pre- or the post-transaction state — never in between. |
| `durability` | Once commit returns, the result is the transaction's, and any later crash + recovery reproduces exactly it. |
| `recovery_idempotent` | Any number of crashes *during* recovery, then a completed recovery, still gives an allowed state. |
| `get_correct` | A read inside a transaction sees the transaction's own writes, and the committed disk elsewhere. |
| `put_correct`, `put?_ok` | A write changes exactly one logical block; `put?` only builds committable transactions. |
| `commitAll_spec` | A crash in a sequence of transactions recovers to the state after some prefix — never a half-applied one. |
| `commit_spec`, `recover_spec` | The full Crash Hoare triples the above build on. |

Statements in plain words, the axiom report and harness statistics are collected in
[`docs/results.html`](docs/results.html).

## How it works

- **Disk model** (`Crashproof/Disk.lean`): each block has a current value plus the older values
  written since its last sync; `write` buffers, `sync` is a barrier, a crash leaves each block
  at any surviving value, and a block being written may be torn at a 512-byte sector boundary.
  This is the FSCQ/xv6 asynchronous-disk model.
- **Crash Hoare Logic** (`Crashproof/Prog.lean`): programs are a free monad with an operational
  semantics in which a crash may fire before any step; specifications are pre / post / **crash**
  conditions, as in FSCQ.
- **The log** (`Crashproof/Log.lean`): header + log slots + install + clear, with explicit
  barriers — the same protocol shape as wren-os's `kernel/log.c`.
- **Real blocks** (`Crashproof/Block.lean`): a 4096-byte `ByteArray` codec whose round-trip and
  tear-tolerance laws are proved, so the theorems apply to the bytes the executable writes.
- **Running code** (`App/`, `native/dev.c`, `Main.lean`): the executable interprets the very
  `Prog` values the theorems describe, on a disk-image file, with a simulated write cache and
  crash injection.

See [`docs/report.md`](docs/report.md) for the full write-up and [`docs/DESIGN.md`](docs/DESIGN.md)
for the architecture. A beginner's walkthrough in Traditional Chinese is in
[`docs/導讀.zh-TW.md`](docs/導讀.zh-TW.md).

## Results (measured on this machine)

Apple M-series, shared machine; fixed seeds, printed on failure.

- **Proofs**: build clean, no `sorry`, only the three standard axioms (`make proofs`).
- **Crash harness**: 2000/2000 runs recover to an allowed state across inject / torn / kill
  crashes, with extra crashes injected during recovery (`make harness`).
- **Mutation checks**: 6/6 one-line proof mutants fail to compile; 7/7 broken-protocol mutants
  are caught by the harness (`make mutants`).
- **Differential vs. wren-os**: wren-os's `kernel/log.c`, compiled unmodified, passes the same
  harness 2000/2000 (`make diff-wren`). The one observable protocol difference (wren-os relies
  on a CRC instead of a final barrier) is reproduced and assessed in `docs/report.md` §7 and
  `wren/reproduce.sh`. It is not a bug.

## Limitations

- The **trusted base** is unverified: the Lean compiler, `native/dev.c`, the OS and the drive
  firmware. The model assumes flushes are honest and barriers are true fences. The harness
  tests this bridge; the proofs do not cover it.
- No file-system or key-value layer is built on top yet. `commitAll_spec` is the base for one;
  it was left out for time rather than faked.
- Concurrency is modelled only as transactions in sequence (`commitAll_spec`); the executable
  is single-threaded.

## Build and test

Needs Lean 4 (via [elan](https://leanprover.github.io); the version is pinned in
`lean-toolchain`) and Python 3. From this directory (its name contains spaces and CJK — all
build paths are relative):

```sh
make build        # compile the library and the executable
make proofs       # no sorry; only propext / Classical.choice / Quot.sound
make test         # build + proofs + crash harness
make demo         # the transcript above
make mutants      # proof and harness mutation checks
make diff-wren    # differential test against wren-os (needs the wren-os repo as a sibling)
make results      # regenerate docs/results.html
```

Or double-click **`跑跑看.command`** (Chinese, beginner-friendly: builds, checks the proofs,
runs the harness and opens the results page).

## Related work

- **FSCQ** (Chen et al., SOSP 2015) — the file system this learns from; it introduced Crash
  Hoare Logic. **DFSCQ** (Chen et al., SOSP 2017) adds a log-bypass and a precise fsync spec.
- **Yggdrasil** (Sigurbjarnarson et al., OSDI 2016) — crash-consistency by push-button SMT
  verification rather than interactive proof.
- **Perennial** (Chajed et al., SOSP 2019) — concurrent crash-safety in Coq/Iris; goes well
  beyond the sequential log here.
- **xv6's log** — the teaching redo-log whose protocol crashproof and wren-os both follow.
- **wren-os** (`github.com/useless-husband/wren-os`) — the author's from-scratch OS; its
  `kernel/log.c` is the differential-test target here, used read-only and unmodified.
- **linproof** (`github.com/useless-husband/linproof`) — the author's earlier Lean project
  (a linearizability checker, proved correct); same toolchain and CI conventions.

This is a learning reimplementation of published ideas. It claims no novelty and no
affiliation with the authors of the work above.

## License

MIT — see [LICENSE](LICENSE).
