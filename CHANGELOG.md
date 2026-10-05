# Changelog

All notable changes to this project are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/), and the project uses semantic versioning.

## [0.1.0] - 2026-10-05

First release.

### Added
- Asynchronous disk model with crashes and torn sectors (`Crashproof/Disk.lean`), and a
  free-monad program type with a crash-aware operational semantics and a Crash Hoare Logic
  (`Crashproof/Prog.lean`).
- An executable write-ahead log (`Crashproof/Log.lean`) with begin / write / read / commit /
  recovery, using the same header + log-blocks + install + clear protocol as wren-os's log.
- Machine-checked theorems (no `sorry`, only the axioms `propext`, `Classical.choice`,
  `Quot.sound`): atomicity, durability, idempotent recovery, correctness of reads and writes
  inside a transaction, and a specification for sequences of transactions.
- A `ByteArray` block codec (`Crashproof/Block.lean`) with proved round-trip and
  tear-tolerance laws, so the proofs apply to the block type the executable actually uses.
- A native executable operating on a disk-image file, with a simulated write cache and crash
  injection (`App/`, `native/dev.c`, `Main.lean`).
- A crash-injection harness that model-tests the executable against the spec with fixed seeds
  (`harness/crashtest.py`), and a mutation-check driver (`harness/mutants.py`).
- A host driver that runs wren-os's `kernel/log.c` unmodified against the same simulated disk
  (`wren/`), for a differential crash test; and a reproducer for the one observable protocol
  difference (`wren/reproduce.sh`).
- `docs/results.html`, a double-clickable `跑跑看.command`, and CI on Ubuntu and macOS.
