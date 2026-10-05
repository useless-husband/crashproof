# Design notes

This complements `docs/report.md` (the full write-up) with the architecture and the
trade-offs that were rejected. Read the report first.

## Module map

```
Crashproof/Disk.lean     asynchronous disk: ValSet, write/sync, Survives/CrashesTo, torn sectors
Crashproof/Prog.lean     free-monad programs, Exec semantics, Crash Hoare Logic (Spec + rules)
Crashproof/Log.lean      the protocol: layout, Txn, commitOps, recoverOps, Idle, recovered
Crashproof/Writes.lean   applyWrites algebra: idempotence, put/find? meaning
Crashproof/LogProofs.lean the three crash lemmas + prefix-walk of commit and recovery
Crashproof/Theorems.lean  the headline theorems and sequences of transactions
Crashproof/Block.lean     ByteArray codec on 512-byte sectors; decode_encode + decode_mix
App/Device.lean          interpret a Prog on a file with a simulated write cache + crash injection
App/Image.lean           image layout, tagged test blocks, dump/describe
App/Buggy.lean           deliberately broken protocols for mutation testing (unproved)
Main.lean                command line: format / run / recover / dump / demo
native/dev.c             the only C: pread/pwrite/fsync/F_FULLFSYNC (trusted)
harness/crashtest.py     model-based crash testing of the executable
harness/mutants.py       proof mutants (must fail to compile) + harness mutants (must be caught)
wren/                    wren-os's log.c on a host simulated disk, for the differential test
```

The dependency arrow points one way: `Crashproof/*` is pure and verified and never imports
`App/*`; `App/*` interprets the verified `Prog` values but adds no axioms to them.

## Hard problems and how they were solved

**Expressing "a crash can happen anywhere".** A crash is a rule of the operational semantics
(`Exec.crash`) that fires before any step, rather than a separate fault model bolted on. A
straight-line program's crash states are then exactly the prefixes of its operation list
(`Op.exec_run`), which `AllPrefixes` captures and composes over `++`. This is what makes the
commit proof a sequence of small, local arguments instead of one monolith.

**Reasoning about partial installs and tears uniformly.** `crash_committed` is proved for an
*arbitrary* contents of the home blocks: it never looks at how far the install got, so a
half-installed or torn home block is handled by the same lemma as a fully-installed one. Tears
enter only at the header, through `decode_mix`, where one sector's atomicity is all that is
needed.

**Idempotent recovery as induction.** `RecoversTo` is an inductive relation: `done`, or `crash`
then `CrashesTo` then `RecoversTo` again. `recovery_idempotent` is its induction, using
`recover_spec`'s crash condition (`RecoverCrash`: a crash leaves a state with the same
`recovered` value) at the inductive step.

## Trade-offs rejected

- **A checksummed header (wren-os's design).** It saves one barrier per commit but needs CRC
  collision-resistance and single-sector atomicity as assumptions. For a project whose point is
  a clean proof, the extra barrier is cheaper than the extra hypotheses. The comparison in the
  report shows both are correct; crashproof keeps the simpler invariant (`Idle`: the header is
  *durably* empty), wren-os keeps the faster protocol.
- **Mathlib.** Not used. The proofs need only `List`/`Nat` lemmas from Lean's own library, so
  CI stays fast and the trusted base stays small.
- **Verifying the I/O layer.** Out of reach: `pread`/`pwrite`/`fsync` are `@[extern]` C. Rather
  than pretend, `native/dev.c` is named as trusted and the harness tests it.
- **A richer file system on top.** `commitAll_spec` (sequences of atomic transactions) is the
  natural base for a key-value or file layer; building that layer was left out for time and is
  listed under Limitations, not faked.
