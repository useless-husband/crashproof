# crashproof: a crash-safe write-ahead log, proved in Lean 4

A project report. This is a learning reimplementation of ideas from FSCQ (Chen, Ziegler,
Chajed, Chlipala, Kaashoek, Zeldovich, *Using Crash Hoare Logic for Certifying the FSCQ File
System*, SOSP 2015) in a different proof assistant. It is not affiliated with MIT and claims
no novelty. The goal was to understand how a storage layer's crash-safety can be *proved*
rather than only tested, and to connect that proof to a running program and to a separate
operating system's log (wren-os).

## 1. The disk model

A real disk with a write cache does not store what you wrote when you wrote it. `write`
returns once the data is in a volatile cache; the drive copies cached blocks to the platter
later, in an order of its choosing. A `sync` (a cache-flush or a FUA/barrier request) returns
only once everything written before it is durable. On power loss each block is left holding
*some* value written to it since its last sync, independently of every other block.

`Crashproof/Disk.lean` models this. A disk maps each block address to a `ValSet`: a current
value `cur` (what a read returns, because reads are served from the cache) and a list `old`
of older values written since the last sync that the platter might still hold.

- `write a v` makes `v` current and pushes the previous current value onto `old`.
- `sync` collapses every `ValSet` to its current value (`old := []`).
- `CrashesTo d x` says platter state `x` is a possible outcome of cutting power at disk `d`:
  for every block, `x` holds a value that `Survives` that block's value set.

`Survives s v` holds when `v` is one of the values in `s`, *or* `v` is a tear: a mix of two
of them (`Codec.mix`). A 4096-byte block spans eight 512-byte sectors; a drive writes a
sector atomically but may stop between sectors, so a torn block is the first *k* sectors of
one value and the rest of another. The model needs only two facts about tears, both proved
for the real block type in `Crashproof/Block.lean`: a block torn with itself is unchanged
(`mix_self`), and the commit header &mdash; which fits in one sector &mdash; decodes like one
of the two torn values (`decode_mix`).

**Faithfulness.** This is the standard model behind xv6 and FSCQ: buffered writes, an explicit
barrier, per-block independent loss and reordering, and sector-granularity tearing. What it
deliberately does *not* model: media bit-rot after a successful write, a drive that lies about
a completed flush (firmware bugs), reordering *across* a barrier (we take the barrier as a
true fence), and multi-disk failures. Those are part of the trusted base (section 6).

## 2. The protocol

`Crashproof/Log.lean`. The image is laid out as: block 0 is the header; blocks `1..L` are the
log slots; logical block `a` lives at `L + 1 + a`. A transaction `Txn` is an in-memory list of
(address, value) writes with each address recorded once (`put` replaces an earlier write to
the same address; `put?` additionally refuses a transaction that would not fit in the log or
in one header).

`commit` is a straight-line list of block operations (`commitOps`):

1. copy the new values into log slots `1..n`; **sync**;
2. write the header listing the *n* home addresses &mdash; **the commit point** &mdash;; **sync**;
3. install: write each new value to its home block; **sync**;
4. retire: write an empty header; **sync**.

`recover`, run at every mount: read the header; if it commits *n* addresses, copy each log
slot to its home block and **sync**; then write an empty header and **sync**. Reading the log
is the only data-dependent part; the rest is straight-line.

This is xv6's redo log with the barriers written out explicitly, and the same shape as
wren-os's `kernel/log.c`. The one difference from wren-os is discussed in section 7.

## 3. Specification style: Crash Hoare Logic

A crash can interrupt a program between any two block operations, so an ordinary Hoare triple
is not enough: we must also say what every *interrupted* run leaves behind. Following FSCQ,
`Crashproof/Prog.lean` defines a quadruple

```
Spec pre p post crash :=
  for every disk d and result r, if pre d and p can execute on d to r,
  then r is either (done d' a) with post a d', or (crashed d') with crash d'.
```

`Exec` is the operational semantics: a small inductive relation with one rule per operation
plus a `crash` rule that may fire before *any* step. The crash condition describes the disk at
the instant of the crash (with its pending writes); what the platter may then hold is
`CrashesTo`, and what recovery makes of that is `recovered`. The logic has the usual rules
(`spec_bind` sequences two programs and unions their crash conditions; `spec_read`,
`spec_ret`, `spec_conseq`), proved once and reused.

## 4. Proof structure: which lemmas carry the weight

The heart is `Crashproof/LogProofs.lean`. The key definitions:

- `recovered L x` &mdash; the logical disk recovery produces from platter contents `x`. Every
  crash theorem is phrased through this one function.
- `Idle L m d` &mdash; the log is at rest with logical disk `m`: the header is durably empty and
  every data block is durable with the value `m` gives it.
- `CrashesTo`, from the disk model.

Three lemmas do the real work, one per kind of intermediate state, each saying what
`recovered` yields *whatever the crash does*:

- `Idle.crash`: from an idle state, recovery reproduces the logical disk.
- `crash_committed`: when the header durably commits a transaction and the log slots are
  durable, recovery yields the transaction's result **regardless of how far the install got**
  (home blocks may be half-written or torn).
- `crash_header_pending`: while the header is mid-write, it decodes as the old or the new
  header (by `decode_mix`), so recovery yields one of exactly two states.

`commit_prefixes` then walks `commitOps` phase by phase. `AllPrefixes G ops d` means `G`
holds after every prefix of `ops` &mdash; i.e. wherever a crash lands &mdash; and composes over
`++` (`AllPrefixes.append`). Feeding each phase the matching lemma above gives the crash
condition of the whole commit; the post-state is computed directly. `recover_prefixes` does
the same for recovery, using that replay is idempotent (`applyWrites_idem`) so a crash during
recovery leaves a state the next recovery handles identically.

From these, `Crashproof/Theorems.lean` states the headline results. `RecoversTo` is an
inductive relation capturing "recovery, possibly crashing and restarting any number of times,
eventually completes"; `recovery_idempotent` is its induction.

## 5. The theorems (exactly as proved)

- **`atomicity`** &mdash; a crash during `commit` followed by `RecoversTo` ends with the logical
  disk equal to the pre-transaction state *or* the post-transaction state.
- **`durability`** &mdash; after `commit` returns, the logical disk is the transaction's result,
  and any later crash + recovery reproduces exactly that result.
- **`recovery_idempotent`** &mdash; any number of crashes during recovery, then a completed
  recovery, leaves the log idle at the state the first crash determined.
- **`get_correct`** &mdash; a read in a transaction returns the transaction's own writes and the
  committed disk elsewhere, changing nothing.
- **`put_correct`**, **`put?_ok`** &mdash; a recorded write changes exactly one logical block and
  keeps each block logged once; `put?` only builds committable transactions.
- **`commitAll_spec`** &mdash; a crash during a sequence of transactions recovers to the state
  after some prefix of them, never to a half-applied transaction.
- **`commit_spec`**, **`recover_spec`** &mdash; the full Crash Hoare triples the above build on.

`scripts/check-proofs.sh` rejects `sorry`/`admit`/`native_decide` and any `axiom`/`unsafe`/
`partial`/`extern` in the verified library, and checks with `#print axioms` that every theorem
uses only `propext`, `Classical.choice`, `Quot.sound`. CI runs it on every push.

## 6. The trusted base (what the proofs do *not* cover)

The proofs are about the model and the protocol. A bug outside them can still lose data:

- the Lean kernel and the compiler that turns `Prog` into a binary;
- `native/dev.c` (~90 lines of C: `pread`/`pwrite`/`fsync`/`F_FULLFSYNC`) and the simulated
  cache in `App/Device.lean` &mdash; these interpret the very `Prog` values the theorems describe,
  but the interpretation itself is unverified;
- the operating system and file system under the image file, and the drive firmware;
- the model's own assumptions (section 1): no lying flushes, barriers are true fences.

The crash harness exists precisely to test this untrusted bridge.

## 7. Testing the executable, and the wren-os comparison

**Harness (`harness/crashtest.py`).** For each fixed seed it formats an image, generates a
random workload (transactions with reads whose expected answers come from an independent
Python model), runs it while cutting the power &mdash; `inject` (power off before block operation
*N*), `torn` (also tear a block at a sector boundary), or `kill` (SIGKILL the process) &mdash;
optionally crashes the recovery up to three more times, then recovers and checks the image
equals the model state after every acknowledged transaction, possibly plus the one in flight,
and nothing else. Result: **2000/2000** runs consistent (and 1500/run in CI on Ubuntu and
macOS). This is model-based testing, because the proofs cover the model, not the compiler/OS.

**Mutation checks (`harness/mutants.py`).** Each one-line protocol bug must break a proof or be
caught by the harness. Six *proof mutants* edit the real `commitOps`/`recoverOps` (drop the
log-slot barrier, drop the install barrier, never retire the header, retire without syncing,
truncate the header's address list, drop recovery's barrier): all six stop `lake build`
compiling. Seven *harness mutants* run broken protocols from `App/Buggy.lean` through the
harness: all seven are caught (e.g. "header written before log slots" lands in a wrong state
in ~9% of runs; "recovery never clears the header" in ~46%). The exact numbers are on the
results page.

**Differential test against wren-os.** `wren/build.sh` compiles wren-os's `kernel/log.c` and
`lib/crc32c.c` **unmodified** (printing the file's SHA-256 and the source commit) against a
host shim (`wren/shim.c`) that provides the same simulated asynchronous disk and the same
command line as the crashproof executable. The identical harness then drives wren-os's real
log: **2000/2000** runs consistent. Read-only use of the wren-os repository; nothing in it is
changed.

**The one protocol difference (reproducer: `wren/reproduce.sh`).** crashproof *syncs* after
retiring the header (step 4), so after `commit` returns the on-disk header is durably empty.
wren-os omits that final barrier and instead protects the header with a CRC32C over the header
fields and the logged data. The observable effect: after a single clean commit, crashproof's
header reads "empty" while wren-os's still names the committed transaction. **This is not a
bug.** wren-os's recovery recomputes the CRC over the *current* log data; once the next
transaction overwrites the log slots, a stale header fails its checksum and is ignored, and a
genuinely-committed header is replayed idempotently. So wren-os proves the same end-to-end
property by a different argument, and trades one barrier per commit (a real performance win)
for two extra assumptions that the crashproof proof does not need: (a) CRC32C collision
resistance against the specific data a later transaction writes, and (b) that the header, one
sector, is written atomically so a torn header is detected rather than silently valid. How
realistic is the risk? (a) is a 1-in-2^32 accident per stale-header mount for arbitrary data
and effectively unreachable for an adversary who cannot choose the logged bytes; (b) holds on
every drive with 512-byte atomic sectors, which the model assumes anyway. In short: wren-os's
design is sound and faster; crashproof's is simpler to prove. Documenting *why* both are
correct, from the same model, was the most useful outcome of the comparison.

## 8. Lessons

- Phrasing every crash theorem through one function (`recovered`) and proving three
  state-shaped lemmas, then composing them along the operation list, kept the proof modular;
  the alternative (reasoning about each crash point ad hoc) does not scale.
- The hardest honesty is the trusted base. The proof is worth little without the harness that
  tests everything the proof excludes; the two together are the point.
- Comparing with a second, independently written log (wren-os) turned an abstract proof into a
  concrete claim about real code, and surfaced a genuine design axis (barrier vs. checksum)
  that reading one implementation alone would have hidden.
