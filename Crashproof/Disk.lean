/-!
# The asynchronous disk

This is the disk model of FSCQ (Chen et al., SOSP 2015), restated in Lean.

A real drive has a volatile write cache. `write` returns as soon as the data is in that
cache; the drive may move cached blocks to stable storage later, in any order. A `sync`
(a cache flush, or a FUA/barrier request) returns only when everything written before it is
stable. If power is cut, each block may be left with *any* value written to it since its
last sync, independently of every other block.

We model that by giving each block a *value set*: `cur` is what a read returns now (the
drive serves reads from its cache), and `old` lists the values written since the last
sync that the platter may still hold, including the value that was there at the last sync.
`sync` collapses every value set to `cur`. A crash picks, for each block, one value it
`Survives` with; the machine then restarts on a disk whose value sets are singletons.

Torn writes are modelled too: a block that is being written may end up as a *mix* of two
of its possible values (for a 4096-byte block on 512-byte sectors: some sectors from one
value, the rest from the other). Which mixes are possible is a parameter of the block type
(`Codec.mix`). The log's correctness needs only two facts about tearing: a block mixed with
itself is unchanged, and the commit header decodes the same as one of the two mixed values
(it fits in one sector, which the drive writes atomically).
-/

namespace Crashproof

/-- Everything the log needs to know about a block type: how tears look and how the
commit header is stored in a block. -/
class Codec (V : Type) where
  /-- `mix x y v`: a write tearing between `x` and `y` may leave `v` on the platter. -/
  mix : V → V → V → Prop
  /-- Tearing a block between a value and itself leaves that value. -/
  mix_self : ∀ {x v : V}, mix x x v → v = x
  /-- The commit header: the list of (logical) home addresses of the logged blocks. -/
  encode : List Nat → V
  /-- `none` for a block that is not a well-formed header. -/
  decode : V → Option (List Nat)
  /-- How many addresses one header can hold. -/
  capacity : Nat
  /-- Addresses must be below this bound to be stored in a header. -/
  addrBound : Nat
  decode_encode : ∀ l : List Nat, l.length ≤ capacity → (∀ a ∈ l, a < addrBound) →
    decode (encode l) = some l
  /-- The header is tear-proof: a torn header block decodes like one of the two values. -/
  decode_mix : ∀ {x y v : V}, mix x y v → decode v = decode x ∨ decode v = decode y

/-- The state of one block: the value reads return, plus older values written since the last
sync that a crash may still expose. -/
structure ValSet (V : Type) where
  cur : V
  old : List V

/-- All values a crash could expose (before tearing). -/
def ValSet.vals {V : Type} (s : ValSet V) : List V := s.cur :: s.old

/-- A disk maps every block address to a value set. The model is unbounded; the executable
checks addresses against the image size before they reach the protocol. -/
abbrev Disk (V : Type) := Nat → ValSet V

namespace Disk

variable {V : Type}

/-- Buffered write: the new value becomes current, the previous one stays possible. -/
def write (d : Disk V) (a : Nat) (v : V) : Disk V :=
  fun b => if b = a then ⟨v, (d a).cur :: (d a).old⟩ else d b

/-- Barrier: every block becomes durable at its current value. -/
def sync (d : Disk V) : Disk V := fun b => ⟨(d b).cur, []⟩

/-- The disk the machine sees after rebooting from a crash that left `x` on the platter. -/
def ofState (x : Nat → V) : Disk V := fun b => ⟨x b, []⟩

/-- The current contents, as a function. -/
def curState (d : Disk V) : Nat → V := fun b => (d b).cur

/-- A block has no pending writes. -/
def Durable (d : Disk V) (a : Nat) : Prop := (d a).old = []

end Disk

section Crash
variable {V : Type} [Codec V]

/-- `Survives s v`: after a power cut, a block whose value set is `s` may hold `v`. -/
def Survives (s : ValSet V) (v : V) : Prop :=
  v ∈ s.vals ∨ ∃ x ∈ s.vals, ∃ y ∈ s.vals, Codec.mix x y v

/-- `CrashesTo d x`: cutting power when the disk is `d` may leave the platter as `x`.
Every block chooses independently, so writes since the last sync may be lost, reordered or
torn. -/
def CrashesTo (d : Disk V) (x : Nat → V) : Prop := ∀ a, Survives (d a) (x a)

theorem survives_durable {s : ValSet V} {v : V} (h : s.old = []) (hv : Survives s v) :
    v = s.cur := by
  obtain ⟨cur, old⟩ := s
  simp only at h
  subst h
  rcases hv with hv | ⟨x, hx, y, hy, hm⟩
  · simpa [ValSet.vals] using hv
  · simp [ValSet.vals] at hx hy
    subst hx; subst hy
    exact Codec.mix_self hm

/-- What a crash can do to a header block: it decodes like one of the written values. -/
theorem survives_decode {s : ValSet V} {v : V} (hv : Survives s v) :
    ∃ u ∈ s.vals, Codec.decode v = Codec.decode u := by
  rcases hv with hv | ⟨x, hx, y, hy, hm⟩
  · exact ⟨v, hv, rfl⟩
  · rcases Codec.decode_mix hm with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨y, hy, h⟩

theorem crashesTo_durable {d : Disk V} {x : Nat → V} {a : Nat} (h : CrashesTo d x)
    (hd : d.Durable a) : x a = (d a).cur :=
  survives_durable hd (h a)

/-- A disk with no pending writes crashes only to its current contents. -/
theorem crashesTo_ofState {x y : Nat → V} (h : CrashesTo (Disk.ofState x) y) : y = x := by
  funext a
  exact survives_durable (s := ⟨x a, []⟩) rfl (h a)

theorem crashesTo_refl (x : Nat → V) : CrashesTo (Disk.ofState x) x :=
  fun _ => Or.inl (List.mem_cons_self ..)

end Crash

namespace Disk
variable {V : Type}

@[simp] theorem write_same (d : Disk V) (a : Nat) (v : V) :
    d.write a v a = ⟨v, (d a).cur :: (d a).old⟩ := by simp [write]

@[simp] theorem write_other (d : Disk V) {a b : Nat} (v : V) (h : b ≠ a) :
    d.write a v b = d b := by simp [write, h]

@[simp] theorem sync_apply (d : Disk V) (b : Nat) : d.sync b = ⟨(d b).cur, []⟩ := rfl

@[simp] theorem ofState_apply (x : Nat → V) (b : Nat) : Disk.ofState x b = ⟨x b, []⟩ := rfl

end Disk

end Crashproof
