import Crashproof.Disk

/-!
# Real blocks: 4096-byte `ByteArray`s on 512-byte sectors

This instantiates `Codec` for the block type the executable uses, and proves its two laws:

* `decode_encode`: the header format round-trips (magic, count, then 32-bit little-endian
  addresses, all inside the first sector);
* `decode_mix`: a torn header block decodes like one of the two values. A tear keeps the
  first `k` sectors of one value and the rest of the other (a drive writes a sector
  atomically but may stop between sectors). `decode` reads only sector 0, so it sees one
  value or the other.

The header layout matches nothing else on purpose; it is not wren-os's format.
-/

namespace Crashproof.Block

def blockSize : Nat := 4096
def sectorSize : Nat := 512
def sectors : Nat := blockSize / sectorSize

/-- "CPLG" read as a little-endian 32-bit number. -/
def magic : Nat := 0x474c5043

/-- Addresses that fit in one sector after the 8-byte prefix. -/
def capacity : Nat := (sectorSize - 8) / 4

def u32le (n : Nat) : List UInt8 :=
  [UInt8.ofNat n, UInt8.ofNat (n / 256), UInt8.ofNat (n / 65536), UInt8.ofNat (n / 16777216)]

def readU32 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: c :: d :: rest =>
    some (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat, rest)
  | _ => none

def readAddrs : Nat → List UInt8 → Option (List Nat)
  | 0, _ => some []
  | k + 1, bs =>
    match readU32 bs with
    | some (a, rest) => (readAddrs k rest).map (a :: ·)
    | none => none

def decodeList (bs : List UInt8) : Option (List Nat) :=
  match readU32 bs with
  | some (mg, rest) =>
    if mg = magic then
      match readU32 rest with
      | some (n, rest') => if n ≤ capacity then readAddrs n rest' else none
      | none => none
    else none
  | none => none

def headerBytes (l : List Nat) : List UInt8 :=
  u32le magic ++ u32le l.length ++ l.flatMap u32le

def encodeList (l : List Nat) : List UInt8 :=
  headerBytes l ++ List.replicate (blockSize - (headerBytes l).length) 0

def encode (l : List Nat) : ByteArray := ⟨(encodeList l).toArray⟩

def decode (b : ByteArray) : Option (List Nat) := decodeList (b.data.toList.take sectorSize)

/-- A write torn between `x` and `y`: the first `k` sectors of one, the rest of the other. -/
def Mix (x y v : ByteArray) : Prop :=
  x.size = blockSize ∧ y.size = blockSize ∧
    ∃ k ≤ sectors, v.data.toList =
      x.data.toList.take (sectorSize * k) ++ y.data.toList.drop (sectorSize * k)

theorem readU32_u32le {n : Nat} (h : n < 2 ^ 32) (rest : List UInt8) :
    readU32 (u32le n ++ rest) = some (n, rest) := by
  simp only [u32le, readU32, List.cons_append, List.nil_append]
  simp
  omega

theorem readAddrs_flatMap {l : List Nat} (h : ∀ a ∈ l, a < 2 ^ 32) (rest : List UInt8) :
    readAddrs l.length (l.flatMap u32le ++ rest) = some l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readAddrs]
    rw [readU32_u32le (h a (List.mem_cons_self ..))]
    simp only []
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rfl

theorem decodeList_header {l : List Nat} (hl : l.length ≤ capacity) (h : ∀ a ∈ l, a < 2 ^ 32)
    (rest : List UInt8) : decodeList (headerBytes l ++ rest) = some l := by
  have hcap : capacity < 2 ^ 32 := by simp [capacity, sectorSize]
  simp only [decodeList, headerBytes, List.append_assoc]
  rw [readU32_u32le (by simp [magic])]
  simp only [if_pos]
  rw [readU32_u32le (by omega)]
  simp only [hl, if_true]
  exact readAddrs_flatMap h rest

theorem headerBytes_length (l : List Nat) : (headerBytes l).length = 8 + 4 * l.length := by
  simp [headerBytes, u32le]
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, u32le, ih]; omega

theorem decode_encode (l : List Nat) (hl : l.length ≤ capacity) (h : ∀ a ∈ l, a < 2 ^ 32) :
    decode (encode l) = some l := by
  simp only [decode, encode, encodeList, List.toList_toArray]
  have hlen : (headerBytes l).length ≤ sectorSize := by
    rw [headerBytes_length]; simp [capacity, sectorSize] at hl ⊢; omega
  rw [List.take_append, List.take_of_length_le hlen]
  exact decodeList_header hl h _

theorem mix_self {x v : ByteArray} (h : Mix x x v) : v = x := by
  obtain ⟨_, _, k, _, hv⟩ := h
  rw [List.take_append_drop] at hv
  exact ByteArray.ext (Array.toList_inj.mp hv)

theorem decode_mix {x y v : ByteArray} (h : Mix x y v) : decode v = decode x ∨ decode v = decode y := by
  obtain ⟨hx, _, k, hk, hv⟩ := h
  simp only [decode, hv]
  cases k with
  | zero => right; simp
  | succ k =>
    left
    have hlen : sectorSize ≤ (x.data.toList.take (sectorSize * (k + 1))).length := by
      simp only [List.length_take, Array.length_toList]
      have : x.data.size = blockSize := hx
      simp [this, sectorSize, blockSize, sectors] at hk ⊢
      omega
    rw [List.take_append_of_le_length hlen, List.take_take]
    have : min sectorSize (sectorSize * (k + 1)) = sectorSize :=
      Nat.min_eq_left (Nat.le_mul_of_pos_right _ (by omega))
    rw [this]

instance : Codec ByteArray where
  mix := Mix
  mix_self := mix_self
  encode := encode
  decode := decode
  capacity := capacity
  addrBound := 2 ^ 32
  decode_encode := decode_encode
  decode_mix := decode_mix

end Crashproof.Block
