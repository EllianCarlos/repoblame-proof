/-
  The line filter of a source blob (`blame_filter_build`,
  `blame_filter_set`, `blame_filter_test`).
-/
import RepoblameProof.Basic

namespace RB

/-- An item of a filter: one line, or two lines that follow one another. -/
inductive Item (K : Type) where
  | line : K → Item K
  | pair : K → K → Item K
deriving DecidableEq, Repr

variable {L K : Type}

/-- `BLAME_FILTER_LINE_SCORE`: a single line goes in the filter only when
it scores above this. -/
def lineScoreMin : Nat := 16

/-- The pairs of adjacent lines of a blob. -/
def pairItems (key : L → K) : List L → List (Item K)
  | a :: b :: rest => Item.pair (key a) (key b) :: pairItems key (b :: rest)
  | _ => []

/-- The single lines of a blob that score above `lineScoreMin`. -/
def lineItems (lv : LineView L K) (src : List L) : List (Item K) :=
  (src.filter (fun x => decide (lineScoreMin < 1 + lv.alnum x))).map (fun x => Item.line (lv.key x))

/-- The items that `blame_filter_build` puts in the filter of `src`
(before the removal of duplicates, which does not change membership). -/
def items (lv : LineView L K) (src : List L) : List (Item K) :=
  lineItems lv src ++ pairItems lv.key src

/-- A filter: a set of items with no false negatives.  False positives
are allowed.  `salt` is the salt of the filter (from the blob id). -/
structure FilterImpl (K : Type) where
  F : Type
  build : UInt64 → List (Item K) → F
  mem : F → Item K → Bool
  noFalseNeg : ∀ salt xs x, x ∈ xs → mem (build salt xs) x = true

/-! ### The exact filter (no false positives): a reference instance. -/

def exactFilter (K : Type) [DecidableEq K] : FilterImpl K where
  F := List (Item K)
  build := fun _ xs => xs
  mem := fun f x => decide (x ∈ f)
  noFalseNeg := by intro _ xs x h; simp [h]

/-! ### Bloom filters with any probe function

The bits are a natural number; bit `b` is set when `testBit b` holds.
`probes salt nbits e` gives the bit numbers of the item with hash `e`.
The theorem holds for every probe function: set and test use the same
probes, and a set never clears a bit. -/

structure BloomF where
  nbits : Nat
  salt : UInt64
  bits : Nat

def setBits (acc : Nat) (bs : List Nat) : Nat := bs.foldl (fun a b => a ||| (1 <<< b)) acc

theorem setBits_mono (bs : List Nat) : ∀ acc i, acc.testBit i = true → (setBits acc bs).testBit i = true := by
  induction bs with
  | nil => intro acc i h; simpa [setBits] using h
  | cons b bs ih =>
    intro acc i h
    simp only [setBits, List.foldl] at *
    apply ih
    rw [Nat.testBit_or, h]; rfl

theorem setBits_sets (bs : List Nat) : ∀ acc b, b ∈ bs → (setBits acc bs).testBit b = true := by
  induction bs with
  | nil => intro _ _ h; cases h
  | cons c bs ih =>
    intro acc b h
    simp only [setBits, List.foldl] at *
    rcases List.mem_cons.mp h with h | h
    · subst h
      apply setBits_mono
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self]; simp
    · exact ih _ _ h

def bloomBits (probes : UInt64 → Nat → UInt64 → List Nat) (enc : Item K → UInt64)
    (salt : UInt64) (n : Nat) (acc : Nat) (xs : List (Item K)) : Nat :=
  xs.foldl (fun a x => setBits a (probes salt n (enc x))) acc

theorem bloomBits_mono (probes : UInt64 → Nat → UInt64 → List Nat) (enc : Item K → UInt64)
    (salt : UInt64) (n : Nat) (xs : List (Item K)) :
    ∀ acc i, acc.testBit i = true → (bloomBits probes enc salt n acc xs).testBit i = true := by
  induction xs with
  | nil => intro acc i h; simpa [bloomBits] using h
  | cons x xs ih =>
    intro acc i h
    simp only [bloomBits, List.foldl] at *
    exact ih _ _ (setBits_mono _ _ _ h)

theorem bloomBits_sets (probes : UInt64 → Nat → UInt64 → List Nat) (enc : Item K → UInt64)
    (salt : UInt64) (n : Nat) (xs : List (Item K)) :
    ∀ acc x b, x ∈ xs → b ∈ probes salt n (enc x) → (bloomBits probes enc salt n acc xs).testBit b = true := by
  induction xs with
  | nil => intro _ _ _ h; cases h
  | cons y xs ih =>
    intro acc x b hx hb
    simp only [bloomBits, List.foldl] at *
    rcases List.mem_cons.mp hx with h | h
    · subst h
      exact bloomBits_mono probes enc salt n xs _ _ (setBits_sets _ _ _ hb)
    · exact ih _ x b h hb

/-- A Bloom filter for the probe function `probes`, the item hash `enc`
and the size function `size` (the number of bits for a list of items). -/
def bloom (probes : UInt64 → Nat → UInt64 → List Nat) (enc : Item K → UInt64)
    (size : List (Item K) → Nat) : FilterImpl K where
  F := BloomF
  build := fun salt xs =>
    let n := size xs
    ⟨n, salt, bloomBits probes enc salt n 0 xs⟩
  mem := fun f x => (probes f.salt f.nbits (enc x)).all (fun b => f.bits.testBit b)
  noFalseNeg := by
    intro salt xs x hx
    simp only [List.all_eq_true]
    intro b hb
    exact bloomBits_sets probes enc salt (size xs) xs 0 x b hx hb

/-! ### The probe function, item hashes and size of the C code

These are bit-exact copies of `blame_mix`, `blame_item_line`,
`blame_item_pair`, `blame_filter_bit`, `blame_filter_set` and the size
rule of `blame_filter_build`.  The replay uses them to compare decisions
with the C code; the theorems do not depend on them. -/

def mix (x : UInt64) : UInt64 :=
  let x := x ^^^ (x >>> 33)
  let x := x * 0xff51afd7ed558ccd
  let x := x ^^^ (x >>> 33)
  let x := x * 0xc4ceb9fe1a85ec53
  x ^^^ (x >>> 33)

def cEnc : Item UInt64 → UInt64
  | .line h => mix (h ^^^ 0x9e3779b97f4a7c15)
  | .pair a b => mix (a * 0x9e3779b97f4a7c15 + b)

def cProbes (salt : UInt64) (nbits : Nat) (item : UInt64) : List Nat :=
  let x := mix (item ^^^ salt)
  let h1 : UInt32 := x.toUInt32
  let h2 : UInt32 := (x >>> 32).toUInt32 ||| 1
  [h1, h1 + h2, h1 + h2 + h2].map (fun h => (h.toNat * nbits) >>> 32)

/-- The number of distinct values of a list of hashes. -/
def distinctCount (xs : List UInt64) : Nat :=
  let s := (xs.map UInt64.toNat).mergeSort (· ≤ ·)
  let rec go : List Nat → Option Nat → Nat
    | [], _ => 0
    | y :: ys, none => 1 + go ys (some y)
    | y :: ys, some z => (if y = z then 0 else 1) + go ys (some y)
  go s none

def cSize (xs : List (Item UInt64)) : Nat :=
  let d := distinctCount (xs.map cEnc)
  let n := d * 10
  let n := if n < 64 then 64 else n
  let n := if n > 2 ^ 31 then 2 ^ 31 else n
  (n + 7) / 8 * 8

/-- The filter of the C code. -/
def cBloom : FilterImpl UInt64 := bloom cProbes cEnc cSize

end RB
