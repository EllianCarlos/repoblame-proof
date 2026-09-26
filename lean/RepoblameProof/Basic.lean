/-
  Basic objects of the copy search.

  C source: src/libgit2/blame_git.c at 3cbd497e5 (branch exp/repo-blame).
  See MAPPING.md for the line ranges.
-/
namespace RB

/-- What the copy search reads from a line: `key` is the hash of the line
without its newline (`blame_line_hash`), `alnum` is the number of ASCII
letters and digits of the line (the part of `blame_entry_score`). -/
structure LineView (L K : Type) where
  key   : L → K
  alnum : L → Nat

variable {L K : Type}

/-- `n` elements of `l` from index `t`. -/
def slice {α : Type} (l : List α) (t n : Nat) : List α := (l.drop t).take n

/-- The sum of the letters and digits of some lines. -/
def asum (lv : LineView L K) : List L → Nat
  | [] => 0
  | x :: xs => lv.alnum x + asum lv xs

/-- The score of an entry: 1 plus the letters and digits of its lines
(git's `ent_score`, libgit2's `blame_entry_score`). -/
def escore (lv : LineView L K) (ls : List L) : Nat := 1 + asum lv ls

/-- A run of lines that xdiff reports in common: `len` lines from line `t`
of the target (the lines of the blame entry) and from line `p` of the
source blob.  One call of `handle_split` with `tlno < same`. -/
structure Region where
  t : Nat
  p : Nat
  len : Nat
deriving DecidableEq, Repr, Inhabited

/-- The property of a diff that the filter needs: the lines of a common
run are equal in the two files, and the run is inside both files. -/
def Region.Valid (cand src : List L) (r : Region) : Prop :=
  1 ≤ r.len ∧ r.t + r.len ≤ cand.length ∧ r.p + r.len ≤ src.length ∧
  slice cand r.t r.len = slice src r.p r.len

/-- The score of the split that a region gives. -/
def rscore (lv : LineView L K) (cand : List L) (r : Region) : Nat :=
  escore lv (slice cand r.t r.len)

/-- A split: the source (its index in the list of sources) and the region.
In C, the three entries `split[0..2]` are a function of the entry, the
region and the origin of the source (`split_overlap`). -/
structure Split where
  src : Nat
  r : Region
deriving DecidableEq, Repr, Inhabited

/-- `copy_split_if_better`: keep the best split; a later split with the
same score wins. -/
def better (sc : Split → Nat) : Option Split → Option Split → Option Split
  | b, none => b
  | none, some p => some p
  | some b, some p => if sc p < sc b then some b else some p

/-- The potential split of one region (`handle_split`: only `tlno < same`). -/
def potOf (i : Nat) (r : Region) : Option Split :=
  if 1 ≤ r.len then some ⟨i, r⟩ else none

/-- `find_copy_in_blob`: the best split over the regions, in diff order. -/
def bestInBlob (sc : Split → Nat) (i : Nat) (regs : List Region) : Option Split :=
  regs.foldl (fun b r => better sc b (potOf i r)) none

/-! ### Lemmas -/

theorem better_none (sc : Split → Nat) (b : Option Split) : better sc b none = b := by
  cases b <;> rfl

theorem better_some_cases (sc : Split → Nat) (b : Option Split) (p : Split) :
    better sc b (some p) = some p ∨ (∃ x, b = some x ∧ sc p < sc x ∧ better sc b (some p) = some x) := by
  cases b with
  | none => exact Or.inl rfl
  | some x =>
    simp only [better]
    by_cases h : sc p < sc x
    · exact Or.inr ⟨x, rfl, h, by simp [h]⟩
    · exact Or.inl (by simp [h])

/-- A property of splits that `better` keeps. -/
theorem better_pres (sc : Split → Nat) (P : Split → Prop) (b q : Option Split)
    (hb : ∀ s, b = some s → P s) (hq : ∀ s, q = some s → P s) :
    ∀ s, better sc b q = some s → P s := by
  intro s hs
  cases q with
  | none => rw [better_none] at hs; exact hb s hs
  | some p =>
    rcases better_some_cases sc b p with h | ⟨x, hx, _, h⟩
    · rw [h] at hs; rw [← Option.some.inj hs]; exact hq p rfl
    · rw [h] at hs; rw [← Option.some.inj hs]; exact hb x hx

/-- If every region scores at most `bar`, the best split scores at most `bar`. -/
theorem bestInBlob_le (sc : Split → Nat) (i : Nat) (regs : List Region) (bar : Nat)
    (h : ∀ r ∈ regs, 1 ≤ r.len → sc ⟨i, r⟩ ≤ bar) :
    ∀ s, bestInBlob sc i regs = some s → sc s ≤ bar := by
  unfold bestInBlob
  suffices H : ∀ (b : Option Split), (∀ s, b = some s → sc s ≤ bar) →
      ∀ s, regs.foldl (fun b r => better sc b (potOf i r)) b = some s → sc s ≤ bar by
    exact H none (by intro s hs; cases hs)
  induction regs with
  | nil => intro b hb s hs; exact hb s hs
  | cons r rs ih =>
    intro b hb s hs
    simp only [List.foldl] at hs
    refine ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) _ ?_ s hs
    apply better_pres sc (fun s => sc s ≤ bar) b (potOf i r) hb
    intro s' hs'
    unfold potOf at hs'
    split at hs'
    · cases hs'; exact h r (List.mem_cons_self) (by assumption)
    · cases hs'

end RB
