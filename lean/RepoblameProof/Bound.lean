/-
  The upper bound of the copy search (`blame_source_can_match`) and its
  soundness: when a region scores above `t`, the check says "can match".
-/
import RepoblameProof.Filter

namespace RB

variable {L K : Type}

/-- The state of the scan in `blame_source_can_match`: the previous line,
`run` (the letters and digits of the current run) and `run_len`. -/
structure ScanSt (L : Type) where
  prev : Option L
  run : Nat
  len : Nat

/-- One step of the loop: continue the run when the pair of the previous
line and this line can be in the filter, else start a new run. -/
def scanStep (lv : LineView L K) (mem : Item K → Bool) (st : ScanSt L) (x : L) : ScanSt L :=
  match st.prev with
  | some p =>
    if 0 < st.len && mem (Item.pair (lv.key p) (lv.key x)) then ⟨some x, st.run + lv.alnum x, st.len + 1⟩
    else ⟨some x, lv.alnum x, 1⟩
  | none => ⟨some x, lv.alnum x, 1⟩

/-- The two tests of the loop body that return true. -/
def scanHit (lv : LineView L K) (mem : Item K → Bool) (t : Nat) (st : ScanSt L) (x : L) : Bool :=
  (decide (2 ≤ st.len) && decide (t < 1 + st.run)) ||
  (decide (st.len = 1) && decide (t < 1 + lv.alnum x) && mem (Item.line (lv.key x)))

def scan (lv : LineView L K) (mem : Item K → Bool) (t : Nat) : ScanSt L → List L → Bool
  | _, [] => false
  | st, x :: xs =>
    let st' := scanStep lv mem st x
    scanHit lv mem t st' x || scan lv mem t st' xs

/-- `blame_source_can_match(s, l, threshold)`: false means that no split of
the lines `cand` against the source can score above `t`. -/
def canMatch (lv : LineView L K) (mem : Item K → Bool) (t : Nat) (cand : List L) : Bool :=
  if t < lineScoreMin then true else scan lv mem t ⟨none, 0, 0⟩ cand

/-! ### Lemmas on the scan -/

theorem scanStep_props (lv : LineView L K) (mem : Item K → Bool) (st : ScanSt L) (x : L) :
    (scanStep lv mem st x).prev = some x ∧ 1 ≤ (scanStep lv mem st x).len ∧
    lv.alnum x ≤ (scanStep lv mem st x).run := by
  unfold scanStep
  cases st.prev with
  | none => simp
  | some p =>
    simp only
    split <;> simp <;> omega

theorem asum_append (lv : LineView L K) (a b : List L) : asum lv (a ++ b) = asum lv a + asum lv b := by
  induction a with
  | nil => simp [asum]
  | cons x xs ih => simp [asum, ih]; omega

theorem pairItems_cons_sub (key : L → K) (a b : L) (l : List L) (z : Item K)
    (h : z ∈ pairItems key (b :: l)) : z ∈ pairItems key (a :: b :: l) := by
  simp only [pairItems]; exact List.mem_cons_of_mem _ h

theorem scan_append_true (lv : LineView L K) (mem : Item K → Bool) (t : Nat) (rest : List L)
    (hr : ∀ st, scan lv mem t st rest = true) :
    ∀ (pre : List L) st, scan lv mem t st (pre ++ rest) = true := by
  intro pre
  induction pre with
  | nil => intro st; exact hr st
  | cons x xs ih => intro st; simp [scan, ih]

/-- A run that continues from a previous line `p`. -/
theorem scan_run_extend (lv : LineView L K) (mem : Item K → Bool) (t : Nat) (post : List L) :
    ∀ (seg : List L) (st : ScanSt L) (p : L) (acc : Nat),
      st.prev = some p → 1 ≤ st.len → acc ≤ st.run →
      (∀ y ∈ pairItems lv.key (p :: seg), mem y = true) →
      seg ≠ [] → t < 1 + acc + asum lv seg →
      scan lv mem t st (seg ++ post) = true := by
  intro seg
  induction seg with
  | nil => intro _ _ _ _ _ _ _ h; exact absurd rfl h
  | cons x rest ih =>
    intro st p acc hprev hlen hacc hpairs _ hscore
    have hpx : mem (Item.pair (lv.key p) (lv.key x)) = true := hpairs _ (by simp [pairItems])
    have hstep : scanStep lv mem st x = ⟨some x, st.run + lv.alnum x, st.len + 1⟩ := by
      unfold scanStep; rw [hprev]; simp only
      have : (0 < st.len) = True := by simp; omega
      simp [hpx]; omega
    simp only [List.cons_append, scan, hstep]
    cases rest with
    | nil =>
      simp only [asum] at hscore
      simp [scanHit]; omega
    | cons y ys =>
      have := ih ⟨some x, st.run + lv.alnum x, st.len + 1⟩ x (acc + lv.alnum x) rfl (by simp)
        (by simp; omega) (by intro z hz; exact hpairs z (pairItems_cons_sub _ _ _ _ _ hz))
        (by simp) (by simp only [asum] at hscore ⊢; omega)
      rw [List.cons_append] at this
      simp [this]

/-- A run that starts at `x`. -/
theorem scan_run_start (lv : LineView L K) (mem : Item K → Bool) (t : Nat) (post : List L)
    (x : L) (rest : List L) (st : ScanSt L)
    (hpairs : ∀ y ∈ pairItems lv.key (x :: rest), mem y = true)
    (hsingle : rest = [] → t < 1 + lv.alnum x ∧ mem (Item.line (lv.key x)) = true)
    (hscore : t < 1 + asum lv (x :: rest)) :
    scan lv mem t st ((x :: rest) ++ post) = true := by
  obtain ⟨hp, hl, hr⟩ := scanStep_props lv mem st x
  simp only [List.cons_append, scan]
  cases rest with
  | nil =>
    obtain ⟨h1, h2⟩ := hsingle rfl
    simp only [scanHit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h : (scanStep lv mem st x).len = 1
    · exact Or.inl (Or.inr ⟨⟨h, h1⟩, h2⟩)
    · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
  | cons y ys =>
    have := scan_run_extend lv mem t post (y :: ys) (scanStep lv mem st x) x (lv.alnum x) hp hl hr
      hpairs (by simp)
      (by simp only [asum] at hscore ⊢; omega)
    rw [List.cons_append] at this
    simp [this]


/-! ### Items of a part of a blob -/

theorem pairItems_append_left (key : L → K) (v : List L) (z : Item K) :
    ∀ u : List L, z ∈ pairItems key u → z ∈ pairItems key (u ++ v) := by
  intro u
  induction u with
  | nil => intro h; simp [pairItems] at h
  | cons a u' ih =>
    intro h
    cases u' with
    | nil => simp [pairItems] at h
    | cons b r =>
      simp only [pairItems, List.mem_cons] at h
      simp only [List.cons_append, pairItems, List.mem_cons]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by have := ih h; simpa using this)

theorem pairItems_append_right (key : L → K) (v : List L) (z : Item K) (hv : z ∈ pairItems key v) :
    ∀ u : List L, z ∈ pairItems key (u ++ v) := by
  intro u
  induction u with
  | nil => simpa using hv
  | cons a u' ih =>
    simp only [List.cons_append]
    cases h : u' ++ v with
    | nil => rw [h] at ih; simp [pairItems] at ih
    | cons b r => rw [h] at ih; simp only [pairItems]; exact List.mem_cons_of_mem _ ih

theorem slice_decomp {α : Type} (l : List α) (t n : Nat) :
    l = l.take t ++ (slice l t n ++ (l.drop t).drop n) := by
  simp only [slice, List.take_append_drop]

theorem mem_of_mem_slice {α : Type} {l : List α} {t n : Nat} {x : α} (h : x ∈ slice l t n) : x ∈ l :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem pairItems_slice (key : L → K) (l : List L) (t n : Nat) (z : Item K)
    (h : z ∈ pairItems key (slice l t n)) : z ∈ pairItems key l := by
  rw [slice_decomp l t n]
  exact pairItems_append_right key _ z (pairItems_append_left key _ z _ h) _

theorem length_slice {α : Type} (l : List α) (t n : Nat) (h : t + n ≤ l.length) :
    (slice l t n).length = n := by
  simp [slice]; omega

/-! ### Soundness of the bound -/

/-- **Bound soundness.**  If xdiff reports a valid region of the entry
lines `cand` against the source `src` that scores above `t`, then
`blame_source_can_match` with the filter of `src` returns true.  Thus a
"false" answer proves that no split of this source scores above `t`.
The only property of the filter that the proof uses is `noFalseNeg`. -/
theorem canMatch_sound (lv : LineView L K) (FI : FilterImpl K) (salt : UInt64)
    (cand src : List L) (r : Region) (hv : r.Valid cand src) (t : Nat)
    (ht : t < rscore lv cand r) :
    canMatch lv (FI.mem (FI.build salt (items lv src))) t cand = true := by
  obtain ⟨hlen, htb, hpb, heq⟩ := hv
  unfold canMatch
  split
  · rfl
  · rename_i h16
    have hseg_len : (slice cand r.t r.len).length = r.len := length_slice cand r.t r.len htb
    rw [slice_decomp cand r.t r.len]
    apply scan_append_true
    intro st
    unfold rscore escore at ht
    have hmem : ∀ y, y ∈ items lv src → FI.mem (FI.build salt (items lv src)) y = true :=
      fun y hy => FI.noFalseNeg salt _ y hy
    generalize hs : slice cand r.t r.len = seg at hseg_len ht ⊢
    cases seg with
    | nil => simp at hseg_len; omega
    | cons x rest =>
      apply scan_run_start lv _ t _ x rest st
      · intro y hy
        apply hmem
        unfold items
        apply List.mem_append_right
        rw [← hs, heq] at hy
        exact pairItems_slice lv.key src r.p r.len y hy
      · intro hrest
        subst hrest
        simp only [asum] at ht
        refine ⟨by omega, ?_⟩
        apply hmem
        unfold items lineItems
        apply List.mem_append_left
        apply List.mem_map.mpr
        refine ⟨x, ?_, rfl⟩
        apply List.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · have hx : x ∈ slice cand r.t r.len := by rw [hs]; simp
          rw [heq] at hx
          exact mem_of_mem_slice hx
        · simp only [lineScoreMin] at h16 ⊢; exact decide_eq_true (by omega)
      · exact ht

/-- The contrapositive, as the search uses it: when the check says "no",
every region of this source scores at most `t`. -/
theorem canMatch_false_le (lv : LineView L K) (FI : FilterImpl K) (salt : UInt64)
    (cand src : List L) (r : Region) (hv : r.Valid cand src) (t : Nat)
    (hno : canMatch lv (FI.mem (FI.build salt (items lv src))) t cand = false) :
    rscore lv cand r ≤ t := by
  have := canMatch_sound lv FI salt cand src r hv t
  apply Nat.le_of_not_lt
  intro h
  have h2 := this h
  rw [hno] at h2; cases h2

end RB
