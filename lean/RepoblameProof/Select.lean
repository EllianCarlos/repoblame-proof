/-
  The choice of the best split of one copy candidate over the sources.

  Reference: `find_best_copies_in_diff` (a fold of `copy_split_if_better`
  over all sources, in list order).
  Repoblame: `find_best_copies_in_list` (the same fold, but a source is
  skipped when the filter proves that it cannot score above `bar`).
-/
import RepoblameProof.Bound

namespace RB

/-- The split is above the threshold (`blame_entry_score > threshold`). -/
def hi (sc : Split → Nat) (thr : Nat) : Option Split → Bool
  | some x => decide (thr < sc x)
  | none => false

/-- What `find_copy_in_parent` does with the best split of a candidate: it
splits the entry only when the split scores above the threshold. -/
def accept (sc : Split → Nat) (thr : Nat) (o : Option Split) : Option Split :=
  if hi sc thr o then o else none

/-- The state of one candidate in `find_best_copies_in_list`:
`c->split` and `best[j]`. -/
structure OSt where
  best : Option Split
  bs : Nat
deriving Repr

/-- The bar of the pruning: `bar = threshold`, or `best[j] - 1` when the
candidate has a split and `best[j] > threshold` (a tie must stay). -/
def bar (thr : Nat) (st : OSt) : Nat :=
  if st.best.isSome && decide (thr < st.bs) then st.bs - 1 else thr

/-- `copy_split_if_better` when the potential split exists: the result
always exists. -/
def betterS (sc : Split → Nat) : Option Split → Split → Split
  | none, p => p
  | some b, p => if sc p < sc b then b else p

/-- One source for one candidate: `x.1 bar` is true when the search skips
the source (`prune && s->filtered && !blame_source_can_match(bar)`),
`x.2` is the split of `find_copy_in_blob` (computed only when it is not
skipped).  After `copy_split_if_better`, `best[j]` is the score of
`c->split[1]`. -/
def optStep (sc : Split → Nat) (thr : Nat) (st : OSt) (x : (Nat → Bool) × Option Split) : OSt :=
  if x.1 (bar thr st) then st else
  match x.2 with
  | none => st
  | some p => ⟨some (betterS sc st.best p), sc (betterS sc st.best p)⟩

/-- The reference fold. -/
def refFold (sc : Split → Nat) (ps : List (Option Split)) : Option Split :=
  ps.foldl (better sc) none

/-- The pruned fold. -/
def optFold (sc : Split → Nat) (thr : Nat) (xs : List ((Nat → Bool) × Option Split)) : Option Split :=
  (xs.foldl (optStep sc thr) ⟨none, 0⟩).best

/-- A skip is sound when the skipped split scores at most the bar. -/
def SkipSound (sc : Split → Nat) (x : (Nat → Bool) × Option Split) : Prop :=
  ∀ b, x.1 b = true → ∀ s, x.2 = some s → sc s ≤ b

/-! ### Proof -/

theorem better_some_eq (sc : Split → Nat) (b : Option Split) (p : Split) :
    better sc b (some p) = some (betterS sc b p) := by
  cases b with
  | none => rfl
  | some x => simp only [better, betterS]; split <;> rfl

theorem hi_betterS (sc : Split → Nat) (thr : Nat) (b : Option Split) (p : Split) :
    decide (thr < sc (betterS sc b p)) = (hi sc thr b || decide (thr < sc p)) := by
  cases b with
  | none => simp only [betterS, hi, Bool.false_or]; exact rfl
  | some x =>
    simp only [betterS, hi]
    by_cases h : sc p < sc x
    · simp only [h, ite_true]
      by_cases h2 : thr < sc x <;> by_cases h3 : thr < sc p <;> simp [h2, h3] <;> omega
    · simp only [h, ite_false]
      by_cases h2 : thr < sc x <;> by_cases h3 : thr < sc p <;> simp [h2, h3] <;> omega

theorem betterS_of_not_hi (sc : Split → Nat) (thr : Nat) (b : Option Split) (p : Split)
    (hb : hi sc thr b = false) (hp : thr < sc p) : betterS sc b p = p := by
  cases b with
  | none => rfl
  | some x =>
    simp only [hi, decide_eq_false_iff_not] at hb
    simp only [betterS]
    have : ¬ sc p < sc x := by omega
    simp [this]

/-- The simulation relation between the reference state and the pruned
state. -/
def Rel (sc : Split → Nat) (thr : Nat) (rb : Option Split) (ob : OSt) : Prop :=
  (hi sc thr rb = true → ob.best = rb) ∧
  (hi sc thr rb = false → hi sc thr ob.best = false) ∧
  (∀ y, ob.best = some y → ob.bs = sc y)

theorem rel_step (sc : Split → Nat) (thr : Nat) (rb : Option Split) (ob : OSt)
    (x : (Nat → Bool) × Option Split) (hx : SkipSound sc x) (hR : Rel sc thr rb ob) :
    Rel sc thr (better sc rb x.2) (optStep sc thr ob x) := by
  obtain ⟨h1, h2, h3⟩ := hR
  rcases x with ⟨pr, pot⟩
  cases pot with
  | none =>
    rw [better_none]
    unfold optStep
    simp only
    split <;> exact ⟨h1, h2, h3⟩
  | some p =>
    unfold optStep
    simp only
    rw [better_some_eq]
    have hnew : ∀ q : Split, (∀ y, some q = some y → sc q = sc y) := by
      intro q y hy; rw [Option.some.inj hy]
    by_cases hpr : pr (bar thr ob) = true
    · -- the source is skipped
      rw [ite_eq_left_iff.mpr (fun h => absurd hpr h)]
      have hle : sc p ≤ bar thr ob := hx _ hpr p rfl
      cases hrb : hi sc thr rb with
      | true =>
        have hob := h1 hrb
        cases rb with
        | none => simp [hi] at hrb
        | some r =>
          simp only [hi, decide_eq_true_eq] at hrb
          have hbs := h3 r hob
          have hbar : bar thr ob = sc r - 1 := by
            unfold bar; rw [hob, hbs]; simp [hrb]
          have hlt : sc p < sc r := by omega
          have hbet : betterS sc (some r) p = r := by simp [betterS, hlt]
          rw [hbet]
          refine ⟨fun _ => hob, fun h => ?_, h3⟩
          simp [hi, hrb] at h
      | false =>
        have hob := h2 hrb
        have hbar : bar thr ob = thr := by
          unfold bar
          cases hb : ob.best with
          | none => simp
          | some y =>
            rw [hb] at hob
            simp only [hi, decide_eq_false_iff_not] at hob
            have := h3 y hb
            simp [this, hob]
        rw [hbar] at hle
        have hhi : hi sc thr (some (betterS sc rb p)) = false := by
          simp only [hi]; rw [hi_betterS, hrb]; simp; omega
        refine ⟨fun h => ?_, fun _ => hob, h3⟩
        rw [hhi] at h; cases h
    · -- the source is compared
      rw [if_neg hpr]
      cases hrb : hi sc thr rb with
      | true =>
        have hob := h1 hrb
        rw [hob]
        refine ⟨fun _ => rfl, fun h => h, hnew _⟩
      | false =>
        have hob := h2 hrb
        by_cases hp : thr < sc p
        · rw [betterS_of_not_hi sc thr rb p hrb hp, betterS_of_not_hi sc thr ob.best p hob hp]
          exact ⟨fun _ => rfl, fun h => h, hnew _⟩
        · have hr' : hi sc thr (some (betterS sc rb p)) = false := by
            simp only [hi]; rw [hi_betterS, hrb]; simp; omega
          have ho' : hi sc thr (some (betterS sc ob.best p)) = false := by
            simp only [hi]; rw [hi_betterS, hob]; simp; omega
          refine ⟨fun h => ?_, fun _ => ho', hnew _⟩
          rw [hr'] at h; cases h

theorem rel_fold (sc : Split → Nat) (thr : Nat) (xs : List ((Nat → Bool) × Option Split))
    (hx : ∀ x ∈ xs, SkipSound sc x) :
    ∀ rb ob, Rel sc thr rb ob →
      Rel sc thr ((xs.map Prod.snd).foldl (better sc) rb) (xs.foldl (optStep sc thr) ob) := by
  induction xs with
  | nil => intro rb ob h; simpa using h
  | cons x xs ih =>
    intro rb ob h
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) _ _
      (rel_step sc thr rb ob x (hx x List.mem_cons_self) h)

/-- **Selection soundness.**  When each skip is sound (the skipped split
scores at most the bar), the pruned fold and the reference fold give the
same accepted split: the same split when the reference split scores
above the threshold, and no split otherwise.  The tie rule ("the last
source with the highest score wins") is kept. -/
theorem accept_optFold (sc : Split → Nat) (thr : Nat) (xs : List ((Nat → Bool) × Option Split))
    (hx : ∀ x ∈ xs, SkipSound sc x) :
    accept sc thr (optFold sc thr xs) = accept sc thr (refFold sc (xs.map Prod.snd)) := by
  have h0 : Rel sc thr none ⟨none, 0⟩ := ⟨fun h => by simp [hi] at h, fun _ => rfl, fun y hy => by cases hy⟩
  obtain ⟨h1, h2, _⟩ := rel_fold sc thr xs hx none ⟨none, 0⟩ h0
  unfold optFold refFold accept
  cases hr : hi sc thr ((xs.map Prod.snd).foldl (better sc) none) with
  | true => rw [h1 hr]; simp [hr]
  | false => rw [h2 hr]; simp

/-- Without a filter no source is skipped, and the pruned fold is the
reference fold (not only after `accept`). -/
theorem optFold_noskip (sc : Split → Nat) (thr : Nat) (ps : List (Option Split)) :
    optFold sc thr (ps.map (fun p => ((fun _ => false), p))) = refFold sc ps := by
  unfold optFold refFold
  suffices H : ∀ (b : Option Split) (n : Nat), (∀ y, b = some y → n = sc y) →
      ((ps.map (fun p => ((fun _ => false), p))).foldl (optStep sc thr) ⟨b, n⟩).best = ps.foldl (better sc) b by
    exact H none 0 (fun y hy => by cases hy)
  induction ps with
  | nil => intro b n _; rfl
  | cons p ps ih =>
    intro b n hn
    simp only [List.map_cons, List.foldl_cons]
    unfold optStep
    simp only [Bool.false_eq_true, if_false]
    cases p with
    | none =>
      simp only [better_none]
      exact ih b n hn
    | some q =>
      rw [better_some_eq]
      exact ih _ _ (fun y hy => by rw [Option.some.inj hy])

/-! ### The loop order of the C code

Both C functions loop over the sources outside and over the candidates
inside.  Each candidate has its own state, so this is the same as one
fold per candidate. -/

theorem foldl_map_comm {α β : Type} (f : α → β → α) :
    ∀ (srcs : List β) (cs : List α),
      srcs.foldl (fun cs s => cs.map (fun c => f c s)) cs = cs.map (fun c => srcs.foldl f c) := by
  intro srcs
  induction srcs with
  | nil => intro cs; simp
  | cons s ss ih => intro cs; simp [ih, List.map_map, Function.comp_def]

end RB
