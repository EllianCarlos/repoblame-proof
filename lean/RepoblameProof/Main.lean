/-
  The main theorems: repoblame gives the output of the reference blame,
  for each file, under any schedule of the files and threads.
-/
import RepoblameProof.Blame

namespace RB

variable {L K O C P D : Type} [DecidableEq O] [DecidableEq C] [DecidableEq P]
variable (R : Repo L K O C P D) (FI : FilterImpl K)

/-- **Hypothesis on xdiff.**  Each common run that xdiff reports between a
source blob and the lines of an entry is inside both files, and its lines
are equal.  (Any edit script has this property.) -/
def DiffValid : Prop :=
  ∀ src cand r, r ∈ R.diff src cand → 1 ≤ r.len → Region.Valid cand src r

theorem runPure_bind' {Q A α β : Type} (o : Q → A) (p : Prog Q A α) (f : α → Prog Q A β) :
    runPure o (Prog.bind p f) = runPure o (f (runPure o p)) := runPure_bind o p f

/-- When the check of the filter of `pb` says "no", the best split of `pb`
scores at most `t`. -/
theorem prune_sound (HD : DiffValid R) (ls pb : List L) (salt : UInt64) (t : Nat)
    (h : canMatch R.lv (FI.mem (FI.build salt (items R.lv pb))) t ls = false) (i : Nat) :
    ∀ s, bestInBlob (fun s => rscore R.lv ls s.r) i (R.diff pb ls) = some s → rscore R.lv ls s.r ≤ t :=
  bestInBlob_le _ i _ t (fun r hr hl => canMatch_false_le R.lv FI salt ls pb r (HD pb ls r hr hl) t h)

/-! ### The move filter -/

/-- **Move-filter soundness.**  The move search with the filter of the
parent blob gives the same scoreboard as the move search without it. -/
theorem moveLoop_filter (HD : DiffValid R) (FO : FileOps L O C P) (target po : O) (pb : List L)
    (salt : UInt64) : ∀ f sb i,
    moveLoop R FO (some (FI.mem (FI.build salt (items R.lv pb)))) target po pb f sb i =
    moveLoop R FO none target po pb f sb i := by
  intro f
  induction f with
  | zero => intro sb i; rfl
  | succ f ih =>
    intro sb i
    simp only [moveLoop]
    split
    · rfl
    · rename_i e _
      split
      · exact ih _ _
      · by_cases hp : pruneMove R (some (FI.mem (FI.build salt (items R.lv pb)))) R.thrM (entryLines FO e) = true
        · rw [if_pos hp]
          have hf : canMatch R.lv (FI.mem (FI.build salt (items R.lv pb))) R.thrM (entryLines FO e) = false := by
            simp only [pruneMove, Bool.not_eq_true'] at hp; exact hp
          have hno : pruneMove R (none : Option (Item K → Bool)) R.thrM (entryLines FO e) = false := rfl
          rw [hno]; simp only [Bool.false_eq_true, ite_false]
          split
          · rename_i s hs
            have := prune_sound R FI HD _ pb salt _ hf 0 s hs
            rw [if_neg (by omega)]
            exact ih _ _
          · exact ih _ _
        · rw [if_neg hp]
          have hno : pruneMove R (none : Option (Item K → Bool)) R.thrM (entryLines FO e) = false := rfl
          rw [hno]; simp only [Bool.false_eq_true, ite_false]
          split
          · split
            · exact ih _ _
            · exact ih _ _
          · exact ih _ _

/-! ### The walk is the same for equivalent kernels -/

def MoveEquiv (FO : FileOps L O C P) (K1 K2 : Kernel L O C P FI.F) : Prop :=
  ∀ target po pb f sb i,
    moveLoop R FO ((K1.moveFilter pb).map FI.mem) target po pb f sb i =
    moveLoop R FO ((K2.moveFilter pb).map FI.mem) target po pb f sb i

def SrcEquiv (o1 o2 : Ctx O C → List (Src L P FI.F)) (K1 K2 : Kernel L O C P FI.F) : Prop :=
  ∀ q, ((runPure o1 (K1.getSources q)).map (fun s => (s.path, s.blob)) =
        (runPure o2 (K2.getSources q)).map (fun s => (s.path, s.blob))) ∧
    ∀ ls, accept (fun s => rscore R.lv ls s.r) R.thrC (K1.select R.thrC ls (runPure o1 (K1.getSources q))) =
          accept (fun s => rscore R.lv ls s.r) R.thrC (K2.select R.thrC ls (runPure o2 (K2.getSources q)))

theorem moveAll_congr (FO : FileOps L O C P) (K1 K2 : Kernel L O C P FI.F) (h : MoveEquiv R FI FO K1 K2)
    (target : O) : ∀ ps sb, moveAll R FI FO K1 target ps sb = moveAll R FI FO K2 target ps sb := by
  intro ps
  induction ps with
  | nil => intro sb; rfl
  | cons x ps ih =>
    intro sb
    rcases x with ⟨p, po⟩
    cases po with
    | none => simp only [moveAll]; exact ih sb
    | some po =>
      simp only [moveAll]
      split
      · rfl
      · split
        · exact ih sb
        · rw [h]; exact ih _

theorem copyOne_congr (FO : FileOps L O C P) (K1 K2 : Kernel L O C P FI.F)
    (o1 o2 : Ctx O C → List (Src L P FI.F)) (h : SrcEquiv R FI o1 o2 K1 K2)
    (target : O) (p : C) (po : Option O) (sb : SB O) :
    runPure o1 (copyOne R FI FO K1 target p po sb) = runPure o2 (copyOne R FI FO K2 target p po sb) := by
  unfold copyOne
  split
  · rfl
  · rw [runPure_bind', runPure_bind']
    obtain ⟨h1, h2⟩ := h ⟨target, p, po⟩
    simp only [runPure_ret]
    rw [h1]
    have hc : (fun ls => accept (fun s => rscore R.lv ls s.r) R.thrC
                (K1.select R.thrC ls (runPure o1 (K1.getSources ⟨target, p, po⟩)))) =
              (fun ls => accept (fun s => rscore R.lv ls s.r) R.thrC
                (K2.select R.thrC ls (runPure o2 (K2.getSources ⟨target, p, po⟩)))) := funext h2
    rw [hc]

theorem copyAll_congr (FO : FileOps L O C P) (K1 K2 : Kernel L O C P FI.F)
    (o1 o2 : Ctx O C → List (Src L P FI.F)) (h : SrcEquiv R FI o1 o2 K1 K2) (target : O) :
    ∀ ps sb, runPure o1 (copyAll R FI FO K1 target ps sb) = runPure o2 (copyAll R FI FO K2 target ps sb) := by
  intro ps
  induction ps with
  | nil => intro sb; rfl
  | cons x ps ih =>
    intro sb
    rcases x with ⟨p, po⟩
    simp only [copyAll]
    rw [runPure_bind', runPure_bind', copyOne_congr R FI FO K1 K2 o1 o2 h]
    split
    · rfl
    · exact ih _

theorem passBlame_congr (FO : FileOps L O C P) (K1 K2 : Kernel L O C P FI.F)
    (o1 o2 : Ctx O C → List (Src L P FI.F)) (hm : MoveEquiv R FI FO K1 K2) (h : SrcEquiv R FI o1 o2 K1 K2)
    (o : O) (sb : SB O) :
    runPure o1 (passBlame R FI FO K1 o sb) = runPure o2 (passBlame R FI FO K2 o sb) := by
  unfold passBlame
  simp only [moveAll_congr R FI FO K1 K2 hm]
  repeat' split
  all_goals first | rfl | exact copyAll_congr R FI FO K1 K2 o1 o2 h _ _ _

theorem blame_congr (FO : FileOps L O C P) (K1 K2 : Kernel L O C P FI.F)
    (o1 o2 : Ctx O C → List (Src L P FI.F)) (hm : MoveEquiv R FI FO K1 K2) (h : SrcEquiv R FI o1 o2 K1 K2) :
    ∀ f sb, runPure o1 (blame R FI FO K1 f sb) = runPure o2 (blame R FI FO K2 f sb) := by
  intro f
  induction f with
  | zero => intro sb; rfl
  | succ f ih =>
    intro sb
    simp only [blame]
    split
    · rfl
    · rw [runPure_bind', runPure_bind', passBlame_congr R FI FO K1 K2 o1 o2 hm h]
      exact ih _

/-! ### The kernels of repoblame and of the reference are equivalent -/

theorem move_opt_ref (HD : DiffValid R) (FO : FileOps L O C P) : MoveEquiv R FI FO (optK R FI) (refK R FI) := by
  intro target po pb f sb i
  simp only [optK, refK]
  split
  · exact moveLoop_filter R FI HD FO target po pb 0 f sb i
  · rfl

def strip (s : Src L P FI.F) : Src L P FI.F := { s with filt := none }

theorem strip_canon (po : Option O) (key : CKey C) : ∀ ds : List D,
    (filterPo R FI po (ds.filterMap (mkSrc R FI key))).map (strip FI) = ds.filterMap (refSrc R FI po) := by
  intro ds
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.filterMap_cons]
    cases hd : R.oldSide d with
    | none =>
      have e1 : mkSrc R FI key d = none := by simp [mkSrc, hd]
      have e2 : refSrc R FI po d = none := by simp [refSrc, hd]
      rw [e1, e2]; exact ih
    | some t =>
      have e1 : mkSrc R FI key d = some ⟨t.1, t.2.1, t.2.2,
          if key.filters && R.small t.2.1 then some (FI.build t.2.2 (items R.lv t.2.1)) else none⟩ := by
        simp [mkSrc, hd]
      rw [e1]
      by_cases hn : notPo R po t.1 = true
      · have e2 : refSrc R FI po d = some ⟨t.1, t.2.1, t.2.2, none⟩ := by simp [refSrc, hd, hn]
        rw [e2]
        simp only [filterPo, List.filter_cons, hn, ite_true, List.map_cons]
        rw [← ih]; rfl
      · have e2 : refSrc R FI po d = none := by simp [refSrc, hd, hn]
        rw [e2]
        simp only [filterPo, List.filter_cons, hn]
        exact ih

theorem canon_filt (key : CKey C) (s : Src L P FI.F) (hs : s ∈ canon R FI key) :
    s.filt = none ∨ s.filt = some (FI.build s.salt (items R.lv s.blob)) := by
  unfold canon at hs
  obtain ⟨d, _, hd⟩ := List.mem_filterMap.mp hs
  unfold mkSrc at hd
  cases h : R.oldSide d with
  | none => rw [h] at hd; cases hd
  | some t =>
    rw [h] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    simp only
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem imap_go_mem {α β : Type} (f : Nat → α → β) (x : β) :
    ∀ (l : List α) (i : Nat), x ∈ imap.go f i l → ∃ j a, a ∈ l ∧ x = f j a := by
  intro l
  induction l with
  | nil => intro i h; cases h
  | cons a l ih =>
    intro i h
    simp only [imap.go, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨i, a, List.mem_cons_self, h⟩
    · obtain ⟨j, b, hb, hx⟩ := ih (i + 1) h
      exact ⟨j, b, List.mem_cons_of_mem _ hb, hx⟩

theorem imap_go_map {α β γ : Type} (f : Nat → α → β) (g : β → γ) :
    ∀ (l : List α) (i : Nat), (imap.go f i l).map g = imap.go (fun j a => g (f j a)) i l := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons a l ih => intro i; simp [imap.go, ih]

theorem imap_go_comp {α α' β : Type} (f : Nat → α' → β) (g : α → α') :
    ∀ (l : List α) (i : Nat), imap.go f i (l.map g) = imap.go (fun j a => f j (g a)) i l := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons a l ih => intro i; simp [imap.go, ih]

theorem src_opt_ref (HD : DiffValid R) (o2 : Ctx O C → List (Src L P FI.F)) :
    SrcEquiv R FI (oracle R FI) o2 (optK R FI) (refK R FI) := by
  intro q
  have hopt : runPure (oracle R FI) ((optK R FI).getSources q) = filterPo R FI q.po (canon R FI (keyOf R q)) := rfl
  have href : runPure o2 ((refK R FI).getSources q) = refSources R FI q := rfl
  have hstrip : (filterPo R FI q.po (canon R FI (keyOf R q))).map (strip FI) = refSources R FI q :=
    strip_canon R FI q.po (keyOf R q) _
  rw [hopt, href, ← hstrip]
  refine ⟨by simp [List.map_map, Function.comp_def, strip], fun ls => ?_⟩
  -- the reference selection only reads the blobs
  have hsel : (refK R FI).select R.thrC ls ((filterPo R FI q.po (canon R FI (keyOf R q))).map (strip FI)) =
      refSel R FI R.thrC ls (filterPo R FI q.po (canon R FI (keyOf R q))) := by
    simp only [refK, refSel, imap]
    rw [imap_go_comp]; rfl
  rw [hsel]
  simp only [optK, optSel, refSel]
  have hsnd := imap_go_map (fun i s => (pruneSrc R FI ls s,
      bestInBlob (fun s => rscore R.lv ls s.r) i (R.diff s.blob ls))) Prod.snd
      (filterPo R FI q.po (canon R FI (keyOf R q))) 0
  simp only [imap]
  rw [← hsnd]
  apply accept_optFold
  intro x hx b hb s hs
  obtain ⟨j, a, ha, rfl⟩ := imap_go_mem _ x _ 0 hx
  have ha' : a ∈ canon R FI (keyOf R q) := (List.mem_filter.mp ha).1
  simp only at hb hs
  unfold pruneSrc at hb
  rcases canon_filt R FI _ a ha' with hf | hf
  · rw [hf] at hb; cases hb
  · rw [hf] at hb
    simp only [Bool.not_eq_true'] at hb
    exact prune_sound R FI HD ls a.blob a.salt b hb j s hs

/-! ### Main theorems -/

/-- **Main theorem (one file).**  For every file, every scoreboard and
every fuel, the blame with the repoblame kernel, when each question gets
the canonical list of its key, gives the same scoreboard as the reference
blame.  The only hypothesis is `DiffValid` (and the no-false-negative
property that every `FilterImpl` carries). -/
theorem repoblame_eq_reference (HD : DiffValid R) (FO : FileOps L O C P)
    (o2 : Ctx O C → List (Src L P FI.F)) (fuel : Nat) (sb : SB O) :
    runPure (oracle R FI) (blame R FI FO (optK R FI) fuel sb) =
    runPure o2 (blame R FI FO (refK R FI) fuel sb) :=
  blame_congr R FI FO _ _ _ _ (move_opt_ref R FI HD FO) (src_opt_ref R FI HD o2) fuel sb

/-- The reference asks no question: its value does not depend on the oracle. -/
theorem reference_oracle_free (FO : FileOps L O C P) (o1 o2 : Ctx O C → List (Src L P FI.F))
    (fuel : Nat) (sb : SB O) :
    runPure o1 (blame R FI FO (refK R FI) fuel sb) = runPure o2 (blame R FI FO (refK R FI) fuel sb) :=
  blame_congr R FI FO (refK R FI) (refK R FI) o1 o2 (fun _ _ _ _ _ _ => rfl) (fun _ => ⟨rfl, fun _ => rfl⟩) fuel sb

/-- **Main theorem (whole repository, any schedule).**  Blame many files
(`FO i`, start scoreboard `sb0 i`) with repoblame and one shared cache
that starts empty.  In every run of the cache machine (any order of the
files, any interleaving of the threads, any evictions, any failed list
builds), each blame that ends returns the scoreboard of the reference
blame of its file. -/
theorem repoblame_any_schedule (HD : DiffValid R) (FO : Nat → FileOps L O C P) (fuel : Nat)
    (sb0 : Nat → SB O) (cf : Conf (CKey C) (Ctx O C) (List (Src L P FI.F)) (SB O))
    (hrun : Star (Step (keyOf R) (buildC R FI))
      ⟨[], fun i => .run (blame R FI (FO i) (optK R FI) fuel (sb0 i))⟩ cf)
    (i : Nat) (v : SB O) (hfin : cf.jobs i = .run (.ret v)) :
    v = runPure (fun _ => []) (blame R FI (FO i) (refK R FI) fuel (sb0 i)) := by
  have h := cache_sound (canon R FI) (keyOf R) (buildC R FI) (buildC_eq_canon R FI)
    (fun i => blame R FI (FO i) (optK R FI) fuel (sb0 i)) [] (valid_nil _) cf hrun i v hfin
  rw [h]
  exact repoblame_eq_reference R FI HD (FO i) _ fuel (sb0 i)

end RB
