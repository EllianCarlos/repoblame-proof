/-
  The shared cache of the copy sources (`blame_cache_sources`,
  `blame_source_list_build`, `blame_cache_evict`, `blame_cache_release`)
  and a model of many blames that use it at the same time.

  A blame is a program that asks for source lists (`Prog`).  The reference
  answers each question with the canonical list; the cache answers from
  its map, or makes the list and publishes it.  Threads interleave at the
  sections that hold the mutex.
-/
namespace RB

/-- A program that asks questions of type `Q` and gets answers of type `A`. -/
inductive Prog (Q A α : Type) where
  | ret : α → Prog Q A α
  | ask : Q → (A → Prog Q A α) → Prog Q A α

namespace Prog

variable {Q A α β : Type}

def bind : Prog Q A α → (α → Prog Q A β) → Prog Q A β
  | ret a, f => f a
  | ask q k, f => ask q (fun a => bind (k a) f)

instance : Monad (Prog Q A) where
  pure := ret
  bind := bind

end Prog

variable {Q A α Key : Type}

/-- Run a program with a pure oracle. -/
def runPure (o : Q → A) : Prog Q A α → α
  | .ret a => a
  | .ask q k => runPure o (k (o q))

@[simp] theorem runPure_ret (o : Q → A) (a : α) : runPure o (Prog.ret a) = a := rfl
@[simp] theorem runPure_ask (o : Q → A) (q : Q) (k : A → Prog Q A α) :
    runPure o (Prog.ask q k) = runPure o (k (o q)) := rfl
@[simp] theorem runPure_pure (o : Q → A) (a : α) : runPure o (pure a : Prog Q A α) = a := rfl

theorem runPure_bind {β : Type} (o : Q → A) (p : Prog Q A α) (f : α → Prog Q A β) :
    runPure o (p >>= f) = runPure o (f (runPure o p)) := by
  show runPure o (Prog.bind p f) = _
  induction p with
  | ret a => rfl
  | ask q k ih => exact ih (o q)

/-! ### The cache machine -/

/-- A map entry: `building` is the placeholder of a list that one blame
makes now (`ready == false`); `ready a` is a list that does not change. -/
inductive Slot (A : Type) where
  | building
  | ready (a : A)

abbrev Cache (Key A : Type) := List (Key × Slot A)

def lookup [DecidableEq Key] : Cache Key A → Key → Option (Slot A)
  | [], _ => none
  | (k', s) :: c, k => if k' = k then some s else lookup c k

def publish [DecidableEq Key] (c : Cache Key A) (k : Key) (a : A) : Cache Key A :=
  c.map (fun e => if e.1 = k then (k, Slot.ready a) else e)

def removeKey [DecidableEq Key] (c : Cache Key A) (k : Key) : Cache Key A :=
  c.filter (fun e => !(decide (e.1 = k)))

/-- A blame: it runs, or it makes a list (outside the lock), or it failed. -/
inductive Job (Q A α : Type) where
  | run : Prog Q A α → Job Q A α
  | build : Q → (A → Prog Q A α) → Job Q A α
  | failed : Job Q A α

structure Conf (Key Q A α : Type) where
  cache : Cache Key A
  jobs : Nat → Job Q A α

def upd {β : Type} (f : Nat → β) (i : Nat) (b : β) : Nat → β := fun j => if j = i then b else f j

/-- One atomic step.  `keyOf` gives the key of a question (the commit, the
parent and the two flags); `bld` makes the list from the question.  The
scheduler chooses the job and the step; eviction removes any entries. -/
inductive Step [DecidableEq Key] (keyOf : Q → Key) (bld : Q → A) :
    Conf Key Q A α → Conf Key Q A α → Prop
  | hit (c : Cache Key A) (js : Nat → Job Q A α) (i : Nat) (q : Q) (k : A → Prog Q A α) (a : A) :
      js i = .run (.ask q k) → lookup c (keyOf q) = some (.ready a) →
      Step keyOf bld ⟨c, js⟩ ⟨c, upd js i (.run (k a))⟩
  | miss (c : Cache Key A) (js : Nat → Job Q A α) (i : Nat) (q : Q) (k : A → Prog Q A α) :
      js i = .run (.ask q k) → lookup c (keyOf q) = none →
      Step keyOf bld ⟨c, js⟩ ⟨(keyOf q, .building) :: c, upd js i (.build q k)⟩
  | done (c : Cache Key A) (js : Nat → Job Q A α) (i : Nat) (q : Q) (k : A → Prog Q A α) :
      js i = .build q k →
      Step keyOf bld ⟨c, js⟩ ⟨publish c (keyOf q) (bld q), upd js i (.run (k (bld q)))⟩
  | fail (c : Cache Key A) (js : Nat → Job Q A α) (i : Nat) (q : Q) (k : A → Prog Q A α) :
      js i = .build q k →
      Step keyOf bld ⟨c, js⟩ ⟨removeKey c (keyOf q), upd js i .failed⟩
  | evict (c c' : Cache Key A) (js : Nat → Job Q A α) :
      (∀ e ∈ c', e ∈ c) → Step keyOf bld ⟨c, js⟩ ⟨c', js⟩

inductive Star {β : Type} (R : β → β → Prop) : β → β → Prop
  | refl (x : β) : Star R x x
  | tail {x y z : β} : Star R x y → R y z → Star R x z

/-- Every ready list in the cache is the canonical list of its key. -/
def Valid (o : Key → A) (c : Cache Key A) : Prop := ∀ k a, (k, Slot.ready a) ∈ c → a = o k

def JobOk (o' : Q → A) (P : Prog Q A α) : Job Q A α → Prop
  | .run p => runPure o' p = runPure o' P
  | .build q k => runPure o' (k (o' q)) = runPure o' P
  | .failed => True

def Good (o : Key → A) (keyOf : Q → Key) (P : Nat → Prog Q A α) (cf : Conf Key Q A α) : Prop :=
  Valid o cf.cache ∧ ∀ i, JobOk (fun q => o (keyOf q)) (P i) (cf.jobs i)

theorem lookup_mem [DecidableEq Key] : ∀ (c : Cache Key A) (k : Key) (s : Slot A),
    lookup c k = some s → (k, s) ∈ c
  | [], _, _, h => by simp [lookup] at h
  | (k', s') :: c, k, s, h => by
    simp only [lookup] at h
    split at h
    · rename_i hk; subst hk; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem c k s h)

theorem step_good [DecidableEq Key] (o : Key → A) (keyOf : Q → Key) (bld : Q → A)
    (hbld : ∀ q, bld q = o (keyOf q)) (P : Nat → Prog Q A α)
    (x y : Conf Key Q A α) (hs : Step keyOf bld x y) (hg : Good o keyOf P x) : Good o keyOf P y := by
  obtain ⟨hv, hj⟩ := hg
  cases hs with
  | hit c js i q k a hji hl =>
    refine ⟨hv, fun j => ?_⟩
    simp only [upd]
    split
    · rename_i h; subst h
      have hji' : JobOk (fun q => o (keyOf q)) (P j) (js j) := hj j; rw [hji] at hji'
      simp only [JobOk, runPure_ask] at hji' ⊢
      rw [hv _ a (lookup_mem c _ _ hl)]; exact hji'
    · exact hj j
  | miss c js i q k hji _ =>
    refine ⟨?_, fun j => ?_⟩
    · intro k' a hm
      rcases List.mem_cons.mp hm with h | h
      · cases h
      · exact hv k' a h
    · simp only [upd]
      split
      · rename_i h; subst h
        have hji' : JobOk (fun q => o (keyOf q)) (P j) (js j) := hj j; rw [hji] at hji'
        simp only [JobOk, runPure_ask] at hji' ⊢
        exact hji'
      · exact hj j
  | done c js i q k hji =>
    refine ⟨?_, fun j => ?_⟩
    · intro k' a hm
      simp only [publish, List.mem_map] at hm
      obtain ⟨e, he, heq⟩ := hm
      split at heq
      · cases heq; exact hbld q
      · rw [heq] at he; exact hv k' a he
    · simp only [upd]
      split
      · rename_i h; subst h
        have hji' : JobOk (fun q => o (keyOf q)) (P j) (js j) := hj j; rw [hji] at hji'
        simp only [JobOk] at hji' ⊢
        rw [hbld q]; exact hji'
      · exact hj j
  | fail c js i q k _ =>
    refine ⟨?_, fun j => ?_⟩
    · intro k' a hm
      simp only [removeKey, List.mem_filter] at hm
      exact hv k' a hm.1
    · simp only [upd]
      split
      · simp [JobOk]
      · exact hj j
  | evict c c' js hsub =>
    exact ⟨fun k' a hm => hv k' a (hsub _ hm), hj⟩

theorem star_good [DecidableEq Key] (o : Key → A) (keyOf : Q → Key) (bld : Q → A)
    (hbld : ∀ q, bld q = o (keyOf q)) (P : Nat → Prog Q A α)
    (x y : Conf Key Q A α) (hs : Star (Step keyOf bld) x y) (hg : Good o keyOf P x) :
    Good o keyOf P y := by
  induction hs with
  | refl => exact hg
  | tail _ hstep ih => exact step_good o keyOf bld hbld P _ _ hstep ih

/-- **Cache soundness under any schedule.**  Suppose that the list a blame
makes for a question depends only on the key of the question
(`hbld`), and that the cache starts valid (for example empty).  Then in
every run of the machine (any interleaving of the blames, any evictions,
any failed builds), each blame that ends returns the value of its
program under the canonical oracle: the value that it has without a
cache.  The value does not depend on the schedule, on the other files,
or on the state of the cache. -/
theorem cache_sound [DecidableEq Key] (o : Key → A) (keyOf : Q → Key) (bld : Q → A)
    (hbld : ∀ q, bld q = o (keyOf q)) (P : Nat → Prog Q A α)
    (c0 : Cache Key A) (h0 : Valid o c0) (cf : Conf Key Q A α)
    (hrun : Star (Step keyOf bld) ⟨c0, fun i => .run (P i)⟩ cf)
    (i : Nat) (v : α) (hfin : cf.jobs i = .run (.ret v)) :
    v = runPure (fun q => o (keyOf q)) (P i) := by
  have hg : Good o keyOf P ⟨c0, fun i => .run (P i)⟩ := ⟨h0, fun i => rfl⟩
  have := (star_good o keyOf bld hbld P _ _ hrun hg).2 i
  rw [hfin] at this
  simpa [JobOk] using this

theorem valid_nil (o : Key → A) : Valid o ([] : Cache Key A) := by
  intro k a h; cases h

end RB
