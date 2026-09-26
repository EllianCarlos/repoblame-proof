/-
  The blame of one file (`git_blame__like_git`, `pass_blame`,
  `find_move_in_parent`, `find_copy_in_parent`), written once, with a
  kernel that is either the reference (no cache: `find_best_copies_in_diff`,
  no move filter) or repoblame (`blame_cache_sources`,
  `find_best_copies_in_list`, the move filter).

  All parts that repoblame does not change are parameters (`Repo`,
  `FileOps`): the history, `find_origin`, `find_rename`,
  `pass_blame_to_parent`, `split_blame`, `coalesce`, and xdiff.  The two
  semantics use the same parameters.
-/
import RepoblameProof.Select
import RepoblameProof.Cache

namespace RB

variable {L K O C P D : Type} [DecidableEq O] [DecidableEq C] [DecidableEq P]

/-- A blame entry (`git_blame__entry`). -/
structure Entry (O : Type) where
  lno : Nat
  n : Nat
  slno : Nat
  suspect : O
  guilty : Bool

abbrev SB (O : Type) := List (Entry O)

/-- A copy source (`blame_source`): path, blob, salt and filter. -/
structure Src (L P F : Type) where
  path : P
  blob : List L
  salt : UInt64
  filt : Option F

/-- The key of the cache (`blame_cache_sources`): "commit parent u|m f|n". -/
structure CKey (C : Type) where
  commit : C
  parent : C
  unmod : Bool
  filters : Bool
deriving DecidableEq

/-- The question of a copy search: the target origin, the parent commit,
and the origin in the parent (`porigin`, or none). -/
structure Ctx (O C : Type) where
  target : O
  parent : C
  po : Option O

/-- The data of the repository.  All blames of a run share it. -/
structure Repo (L K O C P D : Type) where
  lv : LineView L K
  thrM : Nat                     -- blame_move_score
  thrC : Nat                     -- blame_copy_score
  moves : Bool                   -- GIT_BLAME_TRACK_COPIES_SAME_FILE
  copies : Bool                  -- GIT_BLAME_TRACK_COPIES_SAME_COMMIT_MOVES (or more)
  ignoreWs : Bool                -- GIT_BLAME_IGNORE_WHITESPACE
  commitOf : O → C
  pathOf : O → P
  blobOf : O → Option (List L)
  unmodFlag : O → Option O → Bool          -- the GIT_DIFF_INCLUDE_UNMODIFIED decision
  deltas : C → C → Bool → List D           -- git_diff_tree_to_tree(parent, commit), in order
  oldSide : D → Option (P × List L × UInt64) -- is_copy_source(delta, NULL): path, blob, salt
  small : List L → Bool                    -- size <= GIT_XDIFF_MAX_SIZE
  diff : List L → List L → List Region     -- xdiff (source, target): the common runs

/-- The parts of the blame of one file that repoblame does not change. -/
structure FileOps (L O C P : Type) where
  final : List L
  passParents : SB O → O → List (C × Option O) × SB O × Bool
  splitMove : SB O → Nat → O → Split → SB O
  applyCopies : SB O → C → List (Entry O × Option Split) → List (P × List L) → SB O × List (Entry O)
  coalesce : SB O → SB O
  fuelMove : Nat
  fuelRounds : Nat

variable (R : Repo L K O C P D) (FI : FilterImpl K)

/-- What differs between the two semantics. -/
structure Kernel (L O C P F : Type) where
  moveFilter : List L → Option F
  getSources : Ctx O C → Prog (Ctx O C) (List (Src L P F)) (List (Src L P F))
  select : Nat → List L → List (Src L P F) → Option Split

def entryLines (FO : FileOps L O C P) (e : Entry O) : List L := slice FO.final e.lno e.n

/-! ### The move search (`find_move_in_parent`) -/

def pruneMove (mem? : Option (Item K → Bool)) (t : Nat) (ls : List L) : Bool :=
  match mem? with
  | none => false
  | some m => !canMatch R.lv m t ls

def moveLoop (FO : FileOps L O C P) (mem? : Option (Item K → Bool)) (target po : O) (pb : List L) :
    Nat → SB O → Nat → SB O
  | 0, sb, _ => sb
  | f + 1, sb, i =>
    match sb[i]? with
    | none => sb
    | some e =>
      let ls := entryLines FO e
      if e.guilty || !(decide (e.suspect = target)) || decide (escore R.lv ls ≤ R.thrM) then
        moveLoop FO mem? target po pb f sb (i + 1)
      else if pruneMove R mem? R.thrM ls then
        moveLoop FO mem? target po pb f sb (i + 1)
      else
        match bestInBlob (fun s => rscore R.lv ls s.r) 0 (R.diff pb ls) with
        | some s =>
          if R.thrM < rscore R.lv ls s.r then moveLoop FO mem? target po pb f (FO.splitMove sb i po s) i
          else moveLoop FO mem? target po pb f sb (i + 1)
        | none => moveLoop FO mem? target po pb f sb (i + 1)

def moveAll (FO : FileOps L O C P) (Kn : Kernel L O C P FI.F) (target : O) :
    List (C × Option O) → SB O → SB O × Bool
  | [], sb => (sb, false)
  | (_, none) :: ps, sb => moveAll FO Kn target ps sb
  | (_, some po) :: ps, sb =>
    if !(sb.any (fun e => !e.guilty && decide (e.suspect = target))) then (sb, true)
    else match R.blobOf po with
      | none => moveAll FO Kn target ps sb
      | some pb => moveAll FO Kn target ps
          (moveLoop R FO ((Kn.moveFilter pb).map FI.mem) target po pb FO.fuelMove sb 0)

/-! ### The copy search (`find_copy_in_parent`) -/

def cands (FO : FileOps L O C P) (target : O) (sb : SB O) : List (Entry O) :=
  sb.filter (fun e => !e.guilty && decide (e.suspect = target) &&
    decide (R.thrC < escore R.lv (entryLines FO e)))

def rounds (FO : FileOps L O C P) (parent : C) (choose : List L → Option Split)
    (srcInfo : List (P × List L)) : Nat → SB O → List (Entry O) → SB O
  | 0, sb, _ => sb
  | _ + 1, sb, [] => sb
  | f + 1, sb, c :: cs =>
    let picks := (c :: cs).map (fun e => (e, choose (entryLines FO e)))
    let r := FO.applyCopies sb parent picks srcInfo
    rounds FO parent choose srcInfo f r.1 r.2

def copyOne (FO : FileOps L O C P) (Kn : Kernel L O C P FI.F) (target : O) (parent : C) (po : Option O)
    (sb : SB O) : Prog (Ctx O C) (List (Src L P FI.F)) (SB O × Bool) :=
  match cands R FO target sb with
  | [] => Prog.ret (sb, true)
  | c :: cs => Prog.bind (Kn.getSources ⟨target, parent, po⟩) (fun srcs =>
      let sb' := rounds FO parent
        (fun ls => accept (fun s => rscore R.lv ls s.r) R.thrC (Kn.select R.thrC ls srcs))
        (srcs.map (fun s => (s.path, s.blob))) FO.fuelRounds sb (c :: cs)
      Prog.ret (sb', (cands R FO target sb').isEmpty))

def copyAll (FO : FileOps L O C P) (Kn : Kernel L O C P FI.F) (target : O) :
    List (C × Option O) → SB O → Prog (Ctx O C) (List (Src L P FI.F)) (SB O)
  | [], sb => Prog.ret sb
  | (p, po) :: ps, sb => Prog.bind (copyOne R FI FO Kn target p po sb)
      (fun r => if r.2 then Prog.ret r.1 else copyAll FO Kn target ps r.1)

/-! ### The walk (`pass_blame`, `git_blame__like_git`) -/

def passBlame (FO : FileOps L O C P) (Kn : Kernel L O C P FI.F) (o : O) (sb : SB O) :
    Prog (Ctx O C) (List (Src L P FI.F)) (SB O) :=
  let r := FO.passParents sb o
  if r.2.2 then Prog.ret r.2.1 else
  let m := if R.moves then moveAll R FI FO Kn o r.1 r.2.1 else (r.2.1, false)
  if m.2 then Prog.ret m.1 else
  if R.copies then copyAll R FI FO Kn o r.1 m.1 else Prog.ret m.1

def markGuilty (o : O) (sb : SB O) : SB O :=
  sb.map (fun e => if e.suspect = o then { e with guilty := true } else e)

def blame (FO : FileOps L O C P) (Kn : Kernel L O C P FI.F) : Nat → SB O → Prog (Ctx O C) (List (Src L P FI.F)) (SB O)
  | 0, sb => Prog.ret sb
  | f + 1, sb =>
    match sb.find? (fun e => !e.guilty) with
    | none => Prog.ret (FO.coalesce sb)
    | some e => Prog.bind (passBlame R FI FO Kn e.suspect sb)
        (fun sb' => blame FO Kn f (markGuilty e.suspect sb'))

/-! ### The two kernels -/

def imap {α β : Type} (f : Nat → α → β) : List α → List β :=
  let rec go (i : Nat) : List α → List β
    | [] => []
    | x :: xs => f i x :: go (i + 1) xs
  go 0

def notPo (po : Option O) (path : P) : Bool := po.all (fun o => !(decide (R.pathOf o = path)))

/-- The key of a question. -/
def keyOf (q : Ctx O C) : CKey C :=
  ⟨R.commitOf q.target, q.parent, R.unmodFlag q.target q.po, !R.ignoreWs⟩

def mkSrc (key : CKey C) (d : D) : Option (Src L P FI.F) :=
  (R.oldSide d).map (fun t => ⟨t.1, t.2.1, t.2.2,
    if key.filters && R.small t.2.1 then some (FI.build t.2.2 (items R.lv t.2.1)) else none⟩)

/-- The canonical list of a key: the value that the cache keeps. -/
def canon (key : CKey C) : List (Src L P FI.F) :=
  (R.deltas key.commit key.parent key.unmod).filterMap (mkSrc R FI key)

/-- `blame_source_list_build`, in the shape of the C code: it reads the
question (target, parent, porigin) through `diff_copy_sources`. -/
def buildC (q : Ctx O C) : List (Src L P FI.F) :=
  (R.deltas (R.commitOf q.target) q.parent (R.unmodFlag q.target q.po)).filterMap
    (mkSrc R FI ⟨R.commitOf q.target, q.parent, R.unmodFlag q.target q.po, !R.ignoreWs⟩)

/-- **The cached value is a function of the key only.** -/
theorem buildC_eq_canon (q : Ctx O C) : buildC R FI q = canon R FI (keyOf R q) := rfl

/-- `diff_copy_sources` and `is_copy_source(delta, porigin)`: the sources of
the reference, without filters. -/
def refSrc (po : Option O) (d : D) : Option (Src L P FI.F) :=
  match R.oldSide d with
  | none => none
  | some t => if notPo R po t.1 then some ⟨t.1, t.2.1, t.2.2, none⟩ else none

def refSources (q : Ctx O C) : List (Src L P FI.F) :=
  (R.deltas (R.commitOf q.target) q.parent (R.unmodFlag q.target q.po)).filterMap (refSrc R FI q.po)

def filterPo (po : Option O) (l : List (Src L P FI.F)) : List (Src L P FI.F) :=
  l.filter (fun s => notPo R po s.path)

/-- `find_best_copies_in_diff`. -/
def refSel (_thr : Nat) (ls : List L) (srcs : List (Src L P FI.F)) : Option Split :=
  refFold (fun s => rscore R.lv ls s.r) (imap (fun i s => bestInBlob (fun s => rscore R.lv ls s.r) i (R.diff s.blob ls)) srcs)

def pruneSrc (ls : List L) (s : Src L P FI.F) (b : Nat) : Bool :=
  match s.filt with
  | none => false
  | some f => !canMatch R.lv (FI.mem f) b ls

/-- `find_best_copies_in_list`. -/
def optSel (thr : Nat) (ls : List L) (srcs : List (Src L P FI.F)) : Option Split :=
  optFold (fun s => rscore R.lv ls s.r) thr
    (imap (fun i s => (pruneSrc R FI ls s, bestInBlob (fun s => rscore R.lv ls s.r) i (R.diff s.blob ls))) srcs)

def refK : Kernel L O C P FI.F where
  moveFilter := fun _ => none
  getSources := fun q => Prog.ret (refSources R FI q)
  select := refSel R FI

def optK : Kernel L O C P FI.F where
  moveFilter := fun pb => if !R.ignoreWs && R.small pb then some (FI.build 0 (items R.lv pb)) else none
  getSources := fun q => Prog.ask q (fun l => Prog.ret (filterPo R FI q.po l))
  select := optSel R FI

/-- The canonical oracle. -/
def oracle (q : Ctx O C) : List (Src L P FI.F) := canon R FI (keyOf R q)

end RB
