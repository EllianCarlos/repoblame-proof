/-
  replay: run the Lean model on traces of the C code and compare.

  usage: replay <trace-without-cache> [<trace-with-cache>]

  A trace comes from the trace build (diff-tests/trace.patch).  The model
  definitions are the ones of the proofs: `bestInBlob`, `refFold`,
  `optStep`/`optFold`, `canMatch`, `items`, and `cBloom` (the bit-exact
  copy of the C filter, an instance of `FilterImpl`).
-/
import RepoblameProof.Main

open RB

abbrev Ln := UInt64 × Nat

def lv : LineView Ln UInt64 := ⟨Prod.fst, Prod.snd⟩

structure SRec where
  si : Nat
  salt : UInt64
  flag : Bool
  lines : List Ln
deriving Inhabited

structure PRec where
  si : Nat
  j : Nat
  pruned : Option Bool
  bar : Option Nat
  regs : List Region
deriving Inhabited

structure Round where
  mode : String
  thr : Nat
  prune : Bool
  cands : Array (List Ln) := #[]
  srcs : Array SRec := #[]
  ps : Array PRec := #[]
  bs : Array (Nat × Option (Split × Nat)) := #[]
deriving Inhabited

structure MoveRec where
  thr : Nat
  filtered : Bool
  small : Bool
  parent : List Ln
  entry : List Ln
  regs : List Region
  pruned : Option Bool
  mt : Option (Option (Split × Nat)) := none
deriving Inhabited

inductive Ev where
  | round (r : Round)
  | move (m : MoveRec)

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0

def parseHex (s : String) : Nat := s.foldl (fun a c => a * 16 + hexVal c) 0

/-- `memcpy(&salt, id, 8)` on a little-endian machine. -/
def saltOfOid (hex : String) : UInt64 :=
  let cs := hex.toList
  let byte (k : Nat) : Nat := hexVal (cs.getD (2 * k) '0') * 16 + hexVal (cs.getD (2 * k + 1) '0')
  ((List.range 8).foldl (fun a k => a + byte k * 256 ^ k) 0).toUInt64

def parseLn (s : String) : Ln :=
  match s.splitOn ":" with
  | [h, a] => ((parseHex h).toUInt64, a.toNat!)
  | _ => (0, 0)

def parseReg (s : String) : Region :=
  match s.splitOn "," with
  | [t, p, n] => ⟨t.toNat!, p.toNat!, n.toNat!⟩
  | _ => ⟨0, 0, 0⟩

/-- `n x1 .. xn` from the front of a word list. -/
def takeCounted {α : Type} (f : String → α) : List String → List α × List String
  | [] => ([], [])
  | n :: rest =>
    let k := n.toNat!
    ((rest.take k).map f, rest.drop k)

def parseTrace (text : String) : Array Ev := Id.run do
  let mut evs : Array Ev := #[]
  let mut cur : Option Round := none
  let mut pend : Option MoveRec := none
  let mut parent : (Nat × Bool × Bool × List Ln) := (0, false, false, [])
  for line in text.splitOn "\n" do
    let w := (line.splitOn " ").filter (· ≠ "")
    match w with
    | "R" :: mode :: thr :: _ :: pr :: _ =>
      if let some m := pend then evs := evs.push (.move m); pend := none
      cur := some { mode := mode, thr := thr.toNat!, prune := pr == "1" }
    | "C" :: _ :: rest =>
      if let some r := cur then cur := some { r with cands := r.cands.push (takeCounted parseLn rest).1 }
    | "S" :: si :: oid :: fl :: rest =>
      if let some r := cur then
        cur := some { r with srcs := r.srcs.push ⟨si.toNat!, saltOfOid oid, fl == "1", (takeCounted parseLn rest).1⟩ }
    | "P" :: si :: j :: pr :: bar :: rest =>
      if let some r := cur then
        let pr' := if pr == "-" then none else some (pr == "1")
        let bar' := if bar == "-" then none else some bar.toNat!
        cur := some { r with ps := r.ps.push ⟨si.toNat!, j.toNat!, pr', bar', (takeCounted parseReg rest).1⟩ }
    | "B" :: j :: "none" :: _ =>
      if let some r := cur then cur := some { r with bs := r.bs.push (j.toNat!, none) }
    | "B" :: j :: si :: t :: p :: n :: sc :: _ =>
      if let some r := cur then
        cur := some { r with bs := r.bs.push (j.toNat!, some (⟨si.toNat!, ⟨t.toNat!, p.toNat!, n.toNat!⟩⟩, sc.toNat!)) }
    | "E" :: _ =>
      if let some r := cur then evs := evs.push (.round r)
      cur := none
    | "MS" :: thr :: fl :: sm :: rest =>
      if let some m := pend then evs := evs.push (.move m); pend := none
      parent := (thr.toNat!, fl == "1", sm == "1", (takeCounted parseLn rest).1)
    | "ME" :: rest =>
      if let some m := pend then evs := evs.push (.move m)
      let (ent, r1) := takeCounted parseLn rest
      let (regs, r2) := takeCounted parseReg r1
      let pr := match r2 with
        | ["-"] => none
        | [x] => some (x == "1")
        | _ => none
      pend := some ⟨parent.1, parent.2.1, parent.2.2.1, parent.2.2.2, ent, regs, pr, none⟩
    | "MT" :: "none" :: _ =>
      if let some m := pend then evs := evs.push (.move { m with mt := some none }); pend := none
    | "MT" :: t :: p :: n :: sc :: _ =>
      if let some m := pend then
        evs := evs.push (.move { m with mt := some (some (⟨0, ⟨t.toNat!, p.toNat!, n.toNat!⟩⟩, sc.toNat!)) })
        pend := none
    | _ => pure ()
  if let some m := pend then evs := evs.push (.move m)
  return evs

/-! ### Checks -/

def validB (cand src : List Ln) (r : Region) : Bool :=
  decide (1 ≤ r.len) && decide (r.t + r.len ≤ cand.length) && decide (r.p + r.len ≤ src.length) &&
  (slice cand r.t r.len == slice src r.p r.len)

structure Stats where
  rounds : Nat := 0
  cands : Nat := 0
  pairs : Nat := 0
  regions : Nat := 0
  regionBad : Nat := 0
  boundChecks : Nat := 0
  boundBad : Nat := 0
  refVsC : Nat := 0          -- D rounds: Lean reference fold = C result
  refVsCBad : Nat := 0
  optVsC : Nat := 0          -- L rounds: Lean pruned fold = C result
  optVsCBad : Nat := 0
  decisions : Nat := 0       -- L rounds: Lean prune decision and bar = C
  decisionBad : Nat := 0
  prunedPairs : Nat := 0
  acceptEq : Nat := 0        -- accept(opt) = accept(ref), Lean (theorem instance)
  acceptBad : Nat := 0
  cAcceptRef : Nat := 0      -- L rounds: accept(C result) = accept(Lean reference)
  cAcceptRefBad : Nat := 0
  moves : Nat := 0
  moveRefBad : Nat := 0      -- Lean move decision = C (MT)
  moveDec : Nat := 0         -- C prune decision = Lean
  moveDecBad : Nat := 0
  movePruned : Nat := 0
  moveSoundBad : Nat := 0    -- Lean says prune but the move is taken
  ties : Nat := 0            -- candidates with 2+ sources at the best score, above the threshold
  barRaised : Nat := 0       -- decisions with bar > threshold
  skipAtRaisedBar : Nat := 0 -- skips with bar > threshold (branch and bound, not only the threshold)
  msgs : Array String := #[]

def Stats.note (s : Stats) (m : String) : Stats :=
  if s.msgs.size < 20 then { s with msgs := s.msgs.push m } else s

def filterOf (s : SRec) : Option cBloom.F :=
  some (cBloom.build s.salt (items lv s.lines))

def splitEq (a b : Option (Split × Nat)) : Bool :=
  match a, b with
  | none, none => true
  | some (x, n), some (y, m) => x.src == y.src && x.r.t == y.r.t && x.r.p == y.r.p && x.r.len == y.r.len && n == m
  | _, _ => false

def checkRound (st : Stats) (r : Round) : Stats := Id.run do
  let mut st := { st with rounds := st.rounds + 1 }
  for hj : j in [0:r.cands.size] do
    let cand := r.cands[j]
    let sc := fun (s : Split) => rscore lv cand s.r
    st := { st with cands := st.cands + 1 }
    -- the per-source data for this candidate, in list order
    let mut xs : Array ((Nat → Bool) × Option Split) := #[]
    let mut cdec : Array (Option Bool × Option Nat) := #[]
    for s in r.srcs do
      let regs := match r.ps.find? (fun p => p.si == s.si && p.j == j) with
        | some p => p.regs
        | none => []
      let pr := (r.ps.find? (fun p => p.si == s.si && p.j == j)).map (fun p => (p.pruned, p.bar))
      cdec := cdec.push (pr.getD (none, none))
      st := { st with pairs := st.pairs + 1 }
      let f? : Option cBloom.F :=
        if r.prune && s.flag then filterOf s else none
      for rg in regs do
        st := { st with regions := st.regions + 1 }
        if !(validB cand s.lines rg) then
          st := { st with regionBad := st.regionBad + 1 }
          st := st.note s!"invalid region {repr rg} cand {j} src {s.si}"
        else if let some f := f? then
          st := { st with boundChecks := st.boundChecks + 1 }
          let t := rscore lv cand rg - 1
          if !(canMatch lv (cBloom.mem f) t cand) then
            st := { st with boundBad := st.boundBad + 1 }
            st := st.note s!"bound violation cand {j} src {s.si}"
      let pot := bestInBlob sc s.si regs
      let prune : Nat → Bool := fun b => match f? with
        | none => false
        | some f => !canMatch lv (cBloom.mem f) b cand
      xs := xs.push (prune, pot)
    let refRes := refFold sc (xs.toList.map Prod.snd)
    match refRes with
    | some b =>
      let n := (xs.toList.filter (fun x => match x.2 with
        | some p => sc p == sc b
        | none => false)).length
      if n ≥ 2 && decide (r.thr < sc b) then st := { st with ties := st.ties + 1 }
    | none => pure ()
    let optRes := optFold sc r.thr xs.toList
    let withScore := fun (o : Option Split) => o.map (fun s => (s, sc s))
    -- C result
    let cRes : Option (Split × Nat) := match r.bs.find? (fun b => b.1 == j) with
      | some b => b.2
      | none => none
    -- theorem instance
    if accept sc r.thr optRes == accept sc r.thr refRes then
      st := { st with acceptEq := st.acceptEq + 1 }
    else
      st := { st with acceptBad := st.acceptBad + 1 }
      st := st.note s!"accept differs (Lean) cand {j}"
    let cAcc : Option Split := match cRes with
      | some (s, n) => if r.thr < n then some s else none
      | none => none
    if r.mode == "D" then
      st := { st with refVsC := st.refVsC + 1 }
      if !(splitEq (withScore refRes) cRes) then
        st := { st with refVsCBad := st.refVsCBad + 1 }
        st := st.note s!"D: Lean ref {repr refRes} C {repr (cRes.map (·.1))} cand {j}"
    else
      st := { st with optVsC := st.optVsC + 1 }
      if !(splitEq (withScore optRes) cRes) then
        st := { st with optVsCBad := st.optVsCBad + 1 }
        st := st.note s!"L: Lean opt {repr optRes} C {repr (cRes.map (·.1))} cand {j}"
      st := { st with cAcceptRef := st.cAcceptRef + 1 }
      if !(cAcc == accept sc r.thr refRes) then
        st := { st with cAcceptRefBad := st.cAcceptRefBad + 1 }
        st := st.note s!"L: accept(C) differs from accept(Lean ref) cand {j}"
      -- replay the decisions and bars of the pruned fold
      let mut ob : OSt := ⟨none, 0⟩
      for hk : k in [0:xs.size] do
        let x := xs[k]
        let b := bar r.thr ob
        let dec := x.1 b
        if dec then st := { st with prunedPairs := st.prunedPairs + 1 }
        if decide (r.thr < b) then
          st := { st with barRaised := st.barRaised + 1 }
          if dec then st := { st with skipAtRaisedBar := st.skipAtRaisedBar + 1 }
        st := { st with decisions := st.decisions + 1 }
        match cdec[k]? with
        | some (some cp, some cb) =>
          if cp != dec || cb != b then
            st := { st with decisionBad := st.decisionBad + 1 }
            st := st.note s!"decision differs cand {j} src {k}: C {cp}/{cb} Lean {dec}/{b}"
        | _ =>
          st := { st with decisionBad := st.decisionBad + 1 }
          st := st.note s!"no C decision cand {j} src {k}"
        ob := optStep sc r.thr ob x
  return st

def checkMove (st : Stats) (m : MoveRec) : Stats := Id.run do
  let mut st := { st with moves := st.moves + 1 }
  let cand := m.entry
  let sc := fun (s : Split) => rscore lv cand s.r
  for rg in m.regs do
    st := { st with regions := st.regions + 1 }
    if !(validB cand m.parent rg) then
      st := { st with regionBad := st.regionBad + 1 }
      st := st.note s!"invalid move region {repr rg}"
  let best := bestInBlob sc 0 m.regs
  let taken := match best with
    | some s => decide (m.thr < sc s)
    | none => false
  -- the Lean filter of the parent blob (salt 0), when the C code can make one
  let f := cBloom.build 0 (items lv m.parent)
  let leanPrune := !canMatch lv (cBloom.mem f) m.thr cand
  if m.small && leanPrune then
    st := { st with movePruned := st.movePruned + 1 }
    if taken then
      st := { st with moveSoundBad := st.moveSoundBad + 1 }
      st := st.note "move: Lean prunes a taken move"
  match m.pruned with
  | some cp =>
    st := { st with moveDec := st.moveDec + 1 }
    if cp != leanPrune then
      st := { st with moveDecBad := st.moveDecBad + 1 }
      st := st.note s!"move decision differs: C {cp} Lean {leanPrune}"
  | none => pure ()
  match m.mt with
  | some cm =>
    if !(splitEq (best.map (fun s => (s, sc s))) cm) then
      st := { st with moveRefBad := st.moveRefBad + 1 }
      st := st.note s!"move split differs: Lean {repr best} C {repr (cm.map (·.1))}"
  | none =>
    -- no MT: the C code skipped the entry; it must be pruned
    if m.pruned != some true then
      st := { st with moveRefBad := st.moveRefBad + 1 }
      st := st.note "move without MT and not pruned"
  return st

def runChecks (evs : Array Ev) : Stats :=
  evs.foldl (fun st e => match e with
    | .round r => checkRound st r
    | .move m => checkMove st m) {}

/-- Cross check of two runs of the same files: the same rounds (the same
candidates, sources and regions) and the same accepted splits. -/
def crossCheck (a b : Array Ev) : Nat × Nat × Array String := Id.run do
  let ra := a.filterMap (fun e => match e with | .round r => some r | _ => none)
  let rb := b.filterMap (fun e => match e with | .round r => some r | _ => none)
  let mut ok := 0
  let mut bad := 0
  let mut msgs : Array String := #[]
  if ra.size != rb.size then
    return (0, 1, #[s!"round count {ra.size} vs {rb.size}"])
  for hi : i in [0:ra.size] do
    let x := ra[i]
    let y := rb[i]!
    let same := x.thr == y.thr && x.cands == y.cands &&
      (x.srcs.map (fun s => (s.si, s.salt, s.lines))) == (y.srcs.map (fun s => (s.si, s.salt, s.lines))) &&
      (x.ps.map (fun p => (p.si, p.j, p.regs))) == (y.ps.map (fun p => (p.si, p.j, p.regs)))
    let acc := fun (r : Round) => r.bs.map (fun (j, o) => (j, match o with
      | some (s, n) => if r.thr < n then some (s.src, s.r.t, s.r.p, s.r.len) else none
      | none => none))
    if same && acc x == acc y then ok := ok + 1
    else
      bad := bad + 1
      if msgs.size < 10 then msgs := msgs.push s!"round {i} differs"
  -- moves: the same entries and parents, and the same taken moves
  let ma := a.filterMap (fun e => match e with | .move m => some m | _ => none)
  let mb := b.filterMap (fun e => match e with | .move m => some m | _ => none)
  if ma.size != mb.size then
    return (ok, bad + 1, msgs.push s!"move count {ma.size} vs {mb.size}")
  for hi : i in [0:ma.size] do
    let x := ma[i]
    let y := mb[i]!
    let tk := fun (m : MoveRec) => match m.mt with
      | some (some (_, n)) => decide (m.thr < n)
      | _ => false
    if x.entry == y.entry && x.parent == y.parent && x.regs == y.regs && tk x == tk y then ok := ok + 1
    else
      bad := bad + 1
      if msgs.size < 10 then msgs := msgs.push s!"move {i} differs"
  return (ok, bad, msgs)

def printStats (name : String) (s : Stats) : IO Unit := do
  IO.println s!"{name}\trounds={s.rounds}\tcands={s.cands}\tpairs={s.pairs}\tregions={s.regions}\tregion_bad={s.regionBad}\tbound_checks={s.boundChecks}\tbound_bad={s.boundBad}\tref_vs_c={s.refVsC}\tref_vs_c_bad={s.refVsCBad}\topt_vs_c={s.optVsC}\topt_vs_c_bad={s.optVsCBad}\tdecisions={s.decisions}\tdecision_bad={s.decisionBad}\tpruned={s.prunedPairs}\taccept_eq={s.acceptEq}\taccept_bad={s.acceptBad}\tc_accept_ref={s.cAcceptRef}\tc_accept_ref_bad={s.cAcceptRefBad}\tmoves={s.moves}\tmove_ref_bad={s.moveRefBad}\tmove_dec={s.moveDec}\tmove_dec_bad={s.moveDecBad}\tmove_pruned={s.movePruned}\tmove_sound_bad={s.moveSoundBad}\tties={s.ties}\tbar_raised={s.barRaised}\tskip_raised={s.skipAtRaisedBar}"
  for m in s.msgs do IO.println s!"  ! {m}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [a] =>
    let ea := parseTrace (← IO.FS.readFile a)
    printStats a (runChecks ea)
    return 0
  | [a, b] =>
    let ea := parseTrace (← IO.FS.readFile a)
    let eb := parseTrace (← IO.FS.readFile b)
    printStats a (runChecks ea)
    printStats b (runChecks eb)
    let (ok, bad, msgs) := crossCheck ea eb
    IO.println s!"cross\tok={ok}\tbad={bad}"
    for m in msgs do IO.println s!"  ! {m}"
    return 0
  | _ =>
    IO.eprintln "usage: replay <trace> [<trace-with-cache>]"
    return 2
