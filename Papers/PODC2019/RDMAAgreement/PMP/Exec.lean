import Papers.PODC2019.RDMAAgreement.PMP.Model

/-!
# A (partial) executable step function for the model of Algorithm 7

`exec` executes one scheduler action deterministically (or fails with `none`); it covers the
steps needed for concrete executions (the read-delivery step only in the "abort" and "no value
read" cases, no `discard`). `exec_sound` shows that every successful `exec` is a `Step`, so
concrete runs can be checked by evaluation (`decide`).
-/

namespace Podc.RDMAAgreement.PMP

set_option linter.unusedSectionVars false

open Function

variable {P M V : Type*} [DecidableEq P] [DecidableEq M] [Fintype M] [Fintype P]

/-- Scheduler actions. -/
inductive Act (P M : Type*)
  | startFirst (q : P)
  | startNext (q : P) (b : ℕ)
  | invPerm (q : P) (m : M)
  | eff (q : P) (m : M)
  | dlv (q : P) (m : M)
  | pass (q : P) (m : M)
  | issue (q : P) (m : M)

/-- Execute one action. -/
def exec (p1 : P) (inp : P → V) (var : Variant) : Act P M → State P M V → Option (State P M V)
  | .startFirst q, s =>
    if q = p1 ∧ (s.pr q).started = false ∧ (s.pr q).active = false ∧ 1 ∉ s.used ∧
        (s.pr q).bal < 1 then
      some { s with
          pr := update s.pr q
            { s.pr q with
              active := true, started := true, noPh1 := true, bal := 1,
              curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
              pc := fun _ => .ph2 }
          used := insert 1 s.used
          p2val := update s.p2val 1 (some (inp q)) }
    else none
  | .startNext q b, s =>
    if ¬(q = p1 ∧ (s.pr q).started = false) ∧ (s.pr q).active = false ∧ b ∉ s.used ∧
        (s.pr q).bal < b ∧ 2 ≤ b then
      some { s with
          pr := update s.pr q
            { s.pr q with
              active := true, started := true, noPh1 := false, bal := b,
              curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
              pc := fun _ => .init }
          used := insert b s.used }
    else none
  | .invPerm q m, s =>
    match (s.pr q).pc m, (s.pr q).link m with
    | .init, .idle => some { s with pr := update s.pr q ((s.pr q).setT m .wPerm (.sent .perm)) }
    | _, _ => none
  | .eff q m, s =>
    match (s.pr q).link m with
    | .sent .perm => some { s with
          perm := update s.perm m q
          pr := update s.pr q ((s.pr q).setL m (.resp .ack)) }
    | .sent (.w1 sl) =>
      if s.perm m = q then
        some { s with
          slot := update s.slot m (update (s.slot m) q sl)
          pr := update s.pr q ((s.pr q).setL m (.resp .ack)) }
      else some { s with pr := update s.pr q ((s.pr q).setL m (.resp .nak)) }
    | .sent (.w2 b v) =>
      if s.perm m = q then
        some { s with
          slot := update s.slot m (update (s.slot m) q ⟨b, some (b, v)⟩)
          pr := update s.pr q ((s.pr q).setL m (.resp .ack))
          votes := insert (m, q, b, v) s.votes }
      else some { s with pr := update s.pr q ((s.pr q).setL m (.resp .nak)) }
    | .sent .rd => some { s with pr := update s.pr q ((s.pr q).setL m (.resp (.snap (s.slot m)))) }
    | _ => none
  | .dlv q m, s =>
    match (s.pr q).pc m, (s.pr q).link m with
    | .wPerm, .resp .ack => some { s with pr := update s.pr q ((s.pr q).setT m .wW1
            (.sent (.w1 ⟨(s.pr q).bal, line21 var (s.pr q).lastIss⟩))) }
    | .wW1, .resp .ack => some { s with pr := update s.pr q ((s.pr q).setT m .wRd (.sent .rd)) }
    | .wW1, .resp .nak => some { s with pr := update s.pr q (((s.pr q).setL m .idle).kill) }
    | .wRd, .resp (.snap f) =>
      if ∃ r, (s.pr q).bal < (f r).mp then
        some { s with pr := update s.pr q (((s.pr q).setL m .idle).kill) }
      else if ∀ r, (f r).acc.isNone = true then
        some { s with
          pr := update s.pr q
            { (s.pr q).setT m .barrier .idle with ready := insert m (s.pr q).ready } }
      else none
    | .wW2, .resp .ack =>
      if Maj (insert m (s.pr q).done) then
        some { s with
          pr := update s.pr q
            ({ (s.pr q).setT m .fin .idle with done := insert m (s.pr q).done }).kill
          decs := (s.pr q).curVal :: s.decs }
      else
        some { s with
          pr := update s.pr q
            { (s.pr q).setT m .fin .idle with done := insert m (s.pr q).done } }
    | .wW2, .resp .nak => some { s with pr := update s.pr q (((s.pr q).setL m .idle).kill) }
    | _, _ => none
  | .pass q m, s =>
    match (s.pr q).pc m, (s.pr q).link m with
    | .barrier, .idle =>
      if Maj (s.pr q).ready then
        if (s.pr q).p2s = false then
          some { s with
            pr := update s.pr q
              { (s.pr q).setT m .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
                p2s := true, lastIss := some ((s.pr q).bal, (s.pr q).curVal) }
            p2val := update s.p2val (s.pr q).bal (some (s.pr q).curVal) }
        else
          some { s with
            pr := update s.pr q
              { (s.pr q).setT m .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
                lastIss := some ((s.pr q).bal, (s.pr q).curVal) } }
      else none
    | _, _ => none
  | .issue q m, s =>
    match (s.pr q).pc m, (s.pr q).link m with
    | .ph2, .idle =>
      some { s with
          pr := update s.pr q
            { (s.pr q).setT m .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
              lastIss := some ((s.pr q).bal, (s.pr q).curVal) } }
    | _, _ => none

/-- Execute a list of actions. -/
def run (p1 : P) (inp : P → V) (var : Variant) :
    List (Act P M) → State P M V → Option (State P M V)
  | [], s => some s
  | a :: as, s => (exec p1 inp var a s).bind (run p1 inp var as)

theorem exec_sound (p1 : P) (inp : P → V) (var : Variant) (a : Act P M) (s s' : State P M V)
    (h : exec p1 inp var a s = some s') : Step p1 inp var s s' := by
  cases a with
  | startFirst q =>
    simp only [exec] at h
    split_ifs at h with hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    cases h; exact Step.startFirst s q h1 h2 h3 h4 h5
  | startNext q b =>
    simp only [exec] at h
    split_ifs at h with hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    cases h; exact Step.startNext s q b h1 h2 h3 h4 h5
  | invPerm q m =>
    simp only [exec] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; exact Step.invPerm s q m ‹_› ‹_›
  | eff q m =>
    simp only [exec] at h
    split at h <;> try simp only [reduceCtorEq] at h
    · cases h; exact Step.effPerm s q m ‹_›
    · split_ifs at h with hp <;> cases h
      · exact Step.effW1 s q m _ ‹_› hp
      · exact Step.effW1nak s q m _ ‹_› hp
    · split_ifs at h with hp <;> cases h
      · exact Step.effW2 s q m _ _ ‹_› hp
      · exact Step.effW2nak s q m _ _ ‹_› hp
    · cases h; exact Step.effRd s q m ‹_›
  | dlv q m =>
    simp only [exec] at h
    split at h <;> try simp only [reduceCtorEq] at h
    · cases h; exact Step.dlvPerm s q m ‹_› ‹_›
    · cases h; exact Step.dlvW1 s q m ‹_› ‹_›
    · cases h; exact Step.dlvW1nak s q m ‹_› ‹_›
    · split_ifs at h with h1 h2 <;> try simp only [reduceCtorEq] at h
      · cases h; exact Step.dlvRdAbort s q m _ ‹_› ‹_› h1
      · cases h
        push Not at h1
        exact Step.dlvRdNone s q m _ ‹_› ‹_› h1 (fun r => Option.isNone_iff_eq_none.mp (h2 r))
    · split_ifs at h with h1 <;> cases h
      · exact Step.dlvW2Decide s q m ‹_› ‹_› h1
      · exact Step.dlvW2 s q m ‹_› ‹_› h1
    · cases h; exact Step.dlvW2nak s q m ‹_› ‹_›
  | pass q m =>
    simp only [exec] at h
    split at h <;> try simp only [reduceCtorEq] at h
    split_ifs at h with h1 h2 <;> try simp only [reduceCtorEq] at h
    · cases h; exact Step.passFirst s q m ‹_› ‹_› h1 h2
    · cases h; exact Step.passLate s q m ‹_› ‹_› h1 (by simpa using h2)
  | issue q m =>
    simp only [exec] at h
    split at h <;> try simp only [reduceCtorEq] at h
    cases h; exact Step.issueFirst s q m ‹_› ‹_›

theorem run_sound (p1 : P) (inp : P → V) (var : Variant) :
    ∀ (as : List (Act P M)) (s s' : State P M V), run p1 inp var as s = some s' →
      Relation.ReflTransGen (Step p1 inp var) s s'
  | [], s, s', h => by cases h; exact .refl
  | a :: as, s, s', h => by
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h⟩ := h
    exact .head (exec_sound p1 inp var a s t ht) (run_sound p1 inp var as t s' h)

end Podc.RDMAAgreement.PMP
