import Papers.PODC2026.ForgetIT.Spec
import Cslib.Computability.Distributed.Byzantine.PartialSync.Sim

/-!
# Forget-IT as a timed algorithm (CSLib partially synchronous model)

`forgetIT prm K` is Algorithms 1–3 as an `Algorithm` of CSLib's partially synchronous Byzantine
model (`Cslib.Byzantine.PartialSync`) on processes `Fin n`: discrete time, every correct process
takes one step per tick, authenticated channels without signatures, at most `f` Byzantine
processes, and between correct processes every message sent at time `τ` is delivered by
`max τ GST + δ`.

One step of a process:
1. append the delivered messages (with their senders) to `rcv`;
2. run `K` *passes* over the rules: each pass computes, from the received messages, a list of
   candidate rule instances (`cands`) and executes, in this order, every candidate that is enabled
   (`En`) at the moment it is examined (`tryAct`);
3. advance the local clock; the messages broadcast in this step form the outbox `out`, which is
   sent to every process (including itself) at the next tick.

The timers are the local clock: `vote-2` on timeout (line 45) once `3Δ` ticks have elapsed since
the last active view entry, the view-change timer (line 65) once `4Δ` ticks have elapsed since
the last view entry. Every executed rule is an enabled rule of `Defs.lean`, so every run of this
algorithm is an execution of the asynchronous system of `Spec.lean` (see `Refinement.lean`).
-/

namespace Podc.ForgetIT

open Finset Cslib.Byzantine.PartialSync

variable {Val : Type} [DecidableEq Val] {n : ℕ}

section decidable

variable {P : Type} [Fintype P] [DecidableEq P]

lemma divergent_iff (f : ℕ) (s : LS P Val) (V : ℕ) :
    divergent f s V ↔ f + 1 ≤ (accAll s V).card ∧
      ∀ q, ∀ G ∈ guardOf (s.acc V q), f + 1 + (accG s V G).card ≤ (accAll s V).card := by
  constructor
  · intro h
    exact ⟨by have := h .safe; omega, fun q G _ => h G⟩
  · rintro ⟨h1, h2⟩ G
    by_cases hG : ∃ q, guardOf (s.acc V q) = some G
    · obtain ⟨q, hq⟩ := hG; exact h2 q G hq
    · have : accG s V G = ∅ := by
        ext q; simp only [accG, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        exact fun h => hG ⟨q, h⟩
      rw [this]; simpa using h1

instance (f : ℕ) (s : LS P Val) (V : ℕ) : Decidable (divergent f s V) :=
  decidable_of_iff _ (divergent_iff f s V).symm

instance (prm : Params P) (p : P) (a : Act P Val) (s : LS P Val) : Decidable (En prm p a s) := by
  cases a <;> dsimp only [En, inW, cert] <;> infer_instance

/-- Timer conditions of the timed implementation; no recovery (no crashes). -/
def TimerOK (prm : Params P) (s : LS P Val) : Act P Val → Prop
  | .timeout2 => s.active = true ∧ 3 * prm.Δ ≤ s.clk - s.entered
  | .vcTimer => 4 * prm.Δ ≤ s.clk - s.entered
  | .recover => False
  | _ => True

/-- Rules the timed implementation may execute: enabled rules, timers only once they expire, and
never the recovery procedure (there are no crashes in this model). -/
def Allowed (prm : Params P) (p : P) (s : LS P Val) (a : Act P Val) : Prop :=
  En prm p a s ∧ TimerOK prm s a

instance (prm : Params P) (p : P) (s : LS P Val) (a : Act P Val) : Decidable (Allowed prm p s a) :=
  by unfold Allowed; cases a <;> dsimp only [TimerOK] <;> infer_instance

end decidable

/-- Try rule `a`: execute it if it is allowed, accumulating the broadcast messages. -/
def tryAct (prm : Params (Fin n)) (p : Fin n) (st : LS (Fin n) Val × List (Msg Val))
    (a : Act (Fin n) Val) : LS (Fin n) Val × List (Msg Val) :=
  if Allowed prm p st.1 a then ((exec prm p a st.1).1, st.2 ++ (exec prm p a st.1).2) else st

section cands

variable (prm : Params (Fin n)) (p : Fin n) (s : LS (Fin n) Val)

/-- Values proposed in received `prepare` messages for view `V` from `q`. -/
def prepVals (V : ℕ) (q : Fin n) : List Val :=
  s.rcv.filterMap fun e => match e.2 with
    | .prepare V' w => if e.1 = q ∧ V' = V then some w else none
    | _ => none

/-- Values of received `vote-1` messages for view `V`. -/
def vote1Vals (V : ℕ) : List Val :=
  (s.rcv.filterMap fun e => match e.2 with
    | .vote1 V' w => if V' = V then some w else none
    | _ => none).dedup

/-- Non-`⊥` locks of received `vote-2` messages for view `V`. -/
def vote2Locks (V : ℕ) : List Val :=
  (s.rcv.filterMap fun e => match e.2 with
    | .vote2 V' (some l) _ => if V' = V then some l else none
    | _ => none).dedup

/-- Guards of received `vote-2` messages for view `V`. -/
def vote2Guards (V : ℕ) : List (GV Val) :=
  (s.rcv.filterMap fun e => match e.2 with
    | .vote2 V' _ (some G) => if V' = V then some G else none
    | _ => none).dedup

/-- Received `vote-2` messages (sender, view, lock, guard). -/
def vote2s : List (Fin n × ℕ × Option Val × Option (GV Val)) :=
  s.rcv.filterMap fun e => match e.2 with
    | .vote2 V l g => some (e.1, V, l, g)
    | _ => none

/-- Values of received `echo-(k+1)` messages for view `V` (and `SAFE`). -/
def echoVals (k : Fin 3) (V : ℕ) : List (GV Val) :=
  (.safe :: s.rcv.filterMap fun e => match e.2 with
    | .echo k' V' x => if k' = k ∧ V' = V then some x else none
    | _ => none).dedup

/-- Views of received `echo-(k+1)` messages. -/
def echoViews (k : Fin 3) : List ℕ :=
  (s.rcv.filterMap fun e => match e.2 with
    | .echo k' V' _ => if k' = k then some V' else none
    | _ => none).dedup

/-- Received `prepare` messages from the leader of their view (view, value). -/
def preps : List (ℕ × Val) :=
  s.rcv.filterMap fun e => match e.2 with
    | .prepare V w => if e.1 = prm.leader V then some (V, w) else none
    | _ => none

/-- The views of the window `{view − 2, view − 1, view}`. -/
def window : List ℕ := [s.view - 2, s.view - 1, s.view].dedup

/-- Candidate rule instances of one pass, in the order in which they are tried. -/
def cands : List (Act (Fin n) Val) :=
  (vote2s s).map (fun e => .accept e.2.1 e.1 e.2.2.1 e.2.2.2) ++
  (vote2Locks s s.view).map .decide ++
  (prepVals s s.view (prm.leader s.view)).map .vote1 ++
  (vote1Vals s s.view).map .lock ++
  (echoVals s 1 (s.view - 1)).map .clearGuard ++
  (if s.active ∧ 3 * prm.Δ ≤ s.clk - s.entered then [.timeout2] else []) ++
  (if 4 * prm.Δ ≤ s.clk - s.entered then [.vcTimer] else []) ++
  (window s).flatMap (fun V =>
    ((none :: (vote2Locks s V).map some).map (.alertSet V)) ++ [.alertClear1 V, .alertClear2 V] ++
    ((vote2s s).filterMap fun e => match e.2.2.1 with
      | some x => if e.2.1 = V then some (.echoLock V e.1 x) else none
      | none => none) ++
    (vote2Guards s V).map (.echoGuard V) ++ [.echoDiv V] ++
    (echoVals s 0 V).map (.echo2 V) ++ (echoVals s 1 V).map (.echo3 V)) ++
  (echoViews s 2).flatMap (fun V => (echoVals s 2 V).flatMap fun x => [.enter3 V x, .enter3L V x]) ++
  (preps prm s).flatMap (fun e => (echoVals s 1 (e.1 - 1)).map (.enterPrep e.1 e.2)) ++
  (echoViews s 0).flatMap (fun V => (echoVals s 0 V).map (.passive V))

end cands

/-- One pass over the rules. -/
def pass (prm : Params (Fin n)) (p : Fin n) (st : LS (Fin n) Val × List (Msg Val)) :
    LS (Fin n) Val × List (Msg Val) :=
  (cands prm st.1).foldl (tryAct prm p) st

/-- The messages delivered in this step, with their senders. -/
def inboxList (inbox : Fin n → List (Msg Val)) : List (Fin n × Msg Val) :=
  (List.finRange n).flatMap fun q => (inbox q).map (q, ·)

/-- One step: receive, `K` passes over the rules, advance the clock. -/
def stepFI (prm : Params (Fin n)) (K : ℕ) (p : Fin n) (s : LS (Fin n) Val)
    (inbox : Fin n → List (Msg Val)) : LS (Fin n) Val :=
  let st := (pass prm p)^[K] ({ s with rcv := s.rcv ++ inboxList inbox }, [])
  { st.1 with clk := s.clk + 1, out := st.2 }

/-- **Forget-IT** (Algorithms 1–3) as a partially synchronous algorithm with `K` rule passes per
tick. Proposals and decisions are values. -/
def forgetIT (prm : Params (Fin n)) (K : ℕ) : Algorithm (Fin n) (Msg Val) (LS (Fin n) Val) Val Val
    where
  init p v := initLS prm p v
  step := stepFI prm K
  send _ s _ := s.out
  decide _ s := s.decided.map Prod.snd

end Podc.ForgetIT
