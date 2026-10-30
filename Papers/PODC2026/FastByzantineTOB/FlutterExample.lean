import Papers.PODC2026.FastByzantineTOB.FlutterSafety

set_option linter.unusedSectionVars false

/-!
# Flutter: runs given by a list of actions; a non-vacuity example

`Run.ofList` turns a list of actions, each enabled when it is performed, into a run (followed by
stuttering). `example_delivers`: with one server, one client and `f = 0`, there is a run in which
the black-box consensus instances satisfy their specification and the server delivers the client's
message — so the hypotheses of `theorem8_totalOrder` etc. are satisfiable by non-trivial runs.
-/

namespace Podc.FastByzantineTOB.Flutter

variable {P C M T : Type*} [LinearOrder C] [LinearOrder M] [LinearOrder T] [AddCommMonoid T]
  [Fintype P] [DecidableEq P] [DecidableEq C]

variable (S : Setup P C T)

/-- The state after the first `k` actions of `acts`. -/
noncomputable def listState (s0 : State P C M T) (acts : List (Action P C M T)) (k : ℕ) :
    State P C M T :=
  (acts.take k).foldl (exec S) s0

/-- Every action of `acts` is enabled when it is performed. -/
def ValidList (s0 : State P C M T) (acts : List (Action P C M T)) : Prop :=
  ∀ i (h : i < acts.length), Enabled S (listState S s0 acts i) acts[i]

lemma listState_succ (s0 : State P C M T) (acts : List (Action P C M T)) (i : ℕ)
    (h : i < acts.length) : listState S s0 acts (i + 1) = exec S (listState S s0 acts i) acts[i] := by
  simp only [listState]
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- The run performing a valid list of actions from an initial state, then stuttering. -/
noncomputable def Run.ofList (c0 : P → T) (d0 : C → T) (acts : List (Action P C M T))
    (h : ValidList S (State.init c0 d0) acts) : Run (M := M) S where
  st := listState S (State.init c0 d0) acts
  init := ⟨c0, d0, by simp [listState]⟩
  step k := by
    by_cases hk : k < acts.length
    · exact Or.inr ⟨acts[k], h k hk, listState_succ S _ acts k hk⟩
    · left
      simp [listState, List.take_of_length_le (by omega : acts.length ≤ k),
        List.take_of_length_le (by omega : acts.length ≤ k + 1)]

/-! ### One server, one client -/

/-- One server, one client, `f = 0`, lock quorum `1`, `Δ̃ = ε = 1`. -/
def S1 : Setup Unit Unit ℕ := ⟨∅, ∅, fun _ => isFalse (Set.notMem_empty _), 0, 1, 1, 1⟩

/-- The tag of the client's message (bet `2`). -/
def x1 : Tag Unit Unit ℕ := ⟨2, (), ()⟩

/-- Broadcast, receive, decide, tick, beat, deliver `Observe` and `Time`, process. -/
def acts1 : List (Action Unit Unit Unit ℕ) :=
  [.cBroadcast () (), .cliMsg () () (.message () 2), .decide () x1 true, .tick () 2, .beat (),
   .srvRecv () () (.observe x1), .srvRecv () () (.time 2), .process () x1 true]

lemma valid1 : ValidList S1 (State.init (fun _ => 0) (fun _ => 0)) acts1 := by
  unfold ValidList
  decide

/-- The example run. -/
noncomputable def R1 : Run (M := Unit) S1 := Run.ofList S1 (fun _ => 0) (fun _ => 0) acts1 valid1

lemma R1_final (k : ℕ) (hk : acts1.length ≤ k) :
    R1.st k = listState S1 (State.init (fun _ => 0) (fun _ => 0)) acts1 acts1.length := by
  simp [R1, Run.ofList, listState, List.take_of_length_le hk]

lemma R1_decs (k : ℕ) (x : Tag Unit Unit ℕ) (v : Bool) (h : (x, v) ∈ ((R1.st k).srv ()).decs) :
    x = x1 ∧ v = true := by
  have h' := R1.mono_of_lstep (fun l => l.decs) (fun _ _ h => h.decs_mono) ()
    (le_max_left k acts1.length) h
  rw [R1_final _ (le_max_right _ _)] at h'
  have hd : ((listState S1 (State.init (fun _ => 0) (fun _ => 0)) acts1 acts1.length).srv ()).decs =
      {(x1, true)} := by decide
  rw [hd, Finset.mem_singleton, Prod.mk.injEq] at h'
  exact h'

/-- **Non-vacuity.** In the run `R1` (one server, one client, `f = 0`, lock quorum `1`) the
consensus black box satisfies Representative Validity and Agreement, the hypotheses of
`theorem8_totalOrder` hold (`n = 1 < f + 1 + q = 2`), and the server delivers the client's
message. -/
theorem example_delivers :
    ConRepValidity R1 ∧ ConAgreement R1 ∧ 1 ≤ S1.q ∧ Fintype.card Unit < S1.f + 1 + S1.q ∧
      ((R1.st acts1.length).srv ()).dels = [((), ())] := by
  refine ⟨?_, ?_, by decide, by decide, ?_⟩
  · intro k p x v _ h
    obtain ⟨rfl, rfl⟩ := R1_decs k x v (by simpa using h)
    refine ⟨acts1.length, ?_⟩
    rw [R1_final _ le_rfl]
    decide
  · intro k k' p q x v w _ _ hv hw
    rw [(R1_decs k x v (by simpa using hv)).2, (R1_decs k' x w (by simpa using hw)).2]
  · rw [R1_final _ le_rfl]
    decide

end Podc.FastByzantineTOB.Flutter
