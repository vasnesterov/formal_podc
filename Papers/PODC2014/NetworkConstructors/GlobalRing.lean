import Papers.PODC2014.NetworkConstructors.Problems

/-!
# Protocol 6 (Global-Ring) does not construct a spanning ring (Theorem 10 is false)

Theorem 10 of Michail–Spirakis claims that Protocol Global-Ring constructs a spanning ring. The
closing rule `(l, q₁, 0) → (l', q₁', 1)` is meant to join the two endpoints of one line, but an
`l`-endpoint and a `q₁`-endpoint of *different* lines may interact as well; then the two lines
are joined with two blocked nodes in the middle. A blocked `q₁''` node that ends up as an
internal node of degree 2 can never be unblocked (its only unblocking rule needs an active edge to
an `l'`/`l''` node), and with `n = 6` agents the scheduler can reach a closed set of 8
configurations in which the active network alternates forever between a spanning line and a
spanning ring. By global fairness, some fair execution visits all of them infinitely often, so its
output never stabilizes (`globalRing_not_constructs`).
-/

namespace Podc.NetworkConstructors.GlobalRing

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem

/-- States of Protocol 6 (Global-Ring). -/
inductive St | q0 | q1 | q2 | l | w | l' | l'' | q1' | q1''
  deriving DecidableEq, Repr

open St

instance : Fintype St :=
  ⟨{q0, q1, q2, l, w, l', l'', q1', q1''}, fun x => by cases x <;> simp⟩

/-- The transition function of Protocol 6 (Global-Ring); unlisted triples are ineffective. -/
def δ : St → St → Bool → St × St × Bool
  | q0, q0, false => (q1, l, true)
  | l, q0, false => (q2, l, true)
  | l, l, false => (q2, w, true)
  | w, q2, true => (q2, w, true)
  | w, q1, true => (q2, l, true)
  | l, q1, false => (l', q1', true)
  -- `(x', y, 0) → (x'', y, 0)` for `x ∈ {l, q₁}`, `y ∈ {l, w, q₁, q₀}`
  | l', l, false => (l'', l, false)
  | l', w, false => (l'', w, false)
  | l', q1, false => (l'', q1, false)
  | l', q0, false => (l'', q0, false)
  | q1', l, false => (q1'', l, false)
  | q1', w, false => (q1'', w, false)
  | q1', q1, false => (q1'', q1, false)
  | q1', q0, false => (q1'', q0, false)
  -- `(x', y', 0) → (x'', y'', 0)` for `x, y ∈ {l, q₁}`
  | l', l', false => (l'', l'', false)
  | l', q1', false => (l'', q1'', false)
  | q1', l', false => (q1'', l'', false)
  | q1', q1', false => (q1'', q1'', false)
  | l'', q1', true => (l, q1, false)
  | l', q1'', true => (l, q1, false)
  | l'', q1'', true => (l, q1, false)
  | a, b, c => (a, b, c)

/-- Protocol 6 (Global-Ring): initial state `q₀`, all states are output states. -/
def P : Protocol St where
  init := q0
  out _ := true
  δ := δ

/-- A configuration on 6 agents from agent states and a list of active edges. -/
def mk (s : Fin 6 → St) (es : List (Fin 6 × Fin 6)) : Config (Fin 6) St where
  st := s
  edge u v := decide ((u, v) ∈ es) || decide ((v, u) ∈ es)
  symm _ _ := Bool.or_comm _ _

/-- The path from the initial configuration into the bad closed set. -/
def pre : List (Config (Fin 6) St) :=
  [mk ![q0, q0, q0, q0, q0, q0] [],
   mk ![q1, l, q0, q0, q0, q0] [(0, 1)],
   mk ![q1, l, q0, q1, l, q0] [(0, 1), (3, 4)],
   mk ![q1', l, q0, q1, l', q0] [(0, 1), (0, 4), (3, 4)],
   mk ![q1', q2, l, q1, l', q0] [(0, 1), (0, 4), (1, 2), (3, 4)],
   mk ![q1', q2, l', q1', l', q0] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)],
   mk ![q1'', q2, l', q1'', l', q0] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)],
   mk ![q1'', q2, l', q1, l, q0] [(0, 1), (0, 4), (1, 2), (2, 3)],
   mk ![q1'', q2, l', q1, q2, l] [(0, 1), (0, 4), (1, 2), (2, 3), (4, 5)]]

/-- The bad closed set: 8 configurations, strongly connected. -/
def bad : List (Config (Fin 6) St) :=
  [mk ![q1'', q2, l', q1, q2, l] [(0, 1), (0, 4), (1, 2), (2, 3), (4, 5)],
   mk ![q1'', q2, l, q1, q2, l'] [(0, 1), (0, 4), (1, 2), (3, 5), (4, 5)],
   mk ![q1'', q2, l'', q1, q2, l] [(0, 1), (0, 4), (1, 2), (2, 3), (4, 5)],
   mk ![q1'', q2, l', q1', q2, l'] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 5), (4, 5)],
   mk ![q1'', q2, l, q1, q2, l''] [(0, 1), (0, 4), (1, 2), (3, 5), (4, 5)],
   mk ![q1'', q2, l'', q1', q2, l'] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 5), (4, 5)],
   mk ![q1'', q2, l'', q1', q2, l''] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 5), (4, 5)],
   mk ![q1'', q2, l', q1', q2, l''] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 5), (4, 5)]]

/-- A closed walk through all of `bad`. -/
def cyc : List (Config (Fin 6) St) :=
  [mk ![q1'', q2, l', q1, q2, l] [(0, 1), (0, 4), (1, 2), (2, 3), (4, 5)],
   mk ![q1'', q2, l'', q1, q2, l] [(0, 1), (0, 4), (1, 2), (2, 3), (4, 5)],
   mk ![q1'', q2, l'', q1', q2, l'] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 5), (4, 5)],
   mk ![q1'', q2, l, q1, q2, l'] [(0, 1), (0, 4), (1, 2), (3, 5), (4, 5)],
   mk ![q1'', q2, l', q1', q2, l'] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 5), (4, 5)],
   mk ![q1'', q2, l'', q1', q2, l''] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 5), (4, 5)],
   mk ![q1'', q2, l, q1, q2, l''] [(0, 1), (0, 4), (1, 2), (3, 5), (4, 5)],
   mk ![q1'', q2, l', q1', q2, l''] [(0, 1), (0, 4), (1, 2), (2, 3), (3, 5), (4, 5)],
   mk ![q1'', q2, l', q1, q2, l] [(0, 1), (0, 4), (1, 2), (2, 3), (4, 5)]]

instance : DecidableRel (P.Step (V := Fin 6)) := fun C D => by
  unfold Protocol.Step; infer_instance

theorem pre_chain : pre.IsChain (P.Step (V := Fin 6)) := by decide

theorem cyc_chain : cyc.IsChain (P.Step (V := Fin 6)) := by decide

theorem bad_trap : ∀ C ∈ bad, ∀ u v : Fin 6, u ≠ v → P.interact C u v ∈ bad := by decide

theorem bad_sub_cyc : ∀ C ∈ bad, C ∈ cyc := by decide

theorem pre_head : pre.head (by simp [pre]) = P.initConfig := by decide

theorem pre_last : pre.getLast (by simp [pre]) = cyc.head (by simp [cyc]) := by decide

theorem cyc_last : cyc.getLast (by simp [cyc]) = cyc.head (by simp [cyc]) := by decide

/-- Two configurations of the bad set with different outputs: a spanning line and a spanning
ring. -/
theorem output_ne : P.output (cyc.head (by simp [cyc])) ≠ P.output (cyc[2]'(by simp [cyc])) := by
  intro h
  have := congrArg (fun H : (⊤ : SimpleGraph (Fin 6)).Subgraph => H.Adj 3 5) h
  simp [cyc, mk, Protocol.output, P] at this

theorem reach_bad {C D : Config (Fin 6) St} (hC : C ∈ bad) (h : P.Reachable C D) : D ∈ bad := by
  induction h with
  | refl => exact hC
  | tail _ hst ih =>
    obtain ⟨u, v, huv, rfl⟩ := hst
    exact bad_trap _ ih u v huv

/-- **Theorem 10 of Michail–Spirakis is false.** Protocol Global-Ring does not construct a
spanning ring on `n = 6` agents: some globally fair execution never stabilizes its output (it
alternates forever between a spanning line and a spanning ring). -/
theorem globalRing_not_constructs : ¬ P.Constructs (V := Fin 6) IsSpanningRing := by
  have hne : cyc ≠ [] := by simp [cyc]
  have h0 : P.Reachable P.initConfig (cyc.head hne) := by
    rw [← pre_head, ← pre_last]
    exact List.relationReflTransGen_of_exists_isChain _ pre_chain _
  -- every element of `cyc` reaches its head, and the head reaches every element
  have hto : ∀ C ∈ cyc, P.Reachable C (cyc.head hne) :=
    cyc_chain.backwards_induction _ _ (fun _ _ h hy => .head h hy)
      (fun _ => cyc_last ▸ .refl)
  have hfrom : ∀ C ∈ cyc, P.Reachable (cyc.head hne) C :=
    cyc_chain.induction _ _ (fun _ _ h hx => .tail hx h) (fun _ => .refl)
  refine P.not_constructs_of_unstable (C := cyc.head hne) h0 fun D hD => ?_
  have hDb : D ∈ bad := reach_bad (by simp only [cyc, List.head_cons]; decide) hD
  refine ⟨cyc.head hne, cyc[2]'(by simp [cyc]), hto D (bad_sub_cyc D hDb),
    (hto D (bad_sub_cyc D hDb)).trans (hfrom _ (List.getElem_mem _)), output_ne⟩

end Podc.NetworkConstructors.GlobalRing
