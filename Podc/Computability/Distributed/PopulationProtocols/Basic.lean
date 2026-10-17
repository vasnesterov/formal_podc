import Cslib.Computability.Distributed.PopulationProtocols.Basic

-- CSLib candidate: Cslib/Computability/Distributed/PopulationProtocols/Basic.lean (append to the
-- existing file)

/-!
# Deterministic population protocols: closed state sets and runs of two or three agents

Additions to `Cslib/Computability/Distributed/PopulationProtocols/Basic.lean`.

* `Protocol.ClosedStates P H`: interactions between states of `H` only produce states of `H`.
  Then every configuration reachable from a configuration using only states of `H` uses only
  states of `H` (`ClosedStates.reachable`, `ClosedStates.execution`): the usual way to prove a
  per-agent invariant.
* `Protocol.PairReach P`, `Protocol.TripleReach P`: reachability of the states of two (three)
  agents when only these agents interact; `PairReach.lift`, `TripleReach.lift`: such runs lift
  to the whole population, the other agents being idle. Used to build runs by hand from small
  "gadgets" (e.g. reachability proofs of self-stabilization).
-/

namespace Cslib.PopulationProtocol.Protocol

variable {Q A : Type*}

/-! ### Closed sets of states -/

/-- A set of states `H` is *closed* under `P` if an interaction of two agents in states of `H`
only produces states of `H`. -/
def ClosedStates (P : Protocol Q) (H : Set Q) : Prop :=
  ∀ p ∈ H, ∀ q ∈ H, (P.δ p q).1 ∈ H ∧ (P.δ p q).2 ∈ H

variable [DecidableEq A] {P : Protocol Q} {H : Set Q}

/-- An interaction keeps a configuration inside a closed set of states. -/
theorem ClosedStates.interact (hH : P.ClosedStates H) {C : Config A Q} (hC : ∀ x, C x ∈ H)
    {a b : A} (hab : a ≠ b) : ∀ x, P.interact C a b x ∈ H := by
  have h := hH _ (hC a) _ (hC b)
  intro x
  by_cases hxa : x = a
  · subst hxa; rw [interact_self_left]; exact h.1
  · by_cases hxb : x = b
    · subst hxb; rw [interact_self_right _ _ hab]; exact h.2
    · rw [interact_other _ _ hxa hxb]; exact hC x

/-- A step keeps a configuration inside a closed set of states. -/
theorem ClosedStates.step (hH : P.ClosedStates H) {C D : Config A Q} (hC : ∀ x, C x ∈ H)
    (h : P.Step C D) : ∀ x, D x ∈ H := by
  obtain ⟨a, b, hab, rfl⟩ := h
  exact hH.interact hC hab

/-- **Closed sets of states are invariant.** If `C` only uses states of a closed set `H`, so does
every configuration reachable from `C`. -/
theorem ClosedStates.reachable (hH : P.ClosedStates H) {C D : Config A Q} (hC : ∀ x, C x ∈ H)
    (h : P.Reachable C D) : ∀ x, D x ∈ H := by
  induction h with
  | refl => exact hC
  | tail _ hst ih => exact hH.step ih hst

/-- Along an execution starting in a closed set of states, every configuration stays in it. -/
theorem ClosedStates.execution (hH : P.ClosedStates H) (E : P.Execution A)
    (h0 : ∀ x, E.config 0 x ∈ H) (t : ℕ) : ∀ x, E.config t x ∈ H :=
  hH.reachable h0 (E.reachable_of_le t.zero_le)

/-! ### Runs of two or three agents -/

/-- Reachability of pairs of states under repeated interactions of one ordered pair of agents
(the first one initiating). -/
def PairReach (P : Protocol Q) : Q × Q → Q × Q → Prop :=
  Relation.ReflTransGen fun u v => v = P.δ u.1 u.2

/-- One interaction inside a triple of agents (any of the six ordered pairs). -/
inductive TripleStep (P : Protocol Q) : Q × Q × Q → Q × Q × Q → Prop
  | xy (a b c : Q) : TripleStep P (a, b, c) ((P.δ a b).1, (P.δ a b).2, c)
  | yx (a b c : Q) : TripleStep P (a, b, c) ((P.δ b a).2, (P.δ b a).1, c)
  | xz (a b c : Q) : TripleStep P (a, b, c) ((P.δ a c).1, b, (P.δ a c).2)
  | zx (a b c : Q) : TripleStep P (a, b, c) ((P.δ c a).2, b, (P.δ c a).1)
  | yz (a b c : Q) : TripleStep P (a, b, c) (a, (P.δ b c).1, (P.δ b c).2)
  | zy (a b c : Q) : TripleStep P (a, b, c) (a, (P.δ c b).2, (P.δ c b).1)

/-- Reachability inside a triple of agents. -/
def TripleReach (P : Protocol Q) : Q × Q × Q → Q × Q × Q → Prop :=
  Relation.ReflTransGen (TripleStep P)

/-- Transport of a run of two agents along a map that turns each interaction into a step of
`S`. -/
theorem PairReach.map {R : Type*} {S : R → R → Prop} (f : Q × Q → R)
    (hf : ∀ u, S (f u) (f (P.δ u.1 u.2))) {u v : Q × Q} (h : PairReach P u v) :
    Relation.ReflTransGen S (f u) (f v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => subst hst; exact ih.tail (hf _)

/-- A run of the first two agents of a triple (the first one initiating). -/
theorem PairReach.xy {a b a' b' : Q} (c : Q) (h : PairReach P (a, b) (a', b')) :
    TripleReach P (a, b, c) (a', b', c) :=
  PairReach.map (S := TripleStep P) (fun u => (u.1, u.2, c)) (fun _ => TripleStep.xy _ _ _) h

/-- A run of the first two agents of a triple (the second one initiating). -/
theorem PairReach.yx {a b a' b' : Q} (c : Q) (h : PairReach P (b, a) (b', a')) :
    TripleReach P (a, b, c) (a', b', c) :=
  PairReach.map (S := TripleStep P) (fun u => (u.2, u.1, c)) (fun _ => TripleStep.yx _ _ _) h

/-- A run of the first and third agents of a triple (the first one initiating). -/
theorem PairReach.xz {a c a' c' : Q} (b : Q) (h : PairReach P (a, c) (a', c')) :
    TripleReach P (a, b, c) (a', b, c') :=
  PairReach.map (S := TripleStep P) (fun u => (u.1, b, u.2)) (fun _ => TripleStep.xz _ _ _) h

/-- A run of the first and third agents of a triple (the third one initiating). -/
theorem PairReach.zx {a c a' c' : Q} (b : Q) (h : PairReach P (c, a) (c', a')) :
    TripleReach P (a, b, c) (a', b, c') :=
  PairReach.map (S := TripleStep P) (fun u => (u.2, b, u.1)) (fun _ => TripleStep.zx _ _ _) h

/-- A run of the last two agents of a triple (the second one initiating). -/
theorem PairReach.yz {b c b' c' : Q} (a : Q) (h : PairReach P (b, c) (b', c')) :
    TripleReach P (a, b, c) (a, b', c') :=
  PairReach.map (S := TripleStep P) (fun u => (a, u.1, u.2)) (fun _ => TripleStep.yz _ _ _) h

/-- A run of the last two agents of a triple (the third one initiating). -/
theorem PairReach.zy {b c b' c' : Q} (a : Q) (h : PairReach P (c, b) (c', b')) :
    TripleReach P (a, b, c) (a, b', c') :=
  PairReach.map (S := TripleStep P) (fun u => (a, u.2, u.1)) (fun _ => TripleStep.zy _ _ _) h

/-- A run of two agents `a ≠ b` lifts to the whole population (the other agents are idle). -/
theorem PairReach.lift {C : Config A Q} {a b : A} (hab : a ≠ b) {u : Q × Q}
    (h : PairReach P (C a, C b) u) :
    ∃ D, P.Reachable C D ∧ D a = u.1 ∧ D b = u.2 ∧ ∀ z, z ≠ a → z ≠ b → D z = C z := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, rfl, rfl, fun _ _ _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨D, hD, hDa, hDb, hDz⟩ := ih
    subst hst
    refine ⟨P.interact D a b, hD.tail ⟨a, b, hab, rfl⟩, ?_, ?_, ?_⟩
    · rw [interact_self_left, hDa, hDb]
    · rw [interact_self_right _ _ hab, hDa, hDb]
    · intro z hza hzb; rw [interact_other _ _ hza hzb, hDz z hza hzb]

/-- A run of three distinct agents lifts to the whole population (the other agents are idle). -/
theorem TripleReach.lift {C : Config A Q} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) {u : Q × Q × Q} (h : TripleReach P (C x, C y, C z) u) :
    ∃ D, P.Reachable C D ∧ D x = u.1 ∧ D y = u.2.1 ∧ D z = u.2.2 ∧
      ∀ w, w ≠ x → w ≠ y → w ≠ z → D w = C w := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨D, hD, hDx, hDy, hDz, hDw⟩ := ih
    have hyx := hxy.symm
    have hzx := hxz.symm
    have hzy := hyz.symm
    cases hst with
    | xy a b c =>
      refine ⟨P.interact D x y, hD.tail ⟨x, y, hxy, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | yx a b c =>
      refine ⟨P.interact D y x, hD.tail ⟨y, x, hyx, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | xz a b c =>
      refine ⟨P.interact D x z, hD.tail ⟨x, z, hxz, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | zx a b c =>
      refine ⟨P.interact D z x, hD.tail ⟨z, x, hzx, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | yz a b c =>
      refine ⟨P.interact D y z, hD.tail ⟨y, z, hyz, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]
    | zy a b c =>
      refine ⟨P.interact D z y, hD.tail ⟨z, y, hzy, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp_all [Protocol.interact]

end Cslib.PopulationProtocol.Protocol
