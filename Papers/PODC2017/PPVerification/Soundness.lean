import Papers.PODC2017.PPVerification.Defs

/-!
# Soundness of WS³ (Propositions 19, 20; WS³ ⊆ WS² ⊆ WS)

* `proposition_19`: `WS² = Termination ∧ Consensus`.
* `proposition_20`: LayeredTermination implies Termination.
* `consensus_of_strongConsensus`: StrongConsensus implies Consensus (reachability implies
  potential reachability, Observation 11).
* `ws3_subset_ws2`, `ws3_wellSpecified`: every WS³-protocol is silent and well specified.
-/

namespace Podc.PPVerification

open Cslib.PopulationProtocol Cslib.TransitionSystem

variable {Q Λ : Type*} [DecidableEq Q] [Fintype Q] {P : MProtocol Q Λ}

/-- **Proposition 19.** A protocol belongs to `WS²` (well specified and silent) iff it satisfies
Termination and Consensus. -/
theorem proposition_19 : P.WS2 ↔ P.Termination ∧ P.Consensus := by
  refine ⟨fun ⟨hws, hs⟩ => ⟨MProtocol.silent_iff_termination.1 hs,
    (MProtocol.wellSpecified_iff_consensus hs).1 hws⟩, fun ⟨ht, hc⟩ => ?_⟩
  have hs := MProtocol.silent_iff_termination.2 ht
  exact ⟨(MProtocol.wellSpecified_iff_consensus hs).2 hc, hs⟩

omit [DecidableEq Q] [Fintype Q] in
theorem mem_layersBelow_succ {L : List (Set (Transition Q))} {i : ℕ} (hi : i < L.length)
    {t : Transition Q} : t ∈ layersBelow L (i + 1) ↔ t ∈ layersBelow L i ∨ t ∈ L[i] := by
  simp only [layersBelow, Set.mem_ofPred_eq, List.take_add_one, List.getElem?_eq_getElem hi,
    Option.toList_some, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨S, hS | rfl, ht⟩
    exacts [.inl ⟨S, hS, ht⟩, .inr ht]
  · rintro (⟨S, hS, ht⟩ | ht)
    exacts [⟨S, .inl hS, ht⟩, ⟨_, .inr rfl, ht⟩]

omit [DecidableEq Q] [Fintype Q] in
theorem layersBelow_length (L : List (Set (Transition Q))) :
    layersBelow L L.length = {t | ∃ S ∈ L, t ∈ S} := by
  simp [layersBelow]

omit [Fintype Q] in
/-- **Proposition 20.** LayeredTermination implies Termination. -/
theorem proposition_20 (h : LayeredTermination P) : P.Termination := by
  obtain ⟨L, hpart, hL⟩ := h
  have key : ∀ k ≤ L.length, ∀ C, ∃ D, MReach P.T C D ∧
      Terminal (P.restrict (layersBelow L k)).T D := by
    intro k
    induction k with
    | zero =>
      intro _ C
      refine ⟨C, .refl, terminal_union.2 ⟨?_, MProtocol.terminal_idTrans C⟩⟩
      exact terminal_iff_forall_silent.2 fun t ht => by simp [layersBelow] at ht
    | succ k ih =>
      intro hk C
      obtain ⟨D, hCD, hD⟩ := ih (by omega) C
      obtain ⟨hsil, hdead⟩ := hL k (by omega)
      obtain ⟨D', hDD', hD'⟩ := exists_reach_isSilent_of_forall_silent hsil D
      have hterm' : Terminal (P.restrict L[k]).T D' := terminal_iff_isSilent.2 hD'
      have hbelow := hdead D D' hDD' hD
      refine ⟨D', hCD.trans ?_, ?_⟩
      · refine ((MProtocol.restrict_reach_iff P).1 hDD').mono fun t ht => ?_
        rw [← hpart.cover]
        exact ⟨_, List.getElem_mem _, ht⟩
      · have h1 := terminal_union.1 hbelow
        have h2 := terminal_union.1 hterm'
        refine terminal_union.2 ⟨terminal_iff_forall_silent.2 fun t ht hle => ?_, h1.2⟩
        rcases (mem_layersBelow_succ (by omega)).1 ht with ht | ht
        · exact terminal_iff_forall_silent.1 h1.1 t ht hle
        · exact terminal_iff_forall_silent.1 h2.1 t ht hle
  intro C
  obtain ⟨D, hCD, hD⟩ := key L.length le_rfl C
  rw [MProtocol.restrict, layersBelow_length, hpart.cover] at hD
  exact ⟨D, hCD, (terminal_union.1 hD).1⟩

/-- Every terminal configuration reachable from `C` is potentially reachable from `C`: hence
**StrongConsensus implies Consensus** (§4.2, consequence of Observation 11). -/
theorem consensus_of_strongConsensus (h : StrongConsensus P) : P.Consensus := by
  intro C hC
  obtain ⟨b, hb⟩ := h C hC
  exact ⟨b, fun C' hCC' hterm => hb C' hCC'.potReach hterm⟩

/-- **WS³ ⊆ WS²** (§4.3). -/
theorem ws3_subset_ws2 (h : WS3 P) : P.WS2 :=
  proposition_19.2 ⟨proposition_20 h.1, consensus_of_strongConsensus h.2⟩

/-- **Every WS³-protocol is well specified** (§4.3). -/
theorem ws3_wellSpecified (h : WS3 P) : P.WellSpecified := (ws3_subset_ws2 h).1

end Podc.PPVerification
