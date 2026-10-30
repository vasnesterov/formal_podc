import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolMain

/-!
# Proposition 16 and almost self-stabilisation (Section 7.3, Appendix B.3, Section 8)

**Proposition 16.** If a population machine `A` of size `n` decides `φ`, then there is a population
protocol with at most `16 n` states and a single initial state that decides
`φ'(x) ⇔ x ≥ i ∧ φ(x - i)` for `i = |F| ≤ n`; moreover (Theorem 2's argument) it is almost
self-stabilising: every fair run from a configuration with at least `|Q'|` agents in the initial
state stabilises to `φ'(|C|)`.

The protocol is `Machine.toProtocol A`: the protocol `PP` of Appendix B.3 (`Machine.Tr`) with the
output broadcast (`bcast`), on the valid states `Q* × {true, false}` (`Machine.U'`).

Hypothesis `hdom` (all pointer domains nonempty) is part of Definition 6 of the paper but not of the
Lean structure `Machine`; without it (e.g. `L = 0`, so that `𝓕_IP = ∅`) a machine has no initial
configuration and decides every predicate vacuously.
-/

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem M2P

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

theorem count_le_count_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) (a : α)
    (s : Multiset α) : s.count a ≤ (s.map f).count (f a) := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  exact Multiset.card_le_card (Multiset.monotone_filter_right s (fun x hx => by rw [hx]))

/-- The initial state `(X_1)^{v_1}_none` with opinion `false`, as a state of `toProtocol`. -/
noncomputable def initS' (hdom : ∀ X, (A.dom X).Nonempty) : (A.U' : Finset (St Q F × Bool)) :=
  ⟨(A.initS, false), by simp [U', A.initS_mem_U hdom]⟩

theorem toProtocol_I (hdom : ∀ X, (A.dom X).Nonempty) : A.toProtocol.I = {A.initS' hdom} := by
  ext x
  simp only [toProtocol, PProtocol.restrictTo, bcastPP, Set.mem_preimage, Set.mem_singleton_iff,
    initS']
  rw [Subtype.ext_iff]

theorem card_toProtocol_ge (hdom : ∀ X, (A.dom X).Nonempty) :
    Fintype.card F ≤ Fintype.card (A.U' : Finset (St Q F × Bool)) := by
  refine Fintype.card_le_of_injective
    (fun X => ⟨(.ptr X (A.v0 X) .none, false), by
      simp [U', A.mem_U_ptr, A.v0_mem_dom' hdom X, A.none_mem_stg X]⟩) ?_
  intro X Y h
  have := congrArg (fun s => s.1.1) h
  simp only [St.ptr.injEq] at this
  exact this.1

/-- The reachability statement for the final protocol. -/
theorem toProtocol_reach {φ : ℕ → Bool} (hA : A.Decides φ) (hdom : ∀ X, (A.dom X).Nonempty)
    {C₀ : Multiset (A.U' : Finset (St Q F × Bool))}
    (h : (Fintype.card F ≤ ((C₀.map Subtype.val).map Prod.fst).count A.initS) ∨
      (C₀.map Subtype.val = Multiset.replicate (Multiset.card C₀) (A.initS, false) ∧
        0 < Multiset.card C₀)) :
    ∀ C, Reach A.toProtocol.Step C₀ C → ∃ D, Reach A.toProtocol.Step C D ∧
      StableOut A.toProtocol.Step A.toProtocol.out
        (decide (Fintype.card F ≤ Multiset.card C₀) && φ (Multiset.card C₀ - Fintype.card F)) D := by
  apply PProtocol.restrictTo_reach_stable (A.bcast_closed hdom)
  by_cases hk : Fintype.card F ≤ ((C₀.map Subtype.val).map Prod.fst).count A.initS
  · have hle : Fintype.card F ≤ Multiset.card C₀ := by
      have := Multiset.count_le_card A.initS ((C₀.map Subtype.val).map Prod.fst)
      simp only [Multiset.card_map] at this; omega
    have := A.bcast_large hA hdom hk
    simp only [Multiset.card_map] at this
    simpa [hle] using this
  · obtain ⟨hrep, hpos⟩ := h.resolve_left hk
    have hn : Multiset.card C₀ < Fintype.card F := by
      by_contra hcon
      apply hk
      rw [hrep, Multiset.map_replicate, Multiset.count_replicate_self]
      omega
    rw [hrep]
    intro c hc
    refine ⟨c, .refl, fun e he => ?_⟩
    have := (A.bcast_small hn e (hc.trans he)).1
    rw [show decide (Fintype.card F ≤ Multiset.card C₀) = false by simp; omega]
    rw [Bool.false_and]
    refine A.bcastPP_out ?_ (fun x hx => (this x hx).1)
    intro h0
    have := A.bcastPP.reach_card_eq (hc.trans he)
    rw [h0] at this; simp at this; omega

end Machine

open Classical Machine in
/-- **Proposition 16** of [Czerner, *Population Protocols Decide Double-exponential Thresholds*,
PODC 2023]: a population machine of size `n` deciding `φ` (with nonempty pointer domains, as
required by Definition 6) yields a population protocol with at most `16 n` states and one initial
state deciding `φ'(x) ⇔ x ≥ i ∧ φ(x - i)` for some `i ≤ n` (namely `i = |F|`); the protocol is
moreover almost self-stabilising (Definition 7; this is the argument of Theorem 2). -/
theorem proposition_16 {Q F : Type} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
    (A : Machine Q F) {φ : ℕ → Bool} (hA : A.Decides φ) (hdom : ∀ X, (A.dom X).Nonempty) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (PP : PProtocol S) (i : ℕ),
      i ≤ A.size ∧ Fintype.card S ≤ 16 * A.size ∧ (∃ q, PP.I = {q}) ∧
      PP.DecidesCount (fun x => decide (i ≤ x) && φ (x - i)) ∧
      PP.AlmostSelfStabilising (fun x => decide (i ≤ x) && φ (x - i)) := by
  refine ⟨A.U', inferInstance, inferInstance, A.toProtocol, Fintype.card F, ?_, ?_,
    ⟨_, A.toProtocol_I hdom⟩, ?_, ?_⟩
  · unfold size; omega
  · rw [Fintype.card_coe, A.card_U']
    have := A.card_U_le_size; omega
  · intro E hE hfair
    apply A.toProtocol.stabilises_of_reach _ E rfl hfair
    apply A.toProtocol_reach hA hdom
    right
    refine ⟨Multiset.eq_replicate.2 ⟨by simp, fun b hb => ?_⟩, hE.1⟩
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    have := hE.2 a ha
    rw [A.toProtocol_I hdom, Set.mem_singleton_iff] at this
    rw [this]; rfl
  · intro E hE hfair
    apply A.toProtocol.stabilises_of_reach _ E rfl hfair
    apply A.toProtocol_reach hA hdom
    left
    have h1 := A.card_toProtocol_ge hdom
    have h2 : Multiset.card ((E.st 0).filter (· ∈ A.toProtocol.I)) =
        (E.st 0).count (A.initS' hdom) := by
      rw [Multiset.count_eq_card_filter_eq]
      congr 1
      apply Multiset.filter_congr
      intro x _
      rw [A.toProtocol_I hdom, Set.mem_singleton_iff, eq_comm]
    have h3 : (E.st 0).count (A.initS' hdom) ≤
        ((E.st 0).map Subtype.val).count (A.initS, false) :=
      count_le_count_map Subtype.val (A.initS' hdom) (E.st 0)
    have h4 : ((E.st 0).map Subtype.val).count (A.initS, false) ≤
        (((E.st 0).map Subtype.val).map Prod.fst).count A.initS :=
      count_le_count_map Prod.fst (A.initS, false) ((E.st 0).map Subtype.val)
    have : Fintype.card (A.U' : Finset (St Q F × Bool)) ≤
        Multiset.card ((E.st 0).filter (· ∈ A.toProtocol.I)) := by
      convert hE
    omega


end Podc.PPDoubleExpThresholds
