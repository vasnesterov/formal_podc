import Papers.PODC2020.SelfStabHighDynamics.Section3

/-!
# Remark 3: the condition `Δ ≥ 2` of Theorem 1 is necessary

In `TC_B(1)` every snapshot is the complete graph on `V`, so the algorithm "`lid(p) :=` the
smallest identifier heard in the round (including `p`)" elects `min V` after one round. It knows
nothing about `n` (so it is size-ambiguous) and the set of configurations where every process
elects `min V` is legitimate and closed.
-/

namespace Podc.SelfStabHighDynamics

open Cslib.HeardOf
open Cslib.DynNet (Journey tdist tdist_le_iff journey_succ_iff journey_self_iff)
open StabilizingLEDynamic (DG IsDG JssB)

variable {ι : Type*} [LinearOrder ι]

open Classical in
/-- The algorithm of Remark 3: the state is `lid(p)`; `p` takes the smallest identifier among
itself and the processes it hears. -/
noncomputable def remark3Alg : SAlg ι ι where
  step p m := if h : {q | (m q).isSome}.Finite then (insert p h.toFinset).min' (by simp) else p
  lid _ s := s
  S _ _ := Set.univ
  S_nonempty _ p _ := ⟨p, Set.mem_univ p⟩

/-- In `TC_B(1)` every process of `V` hears exactly `V` in every round. -/
theorem hears_iff_of_JssB_one {V : Finset ι} {G : DG ι} (hG : G ∈ JssB 1 V) (t : ℕ) {p : ι}
    (hp : p ∈ V) (q : ι) : Hears (G t) p q ↔ q ∈ V := by
  constructor
  · rintro (rfl | h)
    · exact hp
    · exact (hG.1 t q p h).1
  · intro hq
    have h := tdist_le_iff.mp (hG.2 q hq p hp t)
    obtain ⟨y, hy, hyp⟩ := (journey_succ_iff le_rfl).mp h
    rw [journey_self_iff] at hy
    subst hy
    rcases hyp with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h

theorem remark3_exec_succ {V : Finset ι} (hV : V.Nonempty) {G : DG ι} (hG : G ∈ JssB 1 V)
    (γ : ι → ι) (t : ℕ) {p : ι} (hp : p ∈ V) :
    remark3Alg.exec G γ (t + 1) p = V.min' hV := by
  classical
  change remark3Alg.step p (msgs (G t) (remark3Alg.exec G γ t) p) = _
  have hset : {q | (msgs (G t) (remark3Alg.exec G γ t) p q).isSome} = (V : Set ι) := by
    ext q
    simp only [msgs, Set.mem_setOf_eq, Finset.mem_coe]
    rw [← hears_iff_of_JssB_one hG t hp q]
    split_ifs with h <;> simp [h]
  have hfin : {q | (msgs (G t) (remark3Alg.exec G γ t) p q).isSome}.Finite := by
    rw [hset]; exact V.finite_toSet
  have hs : insert p hfin.toFinset = V := by
    ext q
    simp only [Finset.mem_insert, Set.Finite.mem_toFinset]
    rw [hset]
    simp only [Finset.mem_coe]
    constructor
    · rintro (rfl | h)
      · exact hp
      · exact h
    · exact Or.inr
  have hstep : ∀ m : ι → Option ι, remark3Alg.step p m =
      if h : {q | (m q).isSome}.Finite then (insert p h.toFinset).min' (by simp) else p :=
    fun _ => rfl
  rw [hstep, dif_pos hfin]
  exact le_antisymm (Finset.min'_le _ _ (hs ▸ V.min'_mem hV))
    (Finset.le_min' _ _ _ fun y hy => V.min'_le _ (hs ▸ hy))

/-- **Remark 3.** In `TC_B(1)`, the algorithm `remark3Alg` is a self-stabilizing leader election
algorithm whose legitimate configurations (every process of `V` elects `min V`) are closed, and it
is `(1, V)`-ambiguous for every `V` with at least two processes. -/
theorem remark_3 {V : Finset ι} (hV : V.Nonempty) :
    IsLegit remark3Alg (JssB 1) (spLE remark3Alg) V {γ | ∀ p ∈ V, γ p = V.min' hV} ∧
    Closed remark3Alg (JssB 1) V {γ | ∀ p ∈ V, γ p = V.min' hV} ∧
    (2 ≤ V.card → Ambiguous remark3Alg 1 V) := by
  have hall : ∀ G ∈ JssB 1 V, ∀ γ : ι → ι, (∀ p ∈ V, γ p = V.min' hV) →
      ∀ t, ∀ p ∈ V, remark3Alg.exec G γ t p = V.min' hV := by
    intro G hG γ hγ t p hp
    cases t with
    | zero => exact hγ p hp
    | succ t => exact remark3_exec_succ hV hG γ t hp
  refine ⟨⟨fun _ _ _ _ => Set.mem_univ _, fun G hG γ _ => ⟨1, fun p hp =>
    remark3_exec_succ hV hG γ 0 hp⟩, fun G hG γ hγ => ⟨V.min' hV, V.min'_mem hV,
      fun t q hq => hall G hG γ hγ t q hq⟩⟩,
    fun G hG γ hγ t p hp => hall G hG γ hγ t p hp, fun h2 => ⟨Nat.one_pos, by omega,
      fun _ _ _ _ _ => rfl⟩⟩

end Podc.SelfStabHighDynamics
