import Papers.PODC2014.DistributedUniversality.SCfromUC

/-!
# Section 4.4: `(k, k − p)`-SC solves `(p + 1)`-set agreement

Raynal, Stainer, Taubenfeld, *Distributed Universality* (PODC 2014), Section 4.4 and Figure 3.

The reduction: process `i` proposes the constant vector `[v_i, …, v_i]` to a `(k, k − p)`-SC object,
obtains `k − p` pairs, and decides the maximum of the `k − p` values it obtained. The paper's argument
("for any process `p_i`, at most `p` values among the `k` values proposed are greater than the value
decided by `p_i`") is correct; we verify it combinatorially, for an arbitrary set of deciding
processes and an arbitrary linearly ordered value type (`setAgreement_of_SC`).

We also record the two "extreme cases" of Section 4.4: `(k, k)`-SC solves consensus (decide the value
of entry `0`, `consensus_of_SC_kk`), and a vector of `k` consensus decisions is a `(k, k)`-SC outcome
(`SC_kk_of_consensus`). That `(k, 1)`-SC is `k`-SC holds by definition (`IsSCOutcome` with `ℓ = 1`
is exactly the `k`-SC specification), so it is not restated.
-/

namespace Podc.DistributedUniversality.Abstract

variable {P V : Type*}

/-- **`m`-set agreement** among the deciding processes `S` (with proposals `v`): at most `m`
distinct decisions, each of them proposed by some process. -/
def IsSetAgreement [DecidableEq V] (m : ℕ) (S : Finset P) (v : P → V) (out : P → V) : Prop :=
  (S.image out).card ≤ m ∧ ∀ i ∈ S, ∃ j, out i = v j

/-- The maximum of the decided values of a `(k, ℓ)`-SC outcome exists when `ℓ ≥ 1`. -/
lemma IsSCOutcome.exists_isGreatest [LinearOrder V] {k ℓ : ℕ} {S : Finset P}
    {prop : P → Fin k → V} {D : P → Finset (Fin k)} {d : P → Fin k → V}
    (h : IsSCOutcome k ℓ S prop D d) (hℓ : 0 < ℓ) {i : P} (hi : i ∈ S) :
    ∃ o, IsGreatest (d i '' ↑(D i)) o := by
  have hne : (D i).Nonempty := Finset.card_pos.1 (by rw [h.card_eq i hi]; exact hℓ)
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (D i) (d i) hne
  exact ⟨d i x, ⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmax y hy⟩

/-- **Section 4.4, "From `(k, k − p)`-SC to `(p + 1)`-set agreement"** of [Raynal–Stainer–Taubenfeld,
PODC 2014]. Each process `i` proposes the constant vector `fun _ => v i` to a `(k, k − p)`-SC object
and decides `out i`, the maximum of the `k − p` values it obtains. Then the decisions solve
`(p + 1)`-set agreement. -/
theorem setAgreement_of_SC [LinearOrder V] {k p : ℕ} {S : Finset P} {v : P → V}
    {D : P → Finset (Fin k)} {d : P → Fin k → V}
    (h : IsSCOutcome k (k - p) S (fun j _ => v j) D d) (out : P → V)
    (hout : ∀ i ∈ S, IsGreatest (d i '' ↑(D i)) (out i)) :
    IsSetAgreement (p + 1) S v out := by
  classical
  refine ⟨?_, fun i hi => ?_⟩
  swap
  · obtain ⟨x, hx, hxo⟩ := (hout i hi).1
    obtain ⟨j, hj⟩ := h.valid i hi x hx
    exact ⟨j, hxo ▸ hj⟩
  rcases (S.image out).eq_empty_or_nonempty with hE | hne
  · simp [hE]
  -- the process `i₀` with the smallest decision
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image S out (Finset.image_nonempty.1 hne)
  set m := out i₀
  -- a global value per entry (well defined by agreement)
  let w : Fin k → V := fun x => if hx : ∃ j ∈ S, x ∈ D j then d hx.choose x else m
  have hw : ∀ j ∈ S, ∀ x ∈ D j, w x = d j x := by
    intro j hj x hx
    have hx' : ∃ j ∈ S, x ∈ D j := ⟨j, hj, hx⟩
    simp only [w]
    rw [dite_eq_left_of_eq_true (eq_true hx')]
    exact h.agree _ hx'.choose_spec.1 j hj x hx'.choose_spec.2 hx
  -- every decision other than `m` is the value of an entry outside `D i₀`
  have hsub : S.image out ⊆ insert m ((D i₀)ᶜ.image w) := by
    intro o ho
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ho
    rcases (hmin j hj).eq_or_lt with heq | hlt
    · simp [m, heq]
    · obtain ⟨x, hx, hxo⟩ := (hout j hj).1
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨x, ?_, by rw [hw j hj x hx, hxo]⟩)
      rw [Finset.mem_compl]
      intro hx₀
      have : d i₀ x ≤ m := (hout i₀ hi₀).2 ⟨x, hx₀, rfl⟩
      rw [← h.agree j hj i₀ hi₀ x hx hx₀, hxo] at this
      exact absurd hlt (not_lt.2 this)
  calc (S.image out).card ≤ (insert m ((D i₀)ᶜ.image w)).card := Finset.card_le_card hsub
    _ ≤ ((D i₀)ᶜ.image w).card + 1 := Finset.card_insert_le _ _
    _ ≤ (D i₀)ᶜ.card + 1 := by gcongr; exact Finset.card_image_le
    _ ≤ p + 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h.card_eq i₀ hi₀]
      omega

/-- **Section 4.4, "`(k, k)`-SC is consensus" (first direction)**: with a `(k, k)`-SC object, `k ≥ 1`,
deciding the value of entry `0` solves consensus (agreement and validity). -/
theorem consensus_of_SC_kk {k : ℕ} [NeZero k] {S : Finset P} {prop : P → Fin k → V}
    {D : P → Finset (Fin k)} {d : P → Fin k → V} (h : IsSCOutcome k k S prop D d) :
    (∀ i ∈ S, ∀ j ∈ S, d i 0 = d j 0) ∧ ∀ i ∈ S, ∃ j, d i 0 = prop j 0 := by
  have huniv : ∀ i ∈ S, D i = Finset.univ := fun i hi =>
    Finset.eq_univ_of_card _ (by rw [h.card_eq i hi, Fintype.card_fin])
  exact ⟨fun i hi j hj => h.agree i hi j hj 0 (by simp [huniv i hi]) (by simp [huniv j hj]),
    fun i hi => h.valid i hi 0 (by simp [huniv i hi])⟩

/-- **Section 4.4, "`(k, k)`-SC is consensus" (second direction)**: if all processes decide the same
vector `c` from `k` consensus instances (entry `x` of `c` proposed by some process in entry `x`),
the outcome is a `(k, k)`-SC outcome. -/
theorem SC_kk_of_consensus {k : ℕ} {S : Finset P} {prop : P → Fin k → V} (c : Fin k → V)
    (hc : ∀ x, ∃ j, c x = prop j x) :
    IsSCOutcome k k S prop (fun _ => Finset.univ) (fun _ => c) :=
  ⟨fun _ _ => by simp, fun _ _ x _ => hc x, fun _ _ _ _ _ _ _ => rfl⟩

/-- Non-vacuity of `setAgreement_of_SC`: with `k = 2`, `p = 1`, three processes proposing
`0, 1, 2` and deciding on entries `{0}`, `{1}`, `{1}` with entry values `0` and `1`, the hypotheses
hold and two distinct values are decided. -/
example : IsSCOutcome 2 (2 - 1) (Finset.univ : Finset (Fin 3)) (fun j _ => (j : ℕ))
    (fun i => if i = 0 then {0} else {1}) (fun _ x => (x : ℕ)) ∧
    ((Finset.univ : Finset (Fin 3)).image (fun i => if i = 0 then 0 else 1)).card = 2 := by
  refine ⟨⟨by decide, ?_, by decide⟩, by decide⟩
  intro i _ x _
  exact ⟨⟨x, by omega⟩, rfl⟩

end Podc.DistributedUniversality.Abstract
