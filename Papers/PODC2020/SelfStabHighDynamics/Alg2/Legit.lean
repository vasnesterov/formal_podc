import Papers.PODC2020.SelfStabHighDynamics.Alg2.Exec

/-!
# Algorithm 2: legitimate configurations (Lemmas 8 and 9, Theorems 5 and 7)
-/

namespace Podc.SelfStabHighDynamics.Alg2

open Cslib.HeardOf Cslib.DynNet
open StabilizingLEDynamic (DG IsDG JssQ JssB)

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ}

/-- Legitimate configurations of Algorithm 2 for `V` (Section 5.2): every process `p ∈ V` has
`lid(p) = id(ℓ)` (`ℓ = min V`) and the identifiers of `members(p)` are exactly `V`. -/
def Legit (V : Finset ι) (γ : ι → MSt ι) : Prop :=
  ∀ p (hp : p ∈ V), (γ p).lid = V.min' ⟨p, hp⟩ ∧ ∀ x, x ∈ keys (γ p).mem ↔ x ∈ V

theorem legit_iff {V : Finset ι} (hV : V.Nonempty) {γ : ι → MSt ι} :
    Legit V γ ↔ ∀ p ∈ V, (γ p).lid = V.min' hV ∧ ∀ x, x ∈ keys (γ p).mem ↔ x ∈ V :=
  Iff.rfl

variable {V : Finset ι} {G : DG ι} {γ : ι → MSt ι}

/-- One step from a legitimate configuration of Algorithm 2 (in any dynamic graph with vertex
set `V`) leads to a legitimate configuration. -/
theorem legit_succ (hG : IsDG V G) {t : ℕ} (hc : (alg Δ).exec G γ t ∈ (alg Δ).Cfg V)
    (hL : Legit V ((alg Δ).exec G γ t)) : Legit V ((alg Δ).exec G γ (t + 1)) := by
  intro p hp
  obtain ⟨hn, hinv, -⟩ := mem_S.1 (hc p hp)
  have hkV : ∀ r ∈ V, ∀ y ∈ ((alg Δ).exec G γ t r).mem, y.1 ∈ V := fun r hr y hy =>
    ((hL r hr).2 y.1).1 (mem_keys.2 ⟨y.2, hy⟩)
  have hmb : ∀ x ∈ mbx Δ G γ t p, x.1 ≠ p → x.1 ∈ V := by
    intro x hx _
    obtain ⟨r, hr, hx, -⟩ := (mem_mbx hG).1 hx
    exact hkV r (hG t r p hr).1 x hx
  have hkeys : ∀ x, x ∈ keys ((alg Δ).exec G γ (t + 1) p).mem ↔ x ∈ V := by
    intro x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := mem_keys.1 hx
      rw [exec_succ] at hb
      exact round_keys hp (hkV p hp) hmb _ hb
    · intro hx
      obtain ⟨b, hb⟩ := mem_keys.1 (((hL p hp).2 x).2 hx)
      have := (tail_of_forall (hkV p hp) hb).round (Δ := Δ) (mb := mbx Δ G γ t p) hp hn hinv hmb
      rw [exec_succ]
      exact this.mem_keys
  exact ⟨by rw [lid_exec_succ]; exact minKey_eq_min' hp hkeys, hkeys⟩

/-- **Closure of `Cfg ∩ Legit`** (remark before Lemma 8), in any dynamic graph with vertex set
`V`. -/
theorem legit_exec (hG : IsDG V G) (hγ : γ ∈ (alg Δ).Cfg V ∩ {γ | Legit V γ}) (t : ℕ) :
    (alg Δ).exec G γ t ∈ (alg Δ).Cfg V ∩ {γ | Legit V γ} := by
  induction t with
  | zero => exact hγ
  | succ t ih => exact ⟨exec_cfg hG hγ.1 _, legit_succ hG ih.1 ih.2⟩

/-- If all identifiers of `V` are in every `members(p)` at time `t ≥ 1`, the configuration is
legitimate (the `members` queues have at most `n = |V|` distinct identifiers). -/
theorem legit_of_keys (hG : IsDG V G) (hγ : γ ∈ (alg Δ).Cfg V) {t : ℕ} (ht : 1 ≤ t)
    (h : ∀ p ∈ V, ∀ q ∈ V, q ∈ keys ((alg Δ).exec G γ t p).mem) :
    Legit V ((alg Δ).exec G γ t) := by
  intro p hp
  obtain ⟨hn, ⟨hlen, hnd⟩, -⟩ := mem_S.1 (exec_cfg hG hγ t p hp)
  have hsub : V ⊆ (keys ((alg Δ).exec G γ t p).mem).toFinset := fun q hq =>
    List.mem_toFinset.2 (h p hp q hq)
  have hcard : (keys ((alg Δ).exec G γ t p).mem).toFinset.card ≤ V.card := by
    rw [List.toFinset_card_of_nodup hnd]; simp only [keys, List.length_map]; omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hkeys : ∀ x, x ∈ keys ((alg Δ).exec G γ t p).mem ↔ x ∈ V := by
    intro x; rw [heq]; simp
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact ⟨by rw [lid_exec_succ]; exact minKey_eq_min' hp hkeys, hkeys⟩

/-- **Lemma 9**, in the stronger form: in `TC_Q(Δ)` there is `T ≥ Δ` such that every
configuration from the end of Round `T + Δ` on is legitimate. -/
theorem legit_eventually (hG : G ∈ JssQ Δ V) (hγ : γ ∈ (alg Δ).Cfg V) :
    ∃ T ≥ Δ, ∀ t ≥ T + Δ, Legit V ((alg Δ).exec G γ t) := by
  have h : ∀ x ∈ V ×ˢ V, ∃ j ≥ Δ + 1, tdist G j x.1 x.2 ≤ Δ := by
    intro x hx
    rw [Finset.mem_product] at hx
    exact hG.2 x.1 hx.1 x.2 hx.2 (Δ + 1)
  choose! f hf1 hf2 using h
  refine ⟨max (Δ + 1) ((V ×ˢ V).sup f), by omega, fun t ht => ?_⟩
  refine legit_of_keys hG.1 hγ (by omega) fun p hp q hq => ?_
  have hx : (q, p) ∈ V ×ˢ V := Finset.mem_product.2 ⟨hq, hp⟩
  have hle : f (q, p) ≤ (V ×ˢ V).sup f := Finset.le_sup (f := f) hx
  exact mem_of_tdist hG.1 hγ hq (by have := hf1 _ hx; omega) (by have := hf1 _ hx; omega)
    (hf2 _ hx) t (by omega)

/-- **Theorem 7** (0-indexed): in `TC_B(Δ)` (`Δ ≥ 1`), every configuration from the end of Round
`2Δ` on is legitimate. -/
theorem legit_bounded (hΔ : 0 < Δ) (hG : G ∈ JssB Δ V) (hγ : γ ∈ (alg Δ).Cfg V) :
    ∀ t ≥ 2 * Δ, Legit V ((alg Δ).exec G γ t) := by
  intro t ht
  refine legit_of_keys hG.1 hγ (by omega) fun p hp q hq => ?_
  exact mem_of_tdist hG.1 hγ hq le_rfl hΔ (hG.2 q hq p hp Δ) t (by omega)

end Podc.SelfStabHighDynamics.Alg2
