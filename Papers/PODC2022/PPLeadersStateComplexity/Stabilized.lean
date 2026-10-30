import Papers.PODC2022.PPLeadersStateComplexity.Protocol
import Podc.Computability.PetriNets.Rackoff

/-!
# Small stable configurations (Section 5 of Leroux)

A configuration `ρ` is `(T, F)`-stabilized if every configuration reachable from it has no agent
outside `F`. For `F = γ⁻¹(0)` these are the `0`-output stable configurations (Lemma 5.1).
Rackoff's bound (Lemma 5.3, proved in `Podc/Computability/PetriNets/Rackoff.lean`) shows that
stabilization only depends on the small values of a configuration (Lemma 5.4).
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- `ρ` is `(T, F)`-stabilized: every `β` with `ρ →T* β` vanishes outside `F`. -/
def Stabilized (T : Finset (Trans P)) (F : Finset P) (ρ : Config P) : Prop :=
  ∀ β, Reach T ρ β → ∀ p ∉ F, β p = 0

theorem Stabilized.of_reach {T : Finset (Trans P)} {F : Finset P} {ρ ρ' : Config P}
    (h : Stabilized T F ρ) (hr : Reach T ρ ρ') : Stabilized T F ρ' :=
  fun β hβ => h β (hr.trans hβ)

/-- **Lemma 5.1.** For a protocol whose preorder is the reachability relation of a Petri net `T`
and `F = γ⁻¹(0)`, a configuration is `(T, F)`-stabilized iff it is `0`-output stable. -/
theorem lemma_5_1 (Pr : Protocol P) (T : Finset (Trans P))
    (hR : ∀ α β, Pr.R α β ↔ Reach T α β) (ρ : Config P) :
    Stabilized T (Finset.univ.filter fun p => Pr.γ p = Out.zero) ρ ↔ ρ ∈ Pr.S0 := by
  simp only [Stabilized, Protocol.S0, Protocol.outputs, Set.mem_setOf_eq, hR,
    Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall_congr' fun β => imp_congr_right fun _ => ?_
  constructor
  · rintro h j ⟨p, hp, rfl⟩
    by_contra hne
    exact absurd (h p hne) hp.ne'
  · intro h p hp
    by_contra hne
    exact hp (h ⟨p, Nat.pos_of_ne_zero hne, rfl⟩)

/-! ### Rackoff's bound (Lemma 5.3) -/

/-- The `Cslib` Petri net of a finite net `T` (transitions are the elements of `T`). -/
def toPN (T : Finset (Trans P)) : Cslib.PetriNet P T :=
  ⟨fun t p => t.1.1 p, fun t p => t.1.2 p⟩

/-- `ℕ^P → ℤ^P`. -/
def toZ (α : Config P) : P → ℤ := fun p => α p

theorem run_iff_valid {T : Finset (Trans P)} (w : List T) (α : Config P) :
    (∃ β, Run (w.map Subtype.val) α β) ↔ (toPN T).Valid Finset.univ w (toZ α) := by
  induction w generalizing α with
  | nil => simp
  | cons t w ih =>
    simp only [List.map_cons, run_cons, Cslib.PetriNet.valid_cons, Finset.mem_univ, true_imp_iff]
    constructor
    · rintro ⟨β, γ, h1, h2⟩
      rw [Trans.step_iff] at h1
      refine ⟨fun p => by simpa [toPN, toZ] using h1.1 p, ?_⟩
      have : (toPN T).fire t (toZ α) = toZ γ := by
        funext p; have : t.1.1 p ≤ α p := h1.1 p
        simp only [Cslib.PetriNet.fire, toPN, toZ, h1.2, Pi.add_apply, Pi.sub_apply]; push_cast
        omega
      rw [this, ← ih]; exact ⟨β, h2⟩
    · rintro ⟨h1, h2⟩
      have hle : t.1.1 ≤ α := fun p => by simpa [toPN, toZ] using h1 p
      have : (toPN T).fire t (toZ α) = toZ (α - t.1.1 + t.1.2) := by
        funext p; have : t.1.1 p ≤ α p := hle p
        simp only [Cslib.PetriNet.fire, toPN, toZ, Pi.add_apply, Pi.sub_apply]; push_cast
        omega
      rw [this, ← ih] at h2
      obtain ⟨β, hβ⟩ := h2
      exact ⟨β, _, Trans.step_iff.2 ⟨hle, rfl⟩, hβ⟩

theorem run_toZ {T : Finset (Trans P)} {w : List T} {α β : Config P}
    (h : Run (w.map Subtype.val) α β) : (toPN T).run w (toZ α) = toZ β := by
  induction w generalizing α with
  | nil => simp only [List.map_nil, run_nil] at h; simp [h]
  | cons t w ih =>
    obtain ⟨γ, h1, h2⟩ := h
    rw [Cslib.PetriNet.run_cons, ← ih h2]
    congr 1
    funext p
    have := h1.apply_eq p
    simp only [Cslib.PetriNet.fire, toPN, toZ, Trans.delta] at this ⊢
    rw [this]; ring

-- CSLib candidate (with `Podc/Computability/PetriNets/Rackoff.lean`)
/-- Rackoff's bound in the form `(R + M)^(k^k)`. -/
theorem rackoffBound_lt {M R : ℕ} (hM : 1 ≤ M) (hR : 1 ≤ R) :
    ∀ k, 1 ≤ k → Cslib.PetriNet.rackoffBound M R k < (R + M) ^ (k ^ k) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    set x := R + M with hx
    have hx2 : 2 ≤ x := by omega
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      simp [Cslib.PetriNet.rackoffBound]; omega
    rcases Nat.lt_or_ge k 2 with h1' | h2
    · obtain rfl : k = 1 := by omega
      simp only [Cslib.PetriNet.rackoffBound, mul_zero, zero_add, pow_one, add_zero]
      norm_num
      -- (M R + R)^2 + R < (R + M)^4
      have e1 : (R + M) ^ 2 ≥ R * (M + 1) + 2 := by nlinarith
      have e2 : (R + M) ^ 4 = ((R + M) ^ 2) ^ 2 := by ring
      rw [e2]
      calc (M * R + R) ^ 2 + R < (R * (M + 1) + 2) ^ 2 := by nlinarith
        _ ≤ ((R + M) ^ 2) ^ 2 := Nat.pow_le_pow_left e1 2
    have ihk := ih h1
    set g := Cslib.PetriNet.rackoffBound M R k with hg
    set e := k ^ k with he
    have hxe : 1 ≤ x ^ e := Nat.one_le_pow _ _ (by omega)
    have hMg : M * g + R ≤ x ^ (e + 1) := by
      rw [pow_succ]
      nlinarith
    have hpow : (M * g + R) ^ (k + 1) ≤ x ^ ((e + 1) * (k + 1)) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hMg _
    have hexp : (e + 1) * (k + 1) + 1 ≤ (k + 1) ^ (k + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have h1 : (j + 3) ^ (j + 2) ≥ (j + 3) * (j + 2) ^ (j + 1) := by
        rw [pow_succ']
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have h2 : (j + 2) ^ (j + 1) ≥ 2 := by
        calc (j + 2) ^ (j + 1) ≥ (j + 2) ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≥ 2 := by simp
      have h3 : e = (j + 2) * (j + 2) ^ (j + 1) := by rw [he, pow_succ']
      have h4 : (j + 2 + 1) ^ (j + 2 + 1) = (j + 3) * (j + 3) ^ (j + 2) := by
        rw [pow_succ']
      rw [h4, h3]
      nlinarith
    have hlt : g < x ^ ((e + 1) * (k + 1)) :=
      lt_of_lt_of_le ihk (Nat.pow_le_pow_right (by omega) (by nlinarith))
    calc Cslib.PetriNet.rackoffBound M R (k + 1) = (M * g + R) ^ (k + 1) + g := rfl
      _ < 2 * x ^ ((e + 1) * (k + 1)) := by omega
      _ ≤ x * x ^ ((e + 1) * (k + 1)) := Nat.mul_le_mul_right _ hx2
      _ = x ^ ((e + 1) * (k + 1) + 1) := by ring
      _ ≤ x ^ ((k + 1) ^ (k + 1)) := Nat.pow_le_pow_right (by omega) hexp

/-- **Lemma 5.3** (Rackoff). If `ρ` is `T`-coverable from `α`, then it is covered by a word of
length at most `(‖ρ‖∞ + ‖T‖∞)^(|P|^|P|)`. -/
theorem lemma_5_3 {T : Finset (Trans P)} {α β ρ : Config P} (h : Reach T α β) (hρ : ρ ≤ β) :
    ∃ σ : List (Trans P), ∃ γ : Config P, IsWord T σ ∧
      σ.length ≤ (supNorm ρ + netNorm T) ^ (Fintype.card P ^ Fintype.card P) ∧
      Run σ α γ ∧ ρ ≤ γ := by
  obtain ⟨σ, hσ, hrun⟩ := h
  -- degenerate cases
  by_cases hM : netNorm T = 0
  · have htriv : ∀ t ∈ σ, t = (0, 0) := by
      intro t ht
      have := le_netNorm (hσ t ht); rw [hM] at this
      ext p
      · exact Nat.le_zero.1 ((t.fst_le_supNorm p).trans this)
      · exact Nat.le_zero.1 ((t.snd_le_supNorm p).trans this)
    have : β = α := by
      funext p
      have := hrun.apply_eq p
      have h0 : wordDelta σ p = 0 := by
        simp only [wordDelta]
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
        rw [htriv t ht]; simp [Trans.delta]
      omega
    exact ⟨[], α, fun _ h => by simp at h, by simp, rfl, this ▸ hρ⟩
  by_cases hR : supNorm ρ = 0
  · refine ⟨[], α, fun _ h => by simp at h, by simp, rfl, fun p => ?_⟩
    have := le_supNorm ρ p; rw [hR] at this
    simp only [Nat.le_zero] at this; simp [this]
  -- main case
  have hσ' : ∀ t ∈ σ, t ∈ T := hσ
  let w : List T := σ.pmap (fun t ht => ⟨t, ht⟩) hσ'
  have hw : w.map Subtype.val = σ := by
    simp only [w]; rw [List.map_pmap]; simp
  have hval : (toPN T).Valid Finset.univ w (toZ α) := (run_iff_valid w α).1 ⟨β, hw ▸ hrun⟩
  have hcov : (toPN T).Covers Finset.univ w (toZ α) ρ := by
    intro p _
    rw [run_toZ (hw ▸ hrun)]
    simpa [toZ] using hρ p
  obtain ⟨w', hsub, hval', hcov', hlen⟩ := Cslib.PetriNet.exists_short_cover (M := netNorm T)
    (R := supNorm ρ) (fun t p => (t.1.fst_le_supNorm p).trans (le_netNorm t.2))
    (fun p => le_supNorm ρ p) hval hcov
  obtain ⟨γ, hγ⟩ := (run_iff_valid w' α).2 hval'
  refine ⟨w'.map Subtype.val, γ, fun t ht => ?_, ?_, hγ, fun p => ?_⟩
  · obtain ⟨t', -, rfl⟩ := List.mem_map.1 ht; exact t'.2
  · rw [List.length_map]
    refine hlen.trans ?_
    rw [Finset.card_univ]
    rcases Nat.eq_zero_or_pos (Fintype.card P) with hd | hd
    · rw [hd]; simp [Cslib.PetriNet.rackoffBound]
    · exact (rackoffBound_lt (Nat.one_le_iff_ne_zero.2 hM) (Nat.one_le_iff_ne_zero.2 hR) _ hd).le
  · have := hcov' p (Finset.mem_univ p)
    rw [run_toZ hγ] at this
    simpa [toZ] using this

/-- **Lemma 5.4.** Let `ρ` be `(T, F)`-stabilized, `h ≥ ‖T‖∞ (1 + ‖T‖∞)^(|P|^|P|)` positive, and
`R = {p | ρ(p) < h}`. Every configuration `α` with `α|_R ≤ ρ|_R` is `(T, F)`-stabilized. -/
theorem lemma_5_4 {T : Finset (Trans P)} {F : Finset P} {ρ : Config P} (hρ : Stabilized T F ρ)
    {h : ℕ} (hh0 : 0 < h) (hh : netNorm T * (1 + netNorm T) ^ (Fintype.card P ^ Fintype.card P) ≤ h)
    {α : Config P} (hα : res (Finset.univ.filter fun p => ρ p < h) α ≤
      res (Finset.univ.filter fun p => ρ p < h) ρ) :
    Stabilized T F α := by
  set R := Finset.univ.filter fun p => ρ p < h with hRdef
  intro β hβ p hpF
  by_contra hne
  have hρp : ρ p = 0 := hρ ρ (Reach.refl T ρ) p hpF
  have hpR : p ∈ R := by simp [hRdef, hρp, hh0]
  obtain ⟨σ, η, hσ, hlen, hrun, hcov⟩ := lemma_5_3 hβ (ρ := Pi.single p 1) (fun q => by
    by_cases hq : q = p
    · subst hq; simp; omega
    · simp [hq])
  have hsn : supNorm (Pi.single p 1 : Config P) ≤ 1 := supNorm_le_iff.2 fun q => by
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq]
  have hlen' : σ.length ≤ (1 + netNorm T) ^ (Fintype.card P ^ Fintype.card P) :=
    hlen.trans (Nat.pow_le_pow_left (by omega) _)
  set μ := res R ρ - res R α with hμ
  have hsum : res R α + μ = res R ρ := by
    funext q; have : res R α q ≤ res R ρ q := hα q; simp only [hμ, Pi.add_apply, Pi.sub_apply]; omega
  have h1 : Run (σ.map (Trans.res R)) (res R ρ) (res R η + μ) := by
    rw [← hsum]; exact (hrun.res R).add μ
  obtain ⟨δ, hδ, hδR, -⟩ := lemma_5_2 hσ h1 (fun q hq => by
    have : h ≤ ρ q := by simpa [hRdef] using hq
    calc σ.length * netNorm T ≤ (1 + netNorm T) ^ (Fintype.card P ^ Fintype.card P) * netNorm T :=
          Nat.mul_le_mul_right _ hlen'
      _ ≤ h := by rw [mul_comm]; exact hh
      _ ≤ ρ q := this)
  have hδp : δ p ≠ 0 := by
    have := congrFun hδR p
    simp only [res_apply_of_mem hpR, Pi.add_apply] at this
    have := hcov p; simp at this
    omega
  exact hδp (hρ δ ⟨σ, hσ, hδ⟩ p hpF)

end Podc.PPLeadersStateComplexity
