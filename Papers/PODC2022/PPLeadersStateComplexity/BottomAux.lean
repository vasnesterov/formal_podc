import Papers.PODC2022.PPLeadersStateComplexity.Model

-- CSLib candidate (generic Petri-net / labelled-multigraph infrastructure)
/-!
# Auxiliary lemmas for Section 6 of Leroux (bottom configurations)

* `exists_short_path`: if every configuration reachable from `α` that is not "good" lies in a
  finite set `A` and some good configuration is reachable, then a good configuration is reachable
  by a word of length `≤ |A|` (removal of repeated configurations).
* `exists_reach_bottom`: a finite reachability set contains a bottom configuration.
* `ncard_box_le`: counting configurations with a prescribed restriction to `Q` (in a finite set)
  and small values on `R`.
* `lift_of_netOn`: Lemma 5.2 for a net acting only on the places of `U`.
* The arithmetic of the sequence `λ_n` of the proof of Lemma 6.2 (`mu62`).
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ### Runs staying in a set -/

/-- `RunIn A σ α β`: `σ` leads from `α` to `β` and every configuration visited before the last
one lies in `A`. -/
def RunIn (A : Set (Config P)) : List (Trans P) → Config P → Config P → Prop
  | [], α, β => α = β
  | t :: σ, α, β => α ∈ A ∧ ∃ γ, t.Step α γ ∧ RunIn A σ γ β

/-- Split a run staying in `A` at its last visit of `a`. -/
theorem RunIn.split {A : Set (Config P)} (a : Config P) :
    ∀ {σ : List (Trans P)} {x β : Config P}, RunIn A σ x β →
      RunIn (A \ {a}) σ x β ∨
      ∃ t τ γ, t ∈ σ ∧ (∀ u ∈ τ, u ∈ σ) ∧ t.Step a γ ∧ RunIn (A \ {a}) τ γ β
  | [], _, _, h => Or.inl h
  | t :: σ, x, β, ⟨hx, γ, hs, h⟩ => by
    rcases RunIn.split a h with h' | ⟨t', τ, γ', ht', hτ, hs', h'⟩
    · by_cases hxa : x = a
      · subst hxa
        exact Or.inr ⟨t, σ, γ, List.mem_cons_self .., fun u hu => List.mem_cons_of_mem _ hu, hs, h'⟩
      · exact Or.inl ⟨⟨hx, hxa⟩, γ, hs, h'⟩
    · exact Or.inr ⟨t', τ, γ', List.mem_cons_of_mem _ ht',
        fun u hu => List.mem_cons_of_mem _ (hτ u hu), hs', h'⟩

/-- A run staying in a finite set `A` can be shortened to length `≤ |A|`
(by removing cycles), using only transitions of the original run. -/
theorem RunIn.shorten {A : Set (Config P)} (hA : A.Finite) {σ : List (Trans P)}
    {α β : Config P} (h : RunIn A σ α β) :
    ∃ σ', (∀ t ∈ σ', t ∈ σ) ∧ Run σ' α β ∧ σ'.length ≤ A.ncard := by
  obtain ⟨n, hn⟩ : ∃ n, A.ncard = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing A σ α with
  | _ n ih =>
  cases σ with
  | nil => exact ⟨[], by simp, h, by simp⟩
  | cons t τ =>
    have hα : α ∈ A := h.1
    rcases RunIn.split α h with h' | ⟨t', τ', γ, ht', hτ', hs, h'⟩
    · exact absurd rfl h'.1.2
    · have hlt : (A \ {α}).ncard < n := hn ▸ Set.ncard_sdiff_singleton_lt_of_mem hα hA
      obtain ⟨σ', hσ', hr, hl⟩ := ih _ hlt (hA.subset Set.sdiff_subset) h' rfl
      refine ⟨t' :: σ', ?_, ⟨γ, hs, hr⟩, ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        exacts [ht', hτ' u (hσ' u hu)]
      · have := Set.ncard_sdiff_singleton_add_one hα hA
        simp only [List.length_cons]
        omega

/-- Cut a run at its first good configuration; the configurations visited before are reachable
and not good, hence in `A`. -/
theorem exists_runIn_of_reach {T' : Finset (Trans P)} {α₀ : Config P}
    {Good : Config P → Prop} {A : Set (Config P)}
    (hsub : ∀ γ, Reach T' α₀ γ → ¬ Good γ → γ ∈ A) :
    ∀ {σ : List (Trans P)} {α β : Config P}, Reach T' α₀ α → IsWord T' σ → Run σ α β →
      Good β → ∃ σ₁ β₁, IsWord T' σ₁ ∧ RunIn A σ₁ α β₁ ∧ Good β₁
  | [], _, β, _, _, h, hg => ⟨[], β, fun _ h => by simp at h, h, hg⟩
  | t :: σ, α, β, hr, hw, ⟨γ, hs, h⟩, hg => by
    by_cases hα : Good α
    · exact ⟨[], α, fun _ h => by simp at h, rfl, hα⟩
    · have ht : t ∈ T' := hw t (List.mem_cons_self ..)
      have hr' : Reach T' α₀ γ :=
        hr.trans ⟨[t], fun u hu => by simp at hu; exact hu ▸ ht, run_singleton.2 hs⟩
      obtain ⟨σ₁, β₁, h1, h2, h3⟩ := exists_runIn_of_reach hsub hr'
        (fun u hu => hw u (List.mem_cons_of_mem _ hu)) h hg
      refine ⟨t :: σ₁, β₁, fun u hu => ?_, ⟨hsub α hr hα, γ, hs, h2⟩, h3⟩
      rcases List.mem_cons.1 hu with rfl | hu
      exacts [ht, h1 u hu]

/-- **Short paths.** If every non-good configuration reachable from `α` lies in the finite set
`A`, and a good configuration is reachable from `α`, then a good configuration is reachable from
`α` by a word of length at most `|A|`. -/
theorem exists_short_path {T' : Finset (Trans P)} {α : Config P} {Good : Config P → Prop}
    {A : Set (Config P)} (hA : A.Finite) (hsub : ∀ γ, Reach T' α γ → ¬ Good γ → γ ∈ A)
    (h : ∃ β, Reach T' α β ∧ Good β) :
    ∃ σ β, IsWord T' σ ∧ Run σ α β ∧ Good β ∧ σ.length ≤ A.ncard := by
  obtain ⟨β, ⟨σ, hw, hr⟩, hg⟩ := h
  obtain ⟨σ₁, β₁, h1, h2, h3⟩ := exists_runIn_of_reach hsub (Reach.refl T' α) hw hr hg
  obtain ⟨σ', hσ', hr', hl⟩ := h2.shorten hA
  exact ⟨σ', β₁, fun t ht => h1 t (hσ' t ht), hr', h3, hl⟩

/-- A finite reachability set contains a configuration `β` such that every configuration
reachable from `β` can reach `β` back. -/
theorem exists_reach_bottom {T' : Finset (Trans P)} {α : Config P}
    (hfin : {γ | Reach T' α γ}.Finite) :
    ∃ β, Reach T' α β ∧ ∀ γ, Reach T' β γ → Reach T' γ β := by
  obtain ⟨n, hn⟩ : ∃ n, {γ | Reach T' α γ}.ncard = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with
  | _ n ih =>
  by_cases hb : ∀ γ, Reach T' α γ → Reach T' γ α
  · exact ⟨α, Reach.refl _ _, hb⟩
  · push Not at hb
    obtain ⟨γ, hγ, hγα⟩ := hb
    have hsub : {x | Reach T' γ x} ⊂ {x | Reach T' α x} :=
      ⟨fun x hx => hγ.trans hx,
        fun h => hγα (h (show α ∈ {x | Reach T' α x} from Reach.refl T' α))⟩
    obtain ⟨β, hβ, hbot⟩ := ih _ (hn ▸ Set.ncard_lt_ncard hsub hfin) (hfin.subset hsub.1) rfl
    exact ⟨β, hγ.trans hβ, hbot⟩

/-! ### Vanishing places, restricted nets, lifting -/

theorem Run.eq_zero_of_vanish {V : Finset P} {σ : List (Trans P)} {α β : Config P}
    (hσ : ∀ t ∈ σ, ∀ p ∉ V, t.1 p = 0 ∧ t.2 p = 0) (h : Run σ α β)
    (hα : ∀ p ∉ V, α p = 0) : ∀ p ∉ V, β p = 0 := by
  induction σ generalizing α with
  | nil => rw [← run_nil.1 h]; exact hα
  | cons t σ ih =>
    obtain ⟨γ, h1, h2⟩ := h
    refine ih (fun u hu => hσ u (List.mem_cons_of_mem _ hu)) h2 ?_
    intro p hp
    rw [Trans.step_iff] at h1
    rw [h1.2]
    simp [hα p hp, (hσ t (List.mem_cons_self ..) p hp).2]

/-- Configurations reachable in a net acting on `V` from a configuration vanishing outside `V`
vanish outside `V`. -/
theorem Reach.eq_zero_of_netOn {V : Finset P} {T' : Finset (Trans P)} (hT : NetOn V T')
    {α β : Config P} (h : Reach T' α β) (hα : ∀ p ∉ V, α p = 0) : ∀ p ∉ V, β p = 0 := by
  obtain ⟨σ, hw, hr⟩ := h
  exact hr.eq_zero_of_vanish (fun t ht => hT t (hw t ht)) hα

theorem netOn_resNet (Q : Finset P) (T : Finset (Trans P)) : NetOn Q (resNet Q T) := by
  intro t ht p hp
  obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 ht
  simp [Trans.res, hp]

theorem resNet_resNet_of_subset {Q Q' : Finset P} (h : Q ⊆ Q') (T : Finset (Trans P)) :
    resNet Q (resNet Q' T) = resNet Q T := by
  simp only [resNet, Finset.image_image]
  congr 1
  funext t
  simp [Trans.res, Finset.inter_eq_left.2 h]

/-- In `T|_∅` nothing moves. -/
theorem eq_of_reach_resNet_empty {T : Finset (Trans P)} {x y : Config P}
    (h : Reach (resNet ∅ T) x y) : y = x := by
  obtain ⟨σ, hw, hr⟩ := h
  induction σ generalizing x with
  | nil => exact hr.symm
  | cons t σ ih =>
    obtain ⟨γ, h1, h2⟩ := hr
    obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 (hw t (List.mem_cons_self ..))
    rw [Trans.step_iff] at h1
    have : γ = x := by rw [h1.2]; funext p; simp [Trans.res]
    subst this
    exact ih (fun u hu => hw u (List.mem_cons_of_mem _ hu)) h2

theorem isBottom_resNet_empty (T : Finset (Trans P)) (ρ : Config P) :
    IsBottom (resNet ∅ T) (res ∅ ρ) ∧ (component (resNet ∅ T) (res ∅ ρ)).ncard = 1 := by
  have hc : component (resNet ∅ T) (res ∅ ρ) = {res ∅ ρ} := by
    ext x
    simp only [component, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, -⟩; exact eq_of_reach_resNet_empty h
    · rintro rfl; exact ⟨Reach.refl _ _, Reach.refl _ _⟩
  refine ⟨⟨by rw [hc]; exact Set.finite_singleton _, fun β hβ => ?_⟩, by rw [hc]; simp⟩
  rw [eq_of_reach_resNet_empty hβ]; exact Reach.refl _ _

/-- **Lemma 5.2** for a net acting on `U` only: a run of `T|_Q` can be lifted as soon as the
places of `U \ Q` hold at least `|w| ‖T‖∞` agents. -/
theorem lift_of_netOn {T : Finset (Trans P)} {U Q : Finset P} (hT : NetOn U T)
    {w' : List (Trans P)} (hw' : IsWord (resNet Q T) w') {α γ : Config P}
    (h : Run w' (res Q α) γ) (hα : ∀ p ∈ U, p ∉ Q → w'.length * netNorm T ≤ α p) :
    ∃ w β, IsWord T w ∧ w.length = w'.length ∧ Run w α β ∧ res Q β = γ ∧
      ∀ p ∈ U, p ∉ Q → α p ≤ β p + w'.length * netNorm T := by
  obtain ⟨w, hw, rfl⟩ := hw'.exists_of_resNet
  obtain ⟨β, h1, h2, h3⟩ := run_lift (M := fun p => if p ∈ U then netNorm T else 0)
    (fun t ht p _ => by
      by_cases hpU : p ∈ U
      · simp only [hpU, ite_true]; exact (t.fst_le_supNorm p).trans (le_netNorm (hw t ht))
      · simp [hpU, (hT t (hw t ht) p hpU).1])
    h (fun p hp => by
      by_cases hpU : p ∈ U
      · simpa [hpU] using hα p hpU hp
      · simp [hpU])
  refine ⟨w, β, hw, by simp, h1, h2, fun p hpU hp => ?_⟩
  have := h3 p hp
  simpa [hpU] using this

/-! ### Counting -/

/-- The configurations vanishing outside `Q ∪ R`, with restriction to `Q` in a finite set `C`
and values `< θ` on `R`, form a finite set with at most `|C| θ^|R|` elements. -/
theorem ncard_box_le {C : Set (Config P)} (hC : C.Finite) (Q R : Finset P) (θ : ℕ) :
    {x : Config P | (∀ p, p ∉ Q → p ∉ R → x p = 0) ∧ res Q x ∈ C ∧ ∀ p ∈ R, x p < θ}.Finite ∧
    {x : Config P | (∀ p, p ∉ Q → p ∉ R → x p = 0) ∧ res Q x ∈ C ∧ ∀ p ∈ R, x p < θ}.ncard ≤
      C.ncard * θ ^ R.card := by
  set A := {x : Config P | (∀ p, p ∉ Q → p ∉ R → x p = 0) ∧ res Q x ∈ C ∧ ∀ p ∈ R, x p < θ}
  have : Finite C := hC.to_subtype
  let f : A → C × (R → Fin θ) :=
    fun x => (⟨res Q x.1, x.2.2.1⟩, fun p => ⟨x.1 p, x.2.2.2 p p.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    apply Subtype.ext
    funext p
    by_cases hpQ : p ∈ Q
    · have := congrFun h1 p
      simpa [hpQ] using this
    · by_cases hpR : p ∈ R
      · have := congrFun h2 ⟨p, hpR⟩
        simpa using congrArg Fin.val this
      · simp only
        rw [hx.1 p hpQ hpR, hy.1 p hpQ hpR]
  have : Finite A := Finite.of_injective f hf
  refine ⟨Set.toFinite A, ?_⟩
  rw [← Nat.card_coe_set_eq]
  calc Nat.card A ≤ Nat.card (C × (R → Fin θ)) := Nat.card_le_card_of_injective f hf
    _ = C.ncard * θ ^ R.card := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_coe_set_eq]
      simp

/-! ### Arithmetic of the proof of Lemma 6.2 -/

/-- The sequence `λ` of the proof of Lemma 6.2, indexed backwards: `mu62 s N Λ k = λ_{d-k}`,
so `λ_d = Λ` and `λ_n = s λ_{n+1}^{d-n} N + λ_{n+1}`. -/
def mu62 (s N Λ : ℕ) : ℕ → ℕ
  | 0 => Λ
  | k + 1 => s * mu62 s N Λ k ^ (k + 1) * N + mu62 s N Λ k

theorem mu62_zero (s N Λ : ℕ) : mu62 s N Λ 0 = Λ := rfl

theorem mu62_succ (s N Λ k : ℕ) :
    mu62 s N Λ (k + 1) = s * mu62 s N Λ k ^ (k + 1) * N + mu62 s N Λ k := rfl

theorem mu62_mono (s N Λ : ℕ) : Monotone (mu62 s N Λ) :=
  monotone_nat_of_le_succ fun k => by rw [mu62_succ]; exact Nat.le_add_left _ _

theorem one_le_mu62 {s N Λ : ℕ} (h : 1 ≤ Λ) (k : ℕ) : 1 ≤ mu62 s N Λ k :=
  h.trans (mu62_mono s N Λ (Nat.zero_le k))

theorem mu62_le {s N Λ : ℕ} (hΛ : s * N + 1 ≤ Λ) (k : ℕ) :
    mu62 s N Λ k ≤ Λ ^ ((k + 1) ^ k) := by
  induction k with
  | zero => simp [mu62]
  | succ k ih =>
    have hΛ1 : 1 ≤ Λ := by omega
    have h1 : 1 ≤ mu62 s N Λ k := one_le_mu62 hΛ1 k
    have hlt : (k + 1) ^ (k + 1) < (k + 1 + 1) ^ (k + 1) :=
      Nat.pow_lt_pow_left (by omega) (by omega)
    calc mu62 s N Λ (k + 1) = s * mu62 s N Λ k ^ (k + 1) * N + mu62 s N Λ k := rfl
      _ ≤ s * mu62 s N Λ k ^ (k + 1) * N + mu62 s N Λ k ^ (k + 1) := by
          gcongr; exact Nat.le_self_pow (by omega) _
      _ = (s * N + 1) * mu62 s N Λ k ^ (k + 1) := by ring
      _ ≤ Λ * (Λ ^ ((k + 1) ^ k)) ^ (k + 1) := by gcongr
      _ = Λ ^ (1 + (k + 1) ^ (k + 1)) := by
          rw [← pow_mul, ← pow_succ]; ring
      _ ≤ Λ ^ ((k + 1 + 1) ^ (k + 1)) := Nat.pow_le_pow_right hΛ1 (by omega)

/-- `λ_1^d ≤ λ_d^(d^d)`. -/
theorem mu62_pow_le {s N Λ : ℕ} (hΛ : s * N + 1 ≤ Λ) (d : ℕ) :
    mu62 s N Λ (d - 1) ^ d ≤ Λ ^ (d ^ d) := by
  rcases d with _ | m
  · simp; omega
  · simp only [Nat.add_sub_cancel]
    calc mu62 s N Λ m ^ (m + 1) ≤ (Λ ^ ((m + 1) ^ m)) ^ (m + 1) :=
          Nat.pow_le_pow_left (mu62_le hΛ m) _
      _ = Λ ^ ((m + 1) ^ (m + 1)) := by rw [← pow_mul, ← pow_succ]

/-! ### Arithmetic of the proof of Theorem 6.1 -/

theorem one_le_pow_self' (d : ℕ) : 1 ≤ d ^ d := by
  rcases d with _ | d
  · simp
  · exact Nat.one_le_pow _ _ (Nat.succ_pos _)

theorem pow_self_le_pow_self {d' d : ℕ} (h : d' ≤ d) : d' ^ d' ≤ d ^ d := by
  rcases Nat.eq_zero_or_pos d' with rfl | hd'
  · simpa using one_le_pow_self' d
  · calc d' ^ d' ≤ d ^ d' := Nat.pow_le_pow_left h _
      _ ≤ d ^ d := Nat.pow_le_pow_right (by omega) h

theorem one_add_le_two_pow_pow_self (d : ℕ) : 1 + d ≤ 2 ^ (d ^ d) := by
  have h1 : d < 2 ^ d := Nat.lt_two_pow_self
  have h2 : d ≤ d ^ d := by
    rcases d with _ | d
    · simp
    · exact Nat.le_self_pow (by omega) _
  calc 1 + d ≤ 2 ^ d := by omega
    _ ≤ 2 ^ (d ^ d) := Nat.pow_le_pow_right (by omega) h2

/-- One step of the induction in the proof of Theorem 6.1:
`(1 + d'(1 + s‖T‖ + ‖ρ_i‖)^(d'^d')) s ≤ a X^(d^d+1)` when `s ≤ X`, `‖ρ_i‖ ≤ (1 + ‖T‖) X`. -/
theorem arith61_step {d d' N R s r X : ℕ} (hd' : d' ≤ d) (hX : 1 ≤ X) (hs : s ≤ X)
    (hr : r ≤ (1 + N) * X) :
    (1 + d' * (1 + s * N + r) ^ (d' ^ d')) * s ≤
      (1 + d) * (2 + 2 * N + R) ^ (d ^ d) * X ^ (d ^ d + 1) := by
  set K := d ^ d
  have hK : d' ^ d' ≤ K := pow_self_le_pow_self hd'
  have hΛ : 1 + s * N + r ≤ (2 + 2 * N) * X := by
    have : s * N ≤ X * N := Nat.mul_le_mul_right _ hs
    nlinarith
  have hY : 1 ≤ (2 + 2 * N) ^ K * X ^ K := Nat.one_le_iff_ne_zero.2 (by positivity)
  calc (1 + d' * (1 + s * N + r) ^ (d' ^ d')) * s
      ≤ (1 + d * (1 + s * N + r) ^ K) * X := by
        gcongr
      _ ≤ (1 + d * ((2 + 2 * N) * X) ^ K) * X := by gcongr
      _ = (1 + d * ((2 + 2 * N) ^ K * X ^ K)) * X := by rw [mul_pow]
      _ ≤ ((1 + d) * ((2 + 2 * N) ^ K * X ^ K)) * X := by gcongr; nlinarith
      _ = (1 + d) * (2 + 2 * N) ^ K * X ^ (K + 1) := by ring
      _ ≤ (1 + d) * (2 + 2 * N + R) ^ K * X ^ (K + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

end Podc.PPLeadersStateComplexity
