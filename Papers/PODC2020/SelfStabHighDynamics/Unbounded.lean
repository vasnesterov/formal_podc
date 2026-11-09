import Papers.PODC2020.SelfStabHighDynamics.Classes

/-!
# Stabilization time cannot be bounded in `TC_Q(Δ)` and `TC_R` (Theorem 6, Corollary 8,
Lemma 13, Corollary 9)

The proof of Theorem 6 replaces the elected process `ℓ` by a fresh process `v ∉ V` and keeps the
states of the other processes. This uses two assumptions that the paper leaves implicit:

* the identifier domain has more than `n` elements (`[Infinite ι]`), so that `v` exists;
* the possible local states of a process depend on the system only through its size
  (`SizeOnly`), so that the states of `V \ {ℓ}` are also possible states in the system
  `V \ {ℓ} ∪ {v}`. This holds for all algorithms of the paper (which know at most `n` and `Δ`).

Both are necessary: see `Counterexamples.lean`.

The theorems do not assume that `A` is pseudo-stabilizing (a bound on the pseudo-stabilization
phase would imply it anyway).
-/

namespace Podc.SelfStabHighDynamics

open Cslib.HeardOf
open StabilizingLEDynamic (DG IsDG DGClass JssB JssQ Jss J_shift)

variable {ι σ : Type*}

/-- The possible local states of a process depend on the system only through its size (the
algorithm may know `n`, but not the set of processes). -/
def SizeOnly (A : SAlg ι σ) : Prop :=
  ∀ V V' : Finset ι, V.card = V'.card → ∀ p ∈ V, p ∈ V' → A.S V p = A.S V' p

/-- If `SP` holds from index `i`, it holds from every later index (recurring specification). -/
theorem Recurring.suffix_mono {SP : Spec ι σ} (hSP : Recurring SP) {V : Finset ι}
    {e : ℕ → ι → σ} {i j : ℕ} (hij : i ≤ j) (h : SP V fun t => e (i + t)) :
    SP V fun t => e (j + t) := by
  have := hSP V _ h (j - i)
  simp only [← Nat.add_assoc, Nat.add_sub_cancel' hij] at this
  exact this

/-- **Theorem 6.** Let `Δ ≥ 1` and `n ≥ 2`. For every algorithm `A` (whose local states depend on
the system only through `n`) and every `f : ℕ → ℕ → ℕ`, some execution of `A` in some graph of
`TC_Q(Δ)` with `n` processes has a pseudo-stabilization phase longer than `f(n, Δ)`: no suffix
starting at an index `i ≤ f(n, Δ)` satisfies `SP_LE`. -/
theorem theorem_6 [Infinite ι] {A : SAlg ι σ} {Δ n : ℕ} (hΔ : 1 ≤ Δ) (hn : 2 ≤ n)
    (hsize : SizeOnly A) (f : ℕ → ℕ → ℕ) :
    ∃ V : Finset ι, V.card = n ∧ ∃ G ∈ JssQ Δ V, ∃ γ ∈ A.Cfg V,
      ∀ i ≤ f n Δ, ¬ spLE A V (fun t => A.exec G γ (i + t)) := by
  classical
  set T := f n Δ
  have hE0 : ∀ W : Finset ι, IsDG W (fun _ => E0) := fun _ _ _ _ h => h.elim
  -- the TVG: `T` rounds without edges, then the static complete graph
  have hGW : ∀ W : Finset ι, splice (fun _ => E0) T (fun _ => K W) ∈ JssQ Δ W := fun W =>
    splice_mem_JssQ (hE0 W) T (JssB_subset_JssQ _ _ (K_mem_JssB hΔ))
  obtain ⟨V, hV⟩ := Infinite.exists_subset_card_eq ι n
  obtain ⟨γ, hγ⟩ := A.cfg_nonempty V
  set G := splice (fun _ => E0) T (fun _ => K V)
  by_cases hgood : ∀ i ≤ T, ¬ spLE A V (fun t => A.exec G γ (i + t))
  · exact ⟨V, hV, G, hGW V, γ, hγ, hgood⟩
  push_neg at hgood
  obtain ⟨i, hiT, hi⟩ := hgood
  obtain ⟨ℓ, hℓV, hℓ⟩ := (recurring_spLE A).suffix_mono hiT hi
  -- replace `ℓ` by a fresh process `v`
  obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset V
  set V' := insert v (V.erase ℓ)
  have hvℓ : v ≠ ℓ := fun h => hv (h ▸ hℓV)
  have hV' : V'.card = n := by
    rw [Finset.card_insert_of_notMem (fun h => hv (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hℓV]
    omega
  obtain ⟨sv, hsv⟩ := A.S_nonempty V' v (Finset.mem_insert_self _ _)
  set γ' : ι → σ := fun p => if p = v then sv else γ p
  have hγ' : γ' ∈ A.Cfg V' := by
    intro p hp
    by_cases hpv : p = v
    · simp only [γ', if_pos hpv]; exact hpv ▸ hsv
    · simp only [γ', if_neg hpv]
      have hpV : p ∈ V := Finset.mem_of_mem_erase ((Finset.mem_insert.mp hp).resolve_left hpv)
      rw [← hsize V V' (hV.trans hV'.symm) p hpV hp]
      exact hγ p hpV
  set G' := splice (fun _ => E0) T (fun _ => K V')
  -- during the first `T` rounds nobody receives anything
  have hagree : ∀ p, p ≠ v → A.exec G' γ' T p = A.exec G γ T p := by
    intro p hpv
    have h1 : A.exec G' γ' T = conf A.step γ' (fun _ => E0) T := conf_splice_le _ _ _ le_rfl
    have h2 : A.exec G γ T = conf A.step γ (fun _ => E0) T := conf_splice_le _ _ _ le_rfl
    rw [h1, h2]
    exact conf_agree_deaf (fun _ _ h => h.elim) (fun _ _ h => h.elim) (by simp [γ', hpv]) T
  refine ⟨V', hV', G', hGW V', γ', hγ', fun j hjT hj => ?_⟩
  obtain ⟨ℓ', hℓ'V', hℓ'⟩ := (recurring_spLE A).suffix_mono hjT hj
  obtain ⟨q, hq, hqℓ⟩ := Finset.exists_mem_ne (show 2 ≤ V.card by omega) ℓ
  have hqv : q ≠ v := fun h => hv (h ▸ hq)
  have hqV' : q ∈ V' := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hqℓ, hq⟩)
  have e1 : A.lid q (A.exec G' γ' (T + 0) q) = ℓ' := hℓ' 0 q hqV'
  have e2 : A.lid q (A.exec G γ (T + 0) q) = ℓ := hℓ 0 q hq
  rw [Nat.add_zero] at e1 e2
  rw [hagree q hqv, e2] at e1
  subst e1
  rcases Finset.mem_insert.mp hℓ'V' with h | h
  · exact hvℓ h.symm
  · exact Finset.notMem_erase _ _ h

/-- **Corollary 8.** Under the assumptions of Theorem 6, there is no `f` such that, for every
system of `n` processes, some set of legitimate configurations is reached within `f(n, Δ)`
rounds in every execution in `TC_Q(Δ)`. -/
theorem corollary_8 [Infinite ι] {A : SAlg ι σ} {Δ n : ℕ} (hΔ : 1 ≤ Δ) (hn : 2 ≤ n)
    (hsize : SizeOnly A) (f : ℕ → ℕ → ℕ) :
    ¬ ∀ V : Finset ι, V.card = n → ∃ L, IsLegit A (JssQ Δ) (spLE A) V L ∧
      ∀ G ∈ JssQ Δ V, ∀ γ ∈ A.Cfg V, ∃ i ≤ f n Δ, A.exec G γ i ∈ L := by
  intro h
  obtain ⟨V, hV, G, hG, γ, hγ, hbad⟩ := theorem_6 hΔ hn hsize f
  obtain ⟨L, hL, hT⟩ := h V hV
  obtain ⟨i, hi, hiL⟩ := hT G hG γ hγ
  apply hbad i hi
  have := hL.2.2 _ (J_shift hG i) _ hiL
  simpa [SAlg.exec, StabilizingLEDynamic.exec_add] using this

/-- **Lemma 13.** Let `n ≥ 2`. For every algorithm `A` (whose local states depend on the system
only through `n`) and every `g : ℕ → ℕ`, some execution of `A` in some graph of `TC_R` with `n`
processes has a pseudo-stabilization phase longer than `g(n)`. -/
theorem lemma_13 [Infinite ι] {A : SAlg ι σ} {n : ℕ} (hn : 2 ≤ n) (hsize : SizeOnly A)
    (g : ℕ → ℕ) :
    ∃ V : Finset ι, V.card = n ∧ ∃ G ∈ Jss V, ∃ γ ∈ A.Cfg V,
      ∀ i ≤ g n, ¬ spLE A V (fun t => A.exec G γ (i + t)) := by
  obtain ⟨V, hV, G, hG, γ, hγ, h⟩ := theorem_6 (Δ := 1) le_rfl hn hsize fun n _ => g n
  exact ⟨V, hV, G, JssQ_subset_Jss 1 V hG, γ, hγ, h⟩

/-- **Corollary 9.** Under the assumptions of Lemma 13, there is no `g` such that, for every
system of `n` processes, some set of legitimate configurations is reached within `g(n)` rounds
in every execution in `TC_R`. -/
theorem corollary_9 [Infinite ι] {A : SAlg ι σ} {n : ℕ} (hn : 2 ≤ n) (hsize : SizeOnly A)
    (g : ℕ → ℕ) :
    ¬ ∀ V : Finset ι, V.card = n → ∃ L, IsLegit A Jss (spLE A) V L ∧
      ∀ G ∈ Jss V, ∀ γ ∈ A.Cfg V, ∃ i ≤ g n, A.exec G γ i ∈ L := by
  intro h
  obtain ⟨V, hV, G, hG, γ, hγ, hbad⟩ := lemma_13 hn hsize g
  obtain ⟨L, hL, hT⟩ := h V hV
  obtain ⟨i, hi, hiL⟩ := hT G hG γ hγ
  apply hbad i hi
  have := hL.2.2 _ (J_shift hG i) _ hiL
  simpa [SAlg.exec, StabilizingLEDynamic.exec_add] using this

end Podc.SelfStabHighDynamics
