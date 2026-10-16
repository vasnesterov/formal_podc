import Papers.PODC2012.MaximalMatching.Outputs

/-!
# Zero-templates and the base case (§3.6, §3.8 of Hirvonen–Suomela)

* Lemma 13 (`lemma13`): a fixed-point-free map `h : [k] → [k]` with `k ≥ 3` has distinct
  `c₁, c₂, c₃` with `h(c₁) = c₂ ≠ h(c₃)`.
* Lemma 14 (`exists_critical_one`): there is a 1-critical pair.
-/

namespace Papers.PODC2012.MaximalMatching

open Cslib.ColourSystem FreeCox Pointwise Template

variable {k : ℕ}

/-- Lemma 13, combinatorial core. -/
theorem lemma13 (hk : 3 ≤ k) (f : Fin k → Fin k) (hf : ∀ c, f c ≠ c) :
    ∃ c₁ c₂ c₃ : Fin k, c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧ f c₁ = c₂ ∧ f c₃ ≠ c₂ := by
  set one : Fin k := ⟨0, by omega⟩
  by_cases ha : f (f one) ≠ one
  · exact ⟨f one, f (f one), one, (hf _).symm, hf one, ha, rfl, (hf (f one)).symm⟩
  · push Not at ha
    -- a colour `c ∉ {one, f one}`
    obtain ⟨c, hc1, hc2⟩ : ∃ c : Fin k, c ≠ one ∧ c ≠ f one := by
      by_cases h1 : f one = ⟨1, by omega⟩
      · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
        · simp [one, Fin.ext_iff]
        · rw [h1]; simp [Fin.ext_iff]
      · refine ⟨⟨1, by omega⟩, ?_, Ne.symm h1⟩
        simp [one, Fin.ext_iff]
    by_cases hc : f c = f one
    · exact ⟨f one, one, c, hf one, hc2.symm, hc1.symm, ha, by rw [hc]; exact hf one⟩
    · exact ⟨one, f one, c, (hf one).symm, hc1.symm, hc2.symm, rfl, hc⟩

/-! ### Zero-templates and pair templates -/

/-- The 0-template `(Z, ĉ)` with `Z = {e}`. -/
def zeroT (c : Fin k) : Template k := ⟨{1}, fun _ => c⟩

theorem isTemplate_zeroT (c : Fin k) : IsTemplate 0 (zeroT c) := by
  classical
  refine ⟨⟨rfl, fun x hx c' hc' => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [Set.mem_singleton_iff.1 hx] at hc'; simp at hc'
  · rw [Set.mem_singleton_iff.1 hx]
    simp only [Finset.card_eq_zero]
    ext c'; simp [zeroT, gen_ne_one]
  · rw [Set.mem_singleton_iff.1 hx]; simp [zeroT, gen_ne_one]

/-- A template whose forbidden colour is constant `c` has the same realisation everywhere as the
0-template `(Z, ĉ)`. -/
theorem real_eq_of_forb_const {h : ℕ} {T : Template k} (hT : IsTemplate h T) {c : Fin k}
    (hc : ∀ t ∈ T.carrier, T.forb t = c) {t : FreeCox k} (ht : t ∈ T.carrier) :
    T.real t = (zeroT c).real 1 := by
  refine (T.realGraph.view_map_of_reachable (zeroT c).realGraph (fun _ => 1) t ?_).symm
  intro x b hb c'
  have hbT := realGraph_walk_mem ht hb
  have e1 := realGraph_step_isSome hT hbT c'
  have e2 := realGraph_step_isSome (isTemplate_zeroT c) (Set.mem_singleton 1) c'
  rw [hc b hbT] at e1
  have e3 : ∀ y, (zeroT c).realGraph.step 1 c' = some y → y = 1 := by
    intro y hy
    rcases (tGraph_step_eq_some hy).2 with ⟨h1, -⟩ | ⟨-, -, h1⟩
    · simp [zeroT, gen_ne_one] at h1
    · exact h1
  simp only [zeroT] at e2 e3
  cases hG : T.realGraph.step b c' <;> cases hH : (zeroT c).realGraph.step 1 c' <;>
    simp_all [zeroT]

/-- The 1-template on `{e, c₂}` with forbidden colours `f`. -/
def pairT (c₂ : Fin k) (f : FreeCox k → Fin k) : Template k := ⟨{1, gen c₂}, f⟩

theorem mem_pairT {c₂ : Fin k} {f : FreeCox k → Fin k} {x : FreeCox k} :
    x ∈ (pairT c₂ f).carrier ↔ x = 1 ∨ x = gen c₂ := Iff.rfl

theorem colours_pairT {c₂ : Fin k} {f : FreeCox k → Fin k} {x : FreeCox k}
    (hx : x ∈ (pairT c₂ f).carrier) (c : Fin k) :
    c ∈ colours (pairT c₂ f).carrier x ↔ c = c₂ := by
  rw [mem_colours, mem_pairT]
  rcases hx with rfl | rfl
  · simp [gen_ne_one]
  · constructor
    · rintro (h | h)
      · have := congrArg (gen c₂ * ·) h
        simp only [← mul_assoc, gen_mul_gen, one_mul, mul_one] at this
        exact gen_injective this
      · have := congrArg (gen c₂ * ·) h
        simp only [← mul_assoc, gen_mul_gen, one_mul] at this
        exact absurd this (gen_ne_one c)
    · rintro rfl; left; exact gen_mul_gen c

theorem isTemplate_pairT {c₂ : Fin k} {f : FreeCox k → Fin k} (hf : ∀ x, f x ≠ c₂) :
    IsTemplate 1 (pairT c₂ f) := by
  classical
  refine ⟨⟨Or.inl rfl, fun x hx c hc => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rcases hx with rfl | rfl
    · simp at hc
    · have : len (gen c₂ * gen c) = 0 := by simp at hc; omega
      exact Or.inl (len_eq_zero.1 this)
  · have : colours (pairT c₂ f).carrier x = {c₂} := by
      ext c; rw [colours_pairT hx]; simp
    rw [this, Finset.card_singleton]
  · rw [colours_pairT hx]; exact hf x

/-! ### The base case -/

variable {A : Algorithm k} {r : ℕ}

/-- Lemma 14: there exists a 1-critical pair. -/
theorem exists_critical_one (hk : 3 ≤ k) (hA : Good A r) :
    ∃ S T : Template k, IsCritical A 1 S T := by
  -- the function `h(c) = A(Z, ĉ, e)`
  have hZ : ∀ c, ∃ c', (zeroT c).out A 1 = some c' ∧ c' ≠ c := by
    intro c
    obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.1
      (hA.out_ne_none (isTemplate_zeroT c) (by omega) (Set.mem_singleton 1))
    exact ⟨c', hc', hA.out_ne_forb (isTemplate_zeroT c) (Set.mem_singleton 1) hc'⟩
  choose hfun hfun_out hfun_ne using hZ
  obtain ⟨c₁, c₂, c₃, h12, h13, h23, hc12, hc32⟩ := lemma13 hk hfun hfun_ne
  set K := pairT c₂ (fun _ => c₁)
  set L := pairT c₂ (fun _ => c₃)
  set X := pairT c₂ (fun x => if x = 1 then c₁ else c₃)
  have hK : IsTemplate 1 K := isTemplate_pairT (fun _ => h12)
  have hL : IsTemplate 1 L := isTemplate_pairT (fun _ => h23.symm)
  have hX : IsTemplate 1 X := isTemplate_pairT (fun x => by split_ifs <;> [exact h12; exact h23.symm])
  have houtK : ∀ v ∈ K.carrier, K.out A v = some c₂ := by
    intro v hv
    have := hfun_out c₁
    unfold out at this ⊢
    rw [real_eq_of_forb_const hK (fun _ _ => rfl) hv, this, hc12]
  have houtL : ∀ v ∈ L.carrier, L.out A v = some (hfun c₃) := by
    intro v hv
    have := hfun_out c₃
    unfold out at this ⊢
    rw [real_eq_of_forb_const hL (fun _ _ => rfl) hv, this]
  have hc2K : gen c₂ ∈ X.carrier := Or.inr rfl
  by_cases hXo : X.out A 1 = some c₂
  · -- case (ii)
    refine ⟨(gen c₂)⁻¹ • X, (gen c₂)⁻¹ • L, hX.smul hc2K, hL.smul (Or.inr rfl), ⟨?_, ?_⟩, ?_, ?_⟩
    · rfl
    · intro s hs hs1
      have : s = 1 := len_eq_zero.1 (by omega)
      subst this
      simp [X, L, pairT, gen_ne_one]
    · rw [matched_inv_smul, mul_one]
      rintro ⟨c, hc, hco⟩
      rw [colours_pairT (Or.inr rfl)] at hc
      rw [houtL _ (Or.inr rfl), hc] at hco
      exact hc32 (Option.some.inj hco)
    · intro s hs
      rw [matched_inv_smul]
      rw [smul_carrier, mem_inv_smul] at hs
      refine ⟨c₂, (colours_pairT hs c₂).2 rfl, ?_⟩
      rcases hs with hs | hs <;> rw [hs]
      · exact hXo
      · have := hA.out_mul_gen hX (Or.inl rfl) hXo (by simpa using hc2K)
        simpa using this
  · -- case (i)
    refine ⟨K, X, hK, hX, ⟨rfl, ?_⟩, ?_, ?_⟩
    · intro s hs hs1
      have : s = 1 := len_eq_zero.1 (by omega)
      subst this
      simp [K, X, pairT]
    · rintro ⟨c, hc, hco⟩
      rw [colours_pairT (Or.inl rfl)] at hc
      rw [hc] at hco
      exact hXo hco
    · intro s hs
      exact ⟨c₂, (colours_pairT hs c₂).2 rfl, houtK s hs⟩

end Papers.PODC2012.MaximalMatching
