import Papers.PODC2012.MaximalMatching.InductiveStep

/-!
# The lower bound: Theorem 6, Lemma 5, Theorem 2 (lower-bound half), Corollary 3
-/

namespace Papers.PODC2012.MaximalMatching

open Podc.ColourSystem FreeCox Pointwise Template

variable {k : ℕ}

/-- **Theorem 6** of Hirvonen–Suomela. Let `k ≥ 3`, `d = k - 1`, and let `A` be a distributed
algorithm (with some running time `r`) that finds a maximal matching in every `d`-regular
`k`-colour system. Then there are `d`-regular `k`-colour systems `U`, `V` with `U[d] = V[d]`,
`A(U, e) ≠ ⊥` and `A(V, e) = ⊥`. -/
theorem theorem6 (hk : 3 ≤ k) (A : Algorithm k) (r : ℕ) (hA : HasRunningTime A r)
    (hMM : ∀ V, IsColourSystem V → IsRegular V (k - 1) → FindsMaximalMatching A V) :
    ∃ U V : Set (FreeCox k), IsColourSystem U ∧ IsColourSystem V ∧ IsRegular U (k - 1) ∧
      IsRegular V (k - 1) ∧ ball U (k - 1) = ball V (k - 1) ∧ A U 1 ≠ none ∧ A V 1 = none := by
  have hG : Good A r := ⟨hA, hMM⟩
  obtain ⟨S, T, tS, tT, hc, hC3, hC4⟩ :=
    exists_critical hk hG (k - 1) (by omega) (by omega)
  have hfull : k - 1 + 1 = k := by omega
  have eS : S.real 1 = S.carrier := by
    rw [real_eq_of_full tS hfull tS.1.one_mem, inv_one, one_smul]
  have eT : T.real 1 = T.carrier := by
    rw [real_eq_of_full tT hfull tT.1.one_mem, inv_one, one_smul]
  refine ⟨S.carrier, T.carrier, tS.1, tT.1, tS.2.1, tT.2.1, hc.1, ?_, ?_⟩
  · obtain ⟨c, -, hout⟩ := hC4 1 tS.1.one_mem
    have : A S.carrier 1 = some c := by rw [← eS]; exact hout
    rw [this]; exact Option.some_ne_none c
  · cases hout : A T.carrier 1 with
    | none => rfl
    | some c =>
      exfalso
      apply hC3
      refine ⟨c, ?_, by rw [out, eT]; exact hout⟩
      exact (hMM _ tT.1 tT.2.1 1 tT.1.one_mem).1 c hout

/-- Theorem 6, "in particular" part: the running time is at least `d = k - 1`. -/
theorem le_runningTime (hk : 3 ≤ k) (A : Algorithm k) (r : ℕ) (hA : HasRunningTime A r)
    (hMM : ∀ V, IsColourSystem V → IsRegular V (k - 1) → FindsMaximalMatching A V) :
    k - 1 ≤ r := by
  obtain ⟨U, V, hU, hV, -, -, hb, h1, h2⟩ := theorem6 hk A r hA hMM
  by_contra hr
  exact h1 (by rw [hA.apply_one_eq hU hV (ball_mono (by omega) hb), h2])

/-! ### Lemma 5: the case `k ≤ 2` -/

theorem isColourSystem_of_len_le_one {V : Set (FreeCox k)} (h1 : (1 : FreeCox k) ∈ V)
    (hV : ∀ x ∈ V, len x ≤ 1) : IsColourSystem V := by
  refine ⟨h1, fun x hx c hc => ?_⟩
  have := hV x hx
  have h0 : x * gen c = 1 := len_eq_zero.1 (by omega)
  rw [h0]
  exact h1

theorem len_gen_mul_gen {a b : Fin k} (h : a ≠ b) : len (gen a * gen b) = 2 := by
  unfold len; rw [mul_gen_val]; simp [mulGenList, h]

/-- An algorithm that finds a maximal matching on the single edge `{e, a}` matches `a`. -/
theorem out_single_edge {A : Algorithm k} (a : Fin k)
    (hMM : FindsMaximalMatching A {1, gen a}) : A {1, gen a} (gen a) = some a := by
  have hcol : ∀ x ∈ ({1, gen a} : Set (FreeCox k)), ∀ c,
      c ∈ colours {1, gen a} x ↔ c = a := fun x hx c =>
    colours_pairT (f := fun _ => a) hx c
  have hmem : gen a ∈ ({1, gen a} : Set (FreeCox k)) := Or.inr rfl
  have hone : (1 : FreeCox k) ∈ ({1, gen a} : Set (FreeCox k)) := Or.inl rfl
  cases ho : A {1, gen a} (gen a) with
  | some c => rw [(hcol _ hmem c).1 ((hMM _ hmem).1 c ho)]
  | none =>
    exfalso
    have h1 := (hMM _ hmem).2.2 ho a ((hcol _ hmem a).2 rfl)
    rw [gen_mul_gen] at h1
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 h1
    have := (hMM _ hone).2.1 c hc
    rw [(hcol _ hone c).1 ((hMM _ hone).1 c hc), one_mul, ho] at this
    cases this

/-- **Lemma 5** (`k = 2`): a distributed algorithm that finds a maximal matching in every
2-colour system has running time at least `1`. -/
theorem lemma5 (A : Algorithm 2) (hA : HasRunningTime A 0)
    (hMM : ∀ V, IsColourSystem V → FindsMaximalMatching A V) : False := by
  set T : Set (FreeCox 2) := {1, gen 0}
  set U : Set (FreeCox 2) := {1, gen 1}
  set V : Set (FreeCox 2) := {1, gen 0, gen 1}
  have hT : IsColourSystem T :=
    isColourSystem_of_len_le_one (Or.inl rfl) (by rintro x (rfl | rfl) <;> simp)
  have hU : IsColourSystem U :=
    isColourSystem_of_len_le_one (Or.inl rfl) (by rintro x (rfl | rfl) <;> simp)
  have hV : IsColourSystem V :=
    isColourSystem_of_len_le_one (Or.inl rfl) (by rintro x (rfl | rfl | rfl) <;> simp)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  -- the views of `0` in `T` and in `V` coincide up to radius 1, and so do those of `1`
  have view_eq : ∀ a b : Fin 2, a ≠ b → ∀ W : Set (FreeCox 2), (W = {1, gen a}) →
      ball ((gen a)⁻¹ • W) 1 = ball ((gen a)⁻¹ • V) 1 := by
    intro a b hab W hW
    subst hW
    ext z
    simp only [mem_ball, mem_inv_smul]
    refine and_congr_left fun hz => ?_
    have hne : gen a * z ≠ gen b := by
      intro h1
      have : z = gen a * gen b := by rw [← h1, ← mul_assoc, gen_mul_gen, one_mul]
      rw [this, len_gen_mul_gen hab] at hz
      omega
    have hV' : V = {1, gen a, gen b} := by
      ext x
      simp only [V, Set.mem_insert_iff, Set.mem_singleton_iff]
      fin_cases a <;> fin_cases b <;> simp_all
      all_goals tauto
    rw [hV']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hne, or_false]
  have hTV : A V (gen 0) = some 0 := by
    rw [← hA T V (gen 0) (gen 0) hT hV (Or.inr rfl) (Or.inr (Or.inl rfl))
      (view_eq 0 1 h01 T rfl)]
    exact out_single_edge 0 (hMM T hT)
  have hUV : A V (gen 1) = some 1 := by
    rw [← hA U V (gen 1) (gen 1) hU hV (Or.inr rfl) (Or.inr (Or.inr rfl))
      (view_eq 1 0 h01.symm U rfl)]
    exact out_single_edge 1 (hMM U hU)
  have e0 := (hMM V hV (gen 0) (Or.inr (Or.inl rfl))).2.1 0 hTV
  have e1 := (hMM V hV (gen 1) (Or.inr (Or.inr rfl))).2.1 1 hUV
  rw [gen_mul_gen] at e0 e1
  rw [e0] at e1
  exact h01 (Option.some.inj e1)

/-- **Theorem 2** (lower bound): for every `k ≥ 1`, a deterministic distributed algorithm that
finds a maximal matching in every anonymous `k`-edge-coloured tree (`k`-colour system) has running
time at least `k - 1`. For `k ≥ 3` it suffices that `A` is correct on `(k-1)`-regular ones
(`le_runningTime`). -/
theorem theorem2_lower (A : Algorithm k) (r : ℕ) (hA : HasRunningTime A r)
    (hMM : ∀ V, IsColourSystem V → FindsMaximalMatching A V) : k - 1 ≤ r := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · by_contra hr
    have hk2 : k = 2 := by omega
    subst hk2
    have hr0 : r = 0 := by omega
    subst hr0
    exact lemma5 A hA hMM
  · exact le_runningTime hk A r hA (fun V hV _ => hMM V hV)

/-- **Corollary 3** (`Ω(Δ)`): for every `Δ ≥ 2`, an algorithm that finds a maximal matching in
every `Δ`-regular (in particular, maximum degree `Δ`) `(Δ+1)`-edge-coloured tree needs at least
`Δ` rounds. -/
theorem corollary3 (Δ : ℕ) (hΔ : 2 ≤ Δ) (A : Algorithm (Δ + 1)) (r : ℕ) (hA : HasRunningTime A r)
    (hMM : ∀ V, IsColourSystem V → IsRegular V Δ → FindsMaximalMatching A V) : Δ ≤ r := by
  have := le_runningTime (k := Δ + 1) (by omega) A r hA (by simpa using hMM)
  simpa using this

end Papers.PODC2012.MaximalMatching
