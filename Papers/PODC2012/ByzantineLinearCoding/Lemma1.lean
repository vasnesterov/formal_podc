import Papers.PODC2012.ByzantineLinearCoding.EqualityCheck
import Podc.Probability.Finite.SchwartzZippel

/-!
# Lemmas 1 and 2 of Appendix C (Liang–Vaidya, PODC 2012)

* Lemma 2 (Appendix C.4): for a fixed `w × w` matrix `W` and a uniformly random diagonal matrix
  `S`, `S - W` is invertible with probability `≥ 1 - w / |F|` (the paper writes `2^{ρ_k}` for the
  field size; it is `2^{L/ρ_k}`).
* Lemma 1 (Appendix C.1): for invertible `A_1, …, A_ρ` and independent uniformly random diagonal
  matrices `S_{q,p}`, the block matrix `M̃ = [A_q S_{q,p}]_{p,q}` is invertible with probability
  `≥ (1 - w / |F|)^ρ`, provided `w ≤ |F|` (without this proviso the statement is false, see
  `Counterexample.lean`). Proof: the paper's induction on the number of blocks with the Schur
  complement `S_{q+1,q+1} - A_{q+1}⁻¹ F_q M_q⁻¹ P_q`.
-/

namespace Podc.ByzantineLinearCoding

open Finset Matrix Cslib.Probability

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Lemma 2** (Appendix C.4), with the field size `|F|` (the paper's `2^{ρ_k}` is a typo for
`2^{L/ρ_k}`). -/
theorem lemma_2 {w : ℕ} (W : Matrix (Fin w) (Fin w) F) :
    1 - (w : ℝ) / Fintype.card F ≤
      uprob (fun s : Fin w → F => (Matrix.diagonal s - W).det ≠ 0) := by
  classical
  set N : Matrix (Fin w) (Fin w) (MvPolynomial (Fin w) F) :=
    Matrix.diagonal (fun i => MvPolynomial.X i) - W.map MvPolynomial.C with hN
  set p : MvPolynomial (Fin w) F := N.det with hp_def
  have heval : ∀ s, MvPolynomial.eval s p = (Matrix.diagonal s - W).det := by
    intro s
    rw [hp_def, RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j
    · subst h; simp [hN]
    · simp [hN, Matrix.diagonal_apply_ne _ h]
  have hp : p ≠ 0 := by
    intro h0
    have := congrArg
      (MvPolynomial.aeval (R := F) (fun _ : Fin w => (Polynomial.X : Polynomial F))) h0
    rw [map_zero, hp_def, AlgHom.map_det] at this
    have hc : (MvPolynomial.aeval (R := F)
        (fun _ : Fin w => (Polynomial.X : Polynomial F))).mapMatrix N = W.charmatrix := by
      ext i j
      by_cases h : i = j
      · subst h; simp [hN]
      · simp [hN, Matrix.charmatrix_apply, Matrix.diagonal_apply_ne _ h]
    rw [hc, ← Matrix.charpoly] at this
    exact (Matrix.charpoly_monic W).ne_zero this
  have hdeg : p.totalDegree ≤ w := by
    have := totalDegree_det_le N (fun i j => by
      by_cases h : i = j
      · subst h
        simp only [hN, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.map_apply]
        refine (MvPolynomial.totalDegree_sub_C_le _ _).trans ?_
        simp [MvPolynomial.totalDegree_X]
      · simp [hN, Matrix.diagonal_apply_ne _ h])
    simpa using this
  have h := Cslib.Probability.one_sub_le_uprob_eval_ne_zero hp
  simp_rw [heval] at h
  refine le_trans ?_ h
  gcongr

/-- The block matrix `M̃ = [A_q S_{q,p}]` of Appendix C.1, eq. (8): rows `(i, p)`, columns
`(r, q)`, entry `A_q[i, r] · S_{q,p}[r, r]`; `S (q, p)` is the diagonal of `S_{q,p}`. -/
def blockM {w ρ : ℕ} (A : Fin ρ → Matrix (Fin w) (Fin w) F) (S : Fin ρ × Fin ρ → Fin w → F) :
    Matrix (Fin w × Fin ρ) (Fin w × Fin ρ) F :=
  fun ip rq => A rq.2 ip.1 rq.1 * S (rq.2, ip.2) rq.1

/-- Uniform probability is invariant under an equivalence of sample spaces. -/
theorem uprob_comp_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (e : Ω ≃ Ω') (E : Ω' → Prop) :
    uprob (fun x => E (e x)) = uprob E := by
  unfold uprob
  rw [Fintype.card_congr e, Nat.card_congr (e.subtypeEquiv (p := fun x => E (e x)) (q := E)
    fun _ => Iff.rfl)]

/-- Restricting a uniformly random function `σ → β` to the range of an injection `g : κ → σ` gives
a uniformly random function `κ → β`. -/
theorem uprob_comp_injective {κ σ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
    [DecidableEq σ] [Fintype β] [Nonempty β] {g : κ → σ} (hg : Function.Injective g)
    (E : (κ → β) → Prop) :
    uprob (fun c : σ → β => E (c ∘ g)) = uprob E := by
  classical
  let p : σ → Prop := fun x => x ∈ Set.range g
  let e1 := Equiv.piEquivPiSubtypeProd p (fun _ => β)
  let e2 : (κ → β) ≃ ({x // p x} → β) := Equiv.arrowCongr (Equiv.ofInjective g hg) (Equiv.refl β)
  have hcomp : ∀ c : σ → β, c ∘ g = e2.symm (e1 c).1 := by
    intro c; funext k; rfl
  have h1 : Nat.card {c : σ → β // E (c ∘ g)} =
      Nat.card {d : κ → β // E d} * Nat.card ({x // ¬ p x} → β) := by
    rw [← Nat.card_prod]
    refine Nat.card_congr ((e1.subtypeEquiv (q := fun pr => E (e2.symm pr.1))
      fun c => by rw [hcomp])|>.trans (Equiv.prodSubtypeFstEquivSubtypeProd.trans
        (Equiv.prodCongr (e2.symm.subtypeEquiv fun _ => Iff.rfl) (Equiv.refl _))))
  have h2 : Fintype.card (σ → β) = Fintype.card (κ → β) * Fintype.card ({x // ¬ p x} → β) := by
    rw [Fintype.card_congr e1, Fintype.card_prod, Fintype.card_congr e2]
  unfold uprob
  rw [h1, h2, Nat.card_eq_fintype_card (α := {x // ¬ p x} → β)]
  have : (Fintype.card ({x // ¬ p x} → β) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  push_cast
  rw [mul_div_mul_right _ _ this]

/-- The reindexing `(Fin w × Fin ρ) ⊕ Fin w ≃ Fin w × Fin (ρ + 1)` splitting off the last block. -/
def lastBlockEquiv (w ρ : ℕ) : (Fin w × Fin ρ) ⊕ Fin w ≃ Fin w × Fin (ρ + 1) where
  toFun := Sum.elim (fun ip => (ip.1, ip.2.castSucc)) (fun i => (i, Fin.last ρ))
  invFun ip := Fin.lastCases (Sum.inr ip.1) (fun p => Sum.inl (ip.1, p)) ip.2
  left_inv x := by rcases x with ⟨i, p⟩ | i <;> simp
  right_inv ip := by
    rcases ip with ⟨i, p⟩
    induction p using Fin.lastCases <;> simp

omit [Fintype F] [DecidableEq F] in
/-- Splitting off the last block row and column of `M̃` (the matrices `M_q`, `P_q`, `F_q` and
`A_{q+1} S_{q+1,q+1}` of Appendix C.1). -/
theorem blockM_submatrix_lastBlockEquiv {w ρ : ℕ} (A : Fin (ρ + 1) → Matrix (Fin w) (Fin w) F)
    (S : Fin (ρ + 1) × Fin (ρ + 1) → Fin w → F) :
    (blockM A S).submatrix (lastBlockEquiv w ρ) (lastBlockEquiv w ρ) =
      Matrix.fromBlocks
        (blockM (fun q => A q.castSucc) (fun qp => S (qp.1.castSucc, qp.2.castSucc)))
        (Matrix.of fun ip r => A (Fin.last ρ) ip.1 r * S (Fin.last ρ, ip.2.castSucc) r)
        (Matrix.of fun i rq => A rq.2.castSucc i rq.1 * S (rq.2.castSucc, Fin.last ρ) rq.1)
        (A (Fin.last ρ) * Matrix.diagonal (S (Fin.last ρ, Fin.last ρ))) := by
  ext (⟨i, p⟩ | i) (⟨r, q⟩ | r) <;>
    simp [blockM, lastBlockEquiv, Matrix.mul_diagonal]

omit [Fintype F] [DecidableEq F] in
/-- The Schur complement step of Appendix C.1: if `M_q` and `A_{q+1}` are invertible, then
`M_{q+1}` is invertible iff `S_{q+1,q+1} - W` is, where `W = A_{q+1}⁻¹ F_q M_q⁻¹ P_q` does not
depend on `S_{q+1,q+1}`. -/
theorem exists_det_blockM_update_ne_zero_iff {w ρ : ℕ}
    (A : Fin (ρ + 1) → Matrix (Fin w) (Fin w) F) (hA : (A (Fin.last ρ)).det ≠ 0)
    (x : Fin (ρ + 1) × Fin (ρ + 1) → Fin w → F)
    (hx : (blockM (fun q => A q.castSucc) (fun qp => x (qp.1.castSucc, qp.2.castSucc))).det ≠ 0) :
    ∃ W : Matrix (Fin w) (Fin w) F, ∀ a,
      (blockM A (Function.update x (Fin.last ρ, Fin.last ρ) a)).det ≠ 0 ↔
        (Matrix.diagonal a - W).det ≠ 0 := by
  set M' := blockM (fun q => A q.castSucc) (fun qp => x (qp.1.castSucc, qp.2.castSucc))
  set B12 : Matrix (Fin w × Fin ρ) (Fin w) F :=
    Matrix.of fun ip r => A (Fin.last ρ) ip.1 r * x (Fin.last ρ, ip.2.castSucc) r
  set B21 : Matrix (Fin w) (Fin w × Fin ρ) F :=
    Matrix.of fun i rq => A rq.2.castSucc i rq.1 * x (rq.2.castSucc, Fin.last ρ) rq.1
  set AL := A (Fin.last ρ)
  let : Invertible M' := Matrix.invertibleOfIsUnitDet M' (isUnit_iff_ne_zero.mpr hx)
  refine ⟨AL⁻¹ * (B21 * M'⁻¹ * B12), fun a => ?_⟩
  rw [← Matrix.det_submatrix_equiv_self (lastBlockEquiv w ρ), blockM_submatrix_lastBlockEquiv]
  have hne : ∀ p : Fin ρ, (Fin.last ρ, p.castSucc) ≠ (Fin.last ρ, Fin.last ρ) ∧
      (p.castSucc, Fin.last ρ) ≠ (Fin.last ρ, Fin.last ρ) ∧
      ∀ q : Fin ρ, (p.castSucc, q.castSucc) ≠ (Fin.last ρ, Fin.last ρ) := by
    intro p
    refine ⟨?_, ?_, fun q => ?_⟩ <;> simp [Fin.castSucc_ne_last]
  have e1 : blockM (fun q => A q.castSucc)
      (fun qp => Function.update x (Fin.last ρ, Fin.last ρ) a (qp.1.castSucc, qp.2.castSucc)) =
      M' := by
    ext ⟨i, p⟩ ⟨r, q⟩
    simp only [blockM, M', Function.update_of_ne ((hne q).2.2 p)]
  have e2 : (Matrix.of fun ip r => A (Fin.last ρ) ip.1 r *
      Function.update x (Fin.last ρ, Fin.last ρ) a (Fin.last ρ, ip.2.castSucc) r :
        Matrix (Fin w × Fin ρ) (Fin w) F) = B12 := by
    ext ⟨i, p⟩ r
    simp only [B12, Matrix.of_apply, Function.update_of_ne (hne p).1]
  have e3 : (Matrix.of fun i rq => A rq.2.castSucc i rq.1 *
      Function.update x (Fin.last ρ, Fin.last ρ) a (rq.2.castSucc, Fin.last ρ) rq.1 :
        Matrix (Fin w) (Fin w × Fin ρ) F) = B21 := by
    ext i ⟨r, q⟩
    simp only [B21, Matrix.of_apply, Function.update_of_ne (hne q).2.1]
  rw [e1, e2, e3, Function.update_self, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hAL : IsUnit AL.det := isUnit_iff_ne_zero.mpr hA
  have : AL * Matrix.diagonal a - B21 * M'⁻¹ * B12 =
      AL * (Matrix.diagonal a - AL⁻¹ * (B21 * M'⁻¹ * B12)) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAL, Matrix.one_mul]
  rw [this, Matrix.det_mul]
  simp [hx, hA]

/-- **Lemma 1** (Appendix C.1), abstract form: invertible `A_q`, uniformly random diagonals. -/
theorem lemma_1_blockM {w ρ : ℕ} (A : Fin ρ → Matrix (Fin w) (Fin w) F)
    (hA : ∀ q, (A q).det ≠ 0) (hw : w ≤ Fintype.card F) :
    (1 - (w : ℝ) / Fintype.card F) ^ ρ ≤
      uprob (fun S : Fin ρ × Fin ρ → Fin w → F => (blockM A S).det ≠ 0) := by
  classical
  set δ : ℝ := 1 - (w : ℝ) / Fintype.card F with hδ
  have hδ0 : 0 ≤ δ := by
    have : (w : ℝ) / Fintype.card F ≤ 1 := by
      rw [div_le_one (by exact_mod_cast Fintype.card_pos)]; exact_mod_cast hw
    linarith
  induction ρ with
  | zero =>
    have : (fun S : Fin 0 × Fin 0 → Fin w → F => (blockM A S).det ≠ 0) = fun _ => True := by
      funext S; simp [Matrix.det_isEmpty]
    rw [this, uprob_true, pow_zero]
    simp
  | succ ρ ih =>
    let g : Fin ρ × Fin ρ → Fin (ρ + 1) × Fin (ρ + 1) := Prod.map Fin.castSucc Fin.castSucc
    have hg : Function.Injective g :=
      (Fin.castSucc_injective _).prodMap (Fin.castSucc_injective _)
    let A' : Fin ρ → Matrix (Fin w) (Fin w) F := fun q => A q.castSucc
    let ω : Fin (ρ + 1) × Fin (ρ + 1) := (Fin.last ρ, Fin.last ρ)
    let EA : (Fin (ρ + 1) × Fin (ρ + 1) → Fin w → F) → Prop :=
      fun S => (blockM A' (S ∘ g)).det ≠ 0
    let EB : (Fin (ρ + 1) × Fin (ρ + 1) → Fin w → F) → Prop := fun S => (blockM A S).det ≠ 0
    have hIH : δ ^ ρ ≤ uprob EA := by
      have := ih A' (fun q => hA _)
      rwa [← uprob_comp_injective hg] at this
    have hAinv : ∀ x a, EA (Function.update x ω a) ↔ EA x := by
      intro x a
      have : (Function.update x ω a) ∘ g = x ∘ g := by
        funext qp
        simp only [Function.comp_apply]
        rw [Function.update_of_ne]
        obtain ⟨q, p⟩ := qp
        simp [g, ω, Fin.castSucc_ne_last]
      simp only [EA, this]
    have hfib : ∀ x ∈ univ.filter EA, δ * Fintype.card (Fin w → F) ≤
        (#(univ.filter fun a => EB (Function.update x ω a)) : ℝ) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and, EA] at hx
      obtain ⟨W, hW⟩ := exists_det_blockM_update_ne_zero_iff A (hA _) x hx
      have h2 := lemma_2 W
      rw [uprob_eq_card_filter, le_div_iff₀ (by exact_mod_cast Fintype.card_pos)] at h2
      refine h2.trans (le_of_eq ?_)
      congr 2
      exact Finset.filter_congr fun a _ => (hW a).symm
    have key := card_mul_card_filter_and ω (A := EA) (B := EB) hAinv
    have hkey : (Fintype.card (Fin w → F) : ℝ) * #(univ.filter fun x => EA x ∧ EB x) ≥
        δ * Fintype.card (Fin w → F) * #(univ.filter EA) := by
      have : (Fintype.card (Fin w → F) : ℝ) * #(univ.filter fun x => EA x ∧ EB x) =
          ∑ x ∈ univ.filter EA, (#(univ.filter fun a => EB (Function.update x ω a)) : ℝ) := by
        exact_mod_cast key
      rw [this, ge_iff_le, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hfib
    have hpos : (0 : ℝ) < Fintype.card (Fin w → F) := by exact_mod_cast Fintype.card_pos
    have hcount : δ * #(univ.filter EA) ≤ (#(univ.filter fun x => EA x ∧ EB x) : ℝ) := by
      nlinarith
    calc δ ^ (ρ + 1) = δ * δ ^ ρ := pow_succ' _ _
      _ ≤ δ * uprob EA := by gcongr
      _ ≤ uprob (fun x => EA x ∧ EB x) := by
        rw [uprob_eq_card_filter, uprob_eq_card_filter, mul_div_assoc']
        gcongr
      _ ≤ uprob EB := uprob_mono fun _ h => h.2

variable {V : Type*} [Fintype V] [DecidableEq V] {z : V → V → ℕ} {H : Finset V} {ρ : ℕ}

omit [Fintype F] [DecidableEq F] [Fintype V] in
theorem TreePacking.M_eq_blockM (P : TreePacking z H ρ) (c : Coding z ρ F) :
    P.M c = blockM (fun q => P.A q) (fun qp r => c (P.sym (r, qp.1), qp.2)) := by
  ext ⟨i, p⟩ ⟨r, q⟩
  rfl

/-- **Lemma 1** (Appendix C.1): when the coding coefficients are chosen independently and
uniformly at random, `M̃_H` is invertible with probability at least `(1 - (n-f-1)/|F|)^ρ`
(here `P.w = |H| - 1 = n - f - 1`), provided `n - f - 1 ≤ |F|`. -/
theorem TreePacking.lemma_1 (P : TreePacking z H ρ) (hw : P.w ≤ Fintype.card F) :
    (1 - (P.w : ℝ) / Fintype.card F) ^ ρ ≤ uprob (fun c : Coding z ρ F => (P.M c).det ≠ 0) := by
  classical
  let g : (Fin ρ × Fin ρ) × Fin P.w → Sym z × Fin ρ := fun x => (P.sym (x.2, x.1.1), x.1.2)
  have hg : Function.Injective g := by
    rintro ⟨⟨q, p⟩, r⟩ ⟨⟨q', p'⟩, r'⟩ h
    simp only [g, Prod.mk.injEq] at h
    have := P.sym_inj h.1
    simp only [Prod.mk.injEq] at this
    rw [this.1, this.2, h.2]
  let E : (Fin ρ × Fin ρ → Fin P.w → F) → Prop :=
    fun S => (blockM (fun q => (P.A q : Matrix _ _ F)) S).det ≠ 0
  have h1 : uprob (fun c : Coding z ρ F => (P.M c).det ≠ 0) =
      uprob (fun c : Coding z ρ F => E (Equiv.curry _ _ _ (c ∘ g))) := by
    simp only [P.M_eq_blockM]
    rfl
  rw [h1, uprob_comp_injective hg (fun d => E (Equiv.curry _ _ _ d)), uprob_comp_equiv]
  exact lemma_1_blockM _ (fun q => P.det_A_ne_zero q) hw

end Podc.ByzantineLinearCoding
