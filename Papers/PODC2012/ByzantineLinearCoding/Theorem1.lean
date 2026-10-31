import Papers.PODC2012.ByzantineLinearCoding.EqualityCheck
import Podc.Probability.Finite.SchwartzZippel

/-!
# Theorem 1 of Liang–Vaidya (PODC 2012): random coding matrices are correct w.h.p.

For `ρ_k ≤ U_k / 2` (formally: every `H ∈ Ω_k` carries `ρ` edge-disjoint undirected spanning trees,
which is what the Nash-Williams–Tutte theorem gives from `ρ_k ≤ U_k/2`), coding matrices with
independent uniformly random entries from `F` are correct (property (EC)) with probability at least
`1 - C(n, n-f) (n-f-1) ρ / |F|`; for `F = GF(2^{L/ρ})` this is the paper's
`1 - 2^{-L/ρ} C(n, n-f) (n-f-1) ρ`.

Proof (Appendix C.2): the product `∏_{H ∈ Ω_k} det M̃_H` is a nonzero polynomial in the coding
coefficients of total degree `≤ |Ω_k| (n-f-1) ρ`; Schwartz–Zippel bounds the probability that it
vanishes; if it does not vanish, every `M̃_H` is invertible and (EC) follows (Appendix C.1). We show
`det M̃_H ≢ 0` by evaluating it at an explicit coding (`specialCoding`) instead of through Lemma 1.
-/

namespace Podc.ByzantineLinearCoding

open Finset Matrix Cslib.Probability

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- **Appendix C.1 ⇒ (EC).** If `det M̃_H ≠ 0` for every `H ∈ Ω_k` (for some choice of packings),
then the coding is correct. Needs `f < n/3` only to guarantee `n - f ≥ 2`. -/
theorem correct_of_det_ne_zero {n f ρ : ℕ} (hV : Fintype.card V = n) (hf : 3 * f < n)
    {z : V → V → ℕ} {Vk : Finset V} {disp : V → V → Prop}
    (pk : ∀ H ∈ Omega Vk disp (n - f), TreePacking z H ρ) {c : Coding z ρ F}
    (hc : ∀ H (hH : H ∈ Omega Vk disp (n - f)), ((pk H hH).M c).det ≠ 0) :
    Correct z Vk disp f c := by
  intro B hB hVk hdisp X Y hsend hrecv i hi j hj
  by_cases hij : i = j
  · rw [hij]
  -- choose `H ⊇ {i, j}` of size `n - f` among the fault-free nodes
  have hcardB : n - f ≤ #(univ \ B) := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hV]; omega
  have hsub : ({i, j} : Finset V) ⊆ univ \ B := by
    intro v hv; simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> simpa
  have hpair : #({i, j} : Finset V) ≤ n - f := by
    rw [card_pair hij]
    have : 2 ≤ n := by
      have := Finset.card_le_univ ({i, j} : Finset V)
      rw [card_pair hij, hV] at this; exact this
    omega
  obtain ⟨H, hijH, hHB, hHcard⟩ := exists_subsuperset_card_eq hsub hpair hcardB
  have hHnB : ∀ v ∈ H, v ∉ B := fun v hv => (mem_sdiff.1 (hHB hv)).2
  have hHmem : H ∈ Omega Vk disp (n - f) := by
    rw [mem_Omega]
    refine ⟨⟨fun v hv => ?_, hHcard⟩, fun a ha b hb hab => ?_⟩
    · by_contra h; exact hHnB v hv (hVk v h)
    · rcases hdisp a b hab with h | h
      · exact hHnB a ha h
      · exact hHnB b hb h
  set P := pk H hHmem
  have hX : ∀ x, code c (P.sym x) (X (P.sym x).tail) = code c (P.sym x) (X (P.sym x).head) := by
    intro x
    rw [← hsend _ (hHnB _ (P.tail_mem x)), hrecv _ (hHnB _ (P.head_mem x))]
  have key := P.eq_root_of_det_ne_zero (hc H hHmem) X hX
  rw [key i (hijH (by simp)), key j (hijH (by simp))]

omit [DecidableEq V] [Fintype F] [DecidableEq F] in
theorem card_Omega_le {n m : ℕ} (hV : Fintype.card V = n) (Vk : Finset V)
    (disp : V → V → Prop) : #(Omega Vk disp m) ≤ n.choose m := by
  calc #(Omega Vk disp m) ≤ #(Vk.powersetCard m) :=
        card_le_card fun H hH => mem_powersetCard.2 (mem_Omega.1 hH).1
    _ = (#Vk).choose m := card_powersetCard _ _
    _ ≤ n.choose m := Nat.choose_le_choose _ (hV ▸ card_le_univ Vk)

/-- **Theorem 1** of [Liang–Vaidya, PODC 2012]. Let `|V| = n`, `f < n/3`, and let `G_k` (capacities
`z`), `V_k` and the disputes found so far (`disp`) be given. Assume `ρ ≤ U_k/2`, in the form given
by the Nash-Williams–Tutte theorem: every `H ∈ Ω_k` carries `ρ` edge-disjoint unit-capacity spanning
trees. If the entries of the coding matrices are chosen independently and uniformly at random from
the finite field `F`, the coding is correct (property (EC)) with probability at least
`1 - C(n, n-f) (n-f-1) ρ / |F|`. -/
theorem theorem_1 {n f ρ : ℕ} (hV : Fintype.card V = n) (hf : 3 * f < n)
    (z : V → V → ℕ) (Vk : Finset V) (disp : V → V → Prop)
    (hpack : ∀ H ∈ Omega Vk disp (n - f), Nonempty (TreePacking z H ρ)) :
    1 - ((n.choose (n - f) * (n - f - 1) * ρ : ℕ) : ℝ) / Fintype.card F ≤
      uprob (fun c : Coding z ρ F => Correct z Vk disp f c) := by
  classical
  set Ω := Omega Vk disp (n - f)
  let pk : ∀ H ∈ Ω, TreePacking z H ρ := fun H hH => (hpack H hH).some
  set p : MvPolynomial (Sym z × Fin ρ) F := ∏ H ∈ Ω.attach, ((pk H.1 H.2).Mpoly F).det with hp_def
  have hw : ∀ H (hH : H ∈ Ω), (pk H hH).w = n - f - 1 := by
    intro H hH
    have h1 := (pk H hH).card_eq
    have h2 : #H = n - f := (mem_Omega.1 hH).1.2
    omega
  have hp0 : p ≠ 0 := by
    rw [hp_def, prod_ne_zero_iff]
    intro H _ h
    apply (pk H.1 H.2).det_M_specialCoding_ne_zero (F := F)
    rw [← TreePacking.eval_det_Mpoly, h, map_zero]
  have hdeg : (p.totalDegree : ℝ) ≤ ((n.choose (n - f) * (n - f - 1) * ρ : ℕ) : ℝ) := by
    have : p.totalDegree ≤ n.choose (n - f) * (n - f - 1) * ρ := by
      calc p.totalDegree ≤ ∑ H ∈ Ω.attach, ((pk H.1 H.2).Mpoly F).det.totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _H ∈ Ω.attach, (n - f - 1) * ρ := sum_le_sum fun H _ => by
            have := (pk H.1 H.2).totalDegree_det_Mpoly_le (F := F)
            exact this.trans_eq (by rw [hw H.1 H.2])
        _ = #Ω * ((n - f - 1) * ρ) := by rw [sum_const, card_attach, smul_eq_mul]
        _ ≤ n.choose (n - f) * ((n - f - 1) * ρ) :=
            Nat.mul_le_mul_right _ (card_Omega_le hV Vk disp)
        _ = _ := by ring
    exact_mod_cast this
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  calc 1 - ((n.choose (n - f) * (n - f - 1) * ρ : ℕ) : ℝ) / Fintype.card F
      ≤ 1 - (p.totalDegree : ℝ) / Fintype.card F := by gcongr
    _ ≤ uprob (fun c : Coding z ρ F => MvPolynomial.eval c p ≠ 0) :=
        one_sub_le_uprob_eval_ne_zero hp0
    _ ≤ uprob (fun c : Coding z ρ F => Correct z Vk disp f c) := by
        refine uprob_mono fun c hc => correct_of_det_ne_zero hV hf pk fun H hH => ?_
        rw [hp_def, map_prod, prod_ne_zero_iff] at hc
        have := hc ⟨H, hH⟩ (mem_attach _ _)
        rwa [TreePacking.eval_det_Mpoly] at this

end Podc.ByzantineLinearCoding
