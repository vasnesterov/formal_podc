import Papers.PODC2011.LocallyCheckableProofs.LocalTools

/-!
# Colourings as locally checkable proofs (Section 2.2, examples)

"Bipartite graphs are not in LCP(0) but they are contained in LCP(1) … More generally, if a graph
has chromatic number at most `k`, we can prove it with `⌈log k⌉` bits per node: simply give a proper
`k`-colouring as the proof."

* `colorable_admitsLCP`: for `k ≥ 1`, `χ(G) ≤ k` admits locally checkable proofs of size
  `⌈log₂ k⌉` (`Nat.clog 2 k`) on every family, with a radius-1 verifier.
* `bipartite_admitsLCP_one`: bipartite graphs (`χ ≤ 2`) are in `LCP(1)` on every family.

The property is `I.G.Colorable k` (the graph lives on `ℕ`, nodes outside `V` are isolated); for
`k = 0` it is false even for the empty instance, which no verifier can reject, hence `0 < k`.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph

variable {L : Type*}

/-- The `w` low bits of `x`. -/
def lowBits (w x : ℕ) : List Bool := List.ofFn fun i : Fin w => x.testBit i

@[simp] lemma length_lowBits (w x : ℕ) : (lowBits w x).length = w := by simp [lowBits]

lemma lowBits_inj {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w) (h : lowBits w x = lowBits w y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · simpa using congrFun (List.ofFn_injective h) ⟨i, hi⟩
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))]

open Classical in
/-- The colouring verifier: the proof label of `v` is a colour, different from the colours of all
neighbours. -/
noncomputable def colorVerifier (k : ℕ) : Inst L → (ℕ → Fin k) → ℕ → Bool :=
  fun I Q v => decide (∀ u, I.G.Adj v u → Q u ≠ Q v)

lemma colorVerifier_isLocal (k : ℕ) : IsLocal 1 (colorVerifier (L := L) k) := by
  refine isLocal_of_nbr1Eq (fun I Q I' Q' v h => ?_) le_rfl
  simp only [colorVerifier, decide_eq_decide]
  constructor
  · intro H u hu
    have hu' := (h.adj u).2 hu
    rw [← h.prf u hu', ← h.prf_self]; exact H u hu'
  · intro H u hu
    rw [h.prf u hu, h.prf_self]; exact H u ((h.adj u).1 hu)

/-- **Section 2.2.** For `k ≥ 1`, graphs of chromatic number at most `k` admit locally checkable
proofs of size `⌈log₂ k⌉` on every family `F` (a proper `k`-colouring is the proof). -/
theorem colorable_admitsLCP (k : ℕ) (hk : 0 < k) (F : Set (Inst L)) :
    AdmitsLCP F {I | I.G.Colorable k} (fun _ => Nat.clog 2 k) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hlt : ∀ x : Fin k, x.val < 2 ^ Nat.clog 2 k :=
    fun x => lt_of_lt_of_le x.isLt (Nat.le_pow_clog (by norm_num) k)
  refine AdmitsLCPEnc.admitsLCP (enc := fun x : Fin k => lowBits (Nat.clog 2 k) x.val)
    (fun x y h => Fin.ext (lowBits_inj (hlt x) (hlt y) h))
    ⟨1, colorVerifier k, colorVerifier_isLocal k, fun I _ hI => ?_, fun I _ hI Q => ?_⟩
  · obtain ⟨C⟩ := hI
    refine ⟨C, fun v _ => by simp, fun v _ => ?_⟩
    simp only [colorVerifier, decide_eq_true_eq]
    exact fun u hu => (C.valid hu).symm
  · by_contra hall
    push Not at hall
    apply hI
    refine ⟨Coloring.mk Q fun {u w} huw => ?_⟩
    have := hall u (I.sub huw)
    simp only [colorVerifier, ne_eq, Bool.not_eq_false, decide_eq_true_eq] at this
    exact fun h => this w huw h.symm

/-- **Section 2.2.** Bipartite graphs are in `LCP(1)` (on every family). -/
theorem bipartite_admitsLCP_one (F : Set (Inst L)) :
    AdmitsLCP F {I | I.G.Colorable 2} (fun _ => 1) := by
  have h2 : Nat.clog 2 2 = 1 := Nat.clog_pow 2 1 (by norm_num)
  simpa [h2] using colorable_admitsLCP (L := L) 2 (by norm_num) F

end Podc.LocallyCheckableProofs
