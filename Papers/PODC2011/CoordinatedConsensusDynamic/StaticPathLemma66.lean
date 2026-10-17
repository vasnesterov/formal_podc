import Papers.PODC2011.CoordinatedConsensusDynamic.StaticPathLemma65
import Cslib.Foundations.Data.Nat.CeilDiv

/-!
# Lemma 6.6: rotating the path in a suffix of the execution

If `G` and `G'` agree up to time `t - (n - 1 - β)` and are the static paths `P_k`, resp. `P_{k'}`,
in rounds `(t - (n-1-β), t]`, then `(G, t)` and `(G', t)` are joined by a walk of length
`3^(m+1) - 1` in the similarity graph whenever `n ≤ 2^m β` (the paper: `m = ℓ_β = ⌈log₂(n/β)⌉`).

The recursion is the one of Fig. 3 (`a = β`, `b = n - 1 - 2β`). The paper omits the base case;
it is `n ≤ 2β + 1`, where we go `P_k → C → P_{k'}` directly with Lemma 6.5
(`b = 0`, `a = s = n-1-β`).
We need `n ≥ 3` (for `n = 2` the paths are disconnected), which the paper leaves implicit.
-/

namespace CoordCons

namespace StaticPath

open DGraph

/-- `G[H₁, H₂]` of the paper: `g` up to round `t₁`, then `H₁` up to round `t₂`, then `H₂`. -/
def splice (g : ℕ → ℕ → ℕ → Prop) (t₁ t₂ : ℕ) (H₁ H₂ : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop :=
  fun r => if r ≤ t₁ then g r else if r ≤ t₂ then H₁ else H₂

theorem isCP_splice {n : ℕ} {g : ℕ → ℕ → ℕ → Prop} (hg : IsCP n g) (t₁ t₂ : ℕ)
    {H₁ H₂ : ℕ → ℕ → Prop} (h₁ : H₁ = cyc n ∨ ∃ k, H₁ = path n k)
    (h₂ : H₂ = cyc n ∨ ∃ k, H₂ = path n k) : IsCP n (splice g t₁ t₂ H₁ H₂) := by
  intro r
  unfold splice
  split_ifs
  · exact hg r
  · exact h₁
  · exact h₂

/-- Lemma 6.6, in terms of the length `L = n - 1 - β` of the transformed suffix. -/
theorem rotate_walk {n : ℕ} (σ : ℕ → Bool) (hn : 3 ≤ n) (m : ℕ) :
    ∀ {β L t k k' : ℕ} {g g' : ℕ → ℕ → ℕ → Prop}, 1 ≤ β → L + β + 1 = n → n ≤ 2 ^ m * β →
      IsCP n g → IsCP n g' → (∀ r, 1 ≤ r → r ≤ t - L → g r = g' r) →
      (∀ r, t - L < r → r ≤ t → g r = path n k ∧ g' r = path n k') →
      Walk (KnownN n) t (3 ^ (m + 1) - 1) (exec n σ g) (exec n σ g') := by
  have h3 : ∀ j, 1 ≤ 3 ^ j := fun j => Nat.one_le_pow _ _ (by norm_num)
  induction m with
  | zero =>
    intro β L t k k' g g' hβ hL hm
    simp at hm; omega
  | succ m ih =>
    intro β L t k k' g g' hβ hL hm hg hg' hpre hsuf
    by_cases hbase : n ≤ 2 * β + 1
    · -- base case: `P_k → C → P_{k'}`
      let gc : ℕ → ℕ → ℕ → Prop := fun r => if t - L < r ∧ r ≤ t then cyc n else g r
      have hgc : IsCP n gc := by
        intro r; simp only [gc]; split_ifs
        · exact Or.inl rfl
        · exact hg r
      have s1 := lemma_6_5 σ (k := k) (s := L) (a := L) (b := 0) (t := t) (g := gc) (g' := g)
        hn hgc le_rfl (by omega)
        (fun r h1 h2 => by simp only [gc]; rw [ite_eq_right (by omega)])
        (fun r h1 h2 => ⟨by simp only [gc]; rw [ite_eq_left (by omega)],
          (hsuf r (by omega) (by omega)).1⟩)
        (fun r h1 h2 => by omega)
      have s2 := lemma_6_5 σ (k := k') (s := L) (a := L) (b := 0) (t := t) (g := gc) (g' := g')
        hn hgc le_rfl (by omega)
        (fun r h1 h2 => by simp only [gc]; rw [ite_eq_right (by omega)]; exact hpre r h1 (by omega))
        (fun r h1 h2 => ⟨by simp only [gc]; rw [ite_eq_left (by omega)],
          (hsuf r (by omega) (by omega)).2⟩)
        (fun r h1 h2 => by omega)
      have hK := exec_knownN σ hn hg
      have hKc := exec_knownN σ hn hgc
      have hK' := exec_knownN σ hn hg'
      have w : Walk (KnownN n) t 2 (exec n σ g) (exec n σ g') :=
        (Walk.single ⟨hK, hKc, _, s1.symm⟩).append (Walk.single ⟨hKc, hK', _, s2⟩)
      exact Walk.pad w hK' (by have := h3 (m + 1 + 1); rw [pow_succ] at this ⊢; omega)
    · -- recursive step (Fig. 3) with `a = β`, `b = L - β`
      set b := L - β with hb
      have hm' : n ≤ 2 ^ m * (2 * β) := by rw [pow_succ] at hm; linarith
      have hL' : b + 2 * β + 1 = n := by omega
      let M (H₁ H₂ : ℕ → ℕ → Prop) := splice g (t - L) (t - b) H₁ H₂
      have hM : ∀ H₁ H₂, (H₁ = cyc n ∨ ∃ k, H₁ = path n k) → (H₂ = cyc n ∨ ∃ k, H₂ = path n k) →
          IsCP n (M H₁ H₂) := fun H₁ H₂ h₁ h₂ => isCP_splice hg _ _ h₁ h₂
      have hP : ∀ j, path n j = cyc n ∨ ∃ k, path n j = path n k := fun j => Or.inr ⟨j, rfl⟩
      have hCy : cyc n = cyc n ∨ ∃ k, cyc n = path n k := Or.inl rfl
      have M1 := hM _ _ (hP k) (hP (k + β))
      have M2 := hM _ _ hCy (hP (k + β))
      have M3 := hM _ _ hCy (hP (k' + β))
      have M4 := hM _ _ (hP k') (hP (k' + β))
      have hMpre : ∀ H₁ H₂ r, r ≤ t - L → M H₁ H₂ r = g r := fun H₁ H₂ r h => by
        simp only [M, splice]; rw [ite_eq_left h]
      have hMmid : ∀ H₁ H₂ r, t - L < r → r ≤ t - b → M H₁ H₂ r = H₁ := fun H₁ H₂ r h1 h2 => by
        simp only [M, splice]; rw [ite_eq_right (by omega), ite_eq_left h2]
      have hMsuf : ∀ H₁ H₂ r, t - b < r → M H₁ H₂ r = H₂ := fun H₁ H₂ r h => by
        simp only [M, splice]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      -- W1 : g ⇝ G[P_k, P_{k+β}]
      have W1 := ih (β := 2 * β) (L := b) (t := t) (k := k) (k' := k + β) (g := g)
        (g' := M (path n k) (path n (k + β))) (by omega) hL' hm' hg M1
        (fun r h1 h2 => by
          by_cases h : r ≤ t - L
          · rw [hMpre _ _ _ h]
          · rw [hMmid _ _ _ (by omega) h2, (hsuf r (by omega) (by omega)).1])
        (fun r h1 h2 => ⟨(hsuf r (by omega) h2).1, hMsuf _ _ _ h1⟩)
      -- S1 : G[P_k, P_{k+β}] ∼ G[C, P_{k+β}]
      have S1 := lemma_6_5 σ (k := k) (s := β) (a := β) (b := b) (t := t)
        (g := M (cyc n) (path n (k + β))) (g' := M (path n k) (path n (k + β))) hn M2 le_rfl
        (by omega)
        (fun r h1 h2 => by rw [hMpre _ _ _ (by omega), hMpre _ _ _ (by omega)])
        (fun r h1 h2 => ⟨hMmid _ _ _ (by omega) h2, hMmid _ _ _ (by omega) h2⟩)
        (fun r h1 h2 => ⟨hMsuf _ _ _ h1, hMsuf _ _ _ h1⟩)
      -- W2 : G[C, P_{k+β}] ⇝ G[C, P_{k'+β}]
      have W2 := ih (β := 2 * β) (L := b) (t := t) (k := k + β) (k' := k' + β)
        (g := M (cyc n) (path n (k + β))) (g' := M (cyc n) (path n (k' + β))) (by omega) hL' hm'
        M2 M3
        (fun r h1 h2 => by
          by_cases h : r ≤ t - L
          · rw [hMpre _ _ _ h, hMpre _ _ _ h]
          · rw [hMmid _ _ _ (by omega) h2, hMmid _ _ _ (by omega) h2])
        (fun r h1 h2 => ⟨hMsuf _ _ _ h1, hMsuf _ _ _ h1⟩)
      -- S2 : G[C, P_{k'+β}] ∼ G[P_{k'}, P_{k'+β}]
      have S2 := lemma_6_5 σ (k := k') (s := β) (a := β) (b := b) (t := t)
        (g := M (cyc n) (path n (k' + β))) (g' := M (path n k') (path n (k' + β))) hn M3 le_rfl
        (by omega)
        (fun r h1 h2 => by rw [hMpre _ _ _ (by omega), hMpre _ _ _ (by omega)])
        (fun r h1 h2 => ⟨hMmid _ _ _ (by omega) h2, hMmid _ _ _ (by omega) h2⟩)
        (fun r h1 h2 => ⟨hMsuf _ _ _ h1, hMsuf _ _ _ h1⟩)
      -- W3 : G[P_{k'}, P_{k'+β}] ⇝ g'
      have W3 := ih (β := 2 * β) (L := b) (t := t) (k := k' + β) (k' := k')
        (g := M (path n k') (path n (k' + β))) (g' := g') (by omega) hL' hm' M4 hg'
        (fun r h1 h2 => by
          by_cases h : r ≤ t - L
          · rw [hMpre _ _ _ h, hpre r h1 h]
          · rw [hMmid _ _ _ (by omega) h2, (hsuf r (by omega) (by omega)).2])
        (fun r h1 h2 => ⟨hMsuf _ _ _ h1, (hsuf r (by omega) h2).2⟩)
      have K2 := exec_knownN σ hn M2
      have K3 := exec_knownN σ hn M3
      have K1 := exec_knownN σ hn M1
      have K4 := exec_knownN σ hn M4
      have w := ((((W1.append (Walk.single ⟨K1, K2, _, S1.symm⟩)).append W2).append
        (Walk.single ⟨K3, K4, _, S2⟩)).append W3)
      refine Walk.cast w ?_
      have := h3 (m + 1)
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, pow_succ 3 (m + 1)]
      omega

/-- **Lemma 6.6** of [KMO11]: `d((G, t), (G', t)) ≤ 3^(m+1) - 1` whenever `n ≤ 2^m β`
(the paper takes `m = ℓ_β = ⌈log₂(n/β)⌉`, see `lemma_6_6_clog`). `G = exec n σ g`,
`G' = exec n σ g'` agree up to time `t - (n - 1 - β)` and are `P_k`, resp. `P_{k'}`, in rounds
`(t - (n - 1 - β), t]`. -/
theorem lemma_6_6 {n β m t k k' : ℕ} (σ : ℕ → Bool) {g g' : ℕ → ℕ → ℕ → Prop} (hn : 3 ≤ n)
    (hβ : 1 ≤ β) (hβn : β < n) (hm : n ≤ 2 ^ m * β) (hg : IsCP n g) (hg' : IsCP n g')
    (hpre : ∀ r, 1 ≤ r → r ≤ t - (n - 1 - β) → g r = g' r)
    (hsuf : ∀ r, t - (n - 1 - β) < r → r ≤ t → g r = path n k ∧ g' r = path n k') :
    Walk (KnownN n) t (3 ^ (m + 1) - 1) (exec n σ g) (exec n σ g') :=
  rotate_walk σ hn m hβ (by omega) hm hg hg' hpre hsuf

/-- The paper's `ℓ_β = ⌈log₂(n/β)⌉`. -/
def ellBeta (n β : ℕ) : ℕ := Nat.clog 2 (n ⌈/⌉ β)

theorem le_two_pow_ellBeta {n β : ℕ} (hβ : 1 ≤ β) : n ≤ 2 ^ ellBeta n β * β := by
  have h1 : n ⌈/⌉ β ≤ 2 ^ ellBeta n β := Nat.le_pow_clog (by norm_num) _
  exact (Nat.le_ceilDiv_mul hβ).trans (Nat.mul_le_mul_right β h1)

/-- Lemma 6.6 with the paper's `ℓ_β = ⌈log₂(n/β)⌉`. -/
theorem lemma_6_6_clog {n β t k k' : ℕ} (σ : ℕ → Bool) {g g' : ℕ → ℕ → ℕ → Prop} (hn : 3 ≤ n)
    (hβ : 1 ≤ β) (hβn : β < n) (hg : IsCP n g) (hg' : IsCP n g')
    (hpre : ∀ r, 1 ≤ r → r ≤ t - (n - 1 - β) → g r = g' r)
    (hsuf : ∀ r, t - (n - 1 - β) < r → r ≤ t → g r = path n k ∧ g' r = path n k') :
    Walk (KnownN n) t (3 ^ (ellBeta n β + 1) - 1) (exec n σ g) (exec n σ g') :=
  lemma_6_6 σ hn hβ hβn (le_two_pow_ellBeta hβ) hg hg' hpre hsuf

end StaticPath

end CoordCons
