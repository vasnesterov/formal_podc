import Papers.PODC2020.BinaryLabelingClassification.Families

/-!
# Solutions along a spine of relevant nodes

Two combinatorial facts behind the `Ω(n)` lower bounds of §8, stated for an arbitrary graph with
a path `w₀ – b₀ – w₁ – b₁ – ⋯` of relevant white (`w_k`) and black (`b_k`) nodes:

* **V.a** (`W = 10⁺1`, `B = 010`): every relevant white node labels all its edges alike, and every
  relevant black node of degree 2 has exactly one edge in `X`. Hence the labels alternate along
  the spine: `x(w_{i+n}, b_{i+n}) = x(w_i, b_i) xor (n odd)` (`va_alternate`). In the paper's
  words, the degree-`d` nodes are properly 2-coloured.
* **VI.b, easiest problem** (`W = 110⁺`, `B = 0⁺11`): read `X` as an orientation (edges in `X`
  from black to white); then every relevant node has at most one incoming edge, so along the
  spine, once an edge points right, all later edges point right (`dirR_mono`).
-/

namespace Podc.BinaryLabeling

open SimpleGraph

variable {V : Type*} [Finite V] {G : SimpleGraph V} {x : V → V → Bool}

lemma degX_eq_zero_iff {v : V} : degX G x v = 0 ↔ ∀ w, G.Adj v w → x v w = false := by
  rw [degX, Set.ncard_eq_zero (Set.toFinite _)]
  constructor
  · intro h w hw
    by_contra hc
    have : w ∈ {w | G.Adj v w ∧ x v w = true} := ⟨hw, by simpa using hc⟩
    rw [h] at this; exact this
  · intro h
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hw; simp [h w hw]

lemma degX_eq_deg_iff {v : V} : degX G x v = deg G v ↔ ∀ w, G.Adj v w → x v w = true := by
  constructor
  · intro h w hw
    have hsub : {w | G.Adj v w ∧ x v w = true} ⊆ G.neighborSet v := fun w hw => hw.1
    have := Set.eq_of_subset_of_ncard_le hsub (le_of_eq h.symm) (Set.toFinite _)
    have hw' : w ∈ G.neighborSet v := hw
    rw [← this] at hw'
    exact hw'.2
  · intro h
    unfold degX deg
    congr 1
    ext w
    exact ⟨fun hw => hw.1, fun hw => ⟨hw, h w hw⟩⟩

lemma two_le_degX {v u₁ u₂ : V} (hne : u₁ ≠ u₂) (h₁ : G.Adj v u₁) (h₂ : G.Adj v u₂)
    (hx₁ : x v u₁ = true) (hx₂ : x v u₂ = true) : 2 ≤ degX G x v := by
  have hsub : ({u₁, u₂} : Set V) ⊆ {w | G.Adj v w ∧ x v w = true} := by
    rintro w (rfl | rfl)
    · exact ⟨h₁, hx₁⟩
    · exact ⟨h₂, hx₂⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair hne] at this

lemma degX_le_deg_sub_two {v u₁ u₂ : V} (hne : u₁ ≠ u₂) (h₁ : G.Adj v u₁) (h₂ : G.Adj v u₂)
    (hx₁ : x v u₁ = false) (hx₂ : x v u₂ = false) : degX G x v ≤ deg G v - 2 := by
  have hsub : {w | G.Adj v w ∧ x v w = true} ⊆ G.neighborSet v \ {u₁, u₂} := by
    rintro w ⟨hw, hxw⟩
    refine ⟨hw, ?_⟩
    rintro (rfl | rfl)
    · simp [hx₁] at hxw
    · simp [hx₂] at hxw
  have h2 : ({u₁, u₂} : Set V) ⊆ G.neighborSet v := by
    rintro w (rfl | rfl)
    · exact h₁
    · exact h₂
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_sdiff h2, Set.ncard_pair hne] at this

/-! ### Family V.a -/

section Va

variable {P : Problem} (hP : P.IsVa) {f : V → Bool}
include hP

/-- V.a: a relevant white node labels all its edges alike. -/
lemma va_white_const (hsol : IsSolution P G f x) {v z₁ z₂ : V} (hv : f v = true)
    (hd : deg G v = P.d) (h₁ : G.Adj v z₁) (h₂ : G.Adj v z₂) : x v z₁ = x v z₂ := by
  have hW := hsol.2.1 v hv hd
  rw [hP.2.1] at hW
  rcases hW with h | h
  · rw [degX_eq_zero_iff] at h; rw [h _ h₁, h _ h₂]
  · rw [Set.mem_singleton_iff, ← hd, degX_eq_deg_iff] at h; rw [h _ h₁, h _ h₂]

/-- V.a: a relevant black node has exactly one edge in `X`. -/
lemma va_black_flip (hsol : IsSolution P G f x) {v u₁ u₂ : V} (hv : f v = false)
    (hd : deg G v = 2) (hne : u₁ ≠ u₂) (h₁ : G.Adj v u₁) (h₂ : G.Adj v u₂) :
    x v u₁ ≠ x v u₂ := by
  have hB := hsol.2.2 v hv (by rw [hd, hP.1])
  rw [hP.2.2, Set.mem_singleton_iff] at hB
  intro heq
  cases h : x v u₁
  · have := degX_le_deg_sub_two hne h₁ h₂ h (heq ▸ h)
    omega
  · have := two_le_degX hne h₁ h₂ h (heq ▸ h)
    omega

/-- V.a: along a spine of relevant nodes, the labels alternate. -/
lemma va_alternate (hsol : IsSolution P G f x) (w b : ℕ → V) (i : ℕ) :
    ∀ n : ℕ,
    (∀ k, i < k → k ≤ i + n → f (w k) = true ∧ deg G (w k) = P.d) →
    (∀ k, i ≤ k → k < i + n → f (b k) = false ∧ deg G (b k) = 2 ∧ w k ≠ w (k + 1)) →
    (∀ k, i ≤ k → k ≤ i + n → G.Adj (w k) (b k)) →
    (∀ k, i ≤ k → k < i + n → G.Adj (b k) (w (k + 1))) →
    x (w (i + n)) (b (i + n)) = (x (w i) (b i) ^^ decide (n % 2 = 1)) := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro hw hb h1 h2
    have ih' := ih (fun k hk hk' => hw k hk (by omega)) (fun k hk hk' => hb k hk (by omega))
      (fun k hk hk' => h1 k hk (by omega)) (fun k hk hk' => h2 k hk (by omega))
    obtain ⟨hbf, hbd, hne⟩ := hb (i + n) (by omega) (by omega)
    obtain ⟨hwf, hwd⟩ := hw (i + n + 1) (by omega) (by omega)
    have hflip := va_black_flip hP hsol hbf hbd hne (h1 (i + n) (by omega) (by omega)).symm
      (h2 (i + n) (by omega) (by omega))
    rw [← hsol.1 (h1 (i + n) (by omega) (by omega)),
      ← hsol.1 (h2 (i + n) (by omega) (by omega)).symm] at hflip
    have hconst := va_white_const hP hsol hwf hwd (h1 (i + n + 1) (by omega) (by omega))
      (h2 (i + n) (by omega) (by omega)).symm
    rw [show i + (n + 1) = i + n + 1 by ring, hconst]
    rw [ih'] at hflip
    have hpar : decide ((n + 1) % 2 = 1) = !decide (n % 2 = 1) := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, Nat.succ_mod_two_eq_zero_iff,
        Nat.succ_mod_two_eq_one_iff]
    rw [hpar]
    revert hflip
    cases x (w (i + n + 1)) (b (i + n)) <;> cases x (w i) (b i) <;>
      cases decide (n % 2 = 1) <;> simp

end Va

/-! ### The easiest problem of VI.b -/

section VIb

variable {d δ : ℕ} {hd : 2 ≤ d} {hδ : 2 ≤ δ} {f : V → Bool}

/-- Direction of the `s`-th spine edge: `true` iff it points to the right (towards larger
indices), where an edge in `X` is oriented from its black to its white endpoint. Edge `2k` is
`w_k – b_k`, edge `2k + 1` is `b_k – w_{k+1}`. -/
def dirR (x : V → V → Bool) (w b : ℕ → V) (s : ℕ) : Bool :=
  if s % 2 = 0 then !x (w (s / 2)) (b (s / 2)) else x (w (s / 2 + 1)) (b (s / 2))

/-- VI.b (easiest problem): at a relevant node, a right-pointing edge is followed by a
right-pointing edge (at most one incoming edge). -/
lemma dirR_step (hsol : IsSolution (viEasy d δ hd hδ) G f x) (w b : ℕ → V) (s : ℕ)
    (hw : s % 2 = 1 → f (w (s / 2 + 1)) = true ∧ deg G (w (s / 2 + 1)) = d ∧
      b (s / 2) ≠ b (s / 2 + 1))
    (hb : s % 2 = 0 → f (b (s / 2)) = false ∧ deg G (b (s / 2)) = δ ∧ w (s / 2) ≠ w (s / 2 + 1))
    (h1 : ∀ k, G.Adj (w k) (b k)) (h2 : ∀ k, G.Adj (b k) (w (k + 1)))
    (h : dirR x w b s = true) : dirR x w b (s + 1) = true := by
  unfold dirR at h ⊢
  rcases Nat.mod_two_eq_zero_or_one s with hs | hs
  · obtain ⟨hbf, hbd, hne⟩ := hb hs
    have hs1 : (s + 1) % 2 = 1 := by omega
    have hdiv : (s + 1) / 2 = s / 2 := by omega
    simp only [hs, hs1, ↓reduceIte, hdiv, one_ne_zero] at h ⊢
    have hB := hsol.2.2 _ hbf hbd
    simp only [viEasy, Set.mem_insert_iff, Set.mem_singleton_iff] at hB
    by_contra hc
    have hx1 : x (b (s / 2)) (w (s / 2)) = false := by
      rw [← hsol.1 (h1 _)]; simpa using h
    have hx2 : x (b (s / 2)) (w (s / 2 + 1)) = false := by
      rw [hsol.1 (h2 _)]; simpa using hc
    have := degX_le_deg_sub_two hne (h1 _).symm (h2 _) hx1 hx2
    omega
  · obtain ⟨hwf, hwd, hne⟩ := hw hs
    have hs1 : (s + 1) % 2 = 0 := by omega
    have hdiv : (s + 1) / 2 = s / 2 + 1 := by omega
    simp only [hs, hs1, ↓reduceIte, hdiv, one_ne_zero] at h ⊢
    have hW := hsol.2.1 _ hwf hwd
    simp only [viEasy, Set.mem_insert_iff, Set.mem_singleton_iff] at hW
    by_contra hc
    have hx2 : x (w (s / 2 + 1)) (b (s / 2 + 1)) = true := by simpa using hc
    have := two_le_degX hne (h2 _).symm (h1 _) h hx2
    omega

/-- VI.b (easiest problem): along a spine of relevant nodes, once an edge points right, all later
edges point right. -/
lemma dirR_mono (hsol : IsSolution (viEasy d δ hd hδ) G f x) (w b : ℕ → V) (lo hi : ℕ)
    (hw : ∀ k, lo ≤ 2 * k + 1 → 2 * k + 1 < hi →
      f (w (k + 1)) = true ∧ deg G (w (k + 1)) = d ∧ b k ≠ b (k + 1))
    (hb : ∀ k, lo ≤ 2 * k → 2 * k < hi → f (b k) = false ∧ deg G (b k) = δ ∧ w k ≠ w (k + 1))
    (h1 : ∀ k, G.Adj (w k) (b k)) (h2 : ∀ k, G.Adj (b k) (w (k + 1)))
    {s t : ℕ} (hs : lo ≤ s) (hst : s ≤ t) (ht : t ≤ hi) (h : dirR x w b s = true) :
    dirR x w b t = true := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t hst ih =>
    refine dirR_step hsol w b t (fun ht' => hw _ (by omega) (by omega))
      (fun ht' => hb _ (by omega) (by omega)) h1 h2 (ih (by omega))

end VIb

end Podc.BinaryLabeling
