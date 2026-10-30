import Papers.PODC2024.GlobalCertificationHashing.Scheme

/-!
# Main results: Theorems 3 and 4, and the refutation of Conjecture 1

* `theorem_4`: global certification of "homomorphism to `H`" with certificates of
  `≤ 10 (n log₂ n' + log₂ log₂ M(n))` bits (for `n ≥ 1`), uniformly in `H` and `M`.
* `theorem_3`: bipartiteness with `≤ 10 (n + log₂ log₂ M(n))` bits.
* `colorable_scheme`: `k`-colourability with `≤ 10 (n log₂ k + log₂ log₂ M(n))` bits.
* `conjecture_1_false`: for `M(n) = n ^ c` there is no `ε > 0` such that every scheme for
  bipartiteness has size `≥ ε n ln n` for infinitely many `n` (Conjecture 1 of Feuilloley–Hirvonen
  claims the optimal size is `Θ(n log n)`).
* `theorem_3_false_of_small_range`: the implicit assumption `M(n) ≥ n` is needed.
-/

open Finset Real Filter

namespace Podc.GlobalCertificationHashing

/-! ### Real-analytic estimates -/

theorem logb_logb_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ logb 2 (logb 2 m) := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hm
  · simp
  apply logb_nonneg one_lt_two
  rw [← logb_self_eq_one (b := 2) one_lt_two]
  exact logb_le_logb_of_le one_lt_two (by norm_num) (by exact_mod_cast hm)

theorem clog_le_logb (x : ℕ) : (Nat.clog 2 x : ℝ) ≤ logb 2 x + 1 := by
  have h := natCeil_logb_natCast 2 x
  push_cast at h
  rw [← h]
  have : 0 ≤ logb 2 (x : ℝ) := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · exact logb_nonneg one_lt_two (by exact_mod_cast hx)
  exact (Nat.ceil_lt_add_one this).le

theorem log_two_inv_lt : 1 / log 2 < 1.45 := by
  have := log_two_gt_d9
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- `log₂ y ≤ 1.45 y` for `y ≥ 0`. -/
theorem logb_two_le (y : ℝ) (hy : 0 ≤ y) : logb 2 y ≤ 1.45 * y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  have h1 := log_le_sub_one_of_pos hy
  have h2 := log_two_inv_lt
  have hl : 0 < log 2 := log_pos one_lt_two
  rw [logb, div_eq_mul_one_div]
  have : log y ≤ y := by linarith
  rcases le_or_gt 0 (log y) with h | h
  · calc log y * (1 / log 2) ≤ y * 1.45 := by
          apply mul_le_mul this h2.le (by positivity) hy.le
      _ = 1.45 * y := by ring
  · have : log y * (1 / log 2) < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith

/-- `log₂ |L_n| ≤ 1 + 2.9 n + log₂ log₂ M(n)`. -/
theorem logb_fam_length_le {M : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n) (hM : n ≤ M n) :
    logb 2 ((fam M n).length : ℝ) ≤ 1 + 2.9 * n + logb 2 (logb 2 (M n)) := by
  set m := M n
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hn.trans hM
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set A : ℝ := n * exp n * max 1 (log m)
  have hexp : 1 ≤ exp (n : ℝ) := one_le_exp (by positivity)
  have hA : 1 ≤ A := by
    have : 1 ≤ max 1 (log m) := le_max_left _ _
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hexp) this
  -- `|L_n| ≤ 2A`
  have hlen : ((fam M n).length : ℝ) ≤ 2 * A := by
    have h : (fam M n).length ≤ max 1 ⌈(n : ℝ) * exp n * log m⌉₊ := fam_length M n
    have hx : (n : ℝ) * exp n * log m ≤ A := by
      have : log m ≤ max 1 (log m) := le_max_right _ _
      unfold A; gcongr
    have hK : (⌈(n : ℝ) * exp n * log m⌉₊ : ℝ) ≤ 2 * A := by
      have := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) * exp n * log m by
        have : 0 ≤ log (m : ℝ) := log_nonneg hm
        positivity)
      linarith
    calc ((fam M n).length : ℝ) ≤ ((max 1 ⌈(n : ℝ) * exp n * log m⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast h
      _ ≤ 2 * A := by
          rw [Nat.cast_max, Nat.cast_one]; exact max_le (by linarith) hK
  have hlogb2A : logb 2 (2 * A) = 1 + logb 2 n + n / log 2 + logb 2 (max 1 (log m)) := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hmx : max 1 (log m) ≠ 0 := (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
    have hexpb : logb 2 (exp (n : ℝ)) = n / log 2 := by rw [logb, log_exp]
    unfold A
    rw [logb_mul two_ne_zero (by positivity), logb_mul (by positivity) hmx,
      logb_mul hn0 (exp_pos _).ne', logb_self_eq_one one_lt_two, hexpb]
    ring
  have hfirst : logb 2 ((fam M n).length : ℝ) ≤ logb 2 (2 * A) := by
    rcases Nat.eq_zero_or_pos (fam M n).length with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, logb_zero]
      exact logb_nonneg one_lt_two (by linarith)
    · exact logb_le_logb_of_le one_lt_two (by exact_mod_cast h0) hlen
  have hlogn : logb 2 (n : ℝ) ≤ 1.45 * n := logb_two_le _ (by positivity)
  have hn2 : (n : ℝ) / log 2 ≤ 1.45 * n := by
    have := log_two_inv_lt
    rw [div_eq_mul_one_div]; nlinarith
  have hmax : logb 2 (max 1 (log m)) ≤ logb 2 (logb 2 m) := by
    rcases le_total (log (m : ℝ)) 1 with h | h
    · rw [max_eq_left h, logb_one]
      exact logb_logb_nonneg (hn.trans hM)
    · rw [max_eq_right h]
      apply logb_le_logb_of_le one_lt_two (by linarith)
      rw [logb, le_div_iff₀ (log_pos one_lt_two)]
      have := log_two_lt_d9
      have : 0 ≤ log (m : ℝ) := by linarith
      nlinarith
  linarith

/-- **Size of the scheme** (for `n ≥ 1`, `n' ≥ 2`):
`certSize ≤ 10 (n log₂ n' + log₂ log₂ M(n))`. -/
theorem certSize_le {W : Type} [Fintype W] (hW : 2 ≤ Fintype.card W) {M : ℕ → ℕ}
    (hM : ∀ n, n ≤ M n) {n : ℕ} (hn : 1 ≤ n) :
    (certSize W M n : ℝ) ≤
      10 * (n * logb 2 (Fintype.card W) + logb 2 (logb 2 (M n))) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLg : 1 ≤ logb 2 (Fintype.card W : ℝ) := by
    rw [← logb_self_eq_one (b := 2) one_lt_two]
    exact logb_le_logb_of_le one_lt_two (by norm_num) (by exact_mod_cast hW)
  have hLL := logb_logb_nonneg (m := M n) (hn.trans (hM n))
  have h1 := clog_le_logb (fam M n).length
  have h2 := clog_le_logb (Fintype.card W)
  have h3 := logb_fam_length_le (M := M) hn (hM n)
  have hnLg : (n : ℝ) ≤ n * logb 2 (Fintype.card W) := by nlinarith
  unfold certSize
  push_cast
  have : (n : ℝ) * Nat.clog 2 (Fintype.card W) ≤ n * (logb 2 (Fintype.card W) + 1) := by
    gcongr
  nlinarith

/-! ### The degenerate case `n' ≤ 1` -/

/-- If `H` has at most one vertex, a homomorphism to `H` exists iff `G` has no edge and (`H` is
nonempty or `G` is empty): certificates of size `0` suffice. -/
theorem isGlobalScheme_small {W : Type} [Fintype W] (H : SimpleGraph W)
    (hW : Fintype.card W ≤ 1) {M : ℕ → ℕ} (hM : ∀ n, n ≤ M n) :
    IsGlobalScheme (HomTo H) M (fun _ => 0) (fun _ nbrs _ => Nonempty W ∧ nbrs = ∅) := by
  have hsub : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp hW
  intro V _ G
  refine ⟨fun ⟨φ⟩ Id _ => ⟨0, by simp, fun u => ⟨⟨φ u⟩, ?_⟩⟩, fun hall => ?_⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨v, huv, rfl⟩
    exact H.ne_of_adj (φ.map_adj huv) (Subsingleton.elim _ _)
  · obtain ⟨c, -, hacc⟩ := hall (fun v => Fintype.equivFin V v)
      ⟨fun u v huv => (Fintype.equivFin V).injective (Fin.ext huv),
        fun v => (Fintype.equivFin V v).isLt.trans_le (hM _)⟩
    refine ⟨⟨fun v => Classical.choice (hacc v).1, fun {u v} huv => ?_⟩⟩
    have := (hacc u).2
    have hv : ((Fintype.equivFin V v : ℕ)) ∈ (fun v => (Fintype.equivFin V v : ℕ)) ''
        {v | G.Adj u v} := ⟨v, huv, rfl⟩
    rw [this] at hv
    exact hv.elim

/-! ### Theorems 4 and 3 -/

/-- **Theorem 4** of [Bousquet–Feuilloley–Zeitoun, PODC 2024]. For every finite graph `H` with
`n'` vertices and every identifier range `M` with `M(n) ≥ n`, there is a global certification
scheme for "`G` admits a homomorphism to `H`" with certificates of size
`O(n log n' + log log M)`; explicitly `≤ 10 (n log₂ n' + log₂ log₂ M(n))` for all `n ≥ 1`
(the constant `10` is uniform in `H` and `M`). -/
theorem theorem_4 {W : Type} [Fintype W] (H : SimpleGraph W) (M : ℕ → ℕ)
    (hM : ∀ n, n ≤ M n) :
    ∃ s : ℕ → ℕ, HasGlobalScheme (HomTo H) M s ∧ ∀ n ≥ 1,
      (s n : ℝ) ≤ 10 * (n * logb 2 (Fintype.card W) + logb 2 (logb 2 (M n))) := by
  by_cases hW : 2 ≤ Fintype.card W
  · exact ⟨certSize W M, ⟨_, isGlobalScheme_verifier H hM⟩, fun n hn => certSize_le hW hM hn⟩
  · refine ⟨fun _ => 0, ⟨_, isGlobalScheme_small H (by omega) hM⟩, fun n hn => ?_⟩
    have hlog : logb 2 (Fintype.card W : ℝ) = 0 := by
      rcases (by omega : Fintype.card W = 0 ∨ Fintype.card W = 1) with h | h <;> simp [h]
    rw [hlog, mul_zero, zero_add, Nat.cast_zero]
    have := logb_logb_nonneg (m := M n) (hn.trans (hM n))
    positivity

/-- Theorem 4 for the paper's literal definition of a scheme (certificate set of size `2 ^ s(n)`
chosen per `n`). -/
theorem theorem_4_paper_def {W : Type} [Fintype W] (H : SimpleGraph W) (M : ℕ → ℕ)
    (hM : ∀ n, n ≤ M n) :
    ∃ (s : ℕ → ℕ) (A : ℕ → Set ℕ → ℕ → Prop), IsGlobalSchemeAbstract ℕ (HomTo H) M s A ∧
      ∀ n ≥ 1, (s n : ℝ) ≤ 10 * (n * logb 2 (Fintype.card W) + logb 2 (logb 2 (M n))) := by
  obtain ⟨s, ⟨A, hA⟩, hs⟩ := theorem_4 H M hM
  exact ⟨s, A, hA.toAbstract, hs⟩

/-- Bipartiteness is "homomorphism to an edge". -/
theorem bipartite_iff_homTo (V : Type) [Fintype V] (G : SimpleGraph V) :
    Bipartite V G ↔ HomTo (⊤ : SimpleGraph (Fin 2)) V G := Iff.rfl

/-- **Theorem 3** of [Bousquet–Feuilloley–Zeitoun, PODC 2024]. Bipartiteness has a global
certification scheme of size `O(n + log log M)`; explicitly `≤ 10 (n + log₂ log₂ M(n))` for
`n ≥ 1`. -/
theorem theorem_3 (M : ℕ → ℕ) (hM : ∀ n, n ≤ M n) :
    ∃ s : ℕ → ℕ, HasGlobalScheme Bipartite M s ∧ ∀ n ≥ 1,
      (s n : ℝ) ≤ 10 * (n + logb 2 (logb 2 (M n))) := by
  obtain ⟨s, ⟨A, hA⟩, hs⟩ := theorem_4 (⊤ : SimpleGraph (Fin 2)) M hM
  refine ⟨s, ⟨A, hA.congr fun V _ G => (bipartite_iff_homTo V G).symm⟩, fun n hn => ?_⟩
  have := hs n hn
  simpa using this

/-- `k`-colourability (homomorphism to the clique `K_k`, Section 1). -/
theorem colorable_scheme (k : ℕ) (M : ℕ → ℕ) (hM : ∀ n, n ≤ M n) :
    ∃ s : ℕ → ℕ, HasGlobalScheme (fun _ _ G => G.Colorable k) M s ∧ ∀ n ≥ 1,
      (s n : ℝ) ≤ 10 * (n * logb 2 k + logb 2 (logb 2 (M n))) := by
  obtain ⟨s, ⟨A, hA⟩, hs⟩ := theorem_4 (⊤ : SimpleGraph (Fin k)) M hM
  exact ⟨s, ⟨A, hA.congr fun V _ G => Iff.rfl⟩, fun n hn => by simpa using hs n hn⟩

/-! ### Conjecture 1 is false -/

/-- In the standard case `M(n) = n ^ c`, bipartiteness has a scheme of size `O(n)`. -/
theorem theorem_3_poly (c : ℕ) (hc : 1 ≤ c) :
    ∃ s : ℕ → ℕ, HasGlobalScheme Bipartite (fun n => n ^ c) s ∧ ∀ n ≥ 1,
      (s n : ℝ) ≤ 10 * (1 + 2.2 * c) * n := by
  obtain ⟨s, hs, hb⟩ := theorem_3 (fun n => n ^ c) (fun n => Nat.le_self_pow (by omega) n)
  refine ⟨s, hs, fun n hn => (hb n hn).trans ?_⟩
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hin : logb 2 ((n ^ c : ℕ) : ℝ) = c * logb 2 n := by push_cast; rw [logb_pow]
  have h1 : 0 ≤ logb 2 (n : ℝ) := logb_nonneg one_lt_two (by exact_mod_cast hn)
  have h2 := logb_two_le (n : ℝ) hn0
  have h3 := logb_two_le (c * logb 2 (n : ℝ)) (by positivity)
  rw [hin]
  have hc0 : (0 : ℝ) ≤ c := by positivity
  nlinarith

/-- **Conjecture 1 (Feuilloley–Hirvonen) is false.** For `M(n) = n ^ c` (`c ≥ 1`), the optimal
size of a global certification scheme for bipartiteness is *not* `Ω(n log n)`: there is no
`ε > 0` such that every scheme has size `≥ ε n ln n` even for infinitely many `n` (this refutes
both the "for all large `n`" and the "infinitely often" reading of `Ω`). -/
theorem conjecture_1_false (c : ℕ) (hc : 1 ≤ c) :
    ¬ ∃ ε > 0, ∀ s : ℕ → ℕ, HasGlobalScheme Bipartite (fun n => n ^ c) s →
      ∃ᶠ n : ℕ in atTop, ε * (n * log n) ≤ s n := by
  rintro ⟨ε, hε, hall⟩
  obtain ⟨s, hs, hb⟩ := theorem_3_poly c hc
  set K : ℝ := 10 * (1 + 2.2 * c)
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hlow, hlarge, hn1⟩ := ((hall s hs).and_eventually
    ((hlog.eventually_gt_atTop (K / ε)).and (eventually_ge_atTop 1))).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hup := hb n hn1
  have : ε * log n ≤ K := by
    have := hlow.trans hup
    have h' : n * (ε * log n) ≤ n * K := by nlinarith
    exact le_of_mul_le_mul_left h' hnpos
  rw [div_lt_iff₀ hε] at hlarge
  linarith

/-! ### The implicit assumption `M(n) ≥ n` -/

theorem not_colorable_two_top_fin_three : ¬ (⊤ : SimpleGraph (Fin 3)).Colorable 2 := by
  rintro ⟨C⟩
  have hinj : Function.Injective C := fun a b h => by
    by_contra hne
    exact C.valid ((SimpleGraph.top_adj a b).mpr hne) h
  have := Fintype.card_le_of_injective C hinj
  simp at this

/-- Without the (implicit) assumption `M(n) ≥ n`, Theorem 3 fails: if `M(3) < 3`, no identifier
assignment exists for 3-vertex graphs, so the paper's definition would force the triangle to be
bipartite. Hence no scheme of any size exists. -/
theorem theorem_3_false_of_small_range (M s : ℕ → ℕ) (hM : M 3 < 3) :
    ¬ HasGlobalScheme Bipartite M s := by
  rintro ⟨A, hA⟩
  apply not_colorable_two_top_fin_three
  refine (hA (Fin 3) ⊤).mpr fun Id hId => ?_
  exfalso
  have := Fintype.card_le_of_injective (fun v : Fin 3 => (⟨Id v, hId.2 v⟩ : Fin (M 3)))
    (fun u v h => hId.1 (congrArg Fin.val h))
  simp at this
  omega

end Podc.GlobalCertificationHashing
