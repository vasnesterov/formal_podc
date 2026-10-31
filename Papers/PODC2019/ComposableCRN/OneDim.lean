import Papers.PODC2019.ComposableCRN.Automaton
import Papers.PODC2019.ComposableCRN.Impossibility

/-!
# Theorem 3.1: the one-dimensional case

`f : ℕ → ℕ` is obliviously-computable iff it is semilinear and nondecreasing.

* `eventually_step_of_semilinear`: a function `ℕ → ℕ` with semilinear graph satisfies
  `f (x + 2P) - f (x + P) = f (x + P) - f x` for all `x ≥ N` (some `N`, `P > 0`). We prove this
  from Mathlib's definition of semilinear sets (finite unions of linear sets `a + ⟨t⟩`).
* `eventually_affine_of_semilinear_of_monotone`: if moreover `f` is nondecreasing then
  `f (x + P) = f x + c` for all `x ≥ N`, so the finite differences are eventually periodic.
* `theorem_3_1_mpr`: the leader-automaton CRN of the paper (states `L_0, …, L_{n-1}`, then
  `P_a` for `a mod p`).
* `theorem_3_1`: the characterization, assuming Lemma 2.7 (cited from [10]) for "⇒".
-/

namespace Podc.ComposableCRN

open Set AddSubmonoid Pointwise

/-- A function `ℕ → ℕ` with semilinear graph is eventually "affine along a period": there are
`N` and `P > 0` with `f (x + 2P) + f x = 2 f (x + P)` for all `x ≥ N`. -/
theorem eventually_step_of_semilinear (f : ℕ → ℕ)
    (hf : IsSemilinearSet {p : ℕ × ℕ | f p.1 = p.2}) :
    ∃ N P, 0 < P ∧ ∀ x ≥ N, f (x + 2 * P) + f x = 2 * f (x + P) := by
  classical
  obtain ⟨S, hS, hG⟩ := isSemilinearSet_iff.mp hf
  choose! a t ht using fun L (hL : L ∈ S) => isLinearSet_iff.mp (hS L hL)
  let per : Set (ℕ × ℕ) → ℕ := fun L =>
    if hu : ∃ u ∈ t L, 0 < u.1 then hu.choose.1 else 1
  have hper_pos : ∀ L, 0 < per L := fun L => by
    simp only [per]; split_ifs with hu
    · exact hu.choose_spec.2
    · exact one_pos
  refine ⟨∑ L ∈ S, (a L).1 + 1, ∏ L ∈ S, per L, Finset.prod_pos fun L _ => hper_pos L, ?_⟩
  intro x hx
  have hmem : (x, f x) ∈ ⋃₀ (S : Set (Set (ℕ × ℕ))) := by rw [← hG]; rfl
  obtain ⟨L, hLS, hxL⟩ := hmem
  have hLG : L ⊆ {p : ℕ × ℕ | f p.1 = p.2} := by
    rw [hG]; exact subset_sUnion_of_mem hLS
  rw [ht L hLS] at hxL hLG
  obtain ⟨m, hm, hxm⟩ := hxL
  by_cases hu : ∃ u ∈ t L, 0 < u.1
  · set u := hu.choose with hu_def
    have hut : u ∈ t L := hu.choose_spec.1
    have hdvd : u.1 ∣ ∏ L ∈ S, per L := by
      have : per L = u.1 := by simp only [per, hu, ↓reduceDIte, hu_def]
      rw [← this]; exact Finset.dvd_prod_of_mem _ hLS
    obtain ⟨K, hK⟩ := hdvd
    have hpt : ∀ k : ℕ, f (x + k * ∏ L ∈ S, per L) = f x + k * K * u.2 := fun k => by
      have hin : a L +ᵥ (m + (k * K) • u) ∈ a L +ᵥ (AddSubmonoid.closure (t L : Set (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
        vadd_mem_vadd_set (add_mem hm (nsmul_mem (subset_closure hut) _))
      have hval := hLG hin
      simp only [vadd_eq_add, mem_ofPred_eq] at hxm hval
      rw [← add_assoc, hxm] at hval
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hval
      rw [hK, ← hval]
      congr 1
      ring
    have h1 := hpt 1
    have h2 := hpt 2
    simp only [one_mul] at h1
    rw [h1, h2]
    ring
  · exfalso
    push Not at hu
    have hzero : ∀ v ∈ AddSubmonoid.closure (t L : Set (ℕ × ℕ)), v.1 = 0 := fun v hv => by
      induction hv using closure_induction with
      | mem v hv => exact Nat.le_zero.mp (hu v hv)
      | zero => rfl
      | add v w _ _ hv hw => simp [hv, hw]
    have hx' : x = (a L).1 := by
      have := congrArg Prod.fst hxm
      simp only [vadd_eq_add, Prod.fst_add, hzero m hm, add_zero] at this
      exact this.symm
    have : (a L).1 ≤ ∑ L ∈ S, (a L).1 :=
      Finset.single_le_sum (f := fun L => (a L).1) (fun _ _ => Nat.zero_le _) hLS
    omega

/-- A nondecreasing function `ℕ → ℕ` with semilinear graph is eventually quasi-affine:
`f (x + P) = f x + c` for all `x ≥ N`. -/
theorem eventually_affine_of_semilinear_of_monotone (f : ℕ → ℕ)
    (hf : IsSemilinearSet {p : ℕ × ℕ | f p.1 = p.2}) (hmono : Monotone f) :
    ∃ N P c, 0 < P ∧ ∀ x ≥ N, f (x + P) = f x + c := by
  obtain ⟨N, P, hP, hstep⟩ := eventually_step_of_semilinear f hf
  -- `c x = f (x + P) - f x` is `P`-periodic beyond `N`
  set c : ℕ → ℕ := fun x => f (x + P) - f x with hc
  have hcP : ∀ x, f (x + P) = f x + c x := fun x => by
    have := hmono (Nat.le_add_right x P); simp only [hc]; omega
  have hcper : ∀ x ≥ N, c (x + P) = c x := fun x hx => by
    have := hstep x hx; have h1 := hcP x; have h2 := hcP (x + P)
    rw [show x + P + P = x + 2 * P by ring] at h2
    omega
  have hkP : ∀ x ≥ N, ∀ k, f (x + k * P) = f x + k * c x := by
    intro x hx k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : c (x + k * P) = c x := by
        clear ih
        induction k with
        | zero => simp
        | succ k ih' =>
          rw [show x + (k + 1) * P = x + k * P + P by ring, hcper _ (by omega), ih']
      rw [show x + (k + 1) * P = x + k * P + P by ring, hcP, ih, hck]
      ring
  -- monotonicity forces `c` to be constant beyond `N`
  have hcsucc : ∀ x ≥ N, c (x + 1) = c x := by
    intro x hx
    have hlow : ∀ k, f x + k * c x ≤ f (x + 1) + k * c (x + 1) := fun k => by
      rw [← hkP x hx, ← hkP (x + 1) (by omega)]
      exact hmono (by omega)
    have hup : ∀ k, f (x + 1) + k * c (x + 1) ≤ f x + (k + 1) * c x := fun k => by
      rw [← hkP x hx, ← hkP (x + 1) (by omega)]
      exact hmono (by nlinarith)
    rcases lt_trichotomy (c x) (c (x + 1)) with hlt | heq | hgt
    · exfalso
      have h := hup (f x + c x + 1)
      have : (f x + c x + 1) * (c x + 1) ≤ (f x + c x + 1) * c (x + 1) :=
        Nat.mul_le_mul_left _ hlt
      nlinarith
    · exact heq.symm
    · exfalso
      have h := hlow (f (x + 1) + 1)
      have : (f (x + 1) + 1) * (c (x + 1) + 1) ≤ (f (x + 1) + 1) * c x :=
        Nat.mul_le_mul_left _ hgt
      nlinarith
  have hconst : ∀ x ≥ N, c x = c N := by
    intro x hx
    induction x, hx using Nat.le_induction with
    | base => rfl
    | succ x hx ih => rw [hcsucc x hx, ih]
  exact ⟨N, P, c N, hP, fun x hx => by rw [hcP, hconst x hx]⟩

/-- Theorem 3.1, "⇐": a semilinear nondecreasing `f : ℕ → ℕ` is obliviously-computable (as a
function of one input `x : Fin 1 → ℕ`). -/
theorem theorem_3_1_mpr (f : ℕ → ℕ) (hf : IsSemilinearSet {p : ℕ × ℕ | f p.1 = p.2})
    (hmono : Monotone f) : ObliviouslyComputable (fun x : Fin 1 → ℕ => f (x 0)) := by
  obtain ⟨N, P, c, hP, hNP⟩ := eventually_affine_of_semilinear_of_monotone f hf hmono
  -- the leader's state: `x` while `x < N + P`, then `N + (x - N) mod P`
  let red : ℕ → ℕ := fun m => if m < N + P then m else N + (m - N) % P
  have hred_lt : ∀ m, red m < N + P := fun m => by
    simp only [red]; split_ifs with h
    · exact h
    · have := Nat.mod_lt (m - N) hP; omega
  have hred_ge : ∀ m ≥ N, red m = N + (m - N) % P := fun m hm => by
    simp only [red]; split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rfl
  have hred_lt' : ∀ m < N, red m = m := fun m hm => by
    simp only [red, show m < N + P by omega, ↓reduceIte]
  have hkP : ∀ y ≥ N, ∀ k, f (y + P * k) = f y + k * c := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih => rw [show y + P * (k + 1) = y + P * k + P by ring, hNP _ (by omega), ih]; ring
  -- finite differences only depend on `red`
  have hΔ : ∀ m, f (m + 1) - f m = f (red m + 1) - f (red m) := fun m => by
    by_cases hm : m < N
    · rw [hred_lt' m hm]
    · push Not at hm
      have hdecomp : m = red m + P * ((m - N) / P) := by
        rw [hred_ge m hm]; have := Nat.mod_add_div (m - N) P; omega
      have hr : red m ≥ N := by rw [hred_ge m hm]; omega
      conv_lhs => rw [hdecomp, show red m + P * ((m - N) / P) + 1 =
        (red m + 1) + P * ((m - N) / P) by ring]
      rw [hkP _ hr, hkP _ (by omega)]
      omega
  have hnext : ∀ m, red (m + 1) = red (red m + 1) := fun m => by
    by_cases hm : m < N
    · rw [hred_lt' m hm]
    · push Not at hm
      rw [hred_ge _ (by omega), hred_ge m hm, hred_ge _ (by omega)]
      congr 1
      rw [show N + (m - N) % P + 1 - N = (m - N) % P + 1 by omega, Nat.mod_add_mod,
        show m + 1 - N = m - N + 1 by omega]
  have hsingle : ∀ (c : Fin 1 → ℕ) (i : Fin 1), (c + Pi.single i 1 : Fin 1 → ℕ) 0 = c 0 + 1 := by
    intro c i; fin_cases i; simp
  refine obliviouslyComputable_of_automaton (Q := Fin (N + P)) _
    (fun x => ⟨red (x 0), hred_lt _⟩) (fun c i => ?_) (fun c c' hcc' i => ?_)
  · simp only [hsingle]; exact hmono (Nat.le_succ _)
  · simp only [Fin.mk.injEq] at hcc'
    simp only [hsingle, Fin.mk.injEq]
    exact ⟨by rw [hΔ, hcc', ← hΔ], by rw [hnext, hcc', ← hnext]⟩

/-- An obliviously-computable function is stably computable. -/
theorem ObliviouslyComputable.stablyComputable {ι : Type} [Fintype ι] {f : (ι → ℕ) → ℕ}
    (h : ObliviouslyComputable f) : StablyComputable f := by
  obtain ⟨S, i1, i2, C, -, -, hf⟩ := h
  exact ⟨S, i1, i2, C, hf⟩

/-- **Theorem 3.1.** `f : ℕ → ℕ` is obliviously-computable iff it is semilinear and
nondecreasing. The "⇒" direction uses Lemma 2.7 (stably computable ⇒ semilinear, [10]) as a
hypothesis; "⇐" is `theorem_3_1_mpr`. -/
theorem theorem_3_1 (h27 : StablyComputableImpliesSemilinear) (f : ℕ → ℕ) :
    ObliviouslyComputable (fun x : Fin 1 → ℕ => f (x 0)) ↔
      IsSemilinearSet {p : ℕ × ℕ | f p.1 = p.2} ∧ Monotone f := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => theorem_3_1_mpr f h.1 h.2⟩
  · have hs := h27 (Fin 1) _ h.stablyComputable
    let φ : (Fin 1 → ℕ) × ℕ →+ ℕ × ℕ :=
      { toFun := fun p => (p.1 0, p.2), map_zero' := rfl, map_add' := fun _ _ => rfl }
    convert hs.image φ using 1
    ext ⟨a, b⟩
    simp only [mem_ofPred_eq, mem_image, Prod.exists]
    constructor
    · rintro rfl
      exact ⟨fun _ => a, f a, rfl, rfl⟩
    · rintro ⟨x, y, hxy, hφ⟩
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq] at hφ
      rw [← hφ.1, ← hφ.2]; exact hxy
  · intro a b hab
    exact h.monotone (show (fun _ : Fin 1 => a) ≤ fun _ => b from fun _ => hab)

end Podc.ComposableCRN
