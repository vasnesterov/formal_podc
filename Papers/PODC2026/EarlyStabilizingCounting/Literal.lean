import Papers.PODC2026.EarlyStabilizingCounting.Recursion

/-!
# Algorithm 1 as written (input `C_v + R`) never counts

Algorithm 1, line 3 of [LL26] starts King Consensus with input `C_v + R mod C`. By the paper's own
conventions (Section 4) an instance started in round `r` executes its `R`-th round in round
`r + R - 1`; line 7 then sets `C_v` to the output and line 15 increments it. So after an instance
outputs the agreed value, `C_v` has advanced by `R + 1` in `R` rounds. Whenever the clocks already
agree and some instance has a correct leader agreed upon by all correct nodes (which happens every
`k_b` rounds once a filtered clock counts), the counter jumps by `2` in one round.

* `literal_breaks` (trace level): with input offset `δ = D`, the output clocks cannot count past
  any instance with an agreed correct leader.
* `literal_never_counts`: for `n ≥ 2`, `C ≥ 2` and any early-stabilizing sub-counters, **no**
  fault-free execution of the literal algorithm (`tmpl 3`) ever stabilizes.
* `literal_exists_exec`: such executions exist (so the statement is not vacuous).

The proof of Lemma 5.4 assumes the output appears in round `r + R`; with input `C_v + R - 1`
(`tmpl 2`) everything works (`theorem_5_7`, `corollary_5_8`).
-/

set_option linter.unusedSectionVars false

namespace EarlyStabilizingCounting

open Finset Cslib.Byzantine.SyncCounting

/-- With input offset `δ = D` the clocks cannot count across an instance whose correct leader is
agreed upon by all correct nodes. -/
theorem literal_breaks {n C D : ℕ} {F : Finset (Fin n)} {cv : ℕ → Fin n → ℕ}
    {ld : Bool → ℕ → Fin n → Option (Fin n)} {out : Bool → ℕ → Fin n → Option ℕ}
    (hC : 2 ≤ C) (h : TraceHyp n C D D F cv ld out) {T : ℕ} (hT : CountsFrom F C cv T)
    {b : Bool} {τ : ℕ} (hτ : T ≤ τ) {ℓ : Fin n} (hℓ : ℓ ∉ F)
    (hlead : ∀ v, v ∉ F → ld b τ v = some ℓ) : False := by
  obtain ⟨c₀, hc⟩ := hT
  set c := (c₀ + (τ - T) + D) % C with hcdef
  have hin : ∀ v, v ∉ F → (cv τ v + D) % C = c := by
    intro v hv
    have := hc (τ - T) v hv
    rw [show T + (τ - T) = τ by omega] at this
    rw [Nat.add_mod, this, ← Nat.add_mod]
  have hk := (h.kc b τ).king ℓ hℓ hlead
  have hv1 := (h.kc b τ).validity c hin ℓ hℓ
  have hyl : out b τ ℓ = some c := by
    rcases hv1 with h1 | h1
    · exact absurd h1 hk.1
    · exact h1
  have hb : out b τ ℓ = some c := hyl
  have hb' := (h.kc (!b) τ).validity c hin ℓ hℓ
  have happ : ((out true τ ℓ).orElse fun _ => out false τ ℓ).getD (cv (τ + D - 1) ℓ) = c := by
    cases b
    · simp only [Bool.not_false] at hb'
      rcases hb' with h1 | h1 <;> simp [h1, hb]
    · simp [hb]
  have hupd := h.update τ ℓ hℓ
  rw [happ] at hupd
  have hcount := hc (τ - T + D) ℓ hℓ
  rw [show T + (τ - T + D) = τ + D by omega, hupd, Nat.mod_mod] at hcount
  -- (c + 1) % C = (c₀ + (τ - T) + D) % C = c
  rw [hcdef, Nat.mod_add_mod, show c₀ + (τ - T + D) = c₀ + (τ - T) + D by omega] at hcount
  have := Nat.sub_mod_eq_zero_of_mod_eq hcount
  rw [show c₀ + (τ - T) + D + 1 - (c₀ + (τ - T) + D) = 1 by omega] at this
  have := Nat.le_of_dvd one_pos (Nat.dvd_of_mod_eq_zero this)
  omega

variable {n C : ℕ} {X₀ X₁ : Type} [NeZero C]

/-- Algorithm 1 as written (input `C_v + R` with `R = 3`) never stabilizes: in a fault-free
execution, every counting phase is broken by the next instance with a correct leader. -/
theorem literal_never_counts (hn : 2 ≤ n) (hC : 2 ≤ C)
    {A₀ : Algorithm (Fin (n / 2)) X₀ (kk Dk false * n)}
    {A₁ : Algorithm (Fin (n - n / 2)) X₁ (kk Dk true * n)} {T₀ T₁ : ℕ → ℕ}
    (h₀ : IsESCounter A₀ T₀) (_h₁ : IsESCounter A₁ T₁)
    (x : ℕ → Fin n → LS n × X₀ × X₁) (hx : IsExec (tmpl 3 C A₀ A₁) ∅ x) (T : ℕ) :
    ¬ StabilisesIn (tmpl 3 C A₀ A₁) ∅ x T := by
  rintro ⟨c, hc⟩
  have hF : 3 * (∅ : Finset (Fin n)).card < n := by simp; omega
  have hth := traceHyp hF hx
  have hcount : CountsFrom ∅ C (fun t v => (x t v).1.cv) T := ⟨c, fun r v hv => hc r v hv⟩
  -- the filter of `V₀` counts
  obtain ⟨v₀, hv₀⟩ := h₀ (F₀ ∅) (by simp [F₀]; omega) _ (subExec₀ hx)
  have hfl := lemma_5_1 hF hx false (by rw [inter_empty, card_empty, card_Tset_false]; omega) _ v₀
    (fun j w hw _ => by
      have hw' : w.val < n / 2 := by simpa [Tset, side] using hw
      have hj : i₀ w hw' ∉ F₀ (∅ : Finset (Fin n)) := by simp [F₀]
      have := hv₀ j _ hj
      simp only [subOut, Bool.false_eq_true, ite_false, dite_eq_left hw']
      rw [← this]
      rfl)
  obtain ⟨c₁, hc₁⟩ := hfl
  set s := T₀ (F₀ (∅ : Finset (Fin n))).card + Xf + 2
  set a := kk Dk false with ha
  have ha0 : a = 12 := by simp [ha, kk, Dk]
  have hn0 : 0 < n := by omega
  -- a trigger time after both `T` and `s`
  set s' := max T s
  set τ := s' + (a - (c₁ + (s' - s)) % a) % a with hτ
  have hτmod : (c₁ + (τ - s)) % a = 0 := by
    have h1 : c₁ + (τ - s) = (c₁ + (s' - s)) + (a - (c₁ + (s' - s)) % a) % a := by omega
    rw [h1, Nat.add_mod, Nat.mod_mod]
    have h2 := Nat.mod_lt (c₁ + (s' - s)) (by omega : 0 < a)
    by_cases h3 : (c₁ + (s' - s)) % a = 0
    · rw [h3]; simp
    · rw [Nat.mod_eq_of_lt (show a - (c₁ + (s' - s)) % a < a by omega)]
      rw [show (c₁ + (s' - s)) % a + (a - (c₁ + (s' - s)) % a) = a by omega, Nat.mod_self]
  have hval : ∀ v, flT x false τ v = some ((c₁ + (τ - s)) % (a * n)) := by
    intro v
    have := hc₁ (τ - s) v (by simp)
    rwa [show s + (τ - s) = τ by omega] at this
  have hmod : (c₁ + (τ - s)) % (a * n) % a = 0 := by
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro n rfl)]; exact hτmod
  obtain ⟨hl, hl'⟩ := leader_eq_of_mod (by omega) hn0 hmod
  exact literal_breaks (D := Dk) (b := false) hC hth hcount (τ := τ) (by omega)
    (ℓ := ⟨_, hl⟩) (by simp) (fun v _ => by simp only [hval v]; exact hl')

/-- Non-vacuity: the literal algorithm has fault-free executions (from any initial state). -/
theorem literal_exists_exec (A₀ : Algorithm (Fin (n / 2)) X₀ (kk Dk false * n))
    (A₁ : Algorithm (Fin (n - n / 2)) X₁ (kk Dk true * n)) (x₀ : Fin n → LS n × X₀ × X₁) :
    IsExec (tmpl 3 C A₀ A₁) ∅ (run (tmpl 3 C A₀ A₁) x₀) :=
  isExec_run _ _ _

/-- Combined with `corollary_5_8` for the sub-counters: for every `n ≥ 2` and `C ≥ 2` there are
early-stabilizing sub-counters for which the literal Algorithm 1 has an execution (fault-free)
that never stabilizes. -/
theorem literal_counterexample (hn : 2 ≤ n) (hC : 2 ≤ C) :
    ∃ (X₀ X₁ : Type) (A₀ : Algorithm (Fin (n / 2)) X₀ (kk Dk false * n))
      (A₁ : Algorithm (Fin (n - n / 2)) X₁ (kk Dk true * n)) (x : ℕ → Fin n → LS n × X₀ × X₁),
      IsExec (tmpl 3 C A₀ A₁) ∅ x ∧ ∀ T, ¬ StabilisesIn (tmpl 3 C A₀ A₁) ∅ x T := by
  obtain ⟨X₀, hX₀, A₀, hA₀⟩ := corollary_5_8 (n / 2) (kk Dk false * n) (by omega)
    (by simp [kk, Dk]; omega)
  obtain ⟨X₁, hX₁, A₁, hA₁⟩ := corollary_5_8 (n - n / 2) (kk Dk true * n) (by omega)
    (by simp [kk, Dk]; omega)
  let x₀ : Fin n → LS n × X₀ × X₁ := fun _ => (Classical.arbitrary _, Classical.arbitrary _,
    Classical.arbitrary _)
  exact ⟨X₀, X₁, A₀, A₁, _, literal_exists_exec A₀ A₁ x₀,
    fun T => literal_never_counts hn hC hA₀ hA₁ _ (literal_exists_exec A₀ A₁ x₀) T⟩

end EarlyStabilizingCounting
