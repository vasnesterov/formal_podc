import Papers.PODC2025.MinimalistLE.Flow

/-!
# Deterministic core of the convergence proofs

* `elim_window` — the deterministic content of the proof of Lemma 19 (and of our proof of the
  almost-sure part of Theorem 2): if in a window of `2D+3` rounds a leader `u` that has beeped at
  least as often as a leader `v` gets a `true` coin in rounds `t+2..t+D+2`, while all coins of `v`
  in rounds `t..t+2D+2` are `false`, then `u` and `v` are not both leaders at the end of the window.
* `unique_forever` — once there is at most one leader, a single fixed node is the only leader
  forever (Lemma 9 + leaders are never created). This is what Definition 1 asks for.
* `exec_congr`, `nbeep_congr` — round `t` depends only on the coins of rounds `< t`.
-/

set_option linter.unusedSectionVars false

namespace MinimalistLE

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {init : V → St} {c : ℕ → V → Bool}

/-- A leader whose coins are all `false` during `[t, t+k)` and that is still a leader in round
`t + k` does not beep in rounds `t+1, …, t+k`. -/
theorem no_beep_of_coins_false {t k : ℕ} {v : V}
    (hv : (exec G init c (t + k) v).leader = true)
    (hcv : ∀ s, t ≤ s → s < t + k → c s v = false) :
    ∀ s, t < s → s ≤ t + k → ¬ Beeps G init c s v := by
  intro s hs1 hs2 hB
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  have hl : (exec G init c (r + 1) v).leader = true := leader_anti (by omega) hv
  have hW := claim6_8 hB
  have hB' : (exec G init c (r + 1) v).phase = .B := hB
  rw [exec_succ, next_of_W hW] at hl hB'
  have hc := hcv r (by omega) (by omega)
  split_ifs at hl hB' with h1 h2
  all_goals simp_all

/-- A leader that is still a leader in round `t + D + 3` and gets a `true` coin in some round
`s ∈ [t+2, t+D+2]` beeps in some round of `(t, t+D+3]`. -/
theorem beep_of_coin_true {t D : ℕ} {u : V}
    (hu : (exec G init c (t + D + 3) u).leader = true)
    (hcu : ∃ s, t + 2 ≤ s ∧ s ≤ t + D + 2 ∧ c s u = true) :
    ∃ s, t < s ∧ s ≤ t + D + 3 ∧ Beeps G init c s u := by
  by_contra hno
  push Not at hno
  obtain ⟨s0, hs1, hs2, hc⟩ := hcu
  -- in rounds `t+2 … t+D+3`, `u` is waiting
  have hW : ∀ r, t + 2 ≤ r → r ≤ t + D + 3 → (exec G init c r u).phase = .W := by
    intro r hr1 hr2
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rcases h : (exec G init c (r' + 1) u).phase
    · rfl
    · exact absurd h (hno _ (by omega) (by omega))
    · exact absurd (claim6_9 h) (hno _ (by omega) (by omega))
  have hl : (exec G init c (s0 + 1) u).leader = true := leader_anti (by omega) hu
  have hl0 : (exec G init c s0 u).leader = true := leader_of_succ hl
  have hB := hno (s0 + 1) (by omega) (by omega)
  have hW0 := hW s0 hs1 (by omega)
  change ¬ (exec G init c (s0 + 1) u).phase = .B at hB
  rw [exec_succ, next_of_W hW0] at hl hB
  split_ifs at hl hB with h1 h2 <;> simp_all

/-- **Elimination window** (deterministic core of Lemma 19). Let `D` bound all distances, `L = 2D+3`.
If `N_t(v) ≤ N_t(u)`, the coin of `u` is `true` in some round of `[t+2, t+D+2]` and all coins of `v`
in rounds `[t, t+L)` are `false`, then `u` and `v` are not both leaders in round `t + L`. -/
theorem elim_window (hconn : G.Connected) (hW : ∀ v, (init v).phase = .W) {D : ℕ}
    (hD : ∀ a b, G.dist a b ≤ D) {u v : V} {t : ℕ}
    (hN : nbeep G init c t v ≤ nbeep G init c t u)
    (hcu : ∃ s, t + 2 ≤ s ∧ s ≤ t + D + 2 ∧ c s u = true)
    (hcv : ∀ s, t ≤ s → s < t + (2 * D + 3) → c s v = false)
    (hu : (exec G init c (t + (2 * D + 3)) u).leader = true)
    (hv : (exec G init c (t + (2 * D + 3)) v).leader = true) : False := by
  have hvq := no_beep_of_coins_false hv hcv
  obtain ⟨s, hs1, hs2, hsB⟩ :=
    beep_of_coin_true (D := D) (leader_anti (by omega) hu) hcu
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hNu : nbeep G init c t u + 1 ≤ nbeep G init c (s' + 1) u := by
    rw [nbeep_succ_of_beeps hsB]; have := nbeep_mono (G := G) (init := init) (c := c)
      (show t ≤ s' by omega) u; omega
  have hNv : nbeep G init c (s' + 1) v = nbeep G init c t v := by
    obtain ⟨k, hk⟩ : ∃ k, s' + 1 = t + k := ⟨s' + 1 - t, by omega⟩
    rw [hk]; exact nbeep_const fun r h1 h2 => hvq r h1 (by omega)
  obtain ⟨r, hr1, hr2, hrB⟩ := lemma12 hconn hW (c := c) (u := u) (v := v) (t := s' + 1) (by rw [hNv]; omega)
  exact hvq r (by omega) (by have := hD u v; omega) hrB

/-- Once round `T` has at most one leader, a single node is the only leader in every round `t ≥ T`
(Definition 1, given Eq. (2)). -/
theorem unique_forever (hI : GoodInit init) {T : ℕ}
    (h : ∀ u v, (exec G init c T u).leader = true → (exec G init c T v).leader = true → u = v) :
    ∃ u, ∀ t, T ≤ t → ∀ w, (exec G init c t w).leader = true ↔ w = u := by
  obtain ⟨u, hu⟩ := lemma9 (G := G) (c := c) hI T
  refine ⟨u, fun t ht w => ⟨fun hw => h w u (leader_anti ht hw) hu, ?_⟩⟩
  rintro rfl
  obtain ⟨x, hx⟩ := lemma9 (G := G) (c := c) hI t
  rwa [← h x w (leader_anti ht hx) hu]

/-- The configuration in round `t` depends only on the coins of rounds `< t`. -/
theorem exec_congr {c' : ℕ → V → Bool} {t : ℕ} (h : ∀ s < t, c s = c' s) :
    exec G init c t = exec G init c' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [exec_succ, exec_succ, ih fun s hs => h s (by omega), h t (by omega)]

theorem nbeep_congr {c' : ℕ → V → Bool} {t : ℕ} (h : ∀ s < t, c s = c' s) :
    nbeep G init c t = nbeep G init c' t := by
  funext v
  unfold nbeep
  congr 1
  apply Finset.filter_congr
  intro s hs
  rw [exec_congr fun r hr => h r (by simp at hs; omega)]

end MinimalistLE
