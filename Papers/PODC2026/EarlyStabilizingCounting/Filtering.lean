import Papers.PODC2026.EarlyStabilizingCounting.Basic

/-!
# Clock filtering (Lemma 2.3, Algorithm 8)

The `(K, X, T)`-filtering algorithm of [LL26, Appendix A] (Algorithm 8), in state-broadcast form.
Node `v` keeps `m_v, M_v ∈ [K] ∪ {⊥}` and a cooldown counter `X_v`. In every round it receives from
every node `w` the pair `(C_w, m_w)`, where `C_w` is the clock input of `w` (meaningful for `w ∈ T`):

1. `m_v :=` the value received from a strict majority of `T` (else `⊥`)        (line 2)
2. if some `m` was received from at least `n - t` nodes:                        (line 3)
   `X_v := X_v - 1` if `m = M_v + 1 mod K`, else `X_v := X`; `M_v := m`         (lines 4–5)
   otherwise `X_v := X`                                                          (line 6)
3. output `F_v := M_v` if `X_v = 0`, else `⊥`                                   (line 7)

Modelling notes. Values are compared modulo `K`. The paper's compiler resets out-of-range state
variables to an in-range default; here a cooldown value above `X` is clamped to `X` before
decrementing (`min X_v X - 1`), and outputs are reduced modulo `K`. The selectors of lines 2–3
(`majT`, `quorum`) are computable scans; `majT_eq_majority?` and `quorum_eq_threshold?` identify
them with the library selectors `Finset.majority?` and `Finset.threshold?`.

An execution (`IsFiltExec`) is any sequence of states in which every correct node applies
`filtStep` to some received vectors that agree with the true values on the correct nodes; the clock
inputs `ci t w` (the clock of `w` at time `t`) are arbitrary.

Results:
* `filt_validity` (Lemma 2.3, validity): if fewer than half of `T` is faulty and the clock inputs of
  the correct nodes of `T` count from time `s`, the outputs count from time `s + X + 2`.
* `filt_crusader` (Lemma 2.3, crusader agreement): from time `X` on, the outputs satisfy crusader
  agreement with window `X - 1`.
* `filt_crusader_window_false`: the window `X` claimed by Definition 2.2 / Lemma 2.3 fails
  (`n = 4`, one Byzantine node, `X = 1`, `K = 2`, from time `X + 2` on).
-/

set_option linter.unusedSectionVars false

namespace EarlyStabilizingCounting

open Finset

/-- State of the filtering algorithm at one node. -/
structure FS where
  /-- majority value of the clock set seen in the last round -/
  m : Option ℕ
  /-- the filtered candidate value -/
  M : Option ℕ
  /-- cooldown counter -/
  X : ℕ

/-- Strict majority over `T` of the received clock values (`⊥` if there is none). -/
def majT {n : ℕ} (T : Finset (Fin n)) (cs : Fin n → ℕ) : Option ℕ :=
  match (List.finRange n).find?
      (fun w => decide (w ∈ T) && decide (T.card < 2 * T.countEq cs (cs w))) with
  | some w => some (cs w)
  | none => none

/-- A value received from at least `n - t` nodes, if any. -/
def quorum {n : ℕ} (ms : Fin n → Option ℕ) : Option (Option ℕ) :=
  match (List.finRange n).find? (fun w => decide (n - res n ≤ cnt ms (ms w))) with
  | some w => some (ms w)
  | none => none

/-- `q = M + 1 mod K` (false if either is `⊥`). -/
def succMod (K : ℕ) : Option ℕ → Option ℕ → Bool
  | some c, some c' => decide (c % K = (c' + 1) % K)
  | _, _ => false

/-- One round of Algorithm 8 at a node with state `own`, receiving clock values `cs` and
`m`-values `ms`. -/
def filtStep (n K X : ℕ) (T : Finset (Fin n)) (own : FS) (cs : Fin n → ℕ)
    (ms : Fin n → Option ℕ) : FS :=
  match quorum ms with
  | some q => ⟨majT T cs, q, if succMod K q own.M then min own.X X - 1 else X⟩
  | none => ⟨majT T cs, own.M, X⟩

/-- Output of Algorithm 8 (line 7). -/
def filtOut (K : ℕ) (s : FS) : Option ℕ := if s.X = 0 then s.M.map (· % K) else none

/-- An execution of Algorithm 8 with faulty set `F`, clock set `T` and clock inputs `ci`. -/
def IsFiltExec {n : ℕ} (F : Finset (Fin n)) (K X : ℕ) (T : Finset (Fin n))
    (ci : ℕ → Fin n → ℕ) (fs : ℕ → Fin n → FS) : Prop :=
  ∀ t, ∀ v, v ∉ F → ∃ cs ms, Agree F cs (ci t) ∧ Agree F ms (fun w => (fs t w).m) ∧
    fs (t + 1) v = filtStep n K X T (fs t v) cs ms

/-! ### Helper lemmas -/

section Helpers

variable {n : ℕ}

theorem filtStep_m (n K X : ℕ) (T : Finset (Fin n)) (own : FS) (cs : Fin n → ℕ)
    (ms : Fin n → Option ℕ) : (filtStep n K X T own cs ms).m = majT T cs := by
  unfold filtStep; split <;> rfl

theorem quorum_some {ms : Fin n → Option ℕ} {q : Option ℕ} (h : quorum ms = some q) :
    n - res n ≤ cnt ms q := by
  unfold quorum at h
  split at h
  · rename_i w hw
    have := List.find?_some hw
    simp only [decide_eq_true_eq] at this
    cases h; exact this
  · cases h

/-- For `n > 0`, `quorum` is the library's threshold selector `Finset.threshold?` with threshold
`n - t` (above `n / 2`, so the quorum value is unique). -/
theorem quorum_eq_threshold? (hn : 0 < n) (ms : Fin n → Option ℕ) :
    quorum ms = univ.threshold? (fun w => some (ms w)) (n - res n) := by
  rw [← find?_map_eq_threshold? (L := List.finRange n) (fun w _ => List.mem_finRange w)
    (p := fun w => decide (n - res n ≤ cnt ms (ms w))) (fun w => by simp)
    (by rw [card_univ, Fintype.card_fin]; unfold res; omega)]
  unfold quorum
  split <;> simp_all

theorem quorum_of_cnt (hn : 0 < n) {ms : Fin n → Option ℕ} {q : Option ℕ}
    (h : n - res n ≤ cnt ms q) : quorum ms = some q := by
  rw [quorum_eq_threshold? hn]
  exact threshold?_eq_some (by rw [card_univ, Fintype.card_fin]; unfold res; omega)
    (by simpa using h)

/-- Quorums computed by two correct nodes from vectors agreeing on the correct nodes coincide. -/
theorem quorum_agree {F : Finset (Fin n)} (hF : 3 * F.card < n) {x ms₁ ms₂ : Fin n → Option ℕ}
    (h₁ : Agree F ms₁ x) (h₂ : Agree F ms₂ x) {q₁ q₂ : Option ℕ} (hq₁ : quorum ms₁ = some q₁)
    (hq₂ : quorum ms₂ = some q₂) : q₁ = q₂ := by
  obtain ⟨u, hu1, hu2, huF⟩ := Cslib.Quorum.exists_mem_inter_notMem_of_three_mul_lt (f := res n)
    (s := univ.filter fun w => ms₁ w = q₁) (t := univ.filter fun w => ms₂ w = q₂)
    (by rw [Fintype.card_fin]; unfold res; omega) (card_le_res hF)
    (by rw [Fintype.card_fin]; exact quorum_some hq₁) (by rw [Fintype.card_fin]; exact quorum_some hq₂)
  simp only [mem_filter, mem_univ, true_and] at hu1 hu2
  rw [← hu1, ← hu2, h₁ u huF, h₂ u huF]

/-- `majT` is the library's strict-majority selector `Finset.majority?` over `T`. -/
theorem majT_eq_majority? (T : Finset (Fin n)) (cs : Fin n → ℕ) :
    majT T cs = T.majority? fun w => some (cs w) := by
  rw [← find?_map_eq_majority? (L := List.finRange n) (fun w _ => List.mem_finRange w)
    (p := fun w => decide (w ∈ T) && decide (T.card < 2 * T.countEq cs (cs w))) (fun w => by simp)]
  unfold majT
  split <;> simp_all

/-- If the correct nodes of `T` form a strict majority of `T` and all hold `c`, the strict
majority value is `c`. -/
theorem majT_eq {T F : Finset (Fin n)} (hT : 2 * (T ∩ F).card < T.card) {cs : Fin n → ℕ} {c : ℕ}
    (hc : ∀ w, w ∈ T → w ∉ F → cs w = c) : majT T cs = some c := by
  have hsd := card_sdiff_add_card_inter T F
  rw [majT_eq_majority?]
  exact majority?_eq_of_notMem (F := F) (by omega) fun w hw hwF => by rw [hc w hw hwF]

variable {F T : Finset (Fin n)} {K X : ℕ} {ci : ℕ → Fin n → ℕ} {fs : ℕ → Fin n → FS}

/-- A round of a correct node either resets the cooldown to `X`, or has a quorum that is the
successor of the old `M` (and decrements the clamped cooldown). -/
theorem step_cases (hx : IsFiltExec F K X T ci fs) {v : Fin n} (hv : v ∉ F) (t : ℕ) :
    (fs (t + 1) v).X = X ∨ ∃ ms, Agree F ms (fun w => (fs t w).m) ∧
      quorum ms = some (fs (t + 1) v).M ∧ succMod K (fs (t + 1) v).M (fs t v).M = true ∧
      (fs (t + 1) v).X = min (fs t v).X X - 1 := by
  obtain ⟨cs, ms, -, hms, he⟩ := hx t v hv
  rw [he]
  unfold filtStep
  cases hq : quorum ms with
  | none => left; rfl
  | some q =>
    by_cases hs : succMod K q (fs t v).M = true
    · right; exact ⟨ms, hms, hq, by simpa using hs, by simp [hs]⟩
    · left; simp [hs]

/-- If all correct nodes hold `m = some a` at time `t`, every correct node takes `M := some a`. -/
theorem step_all (hF : 3 * F.card < n) (hx : IsFiltExec F K X T ci fs) {t : ℕ} {a : ℕ}
    (hall : ∀ w, w ∉ F → (fs t w).m = some a) {v : Fin n} (hv : v ∉ F) :
    (fs (t + 1) v).M = some a ∧
      (fs (t + 1) v).X = if succMod K (some a) (fs t v).M then min (fs t v).X X - 1 else X := by
  obtain ⟨cs, ms, -, hms, he⟩ := hx t v hv
  have hq : quorum ms = some (some a) := quorum_of_cnt (by omega) (cnt_all hF hms hall)
  rw [he]
  unfold filtStep
  rw [hq]
  exact ⟨rfl, rfl⟩

/-- After a reset, the cooldown decreases by at most one per round. -/
theorem X_ge_after_reset (hx : IsFiltExec F K X T ci fs) {v : Fin n} (hv : v ∉ F) {t : ℕ}
    (h : (fs (t + 1) v).X = X) : ∀ k, X - k ≤ (fs (t + 1 + k) v).X := by
  intro k
  induction k with
  | zero => simp [h]
  | succ k ih =>
    rw [← add_assoc]
    rcases step_cases hx hv (t + 1 + k) with h' | ⟨_, _, _, _, h'⟩ <;> rw [h'] <;> omega

/-- If a correct node has cooldown `0` at time `τ`, its last `X` rounds had successor quorums. -/
theorem good_of_zero (hx : IsFiltExec F K X T ci fs) {v : Fin n} (hv : v ∉ F) {τ t : ℕ}
    (h0 : (fs τ v).X = 0) (ht : t < τ) (htX : τ ≤ t + X) :
    ∃ ms, Agree F ms (fun w => (fs t w).m) ∧ quorum ms = some (fs (t + 1) v).M ∧
      succMod K (fs (t + 1) v).M (fs t v).M = true := by
  rcases step_cases hx hv t with h | ⟨ms, h1, h2, h3, -⟩
  · have := X_ge_after_reset hx hv h (τ - (t + 1))
    rw [show t + 1 + (τ - (t + 1)) = τ by omega, h0] at this
    omega
  · exact ⟨ms, h1, h2, h3⟩

end Helpers

/-- Lemma 2.3, validity: if fewer than `|T|/2` nodes of `T` are faulty and the clocks of the
correct nodes of `T` count modulo `K` from time `s`, then the outputs count from `s + X + 2`. -/
theorem filt_validity {n K X : ℕ} {F T : Finset (Fin n)} {ci : ℕ → Fin n → ℕ}
    {fs : ℕ → Fin n → FS} (hF : 3 * F.card < n) (hT : 2 * (T ∩ F).card < T.card)
    (hx : IsFiltExec F K X T ci fs) (s c₀ : ℕ)
    (hc : ∀ j, ∀ w, w ∈ T → w ∉ F → ci (s + j) w = (c₀ + j) % K) :
    OCountsFrom F K (fun t v => filtOut K (fs t v)) (s + X + 2) := by
  have hm : ∀ j, ∀ w, w ∉ F → (fs (s + j + 1) w).m = some ((c₀ + j) % K) := by
    intro j w hw
    obtain ⟨cs, ms, hcs, -, he⟩ := hx (s + j) w hw
    rw [he, filtStep_m]
    exact majT_eq hT fun u hu huF => by rw [hcs u huF, hc j u hu huF]
  have key : ∀ j, ∀ v, v ∉ F →
      (fs (s + j + 2) v).M = some ((c₀ + j) % K) ∧ (fs (s + j + 2) v).X ≤ X - j := by
    intro j
    induction j with
    | zero =>
      intro v hv
      obtain ⟨h1, h2⟩ := step_all hF hx (hm 0) hv
      refine ⟨h1, ?_⟩
      rw [h2]; split_ifs <;> omega
    | succ j ih =>
      intro v hv
      have hall : ∀ w, w ∉ F → (fs (s + j + 2) w).m = some ((c₀ + (j + 1)) % K) := by
        intro w hw
        have := hm (j + 1) w hw
        rwa [show s + (j + 1) + 1 = s + j + 2 by omega] at this
      obtain ⟨h1, h2⟩ := step_all hF hx hall hv
      rw [show s + (j + 1) + 2 = s + j + 2 + 1 by omega]
      refine ⟨h1, ?_⟩
      have hs : succMod K (some ((c₀ + (j + 1)) % K)) (fs (s + j + 2) v).M = true := by
        rw [(ih v hv).1]
        simp [succMod, Nat.mod_add_mod, add_assoc]
      rw [h2]
      simp only [hs, ↓reduceIte]
      have := (ih v hv).2
      omega
  refine ⟨c₀ + X, fun j v hv => ?_⟩
  obtain ⟨h1, h2⟩ := key (X + j) v hv
  rw [show s + (X + j) + 2 = s + X + 2 + j by omega] at h1 h2
  show filtOut K (fs (s + X + 2 + j) v) = _
  unfold filtOut
  have hz : (fs (s + X + 2 + j) v).X = 0 := by omega
  simp only [hz, h1, ↓reduceIte, Option.map_some, Nat.mod_mod]
  rw [Nat.add_assoc c₀]

/-- Lemma 2.3, crusader agreement, with window `X - 1`: from time `X` on, if a correct node
outputs `c` at time `τ`, every correct node outputs `⊥` or `c + j` at time `τ + j`, `j ≤ X - 1`.
No assumption on the clock inputs or on `T` is needed. -/
theorem filt_crusader {n K X : ℕ} {F T : Finset (Fin n)} {ci : ℕ → Fin n → ℕ}
    {fs : ℕ → Fin n → FS} (hF : 3 * F.card < n) (hX : 1 ≤ X)
    (hx : IsFiltExec F K X T ci fs) :
    Crusader F K (X - 1) X (fun t v => filtOut K (fs t v)) := by
  intro τ hτ v hv c hc j hj w hw
  dsimp only at hc ⊢
  unfold filtOut at hc ⊢
  by_cases h0 : (fs τ v).X = 0
  swap
  · simp [h0] at hc
  simp only [h0, ↓reduceIte] at hc
  obtain ⟨a, hMa, rfl⟩ := Option.map_eq_some_iff.mp hc
  by_cases h0w : (fs (τ + j) w).X = 0
  swap
  · left; simp [h0w]
  right
  simp only [h0w, ↓reduceIte]
  obtain ⟨τ', rfl⟩ : ∃ τ', τ = τ' + 1 := ⟨τ - 1, by omega⟩
  obtain ⟨msv, hmsv, hqv, -⟩ := good_of_zero hx hv h0 (t := τ') (by omega) (by omega)
  have chain : ∀ i, i ≤ j → ∃ b, (fs (τ' + 1 + i) w).M = some b ∧ b % K = (a + i) % K := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨msw, hmsw, hqw, -⟩ := good_of_zero hx hw h0w (t := τ') (by omega) (by omega)
      refine ⟨a, ?_, rfl⟩
      rw [add_zero, quorum_agree hF hmsw hmsv hqw hqv, hMa]
    | succ i ih =>
      intro hi
      obtain ⟨b, hb, hbm⟩ := ih (by omega)
      obtain ⟨msw, -, -, hs⟩ := good_of_zero hx hw h0w (t := τ' + 1 + i) (by omega) (by omega)
      rw [hb] at hs
      rw [← add_assoc]
      cases hb' : (fs (τ' + 1 + i + 1) w).M with
      | none => rw [hb'] at hs; simp [succMod] at hs
      | some b' =>
        rw [hb'] at hs
        simp only [succMod, decide_eq_true_eq] at hs
        refine ⟨b', rfl, ?_⟩
        rw [hs, ← add_assoc]
        exact Nat.ModEq.add_right 1 hbm
  obtain ⟨b, hb, hbm⟩ := chain j le_rfl
  rw [hb]
  simp [hbm, Nat.mod_add_mod]

/-! ### The counterexample execution for `filt_crusader_window_false`

`n = 4`, faulty node `3`, `T = univ`, `K = 2`, `X = 1`. Initially every node has `M = some 0`,
`X = 1`, and the correct `m`-values `⊥, 0, 1` (no quorum in round 1). Round 2 has no quorum
either. At time 2 the correct `m`-values are `1, 1, ⊥`; in round 3 the faulty node completes the
quorum `1` for node `0` only (node `0` outputs `1` at time 3), while node `1` sees no quorum. At
time 3 all correct `m`-values are `1`, so node `1` takes the quorum `1` in round 4 and outputs `1`
at time 4 instead of `⊥` or `0`. -/

namespace FiltCE

/-- Clock inputs of the correct nodes. -/
def ci : ℕ → Fin 4 → ℕ
  | 0, w => if w = 1 then 1 else 0
  | 1, w => if w = 2 then 0 else 1
  | _, _ => 1

/-- Clock value sent by the faulty node `3` to `v` in round `t + 1`. -/
def advC : ℕ → Fin 4 → ℕ
  | 0, v => if v = 0 then 0 else 1
  | 1, v => if v = 2 then 0 else 1
  | _, _ => 1

/-- `m`-value sent by the faulty node `3` to `v` in round `t + 1`. -/
def advM : ℕ → Fin 4 → Option ℕ
  | 0, _ => none
  | 1, _ => some 0
  | 2, v => if v = 0 then some 1 else none
  | _, _ => some 1

/-- Initial states. -/
def init (w : Fin 4) : FS :=
  ⟨if w = 1 then some 0 else if w = 2 then some 1 else none, some 0, 1⟩

/-- The execution. -/
def fs : ℕ → Fin 4 → FS
  | 0 => init
  | t + 1 => fun v => filtStep 4 2 1 univ (fs t v)
      (fun w => if w = 3 then advC t v else ci t w)
      (fun w => if w = 3 then advM t v else (fs t w).m)

end FiltCE

/-- The `X`-round crusader agreement claimed by Lemma 2.3 (window `j ≤ X`, from the stabilization
time `X + 2`) fails for Algorithm 8: an execution with `n = 4`, one Byzantine node, `K = 2`,
`X = 1`. -/
theorem filt_crusader_window_false :
    ∃ (F T : Finset (Fin 4)) (ci : ℕ → Fin 4 → ℕ) (fs : ℕ → Fin 4 → FS),
      3 * F.card < 4 ∧ IsFiltExec F 2 1 T ci fs ∧
      ¬ Crusader F 2 1 (1 + 2) (fun t v => filtOut 2 (fs t v)) := by
  refine ⟨{3}, univ, FiltCE.ci, FiltCE.fs, by decide, ?_, ?_⟩
  · intro t v _
    refine ⟨fun w => if w = 3 then FiltCE.advC t v else FiltCE.ci t w,
      fun w => if w = 3 then FiltCE.advM t v else (FiltCE.fs t w).m, ?_, ?_, rfl⟩ <;>
    · intro w hw
      simp only [Finset.mem_singleton] at hw
      simp [hw]
  · intro h
    have h3 : filtOut 2 (FiltCE.fs 3 0) = some 1 := by decide +kernel
    have := h 3 le_rfl 0 (by decide) 1 h3 1 le_rfl 1 (by decide)
    revert this
    decide +kernel

end EarlyStabilizingCounting
