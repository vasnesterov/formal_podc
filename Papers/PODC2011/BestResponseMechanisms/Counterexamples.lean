import Papers.PODC2011.BestResponseMechanisms.Mechanism

/-!
# Counterexamples for Section 2 of [NSVZ]

* `theorem_2_7_false`: Theorem 2.7 (2) with the paper's bound of `e_G` rounds is false. A
  4-player game with binary strategies, strict utilities (so tie-breaking plays no role), NBR-solvable
  in `e_G ≤ 2` steps with a clear outcome; with exactly 2 rounds of round robin, player `0`
  strictly gains by never best-responding.
* `outdated_information_false`: with outdated information, "every player is active in every
  round" does not give convergence (extension (1) needs rounds measured by information freshness,
  as in `AsyncRounds`).
* `nbr_outcome_not_unique`: with an infinite strategy space, NBR elimination can end at any
  profile, which need not be a Nash equilibrium (remark after Definition 2.3).
* `figure_1`, `figure_3`: the paper's two example games.
-/

open Set Function Cslib.GameTheory TieBreakGame

namespace Podc.BestResponseMechanisms.Counterexamples

/-! ## Theorem 2.7 with `e_G` rounds -/

/-- Players: `0` (the deviator `i`), `1` (`k`), `2` (`j₂`), `3` (`j₁`); strategies `0`, `1`.
* `j₁` wants to play `0` (dominant);
* `j₂` wants to copy `j₁`;
* `k` wants to play `1` iff `i = 1` and `j₂ = 1`;
* `i` has the dominant strategy `0`, but prefers `(i, k) = (1, 1)` (utility 2) to the
  equilibrium `(0, 0)` (utility 1): `u_i(0,0) = 1, u_i(1,0) = 0, u_i(0,1) = 3, u_i(1,1) = 2`. -/
def g4Utility : Fin 4 → (Fin 4 → Fin 2) → ℕ
  | 0, s => if s 1 = 0 then (if s 0 = 0 then 1 else 0) else (if s 0 = 0 then 3 else 2)
  | 1, s => if s 1 = (if s 0 = 1 ∧ s 2 = 1 then 1 else 0) then 1 else 0
  | 2, s => if s 2 = s 3 then 1 else 0
  | 3, s => if s 3 = 0 then 1 else 0

/-- The game (tie-breaking `0 ≺ 1`, irrelevant since best responses are strict). -/
def g4 : TieBreakGame (Fin 4) (fun _ => Fin 2) ℕ where
  utility := g4Utility
  prec _ x y := x < y

instance (i : Fin 4) : IsStrictTotalOrder (Fin 2) (g4.prec i) :=
  inferInstanceAs (IsStrictTotalOrder (Fin 2) (· < ·))

instance (i : Fin 4) (x y : Fin 2) (s : Fin 4 → Fin 2) : Decidable (g4.Beats i x y s) :=
  inferInstanceAs (Decidable (g4Utility i (update s i y) < g4Utility i (update s i x) ∨
    (g4Utility i (update s i y) = g4Utility i (update s i x) ∧ y < x)))

/-- The outcome `s* = (0, 0, 0, 0)`. -/
def g4Star : Fin 4 → Fin 2 := fun _ => 0

/-- Allowed strategies along the fast elimination: step 1 removes `1` for `i` and `j₁`, step 2
removes `1` for `k` and `j₂`. -/
def g4Allowed : ℕ → Fin 4 → Fin 2 → Bool
  | 0, _, _ => true
  | 1, i, x => x = 0 ∨ i = 1 ∨ i = 2
  | _, _, x => x = 0

def g4E (k : ℕ) : Subgame (fun _ : Fin 4 => Fin 2) := fun i => {x | g4Allowed k i x}

instance (k : ℕ) (i : Fin 4) (x : Fin 2) : Decidable (x ∈ g4E k i) := by
  unfold g4E; infer_instance

instance (H : Subgame (fun _ : Fin 4 => Fin 2)) [∀ i x, Decidable (x ∈ H i)] (i : Fin 4)
    (y : Fin 2) : Decidable (g4.IsNBR H i y) := by
  unfold IsNBR; infer_instance

lemma g4_elimStep (H H' : Subgame (fun _ : Fin 4 => Fin 2)) [∀ i x, Decidable (x ∈ H i)]
    [∀ i x, Decidable (x ∈ H' i)]
    (h : ∀ i (y : Fin 2), (y ∈ H' i → y ∈ H i) ∧ (y ∈ H i → y ∉ H' i → g4.IsNBR H i y)) :
    g4.ElimStep H H' :=
  ⟨fun i y hy => (h i y).1 hy, fun i y hy hy' => (h i y).2 hy hy'⟩

lemma g4E_zero : g4E 0 = full := by
  funext i; ext x; simp [g4E, g4Allowed, full]

lemma g4_solves : g4.Solves g4E 2 g4Star := by
  refine ⟨⟨g4E_zero, ?_⟩, ?_⟩
  · intro k hk
    interval_cases k
    · exact g4_elimStep _ _ (by decide)
    · exact g4_elimStep _ _ (by decide)
  · funext i; ext x; simp [g4E, g4Allowed, g4Star]

instance (H : Subgame (fun _ : Fin 4 => Fin 2)) [∀ i x, Decidable (x ∈ H i)] (i : Fin 4)
    (s : Fin 4 → Fin 2) : Decidable (g4.GloballyOptimal H i s) := by
  unfold GloballyOptimal; infer_instance

instance (i : Fin 4) (x : Fin 2) (s : Fin 4 → Fin 2) : Decidable (g4.IsBR i x s) := by
  unfold IsBR; infer_instance

/-- The elimination order witnessing the clear outcome for player `0`: first `j₁`, then `j₂`,
then `k`, and only then `i`. -/
def g4FAllowed : ℕ → Fin 4 → Fin 2 → Bool
  | 0, _, _ => true
  | 1, i, x => x = 0 ∨ i ≠ 3
  | 2, i, x => x = 0 ∨ i = 0 ∨ i = 1
  | 3, i, x => x = 0 ∨ i = 0
  | _, _, x => x = 0

def g4F (k : ℕ) : Subgame (fun _ : Fin 4 => Fin 2) := fun i => {x | g4FAllowed k i x}

instance (k : ℕ) (i : Fin 4) (x : Fin 2) : Decidable (x ∈ g4F k i) := by
  unfold g4F; infer_instance

lemma g4F_solves : g4.Solves g4F 4 g4Star := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · funext i; ext x; simp [g4F, g4FAllowed, full]
  · intro k hk
    interval_cases k
    · exact g4_elimStep _ _ (by decide)
    · exact g4_elimStep _ _ (by decide)
    · exact g4_elimStep _ _ (by decide)
    · exact g4_elimStep _ _ (by decide)
  · funext i; ext x; simp [g4F, g4FAllowed, g4Star]

/-- `g4` has the clear outcome `s*`: for player `0` the witness is `g4F` at step `3`
(`k₀ = 3 > e_G`), for the others the fast order `g4E` at step `0`. -/
lemma g4_clearWitness_zero : g4.ClearWitness g4Star 0 g4F 4 3 := by
  refine ⟨g4F_solves, by norm_num, ?_, by decide⟩
  ext x; simp [g4F, g4FAllowed]

lemma g4_clearWitness_other (j : Fin 4) (hj : j ≠ 0) : g4.ClearWitness g4Star j g4E 2 0 := by
  refine ⟨g4_solves, by norm_num, ?_, ?_⟩
  · ext x; simp [g4E, g4Allowed]
  · revert j; decide

lemma g4_hasClearOutcome : g4.HasClearOutcome g4Star := by
  refine ⟨⟨g4E, 2, g4_solves⟩, fun i => ?_⟩
  by_cases hi : i = 0
  · subst hi; exact ⟨g4F, 4, 3, g4_clearWitness_zero⟩
  · exact ⟨g4E, 2, 0, g4_clearWitness_other i hi⟩

lemma g4_elimParam_le : g4.elimParam ≤ 2 :=
  Nat.sInf_le ⟨g4E, g4Star, g4_solves⟩

lemma g4_not_isNBR_full (y : Fin 2) : ¬ g4.IsNBR full 1 y := by
  have : ∀ y : Fin 2, ¬ g4.IsNBR (fun _ => {_x | True}) 1 y := by decide
  have h2 : (full : Subgame (fun _ : Fin 4 => Fin 2)) = fun _ => {_x | True} := by
    funext i; simp [full]
  rw [h2]; exact this y

/-- `e_G = 2` exactly. -/
lemma g4_elimParam : g4.elimParam = 2 := by
  refine le_antisymm g4_elimParam_le (le_csInf ⟨2, g4E, g4Star, g4_solves⟩ ?_)
  rintro r ⟨E, s, hE⟩
  by_contra hr
  push Not at hr
  -- some strategy of player `1` other than `s 1` is removed in a step from the full game
  set y : Fin 2 := if s 1 = 0 then 1 else 0 with hy
  have hys : y ≠ s 1 := by
    rw [hy]; split_ifs with h
    · rw [h]; decide
    · exact fun h' => h h'.symm
  have hyr : y ∉ E r 1 := by rw [hE.2]; exact hys
  interval_cases r
  · exact hyr (by rw [hE.1.1]; trivial)
  · exact g4_not_isNBR_full y (hE.1.1 ▸ (hE.1.2 0 (by norm_num)).2 1 y
      (by rw [hE.1.1]; trivial) hyr)

/-- The best-response rule of `g4` (best responses are unique). -/
def g4BR (i : Fin 4) (p : Fin 4 → Fin 2) : Fin 2 := if g4.Beats i 1 0 p then 1 else 0

lemma g4BR_isBRRule : IsBRRule g4 g4BR := by
  intro i p
  revert i p
  decide

/-- The mechanism: round robin `0, 1, 2, 3, 0, 1, …` starting at `(1, 1, 1, 1)`. -/
def g4Mech : Mechanism (fun _ : Fin 4 => Fin 2) := roundRobin (n := 3) (fun _ => 1)

/-- The deviation of player `0`: always announce `1`. -/
def g4Dev : ∀ i : Fin 4, RStrategy (fun _ : Fin 4 => Fin 2) i :=
  update (brStrategy g4Mech g4BR) 0 (fun _ => 1)

/-- The deviating run, computed directly. -/
def g4Traj : ℕ → Fin 4 → Fin 2
  | 0 => fun _ => 1
  | t + 1 => update (g4Traj t) (rrPlayer 3 t)
      (if rrPlayer 3 t = 0 then 1 else g4BR (rrPlayer 3 t) (g4Traj t))

lemma g4Dev_prof (t : ℕ) : g4Mech.prof g4Dev t = g4Traj t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [g4Mech, roundRobin_prof_succ, ← g4Mech, g4Traj, ← ih]
    congr 1
    by_cases h : rrPlayer 3 t = 0
    · simp [h, g4Dev]
    · simp [g4Dev, h, brStrategy_hist]

/-- **Theorem 2.7 (2) is false with `e_G` rounds.** The game `g4` is NBR-solvable with the
clear outcome `s* = 0` (strict best responses, strict total tie-breaking orders), and `e_G ≤ 2`.
The round-robin best-response mechanism with horizon `8` (exactly `2` rounds for every run) is
not incentive compatible: if player `0` always announces `1`, it ends at `(1, 1, 0, 0)` with
utility `2`, while repeated best response ends at `s*` with utility `1`. -/
theorem theorem_2_7_false :
    g4.Solves g4E 2 g4Star ∧ g4.HasClearOutcome g4Star ∧ g4.elimParam = 2 ∧
      IsBRRule g4 g4BR ∧
      (∀ σ, HasRounds (g4Mech.acts σ) 8 2) ∧
      g4Mech.prof (brStrategy g4Mech g4BR) 8 = g4Star ∧
      g4Mech.prof g4Dev 8 = ![1, 1, 0, 0] ∧
      g4.utility 0 (g4Mech.prof (brStrategy g4Mech g4BR) 8) <
        g4.utility 0 (g4Mech.prof g4Dev 8) ∧
      ¬ IsIncentiveCompatible g4 g4Mech g4BR 8 := by
  have hR : ∀ σ, HasRounds (g4Mech.acts σ) 8 2 := fun σ => roundRobin_hasRounds _ σ 2
  have hhon : g4Mech.prof (brStrategy g4Mech g4BR) 8 = g4Star :=
    theorem_2_7_convergence g4Mech g4_solves g4BR_isBRRule le_rfl (hR _) 8 le_rfl
  have hdev : g4Mech.prof g4Dev 8 = ![1, 1, 0, 0] := by
    rw [g4Dev_prof]; decide
  have hlt : g4.utility 0 (g4Mech.prof (brStrategy g4Mech g4BR) 8) <
      g4.utility 0 (g4Mech.prof g4Dev 8) := by
    rw [hhon, hdev]; decide
  refine ⟨g4_solves, g4_hasClearOutcome, g4_elimParam, g4BR_isBRRule, hR, hhon, hdev, hlt, ?_⟩
  intro hIC
  exact absurd (hIC 0 (fun _ => 1)) (not_le.mpr hlt)

/-! ### The same with one player per elimination step

If Definition 2.4 is read so that each step removes strategies of a *single* player, `e_G` of
`g4` is `4`, and `4` rounds suffice there. The game `h4` defeats this reading too: there `e_G = 2`
(simultaneous steps) and `e_G ≤ 4` (single-player steps), but the deviation still pays after `4`
rounds. Players `0` (`i`), `1` (`k`), `2` (`q`), `3` (`p`), strategies `0, …, 3`. If `i = 0`,
the best response of `k`, `q`, `p` is `0`. Otherwise `p` wants `q - 1` (truncated), `q` wants to
copy `p`, and `k` wants `1` iff `q ≥ 1`: the "ladder" `p, q` needs `6` single-player steps to
collapse while `i` is not yet restricted. -/

/-- The strategy each of `k`, `q`, `p` wants. -/
def h4Target : Fin 4 → (Fin 4 → Fin 4) → Fin 4
  | 1, s => if s 0 ≠ 0 ∧ 1 ≤ s 2 then 1 else 0
  | 2, s => if s 0 = 0 then 0 else s 3
  | 3, s => if s 0 = 0 ∨ s 2 = 0 then 0 else s 2 - 1
  | _, _ => 0

/-- Utilities: `k`, `q`, `p` get `1` iff they play their target; `i` gets `1, 0, 3, 2` for
`(i = 0, k ≠ 1), (i ≠ 0, k ≠ 1), (i = 0, k = 1), (i ≠ 0, k = 1)`. -/
def h4Utility : Fin 4 → (Fin 4 → Fin 4) → ℕ
  | 0, s => if s 1 = 1 then (if s 0 = 0 then 3 else 2) else (if s 0 = 0 then 1 else 0)
  | j, s => if s j = h4Target j s then 1 else 0

def h4 : TieBreakGame (Fin 4) (fun _ => Fin 4) ℕ where
  utility := h4Utility
  prec _ x y := x < y

instance (i : Fin 4) (x y : Fin 4) (s : Fin 4 → Fin 4) : Decidable (h4.Beats i x y s) :=
  inferInstanceAs (Decidable (h4Utility i (update s i y) < h4Utility i (update s i x) ∨
    (h4Utility i (update s i y) = h4Utility i (update s i x) ∧ y < x)))

instance (H : Subgame (fun _ : Fin 4 => Fin 4)) [∀ i x, Decidable (x ∈ H i)] (i : Fin 4)
    (y : Fin 4) : Decidable (h4.IsNBR H i y) := by
  unfold IsNBR; infer_instance

instance (H : Subgame (fun _ : Fin 4 => Fin 4)) [∀ i x, Decidable (x ∈ H i)] (i : Fin 4)
    (s : Fin 4 → Fin 4) : Decidable (h4.GloballyOptimal H i s) := by
  unfold GloballyOptimal; infer_instance

instance (i : Fin 4) (x : Fin 4) (s : Fin 4 → Fin 4) : Decidable (h4.IsBR i x s) := by
  unfold IsBR; infer_instance

/-- Subgames of `h4` given by an upper bound on each player's strategy. -/
def h4Box (b : Fin 4 → Fin 4) : Subgame (fun _ : Fin 4 => Fin 4) := fun i => {x | x ≤ b i}

instance (b : Fin 4 → Fin 4) (i x : Fin 4) : Decidable (x ∈ h4Box b i) := by
  unfold h4Box; infer_instance

/-- An elimination step that only touches player `j`. -/
def SinglePlayer {ι : Type*} {S : ι → Type*} (H H' : Subgame S) : Prop :=
  ∃ j, ∀ l, l ≠ j → H' l = H l

lemma h4_elimStep (b b' : Fin 4 → Fin 4)
    (h : ∀ i (y : Fin 4), (y ≤ b' i → y ≤ b i) ∧ (y ≤ b i → ¬ y ≤ b' i → h4.IsNBR (h4Box b) i y)) :
    h4.ElimStep (h4Box b) (h4Box b') :=
  ⟨fun i y hy => (h i y).1 hy, fun i y hy hy' => (h i y).2 hy hy'⟩

/-- The single-player sequence `i, p, q, k` of length `4`. -/
def h4Fast : ℕ → Subgame (fun _ : Fin 4 => Fin 4)
  | 0 => h4Box ![3, 3, 3, 3]
  | 1 => h4Box ![0, 3, 3, 3]
  | 2 => h4Box ![0, 3, 3, 0]
  | 3 => h4Box ![0, 3, 0, 0]
  | _ => h4Box ![0, 0, 0, 0]

/-- The witness order for `i`: `p, q, p, q, p, q, k`, then `i` (first elimination of `i` at
step `7`). -/
def h4Slow : ℕ → Subgame (fun _ : Fin 4 => Fin 4)
  | 0 => h4Box ![3, 3, 3, 3]
  | 1 => h4Box ![3, 3, 3, 2]
  | 2 => h4Box ![3, 3, 2, 2]
  | 3 => h4Box ![3, 3, 2, 1]
  | 4 => h4Box ![3, 3, 1, 1]
  | 5 => h4Box ![3, 3, 1, 0]
  | 6 => h4Box ![3, 3, 0, 0]
  | 7 => h4Box ![3, 0, 0, 0]
  | _ => h4Box ![0, 0, 0, 0]

lemma h4Box_full : h4Box ![3, 3, 3, 3] = full := by
  funext i; ext x; fin_cases i <;> fin_cases x <;> simp [h4Box, full]

lemma h4Box_zero : h4Box ![0, 0, 0, 0] = fun i => {(fun _ => (0 : Fin 4)) i} := by
  funext i; ext x; fin_cases i <;> fin_cases x <;> simp [h4Box]

set_option maxRecDepth 100000 in
lemma h4Fast_solves : h4.Solves h4Fast 4 (fun _ => 0) := by
  refine ⟨⟨h4Box_full, fun k hk => ?_⟩, h4Box_zero⟩
  interval_cases k <;> exact h4_elimStep _ _ (by decide)

lemma h4Fast_single : ∀ k < 4, SinglePlayer (h4Fast k) (h4Fast (k + 1)) := by
  intro k hk
  interval_cases k
  · exact ⟨0, fun l hl => by fin_cases l <;> first | exact absurd rfl hl | rfl⟩
  · exact ⟨3, fun l hl => by fin_cases l <;> first | exact absurd rfl hl | rfl⟩
  · exact ⟨2, fun l hl => by fin_cases l <;> first | exact absurd rfl hl | rfl⟩
  · exact ⟨1, fun l hl => by fin_cases l <;> first | exact absurd rfl hl | rfl⟩

set_option maxRecDepth 100000 in
lemma h4Slow_solves : h4.Solves h4Slow 8 (fun _ => 0) := by
  refine ⟨⟨h4Box_full, fun k hk => ?_⟩, h4Box_zero⟩
  interval_cases k <;> exact h4_elimStep _ _ (by decide)

set_option maxRecDepth 100000 in
lemma h4_hasClearOutcome : h4.HasClearOutcome (fun _ => 0) := by
  refine ⟨⟨_, _, h4Fast_solves⟩, fun i => ?_⟩
  by_cases hi : i = 0
  · subst hi
    refine ⟨h4Slow, 8, 7, h4Slow_solves, by norm_num, ?_, ?_⟩
    · ext x; fin_cases x <;> simp [h4Slow, h4Box]
    · rw [show h4Slow 7 = h4Box ![3, 0, 0, 0] from rfl]; decide
  · refine ⟨h4Fast, 4, 0, h4Fast_solves, by norm_num, ?_, ?_⟩
    · ext x; fin_cases i <;> fin_cases x <;> simp [h4Fast, h4Box]
    · rw [show h4Fast 0 = h4Box ![3, 3, 3, 3] from rfl]; revert i; decide

def h4BR (i : Fin 4) (p : Fin 4 → Fin 4) : Fin 4 :=
  if i = 0 then 0 else h4Target i p

set_option maxRecDepth 100000 in
lemma h4BR_isBRRule : IsBRRule h4 h4BR := by
  intro i p; revert i p; decide

def h4Mech : Mechanism (fun _ : Fin 4 => Fin 4) := roundRobin (n := 3) ![1, 1, 3, 3]

def h4Dev : ∀ i : Fin 4, RStrategy (fun _ : Fin 4 => Fin 4) i :=
  update (brStrategy h4Mech h4BR) 0 (fun _ => 1)

def h4Traj : ℕ → Fin 4 → Fin 4
  | 0 => ![1, 1, 3, 3]
  | t + 1 => update (h4Traj t) (rrPlayer 3 t)
      (if rrPlayer 3 t = 0 then 1 else h4BR (rrPlayer 3 t) (h4Traj t))

lemma h4Dev_prof (t : ℕ) : h4Mech.prof h4Dev t = h4Traj t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [h4Mech, roundRobin_prof_succ, ← h4Mech, h4Traj, ← ih]
    congr 1
    by_cases h : rrPlayer 3 t = 0
    · simp [h, h4Dev]
    · simp [h4Dev, h, brStrategy_hist]

set_option maxRecDepth 100000 in
/-- **Theorem 2.7 (2) is false also for single-player elimination steps.** `h4` is NBR-solvable
with the clear outcome `0` by a sequence of `4` single-player steps (so `e_G ≤ 4` under either
reading of Definition 2.4); after exactly `4` rounds of round robin from `(1, 1, 3, 3)`, the
deviation "always announce `1`" of player `0` ends at `(1, 1, 0, 0)` with utility `2 > 1`. -/
theorem theorem_2_7_false_single_steps :
    h4.Solves h4Fast 4 (fun _ => 0) ∧ (∀ k < 4, SinglePlayer (h4Fast k) (h4Fast (k + 1))) ∧
      h4.HasClearOutcome (fun _ => 0) ∧ IsBRRule h4 h4BR ∧
      (∀ σ, HasRounds (h4Mech.acts σ) 16 4) ∧
      h4Mech.prof (brStrategy h4Mech h4BR) 16 = (fun _ => 0) ∧
      h4Mech.prof h4Dev 16 = ![1, 1, 0, 0] ∧
      ¬ IsIncentiveCompatible h4 h4Mech h4BR 16 := by
  have hR : ∀ σ, HasRounds (h4Mech.acts σ) 16 4 := fun σ => roundRobin_hasRounds _ σ 4
  have hhon : h4Mech.prof (brStrategy h4Mech h4BR) 16 = fun _ => 0 :=
    theorem_2_7_convergence h4Mech h4Fast_solves h4BR_isBRRule le_rfl (hR _) 16 le_rfl
  have hdev : h4Mech.prof h4Dev 16 = ![1, 1, 0, 0] := by
    rw [h4Dev_prof]; decide
  refine ⟨h4Fast_solves, h4Fast_single, h4_hasClearOutcome, h4BR_isBRRule, hR, hhon, hdev, ?_⟩
  intro hIC
  have := hIC 0 (fun _ => 1)
  rw [show update (brStrategy h4Mech h4BR) 0 (fun _ => 1) = h4Dev from rfl, hdev, hhon] at this
  exact absurd this (by decide)

/-! ## Two-player games -/

/-- A two-player game with binary strategies given by its two utility tables, tie-breaking
`0 ≺ 1`. -/
def game2 (u : Fin 2 → (Fin 2 → Fin 2) → ℕ) : TieBreakGame (Fin 2) (fun _ => Fin 2) ℕ where
  utility := u
  prec _ x y := x < y

instance (u : Fin 2 → (Fin 2 → Fin 2) → ℕ) (i : Fin 2) (x y : Fin 2) (s : Fin 2 → Fin 2) :
    Decidable ((game2 u).Beats i x y s) :=
  inferInstanceAs (Decidable (u i (update s i y) < u i (update s i x) ∨
    (u i (update s i y) = u i (update s i x) ∧ y < x)))

instance (u : Fin 2 → (Fin 2 → Fin 2) → ℕ) (i : Fin 2) (x : Fin 2) (s : Fin 2 → Fin 2) :
    Decidable ((game2 u).IsBR i x s) := by
  unfold IsBR; infer_instance

instance (u : Fin 2 → (Fin 2 → Fin 2) → ℕ) (H : Subgame (fun _ : Fin 2 => Fin 2))
    [∀ i x, Decidable (x ∈ H i)] (i : Fin 2) (y : Fin 2) : Decidable ((game2 u).IsNBR H i y) := by
  unfold IsNBR; infer_instance

instance (u : Fin 2 → (Fin 2 → Fin 2) → ℕ) (H : Subgame (fun _ : Fin 2 => Fin 2))
    [∀ i x, Decidable (x ∈ H i)] (i : Fin 2) (s : Fin 2 → Fin 2) :
    Decidable ((game2 u).GloballyOptimal H i s) := by
  unfold GloballyOptimal; infer_instance

lemma game2_elimStep (u : Fin 2 → (Fin 2 → Fin 2) → ℕ) (H H' : Subgame (fun _ : Fin 2 => Fin 2))
    [∀ i x, Decidable (x ∈ H i)] [∀ i x, Decidable (x ∈ H' i)]
    (h : ∀ i (y : Fin 2), (y ∈ H' i → y ∈ H i) ∧ (y ∈ H i → y ∉ H' i → (game2 u).IsNBR H i y)) :
    (game2 u).ElimStep H H' :=
  ⟨fun i y hy => (h i y).1 hy, fun i y hy hy' => (h i y).2 hy hy'⟩

/-- Two-player subgames given by Boolean masks. -/
def mask2 (a : Fin 2 → Fin 2 → Bool) : Subgame (fun _ : Fin 2 => Fin 2) := fun i => {x | a i x}

instance (a : Fin 2 → Fin 2 → Bool) (i x : Fin 2) : Decidable (x ∈ mask2 a i) := by
  unfold mask2; infer_instance

lemma mask2_true : mask2 (fun _ _ => true) = full := by
  funext i; ext x; simp [mask2, full]

/-- An elimination sequence through three masks `full = a₀, a₁, a₂`. -/
def seq2 (a₁ a₂ : Fin 2 → Fin 2 → Bool) : ℕ → Subgame (fun _ : Fin 2 => Fin 2)
  | 0 => mask2 (fun _ _ => true)
  | 1 => mask2 a₁
  | _ => mask2 a₂

instance (a₁ a₂ : Fin 2 → Fin 2 → Bool) (k : ℕ) (i x : Fin 2) : Decidable (x ∈ seq2 a₁ a₂ k i) := by
  unfold seq2; split <;> infer_instance

/-! ### Outdated information -/

/-- Player `0` has the dominant strategy `0`, player `1` wants to copy player `0`. -/
def copyU : Fin 2 → (Fin 2 → Fin 2) → ℕ
  | 0, s => if s 0 = 0 then 1 else 0
  | 1, s => if s 1 = s 0 then 1 else 0

/-- The outdated run: `(1, 1)`, then `(0, 1)` forever. -/
def copyRun (t : ℕ) : Fin 2 → Fin 2 := if t = 0 then ![1, 1] else ![0, 1]

/-- **Extension (1) of Theorem 2.7 needs rounds measured by fresh information.** In the
two-player game `copyU`, NBR-solvable in two steps with outcome `(0, 0)` (and clear outcome),
there is a run in which *every player best-responds at every time step*, each to information
from time `0` (outdated), so every time step is a round in the paper's sense, yet the run never
reaches `(0, 0)`. -/
theorem outdated_information_false :
    (game2 copyU).Solves (seq2 (fun i x => x = 0 ∨ i = 1) (fun _ x => x = 0)) 2 ![0, 0] ∧
    (∀ t (j : Fin 2), ∃ v : Fin 2 → Fin 2, (∀ l, l ≠ j → ∃ τ ≤ t, v l = copyRun τ l) ∧
      (game2 copyU).IsBR j (copyRun (t + 1) j) v) ∧
    ∀ t, copyRun t ≠ ![0, 0] := by
  refine ⟨⟨⟨mask2_true, fun k hk => ?_⟩, ?_⟩, fun t j => ⟨![1, 1], fun l _ => ⟨0, by omega, ?_⟩,
    ?_⟩, fun t => ?_⟩
  · interval_cases k <;> exact game2_elimStep _ _ _ (by decide)
  · funext i; ext x; fin_cases i <;> fin_cases x <;> simp [seq2, mask2]
  · fin_cases l <;> rfl
  · have : copyRun (t + 1) = ![0, 1] := by simp [copyRun]
    rw [this]; revert j; decide
  · unfold copyRun; split_ifs <;> decide

/-! ### Figure 1 -/

/-- Figure 1: rows `A = 0`, `B = 1`, columns `C = 0`, `D = 1`. -/
def fig1U : Fin 2 → (Fin 2 → Fin 2) → ℕ
  | 0, s => ![![2, 0], ![3, 1]] (s 0) (s 1)
  | 1, s => ![![1, 0], ![0, 2]] (s 0) (s 1)

def fig1BR (i : Fin 2) (p : Fin 2 → Fin 2) : Fin 2 := if (game2 fig1U).Beats i 1 0 p then 1 else 0

lemma fig1BR_isBRRule : IsBRRule (game2 fig1U) fig1BR := by
  intro i p; revert i p; decide

def fig1Mech : Mechanism (fun _ : Fin 2 => Fin 2) := roundRobin (n := 1) (fun _ => 0)

def fig1Traj (σ0 : Fin 2) : ℕ → Fin 2 → Fin 2
  | 0 => fun _ => 0
  | t + 1 => update (fig1Traj σ0 t) (rrPlayer 1 t)
      (if rrPlayer 1 t = 0 then σ0 else fig1BR (rrPlayer 1 t) (fig1Traj σ0 t))

/-- **Figure 1**: the game is NBR-solvable (`A` is dominated, then `C`) with outcome `(B, D)`,
which every best-response run reaches; but starting from `(A, C)`, the row player gains by never
moving: the round-robin best-response mechanism is not incentive compatible (for any even
horizon `2m ≥ 4`). -/
theorem figure_1 (m : ℕ) (hm : 2 ≤ m) :
    (game2 fig1U).Solves (seq2 (fun i x => x = 1 ∨ i = 1) (fun _ x => x = 1)) 2 ![1, 1] ∧
    ¬ IsIncentiveCompatible (game2 fig1U) fig1Mech fig1BR (2 * m) := by
  have hS : (game2 fig1U).Solves (seq2 (fun i x => x = 1 ∨ i = 1) (fun _ x => x = 1)) 2
      ![1, 1] := by
    refine ⟨⟨mask2_true, fun k hk => ?_⟩, ?_⟩
    · interval_cases k <;> exact game2_elimStep _ _ _ (by decide)
    · funext i; ext x; fin_cases i <;> fin_cases x <;> simp [seq2, mask2]
  refine ⟨hS, fun hIC => ?_⟩
  have hhon := theorem_2_7_convergence fig1Mech hS fig1BR_isBRRule hm
    (roundRobin_hasRounds (n := 1) _ _ m) (2 * m) le_rfl
  have hdev : ∀ t, fig1Mech.prof (update (brStrategy fig1Mech fig1BR) 0 (fun _ => 0)) t =
      fig1Traj 0 t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [fig1Mech, roundRobin_prof_succ, ← fig1Mech, fig1Traj, ← ih]
      congr 1
      by_cases h : rrPlayer 1 t = 0
      · simp [h]
      · simp [h, brStrategy_hist]
  have hconst : ∀ t, fig1Traj 0 t = fun _ => 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [fig1Traj, ih]
      funext j
      by_cases h : rrPlayer 1 t = 0 <;> simp only [h, ↓reduceIte] <;> revert j <;>
        generalize rrPlayer 1 t = p at * <;> decide +revert
  have := hIC 0 (fun _ => 0)
  rw [hdev, hconst, hhon] at this
  exact absurd this (by decide)

/-! ### Figure 3 -/

/-- Figure 3 (prisoner's dilemma): `C = 0`, `D = 1`. -/
def fig3U : Fin 2 → (Fin 2 → Fin 2) → ℕ
  | 0, s => ![![2, 0], ![3, 1]] (s 0) (s 1)
  | 1, s => ![![2, 3], ![0, 1]] (s 0) (s 1)

/-- **Figure 3**: the prisoner's dilemma is NBR-solvable (in one step) with the clear outcome
`(D, D)`, but both players strictly prefer `(C, C)`, which they can keep forever by jointly
announcing `C`: best-response mechanisms are not collusion-proof. -/
theorem figure_3 :
    (game2 fig3U).Solves (seq2 (fun _ x => x = 1) (fun _ x => x = 1)) 1 ![1, 1] ∧
    (game2 fig3U).HasClearOutcome ![1, 1] ∧
    ∀ i : Fin 2, (game2 fig3U).utility i ![1, 1] < (game2 fig3U).utility i ![0, 0] := by
  have hS : (game2 fig3U).Solves (seq2 (fun _ x => x = 1) (fun _ x => x = 1)) 1 ![1, 1] := by
    refine ⟨⟨mask2_true, fun k hk => ?_⟩, ?_⟩
    · interval_cases k; exact game2_elimStep _ _ _ (by decide)
    · funext i; ext x; fin_cases i <;> fin_cases x <;> simp [seq2, mask2]
  refine ⟨hS, ⟨⟨_, _, hS⟩, fun i => ?_⟩, by decide⟩
  -- for player `i`: first the other player eliminates `C`, then `i`
  refine ⟨seq2 (fun j x => x = 1 ∨ j = i) (fun _ x => x = 1), 2, 1, ⟨⟨mask2_true, ?_⟩, ?_⟩,
    by norm_num, ?_, ?_⟩
  · intro k hk; interval_cases k <;> exact game2_elimStep _ _ _ (by revert i; decide)
  · funext j; ext x; fin_cases j <;> fin_cases x <;> simp [seq2, mask2]
  · ext x; simp [seq2, mask2]
  · revert i; decide

/-! ## Infinite strategy spaces -/

/-- One player choosing a natural number, utility = the number, tie-breaking `<`. -/
def natGame : TieBreakGame Unit (fun _ => ℕ) ℕ where
  utility _ s := s ()
  prec _ x y := x < y

/-- The two-step sequence `ℕ ⊇ {x}`. -/
def natSeq (x : ℕ) : ℕ → Subgame (fun _ : Unit => ℕ)
  | 0 => full
  | _ => fun _ => {x}

/-- **The remark after Definition 2.3 fails for infinite strategy spaces**: in `natGame` every
profile `x` is the outcome of a one-step NBR elimination (all other strategies are beaten by
their successors), so the outcome is not unique, and it is never a Nash equilibrium. (Tie-broken
best responses do not exist here; with `HasBR` the remark holds: `Solves.unique`,
`Solves.isNash`.) -/
theorem nbr_outcome_not_unique (x : ℕ) :
    natGame.Solves (natSeq x) 1 (fun _ => x) ∧ ¬ natGame.IsNash (fun _ => x) := by
  refine ⟨⟨⟨rfl, fun k hk => ?_⟩, rfl⟩, fun h => ?_⟩
  · have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨fun _ _ _ => trivial, fun i y _ hy s _ => ⟨y + 1, trivial, Or.inl ?_⟩⟩
    simp [natGame]
  · have := h () (x + 1)
    simp [natGame] at this

end Podc.BestResponseMechanisms.Counterexamples
