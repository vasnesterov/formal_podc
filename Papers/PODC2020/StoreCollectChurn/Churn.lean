import Mathlib
import Papers.PODC2020.StoreCollectChurn.Constraints

/-!
# The churn model and Lemmas 1–3, Corollary 1 of [AKSW20]

Attiya, Kumari, Somani, Welch, *Store-Collect in the Presence of Continuous Churn with Application
to Snapshots and Lattice Agreement* (PODC 2020; arXiv 2003.07787v3), Sections 3 and 5.

We abstract a timed execution (Section 3) to what the counting lemmas need: every node `p` has an
entry time `enter p ≥ 0` (the time of its first step; the initial members `S0` are the nodes with
`enter p = 0`, a nonempty set), and possibly a leave time or a crash time (at most one of the two,
both not before the entry). A node is *present* at `t` if it entered at or before `t` and did not
leave at or before `t`; a crashed node stays present forever; a node is *active* at `t` if it is
present and has not crashed at or before `t`. `N t` is the number of present nodes.

The paper's assumptions:
* **Churn Assumption**: for all `t > 0`, the number of ENTER and LEAVE events in `[t, t + D]` is
  at most `α · N(t)` (`ChurnExecution.ChurnAssumption`);
* **Minimum System Size**: `N(t) ≥ Nmin` for `t ≥ 0` (`ChurnExecution.MinimumSystemSize`);
* **Failure Fraction Assumption**: at most `Δ · N(t)` nodes are crashed at `t ≥ 0`
  (`ChurnExecution.FailureFraction`).

The paper implicitly assumes `N(t)` is finite; we assume the slightly stronger (and, given the churn
assumption, equivalent) *local finiteness*: only finitely many nodes have entered by any time `t`.

Main results:
* `lemma1_a`, `lemma1_b` (Lemma 1), and their extension to intervals of length `≤ i · D`
  (`enters_le`, `N_le`);
* `lemma2` (Lemma 2, as stated: `0 < α < 0.206`, `i ≤ 3`), the sharper `lemma2_of_sq`
  (`2 (1 - α)^2 ≥ 1`, i.e. `α ≤ 1 - 1/√2 ≈ 0.293`, suffices for `i ≤ 3`) and `lemma2_four`
  (`α < 0.206` even gives `i ≤ 4`); the general `leaves_le`;
* `lemma3` (Lemma 3);
* `corollary1` (Corollary 1, from the cleared Constraint (A') and (B)), and `corollary1_of_Z_pos`,
  which only needs `Z > 0` and `Nmin ≥ 1`: Constraint (A) is not needed for Corollary 1.

The case `t = 0` of Lemmas 1–3 is not covered by the Churn Assumption (stated for `t > 0`); we
derive it from local finiteness (`churn_Ioc`).
-/

open Set

namespace Podc.StoreCollectChurn

/-- A timed execution of [AKSW20], Section 3, abstracted to entry, leave and crash times. -/
structure ChurnExecution (Node : Type*) where
  /-- Time of the first step (`ENTER_p`, or initial membership at time `0`). -/
  enter : Node → ℝ
  /-- Time of `LEAVE_p`, if it occurs. -/
  leave : Node → Option ℝ
  /-- Time of `CRASH_p`, if it occurs. -/
  crash : Node → Option ℝ
  enter_nonneg : ∀ p, 0 ≤ enter p
  enter_le_leave : ∀ p l, leave p = some l → enter p ≤ l
  enter_le_crash : ∀ p c, crash p = some c → enter p ≤ c
  /-- At most one of `CRASH_p` and `LEAVE_p` occurs. -/
  leave_or_crash : ∀ p, leave p = none ∨ crash p = none
  /-- Local finiteness: finitely many nodes have entered by any time. -/
  finite_entered : ∀ t, {p | enter p ≤ t}.Finite
  /-- The set `S0` of initial members is nonempty. -/
  S0_nonempty : ∃ p, enter p = 0

namespace ChurnExecution

variable {Node : Type*} (E : ChurnExecution Node)

/-- The set `S0` of initial members (finite by local finiteness, nonempty by assumption). -/
def S0 : Set Node := {p | E.enter p = 0}

/-- `p` has left at or before `t`. -/
def LeftBy (p : Node) (t : ℝ) : Prop := ∃ l, E.leave p = some l ∧ l ≤ t

/-- `p` has crashed at or before `t`. -/
def CrashedBy (p : Node) (t : ℝ) : Prop := ∃ c, E.crash p = some c ∧ c ≤ t

/-- Nodes present at time `t`: entered at or before `t` and not left at or before `t`. -/
def present (t : ℝ) : Set Node := {p | E.enter p ≤ t ∧ ¬ E.LeftBy p t}

/-- `N(t)`, the number of nodes present at time `t`. -/
noncomputable def N (t : ℝ) : ℕ := (E.present t).ncard

/-- Nodes active at time `t`: present and not crashed. -/
def active (t : ℝ) : Set Node := {p | p ∈ E.present t ∧ ¬ E.CrashedBy p t}

/-- Nodes crashed at time `t` (`CRASH_p` occurs at or before `t`; such nodes are present). -/
def crashed (t : ℝ) : Set Node := {p | E.CrashedBy p t}

/-- Nodes with an `ENTER` event in the set of times `I`. -/
def entersIn (I : Set ℝ) : Set Node := {p | E.enter p ∈ I}

/-- Nodes with a `LEAVE` event in the set of times `I`. -/
def leavesIn (I : Set ℝ) : Set Node := {p | ∃ l, E.leave p = some l ∧ l ∈ I}

/-- Churn Assumption of [AKSW20], Section 3: for all times `t > 0`, there are at most `α · N(t)`
ENTER and LEAVE events in `[t, t + D]` (each node enters once and leaves at most once). -/
def ChurnAssumption (α D : ℝ) : Prop :=
  ∀ t > 0, ((E.entersIn (Icc t (t + D))).ncard + (E.leavesIn (Icc t (t + D))).ncard : ℝ) ≤
    α * E.N t

/-- Minimum System Size assumption of [AKSW20], Section 3. -/
def MinimumSystemSize (Nmin : ℕ) : Prop := ∀ t ≥ 0, Nmin ≤ E.N t

/-- Failure Fraction Assumption of [AKSW20], Section 3: for all `t ≥ 0`, at most `Δ · N(t)` nodes
are crashed at time `t`. -/
def FailureFraction (Δ : ℝ) : Prop := ∀ t ≥ 0, ((E.crashed t).ncard : ℝ) ≤ Δ * E.N t

/-! ### Basic facts -/

theorem crashed_subset_present (t : ℝ) : E.crashed t ⊆ E.present t := by
  rintro p ⟨c, hc, hct⟩
  refine ⟨(E.enter_le_crash p c hc).trans hct, ?_⟩
  rintro ⟨l, hl, -⟩
  rcases E.leave_or_crash p with h | h <;> simp_all

theorem present_finite (t : ℝ) : (E.present t).Finite :=
  (E.finite_entered t).subset fun _ hp => hp.1

theorem entersIn_Ioc_finite (a b : ℝ) : (E.entersIn (Ioc a b)).Finite :=
  (E.finite_entered b).subset fun _ hp => hp.2

theorem leavesIn_Ioc_finite (a b : ℝ) : (E.leavesIn (Ioc a b)).Finite :=
  (E.finite_entered b).subset fun p ⟨l, hl, hlI⟩ => (E.enter_le_leave p l hl).trans hlI.2

theorem leavesIn_Icc_finite (a b : ℝ) : (E.leavesIn (Icc a b)).Finite :=
  (E.finite_entered b).subset fun p ⟨l, hl, hlI⟩ => (E.enter_le_leave p l hl).trans hlI.2

theorem entersIn_Icc_finite (a b : ℝ) : (E.entersIn (Icc a b)).Finite :=
  (E.finite_entered b).subset fun _ hp => hp.2

theorem crashed_finite (t : ℝ) : (E.crashed t).Finite :=
  (E.present_finite t).subset (E.crashed_subset_present t)

/-- Conservation of nodes: for `t ≤ t'`,
`N(t') + #leaves in (t, t'] = N(t) + #enters in (t, t']`. -/
theorem N_add_leaves {t t' : ℝ} (h : t ≤ t') :
    E.N t' + (E.leavesIn (Ioc t t')).ncard = E.N t + (E.entersIn (Ioc t t')).ncard := by
  have hW1 : E.present t' ∪ E.leavesIn (Ioc t t') = {p | E.enter p ≤ t' ∧ ¬ E.LeftBy p t} := by
    ext p
    simp only [present, leavesIn, LeftBy, mem_union, mem_ofPred_eq, mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨l, hl, hl1, hl2⟩)
      · exact ⟨h1, fun ⟨l, hl, hlt⟩ => h2 ⟨l, hl, hlt.trans h⟩⟩
      · refine ⟨(E.enter_le_leave p l hl).trans hl2, ?_⟩
        rintro ⟨l', hl', hl't⟩
        rw [hl] at hl'
        cases hl'
        linarith
    · rintro ⟨h1, h2⟩
      by_cases h3 : ∃ l, E.leave p = some l ∧ l ≤ t'
      · obtain ⟨l, hl, hlt⟩ := h3
        refine Or.inr ⟨l, hl, ?_, hlt⟩
        by_contra h4
        exact h2 ⟨l, hl, le_of_not_gt h4⟩
      · exact Or.inl ⟨h1, h3⟩
  have hW2 : E.present t ∪ E.entersIn (Ioc t t') = {p | E.enter p ≤ t' ∧ ¬ E.LeftBy p t} := by
    ext p
    simp only [present, entersIn, LeftBy, mem_union, mem_ofPred_eq, mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1.trans h, h2⟩
      · refine ⟨h2, ?_⟩
        rintro ⟨l, hl, hlt⟩
        have := E.enter_le_leave p l hl
        linarith
    · rintro ⟨h1, h2⟩
      by_cases h3 : E.enter p ≤ t
      · exact Or.inl ⟨h3, h2⟩
      · exact Or.inr ⟨lt_of_not_ge h3, h1⟩
  have hd1 : Disjoint (E.present t') (E.leavesIn (Ioc t t')) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, hp⟩ ⟨l, hl, hlI⟩
    exact hp ⟨l, hl, hlI.2⟩
  have hd2 : Disjoint (E.present t) (E.entersIn (Ioc t t')) := by
    rw [Set.disjoint_left]
    rintro p ⟨hp, -⟩ hI
    exact absurd hp (not_le.mpr hI.1)
  unfold N
  rw [← Set.ncard_union_eq hd1 (E.present_finite _) (E.leavesIn_Ioc_finite _ _),
    ← Set.ncard_union_eq hd2 (E.present_finite _) (E.entersIn_Ioc_finite _ _), hW1, hW2]

/-- Consequence of conservation: `N(t') ≤ N(t) + #enters in (t, t']`. -/
theorem N_le_add_enters {t t' : ℝ} (h : t ≤ t') :
    (E.N t' : ℝ) ≤ E.N t + (E.entersIn (Ioc t t')).ncard := by
  have := E.N_add_leaves h
  have : E.N t' ≤ E.N t + (E.entersIn (Ioc t t')).ncard := by omega
  exact_mod_cast this

/-- For `t = 0` the Churn Assumption (stated for `t > 0`) still bounds the events in `(0, D]`:
take `ε > 0` smaller than every event time in `(0, D]` (there are finitely many). -/
theorem churn_zero {α D : ℝ} (hD : 0 < D) (hc : E.ChurnAssumption α D) :
    ((E.entersIn (Ioc 0 D)).ncard + (E.leavesIn (Ioc 0 D)).ncard : ℝ) ≤ α * E.N 0 := by
  set F := {p | E.enter p ≤ D}
  have hF : F.Finite := E.finite_entered D
  -- a good `ε`
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), 0 < ε ∧ ε ≤ D ∧ ∀ p ∈ F,
      (0 < E.enter p → ε < E.enter p) ∧ (∀ l, E.leave p = some l → 0 < l → ε < l) := by
    refine eventually_mem_nhdsWithin.and
      ((show ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε ≤ D by
        filter_upwards [Ioo_mem_nhdsGT hD] with ε hε using hε.2.le).and ?_)
    rw [Filter.eventually_all_finite hF]
    intro p _
    refine Filter.Eventually.and ?_ ?_
    · by_cases h : 0 < E.enter p
      · filter_upwards [Ioo_mem_nhdsGT h] with ε hε using fun _ => hε.2
      · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
    · cases hl : E.leave p with
      | none => exact Filter.Eventually.of_forall fun _ l h => by simp at h
      | some l =>
        by_cases h : 0 < l
        · filter_upwards [Ioo_mem_nhdsGT h] with ε hε
          intro l' hl' _
          cases hl'
          exact hε.2
        · exact Filter.Eventually.of_forall fun _ l' hl' h' => by
            cases hl'; exact absurd h' h
  obtain ⟨ε, hε0, hεD, hεF⟩ := hev.exists
  have hsub1 : E.entersIn (Ioc 0 D) ⊆ E.entersIn (Icc ε (ε + D)) := by
    intro p ⟨h1, h2⟩
    exact ⟨((hεF p h2).1 h1).le, by linarith⟩
  have hsub2 : E.leavesIn (Ioc 0 D) ⊆ E.leavesIn (Icc ε (ε + D)) := by
    rintro p ⟨l, hl, h1, h2⟩
    have hpF : p ∈ F := (E.enter_le_leave p l hl).trans h2
    exact ⟨l, hl, ((hεF p hpF).2 l hl h1).le, by linarith⟩
  have hN : E.present ε = E.present 0 := by
    ext p
    simp only [present, LeftBy, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hpF : p ∈ F := h1.trans hεD
      have he : E.enter p ≤ 0 := by
        by_contra h
        have := (hεF p hpF).1 (lt_of_not_ge h)
        linarith
      exact ⟨he, fun ⟨l, hl, hl0⟩ => h2 ⟨l, hl, hl0.trans hε0.le⟩⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1.trans hε0.le, ?_⟩
      rintro ⟨l, hl, hlε⟩
      have hpF : p ∈ F := h1.trans hD.le
      by_cases hl0 : 0 < l
      · have := (hεF p hpF).2 l hl hl0
        linarith
      · exact h2 ⟨l, hl, le_of_not_gt hl0⟩
  have h := hc ε hε0
  rw [N, hN] at h
  have c1 := Set.ncard_le_ncard hsub1 (E.entersIn_Icc_finite _ _)
  have c2 := Set.ncard_le_ncard hsub2 (E.leavesIn_Icc_finite _ _)
  unfold N
  have : ((E.entersIn (Ioc 0 D)).ncard + (E.leavesIn (Ioc 0 D)).ncard : ℝ) ≤
      (E.entersIn (Icc ε (ε + D))).ncard + (E.leavesIn (Icc ε (ε + D))).ncard := by
    exact_mod_cast Nat.add_le_add c1 c2
  linarith

/-- The Churn Assumption for half-open intervals `(t, t + D]`, valid for all `t ≥ 0`. -/
theorem churn_Ioc {α D : ℝ} (hD : 0 < D) (hc : E.ChurnAssumption α D) {t : ℝ} (ht : 0 ≤ t) :
    ((E.entersIn (Ioc t (t + D))).ncard + (E.leavesIn (Ioc t (t + D))).ncard : ℝ) ≤
      α * E.N t := by
  rcases ht.lt_or_eq with ht | rfl
  · have c1 := Set.ncard_le_ncard (s := E.entersIn (Ioc t (t + D)))
      (t := E.entersIn (Icc t (t + D))) (fun p hp => Ioc_subset_Icc_self hp)
      (E.entersIn_Icc_finite _ _)
    have c2 := Set.ncard_le_ncard (s := E.leavesIn (Ioc t (t + D)))
      (t := E.leavesIn (Icc t (t + D))) (fun p ⟨l, hl, hlI⟩ => ⟨l, hl, Ioc_subset_Icc_self hlI⟩)
      (E.leavesIn_Icc_finite _ _)
    have : ((E.entersIn (Ioc t (t + D))).ncard + (E.leavesIn (Ioc t (t + D))).ncard : ℝ) ≤
        (E.entersIn (Icc t (t + D))).ncard + (E.leavesIn (Icc t (t + D))).ncard := by
      exact_mod_cast Nat.add_le_add c1 c2
    exact this.trans (hc t ht)
  · simpa using E.churn_zero hD hc

theorem entersIn_mono {a b b' : ℝ} (h : b ≤ b') :
    (E.entersIn (Ioc a b)).ncard ≤ (E.entersIn (Ioc a b')).ncard :=
  Set.ncard_le_ncard (fun _ hp => ⟨hp.1, hp.2.trans h⟩) (E.entersIn_Ioc_finite _ _)

theorem leavesIn_mono {a b b' : ℝ} (h : b ≤ b') :
    (E.leavesIn (Ioc a b)).ncard ≤ (E.leavesIn (Ioc a b')).ncard :=
  Set.ncard_le_ncard (fun _ ⟨l, hl, hlI⟩ => ⟨l, hl, hlI.1, hlI.2.trans h⟩)
    (E.leavesIn_Ioc_finite _ _)

theorem entersIn_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (E.entersIn (Ioc a c)).ncard ≤ (E.entersIn (Ioc a b)).ncard + (E.entersIn (Ioc b c)).ncard := by
  have : E.entersIn (Ioc a c) = E.entersIn (Ioc a b) ∪ E.entersIn (Ioc b c) := by
    ext p
    simp only [entersIn, mem_ofPred_eq, mem_union]
    rw [← Ioc_union_Ioc_eq_Ioc hab hbc, Set.mem_union]
  rw [this]
  exact Set.ncard_union_le _ _

theorem leavesIn_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (E.leavesIn (Ioc a c)).ncard ≤ (E.leavesIn (Ioc a b)).ncard + (E.leavesIn (Ioc b c)).ncard := by
  have : E.leavesIn (Ioc a c) = E.leavesIn (Ioc a b) ∪ E.leavesIn (Ioc b c) := by
    ext p
    simp only [leavesIn, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨l, hl, hlI⟩
      rw [← Ioc_union_Ioc_eq_Ioc hab hbc] at hlI
      rcases hlI with h | h
      · exact Or.inl ⟨l, hl, h⟩
      · exact Or.inr ⟨l, hl, h⟩
    · rintro (⟨l, hl, hlI⟩ | ⟨l, hl, hlI⟩)
      · exact ⟨l, hl, Ioc_subset_Ioc_right hbc hlI⟩
      · exact ⟨l, hl, Ioc_subset_Ioc_left hab hlI⟩
  rw [this]
  exact Set.ncard_union_le _ _

/-- One step of churn: `N(t + D) ≤ (1 + α) N(t)` for `t ≥ 0`. -/
theorem N_step {α D : ℝ} (hD : 0 < D) (hc : E.ChurnAssumption α D) {t : ℝ} (ht : 0 ≤ t) :
    (E.N (t + D) : ℝ) ≤ (1 + α) * E.N t := by
  have h1 := E.N_le_add_enters (show t ≤ t + D by linarith)
  have h2 := E.churn_Ioc hD hc ht
  have : (0 : ℝ) ≤ (E.leavesIn (Ioc t (t + D))).ncard := Nat.cast_nonneg _
  linarith

/-! ### Lemma 1 -/

/-- Lemma 1(a) of [AKSW20], extended to intervals of length at most `i · D`: for `t ≥ 0` and
`0 ≤ s ≤ i · D`, at most `((1 + α)^i - 1) · N(t)` nodes enter during `(t, t + s]`. -/
theorem enters_le {α D : ℝ} (hα : 0 ≤ α) (hD : 0 < D) (hc : E.ChurnAssumption α D) (i : ℕ) :
    ∀ t ≥ 0, ∀ s, 0 ≤ s → s ≤ i * D →
      ((E.entersIn (Ioc t (t + s))).ncard : ℝ) ≤ ((1 + α) ^ i - 1) * E.N t := by
  induction i with
  | zero =>
    intro t _ s hs hsi
    have : s = 0 := by simp at hsi; linarith
    subst this
    simp [entersIn]
  | succ i ih =>
    intro t ht s hs hsi
    have hpow : 1 ≤ (1 + α) ^ i := one_le_pow₀ (by linarith)
    have hN0 : (0 : ℝ) ≤ E.N t := Nat.cast_nonneg _
    have hchurn := E.churn_Ioc hD hc ht
    have hl0 : (0 : ℝ) ≤ (E.leavesIn (Ioc t (t + D))).ncard := Nat.cast_nonneg _
    have hstep : α ≤ (1 + α) ^ (i + 1) - 1 := by
      rw [pow_succ]; nlinarith
    rcases le_or_gt s D with hsD | hsD
    · have := E.entersIn_mono (a := t) (show t + s ≤ t + D by linarith)
      have : ((E.entersIn (Ioc t (t + s))).ncard : ℝ) ≤ (E.entersIn (Ioc t (t + D))).ncard := by
        exact_mod_cast this
      nlinarith
    · have hsplit := E.entersIn_split (show t ≤ t + D by linarith) (show t + D ≤ t + s by linarith)
      have hih := ih (t + D) (by linarith) (s - D) (by linarith)
        (by push_cast at hsi; nlinarith)
      rw [show t + D + (s - D) = t + s by ring] at hih
      have hNs := E.N_step hD hc ht
      have hsplit' : ((E.entersIn (Ioc t (t + s))).ncard : ℝ) ≤
          (E.entersIn (Ioc t (t + D))).ncard + (E.entersIn (Ioc (t + D) (t + s))).ncard := by
        exact_mod_cast hsplit
      have : ((1 + α) ^ i - 1) * (E.N (t + D) : ℝ) ≤ ((1 + α) ^ i - 1) * ((1 + α) * E.N t) :=
        mul_le_mul_of_nonneg_left hNs (by linarith)
      have e : ((1 + α) ^ (i + 1) - 1) * (E.N t : ℝ) =
          α * E.N t + ((1 + α) ^ i - 1) * ((1 + α) * E.N t) := by ring
      rw [e]
      linarith

/-- Lemma 1(b) of [AKSW20], extended to intervals of length at most `i · D`:
`N(t + s) ≤ (1 + α)^i · N(t)` for `t ≥ 0` and `0 ≤ s ≤ i · D`. -/
theorem N_le {α D : ℝ} (hα : 0 ≤ α) (hD : 0 < D) (hc : E.ChurnAssumption α D) (i : ℕ)
    {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : 0 ≤ s) (hsi : s ≤ i * D) :
    (E.N (t + s) : ℝ) ≤ (1 + α) ^ i * E.N t := by
  have h1 := E.N_le_add_enters (show t ≤ t + s by linarith)
  have h2 := E.enters_le hα hD hc i t ht s hs hsi
  linarith

/-- Lemma 1(a) of [AKSW20]: for all `i ∈ ℕ` and all `t ≥ 0`, at most `((1 + α)^i - 1) · N(t)`
nodes enter during `(t, t + i · D]`. -/
theorem lemma1_a {α D : ℝ} (hα : 0 ≤ α) (hD : 0 < D) (hc : E.ChurnAssumption α D) (i : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ((E.entersIn (Ioc t (t + i * D))).ncard : ℝ) ≤ ((1 + α) ^ i - 1) * E.N t :=
  E.enters_le hα hD hc i t ht _ (by positivity) le_rfl

/-- Lemma 1(b) of [AKSW20]: for all `i ∈ ℕ` and all `t ≥ 0`, `N(t + i · D) ≤ (1 + α)^i · N(t)`. -/
theorem lemma1_b {α D : ℝ} (hα : 0 ≤ α) (hD : 0 < D) (hc : E.ChurnAssumption α D) (i : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    (E.N (t + i * D) : ℝ) ≤ (1 + α) ^ i * E.N t :=
  E.N_le hα hD hc i ht (by positivity) le_rfl

/-! ### Lemma 2 -/

/-- The induction of Lemma 2 of [AKSW20], for intervals of length at most `i · D`: if
`2 (1 - α)^j ≥ 1` for all `j < i`, then for `t ≥ 0` and `0 ≤ s ≤ i · D` at most
`(1 - (1 - α)^i) · N(t)` nodes leave during `(t, t + s]`. -/
theorem leaves_le {α D : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hD : 0 < D)
    (hc : E.ChurnAssumption α D) (i : ℕ) (hi : ∀ j < i, 1 ≤ 2 * (1 - α) ^ j) :
    ∀ t ≥ 0, ∀ s, 0 ≤ s → s ≤ i * D →
      ((E.leavesIn (Ioc t (t + s))).ncard : ℝ) ≤ (1 - (1 - α) ^ i) * E.N t := by
  induction i with
  | zero =>
    intro t _ s hs hsi
    have : s = 0 := by simp at hsi; linarith
    subst this
    simp [leavesIn]
  | succ i ih =>
    intro t ht s hs hsi
    have hw1 : (1 - α) ^ i ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hw2 : 1 ≤ 2 * (1 - α) ^ i := hi i (Nat.lt_succ_self i)
    have hN0 : (0 : ℝ) ≤ E.N t := Nat.cast_nonneg _
    have hchurn := E.churn_Ioc hD hc ht
    have he0 : (0 : ℝ) ≤ (E.entersIn (Ioc t (t + D))).ncard := Nat.cast_nonneg _
    have hpow : (1 - α) ^ (i + 1) = (1 - α) ^ i * (1 - α) := pow_succ _ _
    rcases le_or_gt s D with hsD | hsD
    · have := E.leavesIn_mono (a := t) (show t + s ≤ t + D by linarith)
      have : ((E.leavesIn (Ioc t (t + s))).ncard : ℝ) ≤ (E.leavesIn (Ioc t (t + D))).ncard := by
        exact_mod_cast this
      have hstep : α ≤ 1 - (1 - α) ^ (i + 1) := by
        rw [hpow]; nlinarith
      nlinarith
    · have hsplit := E.leavesIn_split (show t ≤ t + D by linarith) (show t + D ≤ t + s by linarith)
      have hih := ih (fun j hj => hi j (Nat.lt_succ_of_lt hj)) (t + D) (by linarith) (s - D)
        (by linarith) (by push_cast at hsi; nlinarith)
      rw [show t + D + (s - D) = t + s by ring] at hih
      have hcons := E.N_add_leaves (show t ≤ t + D by linarith)
      have hcons' : (E.N (t + D) : ℝ) + (E.leavesIn (Ioc t (t + D))).ncard =
          E.N t + (E.entersIn (Ioc t (t + D))).ncard := by exact_mod_cast hcons
      have hsplit' : ((E.leavesIn (Ioc t (t + s))).ncard : ℝ) ≤
          (E.leavesIn (Ioc t (t + D))).ncard + (E.leavesIn (Ioc (t + D) (t + s))).ncard := by
        exact_mod_cast hsplit
      set ℓ : ℝ := ((E.leavesIn (Ioc t (t + D))).ncard : ℝ)
      set e : ℝ := ((E.entersIn (Ioc t (t + D))).ncard : ℝ)
      set c : ℝ := 1 - (1 - α) ^ i
      -- `N(t + D) ≤ (1 + α) N(t) - 2 ℓ`
      have hM : (E.N (t + D) : ℝ) ≤ (1 + α) * E.N t - 2 * ℓ := by linarith
      have hc0 : 0 ≤ c := by simp only [c]; linarith
      have h12c : 0 ≤ 1 - 2 * c := by simp only [c]; linarith
      have hℓ : ℓ ≤ α * E.N t := by linarith
      have k1 := mul_le_mul_of_nonneg_left hM hc0
      have k2 := mul_le_mul_of_nonneg_left hℓ h12c
      have e2 : 1 - (1 - α) ^ (i + 1) = α + c - c * α := by
        rw [hpow]; simp only [c]; ring
      rw [e2]
      nlinarith

/-- Lemma 2 of [AKSW20]: for all `α` with `0 < α < 0.206`, all `i ≤ 3`, and every `t ≥ 0`, at most
`(1 - (1 - α)^i) · N(t)` nodes leave during `(t, t + i · D]`. -/
theorem lemma2 {α D : ℝ} (hα : 0 < α) (hα' : α < 0.206) (hD : 0 < D)
    (hc : E.ChurnAssumption α D) {i : ℕ} (hi : i ≤ 3) {t : ℝ} (ht : 0 ≤ t) :
    ((E.leavesIn (Ioc t (t + i * D))).ncard : ℝ) ≤ (1 - (1 - α) ^ i) * E.N t := by
  refine E.leaves_le hα.le (by norm_num at hα'; linarith) hD hc i ?_ t ht _ (by positivity) le_rfl
  intro j hj
  have h1 : (0.794 : ℝ) ≤ 1 - α := by norm_num at hα' ⊢; linarith
  have : (0.794 : ℝ) ^ j ≤ (1 - α) ^ j := pow_le_pow_left₀ (by norm_num) h1 j
  have : j ≤ 2 := by omega
  interval_cases j <;> norm_num at this ⊢ <;> linarith

/-- Lemma 2 of [AKSW20] with the sharp hypothesis for `i ≤ 3`: the proof only needs
`2 (1 - α)^2 ≥ 1`, i.e. `α ≤ 1 - 1/√2 ≈ 0.293` (not `α < 0.206`). The statement also covers
intervals of any length `s ≤ i · D`. -/
theorem lemma2_of_sq {α D : ℝ} (hα : 0 ≤ α) (hα2 : 1 ≤ 2 * (1 - α) ^ 2) (hα1 : α ≤ 1)
    (hD : 0 < D) (hc : E.ChurnAssumption α D) {i : ℕ} (hi : i ≤ 3) {t : ℝ} (ht : 0 ≤ t)
    {s : ℝ} (hs : 0 ≤ s) (hsi : s ≤ i * D) :
    ((E.leavesIn (Ioc t (t + s))).ncard : ℝ) ≤ (1 - (1 - α) ^ i) * E.N t := by
  refine E.leaves_le hα hα1 hD hc i ?_ t ht s hs hsi
  intro j hj
  have h0 : 0 ≤ 1 - α := by linarith
  have h11 : 1 - α ≤ 1 := by linarith
  have : j ≤ 2 := by omega
  interval_cases j
  · norm_num
  · nlinarith
  · exact hα2

/-- The hypothesis `α < 0.206` of Lemma 2 of [AKSW20] actually yields the statement for `i ≤ 4`
(`0.206 < 1 - 2^(-1/3) ≈ 0.2063`), for intervals of any length `s ≤ i · D`. -/
theorem lemma2_four {α D : ℝ} (hα : 0 < α) (hα' : α < 0.206) (hD : 0 < D)
    (hc : E.ChurnAssumption α D) {i : ℕ} (hi : i ≤ 4) {t : ℝ} (ht : 0 ≤ t)
    {s : ℝ} (hs : 0 ≤ s) (hsi : s ≤ i * D) :
    ((E.leavesIn (Ioc t (t + s))).ncard : ℝ) ≤ (1 - (1 - α) ^ i) * E.N t := by
  refine E.leaves_le hα.le (by norm_num at hα'; linarith) hD hc i ?_ t ht s hs hsi
  intro j hj
  have h1 : (0.794 : ℝ) ≤ 1 - α := by norm_num at hα' ⊢; linarith
  have : (0.794 : ℝ) ^ j ≤ (1 - α) ^ j := pow_le_pow_left₀ (by norm_num) h1 j
  have : j ≤ 3 := by omega
  interval_cases j <;> norm_num at this ⊢ <;> linarith

/-! ### Lemma 3 and Corollary 1 -/

/-- Lemma 3 of [AKSW20]: for an interval `[t₁, t₂]` with `0 ≤ t₁ ≤ t₂ ≤ t₁ + 3D`, where `S` is the
set of nodes present at `t₁`, at least `Z · |S|` of the nodes in `S` are active at `t₂`, where
`Z = (1 - α)^3 - Δ (1 + α)^3`. -/
theorem lemma3 {α Δ D : ℝ} (hα : 0 < α) (hα' : α < 0.206) (hΔ : 0 ≤ Δ) (hD : 0 < D)
    (hc : E.ChurnAssumption α D) (hf : E.FailureFraction Δ) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₁ + 3 * D) :
    Z α Δ * (E.present t₁).ncard ≤ ((E.present t₁ ∩ E.active t₂).ncard : ℝ) := by
  set S := E.present t₁
  have hsub : S ⊆ (S ∩ E.active t₂) ∪ (E.leavesIn (Ioc t₁ t₂) ∪ E.crashed t₂) := by
    intro p hp
    by_cases hA : p ∈ E.active t₂
    · exact Or.inl ⟨hp, hA⟩
    · right
      by_cases hL : E.LeftBy p t₂
      · obtain ⟨l, hl, hlt⟩ := hL
        refine Or.inl ⟨l, hl, ?_, hlt⟩
        by_contra h
        exact hp.2 ⟨l, hl, le_of_not_gt h⟩
      · refine Or.inr ?_
        by_contra hC
        exact hA ⟨⟨hp.1.trans h12, hL⟩, hC⟩
  have hcard := (Set.ncard_le_ncard hsub ((((E.present_finite _).subset inter_subset_left).union
    ((E.leavesIn_Ioc_finite _ _).union (E.crashed_finite _))))).trans
    ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_union_le _ _) _))
  have hcard' : (S.ncard : ℝ) ≤ (S ∩ E.active t₂).ncard +
      ((E.leavesIn (Ioc t₁ t₂)).ncard + (E.crashed t₂).ncard) := by exact_mod_cast hcard
  -- leaves
  have hlv := E.lemma2_four hα hα' hD hc (i := 3) (by norm_num) ht₁ (s := t₂ - t₁) (by linarith)
    (by push_cast; linarith)
  rw [show t₁ + (t₂ - t₁) = t₂ by ring] at hlv
  -- crashes
  have hN := E.N_le hα.le hD hc 3 ht₁ (s := t₂ - t₁) (by linarith) (by push_cast; linarith)
  rw [show t₁ + (t₂ - t₁) = t₂ by ring] at hN
  have hcr := hf t₂ (by linarith)
  have hcr' : ((E.crashed t₂).ncard : ℝ) ≤ Δ * ((1 + α) ^ 3 * E.N t₁) :=
    hcr.trans (mul_le_mul_of_nonneg_left hN hΔ)
  have hNS : (E.N t₁ : ℝ) = S.ncard := rfl
  unfold Z
  rw [hNS] at hlv hcr'
  nlinarith

/-- A node that is present at `t₁` and active at `t₂ ≥ t₁` is active throughout `[t₁, t₂]`. -/
theorem active_throughout {p : Node} {t₁ t₂ : ℝ} (hp1 : p ∈ E.present t₁)
    (hp2 : p ∈ E.active t₂) : ∀ τ ∈ Icc t₁ t₂, p ∈ E.active τ := by
  rintro τ ⟨h1, h2⟩
  refine ⟨⟨hp1.1.trans h1, fun ⟨l, hl, hlτ⟩ => hp2.1.2 ⟨l, hl, hlτ.trans h2⟩⟩,
    fun ⟨c, hc, hcτ⟩ => hp2.2 ⟨c, hc, hcτ.trans h2⟩⟩

/-- Corollary 1 of [AKSW20] under the weakest arithmetic hypothesis: if `Z > 0` and
`Nmin ≥ 1`, then for every `t ≥ 0` some node is active throughout `[max(0, t - 2D), t + D]`.
(Constraint (A) is not needed.) -/
theorem corollary1_of_Z_pos {α Δ D : ℝ} {Nmin : ℕ} (hα : 0 < α) (hα' : α < 0.206) (hΔ : 0 ≤ Δ)
    (hD : 0 < D) (hc : E.ChurnAssumption α D) (hm : E.MinimumSystemSize Nmin)
    (hf : E.FailureFraction Δ) (hZ : 0 < Z α Δ) (hN : 1 ≤ Nmin) {t : ℝ} (ht : 0 ≤ t) :
    ∃ p, ∀ τ ∈ Icc (max 0 (t - 2 * D)) (t + D), p ∈ E.active τ := by
  set t₁ := max 0 (t - 2 * D)
  have ht₁ : 0 ≤ t₁ := le_max_left _ _
  have h12 : t₁ ≤ t + D := max_le (by linarith) (by linarith)
  have h23 : t + D ≤ t₁ + 3 * D := by have := le_max_right 0 (t - 2 * D); linarith
  have h3 := E.lemma3 hα hα' hΔ hD hc hf ht₁ h12 h23
  have hNt : (1 : ℝ) ≤ (E.present t₁).ncard := by
    have := hm t₁ ht₁
    exact_mod_cast hN.trans this
  have hpos : (0 : ℝ) < ((E.present t₁ ∩ E.active (t + D)).ncard : ℝ) := by nlinarith
  have hne : (E.present t₁ ∩ E.active (t + D)).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    exact_mod_cast hpos.ne'
  obtain ⟨p, hp1, hp2⟩ := hne
  exact ⟨p, E.active_throughout hp1 hp2⟩

/-- Corollary 1 of [AKSW20]: under Constraints (A) (in the cleared form `ConstraintA'`, see
`Constraints.lean`) and (B), for every `t > 0`, at least one node is active throughout the
interval `[max(0, t - 2D), t + D]`. -/
theorem corollary1 {α Δ γ D : ℝ} {Nmin : ℕ} (hα : 0 < α) (hα' : α < 0.206) (hΔ : 0 ≤ Δ)
    (hγ : 0 < γ) (hD : 0 < D) (hc : E.ChurnAssumption α D) (hm : E.MinimumSystemSize Nmin)
    (hf : E.FailureFraction Δ) (hA : ConstraintA' α Δ γ Nmin) (hB : ConstraintB α Δ γ)
    {t : ℝ} (ht : 0 < t) :
    ∃ p, ∀ τ ∈ Icc (max 0 (t - 2 * D)) (t + D), p ∈ E.active τ := by
  have hZN := hA.one_le_Z_mul hα.le hΔ hγ hB
  have hZ := Z_pos_of_B hα.le hγ hB
  have hN : 1 ≤ Nmin := by
    by_contra h
    push Not at h
    have : Nmin = 0 := by omega
    subst this
    simp at hZN
    linarith
  exact E.corollary1_of_Z_pos hα hα' hΔ hD hc hm hf hZ hN ht.le

/-! ### Non-vacuity -/

/-- A static execution: two initial members, no churn, no crashes. -/
def static2 : ChurnExecution (Fin 2) where
  enter _ := 0
  leave _ := none
  crash _ := none
  enter_nonneg _ := le_rfl
  enter_le_leave _ _ h := by simp at h
  enter_le_crash _ _ h := by simp at h
  leave_or_crash _ := Or.inl rfl
  finite_entered _ := Set.toFinite _
  S0_nonempty := ⟨0, rfl⟩

/-- The assumptions of Lemmas 1–3 and Corollary 1 are satisfiable (here with the parameters
`α = 1/1000`, `Δ = 0.21`, `γ = β = 0.78`, `Nmin = 2` of `example_alpha_small`). -/
theorem static2_assumptions (D : ℝ) :
    static2.ChurnAssumption (1 / 1000) D ∧ static2.MinimumSystemSize 2 ∧
      static2.FailureFraction 0.21 ∧ AllConstraints (1 / 1000) 0.21 0.78 0.78 2 := by
  have hN : ∀ t ≥ (0 : ℝ), static2.N t = 2 := by
    intro t ht
    have : static2.present t = Set.univ := by
      ext p
      simp [present, static2, LeftBy, ht]
    simp [N, this]
  refine ⟨?_, ?_, ?_, example_alpha_small 2 le_rfl⟩
  · intro t ht
    have h1 : static2.entersIn (Icc t (t + D)) = ∅ := by
      ext p; simp [entersIn, static2]; intro h; linarith
    have h2 : static2.leavesIn (Icc t (t + D)) = ∅ := by
      ext p; simp [leavesIn, static2]
    rw [h1, h2, hN t ht.le]
    norm_num
  · intro t ht
    rw [hN t ht]
  · intro t ht
    have : static2.crashed t = ∅ := by ext p; simp [crashed, CrashedBy, static2]
    rw [this, hN t ht]
    norm_num

end ChurnExecution

end Podc.StoreCollectChurn
