import Papers.PODC2025.AmnesiacFloodingFaults.Model

/-!
# Balance of a configuration along a closed walk

A closed walk of length `L ≥ 1` is a map `w : ZMod L → V` with `w k ~ w (k + 1)`. A message
`(w k, w (k+1))` travels *clockwise* at position `k`, a message `(w k, w (k-1))` travels
*anticlockwise* at position `k`; in both cases its *head* (sender) sits at position `k`.

Pulling a configuration back along the walk gives a configuration on the cycle graph `C_L`
(for a faux-even cycle this is the paper's even cycle representation `S^{2,H}` on `H²`,
Definition 5.3), and one round of amnesiac flooding on `G` becomes one round on `C_L` in which
some nodes are activated from outside the cycle (`ind_cw_step_sub`). In particular the per-node
conservation law `[cw' k] - [ccw' k] = [cw (k-1)] - [ccw (k+1)]` holds.

* `classSum S w k₀` — the number of clockwise minus anticlockwise messages whose heads are at
  positions `k₀ + 2i`, i.e. in the parity class of `k₀` when `L` is even, and anywhere when `L` is
  odd;
* `BalancedOn S w` — all class sums vanish. For a cycle this is exactly the paper's condition
  (Definition 5.4): equally many messages in each direction on an odd cycle, and, on an even
  cycle, for every message `m` equally many messages in each direction among those whose heads are
  at even distance from the head of `m`.

Main results:
* `balancedOn_step_iff` — balance along any closed walk is invariant under `A_{I,G}`
  (Lemma A.1);
* `not_balancedOn_of_front` — the key new lemma: if a message travels once around the closed walk
  (a clockwise "front" at position `k₀ + t` at every time `t ≤ L`), the configuration was
  imbalanced on the walk. This replaces the paper's Lemmas A.3–A.6 and the word combinatorics of
  Appendix A.
-/

namespace AmnesiacFloodingFaults

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {L : ℕ} {w : ZMod L → V}

/-- `w : ZMod L → V` is a closed walk of length `L` in `G`. -/
def IsClosedWalk (G : SimpleGraph V) (w : ZMod L → V) : Prop := ∀ k, G.Adj (w k) (w (k + 1))

/-- A clockwise message at position `k` of the closed walk `w`. -/
def cw (S : Config V) (w : ZMod L → V) (k : ZMod L) : Prop := (w k, w (k + 1)) ∈ S

/-- An anticlockwise message at position `k` of the closed walk `w`. -/
def ccw (S : Config V) (w : ZMod L → V) (k : ZMod L) : Prop := (w k, w (k - 1)) ∈ S

open Classical in
/-- Indicator of a proposition, as an integer. -/
noncomputable def ind (P : Prop) : ℤ := if P then 1 else 0

lemma ind_of {P : Prop} (h : P) : ind P = 1 := by classical simp [ind, h]

lemma ind_of_not {P : Prop} (h : ¬ P) : ind P = 0 := by classical simp [ind, h]

lemma ind_not (P : Prop) : ind (¬ P) = 1 - ind P := by
  by_cases h : P
  · rw [ind_of h, ind_of_not (not_not.2 h)]; norm_num
  · rw [ind_of h, ind_of_not h]; norm_num

lemma ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by rw [h]

lemma ind_nonneg (P : Prop) : 0 ≤ ind P := by
  by_cases h : P
  · rw [ind_of h]; norm_num
  · rw [ind_of_not h]

lemma ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases h : P
  · rw [ind_of h]
  · rw [ind_of_not h]; norm_num

/-- The size of a class of positions: `L / 2` for even `L`, and `L` for odd `L`. -/
def classSize (L : ℕ) : ℕ := if Even L then L / 2 else L

lemma classSize_pos [NeZero L] : 0 < classSize L := by
  have hL : L ≠ 0 := NeZero.ne L
  unfold classSize
  split_ifs with h
  · obtain ⟨r, hr⟩ := h; omega
  · omega

lemma classSize_le : classSize L ≤ L := by
  unfold classSize; split_ifs <;> omega

lemma two_mul_classSize : (2 * (classSize L : ZMod L)) = 0 := by
  unfold classSize
  split_ifs with h
  · obtain ⟨r, hr⟩ := h
    have : L / 2 = r := by omega
    rw [this]
    have : (2 * (r : ZMod L)) = ((r + r : ℕ) : ZMod L) := by push_cast; ring
    rw [this, ← hr, ZMod.natCast_self]
  · rw [ZMod.natCast_self, mul_zero]

/-- Shifting the class index by one step does not change a class sum. -/
lemma sum_class_shift (f : ZMod L → ℤ) (k₀ : ZMod L) :
    ∑ i ∈ range (classSize L), f (k₀ + 2 * ((i + 1 : ℕ) : ZMod L)) =
      ∑ i ∈ range (classSize L), f (k₀ + 2 * (i : ZMod L)) := by
  have h1 := Finset.sum_range_succ' (fun i => f (k₀ + 2 * (i : ZMod L))) (classSize L)
  have h2 := Finset.sum_range_succ (fun i => f (k₀ + 2 * (i : ZMod L))) (classSize L)
  rw [two_mul_classSize, add_zero] at h2
  simp only [Nat.cast_zero, mul_zero, add_zero] at h1
  linarith

/-- The class sum: clockwise minus anticlockwise messages with heads at positions `k₀ + 2i`. -/
noncomputable def classSum (S : Config V) (w : ZMod L → V) (k₀ : ZMod L) : ℤ :=
  ∑ i ∈ range (classSize L), (ind (cw S w (k₀ + 2 * (i : ZMod L))) -
    ind (ccw S w (k₀ + 2 * (i : ZMod L))))

/-- The configuration `S` is balanced along the closed walk `w`. -/
def BalancedOn (S : Config V) (w : ZMod L → V) : Prop := ∀ k₀, classSum S w k₀ = 0

lemma balancedOn_empty (w : ZMod L → V) : BalancedOn (∅ : Config V) w := by
  intro k₀
  simp [classSum, cw, ccw, ind_of_not]

/-- **Per-node conservation law.** After one round of `A_{I,G}`, the clockwise minus anticlockwise
messages sent from position `k` equal the clockwise minus anticlockwise messages that arrived at
position `k` along the walk. -/
lemma ind_cw_step_sub (hw : IsClosedWalk G w) (I : Set V) (S : Config V) (k : ZMod L) :
    ind (cw (step G I S) w k) - ind (ccw (step G I S) w k) =
      ind (cw S w (k - 1)) - ind (ccw S w (k + 1)) := by
  have hadj1 : G.Adj (w k) (w (k + 1)) := hw k
  have hadj2 : G.Adj (w k) (w (k - 1)) := by
    have := hw (k - 1); rw [sub_add_cancel] at this; exact this.symm
  have e1 : cw (step G I S) w k ↔ ¬ ccw S w (k + 1) ∧ (w k ∈ I ∨ Active S (w k)) := by
    simp only [cw, ccw, mem_step, add_sub_cancel_right]; tauto
  have e2 : ccw (step G I S) w k ↔ ¬ cw S w (k - 1) ∧ (w k ∈ I ∨ Active S (w k)) := by
    simp only [cw, ccw, mem_step, sub_add_cancel]; tauto
  by_cases hact : w k ∈ I ∨ Active S (w k)
  · rw [ind_congr (e1.trans (and_iff_left hact)), ind_congr (e2.trans (and_iff_left hact)),
      ind_not, ind_not]
    ring
  · have h1 : ¬ cw S w (k - 1) := fun h =>
      hact (Or.inr ⟨_, by simpa [cw, sub_add_cancel] using h⟩)
    have h2 : ¬ ccw S w (k + 1) := fun h =>
      hact (Or.inr ⟨_, by simpa [ccw, add_sub_cancel_right] using h⟩)
    rw [ind_of_not (fun h => hact (e1.1 h).2), ind_of_not (fun h => hact (e2.1 h).2),
      ind_of_not h1, ind_of_not h2]

/-- One round of `A_{I,G}` shifts the class sums by one position (Lemma A.1). -/
lemma classSum_step (hw : IsClosedWalk G w) (I : Set V) (S : Config V) (k₀ : ZMod L) :
    classSum (step G I S) w (k₀ + 1) = classSum S w k₀ := by
  unfold classSum
  have : ∀ i : ℕ, ind (cw (step G I S) w (k₀ + 1 + 2 * (i : ZMod L))) -
      ind (ccw (step G I S) w (k₀ + 1 + 2 * (i : ZMod L))) =
      ind (cw S w (k₀ + 2 * (i : ZMod L))) -
        ind (ccw S w (k₀ + 2 * ((i + 1 : ℕ) : ZMod L))) := by
    intro i
    rw [ind_cw_step_sub hw]
    congr 3 <;> push_cast <;> ring
  simp only [this, Finset.sum_sub_distrib]
  rw [sum_class_shift (fun k => ind (ccw S w k))]

/-- **Lemma A.1.** Balance along a closed walk is preserved and reflected by `A_{I,G}`. -/
theorem balancedOn_step_iff (hw : IsClosedWalk G w) (I : Set V) (S : Config V) :
    BalancedOn (step G I S) w ↔ BalancedOn S w := by
  constructor
  · intro h k₀; rw [← classSum_step hw I S k₀]; exact h _
  · intro h k₀; rw [← sub_add_cancel k₀ 1, classSum_step hw I S]; exact h _

lemma balancedOn_iterate_iff (hw : IsClosedWalk G w) (S : Config V) (k : ℕ) :
    BalancedOn ((af G)^[k] S) w ↔ BalancedOn S w := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', balancedOn_step_iff hw, ih]

lemma balancedOn_runFrom_iff (hw : IsClosedWalk G w) (Is : List (Set V)) (S : Config V) :
    BalancedOn (runFrom G Is S) w ↔ BalancedOn S w := by
  induction Is generalizing S with
  | nil => rfl
  | cons I Is ih => rw [runFrom, ih, balancedOn_step_iff hw]

/-- The reversed configuration is balanced exactly when the configuration is (Lemma 5.4). -/
theorem balancedOn_rev_iff (S : Config V) (w : ZMod L → V) :
    BalancedOn (rev S) w ↔ BalancedOn S w := by
  have key : ∀ k₀, classSum (rev S) w (k₀ + 1) = - classSum S w k₀ := by
    intro k₀
    unfold classSum
    have h1 : ∀ i : ℕ, cw (rev S) w (k₀ + 1 + 2 * (i : ZMod L)) ↔
        ccw S w (k₀ + 2 * ((i + 1 : ℕ) : ZMod L)) := by
      intro i
      simp only [cw, ccw, mem_rev]
      constructor <;> intro h <;> convert h using 3 <;> push_cast <;> ring
    have h2 : ∀ i : ℕ, ccw (rev S) w (k₀ + 1 + 2 * (i : ZMod L)) ↔
        cw S w (k₀ + 2 * (i : ZMod L)) := by
      intro i
      simp only [cw, ccw, mem_rev]
      constructor <;> intro h <;> convert h using 3 <;> ring
    simp only [ind_congr (h1 _), ind_congr (h2 _), Finset.sum_sub_distrib]
    rw [sum_class_shift (fun k => ind (ccw S w k))]
    ring
  constructor
  · intro h k₀; have := key k₀; rw [h] at this; linarith
  · intro h k₀; rw [← sub_add_cancel k₀ 1, key, h]; simp

/-! ### A message cannot travel once around a closed walk in a balanced configuration -/

section Front

variable [NeZero L] (hw : IsClosedWalk G w) (S : ℕ → Config V) (I : ℕ → Set V)
  (hS : ∀ t, S (t + 1) = step G (I t) (S t)) (k₀ : ZMod L)

/-- Partial class sums ahead of the front `k₀ + t` at time `t`. -/
noncomputable def frontSum (t j : ℕ) : ℤ :=
  ∑ i ∈ range j, (ind (cw (S t) w (k₀ + t + 2 * ((i + 1 : ℕ) : ZMod L))) -
    ind (ccw (S t) w (k₀ + t + 2 * ((i + 1 : ℕ) : ZMod L))))

omit [NeZero L] in
include hw hS in
lemma frontSum_succ_time {t : ℕ} (h : ¬ ccw (S t) w (k₀ + t + 2)) (j : ℕ) :
    frontSum (w := w) S k₀ (t + 1) j = frontSum (w := w) S k₀ t (j + 1) -
      ind (cw (S t) w (k₀ + t + 2 * ((j + 1 : ℕ) : ZMod L))) := by
  unfold frontSum
  rw [Finset.sum_range_succ]
  have hc : ∀ i : ℕ, ind (cw (S (t + 1)) w (k₀ + ((t + 1 : ℕ) : ZMod L) +
      2 * ((i + 1 : ℕ) : ZMod L))) - ind (ccw (S (t + 1)) w (k₀ + ((t + 1 : ℕ) : ZMod L) +
      2 * ((i + 1 : ℕ) : ZMod L))) =
      ind (cw (S t) w (k₀ + t + 2 * ((i + 1 : ℕ) : ZMod L))) -
        ind (ccw (S t) w (k₀ + t + 2 * ((i + 1 + 1 : ℕ) : ZMod L))) := by
    intro i
    rw [hS, ind_cw_step_sub hw]
    congr 3 <;> push_cast <;> ring
  simp only [hc, Finset.sum_sub_distrib]
  have tele := Finset.sum_range_sub' (fun i => ind (ccw (S t) w (k₀ + t + 2 * ((i + 1 : ℕ) :
    ZMod L)))) j
  have h0 : ind (ccw (S t) w (k₀ + t + 2 * ((0 + 1 : ℕ) : ZMod L))) = 0 := by
    apply ind_of_not; convert h using 2; push_cast; ring
  rw [h0, Finset.sum_sub_distrib] at tele
  linarith

omit [NeZero L] in
include hw hS in
/-- A negative partial sum ahead of the front kills the front within `j` rounds. -/
lemma front_dies (j : ℕ) : ∀ t, frontSum (w := w) S k₀ t j ≤ -1 →
    (∀ s, t ≤ s → s < t + j → ¬ ccw (S s) w (k₀ + s + 2)) → False := by
  induction j with
  | zero => intro t h _; simp [frontSum] at h
  | succ j ih =>
    intro t h hs
    have hst := hs t le_rfl (by omega)
    apply ih (t + 1)
    · rw [frontSum_succ_time hw S I hS k₀ hst]
      linarith [ind_nonneg (cw (S t) w (k₀ + t + 2 * ((j + 1 : ℕ) : ZMod L)))]
    · intro s h1 h2; exact hs s (by omega) (by omega)

include hw hS in
/-- **Key lemma (replaces Lemmas A.3–A.6).** If a clockwise message front is present at position
`k₀ + t` at every time `t ≤ classSize L` (in particular if a message travels once around the closed
walk), the initial configuration is imbalanced on the walk. -/
theorem not_balancedOn_of_front (hfront : ∀ t ≤ classSize L, cw (S t) w (k₀ + t)) :
    ¬ BalancedOn (S 0) w := by
  intro hbal
  -- no anticlockwise message meets the front
  have hno : ∀ s, s < classSize L → ¬ ccw (S s) w (k₀ + s + 2) := by
    intro s hs hc
    have := hfront (s + 1) (by omega)
    rw [hS] at this
    simp only [cw, mem_step] at this
    apply this.2.1
    simp only [ccw] at hc
    convert hc using 3 <;> push_cast <;> ring
  have hbal1 : BalancedOn (S 1) w := by rw [hS]; exact (balancedOn_step_iff hw _ _).2 hbal
  have hM := classSize_pos (L := L)
  have hsplit := hbal1 (k₀ + 1)
  unfold classSum at hsplit
  obtain ⟨M, hMeq⟩ : ∃ M, classSize L = M + 1 := ⟨classSize L - 1, by omega⟩
  rw [hMeq, Finset.sum_range_succ'] at hsplit
  have hcw1 : cw (S 1) w (k₀ + 1) := by simpa using hfront 1 (by omega)
  have hccw1 : ¬ ccw (S 1) w (k₀ + 1) := by
    intro h
    have h0 := hfront 0 (Nat.zero_le _)
    rw [hS] at h
    apply h.2.1
    simpa [cw] using h0
  rw [Nat.cast_zero, mul_zero, add_zero, ind_of hcw1, ind_of_not hccw1] at hsplit
  have hP : frontSum (w := w) S k₀ 1 M ≤ -1 := by
    unfold frontSum
    have : ∀ i ∈ range M, ind (cw (S 1) w (k₀ + 1 + 2 * ((i + 1 : ℕ) : ZMod L))) -
        ind (ccw (S 1) w (k₀ + 1 + 2 * ((i + 1 : ℕ) : ZMod L))) =
        ind (cw (S 1) w (k₀ + ((1 : ℕ) : ZMod L) + 2 * ((i + 1 : ℕ) : ZMod L))) -
        ind (ccw (S 1) w (k₀ + ((1 : ℕ) : ZMod L) + 2 * ((i + 1 : ℕ) : ZMod L))) := by
      intro i _; push_cast; ring_nf
    rw [← Finset.sum_congr rfl this]
    linarith
  exact front_dies hw S I hS k₀ M 1 hP (fun s h1 h2 => hno s (by omega))

end Front

end AmnesiacFloodingFaults
