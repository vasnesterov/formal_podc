import Mathlib

/-!
# Rendezvous in the oriented ring with simultaneous start (Section 3 of Miller–Pelc)

The lower bounds of [Miller, Pelc, *Time versus cost tradeoffs for deterministic rendezvous in
networks*, PODC 2014] are proved in the oriented ring of known size `n` (exploration bound
`E = n - 1`), with simultaneous start. In this setting an agent learns nothing before meeting
(every node has degree 2, and its entry port is determined by its own last move), so a
deterministic algorithm is the same as a *behaviour vector* per label: `V x j ∈ {-1, 0, 1}` is the
move of agent `x` in round `j + 1` of its solo execution (`1` = clockwise = port 0, `-1` =
counterclockwise, `0` = idle). The paper works with behaviour vectors throughout Section 3.

Nodes are `ZMod n`, numbered clockwise (for the analysis only).
* `disp v t` : displacement after `t` rounds; `moves v t` : number of edge traversals.
* `Meets n V x px y py t` : in execution `α(x, px, y, py)` both agents are at the same node at
  the end of round `t` (they follow their solo behaviour until they meet).
* `meetTime` : the first such round `|α(x, px, y, py)|`; `execCost` : the cost of the execution
  (edge traversals of both agents before rendezvous).
* `IsRendezvous`, `TimeLE`, `CostLE` : correctness and worst-case time / cost bounds of an
  algorithm, over all pairs of distinct labels and distinct starting nodes.
-/

namespace Podc.RendezvousTimeCost

open Finset

/-- The behaviour vectors of a rendezvous algorithm for labels `Fin L` in the oriented ring with
simultaneous start. -/
abbrev Behaviour (L : ℕ) := Fin L → ℕ → SignType

/-- Clockwise displacement after the first `t` rounds. -/
def disp (v : ℕ → SignType) (t : ℕ) : ℤ := ∑ j ∈ range t, (v j : ℤ)

/-- Number of edge traversals in the first `t` rounds. -/
def moves (v : ℕ → SignType) (t : ℕ) : ℕ := ∑ j ∈ range t, ((v j : ℤ)).natAbs

/-- In execution `α(x, px, y, py)` the agents are at the same node at the end of round `t`. -/
def Meets (n : ℕ) {L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L) (py : ZMod n)
    (t : ℕ) : Prop :=
  px + (disp (V x) t : ZMod n) = py + (disp (V y) t : ZMod n)

instance (n : ℕ) {L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L) (py : ZMod n)
    (t : ℕ) : Decidable (Meets n V x px y py t) := by
  unfold Meets; infer_instance

/-- The round `|α(x, px, y, py)|` in which the agents first meet (`0` if they never meet). -/
noncomputable def meetTime (n : ℕ) {L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L)
    (py : ZMod n) : ℕ :=
  sInf {t | Meets n V x px y py t}

/-- The cost of execution `α(x, px, y, py)`: edge traversals by both agents before rendezvous. -/
noncomputable def execCost (n : ℕ) {L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L)
    (py : ZMod n) : ℕ :=
  moves (V x) (meetTime n V x px y py) + moves (V y) (meetTime n V x px y py)

/-- The algorithm achieves rendezvous for all distinct labels and distinct starting nodes. -/
def IsRendezvous (n : ℕ) {L : ℕ} (V : Behaviour L) : Prop :=
  ∀ x y : Fin L, x ≠ y → ∀ px py : ZMod n, px ≠ py → ∃ t, Meets n V x px y py t

/-- Worst-case rendezvous time at most `T`. -/
def TimeLE (n : ℕ) {L : ℕ} (V : Behaviour L) (T : ℕ) : Prop :=
  ∀ x y : Fin L, x ≠ y → ∀ px py : ZMod n, px ≠ py → meetTime n V x px y py ≤ T

/-- Worst-case rendezvous cost at most `C`. -/
def CostLE (n : ℕ) {L : ℕ} (V : Behaviour L) (C : ℕ) : Prop :=
  ∀ x y : Fin L, x ≠ y → ∀ px py : ZMod n, px ≠ py → execCost n V x px y py ≤ C

/-! ### Basic lemmas -/

@[simp] lemma disp_zero (v : ℕ → SignType) : disp v 0 = 0 := by simp [disp]

lemma disp_succ (v : ℕ → SignType) (t : ℕ) : disp v (t + 1) = disp v t + (v t : ℤ) := by
  simp [disp, sum_range_succ]

@[simp] lemma moves_zero (v : ℕ → SignType) : moves v 0 = 0 := by simp [moves]

lemma moves_succ (v : ℕ → SignType) (t : ℕ) :
    moves v (t + 1) = moves v t + ((v t : ℤ)).natAbs := by
  simp [moves, sum_range_succ]

lemma natAbs_sign_le_one (s : SignType) : ((s : ℤ)).natAbs ≤ 1 := by
  cases s <;> simp

lemma abs_sign_le_one (s : SignType) : |(s : ℤ)| ≤ 1 := by
  cases s <;> simp

lemma moves_mono (v : ℕ → SignType) {s t : ℕ} (h : s ≤ t) : moves v s ≤ moves v t := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [moves_succ]; omega

lemma moves_le (v : ℕ → SignType) (t : ℕ) : moves v t ≤ t := by
  induction t with
  | zero => simp
  | succ t ih => rw [moves_succ]; have := natAbs_sign_le_one (v t); omega

/-- `moves` over a window: `moves v (s + k) - moves v s ≤ k`. -/
lemma moves_add_le (v : ℕ → SignType) (s k : ℕ) : moves v (s + k) ≤ moves v s + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, moves_succ]; have := natAbs_sign_le_one (v (s + k)); omega

/-- The displacement changes over a window by at most the number of moves in the window. -/
lemma abs_disp_sub_le_moves (v : ℕ → SignType) {s t : ℕ} (h : s ≤ t) :
    |disp v t - disp v s| ≤ (moves v t : ℤ) - moves v s := by
  induction h with
  | refl => simp
  | step hle ih =>
    rename_i m
    rw [disp_succ, moves_succ]
    have := abs_add_le (disp v m - disp v s) (v m : ℤ)
    have h2 : |((v m : ℤ))| = (((v m : ℤ)).natAbs : ℤ) := Int.abs_eq_natAbs _
    push_cast
    calc |disp v m + (v m : ℤ) - disp v s| = |disp v m - disp v s + (v m : ℤ)| := by ring_nf
      _ ≤ _ := this
      _ ≤ _ := by rw [h2]; linarith

lemma abs_disp_le_moves (v : ℕ → SignType) (t : ℕ) : |disp v t| ≤ moves v t := by
  simpa using abs_disp_sub_le_moves v (Nat.zero_le t)

/-- The displacement changes by at most one per round. -/
lemma abs_disp_sub_le (v : ℕ → SignType) {s t : ℕ} (h : s ≤ t) :
    |disp v t - disp v s| ≤ (t : ℤ) - s := by
  have h1 := abs_disp_sub_le_moves v h
  have h2 := moves_add_le v s (t - s)
  rw [Nat.add_sub_cancel' h] at h2
  have : (moves v t : ℤ) ≤ moves v s + ((t - s : ℕ) : ℤ) := by exact_mod_cast h2
  push_cast [h] at this
  linarith

lemma meets_comm {n L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L)
    (py : ZMod n) (t : ℕ) : Meets n V x px y py t ↔ Meets n V y py x px t := eq_comm

lemma meetTime_comm {n L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L)
    (py : ZMod n) : meetTime n V x px y py = meetTime n V y py x px := by
  simp only [meetTime, meets_comm V x px y py]

lemma execCost_comm {n L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L)
    (py : ZMod n) : execCost n V x px y py = execCost n V y py x px := by
  simp only [execCost, meetTime_comm V x px y py, add_comm]

lemma meets_meetTime {n L : ℕ} {V : Behaviour L} {x : Fin L} {px : ZMod n} {y : Fin L}
    {py : ZMod n} (h : ∃ t, Meets n V x px y py t) : Meets n V x px y py (meetTime n V x px y py) :=
  Nat.sInf_mem h

lemma meetTime_le {n L : ℕ} {V : Behaviour L} {x : Fin L} {px : ZMod n} {y : Fin L}
    {py : ZMod n} {t : ℕ} (h : Meets n V x px y py t) : meetTime n V x px y py ≤ t :=
  Nat.sInf_le h

lemma not_meets_of_lt {n L : ℕ} {V : Behaviour L} {x : Fin L} {px : ZMod n} {y : Fin L}
    {py : ZMod n} {t : ℕ} (h : t < meetTime n V x px y py) : ¬ Meets n V x px y py t :=
  fun hm => absurd (meetTime_le hm) (not_le.mpr h)

/-- If the agents never coincide in rounds `≤ T`, then the meeting is after round `T`. -/
lemma lt_meetTime_of_forall {n L : ℕ} {V : Behaviour L} {x : Fin L} {px : ZMod n} {y : Fin L}
    {py : ZMod n} {T : ℕ} (hex : ∃ t, Meets n V x px y py t)
    (h : ∀ t ≤ T, ¬ Meets n V x px y py t) : T < meetTime n V x px y py := by
  by_contra hle
  exact h _ (not_lt.mp hle) (meets_meetTime hex)

/-! ### Trimming -/

/-- `m_x` of procedure `Trim(A)`: the latest meeting round over all executions
`α(x, px, y, py)` with `y ≠ x`, `px ≠ py`. -/
noncomputable def mx (n : ℕ) [NeZero n] {L : ℕ} (V : Behaviour L) (x : Fin L) : ℕ :=
  ((univ : Finset (Fin L × ZMod n × ZMod n)).filter
      (fun q => q.1 ≠ x ∧ q.2.1 ≠ q.2.2)).sup
    (fun q => meetTime n V x q.2.1 q.1 q.2.2)

lemma meetTime_le_mx {n : ℕ} [NeZero n] {L : ℕ} (V : Behaviour L) {x y : Fin L} (hxy : y ≠ x)
    {px py : ZMod n} (hp : px ≠ py) : meetTime n V x px y py ≤ mx n V x := by
  unfold mx
  exact le_sup (f := fun q : Fin L × ZMod n × ZMod n => meetTime n V x q.2.1 q.1 q.2.2)
    (b := (y, px, py)) (mem_filter.2 ⟨mem_univ _, hxy, hp⟩)

lemma exists_meetTime_eq_mx {n : ℕ} [NeZero n] {L : ℕ} (V : Behaviour L) (x : Fin L)
    (hn : 2 ≤ n) (hL : 2 ≤ L) :
    ∃ y px py, y ≠ x ∧ px ≠ py ∧ meetTime n V x px y py = mx n V x := by
  have hne : ((univ : Finset (Fin L × ZMod n × ZMod n)).filter
      (fun q => q.1 ≠ x ∧ q.2.1 ≠ q.2.2)).Nonempty := by
    obtain ⟨y, hy⟩ : ∃ y : Fin L, y ≠ x := by
      by_cases hx : x.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    have h01 : (0 : ZMod n) ≠ 1 := by
      have : Fact (1 < n) := ⟨hn⟩
      exact zero_ne_one
    exact ⟨(y, 0, 1), by simp [hy, h01]⟩
  obtain ⟨q, hq, hqe⟩ := exists_mem_eq_sup _ hne
    (fun q : Fin L × ZMod n × ZMod n => meetTime n V x q.2.1 q.1 q.2.2)
  simp only [mem_filter, mem_univ, true_and] at hq
  exact ⟨q.1, q.2.1, q.2.2, hq.1, hq.2, by unfold mx; rw [hqe]⟩

/-- Displacement of the trimmed behaviour vector: the solo displacement frozen after round
`m_x`. Before `m_x` it is the true displacement. -/
noncomputable def tdisp (n : ℕ) [NeZero n] {L : ℕ} (V : Behaviour L) (x : Fin L) (t : ℕ) : ℤ :=
  disp (V x) (min t (mx n V x))

/-! ### Mirror symmetry -/

/-- The mirrored algorithm (clockwise and counterclockwise exchanged). -/
def mirror {L : ℕ} (V : Behaviour L) : Behaviour L := fun x j => - V x j

@[simp] lemma disp_mirror {L : ℕ} (V : Behaviour L) (x : Fin L) (t : ℕ) :
    disp (mirror V x) t = - disp (V x) t := by
  simp [disp, mirror, sum_neg_distrib]

@[simp] lemma moves_mirror {L : ℕ} (V : Behaviour L) (x : Fin L) (t : ℕ) :
    moves (mirror V x) t = moves (V x) t := by
  simp [moves, mirror]

lemma meets_mirror {n L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L)
    (py : ZMod n) (t : ℕ) : Meets n (mirror V) x px y py t ↔ Meets n V x (-px) y (-py) t := by
  simp only [Meets, disp_mirror, Int.cast_neg]
  constructor <;> intro h <;> linear_combination -h

lemma meetTime_mirror {n L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L)
    (py : ZMod n) : meetTime n (mirror V) x px y py = meetTime n V x (-px) y (-py) := by
  simp only [meetTime, meets_mirror]

lemma execCost_mirror {n L : ℕ} (V : Behaviour L) (x : Fin L) (px : ZMod n) (y : Fin L)
    (py : ZMod n) : execCost n (mirror V) x px y py = execCost n V x (-px) y (-py) := by
  simp only [execCost, meetTime_mirror, moves_mirror]

lemma IsRendezvous.mirror {n L : ℕ} {V : Behaviour L} (h : IsRendezvous n V) :
    IsRendezvous n (mirror V) := by
  intro x y hxy px py hp
  obtain ⟨t, ht⟩ := h x y hxy (-px) (-py) (by simpa using hp)
  exact ⟨t, (meets_mirror V x px y py t).2 ht⟩

lemma CostLE.mirror {n L : ℕ} {V : Behaviour L} {C : ℕ} (h : CostLE n V C) :
    CostLE n (mirror V) C := by
  intro x y hxy px py hp
  rw [execCost_mirror]
  exact h x y hxy _ _ (by simpa using hp)

end Podc.RendezvousTimeCost
