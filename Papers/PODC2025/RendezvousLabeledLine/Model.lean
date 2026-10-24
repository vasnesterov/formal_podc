import Mathlib

/-!
# Rendezvous on the labelled line: trajectories, the CarefulWalk reduction (Theorem 3.1)

Bourreau, Narayanan, Nolin, *Optimal Deterministic Rendezvous in Labeled Lines*, PODC 2025
(arXiv:2505.04564v2).

An agent that is woken up in round `τ` and then follows the trajectory `b : ℕ → V` (position after
`t` rounds of its own clock) is at `delayed τ b t = b (t - τ)` in global round `t` (truncated
subtraction: it sits at its start `b 0` while asleep).  Two agents *meet* in round `t` if they are
at the same node; *meet or cross* additionally counts a simultaneous traversal of one edge in
opposite directions in rounds `t - 1 → t`.

`careTraj lab a` is the trajectory of `care(A)` (Algorithm 1, CarefulWalk) when `A` follows `a`:
every round of `A` becomes four rounds; a stay is stretched, a move `p → q` becomes
"wait, cross, (wait | back and forth), (wait | cross)" according to whether the label increases.

`care_meet` is the trajectory-level content of Theorem 3.1: for **any** type of nodes with injective
labels (the paper's "labelled graph"), a meet-or-cross of the `A`-trajectories with delay
`⌈τ/4⌉` within `T` rounds yields a meeting at a node of the `care`-trajectories with delay `τ`
within `4T` rounds.
-/

namespace Podc.RendezvousLabeledLine

variable {V : Type*}

/-- Global position in round `t` of an agent woken up in round `τ` whose own trajectory is `b`. -/
def delayed (τ : ℕ) (b : ℕ → V) (t : ℕ) : V := b (t - τ)

/-- Rendezvous with simultaneous edge-crossing detection: same node in round `t`, or the two
agents swapped their positions in rounds `t - 1 → t`. -/
def MeetOrCross (x y : ℕ → V) (t : ℕ) : Prop :=
  x t = y t ∨ (0 < t ∧ x t = y (t - 1) ∧ y t = x (t - 1))

/-- Trajectory of `care(A)` (Algorithm 1, CarefulWalk, applied to every round of `A`). -/
def careTraj (lab : V → ℕ) (a : ℕ → V) (t : ℕ) : V :=
  if t % 4 ≤ 1 then a (t / 4)
  else if t % 4 = 2 then a (t / 4 + 1)
  else if lab (a (t / 4)) < lab (a (t / 4 + 1)) then a (t / 4 + 1) else a (t / 4)

lemma careTraj_four_mul (lab : V → ℕ) (a : ℕ → V) (k : ℕ) : careTraj lab a (4 * k) = a k := by
  simp [careTraj]

lemma careTraj_four_mul_add_one (lab : V → ℕ) (a : ℕ → V) (k : ℕ) :
    careTraj lab a (4 * k + 1) = a k := by
  simp only [careTraj]; rw [ite_eq_left (by omega)]; congr 1; omega

lemma careTraj_four_mul_add_two (lab : V → ℕ) (a : ℕ → V) (k : ℕ) :
    careTraj lab a (4 * k + 2) = a (k + 1) := by
  simp only [careTraj]; rw [ite_eq_right (by omega), ite_eq_left (by omega)]; congr 2; omega

lemma careTraj_four_mul_add_three (lab : V → ℕ) (a : ℕ → V) (k : ℕ) :
    careTraj lab a (4 * k + 3) =
      if lab (a k) < lab (a (k + 1)) then a (k + 1) else a k := by
  simp only [careTraj]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have : (4 * k + 3) / 4 = k := by omega
  simp [this]

/-- `care` commutes with relabelling the nodes along a map `f`. -/
lemma careTraj_comp {W : Type*} (f : V → W) (lab : W → ℕ) (a : ℕ → V) :
    careTraj lab (f ∘ a) = f ∘ careTraj (lab ∘ f) a := by
  funext t; simp only [careTraj, Function.comp]; split_ifs <;> rfl

/-- Positions of `care(A)` within the `k`-th block when the `k`-th move of `A` is a real move from
a node to a node of different label: the `Bool` records whether the label increases. -/
lemma careTraj_block (lab : V → ℕ) (a : ℕ → V) (k : ℕ) :
    careTraj lab a (4 * k) = a k ∧ careTraj lab a (4 * k + 1) = a k ∧
    careTraj lab a (4 * k + 2) = a (k + 1) ∧
    careTraj lab a (4 * k + 3) =
      (if lab (a k) < lab (a (k + 1)) then a (k + 1) else a k) ∧
    careTraj lab a (4 * k + 4) = a (k + 1) ∧ careTraj lab a (4 * k + 5) = a (k + 1) := by
  refine ⟨careTraj_four_mul .., careTraj_four_mul_add_one .., careTraj_four_mul_add_two ..,
    careTraj_four_mul_add_three .., ?_, ?_⟩
  · rw [show 4 * k + 4 = 4 * (k + 1) by ring, careTraj_four_mul]
  · rw [show 4 * k + 5 = 4 * (k + 1) + 1 by ring, careTraj_four_mul_add_one]

/-- The position of the delayed `care`-agent: with `τ = 4 τ' - r`, its round `4 i - r + j`
(`j ∈ {0, 1}`) is spent at `delayed τ' b i`. -/
private lemma delayed_care_start (lab : V → ℕ) (b : ℕ → V) (τ i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ 1) :
    delayed τ (careTraj lab b) (4 * i - (4 * ((τ + 3) / 4) - τ) + j) =
      delayed ((τ + 3) / 4) b i := by
  simp only [delayed]
  set τ' := (τ + 3) / 4 with hτ'
  have h1 : τ ≤ 4 * τ' := by omega
  have h2 : 4 * τ' ≤ τ + 3 := by omega
  by_cases hit : τ' ≤ i
  · have : 4 * i - (4 * τ' - τ) + j - τ = 4 * (i - τ') + j := by omega
    rw [this]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simp [careTraj_four_mul]
    · exact careTraj_four_mul_add_one ..
  · have : 4 * i - (4 * τ' - τ) + j - τ = 0 := by omega
    rw [this, show i - τ' = 0 by omega]
    simpa using careTraj_four_mul lab b 0

/-- **Theorem 3.1 (trajectory form).** Let node labels be injective. If the trajectories `a`, `b`
of algorithm `A` meet or cross in round `t` when the second agent is delayed by `⌈τ/4⌉`, then the
`care(A)` trajectories meet at a node in some round `s ≤ 4 t` when the second agent is delayed by
`τ`. -/
theorem care_meet {lab : V → ℕ} (hlab : Function.Injective lab) (a b : ℕ → V) (τ t : ℕ)
    (h : MeetOrCross a (delayed ((τ + 3) / 4) b) t) :
    ∃ s ≤ 4 * t, careTraj lab a s = delayed τ (careTraj lab b) s := by
  set τ' := (τ + 3) / 4 with hτ'
  have h1 : τ ≤ 4 * τ' := by omega
  have h2 : 4 * τ' ≤ τ + 3 := by omega
  set r := 4 * τ' - τ with hr
  -- Case 1: same node in round `t`.
  by_cases hmeet : a t = delayed τ' b t
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · refine ⟨0, le_refl _, ?_⟩
      simpa [delayed, careTraj_four_mul] using
        (show careTraj lab a (4 * 0) = _ from careTraj_four_mul lab a 0).trans
          (hmeet.trans (by simp [delayed, careTraj]))
    -- α is at `a t` in rounds `4t - 2` and `4t`; β is at `delayed τ' b t` in `4t - r`, `4t - r + 1`.
    have hα4 : careTraj lab a (4 * t) = a t := careTraj_four_mul ..
    have hα2 : careTraj lab a (4 * (t - 1) + 2) = a t := by
      rw [careTraj_four_mul_add_two]; congr 1; omega
    have hβ0 := delayed_care_start lab b τ t 0 ht (by omega)
    have hβ1 := delayed_care_start lab b τ t 1 ht (by omega)
    rw [← hτ', ← hr] at hβ0 hβ1
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with hr0 | hr0 | hr0 | hr0
    · refine ⟨4 * t, le_refl _, ?_⟩
      rw [hα4, hmeet, ← hβ0]; congr 1; omega
    · refine ⟨4 * t, le_refl _, ?_⟩
      rw [hα4, hmeet, ← hβ1]; congr 1; omega
    · refine ⟨4 * (t - 1) + 2, by omega, ?_⟩
      rw [hα2, hmeet, ← hβ0]; congr 1; omega
    · refine ⟨4 * (t - 1) + 2, by omega, ?_⟩
      rw [hα2, hmeet, ← hβ1]; congr 1; omega
  -- Case 2: a swap in rounds `t - 1 → t`.
  rcases h with h | ⟨ht, hx, hy⟩
  · exact absurd h hmeet
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hx hy
  -- α moves `p → q`, β moves `q → p`, `p ≠ q`
  have hpq : a k ≠ a (k + 1) := fun e => hmeet (by rw [hy, e])
  -- β really moved, hence was awake: `τ' ≤ k`
  have hk' : τ' ≤ k := by
    by_contra hlt
    apply hpq
    rw [← hy, hx]; simp only [delayed]; congr 1; omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + τ' := ⟨k - τ', by omega⟩
  have hbq : b k' = a (k' + τ' + 1) := by rw [hx]; simp only [delayed]; congr 1; omega
  have hbp : b (k' + 1) = a (k' + τ') := by rw [← hy]; simp only [delayed]; congr 1; omega
  -- positions of β in α's rounds `4k + j`: `careTraj b (4k' + r + j)`
  have hβ : ∀ j, delayed τ (careTraj lab b) (4 * (k' + τ') + j) =
      careTraj lab b (4 * k' + (r + j)) := by
    intro j; simp only [delayed]; congr 1; omega
  obtain ⟨a0, a1, a2, a3, -, -⟩ := careTraj_block lab a (k' + τ')
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := careTraj_block lab b k'
  simp only [hbq, hbp] at b0 b1 b2 b3 b4 b5
  generalize a (k' + τ') = p at *
  generalize a (k' + τ' + 1) = q at *
  set k := k' + τ' with hk
  have hlab : lab p ≠ lab q := fun e => hpq (hlab e)
  have hsk : ∀ j, j ≤ 3 → 4 * k + j ≤ 4 * (k + 1) := fun j hj => by omega
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with hr0 | hr0 | hr0 | hr0 <;>
    rcases lt_or_gt_of_ne hlab with hl | hl
  -- r = 0
  · refine ⟨4 * k + 3, hsk 3 (by omega), ?_⟩
    rw [hβ, hr0, b3, a3]; simp [hl, not_lt.2 hl.le]
  · refine ⟨4 * k + 3, hsk 3 (by omega), ?_⟩
    rw [hβ, hr0, b3, a3]; simp [hl, not_lt.2 hl.le]
  -- r = 1
  · refine ⟨4 * k + 1, hsk 1 (by omega), ?_⟩
    rw [hβ, hr0, b2, a1]
  · refine ⟨4 * k + 1, hsk 1 (by omega), ?_⟩
    rw [hβ, hr0, show 4 * k' + (1 + 1) = 4 * k' + 2 by ring, b2, a1]
  -- r = 2
  · refine ⟨4 * k, hsk 0 (by omega), ?_⟩
    rw [show 4 * k = 4 * k + 0 by ring, hβ, hr0, b2, Nat.add_zero, a0]
  · refine ⟨4 * k, hsk 0 (by omega), ?_⟩
    rw [show 4 * k = 4 * k + 0 by ring, hβ, hr0, b2, Nat.add_zero, a0]
  -- r = 3
  · refine ⟨4 * k + 1, hsk 1 (by omega), ?_⟩
    rw [hβ, hr0, show 4 * k' + (3 + 1) = 4 * k' + 4 by ring, b4, a1]
  · refine ⟨4 * k, hsk 0 (by omega), ?_⟩
    rw [show 4 * k = 4 * k + 0 by ring, hβ, hr0, b3, Nat.add_zero, a0]; simp [hl]

end Podc.RendezvousLabeledLine
