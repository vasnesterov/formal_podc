import Mathlib

/-!
# Appendix B: the `Ω(log n / log log n)` lower bound for task completion

Fischer, Gelles, *The Task Completion Problem and its Application to Crash-Resilient
Computation* (PODC 2026, arXiv:2605.17961), Appendix B (re-proving Georgiou–Russell–Shvartsman).

## Model

`R = 1`: attempting a task takes one round, a node attempts at most one task per round, and the
attempt succeeds iff the node does not crash during (or before) that round.

A deterministic algorithm is abstracted, in *full-information* form, as a `Strategy`: given the
history of crashes so far (`h : List (Finset V)`, **newest round first**; entry `C` = the set of
nodes the adversary crashes in that round), it says which task (if any) each node attempts in the
next round. Since the algorithm is deterministic and the only nondeterminism is the adversary's,
the behaviour of any deterministic algorithm (in any message-passing model, with any amount of
communication, even with an oracle telling everybody which tasks are still incomplete) against a
fixed way of resolving partial message delivery is such a function, so a lower bound for all
strategies is a lower bound for all deterministic algorithms.

* `crashed h` — the nodes crashed in the history `h`;
* `completed σ h` — the tasks completed after the rounds of `h`;
* `Solves σ f r` — every task is completed after `r` rounds against every crash pattern with at
  most `f` crashes.
-/

open Finset

namespace Podc.TaskCompletion.LowerBound

variable {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T] [DecidableEq T]

/-- A deterministic task-completion algorithm with `R = 1` in full-information form: from the
crash history (newest round first) to the task each node attempts in the next round. -/
def Strategy (V T : Type*) := List (Finset V) → V → Option T

/-- The nodes crashed in the history `h`. -/
def crashed : List (Finset V) → Finset V
  | [] => ∅
  | C :: h => C ∪ crashed h

/-- The tasks completed after the rounds recorded in `h`: in the round with crash set `C` (played
after history `h`), node `v` completes the task `σ h v` iff it has not crashed by the end of the
round. -/
def completed (σ : Strategy V T) : List (Finset V) → Finset T
  | [] => ∅
  | C :: h => completed σ h ∪
      univ.filter fun t => ∃ v, v ∉ crashed (C :: h) ∧ σ h v = some t

/-- `σ` solves task completion within `r` rounds against at most `f` crashes. -/
def Solves (σ : Strategy V T) (f : ℝ) (r : ℕ) : Prop :=
  ∀ h : List (Finset V), h.length = r → ((#(crashed h) : ℕ) : ℝ) ≤ f → completed σ h = univ

omit [Fintype T] in
/-- **Claim B.2** (averaging). If each of `n'` nodes attempts at most one task, then among any
`k'` tasks `K` there are at least `⌊k'/2⌋` tasks each attempted by at most `2n'/k'` nodes. -/
theorem claim_B_2 (a : V → Option T) (K : Finset T) :
    ∃ S ⊆ K, #K / 2 ≤ #S ∧
      ∀ t ∈ S, #(univ.filter fun v => a v = some t) * #K ≤ 2 * Fintype.card V := by
  set A : T → ℕ := fun t => #(univ.filter fun v => a v = some t) with hA
  -- each node attempts at most one task
  have hsum : ∀ K' : Finset T, ∑ t ∈ K', A t ≤ Fintype.card V := by
    intro K'
    rw [← card_biUnion]
    · exact card_le_univ _
    · intro t _ t' _ htt'
      simp only [Function.onFun]
      rw [disjoint_left]
      intro v hv hv'
      simp only [mem_filter, mem_univ, true_and] at hv hv'
      exact htt' (Option.some_injective _ (hv.symm.trans hv'))
  refine ⟨K.filter fun t => A t * #K ≤ 2 * Fintype.card V, filter_subset _ _, ?_,
    fun t ht => (mem_filter.1 ht).2⟩
  have hsplit := card_filter_add_card_filter_not
    (s := K) (fun t => A t * #K ≤ 2 * Fintype.card V)
  set B := K.filter fun t => ¬ A t * #K ≤ 2 * Fintype.card V
  have hB : 2 * #B ≤ #K := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
    · have : B = ∅ := by
        refine filter_eq_empty_iff.2 fun t _ => ?_
        have : A t = 0 := by
          simp only [hA, card_eq_zero, filter_eq_empty_iff]
          intro v
          have : Nonempty V := ⟨v⟩
          exact absurd h0 Fintype.card_ne_zero
        simp [this]
      simp [this]
    · have h1 : #B * (2 * Fintype.card V) ≤ ∑ t ∈ B, A t * #K := by
        rw [card_eq_sum_ones, sum_mul]
        refine sum_le_sum fun t ht => ?_
        have := (mem_filter.1 ht).2
        omega
      have h2 : ∑ t ∈ B, A t * #K ≤ Fintype.card V * #K := by
        rw [← sum_mul]
        exact Nat.mul_le_mul_right _ (hsum B)
      have : #B * 2 * Fintype.card V ≤ #K * Fintype.card V := by
        calc #B * 2 * Fintype.card V = #B * (2 * Fintype.card V) := by ring
          _ ≤ Fintype.card V * #K := h1.trans h2
          _ = #K * Fintype.card V := by ring
      have := Nat.le_of_mul_le_mul_right this hpos
      omega
  omega

/-- The adversary of Theorem B.1, built round by round: after `r` rounds there is a set of
`|T| / L ^ r` still-incomplete tasks, and at most `2n/L` nodes were crashed per round. -/
theorem exists_adversary (σ : Strategy V T) {L : ℕ} (hL : 2 ≤ L) (r : ℕ) :
    ∃ h : List (Finset V), h.length = r ∧ ∃ S : Finset T, #S = Fintype.card T / L ^ r ∧
      Disjoint S (completed σ h) ∧ #(crashed h) * L ≤ 2 * r * Fintype.card V := by
  induction r with
  | zero => exact ⟨[], rfl, univ, by simp, by simp [completed], by simp [crashed]⟩
  | succ r ih =>
    obtain ⟨h, hlen, S, hS, hdisj, hcr⟩ := ih
    obtain ⟨G, hGS, hG2, hGa⟩ := claim_B_2 (σ h) S
    obtain ⟨S', hS'G, hS'⟩ := exists_subset_card_eq (s := G) (n := #S / L)
      ((Nat.div_le_div_left hL (by omega)).trans hG2)
    set C := univ.filter fun v => ∃ t ∈ S', σ h v = some t with hCdef
    refine ⟨C :: h, by simp [hlen], S', ?_, ?_, ?_⟩
    · rw [hS', hS, Nat.div_div_eq_div_mul, pow_succ]
    · rw [completed, disjoint_union_right]
      refine ⟨disjoint_of_subset_left (hS'G.trans hGS) hdisj, ?_⟩
      rw [disjoint_left]
      intro t ht ht'
      simp only [mem_filter, mem_univ, true_and] at ht'
      obtain ⟨v, hv, hvt⟩ := ht'
      apply hv
      simp only [crashed, mem_union]
      left
      simp only [C, mem_filter, mem_univ, true_and]
      exact ⟨t, ht, hvt⟩
    · have hC : #C * L ≤ 2 * Fintype.card V := by
        rcases S'.eq_empty_or_nonempty with he | hne
        · have : C = ∅ := by
            simp [C, he]
          simp [this]
        · have hSpos : 0 < #S := card_pos.2 (hne.mono (hS'G.trans hGS))
          have h1 : #C ≤ ∑ t ∈ S', #(univ.filter fun v => σ h v = some t) := by
            calc #C = #(S'.biUnion fun t => univ.filter fun v => σ h v = some t) := by
                  congr 1; ext v; simp [C]
              _ ≤ _ := card_biUnion_le
          have h2 : #C * #S ≤ #S' * (2 * Fintype.card V) := by
            calc #C * #S ≤ (∑ t ∈ S', #(univ.filter fun v => σ h v = some t)) * #S :=
                  Nat.mul_le_mul_right _ h1
              _ = ∑ t ∈ S', #(univ.filter fun v => σ h v = some t) * #S := sum_mul _ _ _
              _ ≤ ∑ t ∈ S', 2 * Fintype.card V := sum_le_sum fun t ht => hGa t (hS'G ht)
              _ = _ := by simp
          have h3 : #S' * L ≤ #S := hS' ▸ Nat.div_mul_le_self _ _
          have : #C * L * #S ≤ 2 * Fintype.card V * #S := by
            calc #C * L * #S = (#C * #S) * L := by ring
              _ ≤ #S' * (2 * Fintype.card V) * L := Nat.mul_le_mul_right _ h2
              _ = (#S' * L) * (2 * Fintype.card V) := by ring
              _ ≤ #S * (2 * Fintype.card V) := Nat.mul_le_mul_right _ h3
              _ = _ := by ring
          exact Nat.le_of_mul_le_mul_right this hSpos
      calc #(crashed (C :: h)) * L ≤ (#C + #(crashed h)) * L :=
            Nat.mul_le_mul_right _ (card_union_le _ _)
        _ = #C * L + #(crashed h) * L := by ring
        _ ≤ 2 * Fintype.card V + 2 * r * Fintype.card V := by omega
        _ = 2 * (r + 1) * Fintype.card V := by ring

/-- **Theorem B.1** (non-asymptotic core). Let `L ≥ 2`, `r` rounds with `2 r n ≤ f L` (i.e. at
most `2n/L` crashes per round suffice) and `L ^ r ≤ n` tasks. Then against every strategy there is
a crash pattern with at most `f` crashes after which some task is still incomplete after `r`
rounds. -/
theorem exists_incomplete (σ : Strategy V T) {L r : ℕ} (hL : 2 ≤ L)
    (hn : L ^ r ≤ Fintype.card T) {f : ℝ}
    (hf : 2 * r * (Fintype.card V : ℝ) ≤ f * L) :
    ∃ h : List (Finset V), h.length = r ∧ ((#(crashed h) : ℕ) : ℝ) ≤ f ∧
      completed σ h ≠ univ := by
  obtain ⟨h, hlen, S, hS, hdisj, hcr⟩ := exists_adversary σ hL r
  refine ⟨h, hlen, ?_, ?_⟩
  · have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have : ((#(crashed h) : ℕ) : ℝ) * L ≤ 2 * r * (Fintype.card V : ℝ) := by exact_mod_cast hcr
    exact le_of_mul_le_mul_right (this.trans hf) hL0
  · have hpos : 0 < #S := by
      rw [hS]
      exact Nat.div_pos hn (pow_pos (by omega) _)
    obtain ⟨t, ht⟩ := card_pos.1 hpos
    intro hu
    exact disjoint_left.1 hdisj ht (hu ▸ mem_univ t)

/-- **Theorem B.1.** Any deterministic algorithm solving the task completion problem with `M = n`
tasks and `R = 1` in the presence of `αn` crash faults, `α ∈ (0, 1)`, requires
`Ω(log n / log log n)` rounds. -/
theorem theorem_B_1 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ (σ : Strategy (Fin n) (Fin n)) (r : ℕ),
      Solves σ (α * n) r → c * Real.log n / Real.log (Real.log n) ≤ r := by
  refine ⟨α / 4, by positivity, ⌈Real.exp (Real.exp 1)⌉₊, fun n hn σ r hsol => ?_⟩
  by_contra! hlt
  have hnR : Real.exp (Real.exp 1) ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans_le hnR
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : Real.exp 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]; exact hnR
  have hlog0 : 0 < Real.log n := by linarith
  have hll : 1 ≤ Real.log (Real.log n) := by
    rw [Real.le_log_iff_exp_le hlog0]; exact hlog
  -- the adversary uses `L = ⌊log n⌋`
  set L := ⌊Real.log n⌋₊ with hLdef
  have hL2 : 2 ≤ L := Nat.le_floor (by push_cast; linarith)
  have hLle : (L : ℝ) ≤ Real.log n := Nat.floor_le hlog0.le
  have hLgt : Real.log n < L + 1 := Nat.lt_floor_add_one _
  have hr1 : (r : ℝ) * Real.log (Real.log n) < α / 4 * Real.log n := by
    rwa [lt_div_iff₀ (by linarith)] at hlt
  have hr2 : (r : ℝ) ≤ (r : ℝ) * Real.log (Real.log n) :=
    le_mul_of_one_le_right (by positivity) hll
  have hpow : L ^ r ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    have : ((L ^ r : ℕ) : ℝ) ≤ n := by
      push_cast
      calc (L : ℝ) ^ r ≤ (Real.log n) ^ r := pow_le_pow_left₀ (by positivity) hLle r
        _ = Real.exp (r * Real.log (Real.log n)) := by
          rw [Real.exp_nat_mul, Real.exp_log hlog0]
        _ ≤ Real.exp (Real.log n) := Real.exp_le_exp.2 (by nlinarith)
        _ = n := Real.exp_log hn0
    exact_mod_cast this
  have hf : 2 * r * (Fintype.card (Fin n) : ℝ) ≤ α * n * L := by
    rw [Fintype.card_fin]
    have h1 : 0 < α * (L + 1 - Real.log n) := mul_pos hα0 (by linarith)
    have : 2 * (r : ℝ) ≤ α * L := by nlinarith
    nlinarith
  obtain ⟨h, hlen, hcr, hne⟩ := exists_incomplete σ hL2 hpow hf
  exact hne (hsol h hlen hcr)

end Podc.TaskCompletion.LowerBound
