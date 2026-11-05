import Papers.PODC2020.StoreCollectChurn.CCC
import Papers.PODC2020.StoreCollectChurn.Constraints

/-!
# CCC is not regular: counterexamples to Theorem 6, Corollary 7, Lemma 10 and Observation 5

**The bug.** In a collect, the client broadcasts `⟨store, LView⟩` at Line 36 (store-back) but at
Line 47 returns the *current* `LView`, which may meanwhile have been enlarged by the server thread
of the same node (Line 48 merges the views of `store` messages of *other* clients into the same
variable `LView`). So a collect can return a value of a concurrent `STORE` that it never wrote back
to a quorum, and a later collect can miss that value. Likewise `view(φ)` is the value of `LView` at
the *end* of the phase (Section 4), which is not the view that the phase stored, so Lemma 10 fails.

**The execution** (static system, `S₀` = five nodes `r = 0, p₁ = 1, p₂ = 2, a = 3, b = 4`, no
`ENTER`/`LEAVE`/`CRASH`; `D = 20`; `β = 3/5`, so `threshold = β · |Members| = 3`):

* `t = 1`: `p₁` invokes `COLLECT` (broadcast #0, the collect query); `p₁`, `a`, `b` answer with
  empty views (#1–#3, received by `p₁` at `t = 3`); `p₁` broadcasts the store-back `⟨store, ∅⟩`
  (#4) at `t = 3`.
* `t = 4`: `r` invokes `STORE(1)` and broadcasts `⟨store, {⟨r, 1, 1⟩}⟩` (#5).
* `t = 5`: `p₁`, `a`, `b` receive the store-back #4 and acknowledge it (#6, #8, #10).
* `t = 6`: `p₁` receives `r`'s store #5 (Line 48): now `LView_{p₁} = {⟨r, 1, 1⟩}`.
* `t = 7`: `p₁` receives the three acks and **returns `V₁ = {⟨r, 1⟩}`** (Line 47).
* `t = 8`–`12`: `p₂` invokes `COLLECT` (#14); `p₂`, `a`, `b` answer with empty views (they have not
  heard of `r`'s store yet); the store-back `⟨store, ∅⟩` (#18) is acknowledged by `p₂`, `a`, `b`,
  and **`p₂` returns `V₂ = ∅`** at `t = 12`.
* Afterwards all remaining broadcasts are delivered (FIFO, delays in `(0, D]`); the messages carrying
  `r`'s value reach `p₂`, `a`, `b` only at `t = 24 = 4 + D`. `r`'s store completes at `t = 25`.

`COLLECT_{p₁}` precedes `COLLECT_{p₂}`, `V₁(r) = 1` and `V₂(r) = ⊥`, so `V₁ ⋠ V₂`: part 2 of
regularity fails. The parameters `α = Δ = 1/100`, `γ = 3/4`, `β = 3/5`, `N_min = 2` satisfy
Constraints A–D of Section 5; the churn, failure-fraction and minimum-size assumptions hold trivially
(no churn, no crash, `N(t) = 5`).
-/

namespace Podc.StoreCollectChurn.CCC.Counterexample

open Podc.StoreCollectChurn

/-- The five nodes. -/
abbrev Node := Fin 5

/-- The storing node. -/
def r : Node := 0
/-- The first collector. -/
def p1 : Node := 1
/-- The second collector. -/
def p2 : Node := 2
/-- Two further servers. -/
def a : Node := 3
/-- Two further servers. -/
def b : Node := 4

/-- Parameters: churn rate `α`. -/
def α : ℚ := 1 / 100
/-- Failure fraction `Δ`. -/
def Δ : ℚ := 1 / 100
/-- Join fraction `γ` (only used by Algorithm 1, which does not fire in a static execution). -/
def γ : ℚ := 3 / 4
/-- Quorum fraction `β`; `β · |Members| = 3`. -/
def β : ℚ := 3 / 5
/-- Minimum system size. -/
def Nmin : ℕ := 2
/-- Maximal message delay. -/
def D : ℕ := 20

/-- The standing assumptions on the parameters (Section 3: `α > 0`, `0 < Δ ≤ 1`, `N_min ≥ 1`) and
Constraints A–D of Section 5, both as printed and with cleared denominators
(`AllConstraints`, `Constraints.lean`). -/
def ParamsOK (α Δ γ β : ℝ) (Nmin : ℕ) : Prop :=
  0 < α ∧ 0 < Δ ∧ Δ ≤ 1 ∧ 0 < Nmin ∧ AllConstraints α Δ γ β Nmin

/-- The parameters of the counterexample satisfy the standing assumptions and Constraints A–D. -/
theorem params_ok : ParamsOK (α : ℝ) Δ γ β Nmin := by
  unfold ParamsOK AllConstraints ConstraintA ConstraintA' ConstraintB ConstraintC ConstraintD
    ConstraintD' Z
  norm_num [α, Δ, γ, β, Nmin]

/-! ## The execution -/

/-- `COLLECT_p` at time `t`. -/
def C (t : ℕ) (p : Node) : TEv 5 := ⟨t, .collect p⟩
/-- `STORE_p(v)` at time `t`. -/
def S (t : ℕ) (p : Node) (v : ℕ) : TEv 5 := ⟨t, .store p v⟩
/-- Receipt by `p` of broadcast number `k` at time `t`. -/
def R (t : ℕ) (p : Node) (k : ℕ) : TEv 5 := ⟨t, .recv p k⟩
/-- Receipts by `p` of the broadcasts `ks` (in this order) at time `t`. -/
def rs (t : ℕ) (p : Node) (ks : List ℕ) : List (TEv 5) := ks.map (R t p)

/-- The interesting part of the execution (until `p₂` returns). The comments give the broadcasts
sent by each step. -/
def exPrefix : List (TEv 5) :=
  [C 1 p1,                                    -- #0 ⟨collect-query, 1, p₁⟩
   R 2 p1 0, R 2 a 0, R 2 b 0,                -- #1, #2, #3 ⟨collect-reply, ∅, 1, p₁⟩
   R 3 p1 1, R 3 p1 2, R 3 p1 3,              -- p₁ reaches the threshold: #4 ⟨store, ∅, 1, p₁⟩
   R 3 a 1, R 3 b 1,                          -- (FIFO filler: reply #1 is for p₁)
   S 4 r 1,                                   -- #5 ⟨store, {⟨r,1,1⟩}, 1, r⟩
   R 5 p1 4, R 5 a 4, R 5 b 4,                -- #6–#11: store-ack (to p₁) and store-echo(∅)
   R 6 p1 5,                                  -- LView_{p₁} = {⟨r,1,1⟩}; #12 ack to r, #13 echo
   R 7 p1 6, R 7 p1 8, R 7 p1 10,             -- p₁ RETURNs {⟨r,1,1⟩}
   C 8 p2,                                    -- #14 ⟨collect-query, 1, p₂⟩
   R 9 p2 14, R 9 a 14, R 9 b 14,             -- #15, #16, #17 ⟨collect-reply, ∅, 1, p₂⟩
   R 10 p2 15, R 10 p2 2, R 10 p2 8, R 10 p2 9, R 10 p2 16,   -- (FIFO: a's #2, #8, #9 first)
   R 10 p2 3, R 10 p2 10, R 10 p2 11, R 10 p2 17,             -- threshold: #18 ⟨store, ∅, 1, p₂⟩
   R 10 a 15, R 10 b 15,
   R 11 p2 18, R 11 a 18, R 11 b 18,          -- #19–#24: store-acks (to p₂) and echoes
   R 12 p2 19, R 12 p2 21, R 12 p2 23]        -- p₂ RETURNs ∅

/-- The complete execution: `exPrefix` followed by the delivery of all remaining broadcasts. Until
`t = 24`, the nodes `p₂`, `a`, `b` receive no message carrying `r`'s value (nor, by FIFO, any later
message of the same sender). -/
def ex : List (TEv 5) := exPrefix ++
  rs 13 r (List.range' 0 25) ++
  rs 13 p1 [7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] ++
  rs 13 p2 [0, 1, 4, 6, 7, 12, 20, 22, 24] ++
  rs 13 a [2, 3, 6, 7, 8, 9, 10, 11, 12, 16, 17, 19, 20, 21, 22, 23, 24] ++
  rs 13 b [2, 3, 6, 7, 8, 9, 10, 11, 12, 16, 17, 19, 20, 21, 22, 23, 24] ++
  rs 14 r (List.range' 25 14) ++
  rs 14 p1 (List.range' 25 14) ++
  rs 14 p2 [36, 37, 38] ++
  rs 14 a [36, 37, 38] ++
  rs 14 b [36, 37, 38] ++
  rs 24 p2 [5, 13, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35] ++
  rs 24 a [5, 13, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35] ++
  rs 24 b [5, 13, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35] ++
  rs 25 r (List.range' 39 6) ++
  rs 25 p1 (List.range' 39 6) ++
  rs 25 p2 (List.range' 39 6) ++
  rs 25 a (List.range' 39 6) ++
  rs 25 b (List.range' 39 6)

/-- The execution is admissible. -/
theorem ex_admissible : Admissible β D ex := by decide +kernel

/-- At the end no operation is pending: all three operations completed. -/
theorem ex_all_idle : ∀ p : Node, ((run β ex).node p).phase = .idle := by decide +kernel

/-- The schedule, with CCC views. -/
theorem ex_sched : (run β ex).sched =
    [.colInv p1, .stInv r 1, .ret p1 [(r, 1, 1)], .colInv p2, .ret p2 [], .ack r] := by
  decide +kernel

/-- The view `V₁ = {⟨r, 1⟩}` returned by `p₁`. -/
def V₁ : Node → Option ℕ := View.val [(r, 1, 1)]
/-- The view `V₂ = ∅` returned by `p₂`. -/
def V₂ : Node → Option ℕ := View.val []

/-- The store-collect schedule of the execution. -/
def σ : List (SCEv Node ℕ) := [.colInv p1, .stInv r 1, .ret p1 V₁, .colInv p2, .ret p2 V₂, .ack r]

theorem schedule_ex : schedule β ex = σ := by
  rw [schedule, ex_sched]; rfl

/-! ## Properties of the schedule -/

/-- `Next σ i j` for concrete positions, by checking the clients of the events in between. -/
macro "next_tac" : tactic => `(tactic|
  (refine ⟨by norm_num, _, _, rfl, rfl, rfl, ?_⟩
   intro k hk₁ hk₂ e he
   interval_cases k <;> simp only [σ, List.getElem?_cons_succ, List.getElem?_cons_zero,
     Option.some.injEq] at he <;> subst he <;> decide))

/-- The event following an invocation of `σ` at the same client is not an invocation. -/
macro "inv_tac" : tactic => `(tactic|
  (intro _ j hj e' he'
   obtain ⟨hij, e₀, e₁, h₀, h₁, hp, hb⟩ := hj
   have hj6 : j < 6 := by
     have := (List.getElem?_eq_some_iff.1 he').1; simpa [σ] using this
   interval_cases j <;> simp only [σ, List.getElem?_cons_succ, List.getElem?_cons_zero,
     Option.some.injEq] at h₀ h₁ he' <;> subst h₀ h₁ he' <;>
   first
   | exact fun h => h
   | omega
   | exact absurd hp (by decide)
   | exact absurd rfl (hb 2 (by omega) (by omega) _ rfl)
   | exact absurd rfl (hb 4 (by omega) (by omega) _ rfl)
   | exact absurd rfl (hb 5 (by omega) (by omega) _ rfl)))

theorem σ_wellFormed : WellFormed σ := by
  intro i e he
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp only [σ, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.some.injEq] at he <;> try subst he
  · exact ⟨fun h => absurd trivial h, by inv_tac⟩
  · exact ⟨fun h => absurd trivial h, by inv_tac⟩
  · exact ⟨fun _ => ⟨0, by next_tac, Or.inr ⟨rfl, _, rfl⟩⟩, fun h => h.elim⟩
  · exact ⟨fun h => absurd trivial h, by inv_tac⟩
  · exact ⟨fun _ => ⟨3, by next_tac, Or.inr ⟨rfl, _, rfl⟩⟩, fun h => h.elim⟩
  · exact ⟨fun _ => ⟨1, by next_tac, Or.inl ⟨1, rfl, rfl⟩⟩, fun h => h.elim⟩
  · simp at he

theorem σ_uniqueValues : UniqueValues σ := by
  intro i i' p v hi hi'
  simp only [StoreAt, σ] at hi hi'
  rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> simp at hi
  rcases i' with _ | _ | _ | _ | _ | _ | _ | i' <;> simp at hi'
  rfl

theorem σ_not_regular : ¬ Regular σ := by
  intro h
  have h₁ : CollectOp σ 0 2 V₁ := ⟨p1, rfl, rfl, by next_tac⟩
  have h₂ : CollectOp σ 3 4 V₂ := ⟨p2, rfl, rfl, by next_tac⟩
  obtain ⟨v, hv, -⟩ := h.2 0 2 V₁ 3 4 V₂ h₁ h₂ (by norm_num) r 1 rfl
  simp [V₂, View.val, View.lookup] at hv

/-- A view containing `⟨r, 1⟩` is not `⪯` the empty view (in any schedule). -/
theorem not_viewLE_empty (τ : List (SCEv Node ℕ)) : ¬ ViewLE τ (View.val [(r, 1, 1)]) (View.val []) := by
  intro h
  obtain ⟨v, hv, -⟩ := h r 1 rfl
  simp [View.val, View.lookup] at hv

/-! ## Main results -/

/-- **Theorem 6 (and Corollary 7) of the paper are false.** There are parameters satisfying
Constraints A–D and an admissible static execution of CCC (Algorithms 1–3, with the charitable
repairs described in `CCC.lean`; `N(t) = 5 ≥ N_min` at all times, no churn, no crash) in which every
operation completes and whose store-collect schedule is well formed, has unique values, and is
**not regular**: `COLLECT_{p₁}` returns `{⟨r, 1⟩}`, the later `COLLECT_{p₂}` returns `∅`. -/
theorem theorem6_false : ∃ (α Δ γ β : ℚ) (Nmin D : ℕ) (ex : List (TEv 5)),
    ParamsOK (α : ℝ) Δ γ β Nmin ∧ Nmin ≤ 5 ∧ 0 < D ∧
    Admissible β D ex ∧ (∀ p, ((run β ex).node p).phase = .idle) ∧
    WellFormed (schedule β ex) ∧ UniqueValues (schedule β ex) ∧ ¬ Regular (schedule β ex) := by
  refine ⟨α, Δ, γ, β, Nmin, D, ex, params_ok, by decide, by decide, ex_admissible, ex_all_idle,
    ?_, ?_, ?_⟩ <;> rw [schedule_ex]
  exacts [σ_wellFormed, σ_uniqueValues, σ_not_regular]

/-- The store-back phase of `COLLECT_{p₁}` (times `3`–`7`). -/
def sPhase : PhaseRec 5 := ⟨p1, .store, 3, 7⟩
/-- The collect phase of `COLLECT_{p₂}` (times `8`–`10`). -/
def cPhase : PhaseRec 5 := ⟨p2, .collect, 8, 10⟩

theorem phases_mem : sPhase ∈ (run β ex).phases ∧ cPhase ∈ (run β ex).phases := by decide +kernel

theorem view_sPhase : phaseView β ex sPhase = [(r, 1, 1)] := by decide +kernel

theorem view_cPhase : phaseView β ex cPhase = [] := by decide +kernel

/-- **Lemma 10 of the paper is false.** In an admissible execution (parameters satisfying
Constraints A–D), a store phase `s` (the store-back of `COLLECT_{p₁}`) finishes before a collect
phase `c` (of `COLLECT_{p₂}`, which terminates) starts, but `view(s) ⋠ view(c)`, where `view(φ)` is
`LView` of the phase's node at the end of `φ` (Section 4). -/
theorem lemma10_false : ∃ (α Δ γ β : ℚ) (Nmin D : ℕ) (ex : List (TEv 5)),
    ParamsOK (α : ℝ) Δ γ β Nmin ∧ Nmin ≤ 5 ∧ 0 < D ∧ Admissible β D ex ∧
    ∃ s ∈ (run β ex).phases, ∃ c ∈ (run β ex).phases,
      s.kind = .store ∧ c.kind = .collect ∧ s.finish < c.start ∧
      ¬ ViewLE (schedule β ex) (phaseView β ex s).val (phaseView β ex c).val := by
  refine ⟨α, Δ, γ, β, Nmin, D, ex, params_ok, by decide, by decide, ex_admissible,
    sPhase, phases_mem.1, cPhase, phases_mem.2, rfl, rfl, by decide, ?_⟩
  rw [view_sPhase, view_cPhase]
  exact not_viewLE_empty _

theorem lview_a_23 : (stateAt β ex 23 a).lview = [] := by decide +kernel

/-- **Observation 5 of the paper is false.** In an admissible execution (parameters satisfying
Constraints A–D, no crash, all nodes active forever), for the store phase `s` (store-back of
`COLLECT_{p₁}`, started at `t_s = 3`) and node `a`, at time `t = t_s + D = 23` (after `s` finished)
`view(s) ⋠ LView_a^t`. -/
theorem observation5_false : ∃ (α Δ γ β : ℚ) (Nmin D : ℕ) (ex : List (TEv 5)),
    ParamsOK (α : ℝ) Δ γ β Nmin ∧ Nmin ≤ 5 ∧ 0 < D ∧ Admissible β D ex ∧
    ∃ s ∈ (run β ex).phases, s.kind = .store ∧ ∃ (p : Fin 5) (t : ℕ),
      s.start + D ≤ t ∧ s.finish ≤ t ∧
      ¬ ViewLE (schedule β ex) (phaseView β ex s).val (stateAt β ex t p).lview.val := by
  refine ⟨α, Δ, γ, β, Nmin, D, ex, params_ok, by decide, by decide, ex_admissible,
    sPhase, phases_mem.1, rfl, a, 23, by decide, by decide, ?_⟩
  rw [view_sPhase, lview_a_23]
  exact not_viewLE_empty _

end Podc.StoreCollectChurn.CCC.Counterexample
