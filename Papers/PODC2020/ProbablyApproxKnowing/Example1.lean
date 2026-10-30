import Papers.PODC2020.ProbablyApproxKnowing.Basic

/-!
# Example 1 (relaxed firing squad) and the claim of §7 about it

Example 1 of [Moses–Zamir]: Alice and Bob, synchronous rounds, every message is lost independently
with probability `0.1`; Alice's initial bit `go` is `0` or `1` with probability `1/2` each.

* `FS`: the protocol FS. If `go = 1` Alice sends two messages in round 1 and fires at time 2. Bob
  replies 'Yes' in round 2 and fires at time 2 if he received a message in round 1, and replies 'No'
  (and never fires) otherwise. We check the numbers of §1 and §8: `μ(both fire | Alice fires) = 0.99`
  (`FS.cprob_both`); Alice's belief that both fire when she fires is `1`, `0` or `0.99` after
  receiving 'Yes', 'No' or nothing (`FS.beliefAt_eq`); the threshold `0.95` is met with
  probability `0.991` (`FS.cprob_threshold`); and in the variant where Alice does not fire after a
  'No', `μ(both fire | Alice fires) = 990/991 ≈ 0.99899` (`FS.cprob_both_noNo`).
* `Mixed`: a protocol in the same setting in which Alice, when `go = 1`, fires at time 1 only with
  probability `1/2` (Bob fires at time 1 iff he received one of her two round-1 messages). It
  satisfies the constraint `μ(φ_both@fire_A | fire_A) ≥ 0.99` of §7, but Alice's belief in `φ_both`
  when she fires is `0.495` at every firing point, so the claim of §7 ("in every protocol that
  satisfies this constraint, … Alice's degree of belief that both are firing … meets or exceeds `0.9`
  with probability at least `0.9`") fails (`Mixed.section7_claim_false`). With the fact "Bob is
  firing" instead of `φ_both` the claim holds (`Mixed.belief_fireB`; in general
  `JointProtocol.section7_claim_fireB` in `Protocol.lean`).

The runs only record the random outcomes that matter (whether Bob received at least one of Alice's
messages, whether Bob's reply was delivered, Alice's coin); runs of the full tree that differ only in
outcomes nobody's relevant local state depends on are merged, which does not change any probability
or belief about the facts considered here.
-/

namespace Podc.ProbablyApproxKnowing.Example1

open Finset PPS

/-- The two agents. -/
inductive Ag | A | B
  deriving DecidableEq

/-! ## The protocol FS -/

namespace FS

/-- Runs: `inl d` (`go = 0`; Bob's 'No' delivered iff `d`), `inr (b, d)` (`go = 1`; Bob received at
least one of Alice's messages iff `b`, probability `0.99`; Bob's reply delivered iff `d`, probability
`0.9`). -/
abbrev R := Bool ⊕ (Bool × Bool)

/-- Run probabilities. -/
noncomputable def μ : R → ℝ
  | .inl d => 1 / 2 * (if d then 9 / 10 else 1 / 10)
  | .inr (b, d) => 1 / 2 * (if b then 99 / 100 else 1 / 100) * (if d then 9 / 10 else 1 / 10)

theorem μ_pos (r : R) : 0 < μ r := by
  rcases r with (_ | _) | ⟨_ | _, _ | _⟩ <;> norm_num [μ]

theorem sum_μ : ∑ r, μ r = 1 := by
  simp [μ, Fintype.sum_sum_type, Fintype.sum_prod_type]; norm_num

/-- Local states (besides the time): Alice holds `go` and, from time 2 on, Bob's reply if it was
delivered (`some true` = 'Yes', `some false` = 'No'); Bob holds, from time 1 on, whether he received a
message from Alice. -/
def info : Ag → R → ℕ → Bool × Option Bool
  | .A, .inl d, t => (false, if 2 ≤ t ∧ d = true then some false else none)
  | .A, .inr (b, d), t => (true, if 2 ≤ t ∧ d = true then some b else none)
  | .B, .inl _, t => (false, if 1 ≤ t then some false else none)
  | .B, .inr (b, _), t => (false, if 1 ≤ t then some b else none)

/-- The pps of FS (times `0, …, 3`). -/
noncomputable def T : PPS R Ag (ℕ × (Bool × Option Bool)) := ofTimed μ μ_pos sum_μ 3 info

theorem T_occurs {i : Ag} {t₀ : ℕ} {x : Bool × Option Bool} {r : R} :
    T.Occurs i (t₀, x) r ↔ t₀ ≤ 3 ∧ info i r t₀ = x := ofTimed_occurs

theorem T_at {φ : Fact R} {i : Ag} {t₀ : ℕ} {x : Bool × Option Bool} {r : R} :
    T.At φ i (t₀, x) r ↔ t₀ ≤ 3 ∧ info i r t₀ = x ∧ φ r t₀ := ofTimed_at

/-- `go = 1`. -/
def go : R → Bool
  | .inl _ => false
  | .inr _ => true

/-- Alice fires at time 2 iff `go = 1` and `fires` holds of the reply she received. FS:
`fires = fun _ => true`; the variant of §8: `fires x = (x ≠ some false)`. -/
def fireA (fires : Option Bool → Bool) : Fact R :=
  fun r t => t = 2 ∧ go r = true ∧ fires (info .A r 2).2 = true

/-- Bob fires at time 2 iff he received a message in round 1. -/
def fireB : Fact R := fun r t => t = 2 ∧ (info .B r 2).2 = some true

/-- `φ_both`: both agents are firing. -/
def both (fires : Option Bool → Bool) : Fact R := fun r t => fireA fires r t ∧ fireB r t

variable (fires : Option Bool → Bool)

theorem performs_iff (r : R) :
    T.Performs (fireA fires) r ↔ go r = true ∧ fires (info .A r 2).2 = true := by
  simp only [PPS.Performs, fireA]
  constructor
  · rintro ⟨_, _, rfl, h⟩; exact h
  · intro h; exact ⟨2, by simp [T, ofTimed], rfl, h⟩

theorem proper (h : fires none = true) : T.Proper (fireA fires) :=
  ⟨⟨.inr (true, false), (performs_iff _ _).2 ⟨rfl, by simpa [info] using h⟩⟩,
    fun _ _ _ _ _ h h' => h.1.trans h'.1.symm⟩

theorem actTime (h : fires none = true) (r : R) (hr : T.Performs (fireA fires) r) :
    T.actTime (fireA fires) r = 2 := by
  obtain ⟨t, ht, h2⟩ := hr
  rw [(proper fires h).actTime_eq ht h2, h2.1]

theorem atAct_iff (h : fires none = true) (r : R) :
    T.AtAct (both fires) (fireA fires) r ↔
      T.Performs (fireA fires) r ∧ (info .B r 2).2 = some true := by
  rw [(proper fires h).atAct_iff]
  constructor
  · rintro ⟨hp, hb⟩
    rw [actTime fires h r hp] at hb
    exact ⟨hp, hb.2.2⟩
  · rintro ⟨hp, hb⟩
    rw [actTime fires h r hp]
    exact ⟨hp, ((performs_iff fires r).1 hp |> fun h' => ⟨rfl, h'⟩), rfl, hb⟩

open Classical in
theorem prob_R (Q : R → Prop) : T.prob Q =
    (if Q (.inl true) then 9 / 20 else 0) + (if Q (.inl false) then 1 / 20 else 0) +
    ((if Q (.inr (true, true)) then 891 / 2000 else 0) +
      (if Q (.inr (true, false)) then 99 / 2000 else 0) +
      ((if Q (.inr (false, true)) then 9 / 2000 else 0) +
        (if Q (.inr (false, false)) then 1 / 2000 else 0))) := by
  simp only [PPS.prob, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [T, ofTimed, μ]
  norm_num

/-- `μ(φ_both@fire_A | fire_A) = 0.99` for FS. -/
theorem cprob_both : T.cprob (T.AtAct (both fun _ => true) (fireA fun _ => true))
    (T.Performs (fireA fun _ => true)) = 99 / 100 := by
  rw [PPS.cprob, prob_R, prob_R]
  simp only [atAct_iff (fun _ => true) rfl, performs_iff]
  simp [info, go]
  norm_num

/-- Variant of §8 (Alice does not fire after a 'No'): `μ(φ_both | fire_A) = 990/991 ≈ 0.99899`. -/
theorem cprob_both_noNo : T.cprob (T.AtAct (both fun x => x ≠ some false)
    (fireA fun x => x ≠ some false)) (T.Performs (fireA fun x => x ≠ some false)) = 990 / 991 := by
  rw [PPS.cprob, prob_R, prob_R]
  simp only [atAct_iff (fun x => x ≠ some false) rfl, performs_iff]
  simp [info, go]
  norm_num

/-- Alice's belief in `φ_both` when she fires in FS: `1` after 'Yes', `0` after 'No', `0.99` if
Bob's reply was lost. -/
theorem beliefAt_eq (r : R) (hr : go r = true) :
    T.beliefAt .A (both fun _ => true) (fireA fun _ => true) r =
      if (info .A r 2).2 = some true then 1 else if (info .A r 2).2 = some false then 0
      else 99 / 100 := by
  have hp : T.Performs (fireA fun _ => true) r := (performs_iff _ r).2 ⟨hr, rfl⟩
  rw [PPS.beliefAt, ite_eq_left hp, actTime _ rfl r hp, PPS.belief, cprob_at]
  change T.prob (T.At _ _ (2, info .A r 2)) / T.prob (T.Occurs _ (2, info .A r 2)) = _
  rw [PPS.prob_congr (fun _ => T_at), PPS.prob_congr (fun _ => T_occurs), prob_R, prob_R]
  rcases r with d | ⟨b, d⟩
  · simp [go] at hr
  · rcases b with _ | _ <;> rcases d with _ | _ <;> simp [info, both, fireA, fireB, go] <;> norm_num

/-- For FS, the threshold `0.95` is met with probability `0.991` when Alice fires (it fails only
when both of Alice's messages and none of Bob's 'No' is lost: probability `0.1·0.1·0.9 = 0.009`). -/
theorem cprob_threshold : T.cprob (fun r => 95 / 100 ≤
    T.beliefAt .A (both fun _ => true) (fireA fun _ => true) r)
    (T.Performs (fireA fun _ => true)) = 991 / 1000 := by
  have h : ∀ r, (95 / 100 ≤ T.beliefAt .A (both fun _ => true) (fireA fun _ => true) r ∧
      T.Performs (fireA fun _ => true) r) ↔
      (go r = true ∧ (info .A r 2).2 ≠ some false) := by
    intro r
    rw [performs_iff]
    by_cases hr : go r = true
    · rw [beliefAt_eq r hr]
      rcases r with d | ⟨b, d⟩
      · simp [go] at hr
      · rcases b with _ | _ <;> rcases d with _ | _ <;> simp [info, go] <;> norm_num
    · simp [hr]
  rw [PPS.cprob, PPS.prob_congr h, prob_R, prob_R]
  simp only [performs_iff]
  simp [info, go]
  norm_num

end FS

/-! ## A mixed-action protocol refuting the claim of §7 -/

namespace Mixed

/-- Runs: `none` (`go = 0`), `some (b, c)` (`go = 1`; Bob received at least one of Alice's two
round-1 messages iff `b`, probability `0.99`; Alice's coin `c`, probability `1/2`). -/
abbrev R := Option (Bool × Bool)

/-- Run probabilities. -/
noncomputable def μ : R → ℝ
  | none => 1 / 2
  | some (b, _) => 1 / 2 * (if b then 99 / 100 else 1 / 100) * (1 / 2)

theorem μ_pos (r : R) : 0 < μ r := by
  rcases r with _ | ⟨_ | _, _ | _⟩ <;> norm_num [μ]

theorem sum_μ : ∑ r, μ r = 1 := by
  simp [μ, Fintype.sum_option, Fintype.sum_prod_type]; norm_num

/-- Local states (besides the time): Alice holds `go` (she receives nothing); Bob holds, from time
1 on, whether he received a message. Alice's coin, tossed when she acts at time 1, is not part of
her local state at time 1. -/
def info : Ag → R → ℕ → Bool × Option Bool
  | .A, none, _ => (false, none)
  | .A, some _, _ => (true, none)
  | .B, none, t => (false, if 1 ≤ t then some false else none)
  | .B, some (b, _), t => (false, if 1 ≤ t then some b else none)

/-- The pps (times `0, 1, 2`). -/
noncomputable def T : PPS R Ag (ℕ × (Bool × Option Bool)) := ofTimed μ μ_pos sum_μ 2 info

theorem T_occurs {i : Ag} {t₀ : ℕ} {x : Bool × Option Bool} {r : R} :
    T.Occurs i (t₀, x) r ↔ t₀ ≤ 2 ∧ info i r t₀ = x := ofTimed_occurs

theorem T_at {φ : Fact R} {i : Ag} {t₀ : ℕ} {x : Bool × Option Bool} {r : R} :
    T.At φ i (t₀, x) r ↔ t₀ ≤ 2 ∧ info i r t₀ = x ∧ φ r t₀ := ofTimed_at

/-- Alice fires at time 1 iff `go = 1` and her coin says so. -/
def fireA : Fact R := fun r t => t = 1 ∧ ∃ b, r = some (b, true)

/-- Bob fires at time 1 iff he received a message in round 1. -/
def fireB : Fact R := fun r t => t = 1 ∧ ∃ c, r = some (true, c)

/-- `φ_both`: both agents are firing. -/
def both : Fact R := fun r t => fireA r t ∧ fireB r t

theorem performs_iff (r : R) : T.Performs fireA r ↔ ∃ b, r = some (b, true) := by
  simp only [PPS.Performs, fireA]
  constructor
  · rintro ⟨_, _, rfl, h⟩; exact h
  · intro h; exact ⟨1, by simp [T, ofTimed], rfl, h⟩

theorem proper : T.Proper fireA :=
  ⟨⟨some (true, true), (performs_iff _).2 ⟨_, rfl⟩⟩, fun _ _ _ _ _ h h' => h.1.trans h'.1.symm⟩

theorem actTime (r : R) (hr : T.Performs fireA r) : T.actTime fireA r = 1 := by
  obtain ⟨t, ht, h1⟩ := hr
  rw [proper.actTime_eq ht h1, h1.1]

open Classical in
theorem prob_R (Q : R → Prop) : T.prob Q = (if Q none then 1 / 2 else 0) +
    ((if Q (some (true, true)) then 99 / 400 else 0) +
      (if Q (some (true, false)) then 99 / 400 else 0) +
      ((if Q (some (false, true)) then 1 / 400 else 0) +
        (if Q (some (false, false)) then 1 / 400 else 0))) := by
  simp only [PPS.prob, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [T, ofTimed, μ]
  norm_num

/-- The protocol satisfies the probabilistic constraint `μ(φ_both@fire_A | fire_A) ≥ 0.99`. -/
theorem cprob_both : T.cprob (T.AtAct both fireA) (T.Performs fireA) = 99 / 100 := by
  have h : ∀ r, T.AtAct both fireA r ↔ r = some (true, true) := by
    intro r
    rw [proper.atAct_iff]
    constructor
    · rintro ⟨hp, ⟨-, b, hb⟩, -, c, hc⟩
      rw [hb] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rw [hb, hc.1]
    · rintro rfl
      have hp : T.Performs fireA (some (true, true)) := (performs_iff _).2 ⟨_, rfl⟩
      exact ⟨hp, by rw [actTime _ hp]; exact ⟨⟨rfl, _, rfl⟩, rfl, _, rfl⟩⟩
  rw [PPS.cprob, prob_R, prob_R]
  simp only [h, performs_iff]
  simp
  norm_num

/-- Alice's belief in `φ_both` when she fires is `0.495` (she does not know her coin yet). -/
theorem beliefAt_both (r : R) (hr : T.Performs fireA r) :
    T.beliefAt .A both fireA r = 99 / 200 := by
  rw [PPS.beliefAt, ite_eq_left hr, actTime r hr, PPS.belief, cprob_at]
  obtain ⟨b, rfl⟩ := (performs_iff r).1 hr
  change T.prob (T.At _ _ (1, info .A (some (b, true)) 1)) /
    T.prob (T.Occurs _ (1, info .A (some (b, true)) 1)) = _
  rw [PPS.prob_congr (fun _ => T_at), PPS.prob_congr (fun _ => T_occurs), prob_R, prob_R]
  simp [info, both, fireA, fireB]
  norm_num

/-- Alice's belief that *Bob* is firing when she fires is `0.99`. -/
theorem belief_fireB (r : R) (hr : T.Performs fireA r) :
    T.beliefAt .A fireB fireA r = 99 / 100 := by
  rw [PPS.beliefAt, ite_eq_left hr, actTime r hr, PPS.belief, cprob_at]
  obtain ⟨b, rfl⟩ := (performs_iff r).1 hr
  change T.prob (T.At _ _ (1, info .A (some (b, true)) 1)) /
    T.prob (T.Occurs _ (1, info .A (some (b, true)) 1)) = _
  rw [PPS.prob_congr (fun _ => T_at), PPS.prob_congr (fun _ => T_occurs), prob_R, prob_R]
  simp [info, fireB]
  norm_num

/-- **The claim of §7 about Example 1 is false.** The paper: "Corollary 7.2 implies that in every
protocol that satisfies this constraint [`μ(φ_both | fire_A) ≥ 0.99`], the probability that Alice's
degree of belief that both are firing together when it decides to fire meets or exceeds `0.9` is at
least `0.9`." In the protocol `Mixed` (which also satisfies the Spec of Example 1) the constraint
holds, but Alice's belief in `φ_both` when she fires is never `≥ 0.9`. (Corollary 7.2 does not apply:
`φ_both` is not local-state independent of `fire_A`.) -/
theorem section7_claim_false :
    T.Proper fireA ∧ (99 / 100 : ℝ) ≤ T.cprob (T.AtAct both fireA) (T.Performs fireA) ∧
      T.cprob (fun r => (9 / 10 : ℝ) ≤ T.beliefAt .A both fireA r) (T.Performs fireA) = 0 ∧
      ¬ T.LocalStateIndependent .A both fireA := by
  have h0 : T.cprob (fun r => (9 / 10 : ℝ) ≤ T.beliefAt .A both fireA r) (T.Performs fireA) = 0 := by
    rw [PPS.cprob, PPS.prob_congr (Q' := fun _ => False)]
    · simp [PPS.prob]
    · intro r
      simp only [iff_false, not_and]
      intro h hp
      rw [beliefAt_both r hp] at h
      norm_num at h
  refine ⟨proper, cprob_both.ge, h0, fun hI => ?_⟩
  have := PPS.corollary_7_2 proper hI (ε := 1 / 10) (by norm_num) (by rw [cprob_both]; norm_num)
  norm_num at this
  rw [h0] at this
  norm_num at this

/-- With the fact "Bob is firing" the conclusion of §7 holds in `Mixed`: Alice believes it with
degree `0.99 ≥ 0.9` whenever she fires. -/
theorem section7_fireB :
    T.cprob (fun r => (9 / 10 : ℝ) ≤ T.beliefAt .A fireB fireA r) (T.Performs fireA) = 1 := by
  rw [PPS.cprob, PPS.prob_congr (Q' := T.Performs fireA), div_self]
  · exact (PPS.prob_pos ((performs_iff _).2 ⟨true, rfl⟩)).ne'
  · intro r
    constructor
    · exact And.right
    · intro hp; exact ⟨by rw [belief_fireB r hp]; norm_num, hp⟩

end Mixed

end Podc.ProbablyApproxKnowing.Example1
