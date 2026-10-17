import Papers.PODC2021.GoodCaseLatencyBB.Basic
import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Unsynchronized start

Abraham–Nayak–Ren–Xiang, PODC 2021, Section 2 ("Clock synchronization") and Section 5.4.

In the *unsynchronized start* model every party starts the protocol (and its local clock) at its
own time; correct parties start at most `σ` apart. We model this on top of the CSLib model:
a protocol is an ordinary `Algorithm P M S V V` (a state machine that, once started, takes one
step per time unit, so it knows its *local* time), and it is run through the wrapper
`lateStart A`, whose input is a pair `(v, k)`: proposal `v`, start time `k`. Before its start
a process sends nothing, takes no steps and drops what it receives (`UValid` forbids correct
processes' messages to arrive before the receiver has started).

Generic tools (CSLib candidates):
* `Run.st_shift_eq`: indistinguishability with a per-process **time shift** and a per-process
  deadline (two runs in which process `p` starts at different times, but sees the same messages
  at the same *local* times).
* `Run.inbox_of_const`: inboxes on links with a constant (effective) delay.
* (the replay lemma for a causally closed set of events is the shared `Run.tokens_replay_rel`,
  `Cslib/Computability/Distributed/Byzantine/PartialSync/Auth.lean`).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P]

/-- The late-start wrapper: input `(v, k)` = proposal `v`, start time `k`. -/
def lateStart (A : Algorithm P M S V V) : Algorithm P M ((V × ℕ) ⊕ S) (V × ℕ) V where
  init p iv := if iv.2 = 0 then .inr (A.init p iv.1) else .inl iv
  step p st ib := st.elim
    (fun vk => if vk.2 ≤ 1 then .inr (A.init p vk.1) else .inl (vk.1, vk.2 - 1))
    (fun x => .inr (A.step p x ib))
  send p st q := st.elim (fun _ => []) (fun x => A.send p x q)
  decide p st := st.elim (fun _ => none) (fun x => A.decide p x)

/-- Start time of `p` in a run of `lateStart A`. -/
def ustart (R : Run P M (V × ℕ)) (p : P) : ℕ := (R.inp p).2

section lateStart

variable {A : Algorithm P M S V V} {R : Run P M (V × ℕ)}

theorem lateStart_st_before (p : P) :
    ∀ τ, τ < ustart R p → R.st (lateStart A) τ p = .inl ((R.inp p).1, ustart R p - τ) := by
  intro τ hτ
  induction τ with
  | zero =>
    simp only [Run.st_zero, lateStart, ustart] at hτ ⊢
    rw [ite_eq_right (by omega)]; rfl
  | succ τ ih =>
    rw [Run.st_succ, ih (by omega)]
    simp only [lateStart, Sum.elim_inl]
    rw [ite_eq_right (by omega)]
    congr 2

theorem lateStart_st_start (p : P) :
    R.st (lateStart A) (ustart R p) p = .inr (A.init p (R.inp p).1) := by
  rcases h : ustart R p with _ | k
  · simp only [Run.st_zero, lateStart]; rw [ite_eq_left (by simpa [ustart] using h)]
  · rw [Run.st_succ, lateStart_st_before p k (by omega)]
    simp only [lateStart, Sum.elim_inl]
    rw [ite_eq_left (by omega)]

theorem lateStart_st_after (p : P) :
    ∀ τ, ustart R p ≤ τ → ∃ x, R.st (lateStart A) τ p = .inr x := by
  intro τ hτ
  induction τ, hτ using Nat.le_induction with
  | base => exact ⟨_, lateStart_st_start p⟩
  | succ τ _ ih =>
    obtain ⟨x, hx⟩ := ih
    exact ⟨_, by rw [Run.st_succ, hx]; rfl⟩

theorem lateStart_out_before {q : P} (hq : q ∉ R.faulty) {τ : ℕ} (hτ : τ < ustart R q) (p : P) :
    R.out (lateStart A) q τ p = [] := by
  rw [Run.out_of_correct _ _ hq, lateStart_st_before q τ hτ]; rfl

end lateStart

/-- A run of the **unsynchronized start** model with at most `f` faults, (effective) delay bound
`d` between correct processes, and clock skew at most `σ` between correct processes. Correct
processes' messages arrive after the receiver has started. -/
structure UValid (f d σ : ℕ) (R : Run P M (V × ℕ)) : Prop where
  card_faulty : R.faulty.card ≤ f
  dl_ge : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → τ ≤ R.dl q τ p
  dl_lt : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → R.dl q τ p < τ + d
  dl_start : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → ustart R p ≤ R.dl q τ p
  skew : ∀ p q, p ∉ R.faulty → q ∉ R.faulty → ustart R p ≤ ustart R q + σ

/-- Runs of the unsynchronized-start model. -/
def unsyncRuns (f d σ : ℕ) : Set (Run P M (V × ℕ)) := {R | UValid f d σ R}

/-- Good-case runs with synchronized start: all correct processes start at time `0`. -/
def unsyncGood (f d : ℕ) : Set (Run P M (V × ℕ)) :=
  {R | UValid f d 0 R ∧ ∀ p ∉ R.faulty, ustart R p = 0}

/-- **Good-case latency under unsynchronized start** (Definition 6): in every admissible run with
an honest broadcaster, every honest process commits within time `T` after the broadcaster starts. -/
def LatencyFromStart {M S K : Type*} (Au : Auth P M K) (A : Algorithm P M S (V × ℕ) V) (s : P)
    (Adm : Set (Run P M (V × ℕ))) (T : ℕ) : Prop :=
  ∀ R ∈ Adm, R.AuthValid Au A → s ∉ R.faulty → ∀ p ∉ R.faulty, CommitsBy A R p (ustart R s + T)

/-- **Byzantine reliable broadcast** in the unsynchronized-start model (the broadcaster's value
is the first component of its input). -/
structure IsBRBU (Au : Auth P M K) (A : Algorithm P M S V V) (s : P)
    (Adm : Set (Run P M (V × ℕ))) : Prop where
  agreement : ∀ R ∈ Adm, R.AuthValid Au (lateStart A) → ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w,
    R.Decides (lateStart A) p v → R.Decides (lateStart A) q w → v = w
  validity : ∀ R ∈ Adm, R.AuthValid Au (lateStart A) → s ∉ R.faulty → ∀ p ∉ R.faulty,
    R.Decides (lateStart A) p (R.inp s).1
  termination : ∀ R ∈ Adm, R.AuthValid Au (lateStart A) →
    (∃ p ∉ R.faulty, ∃ v, R.Decides (lateStart A) p v) →
    ∀ p ∉ R.faulty, ∃ v, R.Decides (lateStart A) p v

/-! ### Generic tools -/

section generic

variable {VI VO : Type*} (A : Algorithm P M S VI VO)

-- CSLib candidate
/-- **Indistinguishability with time shifts.** Each `p ∈ X` is compared at time `τ` of `R` (for
`o p ≤ τ ≤ T p`) with time `τ + o' p - o p` of `R'`. If the states agree at the offsets, and the
inboxes agree whenever all earlier comparisons hold, then all comparisons hold. -/
theorem Run.st_shift_eq (R R' : Run P M VI) {X : Set P} (o o' T : P → ℕ)
    (h0 : ∀ p ∈ X, o p ≤ T p → R.st A (o p) p = R'.st A (o' p) p)
    (hin : ∀ τ, (∀ r ∈ X, ∀ σ ≤ τ, o r ≤ σ → σ ≤ T r → R.st A σ r = R'.st A (σ + o' r - o r) r) →
      ∀ p ∈ X, o p ≤ τ → τ < T p → R.inbox A p τ = R'.inbox A p (τ + o' p - o p)) :
    ∀ τ, ∀ p ∈ X, o p ≤ τ → τ ≤ T p → R.st A τ p = R'.st A (τ + o' p - o p) p := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro p hp hoτ hτT
    rcases Nat.eq_or_lt_of_le hoτ with h | h
    · subst h; rw [h0 p hp hτT]; congr 1; omega
    · obtain ⟨τ', rfl⟩ : ∃ τ', τ = τ' + 1 := ⟨τ - 1, by omega⟩
      have e : τ' + 1 + o' p - o p = (τ' + o' p - o p) + 1 := by omega
      rw [e, Run.st_succ, Run.st_succ, ih τ' (by omega) p hp (by omega) (by omega),
        hin τ' (fun r hr σ hσ h1 h2 => ih σ (by omega) r hr h1 h2) p hp (by omega) (by omega)]

/-- On a link with constant effective delay `c ≥ 1`, the inbox is the batch sent `c` time units
earlier (`Run.inbox_of_dl_eq_add` with offset `c - 1`). -/
theorem Run.inbox_of_const (R : Run P M VI) {q p : P} {c : ℕ} (hc : 1 ≤ c)
    (hdl : ∀ t, R.dl q t p = t + c - 1) (τ : ℕ) :
    R.inbox A p τ q = if c ≤ τ + 1 then R.out A q (τ + 1 - c) p else [] := by
  rw [Run.inbox_of_dl_eq_add A (e := c - 1) fun t => by rw [hdl]; omega]
  split_ifs <;> first | omega | rfl | congr 1; omega

end generic

end GoodCaseLatencyBB
