import Papers.PODC2014.EventualLinParadox.Basic

/-!
# Implementations, executions and progress conditions (Section 3)

An implementation (`Impl`) of a high-level object gives every process a deterministic program:
`invoke` (the local state after an invocation) and `act` (what a process with a pending
operation does next: access a base object `x` with operation `o` and continue with `k r`, take a
local step, or return a response). Processes may be infinite-state (the paper's programmes are
Turing machines; we do not require computability).

Two semantics:

* **Eventually linearizable base objects** (`elSys`, Theorems 12, Proposition 14,
  Proposition 16). A base access is split into an invocation step and a later response step of
  the same process (the base objects are wait-free: a process with a pending base operation
  can always take its response step). The adversary chooses the responses; an execution is
  *admissible* (`ELAdm`) iff the history of every base object `x` is eventually linearizable
  with respect to `x`'s type.
* **Atomic (linearizable) base objects** (`atSys`, Proposition 18). A base access is one atomic
  step that applies a transition `δ (mem x) o r q'` of the base object's (possibly
  nondeterministic) type; the label records the chosen `(r, q')`.

Both are instances of a deterministic labelled system (`LSys`): an execution is a sequence of
labels `lab : ℕ → Option Lab` (`none` = no step at that time), all enabled (`Proper`). Step `n`
writes its high-level event (if any) at position `n` of the history `hist`, so operations are
named by the step of their invocation. Executions are infinite sequences; a finite execution is
one that is eventually `none` (a process may stop taking steps at any time, i.e. crash).

Progress conditions (`WaitFree`, `ObstructionFree`, `NonBlocking`) and correctness conditions
(`IsLinearizable`, `IsEventuallyLinearizable`) quantify over admissible executions.
-/

namespace Podc.EventualLinParadox

/-- What a process with a pending operation does next. -/
inductive Action (X BOp BRes HRes L : Type) where
  /-- Apply operation `o` to base object `x`, continue in local state `k r` for response `r`. -/
  | call (x : X) (o : BOp) (k : BRes → L)
  /-- A local step to local state `l`. -/
  | loc (l : L)
  /-- Return response `r` and continue in local state `l`. -/
  | ret (r : HRes) (l : L)

/-- An implementation of a high-level object (operations `HOp`, responses `HRes`) from base
objects `X` (operations `BOp`, responses `BRes`), for processes `P` with local states `L`. -/
structure Impl (P HOp HRes X BOp BRes L : Type) where
  /-- Initial local states. -/
  locInit : P → L
  /-- Local state after an invocation. -/
  invoke : P → L → HOp → L
  /-- Next action of a process with a pending operation. -/
  act : P → L → Action X BOp BRes HRes L

/-! ### Deterministic labelled systems and their executions -/

/-- A deterministic labelled system: step `n` from configuration `c` with label `l` either is
disabled (`none`) or yields a new configuration, possibly a high-level event and possibly a
base-object event. -/
structure LSys (C Lab E B : Type) where
  init : C
  step : ℕ → C → Lab → Option (C × Option E × Option B)

namespace LSys

variable {C Lab E B : Type} (S : LSys C Lab E B)

/-- The configuration before step `n`, and the outcome of step `n`. -/
def cfgOut (lab : ℕ → Option Lab) : ℕ → C × Option (C × Option E × Option B)
  | 0 => (S.init, (lab 0).bind (S.step 0 S.init))
  | n + 1 =>
    let c := match (cfgOut lab n).2 with
      | none => (cfgOut lab n).1
      | some (o : C × Option E × Option B) => o.1
    (c, (lab (n + 1)).bind (S.step (n + 1) c))

/-- The configuration before step `n`. -/
def cfg (lab : ℕ → Option Lab) (n : ℕ) : C := (S.cfgOut lab n).1

/-- The outcome of step `n` (`none`: no step or disabled). -/
def out (lab : ℕ → Option Lab) (n : ℕ) : Option (C × Option E × Option B) := (S.cfgOut lab n).2

lemma cfg_zero (lab : ℕ → Option Lab) : S.cfg lab 0 = S.init := rfl

lemma out_eq (lab : ℕ → Option Lab) (n : ℕ) : S.out lab n = (lab n).bind (S.step n (S.cfg lab n)) := by
  cases n <;> rfl

lemma cfg_succ (lab : ℕ → Option Lab) (n : ℕ) :
    S.cfg lab (n + 1) = (S.out lab n).elim (S.cfg lab n) Prod.fst := by
  simp only [cfg, out, cfgOut]
  cases (S.cfgOut lab n).2 <;> rfl

/-- The high-level history of an execution. -/
def hist (lab : ℕ → Option Lab) (n : ℕ) : Option E := (S.out lab n).bind (·.2.1)

/-- The base-object history of an execution. -/
def bhist (lab : ℕ → Option Lab) (n : ℕ) : Option B := (S.out lab n).bind (·.2.2)

/-- All labels of the execution are enabled. -/
def Proper (lab : ℕ → Option Lab) : Prop := ∀ n l, lab n = some l → S.step n (S.cfg lab n) l ≠ none

/-- The execution stopped at time `m` (all later labels removed). -/
def trunc (lab : ℕ → Option Lab) (m : ℕ) : ℕ → Option Lab := fun n => if n < m then lab n else none

lemma cfg_congr {lab lab' : ℕ → Option Lab} {m : ℕ} (h : ∀ n < m, lab n = lab' n) :
    ∀ n ≤ m, S.cfg lab n = S.cfg lab' n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cfg_succ, cfg_succ, out_eq, out_eq, ih (by omega), h n (by omega)]

lemma out_congr {lab lab' : ℕ → Option Lab} {m : ℕ} (h : ∀ n < m, lab n = lab' n) {n : ℕ}
    (hn : n < m) : S.out lab n = S.out lab' n := by
  rw [out_eq, out_eq, S.cfg_congr h n hn.le, h n hn]

lemma hist_congr {lab lab' : ℕ → Option Lab} {m : ℕ} (h : ∀ n < m, lab n = lab' n) {n : ℕ}
    (hn : n < m) : S.hist lab n = S.hist lab' n := by
  simp only [hist, S.out_congr h hn]

lemma bhist_congr {lab lab' : ℕ → Option Lab} {m : ℕ} (h : ∀ n < m, lab n = lab' n) {n : ℕ}
    (hn : n < m) : S.bhist lab n = S.bhist lab' n := by
  simp only [bhist, S.out_congr h hn]

lemma out_none_of_lab {lab : ℕ → Option Lab} {n : ℕ} (h : lab n = none) : S.out lab n = none := by
  rw [out_eq, h]; rfl

lemma trunc_agree (lab : ℕ → Option Lab) (m : ℕ) : ∀ n < m, trunc lab m n = lab n :=
  fun _ hn => if_pos hn

lemma hist_trunc_of_ge (lab : ℕ → Option Lab) {m n : ℕ} (h : m ≤ n) : S.hist (trunc lab m) n = none := by
  simp [hist, S.out_none_of_lab (show trunc lab m n = none from if_neg (by omega))]

lemma bhist_trunc_of_ge (lab : ℕ → Option Lab) {m n : ℕ} (h : m ≤ n) :
    S.bhist (trunc lab m) n = none := by
  simp [bhist, S.out_none_of_lab (show trunc lab m n = none from if_neg (by omega))]

lemma proper_trunc {lab : ℕ → Option Lab} (h : S.Proper lab) (m : ℕ) : S.Proper (trunc lab m) := by
  intro n l hl
  have hn : n < m := by by_contra h'; simp [trunc, h'] at hl
  rw [trunc_agree lab m n hn] at hl
  rw [S.cfg_congr (trunc_agree lab m) n hn.le]
  exact h n l hl

/-- Configurations of the execution that follows `pre` before time `n` and the scheduler `σ`
(a function of the time and the current configuration) from time `n` on. -/
def schedCfg (pre : ℕ → Option Lab) (n : ℕ) (σ : ℕ → C → Option Lab) : ℕ → C
  | 0 => S.init
  | k + 1 =>
    let c := schedCfg pre n σ k
    (((if k < n then pre k else σ k c)).bind (S.step k c)).elim c Prod.fst

/-- The execution that follows `pre` before time `n` and the scheduler `σ` from time `n` on. -/
def sched (pre : ℕ → Option Lab) (n : ℕ) (σ : ℕ → C → Option Lab) : ℕ → Option Lab :=
  fun k => if k < n then pre k else σ k (S.schedCfg pre n σ k)

lemma cfg_sched (pre : ℕ → Option Lab) (n : ℕ) (σ : ℕ → C → Option Lab) (k : ℕ) :
    S.cfg (S.sched pre n σ) k = S.schedCfg pre n σ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cfg_succ, out_eq, ih]
    simp only [schedCfg, sched]

lemma sched_of_lt (pre : ℕ → Option Lab) {n : ℕ} (σ : ℕ → C → Option Lab) {k : ℕ} (h : k < n) :
    S.sched pre n σ k = pre k := if_pos h

lemma sched_of_ge (pre : ℕ → Option Lab) {n : ℕ} (σ : ℕ → C → Option Lab) {k : ℕ} (h : n ≤ k) :
    S.sched pre n σ k = σ k (S.cfg (S.sched pre n σ) k) := by
  rw [cfg_sched]; exact if_neg (by omega)

/-- A scheduled extension of a proper execution is proper if the scheduler only proposes
enabled labels. -/
lemma proper_sched {pre : ℕ → Option Lab} (hpre : S.Proper pre) (n : ℕ) {σ : ℕ → C → Option Lab}
    (hσ : ∀ k c l, σ k c = some l → S.step k c l ≠ none) : S.Proper (S.sched pre n σ) := by
  intro k l hl
  by_cases hk : k < n
  · rw [S.sched_of_lt pre σ hk] at hl
    rw [S.cfg_congr (fun i hi => S.sched_of_lt pre σ (lt_trans hi hk)) k le_rfl]
    exact hpre k l hl
  · rw [S.sched_of_ge pre σ (by omega)] at hl
    exact hσ _ _ _ hl

end LSys

/-! ### Well-formedness from a pending-operation map -/

section WF

variable {P X Op Res : Type} [DecidableEq P]

/-- The step condition relating a history to a map `pend n p` (the operation of `p` pending
before step `n`). -/
def PendStep (H : History P X Op Res) (pend : ℕ → P → Option ℕ) (n : ℕ) : Prop :=
  (H n = none ∧ pend (n + 1) = pend n) ∨
  (∃ p x op, H n = some (.inv p x op) ∧ pend n p = none ∧
    pend (n + 1) = Function.update (pend n) p (some n)) ∨
  (∃ p a r, H n = some (.res a r) ∧ pend n p = some a ∧
    pend (n + 1) = Function.update (pend n) p none)

structure PendInv (H : History P X Op Res) (pend : ℕ → P → Option ℕ) (n : ℕ) : Prop where
  pend_spec : ∀ p a, pend n p = some a →
    a < n ∧ (∃ x op, H a = some (.inv p x op)) ∧ ∀ j < n, ∀ r, H j ≠ some (.res a r)
  done : ∀ p a x op, a < n → H a = some (.inv p x op) → pend n p ≠ some a →
    ∃ j < n, ∃ r, H j = some (.res a r)
  res_lt : ∀ j < n, ∀ a r, H j = some (.res a r) → a < j

lemma pendInv_all {H : History P X Op Res} {pend : ℕ → P → Option ℕ}
    (h0 : ∀ p, pend 0 p = none) (hstep : ∀ n, PendStep H pend n) : ∀ n, PendInv H pend n := by
  intro n
  induction n with
  | zero => exact ⟨fun p a h => by simp [h0] at h, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    rcases hstep n with ⟨hn, hp⟩ | ⟨p₀, x₀, op₀, hn, hp0, hp⟩ | ⟨p₀, a₀, r₀, hn, hp0, hp⟩
    · refine ⟨fun p a h => ?_, fun p a x op ha hH hne => ?_, fun j hj a r hr => ?_⟩
      · rw [hp] at h
        obtain ⟨h1, h2, h3⟩ := ih.pend_spec p a h
        refine ⟨by omega, h2, fun j hj r hr => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h3 j hj r hr
        · rw [hn] at hr; cases hr
      · rw [hp] at hne
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · obtain ⟨j, hj, r, hr⟩ := ih.done p a x op ha hH hne; exact ⟨j, by omega, r, hr⟩
        · rw [hn] at hH; cases hH
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ih.res_lt j hj a r hr
        · rw [hn] at hr; cases hr
    · refine ⟨fun p a h => ?_, fun p a x op ha hH hne => ?_, fun j hj a r hr => ?_⟩
      · rw [hp, Function.update_apply] at h
        split_ifs at h with hpp
        · cases h; subst hpp
          refine ⟨by omega, ⟨x₀, op₀, hn⟩, fun j hj r hr => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · have := ih.res_lt j hj _ r hr; omega
          · rw [hn] at hr; cases hr
        · obtain ⟨h1, h2, h3⟩ := ih.pend_spec p a h
          refine ⟨by omega, h2, fun j hj r hr => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact h3 j hj r hr
          · rw [hn] at hr; cases hr
      · rw [hp, Function.update_apply] at hne
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · split_ifs at hne with hpp
          · subst hpp
            obtain ⟨j, hj, r, hr⟩ := ih.done p a x op ha hH (by rw [hp0]; simp)
            exact ⟨j, by omega, r, hr⟩
          · obtain ⟨j, hj, r, hr⟩ := ih.done p a x op ha hH hne; exact ⟨j, by omega, r, hr⟩
        · rw [hn] at hH; cases hH; simp at hne
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ih.res_lt j hj a r hr
        · rw [hn] at hr; cases hr
    · obtain ⟨ha₀n, ⟨xa, opa, hHa₀⟩, hnores⟩ := ih.pend_spec p₀ a₀ hp0
      refine ⟨fun p a h => ?_, fun p a x op ha hH hne => ?_, fun j hj a r hr => ?_⟩
      · rw [hp, Function.update_apply] at h
        split_ifs at h with hpp
        obtain ⟨h1, ⟨x, op, h2⟩, h3⟩ := ih.pend_spec p a h
        refine ⟨by omega, ⟨x, op, h2⟩, fun j hj r hr => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h3 j hj r hr
        · rw [hn] at hr; cases hr
          rw [hHa₀] at h2; cases h2; exact hpp rfl
      · rw [hp, Function.update_apply] at hne
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · split_ifs at hne with hpp
          · subst hpp
            by_cases haa : a = a₀
            · subst haa; exact ⟨n, by omega, r₀, hn⟩
            · obtain ⟨j, hj, r, hr⟩ := ih.done p a x op ha hH (by rw [hp0]; simpa using Ne.symm haa)
              exact ⟨j, by omega, r, hr⟩
          · obtain ⟨j, hj, r, hr⟩ := ih.done p a x op ha hH hne; exact ⟨j, by omega, r, hr⟩
        · rw [hn] at hH; cases hH
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ih.res_lt j hj a r hr
        · rw [hn] at hr; cases hr; exact ha₀n

/-- A history explained by a pending-operation map is well-formed. -/
theorem wellFormed_of_pend {H : History P X Op Res} (pend : ℕ → P → Option ℕ)
    (h0 : ∀ p, pend 0 p = none) (hstep : ∀ n, PendStep H pend n) : WellFormed H := by
  have I := pendInv_all h0 hstep
  have hres : ∀ j a r, H j = some (.res a r) → ∃ p, pend j p = some a := by
    intro j a r hj
    rcases hstep j with ⟨hn, -⟩ | ⟨p, x, op, hn, -⟩ | ⟨p, a', r', hn, hp, -⟩
    · rw [hn] at hj; cases hj
    · rw [hn] at hj; cases hj
    · rw [hn] at hj; cases hj; exact ⟨p, hp⟩
  refine ⟨fun a j r hj => ?_, fun a j j' r r' hj hj' => ?_, fun a b p x x' op op' ha hb hab => ?_⟩
  · obtain ⟨p, hp⟩ := hres j a r hj
    obtain ⟨h1, ⟨x, op, h2⟩, -⟩ := (I j).pend_spec p a hp
    exact ⟨h1, p, x, op, h2⟩
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · obtain ⟨p, hp⟩ := hres j' a r' hj'
      exact (I j').pend_spec p a hp |>.2.2 j h r hj
    · obtain ⟨p, hp⟩ := hres j a r hj
      exact (I j).pend_spec p a hp |>.2.2 j' h r' hj'
  · have hpb : pend b p = none := by
      rcases hstep b with ⟨hn, -⟩ | ⟨p', x'', op'', hn, hp', -⟩ | ⟨p', a', r', hn, -, -⟩
      · rw [hn] at hb; cases hb
      · rw [hn] at hb; cases hb; exact hp'
      · rw [hn] at hb; cases hb
    obtain ⟨j, hj, r, hr⟩ := (I b).done p a x op hab ha (by rw [hpb]; simp)
    exact ⟨j, r, hj, hr⟩

end WF

/-! ### Correctness and progress conditions for a labelled system -/

namespace LSys

variable {C Lab B P HOp HRes Q : Type} (S : LSys C Lab (Ev P Unit HOp HRes) B) (proc : Lab → P)
  (Adm : (ℕ → Option Lab) → Prop)

/-- Process `p` takes step `n`. -/
def StepBy (lab : ℕ → Option Lab) (n : ℕ) (p : P) : Prop := ∃ l, lab n = some l ∧ proc l = p

/-- Process `p` takes infinitely many steps. -/
def InfSteps (lab : ℕ → Option Lab) (p : P) : Prop := ∀ N, ∃ n ≥ N, StepBy proc lab n p

/-- **Wait-freedom**: every operation of a process that takes infinitely many steps completes. -/
def WaitFree : Prop :=
  ∀ lab, Adm lab → ∀ a p op, S.hist lab a = some (.inv p () op) → InfSteps proc lab p →
    Completed (S.hist lab) a

/-- **Obstruction-freedom**: if from some time on only `p` takes steps, and infinitely many,
then every operation of `p` completes. -/
def ObstructionFree : Prop :=
  ∀ lab, Adm lab → ∀ a p op N, S.hist lab a = some (.inv p () op) →
    (∀ n ≥ N, ∀ l, lab n = some l → proc l = p) → InfSteps proc lab p → Completed (S.hist lab) a

/-- **Non-blocking** (lock-freedom): if an operation is pending at time `N` and steps continue
to be taken, some operation completes after `N`. -/
def NonBlocking : Prop :=
  ∀ lab, Adm lab → ∀ N a p op, S.hist lab a = some (.inv p () op) → a < N →
    (∀ j < N, ∀ r, S.hist lab j ≠ some (.res a r)) → (∀ N', ∃ n ≥ N', lab n ≠ none) →
    ∃ j ≥ N, ∃ b r, S.hist lab j = some (.res b r)

/-- The implementation is **linearizable** (for the type `T`): every admissible history is. -/
def IsLinearizable (T : ObjType Q HOp HRes) : Prop :=
  ∀ lab, Adm lab → Linearizable (fun _ => T) (S.hist lab)

/-- **Definition 4**: the implementation is **eventually linearizable**: every admissible
history is (with a `t` depending on the history). -/
def IsEventuallyLinearizable (T : ObjType Q HOp HRes) : Prop :=
  ∀ lab, Adm lab → EventuallyLinearizable (fun _ => T) (S.hist lab)

variable {S proc Adm}

lemma WaitFree.obstructionFree (h : S.WaitFree proc Adm) : S.ObstructionFree proc Adm :=
  fun lab hlab a p op _ ha _ hinf => h lab hlab a p op ha hinf

end LSys

/-! ### Semantics with eventually linearizable base objects -/

/-- Labels: the environment invokes `op` at `p`; `p` performs its next action (a base
invocation, a local step or a return); the pending base operation of `p` returns `r`. -/
inductive ELab (P HOp BRes : Type) where
  | inv (p : P) (op : HOp)
  | step (p : P)
  | bres (p : P) (r : BRes)

/-- The process taking a step. -/
def ELab.proc {P HOp BRes : Type} : ELab P HOp BRes → P
  | .inv p _ => p
  | .step p => p
  | .bres p _ => p

/-- Configurations: local states, pending high-level operations (by the position of their
invocation) and pending base operations. -/
structure ECfg (P L : Type) where
  loc : P → L
  pend : P → Option ℕ
  bpend : P → Option ℕ

section EL

variable {P HOp HRes X BOp BRes L : Type} [DecidableEq P]

/-- One step of the semantics with eventually linearizable base objects. -/
def elStep (I : Impl P HOp HRes X BOp BRes L) (n : ℕ) (c : ECfg P L) :
    ELab P HOp BRes → Option (ECfg P L × Option (Ev P Unit HOp HRes) × Option (Ev P X BOp BRes))
  | .inv p op =>
    if c.pend p = none then
      some ({ c with loc := Function.update c.loc p (I.invoke p (c.loc p) op),
                     pend := Function.update c.pend p (some n) }, some (.inv p () op), none)
    else none
  | .step p =>
    match c.pend p, c.bpend p with
    | some a, none =>
      match I.act p (c.loc p) with
      | .call x o _ => some ({ c with bpend := Function.update c.bpend p (some n) }, none,
          some (.inv p x o))
      | .loc l => some ({ c with loc := Function.update c.loc p l }, none, none)
      | .ret r l => some ({ c with loc := Function.update c.loc p l,
                                   pend := Function.update c.pend p none }, some (.res a r), none)
    | _, _ => none
  | .bres p r =>
    match c.bpend p with
    | some b =>
      match I.act p (c.loc p) with
      | .call _ _ k => some ({ c with loc := Function.update c.loc p (k r),
                                      bpend := Function.update c.bpend p none }, none,
          some (.res b r))
      | _ => none
    | none => none

/-- The labelled system of an implementation over eventually linearizable base objects. -/
def elSys (I : Impl P HOp HRes X BOp BRes L) :
    LSys (ECfg P L) (ELab P HOp BRes) (Ev P Unit HOp HRes) (Ev P X BOp BRes) :=
  ⟨⟨I.locInit, fun _ => none, fun _ => none⟩, elStep I⟩

/-- Admissible executions over eventually linearizable base objects of types `B x`: all labels
enabled and the history of every base object `x` eventually linearizable. -/
def ELAdm {Q' : Type} (I : Impl P HOp HRes X BOp BRes L) (B : X → ObjType Q' BOp BRes)
    (lab : ℕ → Option (ELab P HOp BRes)) : Prop :=
  (elSys I).Proper lab ∧
    ∀ x, EventuallyLinearizable (fun _ => B x) (restrict ((elSys I).bhist lab) x)

lemma elSys_cfg_succ (I : Impl P HOp HRes X BOp BRes L) (lab : ℕ → Option (ELab P HOp BRes)) (n : ℕ) :
    (elSys I).cfg lab (n + 1) =
      ((lab n).bind (elStep I n ((elSys I).cfg lab n))).elim ((elSys I).cfg lab n) Prod.fst := by
  rw [LSys.cfg_succ, LSys.out_eq]; rfl

lemma elSys_hist (I : Impl P HOp HRes X BOp BRes L) (lab : ℕ → Option (ELab P HOp BRes)) (n : ℕ) :
    (elSys I).hist lab n = ((lab n).bind (elStep I n ((elSys I).cfg lab n))).bind (·.2.1) := by
  rw [LSys.hist, LSys.out_eq]; simp only [elSys]

lemma elSys_bhist (I : Impl P HOp HRes X BOp BRes L) (lab : ℕ → Option (ELab P HOp BRes)) (n : ℕ) :
    (elSys I).bhist lab n = ((lab n).bind (elStep I n ((elSys I).cfg lab n))).bind (·.2.2) := by
  rw [LSys.bhist, LSys.out_eq]; simp only [elSys]

lemma el_pendStep (I : Impl P HOp HRes X BOp BRes L) (lab : ℕ → Option (ELab P HOp BRes)) (n : ℕ) :
    PendStep ((elSys I).hist lab) (fun n => ((elSys I).cfg lab n).pend) n := by
  simp only [PendStep, elSys_hist, elSys_cfg_succ]
  generalize (elSys I).cfg lab n = c
  rcases lab n with _ | l
  · simp
  · cases l with
    | inv p op =>
      simp only [Option.bind_some, elStep]
      split_ifs with h
      · exact Or.inr (Or.inl ⟨p, (), op, rfl, h, rfl⟩)
      · simp
    | step p =>
      simp only [Option.bind_some, elStep]
      rcases hp : c.pend p with _ | a
      · simp
      rcases hb : c.bpend p with _ | b
      swap; · simp
      cases hact : I.act p (c.loc p) with
      | call x o k => simp
      | loc l => simp
      | ret r l => exact Or.inr (Or.inr ⟨p, a, r, rfl, hp, rfl⟩)
    | bres p r =>
      simp only [Option.bind_some, elStep]
      rcases hb : c.bpend p with _ | b
      · simp
      · cases hact : I.act p (c.loc p) <;> simp

lemma el_bpendStep (I : Impl P HOp HRes X BOp BRes L) (lab : ℕ → Option (ELab P HOp BRes)) (n : ℕ) :
    PendStep ((elSys I).bhist lab) (fun n => ((elSys I).cfg lab n).bpend) n := by
  simp only [PendStep, elSys_bhist, elSys_cfg_succ]
  generalize (elSys I).cfg lab n = c
  rcases lab n with _ | l
  · simp
  · cases l with
    | inv p op =>
      simp only [Option.bind_some, elStep]
      split_ifs with h <;> simp
    | step p =>
      simp only [Option.bind_some, elStep]
      rcases hp : c.pend p with _ | a
      · simp
      rcases hb : c.bpend p with _ | b
      swap; · simp
      cases hact : I.act p (c.loc p) with
      | call x o k => exact Or.inr (Or.inl ⟨p, x, o, rfl, hb, rfl⟩)
      | loc l => simp
      | ret r l => simp
    | bres p r =>
      simp only [Option.bind_some, elStep]
      rcases hb : c.bpend p with _ | b
      · simp
      · cases hact : I.act p (c.loc p) with
        | call x o k => exact Or.inr (Or.inr ⟨p, b, r, rfl, hb, rfl⟩)
        | loc l => simp
        | ret r l => simp

/-- Histories of executions are well-formed. -/
theorem el_wellFormed_hist (I : Impl P HOp HRes X BOp BRes L) (lab : ℕ → Option (ELab P HOp BRes)) :
    WellFormed ((elSys I).hist lab) :=
  wellFormed_of_pend _ (fun _ => rfl) (el_pendStep I lab)

theorem el_wellFormed_bhist (I : Impl P HOp HRes X BOp BRes L) (lab : ℕ → Option (ELab P HOp BRes)) :
    WellFormed ((elSys I).bhist lab) :=
  wellFormed_of_pend _ (fun _ => rfl) (el_bpendStep I lab)

end EL

/-! ### Semantics with atomic (linearizable) base objects -/

/-- Labels: the environment invokes `op` at `p`; `p` takes a local step or returns; `p`
atomically applies its pending base access, which returns `r` and leaves the object in state
`q`. -/
inductive ALab (P HOp BRes Q : Type) where
  | inv (p : P) (op : HOp)
  | step (p : P)
  | acc (p : P) (r : BRes) (q : Q)

/-- The process taking a step. -/
def ALab.proc {P HOp BRes Q : Type} : ALab P HOp BRes Q → P
  | .inv p _ => p
  | .step p => p
  | .acc p _ _ => p

/-- Configurations: local states, pending operations and the states of the base objects. -/
structure ACfg (P L X Q : Type) where
  loc : P → L
  pend : P → Option ℕ
  mem : X → Q

section Atomic

variable {P HOp HRes X BOp BRes L Q : Type} [DecidableEq P] [DecidableEq X]

/-- One step of the semantics with atomic base objects of types `B x`. -/
noncomputable def atStep (I : Impl P HOp HRes X BOp BRes L) (B : X → ObjType Q BOp BRes) (n : ℕ)
    (c : ACfg P L X Q) : ALab P HOp BRes Q →
      Option (ACfg P L X Q × Option (Ev P Unit HOp HRes) × Option Empty)
  | .inv p op =>
    if c.pend p = none then
      some ({ c with loc := Function.update c.loc p (I.invoke p (c.loc p) op),
                     pend := Function.update c.pend p (some n) }, some (.inv p () op), none)
    else none
  | .step p =>
    match c.pend p with
    | some a =>
      match I.act p (c.loc p) with
      | .loc l => some ({ c with loc := Function.update c.loc p l }, none, none)
      | .ret r l => some ({ c with loc := Function.update c.loc p l,
                                   pend := Function.update c.pend p none }, some (.res a r), none)
      | .call _ _ _ => none
    | none => none
  | .acc p r q =>
    match c.pend p with
    | some _ =>
      match I.act p (c.loc p) with
      | .call x o k => by
        classical
        exact if (B x).δ (c.mem x) o r q then
          some ({ c with loc := Function.update c.loc p (k r),
                         mem := Function.update c.mem x q }, none, none)
          else none
      | _ => none
    | none => none

/-- The labelled system of an implementation over atomic base objects of types `B x`, with
initial base-object states `m₀`. -/
noncomputable def atSys (I : Impl P HOp HRes X BOp BRes L) (B : X → ObjType Q BOp BRes) (m₀ : X → Q) :
    LSys (ACfg P L X Q) (ALab P HOp BRes Q) (Ev P Unit HOp HRes) Empty :=
  ⟨⟨I.locInit, fun _ => none, m₀⟩, atStep I B⟩

variable (I : Impl P HOp HRes X BOp BRes L) (B : X → ObjType Q BOp BRes) (m₀ : X → Q)

lemma atSys_cfg_succ (lab : ℕ → Option (ALab P HOp BRes Q)) (n : ℕ) :
    (atSys I B m₀).cfg lab (n + 1) =
      ((lab n).bind (atStep I B n ((atSys I B m₀).cfg lab n))).elim
        ((atSys I B m₀).cfg lab n) Prod.fst := by
  rw [LSys.cfg_succ, LSys.out_eq]; rfl

lemma atSys_hist (lab : ℕ → Option (ALab P HOp BRes Q)) (n : ℕ) :
    (atSys I B m₀).hist lab n =
      ((lab n).bind (atStep I B n ((atSys I B m₀).cfg lab n))).bind (·.2.1) := by
  rw [LSys.hist, LSys.out_eq]; rfl

lemma at_pendStep (lab : ℕ → Option (ALab P HOp BRes Q)) (n : ℕ) :
    PendStep ((atSys I B m₀).hist lab) (fun n => ((atSys I B m₀).cfg lab n).pend) n := by
  simp only [PendStep, atSys_hist, atSys_cfg_succ]
  generalize (atSys I B m₀).cfg lab n = c
  rcases lab n with _ | l
  · simp
  · cases l with
    | inv p op =>
      simp only [Option.bind_some, atStep]
      split_ifs with h
      · exact Or.inr (Or.inl ⟨p, (), op, rfl, h, rfl⟩)
      · simp
    | step p =>
      simp only [Option.bind_some, atStep]
      rcases hp : c.pend p with _ | a
      · simp
      cases hact : I.act p (c.loc p) with
      | call x o k => simp
      | loc l => simp
      | ret r l => exact Or.inr (Or.inr ⟨p, a, r, rfl, hp, rfl⟩)
    | acc p r q =>
      simp only [Option.bind_some, atStep]
      rcases hp : c.pend p with _ | a
      · simp
      cases hact : I.act p (c.loc p) with
      | call x o k => simp only; split_ifs <;> simp
      | loc l => simp
      | ret r l => simp

/-- Histories of executions over atomic base objects are well-formed. -/
theorem at_wellFormed_hist (lab : ℕ → Option (ALab P HOp BRes Q)) :
    WellFormed ((atSys I B m₀).hist lab) :=
  wellFormed_of_pend _ (fun _ => rfl) (at_pendStep I B m₀ lab)

lemma at_hist_inv {lab : ℕ → Option (ALab P HOp BRes Q)} {n : ℕ} {p : P} {x : Unit} {op : HOp}
    (h : (atSys I B m₀).hist lab n = some (.inv p x op)) :
    lab n = some (.inv p op) ∧ ((atSys I B m₀).cfg lab n).pend p = none := by
  rw [atSys_hist] at h
  generalize (atSys I B m₀).cfg lab n = c at h ⊢
  rcases hl : lab n with _ | l
  · rw [hl] at h; simp at h
  · rw [hl] at h
    cases l with
    | inv p' op' =>
      simp only [Option.bind_some, atStep] at h
      split_ifs at h with h1
      · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, h1⟩
      · simp at h
    | step p' =>
      simp only [Option.bind_some, atStep] at h
      rcases hp : c.pend p' with _ | a <;> rw [hp] at h
      · simp at h
      · cases hact : I.act p' (c.loc p') <;> rw [hact] at h <;> simp at h
    | acc p' r q =>
      simp only [Option.bind_some, atStep] at h
      rcases hp : c.pend p' with _ | a <;> rw [hp] at h
      · simp at h
      · cases hact : I.act p' (c.loc p') <;> rw [hact] at h
        · simp only at h; split_ifs at h <;> simp at h
        all_goals simp at h

end Atomic

end Podc.EventualLinParadox
