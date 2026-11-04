import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/Timed/Basic.lean

/-!
# Timed message passing with drift-free clocks: runs, shifting, locality

A model of partially synchronous message passing in continuous time, as used in the lower-bound
proofs of Lundelius–Lynch, Attiya–Welch, Kosa, Mavronicolas–Roth and Wang–Welch–Lee (shifting
arguments). Processes `P` have drift-free local clocks: the clock of `p` reads `real + off p`.

* An algorithm (`Algorithm P I R M`) is given by the *local behaviour* of each process: a causal
  function `beh p` from the set of timed local input events (invocations `inv k a` of operation
  `k` with argument `a`, receipts `recv q m`) to the set of timed local output events (responses
  `resp k r`, sends `send q m`), all time stamps being *local clock* times. Causality: the outputs
  up to clock time `τ` only depend on the inputs up to `τ` (closed), and there is no output without
  input (`beh p ∅ = ∅`: processes start quiescent). Every deterministic event-driven automaton
  with timers whose runs are not Zeno induces such a function (tag messages with sequence numbers
  if needed); so lower bounds proved for all `Algorithm`s apply to all such automata.
* A scenario (`Scenario`) fixes the clock offsets, the finitely many operation invocations
  (`Call`: process, id, real invocation time, argument) and the message delays as a function of
  sender, receiver and real send time.
* A run of a scenario (`IsRun`) is a family of local input histories that is a fixpoint of
  "invocations ∪ receipts of the messages sent by the local behaviours", and is bounded below in
  time. If the delays are bounded below by some `γ > 0` the run exists (`exists_run`) and is
  unique (`IsRun.unique`).
* `Scenario.shift s x` moves every event of `p` by `x p` in real time keeping clock times; the
  same local histories form a run of the shifted scenario (`IsRun.shift`): shifting is invisible
  to the processes, and delays change by `x receiver - x sender`.
* `agree_window`: the general *locality* lemma — two runs of scenarios with the same offsets
  agree in a window `[Q p, C p)` of every process if their pre-window parts have the same
  residual behaviour, no pre-window message lands in a window, invocations and delays agree in the
  windows and the cut `C` is causally closed. `agree_of_cut` is the special case with no
  pre-window part (chopping a run).
-/

namespace Cslib.TimedMP

variable {P I R M : Type*}

/-- Local input events of a process. -/
inductive InEv (P I M : Type*) where
  /-- Invocation of the operation with (per-process) id `k` and argument `a`. -/
  | inv (k : ℕ) (a : I)
  /-- Receipt of message `m` from `q`. -/
  | recv (q : P) (m : M)

/-- Local output events of a process. -/
inductive OutEv (P R M : Type*) where
  /-- Response `r` to the operation with id `k`. -/
  | resp (k : ℕ) (r : R)
  /-- Sending message `m` to `q`. -/
  | send (q : P) (m : M)

/-- Two timed event sets agree up to time `τ` (inclusive). -/
def AgreeLe {E : Type*} (h h' : Set (ℝ × E)) (τ : ℝ) : Prop :=
  ∀ e : ℝ × E, e.1 ≤ τ → (e ∈ h ↔ e ∈ h')

/-- Two timed event sets agree strictly before time `τ`. -/
def AgreeLt {E : Type*} (h h' : Set (ℝ × E)) (τ : ℝ) : Prop :=
  ∀ e : ℝ × E, e.1 < τ → (e ∈ h ↔ e ∈ h')

/-- A deterministic algorithm, given by causal local behaviours (in local clock time). -/
structure Algorithm (P I R M : Type*) where
  /-- The outputs of `p` as a function of its inputs. -/
  beh : P → Set (ℝ × InEv P I M) → Set (ℝ × OutEv P R M)
  /-- Causality: outputs up to `τ` depend only on inputs up to `τ`. -/
  causal : ∀ p h h' τ, AgreeLe h h' τ → AgreeLe (beh p h) (beh p h') τ
  /-- No output without input (processes start quiescent). -/
  quiet : ∀ p, beh p ∅ = ∅

namespace Algorithm

variable (A : Algorithm P I R M)

theorem causal_lt (p : P) {h h' : Set (ℝ × InEv P I M)} {τ : ℝ} (hh : AgreeLt h h' τ) :
    AgreeLt (A.beh p h) (A.beh p h') τ := by
  intro o ho
  exact A.causal p h h' o.1 (fun e he => hh e (lt_of_le_of_lt he ho)) o le_rfl

/-- If the input has no event before `τ`, neither has the output. -/
theorem beh_ge (p : P) {h : Set (ℝ × InEv P I M)} {τ : ℝ} (hh : ∀ e ∈ h, τ ≤ e.1)
    {o : ℝ × OutEv P R M} (ho : o ∈ A.beh p h) : τ ≤ o.1 := by
  by_contra hlt
  push_neg at hlt
  have : AgreeLt h ∅ τ := fun e he => by
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun h' => absurd (hh e h') (not_le.mpr he)
  have := (A.causal_lt p this) o hlt
  rw [A.quiet] at this
  exact this.mp ho

end Algorithm

/-- An operation invocation of a scenario: process, per-process id, real time, argument. -/
@[ext]
structure Call (P I : Type*) where
  /-- Invoking process. -/
  p : P
  /-- Identifier (unique per process). -/
  k : ℕ
  /-- Real invocation time. -/
  t : ℝ
  /-- Argument (operation type and argument). -/
  a : I

/-- A scenario: clock offsets, invocations, message delays (sender, receiver, real send time). -/
structure Scenario (P I : Type*) where
  /-- Clock offset: the clock of `p` reads `real + off p`. -/
  off : P → ℝ
  /-- The operation invocations. -/
  calls : List (Call P I)
  /-- `delay q p σ` is the delay of a message sent from `q` to `p` at real time `σ`. -/
  delay : P → P → ℝ → ℝ

namespace Scenario

variable (s : Scenario P I)

/-- Invocation events of `p`, in local clock time. -/
def callEv (p : P) : Set (ℝ × InEv P I M) :=
  {e | ∃ c ∈ s.calls, c.p = p ∧ e = (c.t + s.off p, InEv.inv c.k c.a)}

/-- Receipt events of `p` (in local clock time) of the messages sent in the outputs `O`. -/
def recvEv (O : P → Set (ℝ × OutEv P R M)) (p : P) : Set (ℝ × InEv P I M) :=
  {e | ∃ q σ m, (σ, OutEv.send p m) ∈ O q ∧
    e = (σ - s.off q + s.delay q p (σ - s.off q) + s.off p, InEv.recv q m)}

/-- Real time of a local clock reading of `p`. -/
def real (p : P) (κ : ℝ) : ℝ := κ - s.off p

/-- All delays are at least `γ > 0`. -/
def MinDelay (γ : ℝ) : Prop := 0 < γ ∧ ∀ q p σ, γ ≤ s.delay q p σ

/-- Admissibility: delays in `[d - u, d]`, clock skew at most `ε`. -/
def Admissible (d u ε : ℝ) : Prop :=
  (∀ q p σ, d - u ≤ s.delay q p σ ∧ s.delay q p σ ≤ d) ∧ ∀ p q, |s.off p - s.off q| ≤ ε

/-- Shift every event of `p` by `x p` in real time, keeping its clock times. -/
def shift (x : P → ℝ) : Scenario P I where
  off p := s.off p - x p
  calls := s.calls.map fun c => { c with t := c.t + x c.p }
  delay q p σ := s.delay q p (σ - x q) + x p - x q

end Scenario

/-- One step of the fixpoint equation defining runs. -/
def step (A : Algorithm P I R M) (s : Scenario P I) (H : P → Set (ℝ × InEv P I M)) (p : P) :
    Set (ℝ × InEv P I M) :=
  s.callEv p ∪ s.recvEv (fun q => A.beh q (H q)) p

/-- `H` (local input histories, clock time) is a run of scenario `s`. -/
def IsRun (A : Algorithm P I R M) (s : Scenario P I) (H : P → Set (ℝ × InEv P I M)) : Prop :=
  (∀ p, H p = step A s H p) ∧ ∃ T : ℝ, ∀ p, ∀ e ∈ H p, T ≤ e.1 - s.off p

/-- Agreement of two families in real time (offsets of `s`) strictly before `T`. -/
def AgreeReal (s : Scenario P I) (H H' : P → Set (ℝ × InEv P I M)) (T : ℝ) : Prop :=
  ∀ p e, e.1 - s.off p < T → (e ∈ H p ↔ e ∈ H' p)

section Existence

variable (A : Algorithm P I R M) (s : Scenario P I)

theorem step_agree {γ : ℝ} (hγ : s.MinDelay γ) {H H' : P → Set (ℝ × InEv P I M)} {T : ℝ}
    (h : AgreeReal s H H' T) : AgreeReal s (step A s H) (step A s H') (T + γ) := by
  intro p e he
  simp only [step, Set.mem_union]
  apply or_congr Iff.rfl
  have key : ∀ (H₁ H₂ : P → Set (ℝ × InEv P I M)), AgreeReal s H₁ H₂ T →
      e ∈ s.recvEv (fun q => A.beh q (H₁ q)) p → e ∈ s.recvEv (fun q => A.beh q (H₂ q)) p := by
    intro H₁ H₂ h12 hmem
    obtain ⟨q, σ, m, hσ, hem⟩ := hmem
    refine ⟨q, σ, m, ?_, hem⟩
    subst hem
    have hd := hγ.2 q p (σ - s.off q)
    simp only at he
    have hlt : σ < T + s.off q := by linarith
    have hag : AgreeLt (H₁ q) (H₂ q) (T + s.off q) := fun e' he' => h12 q e' (by linarith)
    exact (A.causal_lt q hag (σ, OutEv.send p m) hlt).mp hσ
  exact ⟨key H H' h, key H' H (fun p e he => (h p e he).symm)⟩

/-- Iterates of the fixpoint step from the empty family. -/
def iter : ℕ → P → Set (ℝ × InEv P I M)
  | 0 => fun _ => ∅
  | j + 1 => step A s (iter j)

/-- A lower bound of all invocation times. -/
noncomputable def t0 : ℝ := (s.calls.map Call.t).foldr min 0

theorem t0_le {c : Call P I} (hc : c ∈ s.calls) : t0 s ≤ c.t := by
  unfold t0
  generalize s.calls = l at hc
  induction l with
  | nil => simp at hc
  | cons c' l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hc)

theorem iter_ge {γ : ℝ} (hγ : s.MinDelay γ) (j : ℕ) :
    ∀ p, ∀ e ∈ iter A s j p, t0 s ≤ e.1 - s.off p := by
  induction j with
  | zero => intro p e he; simp [iter] at he
  | succ j ih =>
    intro p e he
    simp only [iter, step, Set.mem_union] at he
    rcases he with ⟨c, hc, hcp, rfl⟩ | ⟨q, σ, m, hσ, rfl⟩
    · subst hcp; simp only [add_sub_cancel_right]; exact t0_le s hc
    · have h1 : t0 s + s.off q ≤ σ := by
        refine A.beh_ge q (fun e' he' => ?_) hσ
        have := ih q e' he'
        linarith
      have := hγ.2 q p (σ - s.off q)
      have := hγ.1
      simp only
      linarith

theorem iter_agree {γ : ℝ} (hγ : s.MinDelay γ) (j : ℕ) :
    AgreeReal s (iter A s j) (iter A s (j + 1)) (t0 s + j * γ) := by
  induction j with
  | zero =>
    intro p e he
    simp only [Nat.cast_zero, zero_mul, add_zero] at he
    constructor
    · intro h; simp [iter] at h
    · intro h
      exact absurd (iter_ge A s hγ 1 p e h) (not_le.mpr he)
  | succ j ih =>
    have := step_agree A s hγ ih
    intro p e he
    exact this p e (by push_cast at he; linarith)

theorem iter_agree_le {γ : ℝ} (hγ : s.MinDelay γ) {j j' : ℕ} (hjj : j ≤ j') :
    AgreeReal s (iter A s j) (iter A s j') (t0 s + j * γ) := by
  induction j', hjj using Nat.le_induction with
  | base => intro p e _; exact Iff.rfl
  | succ j' hj ih =>
    intro p e he
    refine (ih p e he).trans (iter_agree A s hγ j' p e ?_)
    have : (j : ℝ) ≤ j' := by exact_mod_cast hj
    nlinarith [hγ.1]

/-- The limit of the iterates. -/
noncomputable def limRun (γ : ℝ) : P → Set (ℝ × InEv P I M) := fun p =>
  {e | e ∈ iter A s (⌈(e.1 - s.off p - t0 s) / γ⌉₊ + 1) p}

theorem limRun_agree {γ : ℝ} (hγ : s.MinDelay γ) (j : ℕ) :
    AgreeReal s (limRun A s γ) (iter A s j) (t0 s + j * γ) := by
  intro p e he
  simp only [limRun, Set.mem_ofPred_eq]
  set J := ⌈(e.1 - s.off p - t0 s) / γ⌉₊ + 1
  have hJ : e.1 - s.off p < t0 s + J * γ := by
    have h1 : (e.1 - s.off p - t0 s) / γ ≤ ⌈(e.1 - s.off p - t0 s) / γ⌉₊ := Nat.le_ceil _
    have h2 : e.1 - s.off p - t0 s ≤ ⌈(e.1 - s.off p - t0 s) / γ⌉₊ * γ := by
      rwa [div_le_iff₀ hγ.1] at h1
    simp only [J, Nat.cast_add, Nat.cast_one]
    nlinarith [hγ.1]
  rcases le_total J j with hle | hle
  · exact iter_agree_le A s hγ hle p e hJ
  · exact (iter_agree_le A s hγ hle p e he).symm

theorem limRun_isRun {γ : ℝ} (hγ : s.MinDelay γ) : IsRun A s (limRun A s γ) := by
  refine ⟨fun p => ?_, t0 s, fun p e he => ?_⟩
  · ext e
    -- pick `j` large
    obtain ⟨j, hj⟩ := exists_nat_gt ((e.1 - s.off p - t0 s) / γ)
    have hej : e.1 - s.off p < t0 s + j * γ := by
      rw [div_lt_iff₀ hγ.1] at hj; linarith
    have h1 := limRun_agree A s hγ (j + 1) p e (by push_cast; nlinarith [hγ.1])
    have h2 := step_agree A s hγ (limRun_agree A s hγ j) p e (by linarith [hγ.1])
    rw [h1]
    exact h2.symm
  · have h := limRun_agree A s hγ (⌈(e.1 - s.off p - t0 s) / γ⌉₊ + 1) p e
    simp only [limRun, Set.mem_ofPred_eq] at he
    exact iter_ge A s hγ _ p e he

/-- Runs exist when delays are bounded below by a positive constant. -/
theorem exists_run {γ : ℝ} (hγ : s.MinDelay γ) : ∃ H, IsRun A s H :=
  ⟨limRun A s γ, limRun_isRun A s hγ⟩

end Existence

/-- Same residual behaviour after clock time `κ`: two input histories of `p` (with no events
from `κ` on) lead to the same outputs from `κ` on, whatever inputs arrive from `κ` on. This is
"same local state at `κ`" for a causal behaviour. -/
def SameResidual (f : Set (ℝ × InEv P I M) → Set (ℝ × OutEv P R M))
    (h h' : Set (ℝ × InEv P I M)) (κ : ℝ) : Prop :=
  ∀ c : Set (ℝ × InEv P I M), (∀ e ∈ c, κ ≤ e.1) →
    ∀ o : ℝ × OutEv P R M, κ ≤ o.1 → (o ∈ f (h ∪ c) ↔ o ∈ f (h' ∪ c))

section Locality

variable [Finite P] (A : Algorithm P I R M)

/-- **Locality lemma** (general form). Two runs of scenarios with the same offsets agree in the
windows `[Q p, C p)` (real time) if: their parts before the windows have the same residual
behaviour, no message sent before the window of its sender is received in the window of its
receiver, invocations agree in the windows, delays of messages sent in the windows agree unless
both land after the receiver's cut, and the cut is causally closed. -/
theorem agree_window (s s' : Scenario P I) (hoff : s.off = s'.off)
    {H H' : P → Set (ℝ × InEv P I M)} (hH : IsRun A s H) (hH' : IsRun A s' H')
    {γ : ℝ} (hγ : s.MinDelay γ) (Q C : P → ℝ)
    (hpre : ∀ p, SameResidual (A.beh p) (H p ∩ {e | e.1 < Q p + s.off p})
      (H' p ∩ {e | e.1 < Q p + s.off p}) (Q p + s.off p))
    (hpreMsg : ∀ q r σ (m : M), σ < Q q + s.off q →
      ((σ, OutEv.send r m) ∈ A.beh q (H q) →
        σ - s.off q + s.delay q r (σ - s.off q) < Q r) ∧
      ((σ, OutEv.send r m) ∈ A.beh q (H' q) →
        σ - s.off q + s'.delay q r (σ - s.off q) < Q r))
    (hcalls : ∀ p (e : ℝ × InEv P I M), Q p ≤ e.1 - s.off p → e.1 - s.off p < C p →
      (e ∈ s.callEv p ↔ e ∈ s'.callEv p))
    (hdel : ∀ q r σ, Q q ≤ σ → σ < C q → s.delay q r σ = s'.delay q r σ ∨
      (C r ≤ σ + s.delay q r σ ∧ C r ≤ σ + s'.delay q r σ))
    (hcut : ∀ q r σ, C q ≤ σ → C r ≤ σ + s.delay q r σ ∧ C r ≤ σ + s'.delay q r σ) :
    ∀ p (e : ℝ × InEv P I M), Q p ≤ e.1 - s.off p → e.1 - s.off p < C p →
      (e ∈ H p ↔ e ∈ H' p) := by
  obtain ⟨T₁, hT₁⟩ := hH.2
  obtain ⟨T₂, hT₂⟩ := hH'.2
  set T0 := min T₁ T₂
  -- the statement for real times below `T`
  let Pr : ℝ → Prop := fun T => ∀ p (e : ℝ × InEv P I M), Q p ≤ e.1 - s.off p →
      e.1 - s.off p < C p → e.1 - s.off p < T → (e ∈ H p ↔ e ∈ H' p)
  have base : Pr T0 := by
    intro p e _ _ hT
    constructor
    · intro he; have := hT₁ p e he; exact absurd this (by
        have : T0 ≤ T₁ := min_le_left _ _; linarith)
    · intro he; have := hT₂ p e he; rw [← hoff] at this; exact absurd this (by
        have : T0 ≤ T₂ := min_le_right _ _; linarith)
  -- inputs in the window determine the residual outputs
  have outAgree : ∀ T, Pr T → ∀ q σ (o : OutEv P R M), Q q + s.off q ≤ σ → σ < C q + s.off q →
      σ < T + s.off q → ((σ, o) ∈ A.beh q (H q) ↔ (σ, o) ∈ A.beh q (H' q)) := by
    intro T hT q σ o hQ hC hTσ
    set κ := Q q + s.off q
    have hsplit : ∀ (G : P → Set (ℝ × InEv P I M)),
        G q = (G q ∩ {e | e.1 < κ}) ∪ (G q ∩ {e | κ ≤ e.1}) := by
      intro G; ext e; by_cases h : e.1 < κ
      · simp [h]
      · simp [h, not_lt.mp h]
    have e1 : (σ, o) ∈ A.beh q (H q) ↔
        (σ, o) ∈ A.beh q ((H q ∩ {e | e.1 < κ}) ∪ (H' q ∩ {e | κ ≤ e.1})) := by
      rw [hsplit H] at *
      refine A.causal q _ _ σ ?_ (σ, o) le_rfl
      intro e he
      by_cases hk : e.1 < κ
      · simp [hk, not_le.mpr hk]
      · push_neg at hk
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, not_lt.mpr hk,
          and_false, hk, and_true, false_or]
        exact hT q e (by simp [κ] at hk ⊢; linarith) (by linarith) (by linarith)
    rw [e1, hpre q _ (fun e he => he.2) _ hQ]
    conv_rhs => rw [hsplit H']
  intro p e hQ hC
  have step' : ∀ T, Pr T → Pr (T + γ) := by
    intro T hT p e hQ hC hTe
    rw [hH.1 p, hH'.1 p]
    simp only [step, Set.mem_union]
    apply or_congr (hcalls p e hQ hC)
    constructor
    · rintro ⟨q, σ, m, hσ, rfl⟩
      simp only at hQ hC hTe
      have hd := hγ.2 q p (σ - s.off q)
      -- position of the send
      by_cases hpq : σ < Q q + s.off q
      · have := (hpreMsg q p σ m hpq).1 hσ; linarith
      push_neg at hpq
      by_cases hcq : C q + s.off q ≤ σ
      · have := (hcut q p (σ - s.off q) (by linarith)).1; linarith
      push_neg at hcq
      rcases hdel q p (σ - s.off q) (by linarith) (by linarith) with hdq | hdq
      · refine ⟨q, σ, m, ?_, ?_⟩
        · exact (outAgree T hT q σ _ hpq hcq (by linarith)).mp hσ
        · rw [← hoff, ← hdq]
      · linarith [hdq.1]
    · rintro ⟨q, σ, m, hσ, he⟩
      subst he
      simp only at hQ hC hTe
      rw [← hoff] at hQ hC hTe ⊢
      by_cases hpq : σ < Q q + s.off q
      · have := (hpreMsg q p σ m hpq).2 hσ; linarith
      push_neg at hpq
      by_cases hcq : C q + s.off q ≤ σ
      · have := (hcut q p (σ - s.off q) (by linarith)).2; linarith
      push_neg at hcq
      rcases hdel q p (σ - s.off q) (by linarith) (by linarith) with hdq | hdq
      · have hd := hγ.2 q p (σ - s.off q)
        rw [← hdq] at hTe ⊢
        refine ⟨q, σ, m, ?_, rfl⟩
        exact (outAgree T hT q σ _ hpq hcq (by linarith)).mpr hσ
      · linarith [hdq.2]
  -- induction on `T0 + j γ`
  have all : ∀ j : ℕ, Pr (T0 + j * γ) := by
    intro j
    induction j with
    | zero => simpa using base
    | succ j ih =>
      have := step' _ ih
      simp only [Nat.cast_succ]
      convert this using 1; ring
  obtain ⟨j, hj⟩ := exists_nat_gt ((e.1 - s.off p - T0) / γ)
  rw [div_lt_iff₀ hγ.1] at hj
  exact all j p e hQ hC (by linarith)

end Locality

/-- Shifting does not change the invocation events (in clock time). -/
theorem Scenario.callEv_shift (s : Scenario P I) (x : P → ℝ) (p : P) :
    (s.shift x).callEv (M := M) p = s.callEv p := by
  ext e
  simp only [Scenario.callEv, Scenario.shift, List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, hp, rfl⟩
    exact ⟨c, hc, hp, by simp only at hp ⊢; subst hp; ring_nf⟩
  · rintro ⟨c, hc, rfl, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl, by simp only; ring_nf⟩

section Consequences

variable (A : Algorithm P I R M)

theorem IsRun.lower {A : Algorithm P I R M} {s : Scenario P I} {H : P → Set (ℝ × InEv P I M)}
    (h : IsRun A s H) : ∃ T : ℝ, ∀ p, (∀ e ∈ H p, T ≤ e.1 - s.off p) ∧
      ∀ o ∈ A.beh p (H p), T ≤ o.1 - s.off p := by
  obtain ⟨T, hT⟩ := h.2
  refine ⟨T, fun p => ⟨hT p, fun o ho => ?_⟩⟩
  have := A.beh_ge p (τ := T + s.off p) (fun e he => by have := hT p e he; linarith) ho
  linarith

/-- Shifting a scenario does not change the local histories. -/
theorem IsRun.shift [Finite P] {s : Scenario P I} {H : P → Set (ℝ × InEv P I M)}
    (h : IsRun A s H) (x : P → ℝ) : IsRun A (s.shift x) H := by
  refine ⟨fun p => ?_, ?_⟩
  · suffices hs : step A (s.shift x) H p = step A s H p by rw [hs]; exact h.1 p
    ext e
    simp only [step, Set.mem_union, Scenario.callEv, Scenario.recvEv, Scenario.shift,
      List.mem_map]
    apply or_congr
    · constructor
      · rintro ⟨_, ⟨c, hc, rfl⟩, hp, rfl⟩
        exact ⟨c, hc, hp, by simp only at hp ⊢; subst hp; ring_nf⟩
      · rintro ⟨c, hc, rfl, rfl⟩
        exact ⟨_, ⟨c, hc, rfl⟩, rfl, by simp only; ring_nf⟩
    · constructor
      · rintro ⟨q, σ, m, hσ, rfl⟩
        exact ⟨q, σ, m, hσ, by simp only [Prod.mk.injEq, and_true]; ring_nf⟩
      · rintro ⟨q, σ, m, hσ, rfl⟩
        exact ⟨q, σ, m, hσ, by simp only [Prod.mk.injEq, and_true]; ring_nf⟩
  · obtain ⟨T, hT⟩ := h.2
    obtain ⟨b, hb⟩ : BddBelow (Set.range x) := (Set.finite_range x).bddBelow
    refine ⟨T + b, fun p e he => ?_⟩
    have := hT p e he
    have := hb ⟨p, rfl⟩
    simp only [Scenario.shift]
    linarith

variable [Finite P]

/-- **Chopping**: two runs of scenarios with the same offsets agree before a causally closed cut
`C` if invocations before the cut agree and delays of messages sent before the cut agree (unless
both land after the receiver's cut). -/
theorem agree_of_cut (s s' : Scenario P I) (hoff : s.off = s'.off)
    {H H' : P → Set (ℝ × InEv P I M)} (hH : IsRun A s H) (hH' : IsRun A s' H')
    {γ : ℝ} (hγ : s.MinDelay γ) (C : P → ℝ)
    (hcalls : ∀ p (e : ℝ × InEv P I M), e.1 - s.off p < C p →
      (e ∈ s.callEv p ↔ e ∈ s'.callEv p))
    (hdel : ∀ q r σ, σ < C q → s.delay q r σ = s'.delay q r σ ∨
      (C r ≤ σ + s.delay q r σ ∧ C r ≤ σ + s'.delay q r σ))
    (hcut : ∀ q r σ, C q ≤ σ → C r ≤ σ + s.delay q r σ ∧ C r ≤ σ + s'.delay q r σ) :
    ∀ p (e : ℝ × InEv P I M), e.1 - s.off p < C p → (e ∈ H p ↔ e ∈ H' p) := by
  obtain ⟨T₁, hT₁⟩ := hH.lower
  obtain ⟨T₂, hT₂⟩ := hH'.lower
  set T0 := min T₁ T₂ - 1
  have h1 : T0 < T₁ := by have := min_le_left T₁ T₂; linarith
  have h2 : T0 < T₂ := by have := min_le_right T₁ T₂; linarith
  have empty1 : ∀ p, H p ∩ {e | e.1 < T0 + s.off p} = ∅ := by
    intro p; ext e
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    intro he; have := (hT₁ p).1 e he; linarith
  have empty2 : ∀ p, H' p ∩ {e | e.1 < T0 + s.off p} = ∅ := by
    intro p; ext e
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    intro he; have := (hT₂ p).1 e he; rw [hoff]; linarith
  have key := agree_window A s s' hoff hH hH' hγ (fun _ => T0) C
    (fun p => by rw [empty1, empty2]; intro c _ o _; exact Iff.rfl)
    (fun q r σ m hσ => ⟨fun ho => by have := (hT₁ q).2 _ ho; simp at this; linarith,
      fun ho => by have := (hT₂ q).2 _ ho; simp at this; rw [hoff] at hσ; linarith⟩)
    (fun p e _ hC => hcalls p e hC) (fun q r σ _ hC => hdel q r σ hC) hcut
  intro p e he
  by_cases hlow : T0 ≤ e.1 - s.off p
  · exact key p e hlow he
  · push_neg at hlow
    constructor
    · intro h; have := (hT₁ p).1 e h; linarith
    · intro h; have := (hT₂ p).1 e h; rw [hoff] at hlow; linarith

/-- Outputs agree where inputs agree (strictly before a time). -/
theorem beh_agree {H H' : P → Set (ℝ × InEv P I M)} (p : P) {τ : ℝ}
    (h : ∀ e : ℝ × InEv P I M, e.1 < τ → (e ∈ H p ↔ e ∈ H' p)) :
    ∀ o : ℝ × OutEv P R M, o.1 < τ → (o ∈ A.beh p (H p) ↔ o ∈ A.beh p (H' p)) :=
  A.causal_lt p h

/-- Runs are unique (given a positive minimal delay). -/
theorem IsRun.unique {s : Scenario P I} {H H' : P → Set (ℝ × InEv P I M)} (hH : IsRun A s H)
    (hH' : IsRun A s H') {γ : ℝ} (hγ : s.MinDelay γ) : H = H' := by
  funext p; ext e
  exact agree_of_cut A s s rfl hH hH' hγ (fun _ => e.1 - s.off p + 1)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Or.inl rfl)
    (fun q r σ hσ => by have := hγ.2 q r σ; have := hγ.1; constructor <;> linarith)
    p e (by linarith)

end Consequences

end Cslib.TimedMP
