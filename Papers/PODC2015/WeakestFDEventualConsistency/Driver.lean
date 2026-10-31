import Papers.PODC2015.WeakestFDEventualConsistency.Specs

/-!
# Sequential black-box drivers (skeleton of Algorithms 6 and 7)

Algorithms 6 and 7 of [DGKPS15] (Appendix A) transform one consensus-like abstraction into
another. Both have the same control skeleton, which we model once: a process keeps a counter
`n` (`n = 0`: not started; `n = c + 1`: the current black-box instance is `c`) and some data
`d : D`.

* At its first step the process starts: it invokes instance `0` of the black box with
  `prop p 0 d₀` (and produces some application outputs `startOut p`).
* When the black box returns `x` to the current instance `c` (an input event `(c, x)`), the process
  updates its data to `upd p c x d`, produces the application outputs `respOut p c x d`, and
  invokes instance `c + 1` of the black box with `prop p (c + 1) (upd p c x d)`.
* All other events are ignored. No messages are sent.

Black-box invocations are outputs (`DOut.bb`), black-box responses are input events chosen by the
adversary; the black box is constrained only by hypotheses on `bbHist`.

The main generic facts: the invocations of the black box satisfy the (receptive) usage
assumption `ECHist.ProperUseEIC` whatever the black box does (`bbHist_properUseEIC`), faulty
processes reach only finitely many instances (`exists_bound_of_not_correct`) and correct ones
reach every instance if the black box terminates (`exists_trans_of_correct`).
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

/-- Outputs of a driver: an invocation of the black box, or an application-level output. -/
inductive DOut (X Oa : Type*) where
  /-- Invocation of instance `j` of the black box with `w`. -/
  | bb (j : ℕ) (w : X)
  /-- An application-level output. -/
  | app (o : Oa)

/-- Application-level outputs of a transformation: invocations and responses of the implemented
abstraction. -/
inductive AOut (V : Type*) where
  /-- The application invokes instance `j` with `v`. -/
  | inv (j : ℕ) (v : V)
  /-- `v` is returned to instance `j`. -/
  | resp (j : ℕ) (v : V)

/-- The parameters of a sequential black-box driver. -/
structure Driver (P D X Oa : Type*) where
  /-- Initial data. -/
  d0 : D
  /-- Application outputs of the first step. -/
  startOut : P → List Oa
  /-- New data after the response `x` to the current instance `c`. -/
  upd : P → ℕ → X → D → D
  /-- Application outputs on the response `x` to the current instance `c` (old data `d`). -/
  respOut : P → ℕ → X → D → List Oa
  /-- The value proposed to instance `j` of the black box, given the (new) data. -/
  prop : P → ℕ → D → X

namespace Driver

variable {P D X Oa R : Type*} (Dr : Driver P D X Oa)

/-- One step of a driver. -/
def stepFn (p : P) (s : ℕ × D) (e : Event P Empty (ℕ × X)) :
    (ℕ × D) × Option Empty × List (DOut X Oa) :=
  match s.1, e with
  | 0, _ => ((1, s.2), none, (Dr.startOut p).map .app ++ [.bb 0 (Dr.prop p 0 s.2)])
  | c + 1, .input (j, x) =>
    if j = c then
      ((c + 2, Dr.upd p c x s.2), none,
        (Dr.respOut p c x s.2).map .app ++ [.bb (c + 1) (Dr.prop p (c + 1) (Dr.upd p c x s.2))])
    else (s, none, [])
  | _ + 1, _ => (s, none, [])

lemma stepFn_zero (p : P) (s : ℕ × D) (e : Event P Empty (ℕ × X)) (h : s.1 = 0) :
    Dr.stepFn p s e =
      ((1, s.2), none, (Dr.startOut p).map .app ++ [.bb 0 (Dr.prop p 0 s.2)]) := by
  obtain ⟨a, d⟩ := s; simp only at h; subst h; rfl

lemma stepFn_input (p : P) (s : ℕ × D) (c : ℕ) (x : X) (h : s.1 = c + 1) :
    Dr.stepFn p s (.input (c, x)) =
      ((c + 2, Dr.upd p c x s.2), none,
        (Dr.respOut p c x s.2).map .app ++ [.bb (c + 1) (Dr.prop p (c + 1) (Dr.upd p c x s.2))]) := by
  obtain ⟨a, d⟩ := s; simp only at h; subst h; simp [stepFn]

lemma stepFn_input_ne (p : P) (s : ℕ × D) (c j : ℕ) (x : X) (h : s.1 = c + 1) (hj : j ≠ c) :
    Dr.stepFn p s (.input (j, x)) = (s, none, []) := by
  obtain ⟨a, d⟩ := s; simp only at h; subst h; simp [stepFn, hj]

lemma stepFn_tick (p : P) (s : ℕ × D) (c : ℕ) (h : s.1 = c + 1) :
    Dr.stepFn p s .tick = (s, none, []) := by
  obtain ⟨a, d⟩ := s; simp only at h; subst h; rfl

/-- The driver as an algorithm (it uses no failure detector and sends no messages). -/
def alg (R : Type*) : Algorithm P R Empty (ℕ × X) (DOut X Oa) (ℕ × D) where
  init _ := (0, Dr.d0)
  step p _ s e := Dr.stepFn p s e

variable [DecidableEq P] (r : Run P R (ℕ × X))

/-- The history of the black box: invocations are outputs, responses are input events. -/
def bbHist : ECHist P X where
  inv p j w t := (Dr.alg R).Out r p (.bb j w) t
  resp p j x t := r.σ t = some (p, .input (j, x))

/-- The history of the implemented abstraction (application-level outputs). -/
def appHist {V : Type*} (Dr : Driver P D X (AOut V)) (r : Run P R (ℕ × X)) : ECHist P V where
  inv p j v t := (Dr.alg R).Out r p (.app (.inv j v)) t
  resp p j v t := (Dr.alg R).Out r p (.app (.resp j v)) t

/-- The counter of `p` at time `t`. -/
abbrev n (p : P) (t : ℕ) : ℕ := ((Dr.alg R).st r p t).1

/-- The data of `p` at time `t`. -/
abbrev dat (p : P) (t : ℕ) : D := ((Dr.alg R).st r p t).2

lemma event_recv_none (C : Config P Empty (ℕ × D)) (q : P) (s : ℕ) :
    C.event (.recv q s : Choice P (ℕ × X)) = none := by
  simp only [Config.event]
  rcases C.msg s with _ | ⟨_, m⟩
  · rfl
  · exact m.elim

/-- The three possible effects of time `t` on `p`. -/
lemma step_cases (t : ℕ) (p : P) :
    ((Dr.alg R).st r p (t + 1) = (Dr.alg R).st r p t ∧ ∀ o, ¬ (Dr.alg R).Out r p o t) ∨
    (Dr.n r p t = 0 ∧ (∃ c, r.σ t = some (p, c)) ∧
      (Dr.alg R).st r p (t + 1) = (1, Dr.dat r p t) ∧
      (Dr.alg R).outAt r t =
        (Dr.startOut p).map .app ++ [.bb 0 (Dr.prop p 0 (Dr.dat r p t))]) ∨
    (∃ c x, Dr.n r p t = c + 1 ∧ r.σ t = some (p, .input (c, x)) ∧
      (Dr.alg R).st r p (t + 1) = (c + 2, Dr.upd p c x (Dr.dat r p t)) ∧
      (Dr.alg R).outAt r t = (Dr.respOut p c x (Dr.dat r p t)).map .app ++
        [.bb (c + 1) (Dr.prop p (c + 1) (Dr.upd p c x (Dr.dat r p t)))]) := by
  have hno : ∀ o, ¬ (∃ c, r.σ t = some (p, c)) → ¬ (Dr.alg R).Out r p o t :=
    fun o h h' => h h'.1
  rcases hσ : r.σ t with _ | ⟨q, c⟩
  · refine Or.inl ⟨(Dr.alg R).loc_succ_of_ne r t p (by simp [hσ]), fun o => hno o (by simp [hσ])⟩
  by_cases hq : q = p
  swap
  · have hne : ∀ c', r.σ t ≠ some (p, c') := by
      intro c' h; rw [hσ] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact hq h.1
    exact Or.inl ⟨(Dr.alg R).loc_succ_of_ne r t p hne, fun o => hno o (by simpa using hne)⟩
  subst hq
  rcases he : ((Dr.alg R).cfg r t).event c with _ | e
  · obtain ⟨h1, h2⟩ := (Dr.alg R).cfg_succ_of_event_none r t q c hσ he
    refine Or.inl ⟨by simp [Algorithm.st, h1], fun o ho => ?_⟩
    have := ho.2; rw [h2] at this; simp at this
  obtain ⟨h1, -, h3⟩ := (Dr.alg R).cfg_succ_of_event r t q c e hσ he
  replace h1 : (Dr.alg R).st r q (t + 1) = (Dr.stepFn q ((Dr.alg R).st r q t) e).1 := h1
  replace h3 : (Dr.alg R).outAt r t = (Dr.stepFn q ((Dr.alg R).st r q t) e).2.2 := h3
  rcases hn : Dr.n r q t with _ | k
  · right; left
    refine ⟨rfl, ⟨c, rfl⟩, ?_, ?_⟩
    · rw [h1, stepFn_zero _ _ _ _ hn]
    · rw [h3, stepFn_zero _ _ _ _ hn]
  · cases e with
    | input i =>
      obtain ⟨j, x⟩ := i
      have hc : c = .input (j, x) := by
        cases c with
        | recv q' s' => rw [event_recv_none] at he; simp at he
        | tick => simp [Config.event] at he
        | input i => simp [Config.event] at he; rw [he]
      subst hc
      by_cases hj : j = k
      · subst hj
        right; right
        refine ⟨j, x, rfl, rfl, ?_, ?_⟩
        · rw [h1, stepFn_input _ _ _ _ _ hn]
        · rw [h3, stepFn_input _ _ _ _ _ hn]
      · left
        refine ⟨?_, fun o ho => ?_⟩
        · rw [h1, stepFn_input_ne _ _ _ _ _ _ hn hj]
        · have := ho.2; rw [h3, stepFn_input_ne _ _ _ _ _ _ hn hj] at this; simp at this
    | tick =>
      left
      refine ⟨?_, fun o ho => ?_⟩
      · rw [h1, stepFn_tick _ _ _ _ hn]
      · have := ho.2; rw [h3, stepFn_tick _ _ _ _ hn] at this; simp at this
    | recv q' m => exact m.elim

variable {Dr r}

lemma out_iff' {p : P} {o : DOut X Oa} {t : ℕ} :
    (Dr.alg R).Out r p o t ↔ (∃ c, r.σ t = some (p, c)) ∧ o ∈ (Dr.alg R).outAt r t := Iff.rfl

@[simp] lemma n_zero (p : P) : Dr.n r p 0 = 0 := rfl

@[simp] lemma dat_zero (p : P) : Dr.dat r p 0 = Dr.d0 := rfl

/-- The counter increases by at most one per step. -/
lemma n_succ (p : P) (t : ℕ) :
    Dr.n r p (t + 1) = Dr.n r p t ∨ Dr.n r p (t + 1) = Dr.n r p t + 1 := by
  rcases Dr.step_cases r t p with ⟨h, -⟩ | ⟨h0, -, h, -⟩ | ⟨c, x, hc, -, h, -⟩
  · left; simp [n, h]
  · right; simp only [n, dat] at h h0 ⊢; rw [h, h0]
  · right; simp only [n, dat] at h hc ⊢; rw [h, hc]

lemma n_mono (p : P) {t t' : ℕ} (h : t ≤ t') : Dr.n r p t ≤ Dr.n r p t' := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ t' _ ih => rcases n_succ (Dr := Dr) (r := r) p t' with h | h <;> omega

/-- When the counter does not change, nothing happens. -/
lemma stay_of_n_eq {p : P} {t : ℕ} (h : Dr.n r p (t + 1) = Dr.n r p t) :
    (Dr.alg R).st r p (t + 1) = (Dr.alg R).st r p t ∧ ∀ o, ¬ (Dr.alg R).Out r p o t := by
  rcases Dr.step_cases r t p with h' | ⟨h0, -, h', -⟩ | ⟨c, x, hc, -, h', -⟩
  · exact h'
  · exfalso; simp only [n, dat] at h h0 h'; rw [h', h0] at h; simp at h
  · exfalso; simp only [n, dat] at h hc h'; rw [h', hc] at h; simp at h

/-- A transition from `0`. -/
lemma trans_zero {p : P} {t : ℕ} (h0 : Dr.n r p t = 0) (h1 : Dr.n r p (t + 1) = 1) :
    (∃ c, r.σ t = some (p, c)) ∧ Dr.dat r p (t + 1) = Dr.dat r p t ∧
      (Dr.alg R).outAt r t = (Dr.startOut p).map .app ++ [.bb 0 (Dr.prop p 0 (Dr.dat r p t))] := by
  rcases Dr.step_cases r t p with ⟨h, -⟩ | ⟨-, hσ, h, ho⟩ | ⟨c, x, hc, -, h, -⟩
  · exfalso; simp only [n] at h0 h1; rw [h] at h1; omega
  · exact ⟨hσ, by simp only [dat]; rw [h], ho⟩
  · exfalso; simp only [n] at h0 hc; omega

/-- A transition from `c + 1`: the response to the current instance `c`. -/
lemma trans_succ {p : P} {t c : ℕ} (h0 : Dr.n r p t = c + 1) (h1 : Dr.n r p (t + 1) = c + 2) :
    ∃ x, r.σ t = some (p, .input (c, x)) ∧
      Dr.dat r p (t + 1) = Dr.upd p c x (Dr.dat r p t) ∧
      (Dr.alg R).outAt r t = (Dr.respOut p c x (Dr.dat r p t)).map .app ++
        [.bb (c + 1) (Dr.prop p (c + 1) (Dr.upd p c x (Dr.dat r p t)))] := by
  rcases Dr.step_cases r t p with ⟨h, -⟩ | ⟨h0', -, -, -⟩ | ⟨c', x, hc, hσ, h, ho⟩
  · exfalso; simp only [n] at h0 h1; rw [h] at h1; omega
  · exfalso; simp only [n] at h0 h0'; omega
  · have : c' = c := by simp only [n] at h0 hc; omega
    subst this
    exact ⟨x, hσ, by simp only [dat]; rw [h], ho⟩

/-- A response to the current instance makes a transition. -/
lemma trans_of_input {p : P} {t c : ℕ} {x : X} (hσ : r.σ t = some (p, .input (c, x)))
    (h0 : Dr.n r p t = c + 1) : Dr.n r p (t + 1) = c + 2 := by
  obtain ⟨h1, -, -⟩ := (Dr.alg R).cfg_succ_of_event r t p _ _ hσ (Algorithm.event_input _ _)
  change (Dr.alg R).st r p (t + 1) = (Dr.stepFn p ((Dr.alg R).st r p t) (.input (c, x))).1 at h1
  simp only [n] at h0 ⊢
  rw [h1, stepFn_input _ _ _ _ _ h0]

lemma st_succ_input {p : P} {t c : ℕ} {x : X} (hσ : r.σ t = some (p, .input (c, x)))
    (h0 : Dr.n r p t = c + 1) :
    (Dr.alg R).st r p (t + 1) = (c + 2, Dr.upd p c x (Dr.dat r p t)) := by
  obtain ⟨h1, -, -⟩ := (Dr.alg R).cfg_succ_of_event r t p _ _ hσ (Algorithm.event_input _ _)
  change (Dr.alg R).st r p (t + 1) = (Dr.stepFn p ((Dr.alg R).st r p t) (.input (c, x))).1 at h1
  rw [h1, stepFn_input _ _ _ _ _ h0]

lemma st_succ_tick {p : P} {t c : ℕ} (hσ : r.σ t = some (p, .tick)) (h0 : Dr.n r p t = c + 1) :
    (Dr.alg R).st r p (t + 1) = (Dr.alg R).st r p t := by
  obtain ⟨h1, -, -⟩ := (Dr.alg R).cfg_succ_of_event r t p _ _ hσ (Algorithm.event_tick _)
  change (Dr.alg R).st r p (t + 1) = (Dr.stepFn p ((Dr.alg R).st r p t) .tick).1 at h1
  rw [h1, stepFn_tick _ _ _ _ h0]

lemma st_succ_start {p : P} {t : ℕ} (hσ : r.σ t = some (p, .tick)) (h0 : Dr.n r p t = 0) :
    (Dr.alg R).st r p (t + 1) = (1, Dr.dat r p t) := by
  obtain ⟨h1, -, -⟩ := (Dr.alg R).cfg_succ_of_event r t p _ _ hσ (Algorithm.event_tick _)
  change (Dr.alg R).st r p (t + 1) = (Dr.stepFn p ((Dr.alg R).st r p t) .tick).1 at h1
  rw [h1, stepFn_zero _ _ _ _ h0]

/-- The first step of a process makes a transition. -/
lemma trans_of_zero {p : P} {t : ℕ} {c : Choice P (ℕ × X)} (hσ : r.σ t = some (p, c))
    (hc : ∀ q s, c ≠ .recv q s) (h0 : Dr.n r p t = 0) : Dr.n r p (t + 1) = 1 := by
  have he : ∃ e, ((Dr.alg R).cfg r t).event c = some e := by
    cases c with
    | recv q s => exact absurd rfl (hc q s)
    | tick => exact ⟨_, Algorithm.event_tick _⟩
    | input i => exact ⟨_, Algorithm.event_input _ _⟩
  obtain ⟨e, he⟩ := he
  obtain ⟨h1, -, -⟩ := (Dr.alg R).cfg_succ_of_event r t p _ _ hσ he
  change (Dr.alg R).st r p (t + 1) = (Dr.stepFn p ((Dr.alg R).st r p t) e).1 at h1
  simp only [n] at h0 ⊢
  rw [h1, stepFn_zero _ _ _ _ h0]

/-- Before the first step, the data is the initial one. -/
lemma dat_of_n_zero {p : P} {t : ℕ} (h : Dr.n r p t = 0) : Dr.dat r p t = Dr.d0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h' : Dr.n r p t = 0 := by have := n_mono (Dr := Dr) (r := r) p (show t ≤ t + 1 by omega); omega
    rw [← ih h']
    have := (stay_of_n_eq (Dr := Dr) (r := r) (p := p) (t := t) (by omega)).1
    simp only [dat]; rw [this]

/-- Discrete intermediate values: a counter that passes `m` makes the transition from `m`. -/
lemma exists_trans (p : P) {a b m : ℕ} (hab : a ≤ b) (h1 : Dr.n r p a ≤ m)
    (h2 : m < Dr.n r p b) : ∃ t, a ≤ t ∧ t < b ∧ Dr.n r p t = m ∧ Dr.n r p (t + 1) = m + 1 := by
  induction b, hab using Nat.le_induction with
  | base => omega
  | succ b hb ih =>
    by_cases hm : m < Dr.n r p b
    · obtain ⟨t, h1, h2, h3, h4⟩ := ih hm
      exact ⟨t, h1, by omega, h3, h4⟩
    · rcases n_succ (Dr := Dr) (r := r) p b with h | h
      · omega
      · exact ⟨b, hb, by omega, by omega, by omega⟩

/-- Transitions from a given counter value happen at most once. -/
lemma trans_unique (p : P) {t t' : ℕ} (h : Dr.n r p t = Dr.n r p t')
    (ht : Dr.n r p (t + 1) = Dr.n r p t + 1) (ht' : Dr.n r p (t' + 1) = Dr.n r p t' + 1) :
    t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · have := n_mono (Dr := Dr) (r := r) p (show t + 1 ≤ t' by omega); omega
  · exact heq
  · have := n_mono (Dr := Dr) (r := r) p (show t' + 1 ≤ t by omega); omega

/-- Black-box invocations happen exactly at transitions. -/
lemma out_bb_iff {p : P} {j : ℕ} {w : X} {t : ℕ} :
    (Dr.alg R).Out r p (.bb j w) t ↔
      Dr.n r p t = j ∧ Dr.n r p (t + 1) = j + 1 ∧ w = Dr.prop p j (Dr.dat r p (t + 1)) := by
  constructor
  · intro ho
    rcases Dr.step_cases r t p with ⟨-, h⟩ | ⟨h0, -, h, hout⟩ | ⟨c, x, hc, -, h, hout⟩
    · exact absurd ho (h _)
    · have := ho.2; rw [hout] at this
      simp only [List.mem_append, List.mem_map, List.mem_singleton, reduceCtorEq, and_false,
        exists_false, DOut.bb.injEq, false_or] at this
      obtain ⟨rfl, rfl⟩ := this
      simp only [n, dat] at h0 ⊢; rw [h]; simp [h0]
    · have := ho.2; rw [hout] at this
      simp only [List.mem_append, List.mem_map, List.mem_singleton, reduceCtorEq, and_false,
        exists_false, DOut.bb.injEq, false_or] at this
      obtain ⟨rfl, rfl⟩ := this
      simp only [n, dat] at hc ⊢; rw [h]; simp [hc]
  · rintro ⟨h0, h1, rfl⟩
    rcases j with _ | c
    · obtain ⟨hσ, hd, hout⟩ := trans_zero h0 h1
      refine ⟨hσ, ?_⟩
      rw [hout, hd]; simp
    · obtain ⟨x, hσ, hd, hout⟩ := trans_succ h0 h1
      refine ⟨⟨_, hσ⟩, ?_⟩
      rw [hout, hd]; simp

/-- Application outputs happen exactly at transitions. -/
lemma out_app_iff {p : P} {o : Oa} {t : ℕ} :
    (Dr.alg R).Out r p (.app o) t ↔
      (Dr.n r p t = 0 ∧ (∃ c, r.σ t = some (p, c)) ∧ (∀ q s, r.σ t ≠ some (p, .recv q s)) ∧
        o ∈ Dr.startOut p) ∨
      (∃ c x, Dr.n r p t = c + 1 ∧ r.σ t = some (p, .input (c, x)) ∧
        o ∈ Dr.respOut p c x (Dr.dat r p t)) := by
  constructor
  · intro ho
    rcases Dr.step_cases r t p with ⟨-, h⟩ | ⟨h0, hσ, h, hout⟩ | ⟨c, x, hc, hσ, h, hout⟩
    · exact absurd ho (h _)
    · have := ho.2; rw [hout] at this
      simp only [List.mem_append, List.mem_map, DOut.app.injEq, exists_eq_right,
        List.mem_singleton, reduceCtorEq, or_false] at this
      refine Or.inl ⟨h0, hσ, fun q s hs => ?_, this⟩
      have h1 : Dr.n r p (t + 1) = 1 := by simp only [n] at h0 ⊢; rw [h]
      have := (Dr.alg R).cfg_succ_of_event_none r t p _ hs (event_recv_none _ _ _)
      simp only [n, Algorithm.st] at h1 h0; rw [this.1] at h1; omega
    · have := ho.2; rw [hout] at this
      simp only [List.mem_append, List.mem_map, DOut.app.injEq, exists_eq_right,
        List.mem_singleton, reduceCtorEq, or_false] at this
      exact Or.inr ⟨c, x, hc, hσ, this⟩
  · rintro (⟨h0, ⟨c, hσ⟩, hrecv, ho⟩ | ⟨c, x, hc, hσ, ho⟩)
    · have h1 := trans_of_zero hσ (fun q s h => hrecv q s (h ▸ hσ)) h0
      obtain ⟨-, -, hout⟩ := trans_zero h0 h1
      exact ⟨⟨c, hσ⟩, by rw [hout]; simp [ho]⟩
    · have h1 := trans_of_input hσ hc
      obtain ⟨x', hσ', -, hout⟩ := trans_succ hc h1
      rw [hσ] at hσ'; simp only [Option.some.injEq, Prod.mk.injEq, Choice.input.injEq,
        true_and] at hσ'; subst hσ'
      exact ⟨⟨_, hσ⟩, by rw [hout]; simp [ho]⟩

/-! ### The usage of the black box -/

/-- A response of the black box comes after the invocation of its instance. -/
lemma le_n_of_resp (hR : (Dr.bbHist r).RespAfterInv) {p : P} {j : ℕ} {x : X} {t : ℕ}
    (h : (Dr.bbHist r).resp p j x t) : ∃ t', t' < t ∧ Dr.n r p (t' + 1) = j + 1 ∧
      j + 1 ≤ Dr.n r p t := by
  obtain ⟨w, t', ht', hinv⟩ := hR p j x t h
  obtain ⟨-, h1, -⟩ := out_bb_iff.1 hinv
  exact ⟨t', ht', h1, h1 ▸ n_mono p ht'⟩

/-- If the black box responds to instance `j` at `p`, then `p` makes its transition from
instance `j` (in reaction to a response to `j`). -/
lemma exists_trans_of_resp (hR : (Dr.bbHist r).RespAfterInv) {p : P} {j : ℕ} {x : X} {t : ℕ}
    (h : (Dr.bbHist r).resp p j x t) : ∃ t₁ x₁, t₁ ≤ t ∧ Dr.n r p t₁ = j + 1 ∧
      Dr.n r p (t₁ + 1) = j + 2 ∧ r.σ t₁ = some (p, .input (j, x₁)) := by
  obtain ⟨t', ht', h1, hle⟩ := le_n_of_resp hR h
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · obtain ⟨t₁, -, ht₁, h₁, h₂⟩ := exists_trans (Dr := Dr) (r := r) p (Nat.succ_le_of_lt ht')
      h1.le hlt
    obtain ⟨x₁, hσ, -⟩ := trans_succ h₁ h₂
    exact ⟨t₁, x₁, ht₁.le, h₁, h₂, hσ⟩
  · exact ⟨t, x, le_rfl, heq.symm, trans_of_input h heq.symm, h⟩

/-- **The usage of the black box is proper** (`ProperUseEIC`: instance `j + 1` is invoked
exactly in the step of the first response to `j`), whatever the black box does, as long as
it responds only to invoked instances. -/
theorem bbHist_properUseEIC (hR : (Dr.bbHist r).RespAfterInv) : (Dr.bbHist r).ProperUseEIC where
  inv_once p j v v' t t' h h' := by
    obtain ⟨h0, h1, rfl⟩ := out_bb_iff.1 h
    obtain ⟨h0', h1', rfl⟩ := out_bb_iff.1 h'
    have := trans_unique (Dr := Dr) (r := r) p (h0.trans h0'.symm) (by omega) (by omega)
    subst this; exact ⟨rfl, rfl⟩
  inv_succ p j v t h := by
    obtain ⟨h0, h1, -⟩ := out_bb_iff.1 h
    obtain ⟨x, hσ, -⟩ := trans_succ h0 h1
    refine ⟨x, hσ, fun t' v'' ht' hr => ?_⟩
    obtain ⟨-, -, -, hle⟩ := le_n_of_resp hR hr
    have := n_mono (Dr := Dr) (r := r) p ht'.le
    have h0' : Dr.n r p t' = j + 1 := by omega
    have := trans_unique (Dr := Dr) (r := r) p (h0'.trans h0.symm)
      (by rw [trans_of_input hr h0', h0']) (by omega)
    omega
  resp_inv p j v t h hfirst := by
    obtain ⟨t₁, x₁, ht₁, h₁, h₂, hσ⟩ := exists_trans_of_resp hR h
    rcases Nat.lt_or_eq_of_le ht₁ with hlt | rfl
    · exact absurd hσ (hfirst t₁ x₁ hlt)
    · exact ⟨_, out_bb_iff.2 ⟨h₁, h₂, rfl⟩⟩

/-! ### Faulty processes stop, correct ones progress -/

/-- A faulty process reaches only finitely many instances. -/
lemma exists_bound_of_not_correct (hA : (Dr.alg R).Admissible r) {p : P}
    (hp : ¬ r.F.Correct p) : ∃ N, ∀ t, Dr.n r p t ≤ N := by
  obtain ⟨T, hT⟩ := r.F.exists_crashed_of_not_correct hp
  have hstay : ∀ t, T ≤ t → Dr.n r p t = Dr.n r p T := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih =>
      rw [← ih]
      have : ∀ c, r.σ t ≠ some (p, c) := fun c hσ =>
        hA.alive t p c hσ (r.F.mono ht hT)
      simp only [n]; rw [(Dr.alg R).loc_succ_of_ne r t p this]
  refine ⟨Dr.n r p T, fun t => ?_⟩
  rcases le_total t T with h | h
  · exact n_mono p h
  · exact (hstay t h).le

/-- A bound on the instances reached by the faulty processes. -/
lemma exists_bound_faulty [Finite P] 
    (hA : (Dr.alg R).Admissible r) :
    ∃ N, ∀ p, ¬ r.F.Correct p → ∀ t, Dr.n r p t ≤ N := by
  have : ∀ p, ∃ N, ¬ r.F.Correct p → ∀ t, Dr.n r p t ≤ N := fun p => by
    by_cases hp : r.F.Correct p
    · exact ⟨0, fun h => absurd hp h⟩
    · obtain ⟨N, hN⟩ := exists_bound_of_not_correct hA hp
      exact ⟨N, fun _ => hN⟩
  choose Nf hNf using this
  have := Fintype.ofFinite P
  exact ⟨Finset.univ.sup Nf, fun p hp t =>
    (hNf p hp t).trans (Finset.le_sup (f := Nf) (Finset.mem_univ p))⟩

end Driver

end Podc.WeakestFDEventualConsistency
