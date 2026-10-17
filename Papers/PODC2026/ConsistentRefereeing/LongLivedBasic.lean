import Papers.PODC2026.ConsistentRefereeing.Defs
import Cslib.Computability.Distributed.SharedMemory.Covering

/-!
# Long-lived contest: setting, schedules, and the decide entry (Section 5 of [ACE26])

Infrastructure for the impossibility results of Section 5 of Attiya, Castañeda, Enea,
*Impossibility Results for Strong Linearizability: The Difficulty of Consistent Refereeing*
(PODC 2026, arXiv 2506.18401), cited as [ACE26].

We fix (`LLCtx`) an implementation `I` of the long-lived contest object from arbitrary base
objects, the referee `ref`, and a prefix-closed linearization function `h` (w.r.t. the
nondeterministic specification `llSpec`) on the admissible executions (`LLAdm ref`: competitors
only invoke `compete`, the referee invokes `decide` at most once), together with wait-freedom on
admissible executions. All of Section 5 happens inside this context.

## Schedules

In an admissible execution every process has at most one possible next label:
* a competitor `q` that is idle can only invoke `compete q`; a pending process can only take its
  (deterministic) next step `I.nextLabel C q`;
* the referee invokes `decide` if it has not invoked yet, takes its next step if pending, and has
  nothing to do once `decide` returned.

Hence (admissible) extensions of an execution `α` are exactly the label lists obtained from
*schedules* (`List P`, or `ℕ → P` for infinite extensions): `X.ext α σ` lets the processes of
`σ` take their next label in turn (`X.nl`). The paper's "`αq`" is `X.ext α [q]`, a
"competitors-only extension" is `X.ext α σ` with `X.Comp σ` (no referee in `σ`).

## Main definitions

* `LLCtx` — the context; `X.Good α` — `α` is a valid admissible execution.
* `X.nl`, `X.ext1`, `X.extL`, `X.ext` — next label and schedule extensions.
* `X.Dec α x` — `decide()` appears in `h α` with output `x`; `X.DecIn α` — it appears.
* `X.not_dec_of_resps` — if `decide` does not appear in `h α` and some competitor has completed
  more than `x` operations in `α`, no extension has `decide` with output `x` in its
  linearization (the counting argument used throughout Section 5).
* `X.transfer` — schedules of processes of `Q` produce the same labels from executions whose
  final configurations agree on `Q`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Referee

open Impl

/-- Labels of executions of long-lived contest implementations. -/
abbrev LLabel (P : Type) := Label P (llObj P)

/-- The setting of Section 5 of [ACE26]: a wait-free (on admissible executions) implementation
`I` of the long-lived contest object with referee `ref`, and a prefix-closed linearization
function `h` on admissible executions w.r.t. the nondeterministic specification `llSpec P`
(i.e. the data of `I.NStrongLinOn (llSpec P) (LLAdm ref)`). -/
structure LLCtx (P ι L : Type) (B : ι → ObjSpec) [DecidableEq P] [DecidableEq ι] where
  /-- The implementation. -/
  I : Impl (llObj P) B P L
  /-- The referee. -/
  ref : P
  /-- The prefix-closed linearization function. -/
  h : List (LLabel P) → List (OpId P × ContestOp P × LLResp)
  allow : ∀ p, I.allowed p (roleOp ref p)
  wf : I.WaitFreeOn (LLAdm ref)
  lin : ∀ α, I.Valid α → LLAdm ref α → IsNLinearization (llSpec P) α (h α)
  pc : ∀ α β, I.Valid β → LLAdm ref β → α <+: β → h α <+: h β

namespace LLCtx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] (X : LLCtx P ι L B)

/-! ### Good executions and their configurations -/

/-- `α` is a valid admissible execution. -/
def Good (α : List (LLabel P)) : Prop := X.I.Valid α ∧ LLAdm X.ref α

/-- The final configuration of `α` (meaningful for valid `α`). -/
noncomputable def cfg (α : List (LLabel P)) : Config (llObj P) B P L :=
  (X.I.run α).getD X.I.initCfg

variable {X}

lemma Good.run {α : List (LLabel P)} (h : X.Good α) : X.I.run α = some (X.cfg α) := by
  obtain ⟨C, hC⟩ := h.1
  simp [cfg, hC]

lemma Good.of_prefix {α β : List (LLabel P)} (h : X.Good β) (hp : α <+: β) : X.Good α := by
  obtain ⟨γ, rfl⟩ := hp
  exact ⟨X.I.valid_of_prefix h.1 (List.prefix_append _ _), h.2.of_append⟩

lemma good_nil : X.Good [] :=
  ⟨⟨_, rfl⟩, ⟨fun p o ho => by simp [opsOf] at ho, by simp [opsOf]⟩⟩

lemma cfg_nil : X.cfg [] = X.I.initCfg := rfl

/-- Counting invariant for the referee: at most one invocation. -/
lemma Good.ref_counts {α : List (LLabel P)} (h : X.Good α) :
    ((X.cfg α).pend X.ref = none ∧ (opsOf α X.ref).length = (respsOf α X.ref).length) ∨
    ((X.cfg α).pend X.ref ≠ none ∧ (opsOf α X.ref).length = 1 ∧ respsOf α X.ref = []) := by
  have h1 := h.2.once
  rcases X.I.run_counts h.run X.ref with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a, b⟩
  · refine Or.inr ⟨a, by omega, ?_⟩
    rw [← List.length_eq_zero_iff]; omega

lemma Good.pend_ref_ne_none_iff {α : List (LLabel P)} (h : X.Good α) :
    (X.cfg α).pend X.ref ≠ none ↔ opsOf α X.ref ≠ [] ∧ respsOf α X.ref = [] := by
  rcases h.ref_counts with ⟨a, b⟩ | ⟨a, b, c⟩
  · simp only [a, ne_eq, not_true_eq_false, false_iff, not_and]
    intro h1 h2
    rw [h2] at b; simp at b; exact h1 b
  · simp only [ne_eq, a, not_false_eq_true, true_iff, c, and_true]
    intro h1; rw [h1] at b; simp at b

/-- Operations of a competitor are `compete`s, the referee's are `decide`s. -/
lemma Good.op_mem {α : List (LLabel P)} (h : X.Good α) {p : P} {o : ContestOp P}
    (ho : o ∈ opsOf α p) : o = roleOp X.ref p := h.2.role p o ho

/-! ### Next labels and schedule extensions -/

variable (X)

/-- The next label of `p` after `α` (see the module docstring); `none` iff `p` is the referee
and its `decide` has returned. -/
noncomputable def nl (α : List (LLabel P)) (p : P) : Option (LLabel P) :=
  if (X.cfg α).pend p = none then
    (if p = X.ref ∧ opsOf α X.ref ≠ [] then none else some (.inv p (roleOp X.ref p)))
  else some (X.I.nextLabel (X.cfg α) p)

/-- Extension of `α` by one step of `p`. -/
noncomputable def ext1 (α : List (LLabel P)) (p : P) : List (LLabel P) := α ++ (X.nl α p).toList

/-- The labels added by the schedule `σ`. -/
noncomputable def extL : List (LLabel P) → List P → List (LLabel P)
  | _, [] => []
  | α, p :: σ => (X.nl α p).toList ++ extL (X.ext1 α p) σ

/-- Extension of `α` by the schedule `σ` (the paper's `ασ`). -/
noncomputable def ext (α : List (LLabel P)) (σ : List P) : List (LLabel P) := α ++ X.extL α σ

/-- `σ` is a competitors-only schedule. -/
def Comp (σ : List P) : Prop := ∀ p ∈ σ, p ≠ X.ref

/-- The first `n` entries of an infinite schedule. -/
def pre (s : ℕ → P) (n : ℕ) : List P := (List.range n).map s

variable {X}

@[simp] lemma ext_nil (α : List (LLabel P)) : X.ext α [] = α := by simp [ext, extL]

lemma ext_cons (α : List (LLabel P)) (p : P) (σ : List P) :
    X.ext α (p :: σ) = X.ext (X.ext1 α p) σ := by
  simp [ext, extL, ext1]

lemma ext_singleton (α : List (LLabel P)) (p : P) : X.ext α [p] = X.ext1 α p := by
  rw [ext_cons, ext_nil]

lemma ext_append (α : List (LLabel P)) (σ τ : List P) :
    X.ext α (σ ++ τ) = X.ext (X.ext α σ) τ := by
  induction σ generalizing α with
  | nil => simp
  | cons p σ ih => rw [List.cons_append, ext_cons, ext_cons, ih]

lemma ext_eq_append (α : List (LLabel P)) (σ : List P) : X.ext α σ = α ++ X.extL α σ := rfl

lemma extL_append (α : List (LLabel P)) (σ τ : List P) :
    X.extL α (σ ++ τ) = X.extL α σ ++ X.extL (X.ext α σ) τ := by
  have h := ext_append (X := X) α σ τ
  simp only [ext_eq_append, List.append_assoc] at h
  exact List.append_cancel_left h

lemma prefix_ext (α : List (LLabel P)) (σ : List P) : α <+: X.ext α σ := List.prefix_append _ _

lemma ext_prefix_ext (α : List (LLabel P)) (σ τ : List P) : X.ext α σ <+: X.ext α (σ ++ τ) := by
  rw [ext_append]; exact prefix_ext _ _

lemma comp_append {σ τ : List P} : X.Comp (σ ++ τ) ↔ X.Comp σ ∧ X.Comp τ := by
  simp only [Comp, List.mem_append]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp

lemma comp_nil : X.Comp [] := fun _ h => by simp at h

lemma comp_singleton {q : P} (hq : q ≠ X.ref) : X.Comp [q] := by
  intro p hp; simp at hp; rw [hp]; exact hq

lemma comp_replicate {q : P} (hq : q ≠ X.ref) (k : ℕ) : X.Comp (List.replicate k q) := by
  intro p hp; rw [List.eq_of_mem_replicate hp]; exact hq

lemma pre_succ (s : ℕ → P) (n : ℕ) : pre s (n + 1) = pre s n ++ [s n] := by
  simp [pre, List.range_succ]

lemma pre_zero (s : ℕ → P) : pre s 0 = [] := rfl

lemma length_pre (s : ℕ → P) (n : ℕ) : (pre s n).length = n := by simp [pre]

lemma comp_pre {s : ℕ → P} (hs : ∀ n, s n ≠ X.ref) (n : ℕ) : X.Comp (pre s n) := by
  intro p hp; simp only [pre, List.mem_map, List.mem_range] at hp
  obtain ⟨m, -, rfl⟩ := hp; exact hs m

lemma pre_prefix (s : ℕ → P) {m n : ℕ} (h : m ≤ n) : pre s m <+: pre s n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => rw [pre_succ]; exact ih.trans (List.prefix_append _ _)

lemma pre_add (s : ℕ → P) (m n : ℕ) : pre s (m + n) = pre s m ++ pre (fun i => s (m + i)) n := by
  induction n with
  | zero => simp [pre]
  | succ n ih => rw [← Nat.add_assoc, pre_succ, ih, pre_succ, List.append_assoc]

lemma pre_const (q : P) (n : ℕ) : pre (fun _ => q) n = List.replicate n q := by
  simp [pre]

lemma ext_prefix_of_prefix (α : List (LLabel P)) {σ τ : List P} (h : σ <+: τ) :
    X.ext α σ <+: X.ext α τ := by
  obtain ⟨u, rfl⟩ := h; exact ext_prefix_ext _ _ _

/-! ### Basic properties of next labels -/

lemma nl_of_pend {α : List (LLabel P)} {p : P} (h : (X.cfg α).pend p ≠ none) :
    X.nl α p = some (X.I.nextLabel (X.cfg α) p) := by
  simp [nl, h]

lemma nl_of_idle_comp {α : List (LLabel P)} {p : P} (h : (X.cfg α).pend p = none)
    (hp : p ≠ X.ref) : X.nl α p = some (.inv p (.compete p)) := by
  simp [nl, h, hp, roleOp]

lemma nl_isSome_of_ne {α : List (LLabel P)} {p : P} (hp : p ≠ X.ref) : (X.nl α p).isSome := by
  unfold nl; split_ifs with h1 h2
  · exact absurd h2.1 hp
  · rfl
  · rfl

lemma nl_proc {α : List (LLabel P)} {p : P} {ℓ : LLabel P} (h : X.nl α p = some ℓ) :
    ℓ.proc = p := by
  unfold nl at h; split_ifs at h with h1 h2
  · cases h; rfl
  · cases h; exact X.I.nextLabel_proc _ _

/-- One step of a schedule keeps executions good, and the configuration evolves by `step`. -/
lemma Good.nl_step {α : List (LLabel P)} (hα : X.Good α) {p : P} {ℓ : LLabel P}
    (h : X.nl α p = some ℓ) :
    X.I.step (X.cfg α) ℓ = some (X.cfg (α ++ [ℓ])) ∧ X.Good (α ++ [ℓ]) := by
  classical
  have key : ∃ C', X.I.step (X.cfg α) ℓ = some C' := by
    unfold nl at h
    split_ifs at h with h1 h2
    · cases h
      apply Option.isSome_iff_exists.1
      simp [step, h1, X.allow p]
    · cases h
      exact Option.isSome_iff_exists.1 (X.I.step_nextLabel_isSome _ p h1)
  obtain ⟨C', hC'⟩ := key
  have hrun : X.I.run (α ++ [ℓ]) = some C' := by
    rw [run_append_of_eq _ hα.run, runFrom_singleton, hC']
  have hv : X.I.Valid (α ++ [ℓ]) := ⟨C', hrun⟩
  have hcfg : X.cfg (α ++ [ℓ]) = C' := by simp [cfg, hrun]
  refine ⟨by rw [hcfg, hC'], hv, ?_, ?_⟩
  · intro q o ho
    rw [opsOf_append] at ho
    rcases List.mem_append.1 ho with ho | ho
    · exact hα.2.role q o ho
    · unfold nl at h
      split_ifs at h with h1 h2
      · cases h
        simp only [opsOf_cons, opsOf_nil, Label.invOf_inv, List.append_nil] at ho
        by_cases hq : p = q
        · subst hq; simpa using ho
        · simp [hq] at ho
      · cases h
        simp [opsOf_cons, X.I.nextLabel_invOf] at ho
  · rw [opsOf_append, List.length_append]
    have h0 := hα.2.once
    unfold nl at h
    split_ifs at h with h1 h2
    · cases h
      by_cases hp : p = X.ref
      · subst hp
        have : opsOf α X.ref = [] := by
          by_contra hne; exact h2 ⟨rfl, hne⟩
        simp [this]
      · simp [opsOf_cons, hp]; omega
    · cases h
      simp [opsOf_cons, X.I.nextLabel_invOf]; omega

lemma Good.ext1 {α : List (LLabel P)} (hα : X.Good α) (p : P) : X.Good (X.ext1 α p) := by
  unfold LLCtx.ext1
  cases h : X.nl α p with
  | none => simpa using hα
  | some ℓ => exact (hα.nl_step h).2

lemma Good.ext {α : List (LLabel P)} (hα : X.Good α) (σ : List P) : X.Good (X.ext α σ) := by
  induction σ generalizing α with
  | nil => simpa using hα
  | cons p σ ih => rw [ext_cons]; exact ih (hα.ext1 p)

lemma ext1_of_none {α : List (LLabel P)} {p : P} (h : X.nl α p = none) : X.ext1 α p = α := by
  simp [LLCtx.ext1, h]

lemma ext1_of_some {α : List (LLabel P)} {p : P} {ℓ : LLabel P} (h : X.nl α p = some ℓ) :
    X.ext1 α p = α ++ [ℓ] := by
  simp [LLCtx.ext1, h]

/-- A step of `p` does not change the other processes. -/
lemma Good.ext1_other {α : List (LLabel P)} (hα : X.Good α) {p q : P} (hq : q ≠ p) :
    (X.cfg (X.ext1 α p)).loc q = (X.cfg α).loc q ∧
      (X.cfg (X.ext1 α p)).pend q = (X.cfg α).pend q := by
  cases h : X.nl α p with
  | none => rw [ext1_of_none h]; exact ⟨rfl, rfl⟩
  | some ℓ =>
    rw [ext1_of_some h]
    exact step_other (hα.nl_step h).1 (by rw [nl_proc h]; exact Ne.symm hq)

/-- Steps of processes outside `σ` do not change `q`. -/
lemma Good.ext_other {α : List (LLabel P)} (hα : X.Good α) {q : P} {σ : List P}
    (hq : q ∉ σ) :
    (X.cfg (X.ext α σ)).loc q = (X.cfg α).loc q ∧
      (X.cfg (X.ext α σ)).pend q = (X.cfg α).pend q := by
  induction σ generalizing α with
  | nil => simp
  | cons p σ ih =>
    rw [ext_cons]
    have hq' : q ∉ σ := fun h => hq (List.mem_cons_of_mem _ h)
    have hqp : q ≠ p := fun h => hq (by rw [h]; exact List.mem_cons_self)
    obtain ⟨h1, h2⟩ := ih (hα.ext1 p) hq'
    obtain ⟨h3, h4⟩ := hα.ext1_other hqp
    exact ⟨h1.trans h3, h2.trans h4⟩

lemma opsOf_ext1_of_ne {α : List (LLabel P)} {p q : P} (hq : q ≠ p) :
    opsOf (X.ext1 α p) q = opsOf α q := by
  unfold LLCtx.ext1
  cases h : X.nl α p with
  | none => simp
  | some ℓ =>
    rw [opsOf_append]
    have : ℓ.invOf q = none := Label.invOf_eq_none_of_proc_ne (by rw [nl_proc h]; exact Ne.symm hq)
    simp [opsOf_cons, this]

lemma respsOf_ext1_of_ne {α : List (LLabel P)} {p q : P} (hq : q ≠ p) :
    respsOf (X.ext1 α p) q = respsOf α q := by
  unfold LLCtx.ext1
  cases h : X.nl α p with
  | none => simp
  | some ℓ =>
    rw [respsOf_append]
    have : ℓ.retOf q = none := Label.retOf_eq_none_of_proc_ne (by rw [nl_proc h]; exact Ne.symm hq)
    simp [respsOf_cons, this]

lemma opsOf_ext_of_not_mem {α : List (LLabel P)} {q : P} {σ : List P} (hq : q ∉ σ) :
    opsOf (X.ext α σ) q = opsOf α q := by
  induction σ generalizing α with
  | nil => simp
  | cons p σ ih =>
    rw [ext_cons, ih (fun h => hq (List.mem_cons_of_mem _ h)),
      opsOf_ext1_of_ne (fun h => hq (by rw [h]; exact List.mem_cons_self))]

lemma respsOf_ext_of_not_mem {α : List (LLabel P)} {q : P} {σ : List P} (hq : q ∉ σ) :
    respsOf (X.ext α σ) q = respsOf α q := by
  induction σ generalizing α with
  | nil => simp
  | cons p σ ih =>
    rw [ext_cons, ih (fun h => hq (List.mem_cons_of_mem _ h)),
      respsOf_ext1_of_ne (fun h => hq (by rw [h]; exact List.mem_cons_self))]

lemma Comp.not_mem {σ : List P} (h : X.Comp σ) : X.ref ∉ σ := fun hm => h _ hm rfl

lemma respsOf_extL_of_not_mem {α : List (LLabel P)} {q : P} {σ : List P} (hq : q ∉ σ) :
    respsOf (X.extL α σ) q = [] := by
  have h := respsOf_ext_of_not_mem (X := X) (α := α) hq
  rw [ext_eq_append, respsOf_append] at h
  simpa using h

/-- The referee has invoked after a step of it. -/
lemma Good.opsOf_ext1_ref_ne_nil {α : List (LLabel P)} (hα : X.Good α) :
    opsOf (X.ext1 α X.ref) X.ref ≠ [] := by
  unfold LLCtx.ext1 nl
  split_ifs with h1 h2
  · simpa using h2.2
  · simp [opsOf_append, opsOf_cons]
  · simp only [Option.toList_some, opsOf_append, ne_eq, List.append_eq_nil_iff, not_and]
    intro h3
    rcases hα.ref_counts with ⟨a, -⟩ | ⟨-, b, -⟩
    · exact absurd a h1
    · rw [h3] at b; simp at b

/-! ### The decide entry of the linearization -/

variable (X)

/-- `decide()` appears in `h α` with output `x`. -/
def Dec (α : List (LLabel P)) (x : ℕ) : Prop :=
  ((X.ref, 0), ContestOp.decide, LLResp.val x) ∈ X.h α

/-- `decide()` appears in `h α` (paper: `decide() ∈ L(α)`). -/
def DecIn (α : List (LLabel P)) : Prop := ∃ x, X.Dec α x

variable {X}

lemma Dec.mono {α β : List (LLabel P)} {x : ℕ} (h : X.Dec α x) (hβ : X.Good β)
    (hp : α <+: β) : X.Dec β x :=
  (X.pc α β hβ.1 hβ.2 hp).subset h

lemma DecIn.mono {α β : List (LLabel P)} (h : X.DecIn α) (hβ : X.Good β)
    (hp : α <+: β) : X.DecIn β :=
  let ⟨x, hx⟩ := h; ⟨x, hx.mono hβ hp⟩

lemma Dec.unique {α : List (LLabel P)} {x y : ℕ} (hα : X.Good α) (hx : X.Dec α x)
    (hy : X.Dec α y) : x = y := by
  have hnd := (X.lin α hα.1 hα.2).nodup
  have := List.inj_on_of_nodup_map hnd hx hy rfl
  simpa using this

/-- In a legal sequential history of the long-lived contest, `decide` returns a value. -/
lemma legal_decide_val {q : P → ℕ} {l : List (ContestOp P × LLResp)}
    (h : (llSpec P).Legal q l) {r : LLResp} (hr : (ContestOp.decide, r) ∈ l) :
    ∃ x, r = .val x := by
  induction l generalizing q with
  | nil => simp at hr
  | cons y l ih =>
    obtain ⟨o, r'⟩ := y
    obtain ⟨q', hs, hl⟩ := h
    rcases List.mem_cons.1 hr with hr | hr
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨⟨x, hx, -⟩, -⟩ := hs
      exact ⟨x, hx⟩
    · exact ih hl hr

/-- In a legal sequential history of the long-lived contest, `decide` returns a bound on the
number of preceding `compete` operations of every competitor. -/
lemma legal_decide_bound {q : P → ℕ} {l₁ l₂ : List (ContestOp P × LLResp)} {x : ℕ}
    (h : (llSpec P).Legal q (l₁ ++ (ContestOp.decide, LLResp.val x) :: l₂)) (c : P) :
    q c + (l₁.filter (fun y => y.1 = ContestOp.compete c)).length ≤ x := by
  induction l₁ generalizing q with
  | nil =>
    obtain ⟨q', ⟨⟨x', hx', hb⟩, -⟩, -⟩ := h
    simp only [LLResp.val.injEq] at hx'
    subst hx'
    simpa using hb c
  | cons y l₁ ih =>
    obtain ⟨o, r⟩ := y
    obtain ⟨q', hs, hl⟩ := h
    have := ih hl
    cases o with
    | compete i =>
      obtain ⟨-, rfl⟩ := hs
      by_cases hic : i = c
      · subst hic
        simp only [Function.update_self] at this
        simp only [List.filter_cons, decide_true, ite_true, List.length_cons]
        omega
      · rw [Function.update_of_ne (Ne.symm hic)] at this
        have hne : ¬ (ContestOp.compete i = ContestOp.compete c) := by simpa using hic
        simp only [List.filter_cons, hne, decide_false]
        simpa using this
    | decide =>
      obtain ⟨-, rfl⟩ := hs
      simpa [List.filter_cons] using this

/-- A completed `decide` appears in the linearization with its actual output. -/
lemma Good.dec_of_completed {α : List (LLabel P)} (hα : X.Good α)
    (hc : respsOf α X.ref ≠ []) :
    ∃ x, respOf α (X.ref, 0) = some (.val x) ∧ X.Dec α x := by
  have hlin := X.lin α hα.1 hα.2
  have hcomp : Completed α (X.ref, 0) := by
    simp only [Completed]; exact List.length_pos_iff.2 hc
  obtain ⟨⟨y, o, r⟩, hy, hy1⟩ := List.mem_map.1 (hlin.complete _ hcomp)
  simp only at hy1; subst hy1
  have ho : o = .decide := by
    have h1 := hlin.op_eq _ hy
    simp only [opOf] at h1
    have h2 := hα.op_mem (List.mem_of_getElem? h1)
    simpa [roleOp] using h2
  subst ho
  obtain ⟨r', hr'⟩ : ∃ r', respOf α (X.ref, 0) = some r' := by
    simp only [respOf]
    exact ⟨_, List.getElem?_eq_getElem (List.length_pos_iff.2 hc)⟩
  have hrr := hlin.resp_eq _ hy r' hr'
  simp only at hrr; subst hrr
  obtain ⟨x, rfl⟩ := legal_decide_val hlin.legal (List.mem_map.2 ⟨_, hy, rfl⟩)
  exact ⟨x, hr', hy⟩

/-- **The counting argument.** If `decide()` is not in `h β` and a competitor `c` has completed
more than `x` operations in `β`, then no extension of `β` has `decide()` with output `x` in its
linearization. -/
lemma not_dec_of_resps {β : List (LLabel P)} (hβ : X.Good β) (hnd : ¬ X.DecIn β) {c : P}
    (hc : c ≠ X.ref) {x : ℕ} (hx : x < (respsOf β c).length) {γ : List (LLabel P)}
    (hβγ : X.Good (β ++ γ)) : ¬ X.Dec (β ++ γ) x := by
  intro hdec
  obtain ⟨M, hM⟩ := X.pc β (β ++ γ) hβγ.1 hβγ.2 (List.prefix_append _ _)
  have hdec' : ((X.ref, 0), ContestOp.decide, LLResp.val x) ∈ X.h β ++ M := by
    unfold Dec at hdec; rwa [← hM] at hdec
  have hnotin : ((X.ref, 0), ContestOp.decide, LLResp.val x) ∉ X.h β := fun h => hnd ⟨x, h⟩
  have hinM : ((X.ref, 0), ContestOp.decide, LLResp.val x) ∈ M := by
    rcases List.mem_append.1 hdec' with h | h
    · exact absurd h hnotin
    · exact h
  obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem hinM
  have hleg := (X.lin _ hβγ.1 hβγ.2).legal
  rw [← hM] at hleg
  have hb := legal_decide_bound (l₁ := (X.h β ++ M₁).map Prod.snd)
    (l₂ := M₂.map Prod.snd) (x := x) (by simpa using hleg) c
  simp only [llSpec, zero_add] at hb
  -- lower bound on the competes of `c` in `h β`
  have hlin := X.lin β hβ.1 hβ.2
  set F := (X.h β).filter (fun y => y.2.1 = ContestOp.compete c) with hF
  have hsub : ((List.range (x + 1)).map (fun k => (c, k))) ⊆ F.map Prod.fst := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
    have hcomp : Completed β (c, k) := by
      simp only [Completed]; simp at hk; omega
    obtain ⟨y, hy, hy1⟩ := List.mem_map.1 (hlin.complete _ hcomp)
    refine List.mem_map.2 ⟨y, List.mem_filter.2 ⟨hy, ?_⟩, hy1⟩
    have h1 := hlin.op_eq _ hy
    rw [hy1] at h1
    simp only [opOf] at h1
    have h2 := hβ.op_mem (List.mem_of_getElem? h1)
    simp [roleOp, hc] at h2
    simp [h2]
  have hnd' : ((List.range (x + 1)).map (fun k => (c, k))).Nodup :=
    (List.nodup_range).map (fun a b h => by simpa using h)
  have hlen := (List.subperm_of_subset hnd' hsub).length_le
  simp only [List.length_map, List.length_range] at hlen
  have : F.length ≤
      (((X.h β ++ M₁).map Prod.snd).filter (fun y => y.1 = ContestOp.compete c)).length := by
    rw [List.filter_map, List.length_map, List.filter_append, List.length_append]
    simp only [hF]
    have : ((fun y : ContestOp P × LLResp => decide (y.1 = ContestOp.compete c)) ∘
        Prod.snd) = fun y : OpId P × ContestOp P × LLResp => decide (y.2.1 = .compete c) := rfl
    rw [this]; omega
  omega

/-! ### Transfer of schedules between indistinguishable executions -/

lemma nl_eq_of_agree {α α' : List (LLabel P)} {p : P} (hp : Agree p (X.cfg α) (X.cfg α'))
    (hst : p = X.ref → (opsOf α X.ref = [] ↔ opsOf α' X.ref = [])) : X.nl α p = X.nl α' p := by
  unfold nl
  rw [hp.pend, nextLabel_eq_of_agree X.I hp]
  by_cases hpr : p = X.ref
  · subst hpr
    have := hst rfl
    by_cases h1 : opsOf α X.ref = []
    · simp [h1, this.1 h1]
    · have h2 : opsOf α' X.ref ≠ [] := fun h => h1 (this.2 h)
      simp [h1, h2]
  · simp [hpr]

/-- **Transfer.** Schedules of processes of `Q` produce the same labels from two good executions
whose final configurations agree on `Q` (and with the same referee status if the referee is in
`Q`), and the final configurations still agree on `Q`. -/
lemma transfer {Q : Set P} {α α' : List (LLabel P)} (hα : X.Good α) (hα' : X.Good α')
    (hag : AgreeOn Q (X.cfg α) (X.cfg α'))
    (hst : X.ref ∈ Q → (opsOf α X.ref = [] ↔ opsOf α' X.ref = [])) {σ : List P}
    (hσ : ∀ p ∈ σ, p ∈ Q) :
    X.extL α σ = X.extL α' σ ∧ AgreeOn Q (X.cfg (X.ext α σ)) (X.cfg (X.ext α' σ)) ∧
      (X.ref ∈ Q → (opsOf (X.ext α σ) X.ref = [] ↔ opsOf (X.ext α' σ) X.ref = [])) := by
  induction σ generalizing α α' with
  | nil => exact ⟨rfl, by simpa using hag, by simpa using hst⟩
  | cons p σ ih =>
    have hpQ : p ∈ Q := hσ p List.mem_cons_self
    have hnl : X.nl α p = X.nl α' p :=
      nl_eq_of_agree (hag.agree hpQ) (fun h => hst (h ▸ hpQ))
    have h1 : X.Good (X.ext1 α p) := hα.ext1 p
    have h1' : X.Good (X.ext1 α' p) := hα'.ext1 p
    have hag1 : AgreeOn Q (X.cfg (X.ext1 α p)) (X.cfg (X.ext1 α' p)) := by
      cases hn : X.nl α p with
      | none =>
        rw [ext1_of_none hn, ext1_of_none (hnl ▸ hn)]; exact hag
      | some ℓ =>
        have hn' : X.nl α' p = some ℓ := hnl ▸ hn
        rw [ext1_of_some hn, ext1_of_some hn']
        obtain ⟨D', hD', hagD⟩ := step_agreeOn hag (by rw [nl_proc hn]; exact hpQ)
          (hα.nl_step hn).1
        rw [(hα'.nl_step hn').1] at hD'
        cases hD'; exact hagD
    have hst1 : X.ref ∈ Q → (opsOf (X.ext1 α p) X.ref = [] ↔ opsOf (X.ext1 α' p) X.ref = []) := by
      intro hr
      unfold LLCtx.ext1
      rw [opsOf_append, opsOf_append, hnl, List.append_eq_nil_iff, List.append_eq_nil_iff,
        hst hr]
    obtain ⟨e1, e2, e3⟩ := ih h1 h1' hag1 hst1 (fun q hq => hσ q (List.mem_cons_of_mem _ hq))
    refine ⟨?_, ?_, ?_⟩
    · simp only [extL, hnl, e1]
    · rw [ext_cons, ext_cons]; exact e2
    · rw [ext_cons, ext_cons]; exact e3

end LLCtx

end Cslib.SharedMemory.Referee
