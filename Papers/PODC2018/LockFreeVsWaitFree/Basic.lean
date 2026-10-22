import Papers.PODC2018.LockFreeVsWaitFree.Spec
import Cslib.Computability.Distributed.SharedMemory.Solo
import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Setting of the impossibility proof (Section 5 of [ACHP18])

We fix (`Ctx`) an implementation `I` of the `n`-LLAA object (interface `llaaObj`) from
arbitrary base objects, a process `p₀` on side `0` (all other processes are on side `1`), and
assume, as in Section 5 of [ACHP18]:

* every process may invoke `output()` of its side (`allow`);
* wait-freedom on the *admissible* executions (`Adm p₀`: processes only invoke the operation of
  their side, and `p₀` invokes at most once) — the paper only considers executions in which
  `p₀` performs a single `output()`;
* linearizability (w.r.t. the nondeterministic specification `llaaSpec`) of every admissible
  finite execution.

Assuming these properties only on admissible executions makes the impossibility result
stronger than the paper's.

## Schedules

In an admissible execution every process has at most one possible next label: an idle process
`q ≠ p₀` can only invoke `output()` of side `1`; a pending process can only take its
(deterministic) next step `I.nextLabel C q`; `p₀` invokes if it has not invoked yet and has
nothing to do once its operation returned. The paper's "`q(C)`" is `X.ext1 α q`, and
`X.ext α σ` lets the processes of a schedule `σ : List P` take their next label in turn.

## Valency (Section 5)

* `X.Potent α v`: some admissible extension of `α` completes the operation of `p₀` with output
  `v` (paper: `α` is `v`-potent);
* `X.Univ α v`: `α` is `v`-potent and not `w`-potent for `w ≠ v` (paper: `v`-univalent);
* `X.Biv α`: `α` is potent for two different values (paper: bivalent).

The paper writes "`p₀(C)` is `v`-univalent" for `X.Univ (X.ext1 α p₀) v`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeVsWaitFree

open Cslib SharedMemory Impl

/-- Labels of executions of LLAA implementations. -/
abbrev LLabel (P : Type) := Label P llaaObj

/-- The side of process `p` when `p₀` is the only process of side `0`. -/
def side {P : Type} [DecidableEq P] (p₀ p : P) : Fin 2 := if p = p₀ then 0 else 1

/-- Admissible executions (Section 5 of [ACHP18]): every process invokes the operation of its
side, `p₀` (the only process of side `0`) at most once. -/
structure Adm {P : Type} [DecidableEq P] (p₀ : P) (α : List (LLabel P)) : Prop where
  side : ∀ p o, o ∈ opsOf α p → o = side p₀ p
  once : (opsOf α p₀).length ≤ 1

lemma Adm.of_append {P : Type} [DecidableEq P] {p₀ : P} {α β : List (LLabel P)}
    (h : Adm p₀ (α ++ β)) : Adm p₀ α := by
  refine ⟨fun p o ho => h.side p o (by rw [opsOf_append]; exact List.mem_append_left _ ho), ?_⟩
  have := h.once; rw [opsOf_append, List.length_append] at this; omega

/-- The setting of Section 5 of [ACHP18]: an implementation of `n`-LLAA in which `p₀` is the
only process of side `0`, wait-free and linearizable on admissible executions. -/
structure Ctx (P ι L : Type) (B : ι → ObjSpec) [DecidableEq P] [DecidableEq ι] where
  /-- The implementation. -/
  I : Impl llaaObj B P L
  /-- The only process of side `0`. -/
  p₀ : P
  /-- Every process may invoke `output()` of its side. -/
  allow : ∀ p, I.allowed p (side p₀ p)
  /-- Wait-freedom on admissible executions. -/
  wf : I.WaitFreeOn (Adm p₀)
  /-- Linearizability of admissible executions. -/
  lin : ∀ α, I.Valid α → Adm p₀ α → ∃ L, IsNLinearization llaaSpec α L

namespace Ctx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] (X : Ctx P ι L B)

/-! ### Good executions -/

/-- `α` is a valid admissible execution. -/
def Good (α : List (LLabel P)) : Prop := X.I.Valid α ∧ Adm X.p₀ α

/-- The final configuration of `α` (meaningful for valid `α`). -/
noncomputable def cfg (α : List (LLabel P)) : Config llaaObj B P L :=
  (X.I.run α).getD X.I.initCfg

variable {X}

lemma Good.run {α : List (LLabel P)} (h : X.Good α) : X.I.run α = some (X.cfg α) := by
  obtain ⟨C, hC⟩ := h.1
  simp [cfg, hC]

lemma Good.of_prefix {α β : List (LLabel P)} (h : X.Good β) (hp : α <+: β) : X.Good α := by
  obtain ⟨γ, rfl⟩ := hp
  exact ⟨X.I.valid_of_prefix h.1 (List.prefix_append _ _), h.2.of_append⟩

lemma Good.of_append {α β : List (LLabel P)} (h : X.Good (α ++ β)) : X.Good α :=
  h.of_prefix (List.prefix_append _ _)

lemma good_nil : X.Good [] :=
  ⟨⟨_, rfl⟩, ⟨fun p o ho => by simp [opsOf] at ho, by simp [opsOf]⟩⟩

lemma cfg_nil : X.cfg [] = X.I.initCfg := rfl

/-- Counting invariant for `p₀`: at most one invocation. -/
lemma Good.p₀_counts {α : List (LLabel P)} (h : X.Good α) :
    ((X.cfg α).pend X.p₀ = none ∧ (opsOf α X.p₀).length = (respsOf α X.p₀).length) ∨
    ((X.cfg α).pend X.p₀ ≠ none ∧ (opsOf α X.p₀).length = 1 ∧ respsOf α X.p₀ = []) := by
  have h1 := h.2.once
  rcases X.I.run_counts h.run X.p₀ with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a, b⟩
  · refine Or.inr ⟨a, by omega, ?_⟩
    rw [← List.length_eq_zero_iff]; omega

lemma Good.resps_le_one {α : List (LLabel P)} (h : X.Good α) : (respsOf α X.p₀).length ≤ 1 := by
  rcases h.p₀_counts with ⟨-, b⟩ | ⟨-, -, c⟩
  · have := h.2.once; omega
  · simp [c]

/-! ### Next labels and schedule extensions -/

variable (X)

/-- The next label of `p` after `α`; `none` iff `p = p₀` and its operation has returned. -/
noncomputable def nl (α : List (LLabel P)) (p : P) : Option (LLabel P) :=
  if (X.cfg α).pend p = none then
    (if p = X.p₀ ∧ opsOf α X.p₀ ≠ [] then none else some (.inv p (side X.p₀ p)))
  else some (X.I.nextLabel (X.cfg α) p)

/-- Extension of `α` by one step of `p` (paper: `p(C)`). -/
noncomputable def ext1 (α : List (LLabel P)) (p : P) : List (LLabel P) := α ++ (X.nl α p).toList

/-- The labels added by the schedule `σ`. -/
noncomputable def extL : List (LLabel P) → List P → List (LLabel P)
  | _, [] => []
  | α, p :: σ => (X.nl α p).toList ++ extL (X.ext1 α p) σ

/-- Extension of `α` by the schedule `σ`. -/
noncomputable def ext (α : List (LLabel P)) (σ : List P) : List (LLabel P) := α ++ X.extL α σ

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

lemma ext_concat (α : List (LLabel P)) (σ : List P) (p : P) :
    X.ext α (σ ++ [p]) = X.ext1 (X.ext α σ) p := by
  rw [ext_append, ext_singleton]

lemma nl_of_pend {α : List (LLabel P)} {p : P} (h : (X.cfg α).pend p ≠ none) :
    X.nl α p = some (X.I.nextLabel (X.cfg α) p) := by
  simp [nl, h]

lemma nl_of_idle_ne {α : List (LLabel P)} {p : P} (h : (X.cfg α).pend p = none)
    (hp : p ≠ X.p₀) : X.nl α p = some (.inv p 1) := by
  simp [nl, h, hp, side]

lemma nl_isSome_of_ne {α : List (LLabel P)} {p : P} (hp : p ≠ X.p₀) : (X.nl α p).isSome := by
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
    · exact hα.2.side q o ho
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
      by_cases hp : p = X.p₀
      · subst hp
        have : opsOf α X.p₀ = [] := by
          by_contra hne; exact h2 ⟨rfl, hne⟩
        simp [this]
      · simp [opsOf_cons, hp]; omega
    · cases h
      simp [opsOf_cons, X.I.nextLabel_invOf]; omega

lemma Good.ext1 {α : List (LLabel P)} (hα : X.Good α) (p : P) : X.Good (X.ext1 α p) := by
  unfold Ctx.ext1
  cases h : X.nl α p with
  | none => simpa using hα
  | some ℓ => exact (hα.nl_step h).2

lemma Good.ext {α : List (LLabel P)} (hα : X.Good α) (σ : List P) : X.Good (X.ext α σ) := by
  induction σ generalizing α with
  | nil => simpa using hα
  | cons p σ ih => rw [ext_cons]; exact ih (hα.ext1 p)

lemma ext1_of_none {α : List (LLabel P)} {p : P} (h : X.nl α p = none) : X.ext1 α p = α := by
  simp [Ctx.ext1, h]

lemma ext1_of_some {α : List (LLabel P)} {p : P} {ℓ : LLabel P} (h : X.nl α p = some ℓ) :
    X.ext1 α p = α ++ [ℓ] := by
  simp [Ctx.ext1, h]

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
  unfold Ctx.ext1
  cases h : X.nl α p with
  | none => simp
  | some ℓ =>
    rw [opsOf_append]
    have : ℓ.invOf q = none := Label.invOf_eq_none_of_proc_ne (by rw [nl_proc h]; exact Ne.symm hq)
    simp [opsOf_cons, this]

lemma respsOf_ext1_of_ne {α : List (LLabel P)} {p q : P} (hq : q ≠ p) :
    respsOf (X.ext1 α p) q = respsOf α q := by
  unfold Ctx.ext1
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

/-- The labels of a schedule are labels of its processes. -/
lemma extL_proc {α : List (LLabel P)} {σ : List P} {ℓ : LLabel P} (h : ℓ ∈ X.extL α σ) :
    ℓ.proc ∈ σ := by
  induction σ generalizing α with
  | nil => simp [extL] at h
  | cons p σ ih =>
    simp only [extL, List.mem_append] at h
    rcases h with h | h
    · cases hn : X.nl α p with
      | none => simp [hn] at h
      | some ℓ' =>
        simp only [hn, Option.toList_some, List.mem_singleton] at h
        subst h; rw [nl_proc hn]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-! ### Transfer of schedules between indistinguishable executions -/

lemma nl_eq_of_agree {α α' : List (LLabel P)} {p : P} (hp : Agree p (X.cfg α) (X.cfg α'))
    (hst : p = X.p₀ → (opsOf α X.p₀ = [] ↔ opsOf α' X.p₀ = [])) : X.nl α p = X.nl α' p := by
  unfold nl
  rw [hp.pend, nextLabel_eq_of_agree X.I hp]
  by_cases hpr : p = X.p₀
  · subst hpr
    have := hst rfl
    by_cases h1 : opsOf α X.p₀ = []
    · simp [h1, this.1 h1]
    · have h2 : opsOf α' X.p₀ ≠ [] := fun h => h1 (this.2 h)
      simp [h1, h2]
  · simp [hpr]

/-- **Transfer.** Schedules of processes of `Q` produce the same labels from two good executions
whose final configurations agree on `Q` (with the same invocation status of `p₀` if `p₀ ∈ Q`),
and the final configurations still agree on `Q`. -/
lemma transfer {Q : Set P} {α α' : List (LLabel P)} (hα : X.Good α) (hα' : X.Good α')
    (hag : AgreeOn Q (X.cfg α) (X.cfg α'))
    (hst : X.p₀ ∈ Q → (opsOf α X.p₀ = [] ↔ opsOf α' X.p₀ = [])) {σ : List P}
    (hσ : ∀ p ∈ σ, p ∈ Q) :
    X.extL α σ = X.extL α' σ ∧ AgreeOn Q (X.cfg (X.ext α σ)) (X.cfg (X.ext α' σ)) ∧
      (X.p₀ ∈ Q → (opsOf (X.ext α σ) X.p₀ = [] ↔ opsOf (X.ext α' σ) X.p₀ = [])) := by
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
    have hst1 : X.p₀ ∈ Q → (opsOf (X.ext1 α p) X.p₀ = [] ↔ opsOf (X.ext1 α' p) X.p₀ = []) := by
      intro hr
      unfold Ctx.ext1
      rw [opsOf_append, opsOf_append, hnl, List.append_eq_nil_iff, List.append_eq_nil_iff,
        hst hr]
    obtain ⟨e1, e2, e3⟩ := ih h1 h1' hag1 hst1 (fun q hq => hσ q (List.mem_cons_of_mem _ hq))
    refine ⟨?_, ?_, ?_⟩
    · simp only [extL, hnl, e1]
    · rw [ext_cons, ext_cons]; exact e2
    · rw [ext_cons, ext_cons]; exact e3

end Ctx

end Podc.LockFreeVsWaitFree
