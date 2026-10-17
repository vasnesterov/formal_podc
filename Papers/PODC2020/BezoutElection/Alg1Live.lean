import Papers.PODC2020.BezoutElection.Alg1Inv
import Papers.PODC2020.BezoutElection.LiveGen

/-!
# Algorithm 1: termination (basic facts on infinite executions)

Facts about the steps of a fair infinite execution of Algorithm 1 in which all processes
invoke `elect()` (`Ctx`), used by the termination proof (`Alg1Term.lean`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg1

variable {Id : Type} [DecidableEq Id] {R : Type} [Inhabited R] {P : Type} [DecidableEq P]
  [Fintype P] {n : ℕ} {out : Id → Id → R} {ids : P → Id} {π : P → Equiv.Perm (Fin 1)}

/-- The hypotheses of the termination proof. -/
structure Ctx (e : ((alg1 Id n out).impl ids π).InfExec) : Prop where
  hid : Function.Injective ids
  hn : Fintype.card P = n
  fair : e.IsFair
  allinv : AllInvoke e

variable {e : ((alg1 Id n out).impl ids π).InfExec}

namespace Ctx

variable (X : Ctx e)
include X

lemma inv (t : ℕ) : Inv ids n out (e.lbls t) (e.cfg t) := inv_run X.hid X.hn (e.run_lbls t)

lemma basic (t : ℕ) : Basic ids (e.lbls t) (e.cfg t) := (X.inv t).1

lemma me (t : ℕ) (q : P) : ((e.cfg t).loc q).me = ids q := (X.basic t).me q

/-- A step of `q` from a `read` program counter is a read. -/
lemma act_read {t : ℕ} {q : P} (hq : (e.lbl t).proc = q) (hpc : ((e.cfg t).loc q).pc = .read) :
    e.lbl t = .tau q ∧ (e.cfg (t + 1)).loc q = afterRead n ((e.cfg t).loc q) (reg (e.cfg t)) ∧
      reg (e.cfg (t + 1)) = reg (e.cfg t) := by
  have hB := X.basic t
  rcases step_cases (e.step_eq t) with ⟨p, o, hl, hp, -, -, -⟩ |
    ⟨p, hl, hp, hpc', hloc, -, hreg⟩ | ⟨p, w, hl, hp, hpc', -, -, -⟩ |
    ⟨p, r, hl, hp, -, -, hcase⟩ <;> rw [hl] at hq <;> simp only [Label.proc] at hq <;> subst hq
  · exact absurd hp (hB.busy p (by rw [hpc]; simp) (by rw [hpc]; simp))
  · exact ⟨hl, by rw [hloc]; simp, hreg⟩
  · rw [hpc] at hpc'; cases hpc'
  · rcases hcase with ⟨a, h1, -⟩ | ⟨h1 | h1, -⟩ <;> rw [hpc] at h1 <;> cases h1

/-- A step of `q` from a `write w` program counter writes `w`. -/
lemma act_write {t : ℕ} {q : P} {w : Reg Id} (hq : (e.lbl t).proc = q)
    (hpc : ((e.cfg t).loc q).pc = .write w) :
    e.lbl t = .tau q ∧ (e.cfg (t + 1)).loc q = { (e.cfg t).loc q with pc := .read } ∧ reg (e.cfg (t + 1)) = w := by
  have hB := X.basic t
  rcases step_cases (e.step_eq t) with ⟨p, o, hl, hp, -, -, -⟩ |
    ⟨p, hl, hp, hpc', -, -, -⟩ | ⟨p, w', hl, hp, hpc', hloc, -, hreg⟩ |
    ⟨p, r, hl, hp, -, -, hcase⟩ <;> rw [hl] at hq <;> simp only [Label.proc] at hq <;> subst hq
  · exact absurd hp (hB.busy p (by rw [hpc]; simp) (by rw [hpc]; simp))
  · rw [hpc] at hpc'; cases hpc'
  · rw [hpc] at hpc'; cases hpc'
    exact ⟨hl, by rw [hloc]; simp, hreg⟩
  · rcases hcase with ⟨a, h1, -⟩ | ⟨h1 | h1, -⟩ <;> rw [hpc] at h1 <;> cases h1

/-- A step of `q` from a `ret a` program counter is a response. -/
lemma act_ret {t : ℕ} {q : P} {a : Id} (hq : (e.lbl t).proc = q) (hpc : ((e.cfg t).loc q).pc = .ret a) :
    ∃ r, e.lbl t = .ret q r := by
  have hB := X.basic t
  rcases step_cases (e.step_eq t) with ⟨p, o, hl, hp, -, -, -⟩ |
    ⟨p, hl, hp, hpc', -, -, -⟩ | ⟨p, w', hl, hp, hpc', -, -, -⟩ |
    ⟨p, r, hl, hp, -, -, -⟩ <;> rw [hl] at hq <;> simp only [Label.proc] at hq <;> subst hq
  · exact absurd hp (hB.busy p (by rw [hpc]; simp) (by rw [hpc]; simp))
  · rw [hpc] at hpc'; cases hpc'
  · rw [hpc] at hpc'; cases hpc'
  · exact ⟨r, hl⟩

end Ctx

/-- A write happens at time `t`. -/
def WriteAt (e : ((alg1 Id n out).impl ids π).InfExec) (t : ℕ) : Prop :=
  ∃ q w, e.lbl t = .tau q ∧ ((e.cfg t).loc q).pc = .write w

namespace Ctx

variable (X : Ctx e)
include X

/-- The register changes only by writes. -/
lemma reg_step (t : ℕ) : reg (e.cfg (t + 1)) = reg (e.cfg t) ∨
    ∃ q w, e.lbl t = .tau q ∧ ((e.cfg t).loc q).pc = .write w ∧ reg (e.cfg (t + 1)) = w := by
  rcases step_cases (e.step_eq t) with ⟨p, o, hl, hp, -, -, hreg⟩ |
    ⟨p, hl, hp, hpc', -, -, hreg⟩ | ⟨p, w', hl, hp, hpc', hloc, -, hreg⟩ |
    ⟨p, r, hl, hp, -, hreg, -⟩
  · exact Or.inl hreg
  · exact Or.inl hreg
  · exact Or.inr ⟨p, w', hl, hpc', hreg⟩
  · exact Or.inl hreg

lemma reg_of_not_write {t : ℕ} (h : ¬ WriteAt e t) : reg (e.cfg (t + 1)) = reg (e.cfg t) := by
  rcases X.reg_step t with h1 | ⟨q, w, h1, h2, -⟩
  · exact h1
  · exact absurd ⟨q, w, h1, h2⟩ h

lemma other {t : ℕ} {q : P} (h : (e.lbl t).proc ≠ q) : (e.cfg (t + 1)).loc q = (e.cfg t).loc q :=
  (Impl.step_other (e.step_eq _) h).1

/-- Local facts preserved by every step. -/
lemma mono (t : ℕ) (q : P) : ((e.cfg (t + 1)).loc q).me = ((e.cfg t).loc q).me ∧
    (((e.cfg t).loc q).loser = true → ((e.cfg (t + 1)).loc q).loser = true) ∧
    (((e.cfg t).loc q).phase = .committing → ((e.cfg (t + 1)).loc q).phase = .committing) :=
  step_loc_mono (e.step_eq t) q

lemma loser_mono {t t' : ℕ} (h : t ≤ t') {q : P} (hl : ((e.cfg t).loc q).loser = true) :
    ((e.cfg t').loc q).loser = true := by
  induction t', h using Nat.le_induction with
  | base => exact hl
  | succ t' _ ih => exact (X.mono t' q).2.1 ih

lemma phase_mono {t t' : ℕ} (h : t ≤ t') {q : P} (hl : ((e.cfg t).loc q).phase = .committing) :
    ((e.cfg t').loc q).phase = .committing := by
  induction t', h using Nat.le_induction with
  | base => exact hl
  | succ t' _ ih => exact (X.mono t' q).2.2 ih

/-- A process that has started never becomes idle again. -/
lemma not_idle_step {t : ℕ} {q : P} (h : ((e.cfg t).loc q).pc ≠ .idle) : ((e.cfg (t + 1)).loc q).pc ≠ .idle := by
  by_cases hq : (e.lbl t).proc = q
  · cases hpc : ((e.cfg t).loc q).pc with
    | idle => exact absurd hpc h
    | read =>
      rw [(X.act_read hq hpc).2.1]
      rcases afterRead_pc n ((e.cfg t).loc q) (reg (e.cfg t)) with h1 | ⟨w, h1⟩ | ⟨a, h1⟩ <;> rw [h1] <;> simp
    | write w => rw [(X.act_write hq hpc).2.1]; simp
    | ret a =>
      obtain ⟨r, hr⟩ := X.act_ret hq hpc
      rcases step_cases (e.step_eq t) with ⟨p, o, hl, -⟩ | ⟨p, hl, -⟩ | ⟨p, w, hl, -⟩ |
        ⟨p, r', hl, hp, -, -, ⟨a', h1, -, hloc⟩ | ⟨h1, hloc⟩⟩ <;> rw [hr] at hl <;> cases hl
      · rw [hloc]; simp
      · rw [hloc]; exact h
    | fin =>
      rcases step_cases (e.step_eq t) with ⟨p, o, hl, -, hloc, -⟩ | ⟨p, hl, -, hpc', -⟩ |
        ⟨p, w, hl, -, hpc', -⟩ | ⟨p, r', hl, hp, -, -, ⟨a', h1, -, hloc⟩ | ⟨h1, hloc⟩⟩ <;>
        rw [hl] at hq <;> simp only [Label.proc] at hq <;> subst hq
      · rw [hloc]; simp [hpc]
      · rw [hpc] at hpc'; cases hpc'
      · rw [hpc] at hpc'; cases hpc'
      · rw [hpc] at h1; cases h1
      · rw [hloc]; exact h
  · rw [X.other hq]; exact h

/-- Every process eventually leaves `idle` forever. -/
lemma not_idle (q : P) : ∃ T, ∀ t ≥ T, ((e.cfg t).loc q).pc ≠ .idle := by
  obtain ⟨t, o, ht⟩ := X.allinv q
  refine ⟨t + 1, fun t' ht' => ?_⟩
  induction t', ht' using Nat.le_induction with
  | base =>
    rcases step_cases (e.step_eq t) with ⟨p, o', hl, -, hloc, -⟩ | ⟨p, hl, -⟩ | ⟨p, w, hl, -⟩ |
      ⟨p, r', hl, -⟩ <;> rw [ht] at hl <;> cases hl
    show ((e.cfg (t + 1)).loc q).pc ≠ .idle
    rw [hloc]; simp only [Function.update_self]
    split_ifs with h1
    · simp
    · exact h1
  | succ t' _ ih => exact X.not_idle_step ih

/-- A process that has started and does not return is pending. -/
lemma pend_forever (q : P) (T : ℕ) (h : ∀ t ≥ T, ((e.cfg t).loc q).pc ≠ .fin) :
    ∃ T' ≥ T, ∀ t ≥ T', (e.cfg t).pend q ≠ none ∧ ((e.cfg t).loc q).pc ≠ .idle ∧
      ((e.cfg t).loc q).pc ≠ .fin := by
  obtain ⟨T₁, hT₁⟩ := X.not_idle q
  refine ⟨max T T₁, le_max_left _ _, fun t ht => ?_⟩
  have h1 := hT₁ t (by omega)
  have h2 := h t (by omega)
  exact ⟨(X.basic t).busy q h1 h2, h1, h2⟩

lemma pc_cases {s : St Id} (h1 : s.pc ≠ .idle) (h2 : s.pc ≠ .fin) (h3 : ∀ a, s.pc ≠ .ret a) :
    s.pc = .read ∨ ∃ w, s.pc = .write w := by
  cases h : s.pc with
  | idle => exact absurd h h1
  | read => exact Or.inl rfl
  | write w => exact Or.inr ⟨w, rfl⟩
  | ret a => exact absurd h (h3 a)
  | fin => exact absurd h h2

/-- An action of `q` that is not a read keeps `q`'s variables and does not lead to a write. -/
lemma act_nonread {t : ℕ} {q : P} (hq : (e.lbl t).proc = q)
    (hpc : ((e.cfg t).loc q).pc ≠ .read) :
    ((e.cfg (t + 1)).loc q).disc = ((e.cfg t).loc q).disc ∧
    ((e.cfg (t + 1)).loc q).phase = ((e.cfg t).loc q).phase ∧
    ((e.cfg (t + 1)).loc q).loser = ((e.cfg t).loc q).loser ∧
    ∀ w, ((e.cfg (t + 1)).loc q).pc ≠ .write w := by
  have hB := X.basic t
  rcases step_cases (e.step_eq t) with ⟨p, o, hl, hp, hloc, -, -⟩ |
    ⟨p, hl, hp, hpc', -, -, -⟩ | ⟨p, w', hl, hp, hpc', hloc, -, -⟩ |
    ⟨p, r, hl, hp, -, -, ⟨a, h1, -, hloc⟩ | ⟨h1, hloc⟩⟩ <;>
    rw [hl] at hq <;> simp only [Label.proc] at hq <;> subst hq
  · rw [hloc]; simp only [Function.update_self]
    split_ifs with h0
    · simp
    · have h2 : ((e.cfg t).loc p).pc = .fin := by
        by_contra h3; exact hB.busy p h0 h3 hp
      simp [h2]
  · exact absurd hpc' hpc
  · rw [hloc]; simp
  · rw [hloc]; simp
  · rw [hloc]
    rcases h1 with h1 | h1
    · exact absurd (hB.idle p h1) hp
    · simp [h1]

/-- A response label of `p` occurs before `t` if `p` has an output at `t`. -/
lemma ret_of_outputs {t : ℕ} {p : P} (h : outputs (e.lbls t) p ≠ none) :
    ∃ t' r, e.lbl t' = .ret p r := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
  have hmem : r ∈ respsOf (e.lbls t) p := List.mem_of_mem_head? hr
  simp only [respsOf, List.mem_filterMap] at hmem
  obtain ⟨ℓ, hℓ, hret⟩ := hmem
  simp only [Impl.InfExec.lbls, List.mem_map, List.mem_range] at hℓ
  obtain ⟨t', -, rfl⟩ := hℓ
  cases hl : e.lbl t' with
  | inv q o => rw [hl] at hret; simp at hret
  | tau q => rw [hl] at hret; simp at hret
  | ret q r' =>
    rw [hl] at hret
    simp only [Label.retOf_ret] at hret
    split_ifs at hret with hq
    subst hq; exact ⟨t', r', hl⟩

/-- "Eventually forever" from the actions of one process. -/
lemma ev_flush (q : P) (t₀ : ℕ) (Q : ℕ → Prop)
    (hact : ∀ t ≥ t₀, (e.lbl t).proc = q → Q (t + 1))
    (hother : ∀ t ≥ t₀, (e.lbl t).proc ≠ q → Q t → Q (t + 1))
    (hidle : (e.cfg t₀).pend q = none → Q t₀) : ∃ T, ∀ t ≥ T, Q t := by
  have hpres : ∀ t ≥ t₀, Q t → Q (t + 1) := by
    intro t ht hQ
    by_cases h : (e.lbl t).proc = q
    · exact hact t ht h
    · exact hother t ht h hQ
  by_cases hp : (e.cfg t₀).pend q = none
  · obtain ⟨T, -, hT⟩ := ev_forever Q t₀ hpres ⟨t₀, le_rfl, hidle hp⟩
    exact ⟨T, hT⟩
  · obtain ⟨t', ht', hq, -⟩ := e.first_act X.fair hp
    obtain ⟨T, -, hT⟩ := ev_forever Q t₀ hpres ⟨t' + 1, by omega, hact t' ht' hq⟩
    exact ⟨T, hT⟩

/-- If nothing is written from `t₁` on, every active process eventually reads the (constant)
register and decides not to write. -/
lemma read_nowrite (q : P) (t₁ : ℕ) (hpend : ∀ t ≥ t₁, (e.cfg t).pend q ≠ none)
    (hpc : ∀ t ≥ t₁, ((e.cfg t).loc q).pc = .read ∨ ∃ w, ((e.cfg t).loc q).pc = .write w)
    (hnw : ∀ t ≥ t₁, ¬ WriteAt e t) :
    ∃ t ≥ t₁, ((e.cfg t).loc q).pc = .read ∧ e.lbl t = .tau q ∧ reg (e.cfg t) = reg (e.cfg t₁) ∧
      (e.cfg (t + 1)).loc q = afterRead n ((e.cfg t).loc q) (reg (e.cfg t)) ∧
      ∀ w, (afterRead n ((e.cfg t).loc q) (reg (e.cfg t))).pc ≠ .write w := by
  have hreg : ∀ t ≥ t₁, reg (e.cfg t) = reg (e.cfg t₁) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [X.reg_of_not_write (hnw t ht), ih]
  obtain ⟨t, ht, hq, -⟩ := e.first_act X.fair (hpend t₁ le_rfl)
  rcases hpc t ht with h1 | ⟨w, h1⟩
  · obtain ⟨hl, hloc, -⟩ := X.act_read hq h1
    refine ⟨t, ht, h1, hl, hreg t ht, hloc, fun w hw => ?_⟩
    rw [← hloc] at hw
    obtain ⟨t', ht', hq', -, hloc', -⟩ := e.first_act X.fair (hpend (t + 1) (by omega))
    rw [← hloc'] at hw
    exact hnw t' (by omega) ⟨q, w, (X.act_write hq' hw).1, hw⟩
  · exact absurd ⟨q, w, (X.act_write hq h1).1, h1⟩ (hnw t ht)

end Ctx

end BezoutElection.Alg1
