import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Task
import Podc.Order.NatDescent
import Podc.SharedMemory.Run

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Progress.lean

/-!
# Infinite executions and progress conditions for arbitrary objects

CSLib states the prefix and fairness API of infinite executions only for lock objects
(`InfExec.pre`, `InfExec.Fair`, `InfExec.exists_good` in `Mutex.lean`). This file provides it for
every implemented object `A`, together with progress conditions restricted to a set of executions.

## Infinite executions

* `InfExec.lbls e t` — the first `t` labels of `e` (`run_lbls`, `lbls_prefix`, `reachable_cfg`;
  for lock objects `InfExec.pre_eq_lbls`);
* `InfExec.IsFair` — every process with a pending operation eventually takes a step
  (`InfExec.fair_iff_isFair` for lock objects); `InfExec.first_act`;
* `InfExec.exists_good_of_measure` — progress by a measure (generalizes CSLib's
  `InfExec.exists_good`);
* `Impl.step_pend_none`, `InfExec.exists_inv_between`, `InfExec.exists_ret_between`.

## Restricted progress conditions

For a set `E` of finite executions (a usage discipline, e.g. one-shot executions or executions with
a bounded number of invocations; usually `PrefixClosed`):

* `Impl.WaitFreeOn E`, `Impl.LockFreeOn E` — wait-freedom / lock-freedom for the infinite executions all of
  whose prefixes are in `E`;
* `Impl.ObstructionFreeOn E` — a pending process running solo from a configuration reached by an
  execution of `E` returns (CSLib's `OneShotOF` is `ObstructionFreeOn OneShot`, `oneShotOF_iff`).

They are implied by the unrestricted notions and coincide with them for `E = fun _ => True`
(`waitFreeOn_true_iff`, `lockFreeOn_true_iff`, `obstructionFreeOn_true_iff`). Wait-freedom and
lock-freedom imply obstruction-freedom (`WaitFreeOn.obstructionFreeOn`,
`LockFreeOn.obstructionFreeOn`, `LockFree.obstructionFree`), and in one-shot executions with
finitely many processes wait-freedom implies lock-freedom (`WaitFreeOn.lockFreeOn`).

Intended CSLib renames: `InfExec.lbls` ↦ `InfExec.pre`, `InfExec.IsFair` ↦ `InfExec.Fair`,
`InfExec.exists_good_of_measure` ↦ `InfExec.exists_good` (generalizing the `mutexObj` versions).
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

lemma prefixClosed_oneShot [DecidableEq P] : PrefixClosed (OneShot (P := P) (A := A)) :=
  fun _ _ h => h.of_append

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-! ### Prefixes of infinite executions -/

section InfExec

variable {I}

/-- The first `t` labels of an infinite execution. -/
def InfExec.lbls (e : I.InfExec) (t : ℕ) : List (Label P A) :=
  (List.range t).map e.lbl

@[simp] lemma InfExec.lbls_zero (e : I.InfExec) : e.lbls 0 = [] := rfl

lemma InfExec.lbls_succ (e : I.InfExec) (t : ℕ) : e.lbls (t + 1) = e.lbls t ++ [e.lbl t] := by
  simp [InfExec.lbls, List.range_succ]

@[simp] lemma InfExec.length_lbls (e : I.InfExec) (t : ℕ) : (e.lbls t).length = t := by
  simp [InfExec.lbls]

lemma InfExec.run_lbls (e : I.InfExec) (t : ℕ) : I.run (e.lbls t) = some (e.cfg t) := by
  induction t with
  | zero => simp [InfExec.lbls, e.cfg_zero]
  | succ t ih =>
    rw [InfExec.lbls_succ, run_append_of_eq I ih, runFrom_singleton, e.step_eq]

lemma InfExec.valid_lbls (e : I.InfExec) (t : ℕ) : I.Valid (e.lbls t) := ⟨_, e.run_lbls t⟩

lemma InfExec.reachable_cfg (e : I.InfExec) (t : ℕ) : I.Reachable (e.cfg t) := ⟨_, e.run_lbls t⟩

lemma InfExec.lbls_prefix (e : I.InfExec) {t t' : ℕ} (h : t ≤ t') : e.lbls t <+: e.lbls t' := by
  induction t', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t' _ ih => rw [InfExec.lbls_succ]; exact ih.trans (List.prefix_append _ _)

lemma InfExec.opsOf_lbls_mono (e : I.InfExec) (p : P) {t t' : ℕ} (h : t ≤ t') :
    (opsOf (e.lbls t) p).length ≤ (opsOf (e.lbls t') p).length := by
  obtain ⟨γ, hγ⟩ := e.lbls_prefix h
  rw [← hγ, opsOf_append, List.length_append]; omega

/-- For lock objects, CSLib's `InfExec.pre` is `InfExec.lbls`. -/
lemma InfExec.pre_eq_lbls {I : Impl mutexObj B P L} (e : I.InfExec) (t : ℕ) :
    e.pre t = e.lbls t := rfl

/-! ### Pending operations along infinite executions -/

/-- A pending operation can only disappear by a response of its process. -/
lemma step_pend_none {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {p : P} (hp : C.pend p ≠ none) (hp' : C'.pend p = none) : ∃ r, ℓ = .ret p r := by
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv p' o => simp only [Label.proc] at hq; subst hq; exact absurd (step_inv h).1 hp
    | tau p' =>
      simp only [Label.proc] at hq; subst hq
      rw [(step_tau h).2.1] at hp'; exact absurd hp' hp
    | ret p' r => simp only [Label.proc] at hq; subst hq; exact ⟨r, rfl⟩
  · rw [(step_other h hq).2] at hp'; exact absurd hp' hp

/-- A process that is idle at `m₁` and pending at `m₂ ≥ m₁` invoked in between. -/
lemma InfExec.exists_inv_between (e : I.InfExec) {p : P} {m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (h₁ : (e.cfg m₁).pend p = none) (h₂ : (e.cfg m₂).pend p ≠ none) :
    ∃ t, m₁ ≤ t ∧ t < m₂ ∧ ∃ o, e.lbl t = .inv p o := by
  induction m₂, h using Nat.le_induction with
  | base => exact absurd h₁ h₂
  | succ m hle ih =>
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h₂
    rcases step_pend_some (e.step_eq m) ho with h | h
    · obtain ⟨t, ht1, ht2, o', ho'⟩ := ih (by rw [h]; simp)
      exact ⟨t, ht1, by omega, o', ho'⟩
    · exact ⟨m, hle, by omega, o, h⟩

/-- A process that is pending at `m₁` and idle at `m₂ ≥ m₁` returned in between. -/
lemma InfExec.exists_ret_between (e : I.InfExec) {p : P} {m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (h₁ : (e.cfg m₁).pend p ≠ none) (h₂ : (e.cfg m₂).pend p = none) :
    ∃ t, m₁ ≤ t ∧ t < m₂ ∧ ∃ r, e.lbl t = .ret p r := by
  induction m₂, h using Nat.le_induction with
  | base => exact absurd h₂ h₁
  | succ m hle ih =>
    by_cases hm : (e.cfg m).pend p = none
    · obtain ⟨t, ht1, ht2, r, hr⟩ := ih hm
      exact ⟨t, ht1, by omega, r, hr⟩
    · obtain ⟨r, hr⟩ := step_pend_none (e.step_eq m) hm h₂
      exact ⟨m, hle, by omega, r, hr⟩

/-- Steps of other processes do not change the local state and pending operation of `q`. -/
lemma InfExec.cfg_add_of_proc_ne (e : I.InfExec) {t k : ℕ} {q : P}
    (h : ∀ j < k, (e.lbl (t + j)).proc ≠ q) :
    (e.cfg (t + k)).loc q = (e.cfg t).loc q ∧ (e.cfg (t + k)).pend q = (e.cfg t).pend q := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := step_other (e.step_eq (t + k)) (h k (by omega))
    rw [← Nat.add_assoc, h2.1, h2.2]
    exact h1

/-! ### Fairness and progress by a measure -/

/-- An infinite execution is *fair* if every process with a pending operation eventually takes a
step (internal step or response). -/
def InfExec.IsFair (e : I.InfExec) : Prop :=
  ∀ p t, (e.cfg t).pend p ≠ none → ∃ t' ≥ t, (e.lbl t').proc = p ∧ (e.lbl t').IsStep

/-- For lock objects, CSLib's `InfExec.Fair` is `InfExec.IsFair`. -/
lemma InfExec.fair_iff_isFair {I : Impl mutexObj B P L} (e : I.InfExec) : e.Fair ↔ e.IsFair :=
  Iff.rfl

/-- Under fairness, a pending process eventually takes a step; its first step is taken in its
current local state. -/
lemma InfExec.first_act (e : I.InfExec) (hfair : e.IsFair) {q : P} {t : ℕ}
    (hp : (e.cfg t).pend q ≠ none) :
    ∃ t' ≥ t, (e.lbl t').proc = q ∧ (e.lbl t').IsStep ∧ (e.cfg t').loc q = (e.cfg t).loc q ∧
      (e.cfg t').pend q = (e.cfg t).pend q := by
  classical
  have hex : ∃ k, (e.lbl (t + k)).proc = q := by
    obtain ⟨t₁, ht₁, hq, -⟩ := hfair q t hp
    exact ⟨t₁ - t, by rw [Nat.add_sub_cancel' ht₁]; exact hq⟩
  have hc := e.cfg_add_of_proc_ne fun j hj => Nat.find_min hex hj
  refine ⟨t + Nat.find hex, by omega, Nat.find_spec hex, ?_, hc.1, hc.2⟩
  -- the first label of `q` is not an invocation, since `q` is still pending
  have hs := e.step_eq (t + Nat.find hex)
  have hq := Nat.find_spec hex
  cases hl : e.lbl (t + Nat.find hex) with
  | inv q' o =>
    rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
    exact absurd (step_inv hs).1 (hc.2 ▸ hp)
  | ret _ _ => trivial
  | tau _ => trivial

/-- **Progress by a measure.** Let `Good` be a property of times and `μ` a measure. Suppose that
from time `t` on, as long as `Good` fails, process `p` eventually takes a step, each step of `p`
makes `Good` true or decreases `μ`, and other labels make `Good` true or do not increase `μ`.
Then `Good` eventually holds. -/
lemma InfExec.exists_good_of_measure (e : I.InfExec) (p : P) (Good : ℕ → Prop) (μ : ℕ → ℕ)
    (t : ℕ)
    (hstep : ∀ t' ≥ t, ¬ Good t' → ∃ t'' ≥ t', (e.lbl t'').proc = p ∧ (e.lbl t'').IsStep)
    (hp : ∀ t' ≥ t, ¬ Good t' → (e.lbl t').proc = p → (e.lbl t').IsStep →
      Good (t' + 1) ∨ μ (t' + 1) < μ t')
    (ho : ∀ t' ≥ t, ¬ Good t' → ¬ ((e.lbl t').proc = p ∧ (e.lbl t').IsStep) →
      Good (t' + 1) ∨ μ (t' + 1) ≤ μ t') :
    ∃ t' ≥ t, Good t' := by
  by_contra hcon
  push Not at hcon
  have hmono : ∀ m ≥ t, μ (m + 1) ≤ μ m := by
    intro m hm
    by_cases hpm : (e.lbl m).proc = p ∧ (e.lbl m).IsStep
    · exact ((hp m hm (hcon m hm) hpm.1 hpm.2).resolve_left (hcon _ (by omega))).le
    · exact (ho m hm (hcon m hm) hpm).resolve_left (hcon _ (by omega))
  obtain ⟨T, hT, hc⟩ := Nat.eventually_not_of_succ_le hmono
    (p := fun m => (e.lbl m).proc = p ∧ (e.lbl m).IsStep)
    fun m hm hpm => (hp m hm (hcon m hm) hpm.1 hpm.2).resolve_left (hcon _ (by omega))
  obtain ⟨t'', ht'', hpt⟩ := hstep T hT (hcon T hT)
  exact hc t'' ht'' hpt

end InfExec

/-! ### Progress conditions restricted to a set of executions -/

/-- Wait-freedom for the infinite executions whose prefixes are all in `E`. -/
def WaitFreeOn (E : List (Label P A) → Prop) : Prop :=
  ∀ e : I.InfExec, (∀ t, E (e.lbls t)) → ∀ (p : P) (n : ℕ),
    (∀ m ≥ n, (e.cfg m).pend p ≠ none) → ∃ N, ∀ m ≥ N, e.lbl m ≠ .tau p

/-- Lock-freedom for the infinite executions whose prefixes are all in `E`. -/
def LockFreeOn (E : List (Label P A) → Prop) : Prop :=
  ∀ e : I.InfExec, (∀ t, E (e.lbls t)) → (∀ N, ∃ m ≥ N, (e.lbl m).IsStep) →
    ∀ N, ∃ m ≥ N, ∃ p r, e.lbl m = .ret p r

/-- Obstruction-freedom from the configurations reached by executions of `E`: a pending process
running solo returns. -/
def ObstructionFreeOn (E : List (Label P A) → Prop) : Prop :=
  ∀ α C p, I.run α = some C → E α → C.pend p ≠ none → ∃ k, ((I.soloStep p)^[k] C).pend p = none

variable {I}

lemma WaitFree.waitFreeOn (h : I.WaitFree) (E : List (Label P A) → Prop) : I.WaitFreeOn E :=
  fun e _ => h e

lemma LockFree.lockFreeOn (h : I.LockFree) (E : List (Label P A) → Prop) : I.LockFreeOn E :=
  fun e _ hs => h e hs

lemma ObstructionFree.obstructionFreeOn (h : I.ObstructionFree) (E : List (Label P A) → Prop) :
    I.ObstructionFreeOn E :=
  fun α _ p hα _ hp => h _ p ⟨α, hα⟩ hp

lemma waitFreeOn_true_iff : I.WaitFreeOn (fun _ => True) ↔ I.WaitFree :=
  ⟨fun h e => h e fun _ => trivial, fun h => h.waitFreeOn _⟩

lemma lockFreeOn_true_iff : I.LockFreeOn (fun _ => True) ↔ I.LockFree :=
  ⟨fun h e => h e fun _ => trivial, fun h => h.lockFreeOn _⟩

lemma obstructionFreeOn_true_iff : I.ObstructionFreeOn (fun _ => True) ↔ I.ObstructionFree :=
  ⟨fun h C p ⟨α, hα⟩ hp => h α C p hα trivial hp, fun h => h.obstructionFreeOn _⟩

/-- CSLib's one-shot obstruction-freedom is obstruction-freedom on one-shot executions. -/
lemma oneShotOF_iff : I.OneShotOF ↔ I.ObstructionFreeOn OneShot := Iff.rfl

lemma WaitFreeOn.mono {E E' : List (Label P A) → Prop} (h : I.WaitFreeOn E)
    (hE : ∀ α, E' α → E α) : I.WaitFreeOn E' :=
  fun e he => h e fun t => hE _ (he t)

lemma LockFreeOn.mono {E E' : List (Label P A) → Prop} (h : I.LockFreeOn E)
    (hE : ∀ α, E' α → E α) : I.LockFreeOn E' :=
  fun e he hs => h e (fun t => hE _ (he t)) hs

lemma ObstructionFreeOn.mono {E E' : List (Label P A) → Prop} (h : I.ObstructionFreeOn E)
    (hE : ∀ α, E' α → E α) : I.ObstructionFreeOn E' :=
  fun α C p hα he hp => h α C p hα (hE α he) hp

/-- A process that never returns when running solo from a reachable configuration yields an
infinite execution that continues the execution with internal steps of that process only. -/
lemma exists_infExec_solo {α : List (Label P A)} {C : Config A B P L} (hα : I.run α = some C)
    {p : P} (hp : ∀ k, ((I.soloStep p)^[k] C).pend p ≠ none) :
    ∃ e : I.InfExec, (∀ t, e.lbls t = α.take t ++ List.replicate (t - α.length) (.tau p)) ∧
      (∀ m ≥ α.length, e.lbl m = .tau p) ∧ ∀ m ≥ α.length, (e.cfg m).pend p ≠ none := by
  let E : ℕ → List (Label P A) := fun k => α ++ I.soloLabels p C k
  have hE : ∀ k, I.run (E k) = some ((I.soloStep p)^[k] C) := fun k => by
    simp only [E]; rw [run_append_of_eq I hα, runFrom_soloLabels]
  have hElen : ∀ k, (E k).length = α.length + k := fun k => by
    simp only [E, List.length_append, I.soloLabels_length p C k (fun i _ => hp i)]
  obtain ⟨e, hlbl, hcfg⟩ := I.exists_infExec_of_chain E
    (fun k => (List.prefix_append_right_inj α).2 (I.soloLabels_prefix p C k))
    (fun k => by rw [hElen]; omega) (fun k => ⟨_, hE k⟩)
  have hpend : ∀ m ≥ α.length, (e.cfg m).pend p ≠ none := by
    intro m hm
    have h := hcfg (m - α.length) m (by rw [hElen]; omega)
    rw [List.take_of_length_le (by rw [hElen]; omega), hE] at h
    rw [← Option.some_inj.1 h]; exact hp _
  have htau : ∀ m ≥ α.length, e.lbl m = .tau p := by
    intro m hm
    apply I.eq_tau_of_step (e.step_eq _) _ (hpend _ hm) (hpend _ (by omega))
    rw [hlbl (m + 1 - α.length) m (by rw [hElen]; omega)]
    simp only [E]
    rw [List.getElem_append_right (by omega)]
    exact I.soloLabels_proc p C _ _ (List.getElem_mem _)
  have hpre : ∀ m (hm : m < α.length), e.lbl m = α[m] := by
    intro m hm
    rw [hlbl 0 m (by rw [hElen]; omega)]
    simp only [E, soloLabels, List.append_nil]
  refine ⟨e, fun t => ?_, htau, hpend⟩
  induction t with
  | zero => simp
  | succ t ih =>
    rw [InfExec.lbls_succ, ih]
    by_cases ht : t < α.length
    · rw [hpre t ht, show t + 1 - α.length = 0 by omega, show t - α.length = 0 by omega,
        List.replicate_zero, List.append_nil, List.append_nil, List.take_add_one,
        List.getElem?_eq_getElem ht, Option.toList_some]
    · rw [htau t (by omega), List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        show t + 1 - α.length = (t - α.length) + 1 by omega, List.replicate_succ',
        List.append_assoc]

omit [DecidableEq P] in
/-- Prefixes of the infinite execution of `exists_infExec_solo` stay in `E`, if `E` is closed
under prefixes and under internal steps. -/
private lemma lbls_mem_of_solo {E : List (Label P A) → Prop} (hE : PrefixClosed E)
    (htau : ∀ α p, E α → E (α ++ [.tau p])) {α : List (Label P A)} (hα : E α) (p : P) (t : ℕ) :
    E (α.take t ++ List.replicate (t - α.length) (.tau p)) := by
  induction t with
  | zero => simpa using hE.of_prefix (List.nil_prefix) hα
  | succ t ih =>
    by_cases ht : t < α.length
    · rw [show t + 1 - α.length = 0 by omega, List.replicate_zero, List.append_nil]
      exact hE.of_prefix (List.take_prefix _ _) hα
    · rw [List.take_of_length_le (by omega)] at ih ⊢
      rw [show t + 1 - α.length = (t - α.length) + 1 by omega, List.replicate_succ',
        ← List.append_assoc]
      exact htau _ p ih

/-- Wait-freedom implies obstruction-freedom on a set of executions closed under prefixes and
internal steps. -/
theorem WaitFreeOn.obstructionFreeOn {E : List (Label P A) → Prop} (h : I.WaitFreeOn E)
    (hE : PrefixClosed E) (htau : ∀ α p, E α → E (α ++ [.tau p])) : I.ObstructionFreeOn E := by
  intro α C p hα hEα hp
  by_contra hcon
  push Not at hcon
  obtain ⟨e, hlbls, he, hpend⟩ := exists_infExec_solo hα hcon
  obtain ⟨N, hN⟩ := h e (fun t => hlbls t ▸ lbls_mem_of_solo hE htau hEα p t) p _ hpend
  exact hN (max N α.length) (le_max_left _ _) (he _ (le_max_right _ _))

/-- Lock-freedom implies obstruction-freedom on a set of executions closed under prefixes and
internal steps. -/
theorem LockFreeOn.obstructionFreeOn {E : List (Label P A) → Prop} (h : I.LockFreeOn E)
    (hE : PrefixClosed E) (htau : ∀ α p, E α → E (α ++ [.tau p])) : I.ObstructionFreeOn E := by
  intro α C p hα hEα hp
  by_contra hcon
  push Not at hcon
  obtain ⟨e, hlbls, he, -⟩ := exists_infExec_solo hα hcon
  obtain ⟨m, hm, q, r, hr⟩ := h e (fun t => hlbls t ▸ lbls_mem_of_solo hE htau hEα p t)
    (fun N => ⟨max N α.length, le_max_left _ _, by rw [he _ (le_max_right _ _)]; trivial⟩)
    α.length
  rw [he m hm] at hr
  cases hr

/-- Lock-freedom implies obstruction-freedom. -/
theorem LockFree.obstructionFree (h : I.LockFree) : I.ObstructionFree :=
  obstructionFreeOn_true_iff.1 <|
    (lockFreeOn_true_iff.2 h).obstructionFreeOn prefixClosed_true fun _ _ _ => trivial

/-- For one-shot executions with finitely many processes, wait-freedom implies lock-freedom. -/
theorem WaitFreeOn.lockFreeOn [Fintype P] {E : List (Label P A) → Prop} (h : I.WaitFreeOn E)
    (hos : ∀ α, E α → ∀ q, (opsOf α q).length ≤ 1) : I.LockFreeOn E := by
  classical
  intro e hE hsteps N₀
  by_contra hret
  push Not at hret
  -- some process takes infinitely many steps
  obtain ⟨p, hp⟩ : ∃ p, ∀ N, ∃ m ≥ N, (e.lbl m).IsStep ∧ (e.lbl m).proc = p := by
    by_contra hno
    push Not at hno
    choose Nf hNf using hno
    obtain ⟨m, hm, hs⟩ := hsteps (Finset.univ.sup Nf)
    exact hNf _ m (le_trans (Finset.le_sup (Finset.mem_univ _)) hm) hs rfl
  -- hence infinitely many `tau p` (there are no responses after `N₀`)
  have htau : ∀ N, ∃ m ≥ N, e.lbl m = .tau p := by
    intro N
    obtain ⟨m, hm, hs, hpr⟩ := hp (max N N₀)
    refine ⟨m, le_of_max_le_left hm, ?_⟩
    cases hl : e.lbl m with
    | inv q o => rw [hl] at hs; exact hs.elim
    | ret q r => exact absurd hl (hret m (le_of_max_le_right hm) q r)
    | tau q => rw [hl] at hpr; simp only [Label.proc] at hpr; rw [hpr]
  obtain ⟨m₀, -, hm₀⟩ := htau 0
  have hpend₀ : (e.cfg m₀).pend p ≠ none := by
    have hs := e.step_eq m₀; rw [hm₀] at hs; exact (step_tau hs).1
  have hinv₀ : 1 ≤ (opsOf (e.lbls m₀) p).length := by
    rcases I.run_counts (e.run_lbls m₀) p with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd h1 hpend₀
    · omega
  -- `p` stays pending forever after `m₀`
  have hpend : ∀ m ≥ m₀, (e.cfg m).pend p ≠ none := by
    intro m hm hidle
    obtain ⟨m₂, hm₂, hm₂'⟩ := htau m
    have hpend₂ : (e.cfg m₂).pend p ≠ none := by
      have hs := e.step_eq m₂; rw [hm₂'] at hs; exact (step_tau hs).1
    obtain ⟨t, ht1, -, o, ho⟩ := e.exists_inv_between hm₂ hidle hpend₂
    have hle := hos _ (hE (t + 1)) p
    rw [InfExec.lbls_succ, opsOf_append, ho] at hle
    have hmono := e.opsOf_lbls_mono p (hm.trans ht1)
    simp only [opsOf_cons, opsOf_nil, Label.invOf_inv, ite_true, Option.toList_some,
      List.append_nil, List.length_append, List.length_singleton] at hle
    omega
  obtain ⟨N, hN⟩ := h e hE p m₀ hpend
  obtain ⟨m, hm, hm'⟩ := htau N
  exact hN m hm hm'

end Impl

end Cslib.SharedMemory
