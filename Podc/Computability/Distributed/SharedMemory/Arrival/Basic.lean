import Cslib.Computability.Distributed.SharedMemory.Spec
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Arrival/Basic.lean

/-!
# Asynchronous shared memory with (possibly infinitely many) arriving processes

A small model of wait-free one-shot tasks (consensus) in asynchronous shared memory, in which the
set of processes may be infinite (arrival models of Gafni–Merritt–Taubenfeld and Aguilera):

* processes `P` (any type; `ℕ` for the arrival models), deterministic state machines; process `p`
  starts in the local state `A.init p x` determined by its input `x` ("processes start with their
  inputs"); a process *arrives* at its first step;
* shared objects indexed by `ι` (any type), object `i` has the deterministic sequential
  specification `T i : ObjSpec` and initial state `A.mem₀ i` (`ObjSpec.init` is ignored). All of
  them exist from the start: an arbitrary (possibly infinite) `ι` models *infinite memory
  allocation*; a finite `ι` models an algorithm that only uses the objects allocated at set-up;
* a local state either *outputs* a value (`Act.out v`; steps taken in an output state are no-ops)
  or is poised to apply the operation `o` to the object `i` and continue with `k r` on response
  `r` (`Act.access i o k`). Every step that is not a no-op is exactly one operation on one atomic
  object (local computation is folded into the continuation);
* a finite execution is a schedule `σ : List P` (each entry is one step of that process), an
  infinite one a sequence `s : ℕ → P`; processes that stop taking steps have crashed.

This is the crash-stop analogue of `Cslib.SharedMemory.Recoverable` (same `Act`/`Alg`/`Cfg` shape),
generalised from `Fin n` processes with binary inputs to any process type `P` and any input/output
types; the two should eventually share one core (Recoverable = this model + crash events).

Correctness of a consensus algorithm `A : Alg T P V V` w.r.t. a set `Adm` of admissible finite
schedules and a class `K` of infinite schedules (`SolvesCons`):

* **agreement**: the processes that took a step and output a value output the same value;
* **validity**: an output value is the input of a process that took a step;
* **wait-freedom**: in every infinite schedule of `K`, a process taking infinitely many steps
  eventually outputs.

The arrival models over `P = ℕ` are classes of infinite schedules: `infArrival` (all schedules;
model `M₃` of Perrin–Mostéfaoui–Bonin), `finArrival` (finitely many processes take steps; `M₂`),
`boundedBy n` (only `p₀, …, p_{n-1}` take steps; `Mⁿ₁`).

## Main definitions

* `Act`, `Alg`, `Cfg`, `Cfg.step`, `Alg.run`, `Alg.initCfg`, `Alg.exec`, `Cfg.Out`, `Cfg.Poised`
* `pre`, `InfOften`, `Agreement`, `Validity`, `WeakValidity`, `WaitFree`, `SolvesCons`
* `infArrival`, `finArrival`, `boundedBy`, `belowN`
* `AgreeOn`: same memory and same local states of the processes of a set

## Main statements

* `Alg.run_append`, `Cfg.Out.run`: outputs are irrevocable
* `Alg.run_agreeOn`: runs of processes of `Q` preserve `AgreeOn Q`
* `exists_infOften_of_finite`: an infinite schedule over finitely many processes has a process
  that takes infinitely many steps
* `exists_seq_of_chain`: a chain of finite schedules with growing lengths has a limit
-/

namespace Cslib.SharedMemory.Arrival

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {ι : Type} (T : ι → ObjSpec)

/-- What a process does next: apply `o` to object `i` and continue with `k` applied to the
response, or output `v`. -/
inductive Act (L V : Type) where
  /-- Apply operation `o` to object `i`, continue in local state `k r`. -/
  | access (i : ι) (o : (T i).Op) (k : (T i).Resp → L)
  /-- Output state with value `v`. -/
  | out (v : V)

/-- A deterministic algorithm for processes `P` with inputs `In` and outputs `Out`, using the
shared objects `T`. -/
structure Alg (P In Out : Type) where
  /-- Local states. -/
  L : Type
  /-- Initial local state of a process with a given input. -/
  init : P → In → L
  /-- Next action in a local state. -/
  act : L → Act T L Out
  /-- Initial states of the shared objects. -/
  mem₀ : (i : ι) → (T i).State

variable {T} {P X Y : Type} (A : Alg T P X Y)

/-- A configuration: local states and states of the shared objects. -/
@[ext] structure Cfg where
  /-- Local states. -/
  loc : P → A.L
  /-- States of the shared objects. -/
  mem : (i : ι) → (T i).State

variable {A}

/-- `p` is in an output state with value `v`. -/
def Cfg.Out (C : Cfg A) (p : P) (v : Y) : Prop := A.act (C.loc p) = .out v

/-- `p` is poised to access object `i`. -/
def Cfg.Poised (C : Cfg A) (p : P) (i : ι) : Prop := ∃ o k, A.act (C.loc p) = .access i o k

variable [DecidableEq P] [DecidableEq ι]

/-- The next step of `p` (a no-op if `p` is in an output state). -/
def Cfg.step (C : Cfg A) (p : P) : Cfg A :=
  match A.act (C.loc p) with
  | .access i o k => ⟨Function.update C.loc p (k ((T i).δ (C.mem i) o).2),
      Function.update C.mem i ((T i).δ (C.mem i) o).1⟩
  | .out _ => C

namespace Alg

variable (A)

/-- The configuration reached from `C` by the schedule `σ`. -/
def run (C : Cfg A) (σ : List P) : Cfg A := σ.foldl Cfg.step C

/-- The initial configuration for the input vector `x`. -/
def initCfg (x : P → X) : Cfg A := ⟨fun p => A.init p (x p), A.mem₀⟩

/-- The configuration reached by the schedule `σ` from the initial configuration with inputs
`x`. -/
def exec (x : P → X) (σ : List P) : Cfg A := A.run (A.initCfg x) σ

variable {A}

@[simp] lemma run_nil (C : Cfg A) : A.run C [] = C := rfl

@[simp] lemma run_cons (C : Cfg A) (p : P) (σ : List P) :
    A.run C (p :: σ) = A.run (C.step p) σ := rfl

lemma run_append (C : Cfg A) (σ τ : List P) : A.run C (σ ++ τ) = A.run (A.run C σ) τ := by
  simp [run, List.foldl_append]

lemma run_concat (C : Cfg A) (σ : List P) (p : P) : A.run C (σ ++ [p]) = (A.run C σ).step p := by
  simp [run_append]

lemma exec_append (x : P → X) (σ τ : List P) :
    A.exec x (σ ++ τ) = A.run (A.exec x σ) τ := run_append _ _ _

lemma exec_concat (x : P → X) (σ : List P) (p : P) :
    A.exec x (σ ++ [p]) = (A.exec x σ).step p := run_concat _ _ _

@[simp] lemma exec_nil (x : P → X) : A.exec x [] = A.initCfg x := rfl

end Alg

namespace Cfg

lemma step_of_out {C : Cfg A} {p : P} {v : Y} (h : C.Out p v) : C.step p = C := by
  unfold step; rw [h]

lemma step_of_access {C : Cfg A} {p : P} {i : ι} {o : (T i).Op} {k : (T i).Resp → A.L}
    (h : A.act (C.loc p) = .access i o k) :
    C.step p = ⟨Function.update C.loc p (k ((T i).δ (C.mem i) o).2),
      Function.update C.mem i ((T i).δ (C.mem i) o).1⟩ := by
  unfold step; rw [h]

lemma step_loc_self_of_access {C : Cfg A} {p : P} {i : ι} {o : (T i).Op}
    {k : (T i).Resp → A.L} (h : A.act (C.loc p) = .access i o k) :
    (C.step p).loc p = k ((T i).δ (C.mem i) o).2 := by
  rw [step_of_access h]; simp

lemma step_mem_self_of_access {C : Cfg A} {p : P} {i : ι} {o : (T i).Op}
    {k : (T i).Resp → A.L} (h : A.act (C.loc p) = .access i o k) :
    (C.step p).mem i = ((T i).δ (C.mem i) o).1 := by
  rw [step_of_access h]; simp

lemma step_mem_other {C : Cfg A} {p : P} {i j : ι} {o : (T i).Op}
    {k : (T i).Resp → A.L} (h : A.act (C.loc p) = .access i o k) (hj : j ≠ i) :
    (C.step p).mem j = C.mem j := by
  rw [step_of_access h]; simp [Function.update_of_ne hj]

lemma step_loc_other (C : Cfg A) {p q : P} (h : q ≠ p) : (C.step p).loc q = C.loc q := by
  unfold step
  split
  · simp [Function.update_of_ne h]
  · rfl

/-- A step of a process that is not poised on `j` leaves object `j` unchanged. -/
lemma step_mem_of_not_poised (C : Cfg A) {p : P} {j : ι} (h : ¬ C.Poised p j) :
    (C.step p).mem j = C.mem j := by
  unfold step
  split
  · rename_i i o k hact
    have hij : j ≠ i := by rintro rfl; exact h ⟨o, k, hact⟩
    simp [Function.update_of_ne hij]
  · rfl

lemma Out.step {C : Cfg A} {p : P} {v : Y} (h : C.Out p v) (q : P) : (C.step q).Out p v := by
  by_cases hq : p = q
  · subst hq; rw [step_of_out h]; exact h
  · unfold Cfg.Out; rw [step_loc_other C hq]; exact h

lemma Out.unique {C : Cfg A} {p : P} {v w : Y} (hv : C.Out p v) (hw : C.Out p w) : v = w := by
  unfold Cfg.Out at hv hw; rw [hv] at hw; exact Act.out.inj hw

lemma not_out_of_poised {C : Cfg A} {p : P} {i : ι} (h : C.Poised p i) (v : Y) :
    ¬ C.Out p v := by
  obtain ⟨o, k, h⟩ := h; unfold Cfg.Out; rw [h]; exact fun h => by cases h

lemma Poised.unique {C : Cfg A} {p : P} {i j : ι} (hi : C.Poised p i) (hj : C.Poised p j) :
    i = j := by
  obtain ⟨o, k, hi⟩ := hi; obtain ⟨o', k', hj⟩ := hj
  rw [hi] at hj; cases hj; rfl

/-- Every process is either in an output state or poised on some object. -/
lemma out_or_poised (C : Cfg A) (p : P) : (∃ v, C.Out p v) ∨ ∃ i, C.Poised p i := by
  unfold Cfg.Out Cfg.Poised
  cases A.act (C.loc p) with
  | access i o k => exact Or.inr ⟨i, o, k, rfl⟩
  | out v => exact Or.inl ⟨v, rfl⟩

end Cfg

namespace Alg

lemma run_loc_other (C : Cfg A) (σ : List P) {q : P} (h : q ∉ σ) :
    (A.run C σ).loc q = C.loc q := by
  induction σ generalizing C with
  | nil => rfl
  | cons p σ ih =>
    simp only [List.mem_cons, not_or] at h
    rw [run_cons, ih _ h.2, Cfg.step_loc_other _ h.1]

lemma Cfg.Out.run {C : Cfg A} {p : P} {v : Y} (h : C.Out p v) (σ : List P) :
    (A.run C σ).Out p v := by
  induction σ generalizing C with
  | nil => exact h
  | cons q σ ih => exact ih (h.step q)

lemma run_of_out_all (C : Cfg A) (σ : List P) (h : ∀ p ∈ σ, ∃ v, C.Out p v) : A.run C σ = C := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨v, hv⟩ := h p (by simp)
    rw [run_cons, Cfg.step_of_out hv]
    exact ih (fun q hq => h q (by simp [hq]))

end Alg

namespace Alg

/-- A block of steps: distinct processes `ws`, those satisfying `on` poised on object `i` (with
operations `o q`), the others poised on other objects. If the responses of the operations `o q`
are a constant `r0` on the states satisfying an invariant `Q` (preserved by them), then object
`i` ends in the state obtained by applying the operations of the `on`-processes in order, and
each `on`-process continues with `k q r0`. -/
lemma run_on (C : Cfg A) (i : ι) (ws : List P) (hnd : ws.Nodup) (on : P → Prop)
    [DecidablePred on] (o : P → (T i).Op) (r0 : (T i).Resp) (k : P → (T i).Resp → A.L)
    (Q : (T i).State → Prop) (hQ : Q (C.mem i))
    (hblind : ∀ q ∈ ws, on q → ∀ s, Q s → ((T i).δ s (o q)).2 = r0 ∧ Q ((T i).δ s (o q)).1)
    (hon : ∀ q ∈ ws, on q → A.act (C.loc q) = .access i (o q) (k q))
    (hoff : ∀ q ∈ ws, ¬ on q → ∃ j, j ≠ i ∧ C.Poised q j) :
    (A.run C ws).mem i = (T i).runOps (C.mem i) ((ws.filter on).map o) ∧
      Q ((A.run C ws).mem i) ∧ ∀ q ∈ ws, on q → (A.run C ws).loc q = k q r0 := by
  induction ws generalizing C with
  | nil => exact ⟨rfl, hQ, fun _ h => by simp at h⟩
  | cons r ws ih =>
    obtain ⟨hrws, hnd'⟩ := List.nodup_cons.1 hnd
    have hloc : ∀ q ∈ ws, (C.step r).loc q = C.loc q := fun q hq =>
      Cfg.step_loc_other C (fun e => hrws (e ▸ hq))
    rw [run_cons]
    by_cases hr : on r
    · have hact := hon r (by simp) hr
      obtain ⟨h1, h2⟩ := hblind r (by simp) hr (C.mem i) hQ
      obtain ⟨ih1, ih2, ih3⟩ := ih (C.step r) hnd'
        (by rw [Cfg.step_mem_self_of_access hact]; exact h2)
        (fun q hq => hblind q (by simp [hq]))
        (fun q hq hon' => by rw [hloc q hq]; exact hon q (by simp [hq]) hon')
        (fun q hq hon' => by
          obtain ⟨j, hj, hp⟩ := hoff q (by simp [hq]) hon'
          exact ⟨j, hj, by unfold Cfg.Poised; rw [hloc q hq]; exact hp⟩)
      refine ⟨?_, ih2, fun q hq hon' => ?_⟩
      · rw [ih1, Cfg.step_mem_self_of_access hact]; simp [hr]
      · rcases List.mem_cons.1 hq with rfl | hq
        · rw [run_loc_other _ _ hrws, Cfg.step_loc_self_of_access hact, h1]
        · exact ih3 q hq hon'
    · obtain ⟨j, hj, o', k', hact⟩ := hoff r (by simp) hr
      obtain ⟨ih1, ih2, ih3⟩ := ih (C.step r) hnd'
        (by rw [Cfg.step_mem_other hact (Ne.symm hj)]; exact hQ)
        (fun q hq => hblind q (by simp [hq]))
        (fun q hq hon' => by rw [hloc q hq]; exact hon q (by simp [hq]) hon')
        (fun q hq hon' => by
          obtain ⟨j, hj, hp⟩ := hoff q (by simp [hq]) hon'
          exact ⟨j, hj, by unfold Cfg.Poised; rw [hloc q hq]; exact hp⟩)
      refine ⟨?_, ih2, fun q hq hon' => ?_⟩
      · rw [ih1, Cfg.step_mem_other hact (Ne.symm hj)]; simp [hr]
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact absurd hon' hr
        · exact ih3 q hq hon'

end Alg

/-! ### Agreement of configurations -/

/-- `C` and `D` have the same memory and the same local states of the processes of `Q`. -/
def AgreeOn (Q : Set P) (C D : Cfg A) : Prop := C.mem = D.mem ∧ ∀ p ∈ Q, C.loc p = D.loc p

namespace AgreeOn

lemma refl (Q : Set P) (C : Cfg A) : AgreeOn Q C C := ⟨rfl, fun _ _ => rfl⟩

lemma symm {Q : Set P} {C D : Cfg A} (h : AgreeOn Q C D) : AgreeOn Q D C :=
  ⟨h.1.symm, fun p hp => (h.2 p hp).symm⟩

lemma mono {Q Q' : Set P} {C D : Cfg A} (h : AgreeOn Q C D) (hQ : Q' ⊆ Q) : AgreeOn Q' C D :=
  ⟨h.1, fun p hp => h.2 p (hQ hp)⟩

lemma step {Q : Set P} {C D : Cfg A} (h : AgreeOn Q C D) {p : P} (hp : p ∈ Q) :
    AgreeOn Q (C.step p) (D.step p) := by
  have hl := h.2 p hp
  unfold Cfg.step
  rw [hl, h.1]
  split
  · refine ⟨rfl, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; simp
    · simp [Function.update_of_ne hqp, h.2 q hq]
  · exact ⟨h.1, fun q hq => h.2 q hq⟩

lemma out_iff {Q : Set P} {C D : Cfg A} (h : AgreeOn Q C D) {p : P} (hp : p ∈ Q) (v : Y) :
    C.Out p v ↔ D.Out p v := by
  unfold Cfg.Out; rw [h.2 p hp]

lemma poised_iff {Q : Set P} {C D : Cfg A} (h : AgreeOn Q C D) {p : P} (hp : p ∈ Q) (i : ι) :
    C.Poised p i ↔ D.Poised p i := by
  unfold Cfg.Poised; rw [h.2 p hp]

end AgreeOn

lemma Alg.run_agreeOn {Q : Set P} {C D : Cfg A} (h : AgreeOn Q C D) {σ : List P}
    (hσ : ∀ p ∈ σ, p ∈ Q) : AgreeOn Q (A.run C σ) (A.run D σ) := by
  induction σ generalizing C D with
  | nil => exact h
  | cons p σ ih =>
    exact ih (h.step (hσ p (by simp))) (fun q hq => hσ q (by simp [hq]))

/-- The initial configurations of two input vectors that agree on `Q` agree on `Q`. -/
lemma Alg.initCfg_agreeOn {Q : Set P} {x y : P → X} (h : ∀ p ∈ Q, x p = y p) :
    AgreeOn Q (A.initCfg x) (A.initCfg y) :=
  ⟨rfl, fun p hp => by simp [Alg.initCfg, h p hp]⟩

/-! ### Infinite schedules -/

/-- The first `t` steps of the infinite schedule `s`. -/
def pre (s : ℕ → P) (t : ℕ) : List P := (List.range t).map s

/-- `p` takes infinitely many steps in `s`. -/
def InfOften (s : ℕ → P) (p : P) : Prop := ∀ N, ∃ t ≥ N, s t = p

omit [DecidableEq P] in
@[simp] lemma pre_zero (s : ℕ → P) : pre s 0 = [] := rfl

omit [DecidableEq P] in
lemma pre_succ (s : ℕ → P) (t : ℕ) : pre s (t + 1) = pre s t ++ [s t] := by
  simp [pre, List.range_succ]

omit [DecidableEq P] in
@[simp] lemma length_pre (s : ℕ → P) (t : ℕ) : (pre s t).length = t := by simp [pre]

omit [DecidableEq P] in
lemma pre_add (s : ℕ → P) (a b : ℕ) :
    pre s (a + b) = pre s a ++ pre (fun t => s (a + t)) b := by
  induction b with
  | zero => simp
  | succ b ih => rw [← Nat.add_assoc, pre_succ, ih, pre_succ]; simp

omit [DecidableEq P] in
lemma mem_pre {s : ℕ → P} {t : ℕ} {p : P} : p ∈ pre s t ↔ ∃ u < t, s u = p := by
  simp [pre]

omit [DecidableEq P] in
lemma pre_prefix (s : ℕ → P) {t t' : ℕ} (h : t ≤ t') : pre s t <+: pre s t' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pre_add]; exact List.prefix_append _ _

omit [DecidableEq P] in
/-- An infinite schedule whose steps all belong to a finite set has a process that takes
infinitely many steps. -/
lemma exists_infOften_of_finite {s : ℕ → P} {S : Set P} (hS : S.Finite) (hs : ∀ t, s t ∈ S) :
    ∃ p, InfOften s p := by
  by_contra hno
  push Not at hno
  simp only [InfOften, not_forall, not_exists, not_and] at hno
  choose N hN using hno
  obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ S, N p ≤ M := by
    refine ⟨hS.toFinset.sup N, fun p hp => ?_⟩
    exact Finset.le_sup (f := N) (hS.mem_toFinset.2 hp)
  exact hN (s M) M (hM _ (hs M)) rfl

omit [DecidableEq P] in
/-- The limit of a chain of finite schedules with unbounded lengths. -/
lemma exists_seq_of_chain (f : ℕ → List P) (hmono : ∀ k, f k <+: f (k + 1))
    (hlen : ∀ k, k ≤ (f k).length) :
    ∃ s : ℕ → P, ∀ k, pre s (f k).length = f k := by
  have hpre : ∀ {k k'}, k ≤ k' → f k <+: f k' := by
    intro k k' h
    induction h with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (hmono _)
  have hlt : ∀ t, t < (f (t + 1)).length := fun t => Nat.lt_of_lt_of_le (Nat.lt_succ_self t)
    (hlen (t + 1))
  refine ⟨fun t => (f (t + 1))[t]'(hlt t), fun k => ?_⟩
  apply List.ext_getElem (by simp)
  intro t h1 h2
  simp only [pre, List.getElem_map, List.getElem_range]
  have ht : t < (f k).length := h2
  rcases le_total k (t + 1) with hk | hk
  · have := (hpre hk).getElem ht
    exact this.symm
  · exact (hpre hk).getElem (hlt t)

/-! ### Consensus -/

section Consensus

variable {V : Type}

/-- The processes of the schedule `σ` output a common value (among those in an output state). -/
def Agreement (A : Alg T P V V) (Adm : List P → Prop) : Prop :=
  ∀ x σ, Adm σ → ∀ p ∈ σ, ∀ q ∈ σ, ∀ v w, (A.exec x σ).Out p v → (A.exec x σ).Out q w → v = w

/-- Validity: an output value is the input of a process that took a step. -/
def Validity (A : Alg T P V V) (Adm : List P → Prop) : Prop :=
  ∀ x σ, Adm σ → ∀ p ∈ σ, ∀ v, (A.exec x σ).Out p v → ∃ q ∈ σ, x q = v

/-- Weak validity: if all processes have the input `v`, every output is `v`. -/
def WeakValidity (A : Alg T P V V) (Adm : List P → Prop) : Prop :=
  ∀ v x σ, Adm σ → (∀ q, x q = v) → ∀ p ∈ σ, ∀ w, (A.exec x σ).Out p w → w = v

/-- Wait-freedom for the infinite schedules of the class `K`: a process that takes infinitely many
steps eventually outputs. -/
def WaitFree (A : Alg T P X Y) (K : (ℕ → P) → Prop) : Prop :=
  ∀ x s, K s → ∀ p, InfOften s p → ∃ t v, (A.exec x (pre s t)).Out p v

/-- `A` solves consensus (agreement, validity, wait-freedom) for the admissible finite schedules
`Adm` and the class `K` of infinite schedules. -/
structure SolvesCons (A : Alg T P V V) (Adm : List P → Prop) (K : (ℕ → P) → Prop) : Prop where
  agreement : Agreement A Adm
  validity : Validity A Adm
  waitFree : WaitFree A K

lemma Validity.weakValidity {A : Alg T P V V} {Adm : List P → Prop} (h : Validity A Adm) :
    WeakValidity A Adm := by
  intro v x σ hσ hx p hp w hw
  obtain ⟨q, -, hq⟩ := h x σ hσ p hp w hw
  rw [← hq, hx]

end Consensus

section Solo

/-- A process running solo after any finite execution eventually outputs. -/
lemma WaitFree.exists_solo_out {A : Alg T P X Y}
    (hwf : WaitFree A (fun s => (Set.range s).Finite)) (x : P → X) (α : List P) (p : P) :
    ∃ m v, (A.exec x (α ++ List.replicate (m + 1) p)).Out p v := by
  classical
  let s : ℕ → P := fun t => if h : t < α.length then α[t] else p
  have hpre : ∀ m, pre s (α.length + m) = α ++ List.replicate m p := by
    intro m
    induction m with
    | zero =>
      apply List.ext_getElem (by simp)
      intro t h1 h2
      simp only [Nat.add_zero, length_pre] at h1
      simp [pre, s, h1]
    | succ m ih =>
      rw [← Nat.add_assoc, pre_succ, ih, List.replicate_succ', List.append_assoc]
      simp [s]
  have hfin : (Set.range s).Finite := by
    apply (α.toFinset.finite_toSet.union (Set.finite_singleton p)).subset
    rintro _ ⟨t, rfl⟩
    by_cases h : t < α.length
    · left; simp [s, h, List.getElem_mem]
    · right; simp [s, h]
  have hinf : InfOften s p := by
    intro N
    exact ⟨N + α.length, by omega, by simp [s]⟩
  obtain ⟨t, v, ht⟩ := hwf x s hfin p hinf
  refine ⟨t, v, ?_⟩
  rw [← hpre]
  obtain ⟨τ, hτ⟩ := pre_prefix s (show t ≤ α.length + (t + 1) by omega)
  rw [← hτ, Alg.exec_append]
  exact Alg.Cfg.Out.run ht τ

end Solo

/-! ### Arrival models (`P = ℕ`) -/

/-- All finite schedules are admissible. -/
def anySched : List ℕ → Prop := fun _ => True

/-- Finite schedules of the processes `p₀, …, p_{n-1}`. -/
def belowN (n : ℕ) : List ℕ → Prop := fun σ => ∀ p ∈ σ, p < n

/-- Infinite arrival model `M₃`: all infinite schedules. -/
def infArrival : (ℕ → ℕ) → Prop := fun _ => True

/-- Finite arrival model `M₂`: finitely many processes take steps. -/
def finArrival : (ℕ → ℕ) → Prop := fun s => (Set.range s).Finite

/-- The classical model `Mⁿ₁`: only `p₀, …, p_{n-1}` take steps. -/
def boundedBy (n : ℕ) : (ℕ → ℕ) → Prop := fun s => ∀ t, s t < n

lemma boundedBy.finArrival {n : ℕ} {s : ℕ → ℕ} (h : boundedBy n s) : finArrival s :=
  (Set.finite_lt_nat n).subset (by rintro _ ⟨t, rfl⟩; exact h t)

lemma WaitFree.mono {A : Alg T ℕ X Y} {K K' : (ℕ → ℕ) → Prop} (h : WaitFree A K)
    (hK : ∀ s, K' s → K s) : WaitFree A K' :=
  fun x s hs => h x s (hK s hs)

end Cslib.SharedMemory.Arrival
