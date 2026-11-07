import Papers.PODC2012.CloserLookFT.ElectionSafety
import Cslib.Computability.Distributed.SharedMemory.Task
import Mathlib.Data.Nat.Log

/-!
# The election algorithm as a CSLib shared-memory implementation

The algorithm of Section 2.1 as an `Impl` of CSLib's asynchronous shared-memory model: `n`
processes (any finite type `P` with decidable equality, identifiers only compared), atomic
read/write registers `turn`, `done`, `V[0]`, …, `V[L-1]` (the base objects `Regs P`), the
one-shot operation `elect` with response `true` (= `1`, leader) or `false` (= `0`).

* `electionImpl L` — the implementation; `electionImpl_accessed` — it only accesses the `L + 2`
  registers `turn`, `done`, `V[0..L-1]` (with `L = ⌈log₂ n⌉` these are the paper's
  `⌈log n⌉ + 2` registers);
* `toSys` — the projection of configurations onto the transition system of `ElectionCore.lean`;
  `reach_toSys` — reachable configurations project to reachable states;
* `election_safety` — **Theorem 2.4** for the implementation: in every finite execution at most one
  process returns `1`.

A process that is invoked again after returning returns its first answer again (one-shot
objects only constrain one-shot executions; this keeps the implementation total).
-/

namespace Podc.CloserLookFT

open Cslib.SharedMemory

/-- Names of the shared registers of one election object. -/
inductive Reg where
  /-- `e.turn` -/
  | turn
  /-- `e.done` -/
  | done
  /-- `e.V[k + 1]` -/
  | v (k : ℕ)
  deriving DecidableEq

/-- The base objects: atomic registers; `turn` and `V[k]` hold identifiers or `0` (`none`),
`done` is a bit. -/
@[reducible] def Regs (P : Type) : Reg → ObjSpec
  | .turn => register (Option P) none
  | .done => register Bool false
  | .v _ => register (Option P) none

/-- The election object: one-shot operation `elect`, response `1` (`true`) or `0` (`false`). -/
abbrev ElectObj : ObjSpec := taskObj Unit Bool

variable {P : Type} [DecidableEq P]

/-- The program of process `p` (one atomic register access per step, see `estep`). -/
def electAct (L : ℕ) (p : P) : ELoc → Action ElectObj (Regs P) ELoc
  | .idle => .ret false .idle
  | .start => .access .turn (.write (some p)) fun _ => if 0 < L then .rdone 0 else .wdone
  | .rdone k => .access .done .read fun b => if b then .out false k k 0 else .rturn k
  | .rturn k => .access .turn .read fun t => if t = some p then .rv k else nextClr k k 0
  | .rv k => .access (.v k) .read fun v => if v = none then .wv k else .rdone k
  | .wv k => .access (.v k) (.write (some p)) fun _ => .rturn2 k
  | .rturn2 k => .access .turn .read fun t =>
      if t = some p then (if k + 1 < L then .rdone (k + 1) else .wdone) else nextClr k (k + 1) 0
  | .clr k b j => .access (.v j) .read fun v => if v = some p then .clw k b j
      else nextClr k b (j + 1)
  | .clw k b j => .access (.v j) (.write none) fun _ => nextClr k b (j + 1)
  | .wdone => .access .done (.write true) fun _ => .out true L L 0
  | .out r a w c => .ret r (.out r a w c)

/-- The almost-wait-free symmetric election algorithm with `L` levels (Section 2.1). -/
def electionImpl (L : ℕ) : Impl ElectObj (Regs P) P ELoc where
  memInit
    | .turn => none
    | .done => false
    | .v _ => none
  locInit _ := .idle
  invoke _ l _ := if l = .idle then .start else l
  act := electAct L

/-- The registers accessed by a process in local state `l` (`none`: no access). -/
def ELoc.reg : ELoc → Option Reg
  | .idle | .out .. => none
  | .start | .rturn _ | .rturn2 _ => some .turn
  | .rdone _ | .wdone => some .done
  | .rv k | .wv k => some (.v k)
  | .clr _ _ j | .clw _ _ j => some (.v j)

/-- Register usage: every register access of a process in a well-formed local state is to
`turn`, `done` or `V[k]` with `k < L` — `L + 2` registers in total (`⌈log n⌉ + 2` for
`L = ⌈log₂ n⌉`). -/
theorem electionImpl_accessed {L : ℕ} (p : P) (l : ELoc) (hl : l.WF L) {i : Reg}
    {o : (Regs P i).Op} {k : (Regs P i).Resp → ELoc}
    (h : (electionImpl (P := P) L).act p l = .access i o k) :
    i = .turn ∨ i = .done ∨ ∃ j < L, i = .v j := by
  cases l <;> simp only [electionImpl, electAct, Action.access.injEq, reduceCtorEq] at h <;>
    (try obtain ⟨rfl, -⟩ := h) <;> simp_all [ELoc.WF] <;> omega

/-- The projection of a configuration to the transition system of `ElectionCore.lean`. -/
def toSys (C : Config ElectObj (Regs P) P ELoc) : ESys P :=
  ⟨⟨C.mem .turn, C.mem .done, fun k => C.mem (.v k)⟩, C.loc⟩

lemma toSys_init (L : ℕ) : toSys (electionImpl (P := P) L).initCfg = ESys.init P := by
  simp only [toSys, Impl.initCfg, electionImpl, ESys.init, EMem.init]

omit [DecidableEq P] in
lemma mem_update_v {m : (i : Reg) → (Regs P i).State} {j : ℕ} {x : Option P} (k : ℕ) :
    Function.update m (Reg.v j) x (Reg.v k) = if k = j then x else m (Reg.v k) := by
  by_cases h : k = j
  · subst h; simp
  · rw [Function.update_of_ne (by simpa using h)]; simp [h]

lemma toSys_step_inv {L : ℕ} {C C' : Config ElectObj (Regs P) P ELoc} {p : P} {o : Unit}
    (h : (electionImpl (P := P) L).step C (.inv p o) = some C') :
    toSys C' = (toSys C).invoke p := by
  obtain ⟨-, -, -, hloc, hmem⟩ := Impl.step_inv h
  simp only [toSys, ESys.invoke, hloc, hmem]
  simp only [electionImpl]
  split_ifs with h1
  · simp [h1]
  · simp [h1]

lemma toSys_step_ret {L : ℕ} {C C' : Config ElectObj (Regs P) P ELoc} {p : P} {r : Bool}
    (h : (electionImpl (P := P) L).step C (.ret p r) = some C') :
    toSys C' = toSys C ∧ (C.loc p = .idle ∧ r = false ∨ ∃ a w c, C.loc p = .out r a w c) := by
  obtain ⟨-, -, hmem, l, hact, hloc⟩ := Impl.step_ret h
  have : l = C.loc p := by
    cases hl : C.loc p <;> simp [electionImpl, electAct, hl] at hact <;> grind
  refine ⟨by simp only [toSys, hmem, hloc, this, Function.update_eq_self], ?_⟩
  cases hl : C.loc p <;> simp [electionImpl, electAct, hl] at hact <;> grind

lemma toSys_step_tau {L : ℕ} {C C' : Config ElectObj (Regs P) P ELoc} {p : P}
    (h : (electionImpl (P := P) L).step C (.tau p) = some C') :
    toSys C' = (toSys C).step L p ∧ C.pend p ≠ none ∧ C.loc p ≠ .idle ∧
      ∀ r a w c, C.loc p ≠ .out r a w c := by
  obtain ⟨hp, -, -⟩ := Impl.step_tau h
  cases hl : C.loc p with
  | idle =>
    rw [Impl.step] at h; simp [hp, electionImpl, electAct, hl] at h
  | out r a w c =>
    rw [Impl.step] at h; simp [hp, electionImpl, electAct, hl] at h
  | _ =>
    rw [Impl.step_tau_eq_some hp (by simp only [electionImpl, electAct, hl]; rfl)] at h
    cases h
    refine ⟨?_, hp, by simp, by simp⟩
    simp only [toSys, ESys.step, estep, hl]
    congr 1
    all_goals (congr 1 <;> (try funext k) <;> simp [mem_update_v, Function.update_apply] <;>
      (try (rintro rfl; rfl)))

/-- One step of the implementation is a step, an invocation or a no-op of the transition
system. -/
lemma toSys_step {L : ℕ} {C C' : Config ElectObj (Regs P) P ELoc} {ℓ : Label P ElectObj}
    (h : (electionImpl (P := P) L).step C ℓ = some C') :
    toSys C' = toSys C ∨ (∃ p, toSys C' = (toSys C).step L p) ∨
      ∃ p, toSys C' = (toSys C).invoke p := by
  cases ℓ with
  | inv p o => exact Or.inr (Or.inr ⟨p, toSys_step_inv h⟩)
  | ret p r => exact Or.inl (toSys_step_ret h).1
  | tau p => exact Or.inr (Or.inl ⟨p, (toSys_step_tau h).1⟩)

/-- Reachable configurations of the implementation project to reachable states. -/
theorem reach_toSys {L : ℕ} {C : Config ElectObj (Regs P) P ELoc}
    (hC : (electionImpl (P := P) L).Reachable C) : EReach L (toSys C) := by
  obtain ⟨α, hα⟩ := hC
  refine Impl.run_induction (Q := fun _ C => EReach L (toSys C)) ?_ ?_ hα
  · rw [toSys_init]; exact EReach.init
  · intro α C ℓ C' _ ih h
    rcases toSys_step h with e | ⟨p, e⟩ | ⟨p, e⟩ <;> rw [e]
    · exact ih
    · exact ih.step p
    · exact ih.invoke p

lemma ESys.elected_step {L : ℕ} {s : ESys P} {p : P} (h : (s.loc p).Elected) (q : P) :
    ((s.step L q).loc p).Elected := by
  by_cases hq : q = p
  · subst hq
    simp only [ESys.step, Function.update_self]
    cases hl : s.loc q <;> rw [hl] at h <;> simp_all [ELoc.Elected, estep]
  · simpa [ESys.step, Function.update_of_ne (Ne.symm hq)] using h

lemma ESys.elected_invoke {s : ESys P} {p : P} (h : (s.loc p).Elected) (q : P) :
    ((s.invoke q).loc p).Elected := by
  unfold ESys.invoke
  split_ifs with hq
  · by_cases hqp : q = p
    · subst hqp; rw [hq] at h; simp [ELoc.Elected] at h
    · simpa [Function.update_of_ne (Ne.symm hqp)] using h
  · exact h

/-- A process that has returned `1` is elected in every later configuration. -/
lemma elected_of_ret_mem {L : ℕ} {α : List (Label P ElectObj)}
    {C : Config ElectObj (Regs P) P ELoc} (hα : (electionImpl (P := P) L).run α = some C) :
    ∀ p, Label.ret p true ∈ α → (C.loc p).Elected := by
  refine Impl.run_induction (Q := fun α C => ∀ p, Label.ret p true ∈ α → (C.loc p).Elected)
    (by simp) ?_ hα
  intro α C ℓ C' _ ih h p hp
  have hpers : (C.loc p).Elected → (C'.loc p).Elected := fun he => by
    rcases toSys_step h with e | ⟨q, e⟩ | ⟨q, e⟩
    · have : C'.loc = C.loc := congrArg ESys.loc e
      rw [this]; exact he
    · have := congrArg ESys.loc e
      simp only [toSys] at this; rw [this]; exact ESys.elected_step he q
    · have := congrArg ESys.loc e
      simp only [toSys] at this; rw [this]; exact ESys.elected_invoke he q
  rcases List.mem_append.1 hp with hp | hp
  · exact hpers (ih p hp)
  · simp only [List.mem_singleton] at hp
    subst hp
    obtain ⟨-, -, -, l, hact, hloc⟩ := Impl.step_ret h
    rw [hloc, Function.update_self]
    cases hl : C.loc p <;> simp [electionImpl, electAct, hl] at hact <;>
      (obtain ⟨rfl, rfl⟩ := hact) <;> simp [ELoc.Elected]

/-- **Theorem 2.4 (safety)** for the implementation: with `L` levels and at most `2^L`
processes (in particular `L = ⌈log₂ n⌉`), in every finite execution at most one process
returns `1`. -/
theorem election_safety {L : ℕ} [Fintype P] (hn : Fintype.card P ≤ 2 ^ L)
    {α : List (Label P ElectObj)} (hα : (electionImpl (P := P) L).Valid α) {p q : P}
    (hp : Label.ret p true ∈ α) (hq : Label.ret q true ∈ α) : p = q := by
  obtain ⟨C, hC⟩ := hα
  exact (reach_toSys ⟨α, hC⟩).elected_unique hn (elected_of_ret_mem hC p hp)
    (elected_of_ret_mem hC q hq)

/-- `L = ⌈log₂ n⌉` levels suffice: `n ≤ 2^⌈log₂ n⌉`. -/
lemma card_le_two_pow_clog [Fintype P] : Fintype.card P ≤ 2 ^ Nat.clog 2 (Fintype.card P) :=
  Nat.le_pow_clog (by norm_num) _

end Podc.CloserLookFT
