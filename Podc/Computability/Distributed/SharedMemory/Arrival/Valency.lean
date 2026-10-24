import Podc.Computability.Distributed.SharedMemory.Arrival.Basic

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Arrival/Valency.lean

/-!
# Valency with respect to a set of processes

Valency arguments for binary consensus algorithms in the model of `Arrival.Basic`, where an
execution is its schedule and the valency of an execution `α` is taken with respect to
extensions by the processes of a set `Q` only (`Q`-valency; with `Q = {p₀, …, p_{n-1}}` this is
the `n`-valency of Afek–Morrison–Wertheim and Perrin–Mostéfaoui–Bonin). The set of processes may
be infinite; `Q` is finite.

Assumptions: agreement for all finite schedules and wait-freedom for the infinite schedules with
finite range (so the results apply to the finite and to the infinite arrival models).

## Main definitions

* `Decides A x σ v`: some process that took a step in `σ` outputs `v`;
* `CanDec Q x α v`, `Biv Q x α`, `Crit Q x α` (bivalent, every step of a process of `Q` leads to
  a non-bivalent execution)

## Main statements

* `Biv.not_out`: in a bivalent execution no process of `Q` and no process that took a step has
  output a value
* `exists_solo_out`: a process running solo outputs (wait-freedom)
* `exists_crit`: every `Q`-bivalent execution has a `Q`-critical extension by processes of `Q`
* `Crit.exists_teams`: in a critical execution there are processes `p, q ∈ Q` whose steps lead to
  `false`-univalent and `true`-univalent executions
* `Crit.false_of_agreeOn`: two extensions of the two teams that are indistinguishable to a
  process `r ∈ Q` give a contradiction
* `Cfg.step_comm`, `Cfg.step_step_agreeOn_of_readOnly`: steps on different objects commute; a
  read-only step is invisible to other processes
-/

namespace Cslib.SharedMemory.Arrival

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {ι : Type} {T : ι → ObjSpec} {P : Type} [DecidableEq P] [DecidableEq ι]

/-! ### Commuting steps -/

namespace Cfg

variable {X Y : Type} {A : Alg T P X Y}

/-- Steps of two different processes on different objects commute. -/
lemma step_comm (C : Cfg A) {r s : P} {i j : ι} (hr : C.Poised r i) (hs : C.Poised s j)
    (hrs : r ≠ s) (hij : i ≠ j) : (C.step r).step s = (C.step s).step r := by
  obtain ⟨o, k, hr⟩ := hr
  obtain ⟨o', k', hs⟩ := hs
  have hs' : A.act ((C.step r).loc s) = .access j o' k' := by
    rw [step_loc_other C (Ne.symm hrs)]; exact hs
  have hr' : A.act ((C.step s).loc r) = .access i o k := by
    rw [step_loc_other C hrs]; exact hr
  rw [step_of_access hs', step_of_access hr', step_of_access hr, step_of_access hs]
  simp only [Function.update_of_ne hij.symm, Function.update_of_ne hij]
  congr 1
  · exact Function.update_comm hrs _ _ _
  · exact Function.update_comm hij _ _ _

/-- A read-only step of `r` (it does not change the state of the accessed object) is invisible
to every other process `s`: after `r; s` and after `s` the memory and the local state of `s`
are the same. -/
lemma step_step_agreeOn_of_readOnly (C : Cfg A) {r s : P} {i : ι} {o : (T i).Op}
    {k : (T i).Resp → A.L} (hr : A.act (C.loc r) = .access i o k)
    (hro : ((T i).δ (C.mem i) o).1 = C.mem i) (hrs : r ≠ s) :
    AgreeOn {s} ((C.step r).step s) (C.step s) := by
  have hmem : (C.step r).mem = C.mem := by
    rw [step_of_access hr]; simp only [hro, Function.update_eq_self]
  have hloc : (C.step r).loc s = C.loc s := step_loc_other C (Ne.symm hrs)
  have h : AgreeOn {s} (C.step r) C := ⟨hmem, fun p hp => by simp at hp; subst hp; exact hloc⟩
  exact h.step (by simp)

end Cfg

/-! ### Valency -/

variable (A : Alg T P Bool Bool)

/-- Some process that took a step in `σ` outputs `v` at the end of `σ`. -/
def Decides (x : P → Bool) (σ : List P) (v : Bool) : Prop := ∃ p ∈ σ, (A.exec x σ).Out p v

/-- `v` can be decided in an extension of `α` by processes of `Q`. -/
def CanDec (Q : Set P) (x : P → Bool) (α : List P) (v : Bool) : Prop :=
  ∃ β : List P, (∀ p ∈ β, p ∈ Q) ∧ Decides A x (α ++ β) v

/-- `α` is `Q`-bivalent. -/
def Biv (Q : Set P) (x : P → Bool) (α : List P) : Prop :=
  CanDec A Q x α false ∧ CanDec A Q x α true

/-- `α` is `Q`-critical: `Q`-bivalent, and the next step of any process of `Q` leads to an
execution that is not `Q`-bivalent. -/
def Crit (Q : Set P) (x : P → Bool) (α : List P) : Prop :=
  Biv A Q x α ∧ ∀ p ∈ Q, ¬ Biv A Q x (α ++ [p])

variable {A}

lemma Decides.append {x : P → Bool} {σ : List P} {v : Bool} (h : Decides A x σ v) (τ : List P) :
    Decides A x (σ ++ τ) v := by
  obtain ⟨p, hp, hout⟩ := h
  exact ⟨p, List.mem_append_left _ hp, by rw [Alg.exec_append]; exact Alg.Cfg.Out.run hout τ⟩

lemma CanDec.mono {Q Q' : Set P} {x : P → Bool} {α : List P} {v : Bool} (h : CanDec A Q x α v)
    (hQ : Q ⊆ Q') : CanDec A Q' x α v := by
  obtain ⟨β, hβ, h⟩ := h; exact ⟨β, fun p hp => hQ (hβ p hp), h⟩

lemma CanDec.of_append {Q : Set P} {x : P → Bool} {α β : List P} {v : Bool}
    (h : CanDec A Q x (α ++ β) v) (hβ : ∀ p ∈ β, p ∈ Q) : CanDec A Q x α v := by
  obtain ⟨γ, hγ, h⟩ := h
  refine ⟨β ++ γ, fun p hp => ?_, by simpa [List.append_assoc] using h⟩
  rcases List.mem_append.1 hp with hp | hp
  · exact hβ p hp
  · exact hγ p hp

lemma Biv.mono {Q Q' : Set P} {x : P → Bool} {α : List P} (h : Biv A Q x α) (hQ : Q ⊆ Q') :
    Biv A Q' x α := ⟨h.1.mono hQ, h.2.mono hQ⟩

section Agreement

variable (hag : Agreement A (fun _ => True))
include hag

/-- In a `Q`-bivalent execution, no process that took a step and no process of `Q` is in an
output state. -/
lemma Biv.not_out {Q : Set P} {x : P → Bool} {α : List P} (h : Biv A Q x α) {p : P}
    (_hp : p ∈ α ∨ p ∈ Q) (v : Bool) : ¬ (A.exec x α).Out p v := by
  intro hout
  obtain ⟨β, hβ, q, hq, hqout⟩ := (if hv : v = true then (hv ▸ h.1) else
    (by simp only [Bool.not_eq_true] at hv; exact hv ▸ h.2) : CanDec A Q x α (!v))
  have hpβ : (A.exec x (α ++ β)).Out p v := by
    rw [Alg.exec_append]; exact Alg.Cfg.Out.run hout β
  have hcfg : A.exec x (α ++ β ++ [p]) = A.exec x (α ++ β) := by
    rw [Alg.exec_concat]; exact Cfg.step_of_out hpβ
  have := hag x (α ++ β ++ [p]) trivial p (by simp) q (List.mem_append_left _ hq) v (!v)
    (by rw [hcfg]; exact hpβ) (by rw [hcfg]; exact hqout)
  cases v <;> simp at this

lemma Biv.not_decides {Q : Set P} {x : P → Bool} {α : List P} (h : Biv A Q x α) (v : Bool) :
    ¬ Decides A x α v := by
  rintro ⟨p, hp, hout⟩; exact h.not_out hag (Or.inl hp) v hout

/-- If an execution can decide `v` and some process that took a step in it outputs `w`, then
`v = w`. -/
lemma CanDec.eq_of_out {Q : Set P} {x : P → Bool} {α : List P} {v w : Bool}
    (h : CanDec A Q x α v) {p : P} (hp : p ∈ α) (hout : (A.exec x α).Out p w) : v = w := by
  obtain ⟨β, -, q, hq, hqout⟩ := h
  exact hag x (α ++ β) trivial q hq p (List.mem_append_left _ hp) v w hqout
    (by rw [Alg.exec_append]; exact Alg.Cfg.Out.run hout β)

end Agreement

section WaitFree

variable (hwf : WaitFree A (fun s => (Set.range s).Finite))
include hwf

/-- A process running solo after any finite execution eventually outputs. -/
lemma exists_solo_out (x : P → Bool) (α : List P) (p : P) :
    ∃ m v, (A.exec x (α ++ List.replicate (m + 1) p)).Out p v :=
  hwf.exists_solo_out x α p

/-- From every execution, some value can be decided by a process of a nonempty set `Q`. -/
lemma exists_canDec {Q : Set P} {p : P} (hp : p ∈ Q) (x : P → Bool) (α : List P) :
    ∃ v, CanDec A Q x α v := by
  obtain ⟨m, v, h⟩ := exists_solo_out hwf x α p
  exact ⟨v, List.replicate (m + 1) p, fun q hq => by rw [List.eq_of_mem_replicate hq]; exact hp,
    p, by simp, h⟩

/-- **Lemma 8** (generic form). Every `Q`-bivalent execution (`Q` finite) has a `Q`-critical
extension by processes of `Q`. -/
theorem exists_crit (hag : Agreement A (fun _ => True)) {Q : Set P} (hQ : Q.Finite) {x : P → Bool} {α : List P}
    (h : Biv A Q x α) : ∃ β, (∀ p ∈ β, p ∈ Q) ∧ Crit A Q x (α ++ β) := by
  classical
  by_contra hno
  push Not at hno
  -- every bivalent extension can be extended by one step keeping bivalence
  have hstep : ∀ β : {β : List P // (∀ p ∈ β, p ∈ Q) ∧ Biv A Q x (α ++ β)},
      ∃ p, p ∈ Q ∧ Biv A Q x (α ++ β.1 ++ [p]) := by
    intro ⟨β, hβQ, hβ⟩
    have := hno β hβQ
    simp only [Crit, not_and, not_forall, not_not] at this
    obtain ⟨p, hp, hb⟩ := this hβ
    exact ⟨p, hp, hb⟩
  choose nxt hnxtQ hnxt using hstep
  let st : ℕ → {β : List P // (∀ p ∈ β, p ∈ Q) ∧ Biv A Q x (α ++ β)} := fun k =>
    Nat.rec ⟨[], by simp, by simpa using h⟩
      (fun _ β => ⟨β.1 ++ [nxt β], by
          intro p hp
          rcases List.mem_append.1 hp with hp | hp
          · exact β.2.1 p hp
          · simp at hp; subst hp; exact hnxtQ β,
        by simpa [List.append_assoc] using hnxt β⟩) k
  have hst_succ : ∀ k, (st (k + 1)).1 = (st k).1 ++ [nxt (st k)] := fun k => rfl
  have hst_len : ∀ k, (st k).1.length = k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [hst_succ]; simp [ih]
  let f : ℕ → List P := fun k => α ++ (st k).1
  obtain ⟨s, hs⟩ := exists_seq_of_chain f
    (fun k => by simp only [f, hst_succ]; exact ⟨[nxt (st k)], by simp⟩)
    (fun k => by simp [f, hst_len])
  have hsf : ∀ k, pre s (α.length + k) = f k := fun k => by
    rw [← hs k]; simp [f, hst_len]
  -- the tail of `s` consists of steps of `Q`
  have htail : ∀ t, s (α.length + t) ∈ Q := by
    intro t
    have h1 := hsf (t + 1)
    rw [← Nat.add_assoc, pre_succ, hsf t] at h1
    simp only [f, hst_succ, ← List.append_assoc] at h1
    have := List.append_inj_right' h1 rfl
    simp only [List.cons.injEq, and_true] at this
    rw [this]; exact hnxtQ _
  obtain ⟨p, hp⟩ := exists_infOften_of_finite hQ htail
  have hpQ : p ∈ Q := by
    obtain ⟨t, -, ht⟩ := hp 0; rw [← ht]; exact htail t
  have hfin : (Set.range s).Finite := by
    apply ((α.toFinset.finite_toSet).union hQ).subset
    rintro _ ⟨t, rfl⟩
    by_cases ht : t < α.length
    · left
      have := hsf 0
      simp only [f, Nat.add_zero] at this
      have hst0 : (st 0).1 = [] := rfl
      rw [hst0, List.append_nil] at this
      simp only [Finset.mem_coe, List.mem_toFinset]
      rw [← this]; exact mem_pre.2 ⟨t, ht, rfl⟩
    · right
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 ht)
      exact htail d
  have hinf : InfOften s p := by
    intro N
    obtain ⟨t, ht, hpt⟩ := hp N
    exact ⟨α.length + t, by omega, hpt⟩
  obtain ⟨t, v, hout⟩ := hwf x s hfin p hinf
  have hbiv := (st t).2.2
  apply hbiv.not_out hag (Or.inr hpQ) v
  obtain ⟨τ, hτ⟩ := pre_prefix s (show t ≤ α.length + t by omega)
  rw [hsf] at hτ
  show (A.exec x (f t)).Out p v
  rw [← hτ, Alg.exec_append]
  exact Alg.Cfg.Out.run hout τ

/-- In a critical execution, the steps of `Q` split into two nonempty teams: some `p ∈ Q` leads to
an execution that can only decide `false`, some `q ∈ Q` to one that can only decide `true`. -/
theorem Crit.exists_teams (hag : Agreement A (fun _ => True)) {Q : Set P} {x : P → Bool} {α : List P} (h : Crit A Q x α) :
    ∃ p ∈ Q, ∃ q ∈ Q, CanDec A Q x (α ++ [p]) false ∧ ¬ CanDec A Q x (α ++ [p]) true ∧
      CanDec A Q x (α ++ [q]) true ∧ ¬ CanDec A Q x (α ++ [q]) false := by
  have hfirst : ∀ v, CanDec A Q x α v → ∃ p ∈ Q, CanDec A Q x (α ++ [p]) v := by
    intro v ⟨β, hβ, hd⟩
    cases β with
    | nil => exact absurd (by simpa using hd) (h.1.not_decides hag v)
    | cons p β =>
      exact ⟨p, hβ p (by simp), β, fun q hq => hβ q (by simp [hq]), by simpa using hd⟩
  obtain ⟨p, hp, hpf⟩ := hfirst false h.1.1
  obtain ⟨q, hq, hqt⟩ := hfirst true h.1.2
  exact ⟨p, hp, q, hq, hpf, fun ht => h.2 p hp ⟨hpf, ht⟩, hqt, fun hf => h.2 q hq ⟨hf, hqt⟩⟩

/-- Two executions extending the two teams of a critical execution cannot be indistinguishable to
a process `r ∈ Q`: running `r` solo would decide the same value in both. -/
theorem false_of_agreeOn {Q : Set P} {x : P → Bool} {α β γ : List P} {p q r : P}
    (hpf : ¬ CanDec A Q x (α ++ [p]) true) (hqt : ¬ CanDec A Q x (α ++ [q]) false)
    (hβ : ∀ s ∈ β, s ∈ Q) (hγ : ∀ s ∈ γ, s ∈ Q) (hr : r ∈ Q)
    (hagr : AgreeOn {r} (A.exec x (α ++ [p] ++ β)) (A.exec x (α ++ [q] ++ γ))) : False := by
  obtain ⟨m, v, hout⟩ := exists_solo_out hwf x (α ++ [p] ++ β) r
  have hrep : ∀ s ∈ List.replicate (m + 1) r, s ∈ ({r} : Set P) := fun s hs => by
    rw [List.eq_of_mem_replicate hs]; rfl
  have h2 := Alg.run_agreeOn hagr hrep
  rw [← Alg.exec_append, ← Alg.exec_append] at h2
  have hout2 := (h2.out_iff (by rfl) v).1 hout
  have hd1 : CanDec A Q x (α ++ [p]) v := ⟨β ++ List.replicate (m + 1) r, fun s hs => by
      rcases List.mem_append.1 hs with hs | hs
      · exact hβ s hs
      · rw [List.eq_of_mem_replicate hs]; exact hr,
    r, by simp, by simpa [List.append_assoc] using hout⟩
  have hd2 : CanDec A Q x (α ++ [q]) v := ⟨γ ++ List.replicate (m + 1) r, fun s hs => by
      rcases List.mem_append.1 hs with hs | hs
      · exact hγ s hs
      · rw [List.eq_of_mem_replicate hs]; exact hr,
    r, by simp, by simpa [List.append_assoc] using hout2⟩
  cases v
  · exact hqt hd2
  · exact hpf hd1

end WaitFree

end Cslib.SharedMemory.Arrival
