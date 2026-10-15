import Papers.PODC2019.AnonymousMutex.Alg1

/-!
# Theorem 1: Algorithm 1 satisfies mutual exclusion

Aghazadeh, Imbs, Raynal, Taubenfeld, Woelfel, PODC 2019 (arXiv:1810.03723), Section 3.2.

**Theorem 1.** For `n` processes and `m > 1` registers with `m ∈ M(n)`, Algorithm 1 satisfies
mutual exclusion. We prove it under the weaker hypothesis `n ≤ m` (`theorem_1`), which follows
from `m > 1 ∧ m ∈ M(n)` (`theorem_1_of_M`).

## Proof

A process is in a *CS-state* if its program counter is `retLock` or `cs` (it has seen a snapshot in
which all `m` registers hold its identifier and has not started `unlock()` since). For a process
`p` in a CS-state, a process `q ≠ p` is *dangerous* if its next step is a write (line 6 or the
`⊥`-write of `shrink()`) into a physical register currently holding `p`'s identifier. The
invariant (`Good`) is:

* at most one process is in a CS-state;
* if `p` is in a CS-state, then
  `#{registers not holding p} + #{dangerous processes} ≤ n - 1`.

When `p` enters its CS-state, all registers hold `p` and there are at most `n - 1` other
processes. Afterwards, only a dangerous process can overwrite a register holding `p` (and it then
stops being dangerous), and a process never becomes dangerous: a write of line 6 is prepared from
a snapshot entry `⊥`, and a `⊥`-write of `shrink()` from a read of the process's own identifier.
Hence while `p` is in a CS-state, at most `n - 1 < m` registers do not hold `p`, so no other
process can see a snapshot full of its own identifier, and no second process enters a CS-state.

The invariant `RegInv` relates the client region (`regionOf`) of every process to its program
counter; in particular a process in the critical section is in a CS-state. Neither invariant needs
client well-formedness, so mutual exclusion even holds for all executions.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg1

variable {Id : Type} [DecidableEq Id] {m : ℕ}

/-! ### Local transitions -/

/-- CS-state: about to return from `lock()`, or in the critical section. -/
def CSst (s : St Id m) : Prop := s.pc = .retLock ∨ s.pc = .cs

/-- The local register that the next step of the process writes (if it is a write). -/
def target (s : St Id m) : Option (Fin m) :=
  match s.pc with
  | .write x => some x
  | .shWrite i _ => if h : i < m then some ⟨i, h⟩ else none
  | _ => none

lemma shrinkFrom_me (s : St Id m) (i : ℕ) (unl : Bool) : (shrinkFrom s i unl).me = s.me := by
  unfold shrinkFrom; split_ifs <;> rfl

lemma shrinkFrom_pc (s : St Id m) (i : ℕ) (unl : Bool) :
    (∃ j, j < m ∧ (shrinkFrom s i unl).pc = .shRead j unl) ∨
      (shrinkFrom s i unl).pc = if unl then .retUnlock else .snap := by
  unfold shrinkFrom
  by_cases h : nextOwn s.view s.me i < m
  · rw [ite_eq_left h]; exact Or.inl ⟨_, h, rfl⟩
  · rw [ite_eq_right h]; exact Or.inr rfl

lemma target_shrinkFrom (s : St Id m) (i : ℕ) (unl : Bool) : target (shrinkFrom s i unl) = none := by
  rcases shrinkFrom_pc s i unl with ⟨j, -, h⟩ | h <;> cases unl <;> simp [target, h]

lemma not_CSst_shrinkFrom (s : St Id m) (i : ℕ) (unl : Bool) : ¬ CSst (shrinkFrom s i unl) := by
  rcases shrinkFrom_pc s i unl with ⟨j, -, h⟩ | h <;> cases unl <;> simp [CSst, h]

lemma firstBot_some {w : Fin m → Option Id} {x : Fin m} (h : firstBot w = some x) : w x = none := by
  simpa using List.find?_some h

/-- The four possible outcomes of lines 4–11 after a snapshot. -/
lemma afterSnap_cases (s : St Id m) (w : Fin m → Option Id) :
    (∃ x, w x = none ∧ afterSnap s w = { s with view := w, pc := .write x }) ∨
      ((∀ x, w x = some s.me) ∧ afterSnap s w = { s with view := w, pc := .retLock }) ∨
      afterSnap s w = shrinkFrom { s with view := w } 0 false ∨
      afterSnap s w = { s with view := w, pc := .snap } := by
  unfold afterSnap
  by_cases h1 : 0 < owned w s.me ∨ ∀ x, w x = none
  · rw [ite_eq_left h1]
    cases hfb : firstBot w with
    | some x => exact Or.inl ⟨x, firstBot_some hfb, rfl⟩
    | none =>
      simp only
      by_cases h2 : owned w s.me = m
      · rw [ite_eq_left h2]
        refine Or.inr (Or.inl ⟨fun x => ?_, rfl⟩)
        have h3 : (Finset.univ.filter fun x => w x = some s.me).card = (Finset.univ : Finset (Fin m)).card := by
          rw [Finset.card_univ, Fintype.card_fin]; exact h2
        exact Finset.filter_card_eq h3 x (Finset.mem_univ x)
      · rw [ite_eq_right h2]
        by_cases h3 : owned w s.me * cnt w < m
        · rw [ite_eq_left h3]; exact Or.inr (Or.inr (Or.inl rfl))
        · rw [ite_eq_right h3]; exact Or.inr (Or.inr (Or.inr rfl))
  · rw [ite_eq_right h1]; exact Or.inr (Or.inr (Or.inr rfl))

lemma afterSnap_me (s : St Id m) (w : Fin m → Option Id) : (afterSnap s w).me = s.me := by
  rcases afterSnap_cases s w with ⟨x, -, h⟩ | ⟨-, h⟩ | h | h <;> rw [h]
  exact shrinkFrom_me _ _ _

/-- The register written after a snapshot was `⊥` in the snapshot. -/
lemma target_afterSnap {s : St Id m} {w : Fin m → Option Id} {x : Fin m}
    (h : target (afterSnap s w) = some x) : w x = none := by
  rcases afterSnap_cases s w with ⟨y, hy, h'⟩ | ⟨-, h'⟩ | h' | h' <;> rw [h'] at h
  · simp only [target, Option.some.injEq] at h; subst h; exact hy
  · simp [target] at h
  · simp [target_shrinkFrom] at h
  · simp [target] at h

/-- A process enters its CS-state only after a snapshot full of its own identifier. -/
lemma CSst_afterSnap {s : St Id m} {w : Fin m → Option Id} (h : CSst (afterSnap s w)) :
    ∀ x, w x = some s.me := by
  rcases afterSnap_cases s w with ⟨y, hy, h'⟩ | ⟨hw, h'⟩ | h' | h' <;> rw [h'] at h
  · simp [CSst] at h
  · exact hw
  · exact absurd h (not_CSst_shrinkFrom _ _ _)
  · simp [CSst] at h

/-! ### Program counters of the client regions -/

/-- Program counters inside `lock()`. -/
def TryPc : PC m → Prop
  | .snap => True
  | .write _ => True
  | .shRead i unl => unl = false ∧ i < m
  | .shWrite i unl => unl = false ∧ i < m
  | .retLock => True
  | _ => False

/-- Program counters inside `unlock()`. -/
def ExitPc : PC m → Prop
  | .shRead i unl => unl = true ∧ i < m
  | .shWrite i unl => unl = true ∧ i < m
  | .retUnlock => True
  | _ => False

/-- Program counters compatible with a client region. -/
def RegPc : Region → PC m → Prop
  | .rem, pc => pc = .rem
  | .trying, pc => TryPc pc
  | .cs, pc => pc = .cs
  | .exiting, pc => ExitPc pc

lemma regPc_shrinkFrom (s : St Id m) (i : ℕ) (unl : Bool) :
    RegPc (if unl then .exiting else .trying) (shrinkFrom s i unl).pc := by
  rcases shrinkFrom_pc s i unl with ⟨j, hj, h⟩ | h
  · cases unl <;> simp [RegPc, TryPc, ExitPc, h, hj]
  · cases unl <;> simp [RegPc, TryPc, ExitPc, h]

lemma tryPc_afterSnap (s : St Id m) (w : Fin m → Option Id) : TryPc (afterSnap s w).pc := by
  rcases afterSnap_cases s w with ⟨y, -, h⟩ | ⟨-, h⟩ | h | h <;> rw [h]
  · simp [TryPc]
  · simp [TryPc]
  · simpa [RegPc] using regPc_shrinkFrom { s with view := w } 0 false
  · simp [TryPc]

/-! ### Invocations and responses -/

lemma invoke_cases (s : St Id m) (o : MutexOp) :
    (s.pc = .rem ∧ o = .lock ∧ (alg1 Id m).invoke s o = { s with pc := .snap }) ∨
      (s.pc = .cs ∧ o = .unlock ∧ (alg1 Id m).invoke s o = shrinkFrom s 0 true) ∨
      (alg1 Id m).invoke s o = s := by
  simp only [alg1]
  cases hpc : s.pc <;> cases o <;> simp

lemma act_ret_cases {s : St Id m} {r : Unit} {l : St Id m} (h : (alg1 Id m).act s = .ret r l) :
    (s.pc = .retLock ∧ l = { s with pc := .cs }) ∨ (s.pc = .retUnlock ∧ l = { s with pc := .rem }) ∨
      (l = s ∧ (s.pc = .rem ∨ s.pc = .cs ∨ (∃ i unl, s.pc = .shRead i unl ∧ m ≤ i) ∨
        (∃ i unl, s.pc = .shWrite i unl ∧ m ≤ i))) := by
  simp only [alg1] at h
  cases hpc : s.pc with
  | rem => rw [hpc] at h; simp only [SymAction.ret.injEq] at h; simp [h.2]
  | cs => rw [hpc] at h; simp only [SymAction.ret.injEq] at h; simp [h.2]
  | snap => rw [hpc] at h; simp at h
  | write x => rw [hpc] at h; simp at h
  | retLock => rw [hpc] at h; simp only [SymAction.ret.injEq] at h; simp [h.2]
  | retUnlock => rw [hpc] at h; simp only [SymAction.ret.injEq] at h; simp [h.2]
  | shRead i unl =>
    rw [hpc] at h; dsimp only at h
    split_ifs at h with hi
    simp only [SymAction.ret.injEq] at h
    simp [h.2]; omega
  | shWrite i unl =>
    rw [hpc] at h; dsimp only at h
    split_ifs at h with hi
    simp only [SymAction.ret.injEq] at h
    simp [h.2]; omega


/-! ### Steps of the implementation -/

section Steps

variable {P : Type} [DecidableEq P] (ids : P → Id) (π : P → Equiv.Perm (Fin m))

/-- Configurations of Algorithm 1. -/
abbrev Cfg1 (Id : Type) [DecidableEq Id] (m : ℕ) (P : Type) :=
  Config mutexObj (fun _ : Unit => memObj m (Option Id) (alg1 Id m).bot) P (St Id m)

variable {ids π}

lemma impl_act_ret {p : P} {s : St Id m} {r : Unit} {l : St Id m}
    (h : ((alg1 Id m).impl ids π).act p s = .ret r l) : (alg1 Id m).act s = .ret r l := by
  simp only [SymAlg.impl] at h
  split at h
  · cases h
  · cases h
  · rename_i heq; cases h; exact heq

lemma not_tau_of_ret {C C' : Cfg1 Id m P} {p : P} {r : Unit} {l : St Id m}
    (hact : (alg1 Id m).act (C.loc p) = .ret r l)
    (h : ((alg1 Id m).impl ids π).step C (.tau p) = some C') : False := by
  obtain ⟨-, -, i, o, k, h1, -⟩ := Impl.step_tau h
  simp only [SymAlg.impl, hact] at h1
  cases h1

/-- The four kinds of internal steps of a process. -/
lemma tau_cases {C C' : Cfg1 Id m P} {p : P}
    (h : ((alg1 Id m).impl ids π).step C (.tau p) = some C') :
    (∀ q, q ≠ p → C'.loc q = C.loc q) ∧
    (((C.loc p).pc = .snap ∧ C'.mem () = C.mem () ∧
        C'.loc p = afterSnap (C.loc p) (fun x => C.mem () (π p x))) ∨
      (∃ x, (C.loc p).pc = .write x ∧
        C'.mem () = Function.update (C.mem ()) (π p x) (some (C.loc p).me) ∧
        C'.loc p = { C.loc p with pc := .snap }) ∨
      (∃ i unl, ∃ hi : i < m, (C.loc p).pc = .shRead i unl ∧ C'.mem () = C.mem () ∧
        C'.loc p = if C.mem () (π p ⟨i, hi⟩) = some (C.loc p).me
          then { C.loc p with pc := .shWrite i unl } else shrinkFrom (C.loc p) (i + 1) unl) ∨
      (∃ i unl, ∃ hi : i < m, (C.loc p).pc = .shWrite i unl ∧
        C'.mem () = Function.update (C.mem ()) (π p ⟨i, hi⟩) none ∧
        C'.loc p = shrinkFrom (C.loc p) (i + 1) unl)) := by
  refine ⟨fun q hq => (Impl.step_other h (Ne.symm hq)).1, ?_⟩
  have hp := (Impl.step_tau h).1
  cases hpc : (C.loc p).pc with
  | snap =>
    have hact : (alg1 Id m).act (C.loc p) = .snap (afterSnap (C.loc p)) := by
      simp only [alg1, hpc]
    rw [SymAlg.impl_step_tau_snap ids π hp hact] at h
    cases h
    exact Or.inl ⟨rfl, by simp, by simp⟩
  | write x =>
    have hact : (alg1 Id m).act (C.loc p) =
        .rmw x (fun _ => some (C.loc p).me) (fun _ => { C.loc p with pc := .snap }) := by
      simp only [alg1, hpc]
    rw [SymAlg.impl_step_tau_rmw ids π hp hact] at h
    cases h
    exact Or.inr (Or.inl ⟨x, rfl, by simp, by simp⟩)
  | shRead i unl =>
    by_cases hi : i < m
    · have hact : (alg1 Id m).act (C.loc p) = .rmw ⟨i, hi⟩ (fun v => v)
          (fun v => if v = some (C.loc p).me then { C.loc p with pc := .shWrite i unl }
            else shrinkFrom (C.loc p) (i + 1) unl) := by
        simp only [alg1, hpc, hi, ↓reduceDIte]
      rw [SymAlg.impl_step_tau_rmw ids π hp hact] at h
      cases h
      exact Or.inr (Or.inr (Or.inl ⟨i, unl, hi, rfl, by simp, by simp⟩))
    · have hact : (alg1 Id m).act (C.loc p) = .ret () (C.loc p) := by
        simp only [alg1, hpc, hi, ↓reduceDIte]
      exact (not_tau_of_ret hact h).elim
  | shWrite i unl =>
    by_cases hi : i < m
    · have hact : (alg1 Id m).act (C.loc p) = .rmw ⟨i, hi⟩ (fun _ => none)
          (fun _ => shrinkFrom (C.loc p) (i + 1) unl) := by
        simp only [alg1, hpc, hi, ↓reduceDIte]
      rw [SymAlg.impl_step_tau_rmw ids π hp hact] at h
      cases h
      exact Or.inr (Or.inr (Or.inr ⟨i, unl, hi, rfl, by simp, by simp⟩))
    · have hact : (alg1 Id m).act (C.loc p) = .ret () (C.loc p) := by
        simp only [alg1, hpc, hi, ↓reduceDIte]
      exact (not_tau_of_ret hact h).elim
  | rem =>
    exact (not_tau_of_ret (by simp only [alg1, hpc]; exact rfl) h).elim
  | cs =>
    exact (not_tau_of_ret (by simp only [alg1, hpc]; exact rfl) h).elim
  | retLock =>
    exact (not_tau_of_ret (by simp only [alg1, hpc]; exact rfl) h).elim
  | retUnlock =>
    exact (not_tau_of_ret (by simp only [alg1, hpc]; exact rfl) h).elim

lemma ret_cases {C C' : Cfg1 Id m P} {p : P} {r : Unit}
    (h : ((alg1 Id m).impl ids π).step C (.ret p r) = some C') :
    (∀ q, q ≠ p → C'.loc q = C.loc q) ∧ C'.mem () = C.mem () ∧
    (((C.loc p).pc = .retLock ∧ C'.loc p = { C.loc p with pc := .cs }) ∨
      ((C.loc p).pc = .retUnlock ∧ C'.loc p = { C.loc p with pc := .rem }) ∨
      (C'.loc p = C.loc p ∧ ((C.loc p).pc = .rem ∨ (C.loc p).pc = .cs ∨
        (∃ i unl, (C.loc p).pc = .shRead i unl ∧ m ≤ i) ∨
        (∃ i unl, (C.loc p).pc = .shWrite i unl ∧ m ≤ i)))) := by
  refine ⟨fun q hq => (Impl.step_other h (Ne.symm hq)).1, ?_⟩
  obtain ⟨-, -, hmem, l, hact, hloc⟩ := Impl.step_ret h
  refine ⟨by rw [hmem], ?_⟩
  have hl : C'.loc p = l := by rw [hloc]; simp
  rw [hl]
  exact act_ret_cases (impl_act_ret hact)

lemma inv_cases {C C' : Cfg1 Id m P} {p : P} {o : MutexOp}
    (h : ((alg1 Id m).impl ids π).step C (.inv p o) = some C') :
    (∀ q, q ≠ p → C'.loc q = C.loc q) ∧ C'.mem () = C.mem () ∧
    (((C.loc p).pc = .rem ∧ o = .lock ∧ C'.loc p = { C.loc p with pc := .snap }) ∨
      ((C.loc p).pc = .cs ∧ o = .unlock ∧ C'.loc p = shrinkFrom (C.loc p) 0 true) ∨
      C'.loc p = C.loc p) := by
  refine ⟨fun q hq => (Impl.step_other h (Ne.symm hq)).1, ?_⟩
  obtain ⟨-, -, -, hloc, hmem⟩ := Impl.step_inv h
  refine ⟨by rw [hmem], ?_⟩
  have hl : C'.loc p = (alg1 Id m).invoke (C.loc p) o := by rw [hloc]; simp [SymAlg.impl]
  rw [hl]
  exact invoke_cases (C.loc p) o

/-- No step changes the identifier stored in a local state. -/
lemma me_step {C C' : Cfg1 Id m P} {ℓ : Label P mutexObj}
    (h : ((alg1 Id m).impl ids π).step C ℓ = some C') (q : P) : (C'.loc q).me = (C.loc q).me := by
  by_cases hq : ℓ.proc = q
  · cases ℓ with
    | inv p o =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, h1 | h1 | h1⟩ := inv_cases h
      · rw [h1.2.2]
      · rw [h1.2.2, shrinkFrom_me]
      · rw [h1]
    | ret p r =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, h1 | h1 | h1⟩ := ret_cases h
      · rw [h1.2]
      · rw [h1.2]
      · rw [h1.1]
    | tau p =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, h1 | ⟨x, h1⟩ | ⟨i, unl, hi, h1⟩ | ⟨i, unl, hi, h1⟩⟩ := tau_cases h
      · rw [h1.2.2, afterSnap_me]
      · rw [h1.2.2]
      · rw [h1.2.2]; split_ifs
        · rfl
        · rw [shrinkFrom_me]
      · rw [h1.2.2, shrinkFrom_me]
  · rw [(Impl.step_other h hq).1]

/-- How a process enters its CS-state: by a snapshot in which all registers hold its
identifier. -/
lemma enter_CSst {C C' : Cfg1 Id m P} {ℓ : Label P mutexObj}
    (h : ((alg1 Id m).impl ids π).step C ℓ = some C') {p : P}
    (hp' : CSst (C'.loc p)) (hp : ¬ CSst (C.loc p)) :
    ℓ = .tau p ∧ C'.mem () = C.mem () ∧ ∀ x, C.mem () (π p x) = some (C.loc p).me := by
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv p o =>
      simp only [Label.proc] at hq; subst hq
      exfalso
      obtain ⟨-, -, h1 | h1 | h1⟩ := inv_cases h
      · rw [h1.2.2] at hp'; simp [CSst] at hp'
      · rw [h1.2.2] at hp'; exact not_CSst_shrinkFrom _ _ _ hp'
      · rw [h1] at hp'; exact hp hp'
    | ret p r =>
      simp only [Label.proc] at hq; subst hq
      exfalso
      obtain ⟨-, -, h1 | h1 | h1⟩ := ret_cases h
      · exact hp (Or.inl h1.1)
      · rw [h1.2] at hp'; simp [CSst] at hp'
      · rw [h1.1] at hp'; exact hp hp'
    | tau p =>
      simp only [Label.proc] at hq; subst hq
      refine ⟨rfl, ?_⟩
      obtain ⟨-, h1 | ⟨x, h1⟩ | ⟨i, unl, hi, h1⟩ | ⟨i, unl, hi, h1⟩⟩ := tau_cases h
      · rw [h1.2.2] at hp'; exact ⟨h1.2.1, CSst_afterSnap hp'⟩
      · rw [h1.2.2] at hp'; simp [CSst] at hp'
      · exfalso; rw [h1.2.2] at hp'; split_ifs at hp'
        · simp [CSst] at hp'
        · exact not_CSst_shrinkFrom _ _ _ hp'
      · exfalso; rw [h1.2.2] at hp'; exact not_CSst_shrinkFrom _ _ _ hp'
  · exact absurd (by rw [← (Impl.step_other h hq).1]; exact hp') hp

end Steps


/-! ### The safety invariant -/

section Invariant

variable {P : Type} [DecidableEq P] (ids : P → Id) (π : P → Equiv.Perm (Fin m))

/-- `q` is *dangerous* for `p`: its next step writes into a physical register holding `p`'s
identifier. -/
def Dang (C : Cfg1 Id m P) (p q : P) : Prop :=
  ∃ x, target (C.loc q) = some x ∧ C.mem () (π q x) = some (ids p)

open Classical in
/-- Physical registers not holding `p`'s identifier. -/
noncomputable def nonOwn (C : Cfg1 Id m P) (p : P) : Finset (Fin m) :=
  Finset.univ.filter fun y => C.mem () y ≠ some (ids p)

open Classical in
/-- Processes `q ≠ p` dangerous for `p`. -/
noncomputable def dangSet [Fintype P] (C : Cfg1 Id m P) (p : P) : Finset P :=
  Finset.univ.filter fun q => q ≠ p ∧ Dang ids π C p q

/-- The safety invariant. -/
structure Good [Fintype P] (C : Cfg1 Id m P) : Prop where
  me : ∀ p, (C.loc p).me = ids p
  excl : ∀ p q, CSst (C.loc p) → CSst (C.loc q) → p = q
  count : ∀ p, CSst (C.loc p) →
    (nonOwn ids C p).card + (dangSet ids π C p).card ≤ Fintype.card P - 1

variable {ids π}

lemma mem_nonOwn {C : Cfg1 Id m P} {p : P} {y : Fin m} :
    y ∈ nonOwn ids C p ↔ C.mem () y ≠ some (ids p) := by
  simp [nonOwn]

lemma mem_dangSet [Fintype P] {C : Cfg1 Id m P} {p q : P} :
    q ∈ dangSet ids π C p ↔ q ≠ p ∧ Dang ids π C p q := by
  simp [dangSet]

lemma nonOwn_congr {C C' : Cfg1 Id m P} {p : P} (hmem : C'.mem () = C.mem ()) :
    nonOwn ids C' p = nonOwn ids C p := by
  ext y; simp only [mem_nonOwn, hmem]

lemma dangSet_mono [Fintype P] {C C' : Cfg1 Id m P} {p : P}
    (hD : ∀ q, q ≠ p → Dang ids π C' p q → Dang ids π C p q) :
    dangSet ids π C' p ⊆ dangSet ids π C p := by
  intro q hq
  rw [mem_dangSet] at hq ⊢
  exact ⟨hq.1, hD q hq.1 hq.2⟩

/-- Count for a step that does not change the memory. -/
lemma count_le_of_mem_eq [Fintype P] {C C' : Cfg1 Id m P} {p : P}
    (hmem : C'.mem () = C.mem ()) (hD : ∀ q, q ≠ p → Dang ids π C' p q → Dang ids π C p q) :
    (nonOwn ids C' p).card + (dangSet ids π C' p).card ≤
      (nonOwn ids C p).card + (dangSet ids π C p).card := by
  rw [nonOwn_congr hmem]
  have := Finset.card_le_card (dangSet_mono hD)
  omega

/-- Count for a write of a value other than `p`'s identifier by a process `q ≠ p` into the
register it targets. -/
lemma count_le_of_write [Fintype P] {C C' : Cfg1 Id m P} {p q : P} {r : Fin m}
    {v : Option Id} (hqp : q ≠ p) (hmem : C'.mem () = Function.update (C.mem ()) r v)
    (hv : v ≠ some (ids p)) (hloc : ∀ q', q' ≠ q → C'.loc q' = C.loc q')
    (ht : ∃ x, target (C.loc q) = some x ∧ π q x = r) (ht' : target (C'.loc q) = none) :
    (nonOwn ids C' p).card + (dangSet ids π C' p).card ≤
      (nonOwn ids C p).card + (dangSet ids π C p).card := by
  classical
  have hD : ∀ q', q' ≠ p → Dang ids π C' p q' → Dang ids π C p q' ∧ q' ≠ q := by
    rintro q' - ⟨x, hx, hm⟩
    by_cases hq' : q' = q
    · subst hq'; rw [ht'] at hx; cases hx
    · rw [hloc q' hq'] at hx
      refine ⟨⟨x, hx, ?_⟩, hq'⟩
      by_cases hr : π q' x = r
      · rw [hmem, hr, Function.update_self] at hm; exact absurd hm hv
      · rw [hmem, Function.update_of_ne hr] at hm; exact hm
  by_cases hr : C.mem () r = some (ids p)
  · have hq : q ∈ dangSet ids π C p := by
      obtain ⟨x, hx, hxr⟩ := ht
      rw [mem_dangSet]
      exact ⟨hqp, x, hx, by rw [hxr]; exact hr⟩
    have h1 : dangSet ids π C' p ⊆ (dangSet ids π C p).erase q := by
      intro q' hq'
      rw [mem_dangSet] at hq'
      obtain ⟨h1, h2⟩ := hD q' hq'.1 hq'.2
      rw [Finset.mem_erase, mem_dangSet]
      exact ⟨h2, hq'.1, h1⟩
    have h2 : nonOwn ids C' p ⊆ insert r (nonOwn ids C p) := by
      intro y hy
      rw [mem_nonOwn] at hy
      rw [Finset.mem_insert, mem_nonOwn]
      by_cases hyr : y = r
      · exact Or.inl hyr
      · rw [hmem, Function.update_of_ne hyr] at hy; exact Or.inr hy
    have e1 := Finset.card_le_card h1
    have e2 := Finset.card_le_card h2
    have e3 := Finset.card_erase_of_mem hq
    have e4 := Finset.card_insert_le r (nonOwn ids C p)
    have e5 := Finset.card_pos.mpr ⟨q, hq⟩
    omega
  · have h1 : dangSet ids π C' p ⊆ dangSet ids π C p :=
      dangSet_mono fun q' hq' hd => (hD q' hq' hd).1
    have h2 : nonOwn ids C' p ⊆ nonOwn ids C p := by
      intro y hy
      rw [mem_nonOwn] at hy ⊢
      by_cases hyr : y = r
      · subst hyr; exact hr
      · rw [hmem, Function.update_of_ne hyr] at hy; exact hy
    have e1 := Finset.card_le_card h1
    have e2 := Finset.card_le_card h2
    omega

/-- The count of a process in its CS-state does not increase. -/
lemma count_step [Fintype P] (hid : Function.Injective ids) {C C' : Cfg1 Id m P}
    {ℓ : Label P mutexObj} (hC : Good ids π C)
    (h : ((alg1 Id m).impl ids π).step C ℓ = some C') {p : P} (hp : CSst (C.loc p)) :
    (nonOwn ids C' p).card + (dangSet ids π C' p).card ≤
      (nonOwn ids C p).card + (dangSet ids π C p).card := by
  -- steps that do not change the memory nor the local states of processes `≠ q`, and after which
  -- `q` is not dangerous unless it was
  have key : ∀ q, (∀ q', q' ≠ q → C'.loc q' = C.loc q') → C'.mem () = C.mem () →
      (q ≠ p → Dang ids π C' p q → Dang ids π C p q) →
      (nonOwn ids C' p).card + (dangSet ids π C' p).card ≤
        (nonOwn ids C p).card + (dangSet ids π C p).card := by
    intro q hloc hmem hq
    refine count_le_of_mem_eq hmem fun q' hq'p hd => ?_
    by_cases hq' : q' = q
    · subst hq'; exact hq hq'p hd
    · obtain ⟨x, hx, hm⟩ := hd
      rw [hloc q' hq'] at hx; rw [hmem] at hm
      exact ⟨x, hx, hm⟩
  -- a process with no target is not dangerous
  have nd : ∀ q, target (C'.loc q) = none → ¬ Dang ids π C' p q := by
    rintro q ht ⟨x, hx, -⟩; rw [ht] at hx; cases hx
  cases ℓ with
  | inv q o =>
    obtain ⟨hloc, hmem, h1⟩ := inv_cases h
    refine key q hloc hmem fun _ hd => ?_
    rcases h1 with h1 | h1 | h1
    · exact absurd hd (nd q (by rw [h1.2.2]; rfl))
    · exact absurd hd (nd q (by rw [h1.2.2, target_shrinkFrom]))
    · obtain ⟨x, hx, hm⟩ := hd; rw [h1] at hx; rw [hmem] at hm; exact ⟨x, hx, hm⟩
  | ret q r =>
    obtain ⟨hloc, hmem, h1⟩ := ret_cases h
    refine key q hloc hmem fun _ hd => ?_
    rcases h1 with h1 | h1 | h1
    · exact absurd hd (nd q (by rw [h1.2]; rfl))
    · exact absurd hd (nd q (by rw [h1.2]; rfl))
    · obtain ⟨x, hx, hm⟩ := hd; rw [h1.1] at hx; rw [hmem] at hm; exact ⟨x, hx, hm⟩
  | tau q =>
    obtain ⟨hloc, h1 | ⟨x, h1⟩ | ⟨i, unl, hi, h1⟩ | ⟨i, unl, hi, h1⟩⟩ := tau_cases h
    · -- snapshot: a write is only prepared for a register that was `⊥`
      refine key q hloc h1.2.1 fun _ hd => ?_
      obtain ⟨x, hx, hm⟩ := hd
      rw [h1.2.2] at hx
      have := target_afterSnap hx
      rw [h1.2.1, this] at hm; cases hm
    · -- write of line 6
      have hqp : q ≠ p := by rintro rfl; rcases hp with hp | hp <;> rw [hp] at h1 <;> cases h1.1
      refine count_le_of_write hqp h1.2.1 ?_ hloc ⟨x, by simp [target, h1.1], rfl⟩
        (by rw [h1.2.2]; rfl)
      rw [hC.me q]; simp only [ne_eq, Option.some.injEq]; exact fun e => hqp (hid e)
    · -- read of `shrink()`: a `⊥`-write is only prepared after reading the own identifier
      refine key q hloc h1.2.1 fun hqp hd => ?_
      obtain ⟨x, hx, hm⟩ := hd
      rw [h1.2.2] at hx
      split_ifs at hx with hv
      · simp only [target, hi, ↓reduceDIte, Option.some.injEq] at hx
        subst hx
        rw [h1.2.1, hv, hC.me q] at hm
        exact absurd (hid (Option.some.inj hm)) hqp
      · rw [target_shrinkFrom] at hx; cases hx
    · -- `⊥`-write of `shrink()`
      have hqp : q ≠ p := by rintro rfl; rcases hp with hp | hp <;> rw [hp] at h1 <;> cases h1.1
      refine count_le_of_write hqp h1.2.1 (by simp) hloc
        ⟨⟨i, hi⟩, by simp [target, h1.1, hi], rfl⟩ (by rw [h1.2.2, target_shrinkFrom])

/-- If `p` is in its CS-state, not all registers hold the same other identifier. -/
lemma not_all_other [Fintype P] (hm : Fintype.card P ≤ m) {C : Cfg1 Id m P} (hC : Good ids π C)
    {p : P} (hp : CSst (C.loc p)) {a : Id} (ha : a ≠ ids p) (hall : ∀ y, C.mem () y = some a) :
    False := by
  have h1 : nonOwn ids C p = Finset.univ := by
    ext y; simp only [mem_nonOwn, Finset.mem_univ, iff_true, hall y, ne_eq, Option.some.injEq]
    exact ha
  have h2 := hC.count p hp
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  have : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨p⟩
  omega

lemma all_of_enter {C : Cfg1 Id m P} {p : P} (hme : (C.loc p).me = ids p)
    (h : ∀ x, C.mem () (π p x) = some (C.loc p).me) : ∀ y, C.mem () y = some (ids p) := by
  intro y
  have := h ((π p).symm y)
  rwa [Equiv.apply_symm_apply, hme] at this

lemma good_init [Fintype P] : Good ids π (((alg1 Id m).impl ids π).initCfg) where
  me _ := rfl
  excl p _ hp := by simp [Impl.initCfg, SymAlg.impl, alg1, CSst] at hp
  count p hp := by simp [Impl.initCfg, SymAlg.impl, alg1, CSst] at hp

lemma good_step [Fintype P] (hid : Function.Injective ids) (hm : Fintype.card P ≤ m)
    {C C' : Cfg1 Id m P} {ℓ : Label P mutexObj} (hC : Good ids π C)
    (h : ((alg1 Id m).impl ids π).step C ℓ = some C') : Good ids π C' := by
  have hme : ∀ p, (C'.loc p).me = ids p := fun p => by rw [me_step h, hC.me]
  refine ⟨hme, ?_, ?_⟩
  · intro p q hp' hq'
    by_cases hp : CSst (C.loc p) <;> by_cases hq : CSst (C.loc q)
    · exact hC.excl p q hp hq
    · obtain ⟨-, hmem, hall⟩ := enter_CSst h hq' hq
      have hpq : p ≠ q := by rintro rfl; exact hq hp
      exact (not_all_other hm hC hp (fun e => hpq (hid e).symm)
        (all_of_enter (hC.me q) hall)).elim
    · obtain ⟨-, hmem, hall⟩ := enter_CSst h hp' hp
      have hpq : p ≠ q := by rintro rfl; exact hp hq
      exact (not_all_other hm hC hq (fun e => hpq (hid e))
        (all_of_enter (hC.me p) hall)).elim
    · obtain ⟨h1, -, -⟩ := enter_CSst h hp' hp
      obtain ⟨h2, -, -⟩ := enter_CSst h hq' hq
      rw [h1] at h2; cases h2; rfl
  · intro p hp'
    by_cases hp : CSst (C.loc p)
    · exact le_trans (count_step hid hC h hp) (hC.count p hp)
    · obtain ⟨-, hmem, hall⟩ := enter_CSst h hp' hp
      have hall' := all_of_enter (hC.me p) hall
      have h1 : nonOwn ids C' p = ∅ := by
        ext y; simp [mem_nonOwn, hmem, hall' y]
      have h2 : dangSet ids π C' p ⊆ Finset.univ.erase p := by
        intro q hq; rw [mem_dangSet] at hq; simp [hq.1]
      have h3 := Finset.card_le_card h2
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ] at h3
      rw [h1, Finset.card_empty]
      omega

end Invariant


/-! ### Regions and program counters -/

section Regions

variable {P : Type} [DecidableEq P] {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

/-- The program counter of every process is compatible with its client region. -/
def RegInv (α : List (Label P mutexObj)) (C : Cfg1 Id m P) : Prop :=
  ∀ p r, regionOf α p = some r → RegPc r (C.loc p).pc

lemma regInv_init : RegInv [] (((alg1 Id m).impl ids π).initCfg) := by
  intro p r hr
  simp only [regionOf_nil, Option.some.injEq] at hr
  subst hr
  rfl

lemma regPc_sh {r : Region} {i : ℕ} {unl : Bool}
    (h : RegPc r (.shRead i unl : PC m) ∨ RegPc r (.shWrite i unl : PC m)) :
    r = (if unl then .exiting else .trying) ∧ i < m := by
  cases r <;> cases unl <;> simp_all [RegPc, TryPc, ExitPc]

lemma regPc_shWrite {i : ℕ} (unl : Bool) (hi : i < m) :
    RegPc (if unl then .exiting else .trying) (.shWrite i unl : PC m) := by
  cases unl <;> simp [RegPc, TryPc, ExitPc, hi]

lemma regInv_step {α : List (Label P mutexObj)} {C C' : Cfg1 Id m P} {ℓ : Label P mutexObj}
    (hinv : RegInv α C) (h : ((alg1 Id m).impl ids π).step C ℓ = some C') :
    RegInv (α ++ [ℓ]) C' := by
  intro p r hr
  by_cases hq : ℓ.proc = p
  · rw [regionOf_append_singleton, ite_eq_left hq] at hr
    obtain ⟨r0, hr0, hnext⟩ := Option.bind_eq_some_iff.mp hr
    have hpc := hinv p r0 hr0
    cases ℓ with
    | inv p' o =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv h
      have hl : C'.loc p' = (alg1 Id m).invoke (C.loc p') o := by rw [hloc]; simp [SymAlg.impl]
      rw [hl]
      cases r0 <;> cases o <;> simp only [Region.next, reduceCtorEq] at hnext <;>
        simp only [Option.some.injEq] at hnext <;> subst hnext
      · simp only [RegPc] at hpc
        simp [alg1, hpc, RegPc, TryPc]
      · simp only [RegPc] at hpc
        simp only [alg1, hpc]
        simpa using regPc_shrinkFrom (C.loc p') 0 true
    | tau p' =>
      simp only [Label.proc] at hq; subst hq
      simp only [Region.next, Option.some.injEq] at hnext; subst hnext
      obtain ⟨-, h1 | ⟨x, h1⟩ | ⟨i, unl, hi, h1⟩ | ⟨i, unl, hi, h1⟩⟩ := tau_cases h
      · rw [h1.1] at hpc; rw [h1.2.2]
        cases r0 <;> simp [RegPc, TryPc, ExitPc] at hpc ⊢
        exact tryPc_afterSnap _ _
      · rw [h1.1] at hpc; rw [h1.2.2]
        cases r0 <;> simp [RegPc, TryPc, ExitPc] at hpc ⊢
      · rw [h1.1] at hpc; rw [h1.2.2]
        obtain ⟨rfl, -⟩ := regPc_sh (Or.inl hpc)
        by_cases hv : C.mem () (π p' ⟨i, hi⟩) = some (C.loc p').me
        · rw [ite_eq_left hv]; exact regPc_shWrite unl hi
        · rw [ite_eq_right hv]; exact regPc_shrinkFrom _ _ _
      · rw [h1.1] at hpc; rw [h1.2.2]
        obtain ⟨rfl, -⟩ := regPc_sh (Or.inr hpc)
        exact regPc_shrinkFrom _ _ _
    | ret p' r' =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, h1 | h1 | h1⟩ := ret_cases h
      · rw [h1.2]
        rw [h1.1] at hpc
        cases r0 <;> simp [RegPc, TryPc, ExitPc, Region.next] at hpc hnext ⊢
        subst hnext; rfl
      · rw [h1.2]
        rw [h1.1] at hpc
        cases r0 <;> simp [RegPc, TryPc, ExitPc, Region.next] at hpc hnext ⊢
        subst hnext; rfl
      · exfalso
        obtain ⟨-, h2 | h2 | ⟨i, unl, h2, hi⟩ | ⟨i, unl, h2, hi⟩⟩ := h1 <;> rw [h2] at hpc
        · cases r0 <;> simp [RegPc, TryPc, ExitPc, Region.next] at hpc hnext
        · cases r0 <;> simp [RegPc, TryPc, ExitPc, Region.next] at hpc hnext
        · have := (regPc_sh (Or.inl hpc)).2; omega
        · have := (regPc_sh (Or.inr hpc)).2; omega
  · rw [regionOf_append_singleton_of_ne _ _ hq] at hr
    rw [(Impl.step_other h hq).1]
    exact hinv p r hr

end Regions

/-! ### Theorem 1 -/

section Main

variable {P : Type} [Fintype P] [DecidableEq P] {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

lemma reach_inv (hid : Function.Injective ids) (hm : Fintype.card P ≤ m)
    (α : List (Label P mutexObj)) :
    ∀ C, ((alg1 Id m).impl ids π).run α = some C → Good ids π C ∧ RegInv α C := by
  induction α using List.reverseRecOn with
  | nil =>
    intro C h
    simp only [Impl.run_nil, Option.some.injEq] at h
    subst h
    exact ⟨good_init, regInv_init⟩
  | append_singleton α ℓ ih =>
    intro C' h
    have e : ((alg1 Id m).impl ids π).run (α ++ [ℓ]) =
        (((alg1 Id m).impl ids π).run α).bind
          (fun C => ((alg1 Id m).impl ids π).runFrom C [ℓ]) :=
      Impl.runFrom_append _ _ _ _
    cases hα : ((alg1 Id m).impl ids π).run α with
    | none => rw [e, hα] at h; cases h
    | some C =>
      rw [e, hα, Option.bind_some, Impl.runFrom_singleton] at h
      obtain ⟨hg, hr⟩ := ih C hα
      exact ⟨good_step hid hm hg h, regInv_step hr h⟩

/-- **Theorem 1** of Aghazadeh–Imbs–Raynal–Taubenfeld–Woelfel (PODC 2019): Algorithm 1 satisfies
mutual exclusion. Stated under the hypothesis `n ≤ m` (number of processes at most the number
of registers), which is implied by the paper's hypothesis `m > 1 ∧ m ∈ M(n)` (see
`theorem_1_of_M`). Processes have pairwise distinct identifiers and arbitrary anonymity
permutations. -/
theorem theorem_1 (ids : P → Id) (hid : Function.Injective ids) (π : P → Equiv.Perm (Fin m))
    (hm : Fintype.card P ≤ m) : ((alg1 Id m).impl ids π).MutualExclusion := by
  rintro α ⟨C, hC⟩ - p q hp hq
  obtain ⟨hg, hr⟩ := reach_inv hid hm α C hC
  have hp' : (C.loc p).pc = .cs := hr p .cs hp
  have hq' : (C.loc q).pc = .cs := hr q .cs hq
  exact hg.excl p q (Or.inr hp') (Or.inr hq')

/-- `m > 1` and `m ∈ M(n)` imply `n ≤ m` (otherwise `ℓ = m` violates `gcd(ℓ, m) = 1`). -/
lemma le_of_mem_M {n : ℕ} (h1 : 1 < m) (hM : m ∈ M n) : n ≤ m := by
  by_contra h
  have := (Nat.coprime_self m).mp (hM m h1 (by omega))
  omega

/-- **Theorem 1** of Aghazadeh–Imbs–Raynal–Taubenfeld–Woelfel (PODC 2019), with the paper's
hypotheses: for `n` processes and `m > 1` registers with `m ∈ M(n)`, Algorithm 1 satisfies
mutual exclusion. -/
theorem theorem_1_of_M (ids : P → Id) (hid : Function.Injective ids)
    (π : P → Equiv.Perm (Fin m)) (h1 : 1 < m) (hM : m ∈ M (Fintype.card P)) :
    ((alg1 Id m).impl ids π).MutualExclusion :=
  theorem_1 ids hid π (le_of_mem_M h1 hM)

end Main

end AnonymousMutex.Alg1
