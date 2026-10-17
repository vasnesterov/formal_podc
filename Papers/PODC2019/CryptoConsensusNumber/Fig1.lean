import Papers.PODC2019.CryptoConsensusNumber.Fig1Defs
import Cslib.Computability.Distributed.SharedMemory.History
import Podc.Computability.Distributed.SharedMemory.History
import Podc.Computability.Distributed.SharedMemory.Model

/-!
# Theorem 1: Figure 1 is a wait-free linearizable implementation of asset transfer

Guerraoui et al., *The Consensus Number of a Cryptocurrency*, PODC 2019, Theorem 1 (the part
"asset transfer with single-owner accounts has a wait-free implementation from an atomic
snapshot"; atomic snapshots are wait-free implementable from registers by Afek et al., which we do
not formalize).

We prove it for the **fixed** Figure 1 (`impl`: `ops_p` is a sequence); the literal Figure 1 (a
set) is not linearizable (`Fig1Bug.lean`).

## Proof

Linearization points as in the paper: a read and a failed transfer at their snapshot, a
successful transfer at its update. The invariant `Inv α C L` (for an execution `α` reaching `C`,
with linearization `L` built so far) says:

* `bal`: `linState L c + outflow(c, S) = q₀ c + inflow(c, S)` for every account `c` (so the
  abstract balance is `balance(c, S)` and no truncation happens);
* `own`: every transfer stored in component `q` of `S` is from an account owned by `q`;
* `ops`: the local copy `ops_q` equals `S q`;
* `upd`: a process between its successful check and its update of a transfer `(a, b, x)` owns `a`
  and `x ≤ balance(a, S)` for the *current* `S` — the outgoing amount of `a` can only be changed by
  its unique owner, the incoming amount only grows;
* bookkeeping: pending operations not yet linearized are not in `L`; finished but not yet
  returned operations are in `L` with the response the specification gives at their position.
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig1

open Cslib.SharedMemory

-- The specifications are plain definitions in `Defs.lean`; unfolding them reducibly here lets
-- `rw`/`simp` see `(atSpec …).State = (Acct → ℕ)` and `(snapObj …).State = (P → List _)`.
set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj

variable {P Acct : Type} [Fintype P] [DecidableEq P] [DecidableEq Acct]
  {μ : Acct → Finset P} {q₀ : Acct → ℕ}

/-- The high-level operation a process is executing, according to its program counter (for the
program counters before the linearization point). -/
def PC.op (μ : Acct → Finset P) (q₀ : Acct → ℕ) (p : P) : PC Acct → Option (atSpec P Acct μ q₀).Op
  | .scanT a b x => some (ATOp.transfer p a b x)
  | .upd a b x => some (ATOp.transfer p a b x)
  | .scanR a => some (ATOp.read a)
  | _ => none

/-- The invariant (see the module docstring). -/
structure Inv (α : List (Label P (atSpec P Acct μ q₀))) (C : Cfg μ q₀)
    (L : List (OpId P × (atSpec P Acct μ q₀).Op)) : Prop where
  lin : IsLinearization α L
  bal : ∀ c, linState L c + outflow c (C.mem ()) = q₀ c + inflow c (C.mem ())
  own : ∀ q t, t ∈ C.mem () q → q ∈ μ t.1
  ops : ∀ q, (C.loc q).ops = C.mem () q
  idle : ∀ q, (C.loc q).pc = .idle → C.pend q = none
  active : ∀ q o, PC.op μ q₀ q (C.loc q).pc = some o →
    C.pend q = some o ∧ curOp α q ∉ L.map Prod.fst ∧ opOf α (curOp α q) = some o
  upd : ∀ q a b x, (C.loc q).pc = .upd a b x →
    q ∈ μ a ∧ x + outflow a (C.mem ()) ≤ q₀ a + inflow a (C.mem ())
  done : ∀ q r, (C.loc q).pc = .done r → ∃ L₁ L₂ o,
    L = L₁ ++ (curOp α q, o) :: L₂ ∧ ((atSpec P Acct μ q₀).δ (linState L₁) o).2 = r

section Aux

variable {A : ObjSpec}

-- CSLib candidate
lemma not_mem_append_single {L : List (OpId P × A.Op)} {x y : OpId P} {o : A.Op}
    (hx : x ∉ L.map Prod.fst) (hxy : x.1 ≠ y.1) : x ∉ (L ++ [(y, o)]).map Prod.fst := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton,
    not_or]
  exact ⟨hx, fun h => hxy (by rw [h])⟩

end Aux

/-- The balance computed from the snapshot is the abstract balance. -/
lemma balance_eq {L : List (OpId P × (atSpec P Acct μ q₀).Op)} {S : P → List (Tr Acct)}
    (h : ∀ c, linState L c + outflow c S = q₀ c + inflow c S) (c : Acct) :
    balance q₀ c S = linState L c := by
  have := h c; simp only [balance]; omega

variable (hμ : ∀ a, (μ a).card ≤ 1)
include hμ

omit [Fintype P] [DecidableEq P] [DecidableEq Acct] in
lemma owner_unique {a : Acct} {p q : P} (hp : p ∈ μ a) (hq : q ∈ μ a) : p = q :=
  Finset.card_le_one.1 (hμ a) p hp q hq

omit hμ in
/-- Invocation steps preserve the invariant. -/
lemma Inv.step_inv {α : List (Label P (atSpec P Acct μ q₀))} {C C' : Cfg μ q₀} {L}
    (hI : Inv α C L) (hcnt : ∀ q, C.pend q = none → (opsOf α q).length = (respsOf α q).length)
    {p : P} {o : (atSpec P Acct μ q₀).Op} (h : (impl μ q₀).step C (.inv p o) = some C') :
    Inv (α ++ [.inv p o]) C' L := by
  obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv h
  have hlen := hcnt p h0
  -- the new local state of `p`
  have hnew : ∃ pc, C'.loc p = ⟨(C.loc p).ops, pc⟩ ∧ pc ≠ .idle ∧ PC.op μ q₀ p pc = some o ∧
      (∀ a b x, pc ≠ .upd a b x) ∧ ∀ r, pc ≠ .done r := by
    rw [hloc, Function.update_self]
    cases o with
    | transfer p' a b x =>
      have : p' = p := hal
      subst this
      exact ⟨.scanT a b x, rfl, by simp, rfl, by simp, by simp⟩
    | read a => exact ⟨.scanR a, rfl, by simp, rfl, by simp, by simp⟩
  obtain ⟨pc, hpc, hpc1, hpc2, hpc3, hpc4⟩ := hnew
  have hother : ∀ q, q ≠ p → C'.loc q = C.loc q ∧ C'.pend q = C.pend q := fun q hq => by
    rw [hloc, hpend, Function.update_of_ne hq, Function.update_of_ne hq]; exact ⟨rfl, rfl⟩
  refine ⟨hI.lin.append_inv p o, by rw [hmem]; exact hI.bal, by rw [hmem]; exact hI.own, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hpc, hmem]; exact hI.ops q
    · rw [(hother q hq).1, hmem]; exact hI.ops q
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hpc] at hq'; exact absurd hq' hpc1
    · rw [(hother q hq).1] at hq'; rw [(hother q hq).2]; exact hI.idle q hq'
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq
      rw [hpc] at hq'
      simp only [hpc2, Option.some.injEq] at hq'
      subst hq'
      refine ⟨by rw [hpend, Function.update_self], ?_, ?_⟩
      · intro hm
        have := hI.lin.mem_invoked (by simpa using hm)
        simp [Invoked] at this; omega
      · simp [opOf, opsOf_append, ← hlen, Label.invOf, Label.retOf]
    · rw [(hother q hq).1] at hq'
      obtain ⟨h1, h2, h3⟩ := hI.active q o' hq'
      exact ⟨by rw [(hother q hq).2]; exact h1, by simpa using h2,
        by simpa using opOf_append_of_eq_some h3 _⟩
  · intro q a b x hq'
    by_cases hq : q = p
    · subst hq; rw [hpc] at hq'; exact absurd hq' (hpc3 a b x)
    · rw [(hother q hq).1] at hq'; rw [hmem]; exact hI.upd q a b x hq'
  · intro q r hq'
    by_cases hq : q = p
    · subst hq; rw [hpc] at hq'; exact absurd hq' (hpc4 r)
    · rw [(hother q hq).1] at hq'; simpa using hI.done q r hq'

omit hμ in
/-- Response steps preserve the invariant. -/
lemma Inv.step_ret {α : List (Label P (atSpec P Acct μ q₀))} {C C' : Cfg μ q₀} {L}
    (hI : Inv α C L) {p : P} {r : (atSpec P Acct μ q₀).Resp}
    (h : (impl μ q₀).step C (.ret p r) = some C') : Inv (α ++ [.ret p r]) C' L := by
  obtain ⟨h0, hpc, rfl⟩ := step_ret_eq h (hI.idle p)
  obtain ⟨L₁, L₂, o, hs, hr⟩ := hI.done p r hpc
  refine ⟨hI.lin.append_ret L₁ L₂ o hs hr, hI.bal, hI.own, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]; exact hI.ops q
    · simp only [Function.update_of_ne hq]; exact hI.ops q
  · intro q hq'
    by_cases hq : q = p
    · subst hq; simp
    · simp only [Function.update_of_ne hq] at hq' ⊢; exact hI.idle q hq'
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; simp [PC.op] at hq'
    · simp only [Function.update_of_ne hq] at hq' ⊢
      obtain ⟨h1, h2, h3⟩ := hI.active q o' hq'
      rw [curOp_append_ret_of_ne α r (Ne.symm hq)]
      exact ⟨h1, h2, opOf_append_of_eq_some h3 _⟩
  · intro q a b x hq'
    by_cases hq : q = p
    · subst hq; simp at hq'
    · simp only [Function.update_of_ne hq] at hq'; exact hI.upd q a b x hq'
  · intro q r' hq'
    by_cases hq : q = p
    · subst hq; simp at hq'
    · simp only [Function.update_of_ne hq] at hq'
      rw [curOp_append_ret_of_ne α r (Ne.symm hq)]; exact hI.done q r' hq'

omit hμ in
/-- A linearization point: `p` executes the step that linearizes its pending operation `o` and
moves to `done` with the response the specification gives. -/
lemma Inv.push_done {α : List (Label P (atSpec P Acct μ q₀))} {C C' : Cfg μ q₀} {L}
    (hI : Inv α C L) {p : P} {o : (atSpec P Acct μ q₀).Op}
    (hact : PC.op μ q₀ p (C.loc p).pc = some o) (hpend : C'.pend = C.pend)
    (hother : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (hp : C'.loc p = ⟨C'.mem () p, .done ((atSpec P Acct μ q₀).δ (linState L) o).2⟩)
    (hbal : ∀ c, ((atSpec P Acct μ q₀).δ (linState L) o).1 c + outflow c (C'.mem ()) =
      q₀ c + inflow c (C'.mem ()))
    (hown : ∀ q t, t ∈ C'.mem () q → q ∈ μ t.1)
    (hops : ∀ q, q ≠ p → C'.mem () q = C.mem () q)
    (hupd : ∀ q a b x, q ≠ p → (C.loc q).pc = .upd a b x →
      x + outflow a (C'.mem ()) ≤ q₀ a + inflow a (C'.mem ())) :
    Inv (α ++ [.tau p]) C' (L ++ [(curOp α p, o)]) := by
  obtain ⟨hp1, hp2, hp3⟩ := hI.active p o hact
  have hnc : ¬ Completed α (curOp α p) := by simp [Completed]
  refine ⟨(hI.lin.push hp3 hp2 hnc).append_tau p, fun c => by rw [linState_concat]; exact hbal c,
    hown, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hp]
    · rw [hother q hq, hops q hq]; exact hI.ops q
  · intro q hq'
    by_cases hq : q = p
    · subst hq; rw [hp] at hq'; cases hq'
    · rw [hother q hq] at hq'; rw [hpend]; exact hI.idle q hq'
  · intro q o' hq'
    by_cases hq : q = p
    · subst hq; rw [hp] at hq'; simp [PC.op] at hq'
    · rw [hother q hq] at hq'
      obtain ⟨h1, h2, h3⟩ := hI.active q o' hq'
      rw [curOp_append_tau, hpend]
      exact ⟨h1, not_mem_append_single h2 hq, opOf_append_of_eq_some h3 _⟩
  · intro q a b x hq'
    by_cases hq : q = p
    · subst hq; rw [hp] at hq'; cases hq'
    · rw [hother q hq] at hq'
      exact ⟨(hI.upd q a b x hq').1, hupd q a b x hq hq'⟩
  · intro q r' hq'
    by_cases hq : q = p
    · subst hq; rw [hp] at hq'; cases hq'
      exact ⟨L, [], o, by simp, rfl⟩
    · rw [hother q hq] at hq'
      obtain ⟨L₁, L₂, o', hs, hr⟩ := hI.done q r' hq'
      exact ⟨L₁, L₂ ++ [(curOp α p, o)], o', by simp [hs], hr⟩

/-- Internal steps preserve the invariant (the linearization grows at linearization points). -/
lemma Inv.step_tau {α : List (Label P (atSpec P Acct μ q₀))} {C C' : Cfg μ q₀} {L}
    (hI : Inv α C L) {p : P} (h : (impl μ q₀).step C (.tau p) = some C') :
    ∃ L', Inv (α ++ [.tau p]) C' L' := by
  have h0 : C.pend p ≠ none := (Impl.step_tau h).1
  have hB := balance_eq hI.bal
  cases hpc : (C.loc p).pc with
  | idle => exact absurd (hI.idle p hpc) h0
  | done r => simp [Impl.step, impl, implGen, hpc] at h
  | scanT a b x =>
    have hact : PC.op μ q₀ p (C.loc p).pc = some (ATOp.transfer p a b x) := by rw [hpc]; rfl
    rw [impl, step_scanT C p a b x h0 hpc] at h
    cases h
    by_cases hc : p ∈ μ a ∧ x ≤ balance q₀ a (C.mem ())
    · simp only [hc, and_self, ↓reduceIte]
      refine ⟨L, hI.lin.append_tau p, hI.bal, hI.own, ?_, ?_, ?_, ?_, ?_⟩
      · intro q
        by_cases hq : q = p
        · subst hq; simp only [Function.update_self]; exact hI.ops q
        · simp only [Function.update_of_ne hq]; exact hI.ops q
      · intro q hq'
        by_cases hq : q = p
        · subst hq; simp at hq'
        · simp only [Function.update_of_ne hq] at hq' ⊢; exact hI.idle q hq'
      · intro q o' hq'
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self] at hq'
          have : PC.op μ q₀ q (PC.upd a b x) = PC.op μ q₀ q (C.loc q).pc := by rw [hpc]; rfl
          rw [this] at hq'
          obtain ⟨h1, h2, h3⟩ := hI.active q o' hq'
          rw [curOp_append_tau]
          exact ⟨h1, h2, opOf_append_of_eq_some h3 _⟩
        · simp only [Function.update_of_ne hq] at hq' ⊢
          obtain ⟨h1, h2, h3⟩ := hI.active q o' hq'
          rw [curOp_append_tau]
          exact ⟨h1, h2, opOf_append_of_eq_some h3 _⟩
      · intro q a' b' x' hq'
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self, PC.upd.injEq] at hq'
          obtain ⟨rfl, rfl, rfl⟩ := hq'
          have := hI.bal a; have := hB a
          exact ⟨hc.1, by dsimp only; omega⟩
        · simp only [Function.update_of_ne hq] at hq'; exact hI.upd q a' b' x' hq'
      · intro q r' hq'
        by_cases hq : q = p
        · subst hq; simp at hq'
        · simp only [Function.update_of_ne hq] at hq'
          rw [curOp_append_tau]; exact hI.done q r' hq'
    · simp only [hc, ↓reduceIte]
      have hc' : ¬ (p ∈ μ a ∧ x ≤ linState L a) := by rwa [← hB a]
      refine ⟨_, hI.push_done hact rfl (fun q hq => by simp [Function.update_of_ne hq]) ?_
        (fun c => ?_) hI.own (fun _ _ => rfl) (fun q a' b' x' _ hq' => (hI.upd q a' b' x' hq').2)⟩
      · simp [hc', hI.ops p]
      · rw [atSpec_transfer_neg hc']; exact hI.bal c
  | upd a b x =>
    have hact : PC.op μ q₀ p (C.loc p).pc = some (ATOp.transfer p a b x) := by rw [hpc]; rfl
    obtain ⟨hown_a, hx⟩ := hI.upd p a b x hpc
    have hlx : x ≤ linState L a := by have := hI.bal a; omega
    have hδ := atSpec_transfer_pos (q₀ := q₀) (q := linState L) (b := b) ⟨hown_a, hlx⟩
    rw [impl, step_upd C p a b x h0 hpc] at h
    cases h
    refine ⟨_, hI.push_done hact rfl ?_ ?_ ?_ ?_ ?_ ?_⟩
    · intro q hq; simp [Function.update_of_ne hq]
    · simp [hown_a, hlx]
    · intro c
      rw [hδ]
      dsimp only
      rw [hI.ops p, inflow_update_append, outflow_update_append, moveFunds_apply]
      have := hI.bal c
      by_cases hca : c = a
      · subst hca
        by_cases hcb : c = b
        · subst hcb; simp only [↓reduceIte]; omega
        · simp only [↓reduceIte, hcb, Ne.symm hcb, ↓reduceIte]; omega
      · by_cases hcb : c = b
        · subst hcb; simp only [hca, Ne.symm hca, ↓reduceIte, ↓reduceIte]; omega
        · simp only [hca, hcb, Ne.symm hca, Ne.symm hcb, ↓reduceIte]; omega
    · intro q t ht
      dsimp only at ht
      by_cases hq : q = p
      · subst hq
        rw [Function.update_self, hI.ops q, List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hI.own q t ht
        · exact hown_a
      · rw [Function.update_of_ne hq] at ht; exact hI.own q t ht
    · intro q hq; simp [Function.update_of_ne hq]
    · intro q a' b' x' hq hq'
      obtain ⟨hown', hx'⟩ := hI.upd q a' b' x' hq'
      have ha' : a ≠ a' := fun h => hq (owner_unique hμ (h ▸ hown') hown_a)
      dsimp only
      rw [hI.ops p, inflow_update_append, outflow_update_append]
      simp only [ha', ↓reduceIte]
      omega
  | scanR a =>
    have hact : PC.op μ q₀ p (C.loc p).pc = some (ATOp.read a) := by rw [hpc]; rfl
    rw [impl, step_scanR C p a h0 hpc] at h
    cases h
    refine ⟨_, hI.push_done hact rfl ?_ ?_ ?_ hI.own (fun _ _ => rfl)
      (fun q a' b' x' _ hq' => (hI.upd q a' b' x' hq').2)⟩
    · intro q hq; simp [Function.update_of_ne hq]
    · simp [hB, hI.ops p]
    · intro c; exact hI.bal c

omit hμ in
lemma inv_init : Inv ([] : List (Label P (atSpec P Acct μ q₀))) (impl μ q₀).initCfg [] := by
  refine ⟨⟨by simp, by simp, fun a ha => by simp [Completed] at ha, fun a b _ hb => by simp at hb,
    trivial⟩, fun c => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Impl.initCfg, impl, implGen, linState]; rfl
  · simp [Impl.initCfg, impl, implGen]
  · simp [Impl.initCfg, impl, implGen]
  · simp [Impl.initCfg, impl, implGen]
  · simp [Impl.initCfg, impl, implGen, PC.op]
  · simp [Impl.initCfg, impl, implGen]
  · simp [Impl.initCfg, impl, implGen]

/-- Every reachable configuration satisfies the invariant for some linearization. -/
theorem inv_of_run {α : List (Label P (atSpec P Acct μ q₀))} {C : Cfg μ q₀}
    (h : (impl μ q₀).run α = some C) : ∃ L, Inv α C L := by
  refine Impl.run_induction (Q := fun α C => ∃ L, Inv α C L) ⟨[], inv_init⟩ ?_ h
  rintro α C₀ ℓ C hα ⟨L, hI⟩ h
  cases ℓ with
  | inv p o => exact ⟨L, hI.step_inv (fun q hq => Impl.run_idle_counts hα hq) h⟩
  | tau p => exact hI.step_tau hμ h
  | ret p r => exact ⟨L, hI.step_ret h⟩

omit hμ in
/-- Every operation finishes within at most two own steps. -/
theorem waitFree_implGen (add : List (Tr Acct) → Tr Acct → List (Tr Acct)) :
    (implGen μ q₀ add).WaitFree := by
  refine (implGen μ q₀ add).waitFree_of_potential
    (fun _ l => match l.pc with | .scanT .. => 2 | .upd .. => 1 | .scanR .. => 1 | _ => 0) ?_
  intro p l i o k hact r
  cases hpc : l.pc <;> simp only [implGen, hpc] at hact
  all_goals cases hact
  · cases r with
    | none => simp
    | some S => dsimp only; split_ifs <;> simp
  all_goals simp

/-- **Theorem 1** of [Guerraoui et al., PODC 2019] (shared-memory part): if every account has at
most one owner, Figure 1 (with `ops_p` kept as a sequence) is a linearizable implementation of
the asset-transfer object from one atomic snapshot object. Linearization points: a read and a
failed transfer at their snapshot, a successful transfer at its update. -/
theorem fig1_linearizable : (impl μ q₀).Linearizable :=
  Impl.linearizable_of_run fun _ _ h => (inv_of_run hμ h).imp fun _ hI => hI.lin

/-- In every reachable configuration, the balance computed from the snapshot memory is the
abstract balance after the linearization (so reads return `balance(a, S)` faithfully and no
truncation occurs in `balance`). -/
theorem balance_eq_linState {α : List (Label P (atSpec P Acct μ q₀))} {C : Cfg μ q₀}
    (h : (impl μ q₀).run α = some C) :
    ∃ L, IsLinearization α L ∧ ∀ c, balance q₀ c (C.mem ()) = linState L c ∧
      outflow c (C.mem ()) ≤ q₀ c + inflow c (C.mem ()) := by
  obtain ⟨L, hI⟩ := inv_of_run hμ h
  exact ⟨L, hI.lin, fun c => ⟨balance_eq hI.bal c, by have := hI.bal c; omega⟩⟩

omit hμ in
/-- **Theorem 1** of [Guerraoui et al., PODC 2019] (wait-freedom): every operation of Figure 1
completes within two own steps (for any owner map). -/
theorem fig1_waitFree : (impl μ q₀).WaitFree := waitFree_implGen _

omit hμ in
/-- The access discipline is not restrictive: every process may invoke every read and every
transfer under its own identity. -/
theorem allowed_iff (p : P) (o : (atSpec P Acct μ q₀).Op) :
    (impl μ q₀).allowed p o ↔ ∀ p' a b x, o = ATOp.transfer p' a b x → p' = p := by
  cases o with
  | transfer p' a b x =>
    simp only [impl, implGen, allowedOp, ATOp.transfer.injEq]
    exact ⟨fun h _ _ _ _ h' => h'.1 ▸ h, fun h => h p' a b x ⟨rfl, rfl, rfl, rfl⟩⟩
  | read a => simp [impl, implGen, allowedOp]

end CryptoCons.Fig1

/-! ## Non-vacuity: a concrete single-owner instance -/

namespace CryptoCons.Fig1.Example

open Cslib.SharedMemory

/-- Two processes, each owning the account with its own index. -/
def μ : Fin 2 → Finset (Fin 2) := fun a => {a}

lemma μ_single : ∀ a, (μ a).card ≤ 1 := fun a => by simp [μ]

example : (impl μ (fun _ => 5)).Linearizable := fig1_linearizable μ_single
example : (impl μ (fun _ => 5)).WaitFree := fig1_waitFree

end CryptoCons.Fig1.Example
