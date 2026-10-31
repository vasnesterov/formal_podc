import Papers.PODC2019.FastReadsRegisterSim.FastTree
import Papers.PODC2019.FastReadsRegisterSim.Section3

/-!
# Executions with inserted reads (for Section 4)

A reader `r` whose first read is described by a decision tree (`node`, `path`, `val` of
`FastTree.lean`, hypotheses `TreeHyp`) can be inserted anywhere in an execution: its read steps
change neither the memory nor the other processes. `rcfg C r l o` is `C` with the local state and
the pending operation of `r` replaced.

* `runFrom_invTaus` — `inv r read` followed by `j` steps at constant memory `M`;
* `step_tau_node`, `step_ret_node` — single steps from a node of the tree;
* `runFrom_readBlock` — a complete first read at constant memory, returning
  `val (path M m)`;
* `runFrom_rcfg` — labels of other processes run the same whatever `r`'s state is.
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι P L : Type} [DecidableEq P] [DecidableEq ι]

/-- `C` with the local state and the pending operation of `r` replaced. -/
def rcfg (C : Config (register V v₀) (BinRegs ι) P L) (r : P) (l : L)
    (o : Option (register V v₀).Op) : Config (register V v₀) (BinRegs ι) P L :=
  { C with loc := Function.update C.loc r l, pend := Function.update C.pend r o }

lemma config_ext {C D : Config (register V v₀) (BinRegs ι) P L} (h1 : C.loc = D.loc)
    (h2 : C.pend = D.pend) (h3 : C.mem = D.mem) : C = D := by
  cases C; cases D; simp_all

lemma eq_rcfg {C D : Config (register V v₀) (BinRegs ι) P L} {r : P} {l : L} {o}
    (hloc : ∀ q, q ≠ r → D.loc q = C.loc q) (hpend : ∀ q, q ≠ r → D.pend q = C.pend q)
    (hmem : D.mem = C.mem) (hl : D.loc r = l) (ho : D.pend r = o) : D = rcfg C r l o := by
  apply config_ext
  · funext q; by_cases hq : q = r
    · subst hq; simp [rcfg, hl]
    · simp [rcfg, Function.update_of_ne hq, hloc q hq]
  · funext q; by_cases hq : q = r
    · subst hq; simp [rcfg, ho]
    · simp [rcfg, Function.update_of_ne hq, hpend q hq]
  · exact hmem

@[simp] lemma rcfg_rcfg (C : Config (register V v₀) (BinRegs ι) P L) (r : P) (l l' : L) (o o') :
    rcfg (rcfg C r l o) r l' o' = rcfg C r l' o' := by
  simp [rcfg, Function.update_idem]

@[simp] lemma rcfg_mem (C : Config (register V v₀) (BinRegs ι) P L) (r : P) (l : L) (o) :
    (rcfg C r l o).mem = C.mem := rfl

@[simp] lemma rcfg_loc_self (C : Config (register V v₀) (BinRegs ι) P L) (r : P) (l : L) (o) :
    (rcfg C r l o).loc r = l := by simp [rcfg]

@[simp] lemma rcfg_pend_self (C : Config (register V v₀) (BinRegs ι) P L) (r : P) (l : L) (o) :
    (rcfg C r l o).pend r = o := by simp [rcfg]

lemma rcfg_loc_ne (C : Config (register V v₀) (BinRegs ι) P L) {r q : P} (l : L) (o)
    (hq : q ≠ r) : (rcfg C r l o).loc q = C.loc q := by simp [rcfg, Function.update_of_ne hq]

lemma rcfg_pend_ne (C : Config (register V v₀) (BinRegs ι) P L) {r q : P} (l : L) (o)
    (hq : q ≠ r) : (rcfg C r l o).pend q = C.pend q := by simp [rcfg, Function.update_of_ne hq]

lemma rcfg_self (C : Config (register V v₀) (BinRegs ι) P L) (r : P) :
    rcfg C r (C.loc r) (C.pend r) = C := by
  apply config_ext <;> simp [rcfg]

variable (I : Sim V v₀ ι P L)

/-- Labels of processes other than `r` run the same whatever `r`'s local state and pending
operation are. -/
lemma runFrom_rcfg {C C' : Config (register V v₀) (BinRegs ι) P L} {r : P}
    {γ : List (Label P (register V v₀))} (hγ : ∀ ℓ ∈ γ, ℓ.proc ≠ r)
    (h : I.runFrom C γ = some C') (l : L) (o) :
    I.runFrom (rcfg C r l o) γ = some (rcfg C' r l o) := by
  have hag : Impl.AgreeOn {q | q ≠ r} C (rcfg C r l o) :=
    ⟨rfl, fun q hq => (rcfg_loc_ne C l o hq).symm, fun q hq => (rcfg_pend_ne C l o hq).symm⟩
  obtain ⟨D', hD', hag'⟩ := Impl.runFrom_agreeOn hag hγ h
  have hoth := Impl.runFrom_other I hD' (q := r) hγ
  rw [hD']
  congr 1
  exact eq_rcfg (fun q hq => (hag'.loc q hq).symm) (fun q hq => (hag'.pend q hq).symm)
    hag'.mem.symm (by rw [hoth.1]; simp) (by rw [hoth.2]; simp)

/-! ## Reads described by a decision tree -/

variable {r : P} {m : ℕ}

variable (r m) in
/-- The first read of `r` is described by the decision tree of depth `m` with root state
`invoke r (locInit r) read`. -/
structure TreeHyp : Prop where
  inner : ∀ u : List Bool, u.length < m →
    ∃ i k, I.act r (node (I.act r) (Sec3.rl₀ I r) u) = .access i .read k ∧
      ∀ b, k b = node (I.act r) (Sec3.rl₀ I r) (u ++ [b])
  leaf : ∀ u : List Bool, u.length = m →
    ∃ l, I.act r (node (I.act r) (Sec3.rl₀ I r) u) = .ret (val (I.act r) (Sec3.rl₀ I r) u) l

variable {I}

/-- The node reached after `u`. -/
abbrev nd (I : Sim V v₀ ι P L) (r : P) (u : List Bool) : L := node (I.act r) (Sec3.rl₀ I r) u

/-- The path at constant memory. -/
abbrev pth (I : Sim V v₀ ι P L) (r : P) (M : Mem ι) (j : ℕ) : List Bool :=
  path (I.act r) (Sec3.rl₀ I r) M j

/-- The value returned at a leaf. -/
abbrev vl (I : Sim V v₀ ι P L) (r : P) (u : List Bool) : V := val (I.act r) (Sec3.rl₀ I r) u

lemma step_tau_node (hT : TreeHyp I r m) {D : Config (register V v₀) (BinRegs ι) P L}
    (hD : D.pend r ≠ none) {u : List Bool} (hu : u.length < m) (hloc : D.loc r = nd I r u) :
    I.step D (.tau r) =
      some (rcfg D r (nd I r (u ++ [bit (I.act r) D.mem (nd I r u)])) (D.pend r)) := by
  obtain ⟨i, k, hk, hkb⟩ := hT.inner u hu
  rw [Impl.step_tau_eq_some hD (by rw [hloc]; exact hk)]
  congr 1
  apply config_ext
  · simp only [rcfg, bit, hk, hkb]
  · simp [rcfg]
  · simp [Function.update_eq_self]

lemma step_ret_node (hT : TreeHyp I r m) {D : Config (register V v₀) (BinRegs ι) P L}
    (hD : D.pend r ≠ none) {u : List Bool} (hu : u.length = m) (hloc : D.loc r = nd I r u) :
    ∃ l, I.step D (.ret r (vl I r u)) = some (rcfg D r l none) := by
  obtain ⟨l, hl⟩ := hT.leaf u hu
  refine ⟨l, ?_⟩
  rw [Impl.step_ret_eq_some hD (by rw [hloc]; exact hl)]
  rfl

/-- `j` steps of `r` from a node, at constant memory. -/
lemma runFrom_taus_node (hT : TreeHyp I r m) {D : Config (register V v₀) (BinRegs ι) P L}
    (hD : D.pend r ≠ none) {i j : ℕ} (hij : i + j ≤ m) (hloc : D.loc r = nd I r (pth I r D.mem i)) :
    I.runFrom D (List.replicate j (.tau r)) =
      some (rcfg D r (nd I r (pth I r D.mem (i + j))) (D.pend r)) := by
  induction j with
  | zero => simp [← hloc, rcfg_self]
  | succ j ih =>
    rw [List.replicate_succ', Impl.runFrom_append_of_eq I (ih (by omega)), Impl.runFrom_singleton,
      step_tau_node hT (u := pth I r D.mem (i + j)) (by simpa using hD) (by simp; omega) (by simp)]
    simp [path, ← add_assoc]

/-- `inv r read` followed by `j ≤ m` steps at constant memory. -/
lemma runFrom_invTaus (hT : TreeHyp I r m) (hr : I.allowed r .read)
    {C : Config (register V v₀) (BinRegs ι) P L} (hC : C.pend r = none)
    (hloc : C.loc r = I.locInit r) {j : ℕ} (hj : j ≤ m) :
    I.runFrom C (.inv r .read :: List.replicate j (.tau r)) =
      some (rcfg C r (nd I r (pth I r C.mem j)) (some .read)) := by
  have hst : I.step C (.inv r .read) = some (rcfg C r (nd I r (pth I r C.mem 0)) (some .read)) := by
    rw [Impl.step_inv_eq_some hC hr]
    congr 1
    apply config_ext <;> simp [rcfg, path, hloc, Sec3.rl₀]
  rw [Impl.runFrom_cons, hst, Option.bind_some,
    runFrom_taus_node hT (by simp) (by omega : 0 + j ≤ m) (by simp)]
  simp

/-- The labels of a complete first read of `r` at constant memory `M`. -/
def readBlock (I : Sim V v₀ ι P L) (r : P) (m : ℕ) (M : Mem ι) :
    List (Label P (register V v₀)) :=
  .inv r .read :: (List.replicate m (.tau r) ++ [.ret r (vl I r (pth I r M m))])

/-- A complete first read of `r`, inserted at a configuration where `r` has not started. -/
lemma runFrom_readBlock (hT : TreeHyp I r m) (hr : I.allowed r .read)
    {C : Config (register V v₀) (BinRegs ι) P L} (hC : C.pend r = none)
    (hloc : C.loc r = I.locInit r) :
    ∃ l, I.runFrom C (readBlock I r m C.mem) = some (rcfg C r l none) := by
  have h1 := runFrom_invTaus hT hr hC hloc (le_refl m)
  obtain ⟨l, hl⟩ := step_ret_node hT (D := rcfg C r (nd I r (pth I r C.mem m)) (some .read))
    (u := pth I r C.mem m)
    (by simp) (by simp) (by simp)
  refine ⟨l, ?_⟩
  rw [readBlock, ← List.cons_append, Impl.runFrom_append_of_eq I h1, Impl.runFrom_singleton]
  simpa using hl

lemma proc_readBlock (M : Mem ι) : ∀ ℓ ∈ readBlock I r m M, ℓ.proc = r := by
  intro ℓ hℓ
  simp only [readBlock, List.mem_cons, List.mem_append, List.mem_replicate,
    List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | ⟨-, rfl⟩ | rfl <;> rfl

lemma opsOf_readBlock (M : Mem ι) (q : P) :
    opsOf (readBlock I r m M) q = if r = q then [.read] else [] := by
  simp only [readBlock, opsOf_cons, opsOf_append, opsOf_replicate_tau, Label.invOf_inv,
    Label.invOf_ret]
  split_ifs <;> simp

lemma respsOf_readBlock (M : Mem ι) (q : P) :
    respsOf (readBlock I r m M) q = if r = q then [vl I r (pth I r M m)] else [] := by
  simp only [readBlock, respsOf_cons, respsOf_append, respsOf_replicate_tau, Label.retOf_inv,
    Label.retOf_ret]
  split_ifs <;> simp

end Podc.FastReadsRegisterSim
