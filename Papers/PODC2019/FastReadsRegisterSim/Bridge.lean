import Papers.PODC2019.FastReadsRegisterSim.ReadTree

/-!
# From CSLib executions to solo runs of the local machine

For a process `p` with a pending operation in configuration `D`, `n` steps of `p` (labels
`tau p`) lead to `Sim.soloCfg I p D n`, the configuration in which `p`'s local state and the memory
are those of the local solo run `lrun (I.act p) n (D.loc p, D.mem)`; the base accesses performed
are those of the local run. Obstruction-freedom gives termination of solo runs.
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι P L : Type} [DecidableEq P] [DecidableEq ι]

/-- The access (as a list of length `≤ 1`) performed by the next step of the local machine. -/
def accL (act : L → Action (register V v₀) (BinRegs ι) L) (p : P) (s : L × Mem ι) :
    List (P × ι × RWOp Bool) :=
  match act s.1 with
  | .access i o _ => [(p, i, o)]
  | .ret _ _ => []

namespace Sim

variable (I : Sim V v₀ ι P L) (p : P)

/-- `p`'s state and the memory after `n` local solo steps of `p` from `D`. -/
def soloCfg (D : Config (register V v₀) (BinRegs ι) P L) (n : ℕ) :
    Config (register V v₀) (BinRegs ι) P L :=
  { D with loc := Function.update D.loc p (lrun (I.act p) n (D.loc p, D.mem)).1,
           mem := (lrun (I.act p) n (D.loc p, D.mem)).2 }

variable {I p}

@[simp] lemma soloCfg_loc_self (D : Config (register V v₀) (BinRegs ι) P L) (n : ℕ) :
    (I.soloCfg p D n).loc p = (lrun (I.act p) n (D.loc p, D.mem)).1 := by
  simp [soloCfg]

@[simp] lemma soloCfg_loc_ne (D : Config (register V v₀) (BinRegs ι) P L) (n : ℕ) {q : P}
    (hq : q ≠ p) : (I.soloCfg p D n).loc q = D.loc q := by
  simp [soloCfg, Function.update_of_ne hq]

@[simp] lemma soloCfg_mem (D : Config (register V v₀) (BinRegs ι) P L) (n : ℕ) :
    (I.soloCfg p D n).mem = (lrun (I.act p) n (D.loc p, D.mem)).2 := rfl

@[simp] lemma soloCfg_pend (D : Config (register V v₀) (BinRegs ι) P L) (n : ℕ) :
    (I.soloCfg p D n).pend = D.pend := rfl

lemma soloCfg_zero (D : Config (register V v₀) (BinRegs ι) P L) : I.soloCfg p D 0 = D := by
  simp [soloCfg]

lemma step_soloCfg {D : Config (register V v₀) (BinRegs ι) P L} (hD : D.pend p ≠ none) {n : ℕ}
    (hn : ¬ IsRet (I.act p) (lrun (I.act p) n (D.loc p, D.mem))) :
    I.step (I.soloCfg p D n) (.tau p) = some (I.soloCfg p D (n + 1)) := by
  rcases isRet_or_acc (act := I.act p) (lrun (I.act p) n (D.loc p, D.mem)) with h | ⟨i, o, k, hk⟩
  · exact absurd h hn
  · rw [Impl.step_tau_eq_some (by simpa using hD) (by simpa using hk)]
    simp only [soloCfg, lrun_succ, lstep, hk, Function.update_idem]

lemma runFrom_taus {D : Config (register V v₀) (BinRegs ι) P L} (hD : D.pend p ≠ none) (n : ℕ)
    (hn : ∀ j < n, ¬ IsRet (I.act p) (lrun (I.act p) j (D.loc p, D.mem))) :
    I.runFrom D (List.replicate n (.tau p)) = some (I.soloCfg p D n) := by
  induction n with
  | zero => simp [soloCfg_zero]
  | succ n ih =>
    rw [List.replicate_succ', Impl.runFrom_append_of_eq I (ih (fun j hj => hn j (by omega))),
      Impl.runFrom_singleton, step_soloCfg hD (hn n (by omega))]

lemma soloStep_soloCfg {D : Config (register V v₀) (BinRegs ι) P L} (hD : D.pend p ≠ none)
    {n : ℕ} (hn : ¬ IsRet (I.act p) (lrun (I.act p) n (D.loc p, D.mem))) :
    I.soloStep p (I.soloCfg p D n) = I.soloCfg p D (n + 1) := by
  rcases isRet_or_acc (act := I.act p) (lrun (I.act p) n (D.loc p, D.mem)) with h | ⟨i, o, k, hk⟩
  · exact absurd h hn
  · have hnl : I.nextLabel (I.soloCfg p D n) p = .tau p := by
      simp [Impl.nextLabel, hk]
    simp only [Impl.soloStep, soloCfg_pend, hD, ↓reduceIte, hnl, step_soloCfg hD hn,
      Option.getD_some]

/-- Obstruction-freedom: the local solo run of a pending process in a reachable configuration
returns. -/
lemma exists_isRet (hof : I.ObstructionFree) {D : Config (register V v₀) (BinRegs ι) P L}
    (hreach : I.Reachable D) (hD : D.pend p ≠ none) :
    ∃ n, IsRet (I.act p) (lrun (I.act p) n (D.loc p, D.mem)) := by
  obtain ⟨k, hk⟩ := hof D p hreach hD
  by_contra hall
  push Not at hall
  have : ∀ j, (I.soloStep p)^[j] D = I.soloCfg p D j := by
    intro j
    induction j with
    | zero => simp [soloCfg_zero]
    | succ j ih => rw [Function.iterate_succ_apply', ih, soloStep_soloCfg hD (hall j)]
  rw [this] at hk
  exact hD hk

lemma runFrom_ret {D : Config (register V v₀) (BinRegs ι) P L} (hD : D.pend p ≠ none) {n : ℕ}
    {u : V} {l : L} (hn : I.act p (lrun (I.act p) n (D.loc p, D.mem)).1 = .ret u l) :
    I.runFrom (I.soloCfg p D n) [.ret p u] =
      some { I.soloCfg p D n with pend := Function.update D.pend p none,
                                  loc := Function.update (I.soloCfg p D n).loc p l } := by
  rw [Impl.runFrom_singleton, Impl.step_ret_eq_some (by simpa using hD) (by simpa using hn)]
  rfl

/-! ### A whole operation run solo -/

variable (I) in
/-- The configuration after `p` invokes `o` in `C`. -/
def invCfg (C : Config (register V v₀) (BinRegs ι) P L) (p : P) (o : (register V v₀).Op) :
    Config (register V v₀) (BinRegs ι) P L :=
  { C with pend := Function.update C.pend p (some o),
           loc := Function.update C.loc p (I.invoke p (C.loc p) o) }

variable (I p) in
/-- Number of steps of the operation `o` invoked by `p` in `C` and run solo. -/
noncomputable def retTime (C : Config (register V v₀) (BinRegs ι) P L) (o : (register V v₀).Op) :
    ℕ := by
  classical
  exact if h : ∃ n, IsRet (I.act p) (lrun (I.act p) n ((I.invCfg C p o).loc p, (I.invCfg C p o).mem))
    then Nat.find h else 0

variable (I p) in
/-- Response and final local state of the operation `o` invoked by `p` in `C` and run solo. -/
noncomputable def retOut (C : Config (register V v₀) (BinRegs ι) P L) (o : (register V v₀).Op) :
    V × L :=
  match I.act p (lrun (I.act p) (I.retTime p C o) ((I.invCfg C p o).loc p, (I.invCfg C p o).mem)).1 with
  | .ret u l => (u, l)
  | .access _ _ _ => (v₀, C.loc p)

variable (I p) in
/-- Labels of the operation `o` invoked by `p` in `C` and run solo to completion. -/
noncomputable def opLabels (C : Config (register V v₀) (BinRegs ι) P L) (o : (register V v₀).Op) :
    List (Label P (register V v₀)) :=
  .inv p o :: (List.replicate (I.retTime p C o) (.tau p) ++ [.ret p (I.retOut p C o).1])

variable (I p) in
/-- Configuration after the operation `o` invoked by `p` in `C` and run solo to completion. -/
noncomputable def opCfg (C : Config (register V v₀) (BinRegs ι) P L) (o : (register V v₀).Op) :
    Config (register V v₀) (BinRegs ι) P L :=
  { I.soloCfg p (I.invCfg C p o) (I.retTime p C o) with
      pend := Function.update (I.invCfg C p o).pend p none,
      loc := Function.update (I.soloCfg p (I.invCfg C p o) (I.retTime p C o)).loc p
        (I.retOut p C o).2 }

@[simp] lemma invCfg_loc_self (C : Config (register V v₀) (BinRegs ι) P L) (o) :
    (I.invCfg C p o).loc p = I.invoke p (C.loc p) o := by simp [invCfg]

@[simp] lemma invCfg_mem (C : Config (register V v₀) (BinRegs ι) P L) (o) :
    (I.invCfg C p o).mem = C.mem := rfl

lemma step_inv_invCfg {C : Config (register V v₀) (BinRegs ι) P L} (hC : C.pend p = none)
    {o : (register V v₀).Op} (ho : I.allowed p o) :
    I.step C (.inv p o) = some (I.invCfg C p o) :=
  Impl.step_inv_eq_some hC ho

/-- Facts about a solo operation in a reachable configuration of an obstruction-free
simulation. -/
lemma retTime_spec (hof : I.ObstructionFree) {C : Config (register V v₀) (BinRegs ι) P L}
    (hreach : I.Reachable C) (hC : C.pend p = none) {o : (register V v₀).Op}
    (ho : I.allowed p o) :
    (∀ j < I.retTime p C o, ¬ IsRet (I.act p)
        (lrun (I.act p) j (I.invoke p (C.loc p) o, C.mem))) ∧
      I.act p (lrun (I.act p) (I.retTime p C o) (I.invoke p (C.loc p) o, C.mem)).1 =
        .ret (I.retOut p C o).1 (I.retOut p C o).2 := by
  classical
  have hreach' : I.Reachable (I.invCfg C p o) := by
    obtain ⟨α, hα⟩ := hreach
    exact ⟨α ++ [.inv p o], by rw [Impl.run_append_of_eq I hα, Impl.runFrom_singleton,
      step_inv_invCfg hC ho]⟩
  have hex := exists_isRet hof hreach' (p := p) (by simp [invCfg])
  simp only [invCfg_loc_self, invCfg_mem] at hex
  have hT : I.retTime p C o = Nat.find hex := by
    simp only [retTime, invCfg_loc_self, invCfg_mem, hex, ↓reduceDIte]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hT] at hj; exact Nat.find_min hex hj
  · obtain ⟨u, l, hul⟩ := hT ▸ Nat.find_spec hex
    simp only [retOut, invCfg_loc_self, invCfg_mem, hul]

lemma runFrom_opLabels (hof : I.ObstructionFree) {C : Config (register V v₀) (BinRegs ι) P L}
    (hreach : I.Reachable C) (hC : C.pend p = none) {o : (register V v₀).Op}
    (ho : I.allowed p o) : I.runFrom C (I.opLabels p C o) = some (I.opCfg p C o) := by
  obtain ⟨h1, h2⟩ := retTime_spec hof hreach hC ho
  have hD : (I.invCfg C p o).pend p ≠ none := by simp [invCfg]
  rw [opLabels, Impl.runFrom_cons, step_inv_invCfg hC ho, Option.bind_some,
    Impl.runFrom_append_of_eq I (runFrom_taus hD _ (by simpa using h1))]
  rw [runFrom_ret hD (by simpa using h2)]
  rfl

lemma runFrom_opLabels_take (hof : I.ObstructionFree)
    {C : Config (register V v₀) (BinRegs ι) P L}
    (hreach : I.Reachable C) (hC : C.pend p = none) {o : (register V v₀).Op}
    (ho : I.allowed p o) {t : ℕ} (ht : t ≤ I.retTime p C o) :
    I.runFrom C (.inv p o :: List.replicate t (.tau p)) =
      some (I.soloCfg p (I.invCfg C p o) t) := by
  obtain ⟨h1, -⟩ := retTime_spec hof hreach hC ho
  have hD : (I.invCfg C p o).pend p ≠ none := by simp [invCfg]
  rw [Impl.runFrom_cons, step_inv_invCfg hC ho, Option.bind_some,
    runFrom_taus hD _ (fun j hj => by simpa using h1 j (by omega))]

@[simp] lemma opCfg_pend_self (C : Config (register V v₀) (BinRegs ι) P L) (o) :
    (I.opCfg p C o).pend p = none := by simp [opCfg]

lemma opCfg_pend_ne (C : Config (register V v₀) (BinRegs ι) P L) (o) {q : P} (hq : q ≠ p) :
    (I.opCfg p C o).pend q = C.pend q := by
  simp [opCfg, invCfg, Function.update_of_ne hq]

lemma opCfg_loc_ne (C : Config (register V v₀) (BinRegs ι) P L) (o) {q : P} (hq : q ≠ p) :
    (I.opCfg p C o).loc q = C.loc q := by
  simp [opCfg, soloCfg, invCfg, Function.update_of_ne hq]

lemma opCfg_mem (C : Config (register V v₀) (BinRegs ι) P L) (o) :
    (I.opCfg p C o).mem =
      (lrun (I.act p) (I.retTime p C o) (I.invoke p (C.loc p) o, C.mem)).2 := by
  simp [opCfg, soloCfg]

/-! ### Accesses -/

lemma accesses_append {C C' : Config (register V v₀) (BinRegs ι) P L}
    {α : List (Label P (register V v₀))} (h : I.runFrom C α = some C')
    (β : List (Label P (register V v₀))) :
    I.accesses C (α ++ β) = I.accesses C α ++ I.accesses C' β := by
  induction α generalizing C with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; simp [accesses]
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      simp only [List.cons_append, accesses, hs, Option.getD_some, ih h, List.append_assoc]

lemma accesses_taus {D : Config (register V v₀) (BinRegs ι) P L} (hD : D.pend p ≠ none) (n : ℕ)
    (hn : ∀ j < n, ¬ IsRet (I.act p) (lrun (I.act p) j (D.loc p, D.mem))) :
    I.accesses D (List.replicate n (.tau p)) =
      (List.range n).flatMap (fun j => accL (I.act p) p (lrun (I.act p) j (D.loc p, D.mem))) := by
  induction n with
  | zero => simp [accesses]
  | succ n ih =>
    rw [List.replicate_succ', accesses_append (runFrom_taus hD n (fun j hj => hn j (by omega))),
      ih (fun j hj => hn j (by omega)), List.range_succ, List.flatMap_append]
    simp [accesses, accessOf, accL]
    rfl

end Sim

/-! ### Counting accesses of a local run -/

section Count

variable {act : L → Action (register V v₀) (BinRegs ι) L} {p : P}

lemma numReads_accL (s : L × Mem ι) :
    numReads p (accL act p s) = (rd act s).toList.length := by
  unfold accL rd
  split
  · rename_i i o k hk
    cases o <;> simp [numReads, hk]
  · rename_i u l hk; simp [numReads, hk]

lemma numReads_run (s : L × Mem ι) (n : ℕ) :
    numReads p ((List.range n).flatMap (fun j => accL act p (lrun act j s))) =
      (rr act s n).length := by
  induction n with
  | zero => simp [numReads, rr]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, rr_succ, List.length_append, ← ih]
    have := numReads_accL (p := p) (act := act) (lrun act n s)
    simp only [numReads] at this
    simp [numReads, List.countP_append, ← this]

lemma numSteps_run (s : L × Mem ι) (n : ℕ) (hn : ∀ j < n, ¬ IsRet act (lrun act j s)) :
    numSteps p ((List.range n).flatMap (fun j => accL act p (lrun act j s))) = n := by
  induction n with
  | zero => simp [numSteps]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [numSteps, List.countP_append] at ih ⊢
    rw [ih (fun j hj => hn j (by omega))]
    rcases isRet_or_acc (act := act) (lrun act n s) with h | ⟨i, o, k, hk⟩
    · exact absurd h (hn n (by omega))
    · simp [accL, hk]

/-- A register whose value changes during a local run is written by some step. -/
lemma exists_write_of_ne (s : L × Mem ι) (n : ℕ) {i : ι} (h : (lrun act n s).2 i ≠ s.2 i) :
    (p, i) ∈ (((List.range n).flatMap (fun j => accL act p (lrun act j s))).filter
      (fun a => decide (a.1 = p ∧ a.2.2 ≠ .read))).map (fun a => (a.1, a.2.1)) := by
  induction n with
  | zero => exact absurd rfl h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.filter_append, List.map_append]
    by_cases h' : (lrun act n s).2 i = s.2 i
    · -- changed by step `n`
      apply List.mem_append_right
      rw [lrun_succ] at h
      rcases isRet_or_acc (act := act) (lrun act n s) with hr | ⟨j, o, k, hk⟩
      · rw [lstep_of_isRet hr] at h; exact absurd h' h
      · have hji : j = i := by
          by_contra hne
          rw [lstep_mem_of_not_acc (fun ⟨o', k', hk'⟩ => by
            rw [hk] at hk'; simp only [Action.access.injEq] at hk'; exact hne hk'.1)] at h
          exact h h'
        subst hji
        cases o with
        | read =>
          rw [lstep_of_rdAt hk] at h; exact absurd h' h
        | write b => simp [accL, hk]
    · exact List.mem_append_left _ (ih h')

lemma numWrites_ge (s : L × Mem ι) (n : ℕ) (rs : List ι) (hnd : rs.Nodup)
    (hrs : ∀ i ∈ rs, (lrun act n s).2 i ≠ s.2 i) :
    rs.length ≤ numWrites p ((List.range n).flatMap (fun j => accL act p (lrun act j s))) := by
  rw [numWrites, List.countP_eq_length_filter]
  have hsub : rs.map (fun i => (p, i)) ⊆ (((List.range n).flatMap
      (fun j => accL act p (lrun act j s))).filter
      (fun a => decide (a.1 = p ∧ a.2.2 ≠ .read))).map (fun a => (a.1, a.2.1)) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact exists_write_of_ne s n (hrs i hi)
  have hnd' : (rs.map (fun i => (p, i))).Nodup :=
    hnd.map (fun a b hab => by simpa using hab)
  have := (hnd'.subperm hsub).length_le
  simpa using this

end Count

end Podc.FastReadsRegisterSim
