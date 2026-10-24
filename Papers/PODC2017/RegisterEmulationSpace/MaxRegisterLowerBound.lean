import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.FullInfo
import Cslib.Computability.Distributed.SharedMemory.Objects.MaxRegister
import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# Theorem 2 of [CS17]: a `k`-writer max-register needs `k` registers

[CS17] G. Chockler, A. Spiegelman, *Space Complexity of Fault-Tolerant Register Emulations*,
PODC 2017 (arXiv 1705.07212).

**Theorem 2.** For all `k > 0`, any algorithm implementing a wait-free `k`-writer max-register
from a collection of wait-free MWMR atomic base registers uses at least `k` base registers.

The paper derives Theorem 2 from its fault-tolerant Theorem 1 (run `2f + 1` copies of the
algorithm and multi-writer ABD on top). We prove it **directly by a covering argument**:

* Stage `j ≤ k` (`Stage`): a reachable configuration in which writers `w 0, …, w (j-1)` each have
  a pending `writeMax` and cover `j` *distinct* registers, while the other writers and the reader
  `q` have never invoked anything.
* Step (`Stage.succ`): let `w j` run `writeMax (j+1)` solo until it is about to write a register
  outside the covered set or returns (`exists_solo_until`). If it returned, a block write by
  `w 0, …, w (j-1)` hides all its writes (`blockWrite_agreeOn`), and a subsequent solo `readMax` by
  `q` returns the same value `r` as in the execution where `w j` did nothing. Linearizability
  forces `r ≥ j + 1` in the first execution (the `writeMax (j+1)` precedes the read) and
  `r ≤ j` in the second (only values `≤ j` were written), a contradiction.

Only obstruction-freedom and linearizability **on `k`-writer executions** (`WriterExec`: every
`writeMax` is invoked by one of the writers) are used.

## Main declarations

* `theorem2` — Theorem 2 with the weakest hypotheses (linearizability and obstruction-freedom on
  `k`-writer executions); `theorem2_of_waitFree` — the paper's form (linearizable, wait-free).
* `Stage`, `Stage.succ`, `exists_stage` — the covering construction.
* `le_resp_of_precedes`, `resp_le_of_ops` — facts about every linearization of a max-register
  history.

The reader `q` must be distinct from the writers: with a single process (`k = 1`, no reader)
zero registers suffice, since the writer can keep the maximum in its local state. The theorem
also holds (trivially) for `k = 0`.
-/

namespace Podc.RegisterEmulationSpace.MaxRegLB

open Cslib.SharedMemory Cslib.SharedMemory.Impl

set_option linter.unusedSectionVars false

/-! ### Linearizations of max-register histories -/

section MaxLin

variable {P : Type} [DecidableEq P]

-- CSLib candidate
/-- In a legal sequential max-register history, a read returns at most `m` if the initial state
and all written values are at most `m`. -/
lemma seqOK_read_le {α : List (Label P maxRegObj)} (m : ℕ) :
    ∀ (Λ : List (OpId P × MaxOp)) (s : ℕ), s ≤ m → (∀ y ∈ Λ, ∀ v, y.2 = .writeMax v → v ≤ m) →
      SeqOK α s Λ → ∀ y ∈ Λ, y.2 = .readMax → ∀ r, respOf α y.1 = some r → r ≤ m := by
  intro Λ
  induction Λ with
  | nil => intro s _ _ _ y hy; simp at hy
  | cons x Λ ih =>
    obtain ⟨x, o⟩ := x
    intro s hs hw hseq y hy hyr r hr
    obtain ⟨h1, h2⟩ := hseq
    have hs' : (maxRegObj.δ s o).1 ≤ m := by
      cases o with
      | readMax => simpa using hs
      | writeMax v => simpa using ⟨hs, hw (x, .writeMax v) (by simp) v rfl⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · simp only at hyr; subst hyr
      have h3 : (s : ℕ) = (r : ℕ) := h1 r hr
      exact h3 ▸ hs
    · exact ih _ hs' (fun y' hy' => hw y' (by simp [hy'])) h2 y hy hyr r hr

-- CSLib candidate
/-- In a legal sequential max-register history, a read returns at least the initial state and
every value written before it. -/
lemma seqOK_read_ge {α : List (Label P maxRegObj)} {b : OpId P} {r : ℕ}
    (hb : respOf α b = some r) (Λ₂ : List (OpId P × MaxOp)) :
    ∀ (Λ₁ : List (OpId P × MaxOp)) (s : ℕ), SeqOK α s (Λ₁ ++ (b, .readMax) :: Λ₂) →
      s ≤ r ∧ ∀ y ∈ Λ₁, ∀ v, y.2 = .writeMax v → v ≤ r := by
  intro Λ₁
  induction Λ₁ with
  | nil =>
    intro s hseq
    have := hseq.1 r hb
    simp at this
    exact ⟨this.le, by simp⟩
  | cons x Λ₁ ih =>
    obtain ⟨x, o⟩ := x
    intro s hseq
    obtain ⟨_, h2⟩ := hseq
    obtain ⟨g1, g2⟩ := ih _ h2
    refine ⟨?_, ?_⟩
    · cases o with
      | readMax => simpa using g1
      | writeMax v => simp at g1; omega
    · intro y hy v hv
      rcases List.mem_cons.1 hy with rfl | hy
      · simp only at hv; subst hv; simp at g1; omega
      · exact g2 y hy v hv

-- CSLib candidate
/-- A completed `readMax` that is preceded (in real time) by a `writeMax v` returns at least `v`,
in every linearization. -/
lemma le_resp_of_precedes {α : List (Label P maxRegObj)} {Λ : List (OpId P × MaxOp)}
    (hΛ : IsLinearization α Λ) {a b : OpId P} {v r : ℕ}
    (ha : opOf α a = some (.writeMax v)) (hb : opOf α b = some .readMax)
    (hr : respOf α b = some r) (hab : Precedes α a b) : v ≤ r := by
  have hbc : Completed α b := by
    simp only [respOf, List.getElem?_eq_some_iff] at hr
    exact hr.1
  have hsub := hΛ.realtime a b hab (hΛ.complete b hbc)
  obtain ⟨r₁, r₂, he, har₁, hbr₂⟩ := List.cons_sublist_iff.1 hsub
  obtain ⟨s, t, rfl⟩ := List.append_of_mem (List.singleton_sublist.1 hbr₂)
  rw [← List.append_assoc] at he
  obtain ⟨Λ₁, Λ', rfl, h1, h2⟩ := List.map_eq_append_iff.1 he
  obtain ⟨y, Λ₂, rfl, hy, -⟩ := List.map_eq_cons_iff.1 h2
  have hy2 : y.2 = .readMax := by
    have := hΛ.op_eq y (by simp)
    rw [hy, hb] at this
    exact (Option.some.inj this).symm
  obtain ⟨y₁, y₂⟩ := y
  simp only at hy hy2
  subst hy hy2
  have hseq := hΛ.seq
  obtain ⟨-, g2⟩ := seqOK_read_ge hr Λ₂ Λ₁ _ hseq
  have ha₁ : a ∈ Λ₁.map Prod.fst := by rw [h1]; simp [har₁]
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha₁
  have hz2 : z.2 = .writeMax v := by
    have := hΛ.op_eq z (by simp [hz])
    rw [ha] at this
    exact (Option.some.inj this).symm
  exact g2 z hz v hz2

-- CSLib candidate
/-- If every `writeMax` of an execution writes a value `≤ m`, every completed `readMax` returns a
value `≤ m`, in every linearization. -/
lemma resp_le_of_ops {α : List (Label P maxRegObj)} {Λ : List (OpId P × MaxOp)}
    (hΛ : IsLinearization α Λ) {m : ℕ}
    (hops : ∀ x v, MaxOp.writeMax v ∈ opsOf α x → v ≤ m) {b : OpId P} {r : ℕ}
    (hb : opOf α b = some .readMax) (hr : respOf α b = some r) : r ≤ m := by
  have hbc : Completed α b := by
    simp only [respOf, List.getElem?_eq_some_iff] at hr
    exact hr.1
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hΛ.complete b hbc)
  have hy2 : y.2 = .readMax := by
    have := hΛ.op_eq y hy
    rw [hb] at this
    exact (Option.some.inj this).symm
  refine seqOK_read_le m Λ 0 (Nat.zero_le _) (fun z hz v hv => ?_) hΛ.seq y hy hy2 r hr
  have := hΛ.op_eq z hz
  rw [hv] at this
  exact hops z.1.1 v (List.mem_of_getElem? this)

end MaxLin

/-! ### Solo runs under obstruction-freedom on a set of executions -/

section Solo

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P S : Type} [DecidableEq P] [DecidableEq ι]

-- CSLib candidate (variant of `Impl.soloOp_spec` for `ObstructionFreeOn`)
/-- Under obstruction-freedom on the executions of `E`, an idle process whose invocation keeps the
execution in `E` can invoke and then run solo until it returns. -/
lemma exists_soloOp_of_obstructionFreeOn (I : Impl A B P S) {E : List (Label P A) → Prop}
    (hof : I.ObstructionFreeOn E) (p : P) (o : A.Op) (ho : I.allowed p o)
    {α : List (Label P A)} {C : Config A B P S} (hα : I.run α = some C) (hC : C.pend p = none)
    (hE : E (α ++ [.inv p o])) :
    ∃ C₁ n, I.step C (.inv p o) = some C₁ ∧ ((I.soloStep p)^[n] C₁).pend p = none ∧
      I.runFrom C (.inv p o :: I.soloLabels p C₁ n) = some ((I.soloStep p)^[n] C₁) := by
  classical
  obtain ⟨C₁, hs⟩ : ∃ C₁, I.step C (.inv p o) = some C₁ := by simp [Impl.step, hC, ho]
  have hC₁ : C₁.pend p ≠ none := by simp [(step_inv hs).2.2.1]
  have hrun : I.run (α ++ [.inv p o]) = some C₁ := by
    rw [run_append_of_eq I hα, runFrom_singleton, hs]
  obtain ⟨n, hn⟩ := hof _ C₁ p hrun hE hC₁
  exact ⟨C₁, n, hs, hn, by rw [runFrom_cons, hs, Option.bind_some, runFrom_soloLabels]⟩

end Solo

/-! ### The covering construction -/

section Construction

variable {ι V : Type} {v₀ : V} {P S : Type} [DecidableEq P] [DecidableEq ι]

/-- `k`-writer executions: every `writeMax` is invoked by a process of `W` (the writers);
the other processes only read. -/
def WriterExec (W : Set P) (α : List (Label P maxRegObj)) : Prop :=
  ∀ p v, MaxOp.writeMax v ∈ opsOf α p → p ∈ W

-- CSLib candidate
/-- Every primitive of a register is read-only or a blind write. -/
lemma regFamily_readOnly_or_overwrites (i : ι) (o : (RegFamily ι V v₀ i).Op) :
    (RegFamily ι V v₀ i).ReadOnly o ∨ (RegFamily ι V v₀ i).Overwrites o := by
  cases o with
  | read => exact Or.inl fun _ => rfl
  | write v => exact Or.inr (register_write_overwrites v₀ v)

variable (I : Impl maxRegObj (RegFamily ι V v₀) P S)

/-- Stage `j` of the covering construction: after the execution `α` (reaching `C`), the writers
`w 0, …, w (j-1)` have invoked `writeMax 1, …, writeMax j` respectively, are still pending, and
cover the pairwise distinct registers `reg 0, …, reg (j-1)`; the writers `w j, …, w (k-1)` and the
reader `q` have never invoked an operation. -/
structure Stage (w : ℕ → P) (q : P) (k j : ℕ) (α : List (Label P maxRegObj))
    (C : Config maxRegObj (RegFamily ι V v₀) P S) (reg : Fin j → ι) : Prop where
  run : I.run α = some C
  cov : ∀ i : Fin j, I.Covers C (w i) (reg i)
  inj : Function.Injective reg
  idle : ∀ i, j ≤ i → i < k → C.pend (w i) = none ∧ opsOf α (w i) = []
  qidle : C.pend q = none ∧ opsOf α q = []
  ops : ∀ x o, o ∈ opsOf α x → ∃ i < j, x = w i ∧ o = .writeMax (i + 1)

variable {I} {w : ℕ → P} {q : P} {k : ℕ} {W : Set P}

lemma stage_zero : Stage I w q k 0 [] I.initCfg Fin.elim0 :=
  ⟨rfl, fun i => i.elim0, fun i => i.elim0, fun _ _ _ => ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    fun _ _ h => by simp at h⟩

/-- The induction step of the covering construction. -/
theorem Stage.succ (hwinj : ∀ i < k, ∀ i' < k, w i = w i' → i = i') (hwq : ∀ i < k, w i ≠ q)
    (hW : ∀ i < k, w i ∈ W) (hallw : ∀ i < k, ∀ v, I.allowed (w i) (.writeMax v))
    (hallq : I.allowed q .readMax)
    (hlin : ∀ α, I.Valid α → WriterExec W α → ∃ Λ, IsLinearization α Λ)
    (hof : I.ObstructionFreeOn (WriterExec W))
    {j : ℕ} {α : List (Label P maxRegObj)} {C : Config maxRegObj (RegFamily ι V v₀) P S}
    {reg : Fin j → ι} (hst : Stage I w q k j α C reg) (hj : j < k) :
    ∃ α' C' reg', Stage I w q k (j + 1) α' C' reg' := by
  classical
  obtain ⟨hCp, hαp⟩ := hst.idle j le_rfl hj
  set p := w j with hp
  have hpne : ∀ i < j, w i ≠ p := fun i hi h => by
    have := hwinj i (by omega) j hj h; omega
  have hqp : q ≠ p := fun h => hwq j hj h.symm
  have hEα : WriterExec W α := fun x v hv => by
    obtain ⟨i, hi, rfl, -⟩ := hst.ops x _ hv; exact hW i (by omega)
  -- `p` invokes `writeMax (j+1)`
  obtain ⟨C₁, hs⟩ : ∃ C₁, I.step C (.inv p (.writeMax (j + 1))) = some C₁ := by
    have hallp : I.allowed p (.writeMax (j + 1)) := hallw j hj _
    simp [Impl.step, hCp, hallp]
  obtain ⟨-, -, hC₁pend, hC₁loc, hC₁mem⟩ := step_inv hs
  have hC₁p : C₁.pend p ≠ none := by simp [hC₁pend]
  have hrun₁ : I.run (α ++ [.inv p (.writeMax (j + 1))]) = some C₁ := by
    rw [run_append_of_eq I hst.run, runFrom_singleton, hs]
  have hE₁ : WriterExec W (α ++ [.inv p (.writeMax (j + 1))]) := fun x v hv => by
    simp only [opsOf_append, opsOf_cons, opsOf_nil, List.append_nil, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hEα x v hv
    · by_cases hx : x = p
      · rw [hx]; exact hW j hj
      · simp [Label.invOf, Ne.symm hx] at hv
  obtain ⟨K, hK⟩ := hof _ C₁ p hrun₁ hE₁ hC₁p
  -- run `p` solo until it returns or is about to write outside the covered registers
  let Q : Action maxRegObj (RegFamily ι V v₀) S → Prop := fun a =>
    ∃ i o κ, a = .access i o κ ∧ (RegFamily ι V v₀ i).Overwrites o ∧ i ∉ Set.range reg
  obtain ⟨m, hbefore, hend⟩ := I.exists_solo_until p C₁ Q ⟨K, hK⟩
  set D := (I.soloStep p)^[m] C₁ with hD
  have hother : ∀ x, x ≠ p → D.loc x = C.loc x ∧ D.pend x = C.pend x := fun x hx => by
    obtain ⟨h1, h2⟩ := iterate_soloStep_other (I := I) hx C₁ m
    obtain ⟨h3, h4⟩ := step_other hs (q := x) (Ne.symm hx)
    exact ⟨h1.trans h3, h2.trans h4⟩
  have hrunD : I.run (α ++ [.inv p (.writeMax (j + 1))] ++ I.soloLabels p C₁ m) = some D := by
    rw [run_append_of_eq I hrun₁, runFrom_soloLabels]
  have hopsD : ∀ x, opsOf (α ++ [.inv p (.writeMax (j + 1))] ++ I.soloLabels p C₁ m) x =
      opsOf α x ++ (if x = p then [.writeMax (j + 1)] else []) := fun x => by
    by_cases hx : x = p
    · subst hx; simp [opsOf_soloLabels, Label.invOf]
    · simp [opsOf_soloLabels, Label.invOf, hx, Ne.symm hx]
  by_cases hDp : D.pend p = none
  · -- `p` returned: contradiction
    exfalso
    -- `p` wrote only inside the covered registers
    have hmemD : ∀ i ∉ Set.range reg, D.mem i = C.mem i := by
      intro i hi
      rw [hD, I.iterate_soloStep_mem_of_readOnly p C₁ (Set.range reg) m
        (fun j' hj' i' o' κ' hact hi' => ?_) i hi, hC₁mem]
      rcases regFamily_readOnly_or_overwrites i' o' with h | h
      · exact h
      · exact absurd ⟨i', o', κ', hact, h, hi'⟩ (hbefore j' hj').2
    -- block write by `w 0, …, w (j-1)` from `C` and from `D`
    let cs : List (P × ι) := List.ofFn fun i : Fin j => (w i, reg i)
    have hcsfst : cs.map Prod.fst = List.ofFn fun i : Fin j => w i := by
      simp [cs, List.map_ofFn, Function.comp_def]
    have hcssnd : cs.map Prod.snd = List.ofFn reg := by simp [cs, List.map_ofFn]; rfl
    have hnd : (cs.map Prod.fst).Nodup := by
      rw [hcsfst, List.nodup_ofFn]
      intro a b hab
      exact Fin.ext (hwinj a (by omega) b (by omega) hab)
    have hmemcs : ∀ c ∈ cs, ∃ i : Fin j, c = (w i, reg i) := fun c hc => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc; exact ⟨i, rfl⟩
    obtain ⟨C₂, D₂, hC₂, hD₂, hag⟩ := blockWrite_agreeOn (I := I) (Q := {x | x ≠ p}) hnd
      (fun c hc => by obtain ⟨i, rfl⟩ := hmemcs c hc; exact hpne i i.2)
      (fun c hc => by obtain ⟨i, rfl⟩ := hmemcs c hc; exact hst.cov i)
      (fun x hx => (hother x hx).1.symm) (fun x hx => (hother x hx).2.symm)
      (fun i hi => by
        refine (hmemD i fun ⟨i', hi'⟩ => hi ?_).symm
        rw [hcssnd, List.mem_ofFn]; exact ⟨i', hi'⟩)
    set bw : List (Label P maxRegObj) := blockWrite (cs.map Prod.fst) with hbw
    have hbwproc : ∀ ℓ ∈ bw, ∃ i < j, ℓ.proc = w i := fun ℓ hℓ => by
      have := mem_blockWrite hℓ
      rw [hcsfst, List.mem_ofFn] at this
      obtain ⟨i, hi⟩ := this; exact ⟨i, i.2, hi.symm⟩
    have hbwq : ∀ ℓ ∈ bw, ℓ.proc ≠ q := fun ℓ hℓ => by
      obtain ⟨i, hi, h⟩ := hbwproc ℓ hℓ; rw [h]; exact hwq i (by omega)
    have hbwp : ∀ ℓ ∈ bw, ℓ.proc ≠ p := fun ℓ hℓ => by
      obtain ⟨i, hi, h⟩ := hbwproc ℓ hℓ; rw [h]; exact hpne i hi
    have hbwops : ∀ x, opsOf bw x = [] := fun x => opsOf_blockWrite _ _
    have hbwresps : ∀ x, respsOf bw x = [] := fun x => respsOf_blockWrite _ _
    have hC₂q : C₂.pend q = none := (I.runFrom_other hC₂ hbwq).2.trans hst.qidle.1
    have hrun₂ : I.run (α ++ bw) = some C₂ := by rw [run_append_of_eq I hst.run, hC₂]
    -- `q` reads solo after the block write
    have hE₂ : WriterExec W (α ++ bw ++ [.inv q .readMax]) := fun x v hv => by
      by_cases hx : x = q
      · subst hx; simp [Label.invOf, hst.qidle.2, hbwops] at hv
      · simp [Label.invOf, Ne.symm hx, hbwops] at hv; exact hEα x v hv
    obtain ⟨C₃, n, hs₃, hn, hδ⟩ :=
      exists_soloOp_of_obstructionFreeOn I hof q .readMax hallq hrun₂ hC₂q hE₂
    set δ : List (Label P maxRegObj) := .inv q .readMax :: I.soloLabels q C₃ n with hδdef
    have hδq : ∀ ℓ ∈ δ, ℓ.proc = q := fun ℓ hℓ => by
      rcases List.mem_cons.1 hℓ with rfl | hℓ
      · rfl
      · exact I.soloLabels_proc q C₃ n ℓ hℓ
    obtain ⟨D₄, hD₄, -⟩ := runFrom_agreeOn hag (fun ℓ hℓ => by
      show ℓ.proc ≠ p; rw [hδq ℓ hℓ]; exact hqp) hδ
    -- the two executions
    set α₂ := α ++ bw ++ δ with hα₂
    set α₁ := α ++ [.inv p (.writeMax (j + 1))] ++ I.soloLabels p C₁ m ++ bw ++ δ with hα₁
    have hrunα₂ : I.run α₂ = some ((I.soloStep q)^[n] C₃) := by
      rw [hα₂, run_append_of_eq I hrun₂, hδ]
    have hrunα₁ : I.run α₁ = some D₄ := by
      rw [hα₁, List.append_assoc _ bw δ, run_append_of_eq I hrunD, runFrom_append_of_eq I hD₂,
        hD₄]
    -- invocations and responses
    have hδops : ∀ x, opsOf δ x = if x = q then [.readMax] else [] := fun x => by
      by_cases hx : x = q
      · subst hx; simp [hδdef, opsOf_soloLabels, Label.invOf]
      · simp [hδdef, opsOf_soloLabels, Label.invOf, hx, Ne.symm hx]
    have hαq : respsOf α q = [] := by
      have := I.run_resps_le_ops hst.run q
      rw [hst.qidle.2] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this)
    have hsoloq : respsOf (I.soloLabels p C₁ m) q = [] :=
      respsOf_eq_nil_of_proc_ne fun ℓ hℓ => by
        rw [I.soloLabels_proc p C₁ m ℓ hℓ]; exact Ne.symm hqp
    have hops₂ : ∀ x, opsOf α₂ x = opsOf α x ++ if x = q then [.readMax] else [] := fun x => by
      simp [hα₂, hbwops, hδops]
    have hops₁ : ∀ x, opsOf α₁ x = opsOf α x ++ (if x = p then [.writeMax (j + 1)] else []) ++
        if x = q then [.readMax] else [] := fun x => by
      rw [hα₁, opsOf_append, opsOf_append, hopsD, hbwops, hδops, List.append_nil]
    have hresps₂ : respsOf α₂ q = respsOf δ q := by simp [hα₂, hαq, hbwresps]
    have hresps₁ : respsOf α₁ q = respsOf δ q := by
      simp [hα₁, hαq, hbwresps, hsoloq, Label.retOf]
    obtain ⟨r, hr⟩ : ∃ r, respsOf δ q = [r] := by
      have := I.run_idle_counts hrunα₂ hn
      rw [hops₂, hresps₂, hst.qidle.2] at this
      exact List.length_eq_one_iff.1 (by simpa using this.symm)
    -- writer-execution property
    have hE₂' : WriterExec W α₂ := fun x v hv => by
      rw [hops₂] at hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hEα x v hv
      · split_ifs at hv <;> simp at hv
    have hE₁' : WriterExec W α₁ := fun x v hv => by
      rw [hops₁] at hv
      simp only [List.mem_append] at hv
      rcases hv with (hv | hv) | hv
      · exact hEα x v hv
      · split_ifs at hv with hx
        · rw [hx]; exact hW j hj
        · simp at hv
      · split_ifs at hv <;> simp at hv
    -- second execution: only values `≤ j` are written, so the read returns `≤ j`
    obtain ⟨Λ₂, hΛ₂⟩ := hlin α₂ ⟨_, hrunα₂⟩ hE₂'
    have hle : r ≤ j := by
      refine resp_le_of_ops hΛ₂ (b := (q, 0)) (fun x v hv => ?_) ?_ ?_
      · rw [hops₂] at hv
        rcases List.mem_append.1 hv with hv | hv
        · obtain ⟨i, hi, -, hvi⟩ := hst.ops x _ hv
          cases hvi; omega
        · split_ifs at hv <;> simp at hv
      · simp [opOf, hops₂, hst.qidle.2]
      · simp [respOf, hresps₂, hr]
    -- first execution: `writeMax (j+1)` precedes the read, so the read returns `≥ j+1`
    obtain ⟨Λ₁, hΛ₁⟩ := hlin α₁ ⟨_, hrunα₁⟩ hE₁'
    have hge : j + 1 ≤ r := by
      refine le_resp_of_precedes hΛ₁ (a := (p, 0)) (b := (q, 0)) ?_ ?_ ?_ ?_
      · simp [opOf, hops₁, hαp, Ne.symm hqp]
      · simp [opOf, hops₁, hst.qidle.2, hqp]
      · simp [respOf, hresps₁, hr]
      · refine ⟨α ++ [.inv p (.writeMax (j + 1))] ++ I.soloLabels p C₁ m, bw ++ δ,
          by simp [hα₁], ?_, ?_⟩
        · have := I.run_idle_counts hrunD hDp
          simp only [Completed]
          rw [← this, hopsD, hαp]; simp
        · simp only [Invoked, hopsD, hst.qidle.2]; simp [hqp]
    exact Nat.not_succ_le_self j (hge.trans hle)
  · -- `p` covers a new register
    obtain ⟨i₀, o, κ, hact, hov, hi₀⟩ := hend.resolve_left hDp
    refine ⟨_, D, Fin.snoc (α := fun _ => ι) reg i₀, hrunD, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.val_last]
        exact ⟨hDp, o, κ, hact, hov⟩
      | cast i =>
        have h := hother (w i) (hpne i i.2)
        simpa using (hst.cov i).congr h.1.symm h.2.symm
    · intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b => simp at hab; exact absurd ⟨b, hab.symm⟩ hi₀
      | cast a =>
        induction b using Fin.lastCases with
        | last => simp at hab; exact absurd ⟨a, hab⟩ hi₀
        | cast b => simp at hab; rw [hst.inj hab]
    · intro i hi hik
      have hip : w i ≠ p := fun h => by have := hwinj i hik j hj h; omega
      refine ⟨(hother _ hip).2.trans (hst.idle i (by omega) hik).1, ?_⟩
      rw [hopsD, (hst.idle i (by omega) hik).2]; simp [hip]
    · refine ⟨(hother _ hqp).2.trans hst.qidle.1, ?_⟩
      rw [hopsD, hst.qidle.2]; simp [hqp]
    · intro x o' ho'
      rw [hopsD] at ho'
      rcases List.mem_append.1 ho' with ho' | ho'
      · obtain ⟨i, hi, rfl, rfl⟩ := hst.ops x o' ho'
        exact ⟨i, by omega, rfl, rfl⟩
      · by_cases hx : x = p
        · simp [hx] at ho'; exact ⟨j, by omega, hx, ho'⟩
        · simp [hx] at ho'

/-- All stages `j ≤ k` of the covering construction exist; in particular `k` writers cover `k`
distinct registers. -/
theorem exists_stage (hwinj : ∀ i < k, ∀ i' < k, w i = w i' → i = i')
    (hwq : ∀ i < k, w i ≠ q) (hW : ∀ i < k, w i ∈ W)
    (hallw : ∀ i < k, ∀ v, I.allowed (w i) (.writeMax v)) (hallq : I.allowed q .readMax)
    (hlin : ∀ α, I.Valid α → WriterExec W α → ∃ Λ, IsLinearization α Λ)
    (hof : I.ObstructionFreeOn (WriterExec W)) :
    ∀ j ≤ k, ∃ α C reg, Stage I w q k j α C reg := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨_, _, _, stage_zero⟩
  | succ j ih =>
    intro hj
    obtain ⟨α, C, reg, h⟩ := ih (by omega)
    exact h.succ hwinj hwq hW hallw hallq hlin hof (by omega)

end Construction

/-! ### Theorem 2 -/

section Main

variable {ι V : Type} {v₀ : V} {P S : Type} [DecidableEq P] [DecidableEq ι]

/-- **Theorem 2 of [CS17]** (Resource complexity of `k`-max-register): any algorithm implementing
a `k`-writer max-register from MWMR atomic registers uses at least `k` registers.

Model: asynchronous shared memory, processes `P`, base objects `RegFamily ι V v₀` (atomic
multi-writer multi-reader read/write registers over an arbitrary value type `V`); `I` implements
the max register `maxRegObj` (over `ℕ`). The writers `w 0, …, w (k-1)` are distinct processes
allowed to invoke `writeMax`, and `q` is a further process allowed to invoke `readMax`.

Hypotheses are only required on **`k`-writer executions** (`WriterExec (Set.range w)`: every
`writeMax` is invoked by a writer): linearizability of every such execution, and
obstruction-freedom from every configuration such an execution reaches. This is weaker than the
paper's wait-freedom (see `theorem2_of_waitFree`).

Proof: directly, by a covering argument (the paper instead reduces to its fault-tolerant
Theorem 1 via `2f + 1` copies and multi-writer ABD); see the module docstring. -/
theorem theorem2 [Fintype ι] {k : ℕ} (I : Impl maxRegObj (RegFamily ι V v₀) P S)
    (w : Fin k → P) (hw : Function.Injective w) (q : P) (hq : ∀ i, w i ≠ q)
    (hallw : ∀ i v, I.allowed (w i) (.writeMax v)) (hallq : I.allowed q .readMax)
    (hlin : ∀ α, I.Valid α → WriterExec (Set.range w) α → ∃ Λ, IsLinearization α Λ)
    (hof : I.ObstructionFreeOn (WriterExec (Set.range w))) :
    k ≤ Fintype.card ι := by
  classical
  let w' : ℕ → P := fun i => if h : i < k then w ⟨i, h⟩ else q
  have hw' : ∀ i (h : i < k), w' i = w ⟨i, h⟩ := fun i h => dite_eq_left h
  obtain ⟨α, C, reg, hst⟩ := exists_stage (I := I) (w := w') (q := q) (k := k)
    (W := Set.range w)
    (fun i hi i' hi' h => by
      rw [hw' i hi, hw' i' hi'] at h; exact congrArg Fin.val (hw h))
    (fun i hi => by rw [hw' i hi]; exact hq _)
    (fun i hi => by rw [hw' i hi]; exact ⟨_, rfl⟩)
    (fun i hi v => by rw [hw' i hi]; exact hallw _ v) hallq hlin hof k le_rfl
  simpa using Fintype.card_le_of_injective reg hst.inj

/-- Theorem 2 of [CS17] as stated in the paper: a linearizable wait-free `k`-writer
max-register implementation from MWMR registers uses at least `k` registers. -/
theorem theorem2_of_waitFree [Fintype ι] {k : ℕ} (I : Impl maxRegObj (RegFamily ι V v₀) P S)
    (w : Fin k → P) (hw : Function.Injective w) (q : P) (hq : ∀ i, w i ≠ q)
    (hallw : ∀ i v, I.allowed (w i) (.writeMax v)) (hallq : I.allowed q .readMax)
    (hlin : I.Linearizable) (hwf : I.WaitFree) :
    k ≤ Fintype.card ι := by
  obtain ⟨h, hh⟩ := hlin
  exact theorem2 I w hw q hq hallw hallq (fun α hα _ => ⟨h α, hh α hα⟩)
    (hwf.obstructionFree.obstructionFreeOn _)

end Main

end Podc.RegisterEmulationSpace.MaxRegLB
