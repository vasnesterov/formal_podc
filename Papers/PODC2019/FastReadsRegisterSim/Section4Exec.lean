import Papers.PODC2019.FastReadsRegisterSim.Exec4
import Papers.PODC2019.FastReadsRegisterSim.LinFacts

/-!
# Section 4: the executions

`wRun I w ws` runs the writes `ws` of `w` one after the other, each solo to completion, from the
initial configuration. `WPre I w β C ws k` collects what we need about a prefix `β` of the writer's
execution (reaching `C`): only `w` moves, `w` invoked the writes `ws`, the first `k` of them
returned, and every other process is still in its initial state. Complete first reads of one or
two readers can be appended (`one_block`, `two_blocks`), and the read of a reader that starts in a
quiescent configuration returns the last written value (`quiescent_val`).
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι P L : Type} [DecidableEq P] [DecidableEq ι]

namespace Sec4

variable (I : Sim V v₀ ι P L) (w : P)

/-- The writes `ws` of `w`, each run solo to completion, from the initial configuration: labels
and final configuration. -/
noncomputable def wRun (ws : List V) :
    List (Label P (register V v₀)) × Config (register V v₀) (BinRegs ι) P L :=
  ws.foldl (fun x v => (x.1 ++ I.opLabels w x.2 (.write v), I.opCfg w x.2 (.write v)))
    ([], I.initCfg)

lemma wRun_nil : wRun I w [] = ([], I.initCfg) := rfl

lemma wRun_concat (ws : List V) (v : V) :
    wRun I w (ws ++ [v]) = ((wRun I w ws).1 ++ I.opLabels w (wRun I w ws).2 (.write v),
      I.opCfg w (wRun I w ws).2 (.write v)) := by
  simp [wRun, List.foldl_append]

/-- A prefix `β` of an execution of the writer alone, reaching `C`, in which `w` invoked the
writes `ws` and the first `k` of them returned. -/
structure WPre (β : List (Label P (register V v₀))) (C : Config (register V v₀) (BinRegs ι) P L)
    (ws : List V) (k : ℕ) : Prop where
  run : I.run β = some C
  procs : ∀ ℓ ∈ β, ℓ.proc = w
  ops : opsOf β w = ws.map .write
  resps : k ≤ (respsOf β w).length
  idle : ∀ q, q ≠ w → C.loc q = I.locInit q ∧ C.pend q = none
  wpend : C.pend w = none ∨ k < ws.length

variable {I w}

lemma wpre_wRun (hw : ∀ v, I.allowed w (.write v)) (hof : I.ObstructionFree) (ws : List V) :
    WPre I w (wRun I w ws).1 (wRun I w ws).2 ws ws.length ∧ (wRun I w ws).2.pend w = none := by
  induction ws using List.reverseRecOn with
  | nil => exact ⟨⟨rfl, by simp [wRun_nil], by simp [wRun_nil], by simp,
      fun q _ => ⟨rfl, rfl⟩, Or.inl rfl⟩, rfl⟩
  | append_singleton ws v ih =>
    obtain ⟨h, hpw⟩ := ih
    have hreach : I.Reachable (wRun I w ws).2 := ⟨_, h.run⟩
    have hrun := Sim.runFrom_opLabels hof hreach hpw (hw v)
    rw [wRun_concat]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, Or.inl (by simp)⟩, by simp⟩
    · rw [Impl.run_append_of_eq I h.run, hrun]
    · intro ℓ hℓ
      rcases List.mem_append.1 hℓ with hℓ | hℓ
      · exact h.procs ℓ hℓ
      · simp only [Sim.opLabels, List.mem_cons, List.mem_append, List.mem_replicate,
          List.not_mem_nil, or_false] at hℓ
        rcases hℓ with rfl | ⟨-, rfl⟩ | rfl <;> rfl
    · simp [opsOf_append, h.ops, opsOf_opLabels]
    · simp [respsOf_append, respsOf_opLabels]; have := h.resps; omega
    · intro q hq
      dsimp only
      rw [Sim.opCfg_loc_ne _ _ hq, Sim.opCfg_pend_ne _ _ hq]
      exact h.idle q hq

/-- The configuration after `t` steps of the write of `v` that follows the writes `ws`. -/
noncomputable def wPart (I : Sim V v₀ ι P L) (w : P) (ws : List V) (v : V) (t : ℕ) :
    Config (register V v₀) (BinRegs ι) P L :=
  I.soloCfg w (I.invCfg (wRun I w ws).2 w (.write v)) t

/-- Number of steps of the write of `v` that follows the writes `ws`. -/
noncomputable abbrev wT (I : Sim V v₀ ι P L) (w : P) (ws : List V) (v : V) : ℕ :=
  I.retTime w (wRun I w ws).2 (.write v)

/-- The memory after `t` steps of the write of `v` that follows the writes `ws`. -/
noncomputable def wMem (I : Sim V v₀ ι P L) (w : P) (ws : List V) (v : V) (t : ℕ) : Mem ι :=
  (wPart I w ws v t).mem

lemma wMem_zero (ws : List V) (v : V) : wMem I w ws v 0 = (wRun I w ws).2.mem := by
  simp [wMem, wPart, Sim.soloCfg]

lemma wMem_T (ws : List V) (v : V) :
    wMem I w ws v (wT I w ws v) = (wRun I w (ws ++ [v])).2.mem := by
  rw [wRun_concat]; simp [wMem, wPart, Sim.opCfg_mem, Sim.soloCfg]

lemma wMem_succ (ws : List V) (v : V) (t : ℕ) :
    wMem I w ws v (t + 1) = (lstep (I.act w)
      (lrun (I.act w) t (I.invoke w ((wRun I w ws).2.loc w) (.write v), (wRun I w ws).2.mem))).2 := by
  simp [wMem, wPart, Sim.soloCfg, lrun_succ]

lemma wMem_eq_lrun (ws : List V) (v : V) (t : ℕ) :
    wMem I w ws v t = (lrun (I.act w) t
      (I.invoke w ((wRun I w ws).2.loc w) (.write v), (wRun I w ws).2.mem)).2 := by
  simp [wMem, wPart, Sim.soloCfg]

/-- One step of the writer changes at most one register. -/
lemma wMem_succ_eq_of_ne (ws : List V) (v : V) (t : ℕ) {i j : ι} (hij : i ≠ j)
    (hi : wMem I w ws v (t + 1) i ≠ wMem I w ws v t i) :
    wMem I w ws v (t + 1) j = wMem I w ws v t j := by
  rw [wMem_succ, wMem_eq_lrun] at *
  exact lstep_mem_eq_of_ne hij hi

lemma wpre_part (hw : ∀ v, I.allowed w (.write v)) (hof : I.ObstructionFree) (ws : List V)
    (v : V) {t : ℕ} (ht : t ≤ wT I w ws v) :
    WPre I w ((wRun I w ws).1 ++ .inv w (.write v) :: List.replicate t (.tau w))
      (wPart I w ws v t) (ws ++ [v]) ws.length := by
  obtain ⟨h, hpw⟩ := wpre_wRun hw hof ws
  have hreach : I.Reachable (wRun I w ws).2 := ⟨_, h.run⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr (by simp)⟩
  · rw [Impl.run_append_of_eq I h.run]
    exact Sim.runFrom_opLabels_take hof hreach hpw (hw v) ht
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact h.procs ℓ hℓ
    · simp only [List.mem_cons, List.mem_replicate] at hℓ
      rcases hℓ with rfl | ⟨-, rfl⟩ <;> rfl
  · simp [opsOf_append, h.ops, opsOf_replicate_tau]
  · simp [respsOf_append, respsOf_replicate_tau]; exact h.resps
  · intro q hq
    simp only [wPart, Sim.soloCfg_pend]
    rw [Sim.soloCfg_loc_ne _ _ hq]
    simp only [Sim.invCfg, Function.update_of_ne hq]
    exact h.idle q hq

/-! ## Appending complete reads -/

variable {r rA rB : P} {m : ℕ}

lemma opsOf_wpre_ne {β : List (Label P (register V v₀))} {C} {ws : List V} {k : ℕ}
    (h : WPre I w β C ws k) {q : P} (hq : q ≠ w) : opsOf β q = [] :=
  opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [h.procs ℓ hℓ]; exact Ne.symm hq)

lemma respsOf_wpre_ne {β : List (Label P (register V v₀))} {C} {ws : List V} {k : ℕ}
    (h : WPre I w β C ws k) {q : P} (hq : q ≠ w) : respsOf β q = [] :=
  respsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [h.procs ℓ hℓ]; exact Ne.symm hq)

/-- A complete first read of `r` appended to a writer prefix. -/
lemma one_block (hT : TreeHyp I r m) (hr : I.allowed r .read) (hrw : r ≠ w)
    {β : List (Label P (register V v₀))} {C} {ws : List V} {k : ℕ} (h : WPre I w β C ws k) :
    I.Valid (β ++ readBlock I r m C.mem) ∧
      opsOf (β ++ readBlock I r m C.mem) w = ws.map .write ∧
      (∀ q, q ≠ w → ∀ o ∈ opsOf (β ++ readBlock I r m C.mem) q, o = .read) ∧
      ReadReturns v₀ (β ++ readBlock I r m C.mem) (r, 0) (vl I r (pth I r C.mem m)) ∧
      ∀ j < k, Precedes (β ++ readBlock I r m C.mem) (w, j) (r, 0) := by
  obtain ⟨hidl, hidp⟩ := h.idle r hrw
  obtain ⟨l, hl⟩ := runFrom_readBlock hT hr hidp hidl
  refine ⟨⟨_, by rw [Impl.run_append_of_eq I h.run, hl]⟩, ?_, ?_, ?_, ?_⟩
  · simp [opsOf_append, h.ops, opsOf_readBlock, hrw]
  · intro q hq o ho
    simp only [opsOf_append, opsOf_wpre_ne h hq, opsOf_readBlock, List.nil_append] at ho
    split_ifs at ho <;> simp_all
  · constructor
    · simp [opOf, opsOf_append, opsOf_wpre_ne h hrw, opsOf_readBlock]
    · simp [respOf, respsOf_append, respsOf_wpre_ne h hrw, respsOf_readBlock]
  · intro j hj
    refine ⟨β, readBlock I r m C.mem, rfl, ?_, ?_⟩
    · simp only [Completed]; have := h.resps; omega
    · simp [Invoked, opsOf_wpre_ne h hrw]

/-- Complete first reads of `rA` and then `rB` appended to a writer prefix. -/
lemma two_blocks (hTA : TreeHyp I rA m) (hTB : TreeHyp I rB m) (hrA : I.allowed rA .read)
    (hrB : I.allowed rB .read) (hAw : rA ≠ w) (hBw : rB ≠ w) (hAB : rA ≠ rB)
    {β : List (Label P (register V v₀))} {C} {ws : List V} {k : ℕ} (h : WPre I w β C ws k) :
    let α := β ++ readBlock I rA m C.mem ++ readBlock I rB m C.mem
    I.Valid α ∧ opsOf α w = ws.map .write ∧
      (∀ q, q ≠ w → ∀ o ∈ opsOf α q, o = .read) ∧
      ReadReturns v₀ α (rA, 0) (vl I rA (pth I rA C.mem m)) ∧
      ReadReturns v₀ α (rB, 0) (vl I rB (pth I rB C.mem m)) ∧
      Precedes α (rA, 0) (rB, 0) ∧ ∀ j < k, Precedes α (w, j) (rA, 0) := by
  intro α
  obtain ⟨hidlA, hidpA⟩ := h.idle rA hAw
  obtain ⟨hidlB, hidpB⟩ := h.idle rB hBw
  obtain ⟨lA, hlA⟩ := runFrom_readBlock hTA hrA hidpA hidlA
  obtain ⟨lB, hlB⟩ := runFrom_readBlock hTB hrB (C := rcfg C rA lA none)
    (by rw [rcfg_pend_ne _ _ _ (Ne.symm hAB)]; exact hidpB)
    (by rw [rcfg_loc_ne _ _ _ (Ne.symm hAB)]; exact hidlB)
  have hBA : rB ≠ rA := Ne.symm hAB
  rw [rcfg_mem] at hlB
  refine ⟨⟨rcfg (rcfg C rA lA none) rB lB none, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [α]
    rw [Impl.run_append_of_eq I (by rw [Impl.run_append_of_eq I h.run, hlA]), hlB]
  · simp [α, opsOf_append, h.ops, opsOf_readBlock, hAw, hBw]
  · intro q hq o ho
    simp only [α, opsOf_append, opsOf_wpre_ne h hq, opsOf_readBlock, List.nil_append] at ho
    split_ifs at ho <;> simp_all
  · constructor
    · simp [α, opOf, opsOf_append, opsOf_wpre_ne h hAw, opsOf_readBlock]
    · simp [α, respOf, respsOf_append, respsOf_wpre_ne h hAw, respsOf_readBlock]
  · constructor
    · simp [α, opOf, opsOf_append, opsOf_wpre_ne h hBw, opsOf_readBlock, hAB]
    · simp [α, respOf, respsOf_append, respsOf_wpre_ne h hBw, respsOf_readBlock, hAB]
  · refine ⟨β ++ readBlock I rA m C.mem, readBlock I rB m C.mem, rfl, ?_, ?_⟩
    · simp [Completed, respsOf_append, respsOf_wpre_ne h hAw, respsOf_readBlock]
    · simp [Invoked, opsOf_append, opsOf_wpre_ne h hBw, opsOf_readBlock, hAB]
  · intro j hj
    refine ⟨β, readBlock I rA m C.mem ++ readBlock I rB m C.mem, by simp [α], ?_, ?_⟩
    · simp only [Completed]; have := h.resps; omega
    · simp [Invoked, opsOf_wpre_ne h hAw]

/-- **A read split around writer steps, followed by a second read.** `r₁` performs all but the
last step of its first read at the end of the writer prefix `β₁` (memory `C₁.mem`), the writer
continues with `γ`, then `r₁` performs its last step (at memory `D.mem`) and returns, and then `r₂`
performs a complete first read. -/
lemma split_two {r₁ r₂ : P} (hT₁ : TreeHyp I r₁ m) (hT₂ : TreeHyp I r₂ m)
    (hr₁ : I.allowed r₁ .read) (hr₂ : I.allowed r₂ .read) (h1w : r₁ ≠ w) (h2w : r₂ ≠ w)
    (h12 : r₁ ≠ r₂) (hm : 1 ≤ m)
    {β₁ : List (Label P (register V v₀))} {C₁} {ws₁ : List V} {k₁ : ℕ} (h₁ : WPre I w β₁ C₁ ws₁ k₁)
    {γ : List (Label P (register V v₀))} {D} {ws₂ : List V} {k₂ : ℕ}
    (h₂ : WPre I w (β₁ ++ γ) D ws₂ k₂) :
    let u := pth I r₁ C₁.mem (m - 1)
    let v₁ := vl I r₁ (u ++ [bit (I.act r₁) D.mem (nd I r₁ u)])
    let α := β₁ ++ (.inv r₁ .read :: List.replicate (m - 1) (.tau r₁)) ++ γ ++
      [.tau r₁, .ret r₁ v₁] ++ readBlock I r₂ m D.mem
    I.Valid α ∧ opsOf α w = ws₂.map .write ∧
      (∀ q, q ≠ w → ∀ o ∈ opsOf α q, o = .read) ∧
      ReadReturns v₀ α (r₁, 0) v₁ ∧
      ReadReturns v₀ α (r₂, 0) (vl I r₂ (pth I r₂ D.mem m)) ∧
      Precedes α (r₁, 0) (r₂, 0) ∧ ∀ j < k₁, Precedes α (w, j) (r₁, 0) := by
  intro u v₁ α
  obtain ⟨hl1, hp1⟩ := h₁.idle r₁ h1w
  obtain ⟨hl2, hp2⟩ := h₂.idle r₂ h2w
  have hγp : ∀ ℓ ∈ γ, ℓ.proc = w := fun ℓ hℓ => h₂.procs ℓ (List.mem_append_right _ hℓ)
  have hγ : I.runFrom C₁ γ = some D := by
    have := h₂.run; rwa [Impl.run_append_of_eq I h₁.run] at this
  have hγops : ∀ q, q ≠ w → opsOf γ q = [] := fun q hq =>
    opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hγp ℓ hℓ]; exact Ne.symm hq)
  have hγresps : ∀ q, q ≠ w → respsOf γ q = [] := fun q hq =>
    respsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hγp ℓ hℓ]; exact Ne.symm hq)
  -- validity
  have e1 := runFrom_invTaus hT₁ hr₁ hp1 hl1 (j := m - 1) (by omega)
  have e2 := runFrom_rcfg I (fun ℓ hℓ => by rw [hγp ℓ hℓ]; exact Ne.symm h1w) hγ
    (nd I r₁ (pth I r₁ C₁.mem (m - 1))) (some .read)
  have e3 := step_tau_node hT₁ (D := rcfg D r₁ (nd I r₁ u) (some .read)) (u := u) (by simp)
    (by simp [u]; omega) (by simp)
  obtain ⟨l', e4⟩ := step_ret_node hT₁
    (D := rcfg (rcfg D r₁ (nd I r₁ u) (some .read)) r₁
      (nd I r₁ (u ++ [bit (I.act r₁) D.mem (nd I r₁ u)])) (some .read))
    (u := u ++ [bit (I.act r₁) D.mem (nd I r₁ u)]) (by simp) (by simp [u]; omega) (by simp)
  obtain ⟨l₂, e5⟩ := runFrom_readBlock hT₂ hr₂ (C := rcfg D r₁ l' none)
    (by rw [rcfg_pend_ne _ _ _ (Ne.symm h12)]; exact hp2)
    (by rw [rcfg_loc_ne _ _ _ (Ne.symm h12)]; exact hl2)
  rw [rcfg_mem] at e5
  have hrun : I.run α = some (rcfg (rcfg D r₁ l' none) r₂ l₂ none) := by
    simp only [α]
    rw [Impl.run_append_of_eq I (C := rcfg D r₁ l' none), e5]
    rw [Impl.run_append_of_eq I (C := rcfg D r₁ (nd I r₁ u) (some .read))]
    · rw [Impl.runFrom_cons, e3, Option.bind_some, Impl.runFrom_singleton]
      simpa using e4
    · rw [Impl.run_append_of_eq I (by rw [Impl.run_append_of_eq I h₁.run, e1]), e2]
  have hβ1 : ∀ q, q ≠ w → opsOf β₁ q = [] := fun q hq => opsOf_wpre_ne h₁ hq
  have hβ1r : ∀ q, q ≠ w → respsOf β₁ q = [] := fun q hq => respsOf_wpre_ne h₁ hq
  have hops2 : opsOf β₁ w ++ opsOf γ w = ws₂.map .write := by
    rw [← opsOf_append]; exact h₂.ops
  refine ⟨⟨_, hrun⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [α, opsOf_append, opsOf_readBlock, opsOf_replicate_tau, h1w, h2w, ← hops2]
  · intro q hq o ho
    simp only [α, opsOf_append, hβ1 q hq, hγops q hq, opsOf_readBlock, opsOf_cons,
      opsOf_replicate_tau, Label.invOf_inv, Label.invOf_tau, Label.invOf_ret, opsOf_nil] at ho
    split_ifs at ho <;> simp_all
  · constructor
    · simp [α, opOf, opsOf_append, hβ1 r₁ h1w, hγops r₁ h1w, opsOf_readBlock,
        opsOf_replicate_tau]
    · simp [α, respOf, respsOf_append, hβ1r r₁ h1w, hγresps r₁ h1w, respsOf_readBlock,
        respsOf_replicate_tau]
  · constructor
    · simp [α, opOf, opsOf_append, hβ1 r₂ h2w, hγops r₂ h2w, opsOf_readBlock,
        opsOf_replicate_tau, h12]
    · simp [α, respOf, respsOf_append, hβ1r r₂ h2w, hγresps r₂ h2w, respsOf_readBlock,
        respsOf_replicate_tau, h12]
  · refine ⟨β₁ ++ (.inv r₁ .read :: List.replicate (m - 1) (.tau r₁)) ++ γ ++
      [.tau r₁, .ret r₁ v₁], readBlock I r₂ m D.mem, rfl, ?_, ?_⟩
    · simp [Completed, respsOf_append, hβ1r r₁ h1w, hγresps r₁ h1w, respsOf_replicate_tau]
    · simp [Invoked, opsOf_append, hβ1 r₂ h2w, hγops r₂ h2w, opsOf_replicate_tau, h12]
  · intro j hj
    refine ⟨β₁, (.inv r₁ .read :: List.replicate (m - 1) (.tau r₁)) ++ γ ++
      [.tau r₁, .ret r₁ v₁] ++ readBlock I r₂ m D.mem, by simp [α], ?_, ?_⟩
    · simp only [Completed]; have := h₁.resps; omega
    · simp [Invoked, hβ1 r₁ h1w]

/-- **Quiescent reads** (atomicity, hence safety): a first read starting after all writes `ws`
returned returns the last written value. -/
lemma quiescent_val (hatom : I.Atomic w) (hT : TreeHyp I r m) (hr : I.allowed r .read)
    (hrw : r ≠ w) {β : List (Label P (register V v₀))} {C} {ws : List V}
    (h : WPre I w β C ws ws.length) :
    vl I r (pth I r C.mem m) = lastVal v₀ ws := by
  obtain ⟨hval, hops, hoth, hret, hpre⟩ := one_block hT hr hrw h
  obtain ⟨j, h1, h2, h3⟩ := lin_read hatom hval hops hoth hret ws.length hpre
  rw [h3, show j = ws.length by omega, List.take_length]

end Sec4

end Podc.FastReadsRegisterSim
