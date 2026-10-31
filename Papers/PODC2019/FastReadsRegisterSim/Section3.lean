import Papers.PODC2019.FastReadsRegisterSim.Bridge
import Papers.PODC2019.FastReadsRegisterSim.Consistency

/-!
# Section 3: safe and regular simulations — step lower bound for the write when the read is fast

For a writer `w` and a reader `r`, the execution `σ_v` of the paper is
`wlab v ++ opLabels r (wcfg v) read`: a solo write of `v` from the initial configuration followed
by a solo read. By safety the read returns `v` (`ret_eq`), so the reader's local runs on the
memories `Mv v` satisfy `SeqReads` (`seqReads`), and the combinatorics of `ReadTree.lean` apply.

* `theorem_3_1` — some read performs at least `log₂ k` base reads (`k ≤ 2 ^ #reads`);
* `theorem_3_2` — if every read of `r` performs at most `log₂ k` base reads, some write
  performs at least `log₂ k` base writes;
* `corollary_3_5` — the same for regular simulations.
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι P L : Type} [DecidableEq P] [DecidableEq ι]

/-! ## Histories of solo operations -/

section Hist

lemma opsOf_replicate_tau (n : ℕ) (p q : P) :
    opsOf (List.replicate n (Label.tau p : Label P (register V v₀))) q = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, opsOf_cons, ih]

lemma respsOf_replicate_tau (n : ℕ) (p q : P) :
    respsOf (List.replicate n (Label.tau p : Label P (register V v₀))) q = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, respsOf_cons, ih]

variable (I : Sim V v₀ ι P L)

lemma opsOf_opLabels (p : P) (C : Config (register V v₀) (BinRegs ι) P L) (o) (q : P) :
    opsOf (I.opLabels p C o) q = if p = q then [o] else [] := by
  simp only [Sim.opLabels, opsOf_cons, opsOf_append, opsOf_replicate_tau, Label.invOf_inv,
    Label.invOf_ret]
  split_ifs <;> simp

lemma respsOf_opLabels (p : P) (C : Config (register V v₀) (BinRegs ι) P L) (o) (q : P) :
    respsOf (I.opLabels p C o) q = if p = q then [(I.retOut p C o).1] else [] := by
  simp only [Sim.opLabels, respsOf_cons, respsOf_append, respsOf_replicate_tau, Label.retOf_inv,
    Label.retOf_ret]
  split_ifs <;> simp

end Hist

namespace Sec3

variable (I : Sim V v₀ ι P L) (w r : P)

/-- The configuration after a solo write of `v` from the initial configuration. -/
noncomputable def wcfg (v : V) : Config (register V v₀) (BinRegs ι) P L :=
  I.opCfg w I.initCfg (.write v)

/-- The labels of a solo write of `v` from the initial configuration. -/
noncomputable def wlab (v : V) : List (Label P (register V v₀)) :=
  I.opLabels w I.initCfg (.write v)

/-- The local state of `r` at the start of its first read. -/
def rl₀ : L := I.invoke r (I.locInit r) .read

/-- The memory after a solo write of `v` from the initial configuration. -/
noncomputable def Mv (v : V) : Mem ι := (wcfg I w v).mem

/-- Number of steps of the first read of `r` after the solo write of `v`. -/
noncomputable def T (v : V) : ℕ := I.retTime r (wcfg I w v) .read

variable {I w r} (hwr : w ≠ r) (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read)
  (hof : I.ObstructionFree)

include hw hof in
lemma run_wlab (v : V) : I.run (wlab I w v) = some (wcfg I w v) :=
  Sim.runFrom_opLabels hof ⟨[], rfl⟩ rfl (hw v)

include hwr in
lemma wcfg_loc_r (v : V) : (wcfg I w v).loc r = I.locInit r :=
  Sim.opCfg_loc_ne _ _ (Ne.symm hwr)

include hwr in
lemma wcfg_pend_r (v : V) : (wcfg I w v).pend r = none :=
  Sim.opCfg_pend_ne _ _ (Ne.symm hwr)

include hw hof in
lemma reach_wcfg (v : V) : I.Reachable (wcfg I w v) := ⟨_, run_wlab hw hof v⟩

include hwr hw hr hof in
lemma run_sigma (v : V) :
    I.run (wlab I w v ++ I.opLabels r (wcfg I w v) .read) =
      some (I.opCfg r (wcfg I w v) .read) := by
  rw [Impl.run_append_of_eq I (run_wlab hw hof v)]
  exact Sim.runFrom_opLabels hof (reach_wcfg hw hof v) (wcfg_pend_r hwr v) hr

include hwr hw hr hof in
lemma read_spec (v : V) :
    (∀ j < T I w r v, ¬ IsRet (I.act r) (lrun (I.act r) j (rl₀ I r, Mv I w v))) ∧
      I.act r (lrun (I.act r) (T I w r v) (rl₀ I r, Mv I w v)).1 =
        .ret (I.retOut r (wcfg I w v) .read).1 (I.retOut r (wcfg I w v) .read).2 := by
  have := Sim.retTime_spec hof (reach_wcfg hw hof v) (wcfg_pend_r hwr v) hr
  rw [wcfg_loc_r hwr v] at this
  exact this

/-- **Safety in `σ_v`**: the solo read after the solo write of `v` returns `v`. -/
lemma ret_eq (hwr : w ≠ r) (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read)
    (hof : I.ObstructionFree) (hsafe : I.Safe w) (v : V) :
    (I.retOut r (wcfg I w v) .read).1 = v := by
  set α := wlab I w v ++ I.opLabels r (wcfg I w v) .read with hα
  have hval : I.Valid α := ⟨_, run_sigma hwr hw hr hof v⟩
  have hops : ∀ q, opsOf α q =
      (if w = q then [RWOp.write v] else []) ++ (if r = q then [RWOp.read] else []) := by
    intro q; simp [hα, wlab, opsOf_opLabels]
  have hwrite : ∀ y u, IsWrite v₀ α y u → y = (w, 0) ∧ u = v := by
    intro y u hy
    simp only [IsWrite, opOf, hops] at hy
    by_cases h1 : w = y.1
    · have h2 : r ≠ y.1 := fun h => hwr (h1.trans h.symm)
      simp only [h1, h2, ite_true, ite_false, List.append_nil] at hy
      rcases y with ⟨y1, y2⟩
      simp only at h1; subst h1
      rcases y2 with _ | y2 <;> simp at hy
      exact ⟨rfl, hy.symm⟩
    · by_cases h2 : r = y.1
      · simp only [h1, h2, ite_true, ite_false, List.nil_append] at hy
        rcases y with ⟨y1, y2⟩
        rcases y2 with _ | y2 <;> simp at hy
      · simp [h1, h2] at hy
  have hsw : SingleWriter v₀ α w := fun y u hy => by rw [(hwrite y u hy).1]
  have hprec : Precedes α (w, 0) (r, 0) := by
    refine ⟨wlab I w v, I.opLabels r (wcfg I w v) .read, rfl, ?_, ?_⟩
    · simp [Completed, wlab, respsOf_opLabels]
    · simp [Invoked, wlab, opsOf_opLabels, hwr]
  have hret : ReadReturns v₀ α (r, 0) (I.retOut r (wcfg I w v) .read).1 := by
    constructor
    · simp [opOf, hops, hwr]
    · simp [respOf, hα, wlab, respsOf_opLabels, hwr]
  rcases hsafe α hval hsw _ _ hret (fun y u hy => by rw [(hwrite y u hy).1]; exact Or.inl hprec)
    with ⟨-, hno⟩ | ⟨y, hy, -⟩
  · exact absurd hprec (hno _ v (by simp [IsWrite, opOf, hops]))
  · exact (hwrite y _ hy).2

/-- The first reads of `r` after solo writes satisfy the hypotheses of `ReadTree.lean`. -/
lemma seqReads (hwr : w ≠ r) (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read)
    (hof : I.ObstructionFree) (hsafe : I.Safe w) :
    SeqReads (I.act r) (rl₀ I r) (Mv I w) where
  term v := ⟨T I w r v, _, _, (read_spec hwr hw hr hof v).2⟩
  correct v n u l hn := by
    obtain ⟨h1, h2⟩ := read_spec hwr hw hr hof v
    have hle : T I w r v ≤ n := by
      by_contra hlt; exact h1 n (by omega) ⟨u, l, hn⟩
    have heq : lrun (I.act r) n (rl₀ I r, Mv I w v) = lrun (I.act r) (T I w r v) (rl₀ I r, Mv I w v) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [lrun_add, lrun_of_isRet ⟨_, _, h2⟩]
    rw [heq, h2] at hn
    simp only [Action.ret.injEq] at hn
    rw [← hn.1, ret_eq hwr hw hr hof hsafe v]

lemma R_eq (hwr : w ≠ r) (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read)
    (hof : I.ObstructionFree) (hsafe : I.Safe w) (v : V) :
    (seqReads hwr hw hr hof hsafe).R v = T I w r v :=
  SeqReads.R_eq_of _ ⟨_, _, (read_spec hwr hw hr hof v).2⟩ (read_spec hwr hw hr hof v).1

include hwr hw hr hof in
/-- The accesses of the first read of `r` after the solo write of `v`. -/
lemma accesses_read (v : V) :
    I.accesses (wcfg I w v) (.inv r .read :: List.replicate (T I w r v) (.tau r)) =
      (List.range (T I w r v)).flatMap
        (fun j => accL (I.act r) r (lrun (I.act r) j (rl₀ I r, Mv I w v))) := by
  have hD : (I.invCfg (wcfg I w v) r .read).pend r ≠ none := by simp [Sim.invCfg]
  have hst := Sim.step_inv_invCfg (I := I) (C := wcfg I w v) (wcfg_pend_r hwr v) hr
  simp only [Sim.accesses, Sim.accessOf, hst, Option.getD_some, List.nil_append]
  rw [Sim.accesses_taus hD]
  · simp [wcfg_loc_r hwr v, rl₀, Mv]
  · intro j hj
    have := (read_spec hwr hw hr hof v).1 j hj
    simpa [wcfg_loc_r hwr v, rl₀, Mv] using this

include hwr hw hr hof in
lemma valid_read (v : V) :
    I.Valid (wlab I w v ++ .inv r .read :: List.replicate (T I w r v) (.tau r)) := by
  apply Impl.valid_of_prefix I ⟨_, run_sigma hwr hw hr hof v⟩
  rw [List.prefix_append_right_inj, Sim.opLabels]
  exact List.cons_prefix_cons.2 ⟨rfl, List.prefix_append _ _⟩

lemma not_ret_replicate (n : ℕ) (p : P) (u : V) :
    Label.ret p u ∉ List.replicate n (Label.tau p : Label P (register V v₀)) := by
  simp [List.mem_replicate]

end Sec3

open Sec3

/-- **Theorem 3.1** of the paper (Chaudhuri–Welch). In every wait-free safe simulation of a
`k`-valued register from binary registers, some read performs at least `log₂ k` base reads:
`k ≤ 2 ^ #reads` (equivalently `⌈log₂ k⌉ ≤ #reads`). -/
theorem theorem_3_1 [Fintype V] (I : Sim V v₀ ι P L) {w r : P} (hwr : w ≠ r)
    (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read) (hwf : I.WaitFree)
    (hsafe : I.Safe w) :
    ∃ α₁ α₂ C, I.run α₁ = some C ∧ I.Valid (α₁ ++ .inv r .read :: α₂) ∧
      (∀ v, Label.ret r v ∉ α₂) ∧
      Fintype.card V ≤ 2 ^ numReads r (I.accesses C (.inv r .read :: α₂)) := by
  have hof := hwf.obstructionFree
  have h := seqReads hwr hw hr hof hsafe
  obtain ⟨v, hv⟩ := h.exists_card_le_two_pow
  refine ⟨wlab I w v, _, _, run_wlab hw hof v, valid_read hwr hw hr hof v,
    fun u => not_ret_replicate _ _ u, ?_⟩
  rw [accesses_read hwr hw hr hof v, numReads_run]
  convert hv using 2
  simp [SeqReads.str, R_eq hwr hw hr hof hsafe v]

/-- **Lemma 3.3** of the paper. In a wait-free safe simulation of a `k`-valued register
(`k = 2 ^ m`) whose reads (by `r`) read at most `m` registers, the decision tree of the first read
of `r` is a complete binary tree with exactly `k` leaves, all at depth `m`: the read-response
strings of the first read after a solo write of `v` (`σ_v`) are exactly the binary strings of
length `m`, each for exactly one value. -/
theorem lemma_3_3 [Fintype V] (I : Sim V v₀ ι P L) {w r : P} (hwr : w ≠ r)
    (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read) (hwf : I.WaitFree)
    (hsafe : I.Safe w) {m : ℕ} (hk : Fintype.card V = 2 ^ m) (hread : I.ReadReadsLE r m) :
    let s : V → List Bool := fun v =>
      (rr (I.act r) (rl₀ I r, Mv I w v) (T I w r v)).map Prod.snd
    (∀ v, (s v).length = m) ∧ (∀ u : List Bool, u.length = m → ∃ v, s v = u) ∧
      Function.Injective s := by
  intro s
  have hof := hwf.obstructionFree
  have h := seqReads hwr hw hr hof hsafe
  have hs : ∀ v, s v = h.str v := fun v => by simp [s, SeqReads.str, R_eq hwr hw hr hof hsafe v]
  have hlen : ∀ v, (h.str v).length ≤ m := by
    intro v
    have := hread _ _ _ (run_wlab hw hof v) (valid_read hwr hw hr hof v)
      (fun u => not_ret_replicate _ _ u)
    rw [accesses_read hwr hw hr hof v, numReads_run] at this
    simpa [SeqReads.str, R_eq hwr hw hr hof hsafe v] using this
  obtain ⟨h1, h2⟩ := h.complete hk hlen
  refine ⟨fun v => by rw [hs]; exact h1 v, fun u hu => ?_, fun v v' hvv => ?_⟩
  · obtain ⟨v, hv⟩ := h2 u hu; exact ⟨v, by rw [hs]; exact hv⟩
  · rw [hs, hs] at hvv; exact h.prefixFree v v' (by rw [hvv])

/-- **Lemma 3.4** of the paper. In the same setting, the first read of `r` after a solo write of
`v` reads pairwise distinct registers, none of which it accessed (read or wrote) earlier during
the read, and each read returns the value the register had after the write of `v`. -/
theorem lemma_3_4 [Fintype V] (I : Sim V v₀ ι P L) {w r : P} (hwr : w ≠ r)
    (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read) (hwf : I.WaitFree)
    (hsafe : I.Safe w) {m : ℕ} (hk : Fintype.card V = 2 ^ m) (hread : I.ReadReadsLE r m) (v : V) :
    ((rr (I.act r) (rl₀ I r, Mv I w v) (T I w r v)).map Prod.fst).Nodup ∧
      (∀ n < T I w r v, ∀ i, RdAt (I.act r) (lrun (I.act r) n (rl₀ I r, Mv I w v)) i →
        ∀ n' < n, ¬ Acc (I.act r) (lrun (I.act r) n' (rl₀ I r, Mv I w v)) i) ∧
      ∀ e ∈ rr (I.act r) (rl₀ I r, Mv I w v) (T I w r v), Mv I w v e.1 = e.2 := by
  have hof := hwf.obstructionFree
  have h := seqReads hwr hw hr hof hsafe
  have hlen : ∀ v, (h.str v).length ≤ m := by
    intro v
    have := hread _ _ _ (run_wlab hw hof v) (valid_read hwr hw hr hof v)
      (fun u => not_ret_replicate _ _ u)
    rw [accesses_read hwr hw hr hof v, numReads_run] at this
    simpa [SeqReads.str, R_eq hwr hw hr hof hsafe v] using this
  have hRv := R_eq hwr hw hr hof hsafe v
  refine ⟨by rw [← hRv]; exact h.nodup_regs hk hlen v, fun n hn i hi =>
    (h.fresh hk hlen (by rw [hRv]; exact hn) hi).1, fun e he => ?_⟩
  obtain ⟨n, hn, hrd⟩ := mem_rr _ he
  obtain ⟨hi, hv⟩ := rd_eq_some.1 (show rd _ _ = some (e.1, e.2) from hrd)
  rw [← hv]; exact ((h.fresh hk hlen (by rw [hRv]; exact hn) hi).2).symm

/-- **Theorem 3.2** of the paper. In a wait-free safe simulation of a `k`-valued register
(`k = 2 ^ m`) from binary registers, if every read of some reader `r` performs at most
`m = log₂ k` base reads, then some write performs at least `log₂ k` base writes. -/
theorem theorem_3_2 [Fintype V] (I : Sim V v₀ ι P L) {w r : P} (hwr : w ≠ r)
    (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read) (hwf : I.WaitFree)
    (hsafe : I.Safe w) {m : ℕ} (hk : Fintype.card V = 2 ^ m) (hread : I.ReadReadsLE r m) :
    I.SomeWriteWritesGE w m := by
  have hof := hwf.obstructionFree
  have h := seqReads hwr hw hr hof hsafe
  have hlen : ∀ v, (h.str v).length ≤ m := by
    intro v
    have := hread _ _ _ (run_wlab hw hof v) (valid_read hwr hw hr hof v)
      (fun u => not_ret_replicate _ _ u)
    rw [accesses_read hwr hw hr hof v, numReads_run] at this
    simpa [SeqReads.str, R_eq hwr hw hr hof hsafe v] using this
  obtain ⟨v, rs, hnd, hlenrs, hrs⟩ := h.exists_far hk hlen I.memInit
  -- the solo write of `v` from the initial configuration
  have hspec := Sim.retTime_spec (I := I) (p := w) hof ⟨[], rfl⟩ rfl (hw v)
  have hD : (I.invCfg I.initCfg w (.write v)).pend w ≠ none := by simp [Sim.invCfg]
  refine ⟨[], List.replicate (I.retTime w I.initCfg (.write v)) (.tau w), I.initCfg, v, rfl, ?_,
    fun u => not_ret_replicate _ _ u, ?_⟩
  · apply Impl.valid_of_prefix I ⟨_, run_wlab hw hof v⟩
    simp only [wlab, Sim.opLabels, List.nil_append]
    exact List.cons_prefix_cons.2 ⟨rfl, List.prefix_append _ _⟩
  · have hst := Sim.step_inv_invCfg (I := I) (C := I.initCfg) (p := w) rfl (hw v)
    simp only [Sim.accesses, Sim.accessOf, hst, Option.getD_some, List.nil_append]
    rw [Sim.accesses_taus hD _ (by simpa using hspec.1)]
    rw [← hlenrs]
    apply numWrites_ge
    · exact hnd
    · intro i hi
      have := hrs i hi
      simpa [Mv, wcfg, Sim.opCfg_mem, Impl.initCfg] using this

/-- **Corollary 3.5** of the paper: Theorem 3.2 for regular simulations. -/
theorem corollary_3_5 [Fintype V] (I : Sim V v₀ ι P L) {w r : P} (hwr : w ≠ r)
    (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read) (hwf : I.WaitFree)
    (hreg : I.Regular w) {m : ℕ} (hk : Fintype.card V = 2 ^ m) (hread : I.ReadReadsLE r m) :
    I.SomeWriteWritesGE w m :=
  theorem_3_2 I hwr hw hr hwf hreg.safe hk hread

end Podc.FastReadsRegisterSim
