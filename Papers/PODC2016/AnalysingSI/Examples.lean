import Papers.PODC2016.AnalysingSI.Robustness
import Papers.PODC2016.AnalysingSI.TxnLemmas

/-!
# Examples of Figure 2 (Cerone–Gotsman, PODC 2016)

Concrete histories and dependency graphs from Figure 2 of the paper. Transaction `0` is always
the initialisation transaction writing the initial values of all objects; session orders are
empty.

* **Write skew** (Figure 2(d)): `writeSkewGraph ∈ GraphSI \ GraphSER`, and the history
  `writeSkew` is in `HistSI \ HistSER`.
* **Long fork** (Figure 2(c)): `longFork ∈ HistPSI \ HistSI`; consequently Theorem 21 is false
  if Definition 20 is read literally (with `ExecSI` in place of `ExecPSI`).
* **Lost update** (Figure 2(b)): the graph of the figure is not in `GraphPSI`, and the history
  `lostUpdate` is not even in `HistPSI`.
-/

namespace Podc.AnalysingSI.Examples

open Relation

/-! ### Generic helpers -/

section Helpers

variable {α : Type*}

/-- A relation that strictly increases a rank function is acyclic. -/
theorem acyclic_of_rank {R : α → α → Prop} (r : α → ℕ) (h : ∀ a b, R a b → r a < r b) :
    Acyclic R := by
  intro a ha
  have key : ∀ x y, TransGen R x y → r x < r y := by
    intro x y hxy
    induction hxy with
    | single h' => exact h _ _ h'
    | tail _ h' ih => exact lt_trans ih (h _ _ h')
  exact lt_irrefl _ (key a a ha)

/-- Sets closed under `R` are closed under `R⁺`. -/
theorem transGen_closed {R : α → α → Prop} (S : α → Prop) (hS : ∀ a b, R a b → S a → S b)
    {a b : α} (h : TransGen R a b) (ha : S a) : S b := by
  induction h with
  | single h' => exact hS _ _ h' ha
  | tail _ h' ih => exact hS _ _ h' ih

variable {Obj V : Type*} [DecidableEq Obj] [DecidableEq V]

/-- A decidable sufficient condition for INT: every operation `o` agrees with the value read by
the first operation on `o`'s object that follows it, if that operation is a read. -/
def intOk : Txn Obj V → Bool
  | [] => true
  | o :: T => intOk T && match T.find? (fun o' => decide (o'.obj = o.obj)) with
      | some (.read _ m) => decide (o.val = m)
      | _ => true

omit [DecidableEq V] in
theorem int_nil : Txn.Int ([] : Txn Obj V) := by
  intro pre suf x n o h
  simp at h

omit [DecidableEq V] in
theorem int_single (o : Op Obj V) : Txn.Int [o] := by
  intro pre suf x n o' h ho
  rcases pre with _ | ⟨p, pre⟩
  · simp at ho
  · simp at h

theorem int_of_intOk : ∀ T : Txn Obj V, intOk T = true → T.Int
  | [], _ => int_nil
  | o :: T, h => by
    rw [intOk, Bool.and_eq_true] at h
    have hT := int_of_intOk T h.1
    have := Txn.Int.append (l₁ := [o]) (l₂ := T) (int_single o) hT ?_
    · simpa using this
    intro x n hr hacc
    rw [Txn.accesses_singleton] at hacc
    subst hacc
    have h2 := h.2
    simp only [Txn.Reads] at hr
    rw [hr] at h2
    simp only [decide_eq_true_eq] at h2
    simp [Txn.finalVal, h2]

end Helpers

/-! ### Write skew (Figure 2(d)) -/

/-- The transactions of Figure 2(d); objects `acct1 = 0`, `acct2 = 1`, initially `60`. -/
def wsTxn : Fin 3 → Txn (Fin 2) ℤ
  | 0 => [.write 0 60, .write 1 60]
  | 1 => [.read 0 60, .read 1 60, .write 0 (-40)]
  | 2 => [.read 0 60, .read 1 60, .write 1 (-40)]

/-- The write-skew history of Figure 2(d). -/
def writeSkew : History (Fin 3) (Fin 2) ℤ where
  txn := wsTxn
  SO := fun _ _ => False

/-- The dependency graph of Figure 2(d): both `T1` and `T2` read both accounts from the
initialisation transaction `T0`; `T0 —WW(acct1)→ T1` and `T0 —WW(acct2)→ T2`. -/
def writeSkewGraph : DepGraph (Fin 3) (Fin 2) ℤ where
  toHistory := writeSkew
  WR := fun _ T S => T = 0 ∧ S ≠ 0
  WW := fun x T S => T = 0 ∧ S.val = x.val + 1

theorem ws_writes (T : Fin 3) (x : Fin 2) (n : ℤ) :
    (wsTxn T).Writes x n ↔ (T = 0 ∧ n = 60) ∨ (T.val = x.val + 1 ∧ n = -40) := by
  fin_cases T <;> fin_cases x <;> simp [wsTxn, Txn.Writes] <;> omega

theorem ws_reads (T : Fin 3) (x : Fin 2) (n : ℤ) :
    (wsTxn T).Reads x n ↔ T ≠ 0 ∧ n = 60 := by
  fin_cases T <;> fin_cases x <;> simp [wsTxn, Txn.Reads] <;> omega


@[simp] theorem ws_txn : writeSkewGraph.txn = wsTxn := rfl
@[simp] theorem ws_toHistory : writeSkewGraph.toHistory = writeSkew := rfl
@[simp] theorem ws_hist_txn : writeSkew.txn = wsTxn := rfl

theorem ws_writeTx (x : Fin 2) (T : Fin 3) : writeSkew.WriteTx x T ↔ T = 0 ∨ T.val = x.val + 1 := by
  simp [History.WriteTx, ws_writes, exists_or]

theorem ws_readsObj (x : Fin 2) (T : Fin 3) : writeSkew.ReadsObj x T ↔ T ≠ 0 := by
  simp [History.ReadsObj, ws_reads]

theorem writeSkewGraph_isDepGraph : writeSkewGraph.IsDepGraph where
  wr_val := by
    rintro T S x ⟨rfl, hS⟩
    exact ⟨60, Ne.symm hS, by simp [ws_writes], by simp [ws_reads, hS]⟩
  wr_exists := by
    intro S x h
    rw [ws_toHistory, ws_readsObj] at h
    exact ⟨0, rfl, h⟩
  wr_unique := by
    rintro T T' S x ⟨rfl, -⟩ ⟨rfl, -⟩
    rfl
  ww_writeTx := by
    rintro x T S ⟨rfl, h⟩
    simp [ws_writeTx, h]
  ww_trans := by
    rintro x T S U ⟨rfl, h⟩ ⟨rfl, -⟩
    simp at h
  ww_irrefl := by
    rintro x T ⟨rfl, h⟩
    simp at h
  ww_total := by
    simp only [ws_writeTx, writeSkewGraph]
    decide

theorem writeSkewGraph_intAll : writeSkewGraph.IntAll := by
  intro T
  fin_cases T <;> exact int_of_intOk _ rfl

/-- `T1 —RW(acct2)→ T2`. -/
theorem ws_rw12 : writeSkewGraph.RWu 1 2 := ⟨1, by decide, 0, ⟨rfl, by decide⟩, rfl, rfl⟩

/-- `T2 —RW(acct1)→ T1`. -/
theorem ws_rw21 : writeSkewGraph.RWu 2 1 := ⟨0, by decide, 0, ⟨rfl, by decide⟩, rfl, rfl⟩

/-- Figure 2(d): the write-skew dependency graph is in `GraphSI`, but not in `GraphSER`
("`G3 ∈ GraphSI \ GraphSER`"). -/
theorem writeSkewGraph_si_not_ser : writeSkewGraph.IsSI ∧ ¬ writeSkewGraph.IsSER := by
  refine ⟨⟨writeSkewGraph_isDepGraph, writeSkewGraph_intAll, ?_⟩, ?_⟩
  · refine acyclic_of_rank (fun T => if T = 0 then 0 else 1) ?_
    rintro a b ⟨c, hac, hcb⟩
    have hb : b ≠ 0 := by
      rcases hcb with _ | ⟨x, -, T', -, -, hww⟩
      · rcases hac with h | ⟨x, -, h⟩ | ⟨x, -, h⟩
        · exact h.elim
        · exact h
        · rintro rfl
          simp at h
      · rintro rfl
        simp at hww
    have ha : a = 0 := by
      rcases hac with h | ⟨x, h, -⟩ | ⟨x, h, -⟩
      · exact h.elim
      · exact h
      · exact h
    simp [ha, hb]
  · rintro ⟨-, -, h⟩
    exact h 1 (TransGen.head (Or.inr ws_rw12) (TransGen.single (Or.inr ws_rw21)))

/-- The write-skew history is allowed by SI (Theorem 9 applied to `writeSkewGraph`). -/
theorem writeSkew_mem_histSI : writeSkew ∈ HistSI :=
  (theorem9 writeSkew).2 ⟨_, _, writeSkewGraph_si_not_ser.1⟩

/-- The write-skew history is not serializable. -/
theorem writeSkew_not_mem_histSER : writeSkew ∉ HistSER := by
  rintro ⟨VIS, CO, ⟨⟨⟨hvc, htr, hirr⟩, htot⟩, -, hext, -, htv⟩⟩
  have key : ∀ (T : Fin 3) (x : Fin 2), T ≠ 0 →
      VIS 0 T ∧ ∀ b, VIS b T → writeSkew.WriteTx x b → b = 0 ∨ CO b 0 := by
    intro T x hT
    obtain ⟨M, ⟨hM1, hM2⟩, hw⟩ := hext T x 60 ((ws_reads T x 60).2 ⟨hT, rfl⟩)
    have hM : M = 0 := by
      change (wsTxn M).Writes x 60 at hw
      rw [ws_writes] at hw
      omega
    subst hM
    exact ⟨hM1.1, fun b h1 h2 => hM2 b ⟨h1, h2⟩⟩
  have htv' : CO = VIS := htv
  have hvis : ∀ a b, CO a b → VIS a b := fun a b h => htv' ▸ h
  rcases htot 1 2 (by decide) with h | h
  · rcases (key 2 0 (by decide)).2 1 (hvis _ _ h) ((ws_writeTx _ _).2 (by decide)) with h' | h'
    · exact absurd h' (by decide)
    · exact hirr _ (htr _ _ _ h' (hvc _ _ (key 1 0 (by decide)).1))
  · rcases (key 1 1 (by decide)).2 2 (hvis _ _ h) ((ws_writeTx _ _).2 (by decide)) with h' | h'
    · exact absurd h' (by decide)
    · exact hirr _ (htr _ _ _ h' (hvc _ _ (key 2 1 (by decide)).1))

/-- Figure 2(d): the write-skew history is in `HistSI \ HistSER`. -/
theorem writeSkew_si_not_ser : writeSkew ∈ HistSI ∧ writeSkew ∉ HistSER :=
  ⟨writeSkew_mem_histSI, writeSkew_not_mem_histSER⟩

/-! ### Long fork (Figure 2(c)) -/

section LongFork

-- `decide` over all quadruples of transaction ids needs larger instance terms
set_option synthInstance.maxSize 4000

/-- The transactions of Figure 2(c); objects `x = 0`, `y = 1`, initially `0`. -/
def lfTxn : Fin 5 → Txn (Fin 2) ℤ
  | 0 => [.write 0 0, .write 1 0]
  | 1 => [.write 0 1]
  | 2 => [.write 1 1]
  | 3 => [.read 0 1, .read 1 0]
  | 4 => [.read 0 0, .read 1 1]

/-- The long-fork history of Figure 2(c). -/
def longFork : History (Fin 5) (Fin 2) ℤ where
  txn := lfTxn
  SO := fun _ _ => False

/-- Read dependencies of Figure 2(c), as triples `(object, writer, reader)`. -/
def lfWR : List (Fin 2 × Fin 5 × Fin 5) := [(0, 1, 3), (0, 0, 4), (1, 0, 3), (1, 2, 4)]

/-- Write dependencies of Figure 2(c), as triples `(object, earlier, later)`. -/
def lfWW : List (Fin 2 × Fin 5 × Fin 5) := [(0, 0, 1), (1, 0, 2)]

/-- The dependency graph of Figure 2(c). -/
def longForkGraph : DepGraph (Fin 5) (Fin 2) ℤ where
  toHistory := longFork
  WR := fun x T S => (x, T, S) ∈ lfWR
  WW := fun x T S => (x, T, S) ∈ lfWW

@[simp] theorem lf_toHistory : longForkGraph.toHistory = longFork := rfl
@[simp] theorem lf_hist_txn : longFork.txn = lfTxn := rfl

theorem lf_writes (T : Fin 5) (x : Fin 2) (n : ℤ) :
    (lfTxn T).Writes x n ↔
      (T = 0 ∧ n = 0) ∨ (T = 1 ∧ x = 0 ∧ n = 1) ∨ (T = 2 ∧ x = 1 ∧ n = 1) := by
  fin_cases T <;> fin_cases x <;> simp [lfTxn, Txn.Writes] <;> omega

theorem lf_reads (T : Fin 5) (x : Fin 2) (n : ℤ) :
    (lfTxn T).Reads x n ↔
      (T = 3 ∧ ((x = 0 ∧ n = 1) ∨ (x = 1 ∧ n = 0))) ∨
        (T = 4 ∧ ((x = 0 ∧ n = 0) ∨ (x = 1 ∧ n = 1))) := by
  fin_cases T <;> fin_cases x <;> simp [lfTxn, Txn.Reads] <;> omega

theorem lf_writeTx (x : Fin 2) (T : Fin 5) :
    longFork.WriteTx x T ↔ T = 0 ∨ (T = 1 ∧ x = 0) ∨ (T = 2 ∧ x = 1) := by
  simp only [History.WriteTx, lf_hist_txn, lf_writes]
  constructor
  · rintro ⟨n, h | h | h⟩
    · exact Or.inl h.1
    · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.1⟩)
  · rintro (h | h | h)
    · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨1, Or.inr (Or.inl ⟨h.1, h.2, rfl⟩)⟩
    · exact ⟨1, Or.inr (Or.inr ⟨h.1, h.2, rfl⟩)⟩

theorem lf_readsObj (x : Fin 2) (T : Fin 5) : longFork.ReadsObj x T ↔ T = 3 ∨ T = 4 := by
  simp only [History.ReadsObj, lf_hist_txn, lf_reads]
  fin_cases x <;> simp [exists_or]

theorem longForkGraph_isDepGraph : longForkGraph.IsDepGraph where
  wr_val := by
    intro T S x h
    have h' : (x, T, S) ∈ lfWR := h
    simp only [lfWR, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
    rcases h' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [lf_writes, lf_reads]
  wr_exists := by
    intro S x h
    rw [lf_toHistory, lf_readsObj] at h
    show ∃ T, (x, T, S) ∈ lfWR
    revert S x
    decide
  wr_unique := by
    intro T T' S x h h'
    change (x, T, S) ∈ lfWR at h
    change (x, T', S) ∈ lfWR at h'
    revert T T' S x
    decide
  ww_writeTx := by
    intro x T S h
    change (x, T, S) ∈ lfWW at h
    simp only [lf_toHistory, lf_writeTx]
    revert T S x
    decide
  ww_trans := by
    intro x T S U h h'
    change (x, T, S) ∈ lfWW at h
    change (x, S, U) ∈ lfWW at h'
    show (x, T, U) ∈ lfWW
    revert x T S U
    decide
  ww_irrefl := by
    intro x T h
    change (x, T, T) ∈ lfWW at h
    revert x T
    decide
  ww_total := by
    simp only [lf_writeTx, longForkGraph]
    decide

theorem longForkGraph_intAll : longForkGraph.IntAll := by
  intro T
  fin_cases T <;> exact int_of_intOk _ rfl

/-- The edges `SO ∪ WR ∪ WW` of Figure 2(c). -/
theorem lf_B (a b : Fin 5) : longForkGraph.B a b ↔
    (a, b) ∈ [((1 : Fin 5), (3 : Fin 5)), (0, 4), (0, 3), (2, 4), (0, 1), (0, 2)] := by
  simp only [DepGraph.B, DepGraph.WRu, DepGraph.WWu, longForkGraph, longFork]
  revert a b
  decide

/-- The anti-dependencies of Figure 2(c): `T3 —RW(y)→ T2` and `T4 —RW(x)→ T1`. -/
theorem lf_RW (a b : Fin 5) : longForkGraph.RWu a b → (a = 3 ∧ b = 2) ∨ (a = 4 ∧ b = 1) := by
  rintro ⟨x, hne, T', h, h'⟩
  change (x, T', a) ∈ lfWR at h
  change (x, T', b) ∈ lfWW at h'
  revert a b x T'
  decide

/-- Figure 2(c): the long-fork dependency graph is in `GraphPSI`. -/
theorem longForkGraph_isPSI : longForkGraph.IsPSI := by
  refine ⟨longForkGraph_isDepGraph, longForkGraph_intAll, ?_⟩
  have hacyc : Acyclic longForkGraph.B := by
    refine acyclic_of_rank (fun T => if T = 0 then 0 else if T = 1 ∨ T = 2 then 1 else 2) ?_
    intro a b h
    rw [lf_B] at h
    revert a b
    decide
  have closed : ∀ (S : Fin 5 → Prop) [DecidablePred S],
      (∀ a b, (a, b) ∈ [((1 : Fin 5), (3 : Fin 5)), (0, 4), (0, 3), (2, 4), (0, 1), (0, 2)] →
        S a → S b) →
      ∀ a b, TransGen longForkGraph.B a b → S a → S b := by
    intro S _ hS a b h ha
    exact transGen_closed S (fun a b h => hS a b ((lf_B a b).1 h)) h ha
  rintro T ⟨S, hTS, hST⟩
  rcases hST with _ | hST
  · exact hacyc _ hTS
  rcases lf_RW _ _ hST with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have := closed (fun a => a = 2 ∨ a = 4) (by decide) _ _ hTS (Or.inl rfl)
    revert this
    decide
  · have := closed (fun a => a = 1 ∨ a = 3) (by decide) _ _ hTS (Or.inl rfl)
    revert this
    decide

/-- Figure 2(c): the long-fork history is allowed by parallel SI (Theorem 21). -/
theorem longFork_mem_histPSI : longFork ∈ HistPSI :=
  (theorem21 longFork).2 ⟨_, _, longForkGraph_isPSI⟩

/-- Figure 2(c) and §2: the long-fork history is not allowed by SI. -/
theorem longFork_not_mem_histSI : longFork ∉ HistSI := by
  rintro ⟨VIS, CO, ⟨⟨⟨hvc, htr, hirr⟩, htot⟩, -, hext, -, hpre, -⟩⟩
  have ext' : ∀ (T : Fin 5) (x : Fin 2) (n : ℤ) (W : Fin 5), (lfTxn T).Reads x n →
      (∀ M, (lfTxn M).Writes x n → M = W) →
      VIS W T ∧ ∀ b, VIS b T → longFork.WriteTx x b → b = W ∨ CO b W := by
    intro T x n W hr hu
    obtain ⟨M, ⟨hM1, hM2⟩, hw⟩ := hext T x n hr
    obtain rfl := hu M hw
    exact ⟨hM1.1, fun b h1 h2 => hM2 b ⟨h1, h2⟩⟩
  obtain ⟨v13, m13⟩ := ext' 3 0 1 1 (by simp [lf_reads]) (by
    intro M h
    rw [lf_writes] at h
    omega)
  obtain ⟨v03, m03⟩ := ext' 3 1 0 0 (by simp [lf_reads]) (by
    intro M h
    rw [lf_writes] at h
    omega)
  obtain ⟨v24, m24⟩ := ext' 4 1 1 2 (by simp [lf_reads]) (by
    intro M h
    rw [lf_writes] at h
    omega)
  obtain ⟨v04, m04⟩ := ext' 4 0 0 0 (by simp [lf_reads]) (by
    intro M h
    rw [lf_writes] at h
    omega)
  -- `T3` sees `T0` and reads `x` from `T1`, so `T0 —CO→ T1`; symmetrically `T0 —CO→ T2`
  have co01 : CO 0 1 := by
    rcases m13 0 v03 ((lf_writeTx _ _).2 (Or.inl rfl)) with h | h
    · exact absurd h (by decide)
    · exact h
  have co02 : CO 0 2 := by
    rcases m24 0 v04 ((lf_writeTx _ _).2 (Or.inl rfl)) with h | h
    · exact absurd h (by decide)
    · exact h
  rcases htot 1 2 (by decide) with h | h
  · -- by PREFIX `T4` sees `T1`, so it cannot read `x` from `T0`
    rcases m04 1 (hpre _ _ _ h v24) ((lf_writeTx _ _).2 (by decide)) with h' | h'
    · exact absurd h' (by decide)
    · exact hirr _ (htr _ _ _ h' co01)
  · -- by PREFIX `T3` sees `T2`, so it cannot read `y` from `T0`
    rcases m03 2 (hpre _ _ _ h v13) ((lf_writeTx _ _).2 (by decide)) with h' | h'
    · exact absurd h' (by decide)
    · exact hirr _ (htr _ _ _ h' co02)

/-- Figure 2(c): the long-fork history is in `HistPSI \ HistSI`. -/
theorem longFork_psi_not_si : longFork ∈ HistPSI ∧ longFork ∉ HistSI :=
  ⟨longFork_mem_histPSI, longFork_not_mem_histSI⟩

/-- With Definition 20 read literally (`HistPSI` defined from `ExecSI`, so that it coincides
with `HistSI`), Theorem 21 is false: the long-fork history has a dependency graph in `GraphPSI`
but is not in `HistSI`. -/
theorem theorem21_literal_false :
    ¬ ∀ H : History (Fin 5) (Fin 2) ℤ,
      H ∈ HistSI ↔ ∃ WR WW, (DepGraph.mk H WR WW).IsPSI := fun h =>
  longFork_not_mem_histSI ((h longFork).2 ⟨_, _, longForkGraph_isPSI⟩)

end LongFork

/-! ### Lost update (Figure 2(b)) -/

/-- The transactions of Figure 2(b); the single object `acct = 0`, initially `0`. -/
def luTxn : Fin 3 → Txn (Fin 1) ℤ
  | 0 => [.write 0 0]
  | 1 => [.read 0 0, .write 0 50]
  | 2 => [.read 0 0, .write 0 25]

/-- The lost-update history of Figure 2(b). -/
def lostUpdate : History (Fin 3) (Fin 1) ℤ where
  txn := luTxn
  SO := fun _ _ => False

/-- The dependency graph of Figure 2(b): `T1` and `T2` read from `T0`, and
`T0 —WW→ T1 —WW→ T2`. -/
def lostUpdateGraph : DepGraph (Fin 3) (Fin 1) ℤ where
  toHistory := lostUpdate
  WR := fun _ T S => T = 0 ∧ S ≠ 0
  WW := fun _ T S => T < S

@[simp] theorem lu_toHistory : lostUpdateGraph.toHistory = lostUpdate := rfl
@[simp] theorem lu_hist_txn : lostUpdate.txn = luTxn := rfl

theorem lu_writes (T : Fin 3) (x : Fin 1) (n : ℤ) :
    (luTxn T).Writes x n ↔ (T = 0 ∧ n = 0) ∨ (T = 1 ∧ n = 50) ∨ (T = 2 ∧ n = 25) := by
  fin_cases T <;> fin_cases x <;> simp [luTxn, Txn.Writes] <;> omega

theorem lu_reads (T : Fin 3) (x : Fin 1) (n : ℤ) :
    (luTxn T).Reads x n ↔ T ≠ 0 ∧ n = 0 := by
  fin_cases T <;> fin_cases x <;> simp [luTxn, Txn.Reads] <;> omega

theorem lu_writeTx (x : Fin 1) (T : Fin 3) : lostUpdate.WriteTx x T := by
  fin_cases T <;> simp [History.WriteTx, lu_writes]

theorem lostUpdateGraph_isDepGraph : lostUpdateGraph.IsDepGraph where
  wr_val := by
    rintro T S x ⟨rfl, hS⟩
    exact ⟨0, Ne.symm hS, by simp [lu_writes], by simp [lu_reads, hS]⟩
  wr_exists := by
    rintro S x ⟨n, h⟩
    exact ⟨0, rfl, ((lu_reads _ _ _).1 h).1⟩
  wr_unique := by
    rintro T T' S x ⟨rfl, -⟩ ⟨rfl, -⟩
    rfl
  ww_writeTx := fun x T S _ => ⟨lu_writeTx x T, lu_writeTx x S⟩
  ww_trans := fun _ _ _ _ h h' => lt_trans h h'
  ww_irrefl := fun _ T h => lt_irrefl T h
  ww_total := fun _ T S _ _ hne => lt_or_gt_of_ne hne

/-- `T2 —RW→ T1`. -/
theorem lu_rw21 : lostUpdateGraph.RWu 2 1 :=
  ⟨0, by decide, 0, ⟨rfl, by decide⟩, (by decide : (0 : Fin 3) < 1)⟩

/-- Figure 2(b): the lost-update dependency graph is not in `GraphPSI` (it has the cycle
`T1 —WW→ T2 —RW→ T1` with a single anti-dependency), hence not in `GraphSI` either. -/
theorem lostUpdateGraph_not_isPSI : ¬ lostUpdateGraph.IsPSI := by
  rintro ⟨-, -, h⟩
  exact h 1 ⟨2, TransGen.single (Or.inr (Or.inr ⟨0, (by decide : (1 : Fin 3) < 2)⟩)), ReflGen.single lu_rw21⟩

/-- Figure 2(b): the lost-update history is not allowed even by parallel SI (NOCONFLICT forces
`T1` and `T2` to be related by visibility). -/
theorem lostUpdate_not_mem_histPSI : lostUpdate ∉ HistPSI := by
  rintro ⟨VIS, CO, ⟨⟨⟨hvc, htr, hirr⟩, -⟩, -, hext, -, -, hnc⟩⟩
  have key : ∀ T : Fin 3, T ≠ 0 →
      VIS 0 T ∧ ∀ b, VIS b T → b = 0 ∨ CO b 0 := by
    intro T hT
    obtain ⟨M, ⟨hM1, hM2⟩, hw⟩ := hext T 0 0 ((lu_reads T 0 0).2 ⟨hT, rfl⟩)
    have hM : M = 0 := by
      change (luTxn M).Writes 0 0 at hw
      rw [lu_writes] at hw
      omega
    subst hM
    exact ⟨hM1.1, fun b h1 => hM2 b ⟨h1, lu_writeTx 0 b⟩⟩
  rcases hnc 1 2 0 (lu_writeTx 0 1) (lu_writeTx 0 2) (by decide) with h | h
  · rcases (key 2 (by decide)).2 1 h with h' | h'
    · exact absurd h' (by decide)
    · exact hirr _ (htr _ _ _ h' (hvc _ _ (key 1 (by decide)).1))
  · rcases (key 1 (by decide)).2 2 h with h' | h'
    · exact absurd h' (by decide)
    · exact hirr _ (htr _ _ _ h' (hvc _ _ (key 2 (by decide)).1))

end Podc.AnalysingSI.Examples
