import Mathlib
import Papers.PODC2023.RuntimeVerification.TimedHist

/-!
# Executions of `A*` (Figure 7) and of the verifier `V_O` (Figure 10)

An execution is described by the operations each process invokes, the responses it obtains
from the black-box implementation `A`, and the (distinct) times of its steps. All shared-memory
contents are *derived* from the times: an atomic `Snapshot` returns everything written before it.

**Steps of the `k`-th operation of process `p`** (local step index `L * k + j`):

| `j` | `A*` (Figure 7) | `V_O` (Figure 10) |
|---|---|---|
| 0 | invocation of `A*.Apply(op)` (line 01 is local) | line 04 |
| 1 | `N.Write(set_i)` (line 02) | |
| 2 | invocation of `A.Apply(op)` (line 03) | |
| 3 | response `y` of `A` (line 04) | |
| 4 | `N.Snapshot()` (line 05), the view `λ` | |
| 5 | response `(y, λ)` of `A*` (lines 06–07) | line 05 |
| 6 | | `M.Write(res_i)` (lines 06–07) |
| 7 | | `M.Snapshot()` and the test (lines 08–12) |

`A*` alone has `L = 6` steps per operation, `V_O` running `A*` has `L = 8`.

Each entry of the snapshot object `N` holds the set of invocation records of its process; its
`Snapshot`, united over the entries, is the set of all invocation records written so far (the
*view*). We store invocation records as `(p, k, op)` (the operation together with its index, which
makes it unique; the paper assumes operations unique and stores `(p, op)`). Likewise `M`, united
over entries, is the set of all 4-tuples `(p, op, y, λ)` written so far.

The history of `A*` (`hS`), of `A` (`hA`) and the history of the *tight execution* `T(E)`
(`hT`, Definition 7.5: invocations at the `Write` step 1, responses at the `Snapshot` step 4) are
timed histories (`TH`); Lemma 7.3 is `simTH_S_T` / `simTH_T_A` (+ `GenLin`).
-/

namespace Podc2023.RuntimeVerification

set_option linter.unusedSectionVars false

open Cslib.SharedMemory.HerlihyWing

/-- `cnt L j n` = the number of `k` with `L * k + j < n`. -/
def cnt (L j n : ℕ) : ℕ := (n + (L - 1 - j)) / L

theorem lt_cnt {L j n k : ℕ} (hj : j < L) : k < cnt L j n ↔ L * k + j < n := by
  have hL : 0 < L := by omega
  rw [cnt, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hL]
  have : (k + 1) * L = L * k + L := by ring
  rw [this]
  generalize L * k = x
  omega

theorem cnt_le_cnt {L i j n : ℕ} (hij : i ≤ j) (hj : j < L) : cnt L j n ≤ cnt L i n := by
  by_contra h
  push Not at h
  have h1 := (lt_cnt (n := n) (k := cnt L i n) hj).1 h
  have h2 := (lt_cnt (n := n) (k := cnt L i n) (lt_of_le_of_lt hij hj)).not.1 (lt_irrefl _)
  omega

/-- Invocation records `(p, k, op)`: elements of views. -/
abbrev IRec (n : ℕ) (Op : Type) := Fin n × ℕ × Op

/-- A (finite) execution: process `p` performed its local steps `0, …, len p - 1`; its `k`-th
operation has argument `op p k` and gets the response `y p k` from `A`; its `i`-th step happens at
time `T p i`. -/
structure Exec (n : ℕ) (Op Y T : Type) where
  len : Fin n → ℕ
  op : Fin n → ℕ → Op
  y : Fin n → ℕ → Y
  T : Fin n → ℕ → T

namespace Exec

variable {n : ℕ} {Op Y T : Type} [LinearOrder T] [DecidableEq Op]

/-- Well-formedness: the steps of a process are in order, distinct steps at distinct times. -/
structure WF (E : Exec n Op Y T) : Prop where
  mono : ∀ p i j, i < j → j < E.len p → E.T p i < E.T p j
  inj : ∀ p q i j, i < E.len p → j < E.len q → E.T p i = E.T q j → p = q ∧ i = j

variable (E : Exec n Op Y T) (L : ℕ)

/-- The view of the `k`-th operation of `p`: the invocation records written (step 1) before its
`Snapshot` (step 4). -/
noncomputable def view (p : Fin n) (k : ℕ) : Finset (IRec n Op) :=
  (Finset.univ : Finset (Fin n)).biUnion fun q =>
    ((Finset.range (cnt L 1 (E.len q))).filter fun j => E.T q (L * j + 1) < E.T p (L * k + 4)).image
      fun j => (q, j, E.op q j)

/-- The timed history with invocations at step `i` and responses at step `r`. -/
def proj {R : Type} (i r : ℕ) (f : Fin n → ℕ → R) : TH (Fin n) Op R T where
  m p := cnt L i (E.len p)
  c p := cnt L r (E.len p)
  op := E.op
  res := f
  ti p k := E.T p (L * k + i)
  tr p k := E.T p (L * k + r)

/-- History of `A*` (responses with views). -/
noncomputable def hS : TH (Fin n) Op (Y × Finset (IRec n Op)) T :=
  E.proj L 0 5 fun p k => (E.y p k, E.view L p k)

/-- History of the tight execution `T(E)` (responses with views). -/
noncomputable def hT : TH (Fin n) Op (Y × Finset (IRec n Op)) T :=
  E.proj L 1 4 fun p k => (E.y p k, E.view L p k)

/-- History of `A`. -/
def hA : TH (Fin n) Op Y T := E.proj L 2 3 E.y

/-- History of `A*` with the views disregarded (Section 7.3.1). -/
def hSy : TH (Fin n) Op Y T := E.proj L 0 5 E.y

/-- History of `T(E)` with the views disregarded. -/
def hTy : TH (Fin n) Op Y T := E.proj L 1 4 E.y

theorem hS_mapRes : (E.hS L).mapRes Prod.fst = E.hSy L := rfl
theorem hT_mapRes : (E.hT L).mapRes Prod.fst = E.hTy L := rfl

variable {E L}

theorem mem_view {p : Fin n} {k : ℕ} {x : IRec n Op} (hL : 1 < L) :
    x ∈ E.view L p k ↔
      L * x.2.1 + 1 < E.len x.1 ∧ E.T x.1 (L * x.2.1 + 1) < E.T p (L * k + 4) ∧
        x.2.2 = E.op x.1 x.2.1 := by
  obtain ⟨q, j, o⟩ := x
  simp only [view, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨q', j', ⟨h1, h2⟩, rfl, rfl, rfl⟩
    exact ⟨(lt_cnt hL).1 h1, h2, rfl⟩
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨q, j, ⟨(lt_cnt hL).2 h1, h2⟩, rfl, rfl, rfl⟩

theorem proj_WF (hw : E.WF) {R : Type} {i r : ℕ} (f : Fin n → ℕ → R) (hir : i < r) (hr : r < L) :
    (E.proj L i r f).WF where
  c_le_m p := cnt_le_cnt hir.le hr
  m_le_c p := by
    simp only [proj]
    by_contra h
    push Not at h
    have h1 := (lt_cnt (lt_trans hir hr)).1 (show cnt L r (E.len p) + 1 < cnt L i (E.len p) by omega)
    have h2 := (lt_cnt (n := E.len p) (k := cnt L r (E.len p)) hr).not.1 (lt_irrefl _)
    have : L * (cnt L r (E.len p) + 1) = L * cnt L r (E.len p) + L := by ring
    omega
  inv_lt_res p k hk := by
    simp only [proj] at hk ⊢
    exact hw.mono p _ _ (by omega) ((lt_cnt hr).1 hk)
  res_lt_inv p k hk := by
    simp only [proj] at hk ⊢
    have h := (lt_cnt (lt_trans hir hr)).1 hk
    have : L * (k + 1) = L * k + L := by ring
    exact hw.mono p _ _ (by omega) (by omega)
  inj := by
    rintro ⟨p, k, b⟩ ⟨q, j, b'⟩ hx hy he
    simp only [TH.Valid, TH.time, proj] at hx hy he
    have hi : i < L := lt_trans hir hr
    have key : ∀ (u v : ℕ), u < L → v < L → L * k + u < E.len p → L * j + v < E.len q →
        E.T p (L * k + u) = E.T q (L * j + v) → p = q ∧ k = j ∧ u = v := by
      intro u v hu hv h1 h2 h3
      obtain ⟨rfl, h4⟩ := hw.inj p q _ _ h1 h2 h3
      refine ⟨rfl, ?_, ?_⟩
      · rcases Nat.lt_trichotomy k j with h | h | h
        · have : L * (k + 1) ≤ L * j := Nat.mul_le_mul_left _ h
          have : L * (k + 1) = L * k + L := by ring
          omega
        · exact h
        · have : L * (j + 1) ≤ L * k := Nat.mul_le_mul_left _ h
          have : L * (j + 1) = L * j + L := by ring
          omega
      · have : L * k = L * j ∨ L * k ≠ L * j := em _
        rcases this with h | h
        · omega
        · exfalso
          rcases Nat.lt_or_gt_of_ne h with h | h
          · have hkj : k < j := by
              by_contra hc; push Not at hc; exact absurd (Nat.mul_le_mul_left L hc) (by omega)
            have : L * (k + 1) ≤ L * j := Nat.mul_le_mul_left _ hkj
            have : L * (k + 1) = L * k + L := by ring
            omega
          · have hkj : j < k := by
              by_contra hc; push Not at hc; exact absurd (Nat.mul_le_mul_left L hc) (by omega)
            have : L * (j + 1) ≤ L * k := Nat.mul_le_mul_left _ hkj
            have : L * (j + 1) = L * j + L := by ring
            omega
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx hy he
    · obtain ⟨rfl, rfl, -⟩ := key i i hi hi ((lt_cnt hi).1 hx) ((lt_cnt hi).1 hy) he; rfl
    · obtain ⟨-, -, h⟩ := key i r hi hr ((lt_cnt hi).1 hx) ((lt_cnt hr).1 hy) he; omega
    · obtain ⟨-, -, h⟩ := key r i hr hi ((lt_cnt hr).1 hx) ((lt_cnt hi).1 hy) he; omega
    · obtain ⟨rfl, rfl, -⟩ := key r r hr hr ((lt_cnt hr).1 hx) ((lt_cnt hr).1 hy) he; rfl

/-! ## Lemma 7.3 -/

/-- The history of `A*` is similar to the history of the tight execution `T(E)`. -/
theorem simTH_S_T (hw : E.WF) (hL : 5 < L) {R : Type} (f : Fin n → ℕ → R) :
    TH.SimTH (E.proj L 0 5 f) (E.proj L 1 4 f) where
  m_le p := cnt_le_cnt (by norm_num) (by omega)
  op_eq _ _ _ := rfl
  c_le p := cnt_le_cnt (by norm_num) hL
  res_eq _ _ _ := rfl
  prec p k q j hk hj h := by
    simp only [proj] at hk hj h ⊢
    have hk' := (lt_cnt hL).1 hk
    have hj' := (lt_cnt (show 1 < L by omega)).1 hj
    calc E.T p (L * k + 4) < E.T p (L * k + 5) := hw.mono _ _ _ (by omega) hk'
      _ < E.T q (L * j + 0) := h
      _ < E.T q (L * j + 1) := hw.mono _ _ _ (by omega) hj'

/-- The history of `T(E)` is similar to the history of `A` (`L ≥ 5`). -/
theorem simTH_T_A (hw : E.WF) (hL : 4 < L) {R : Type} (f : Fin n → ℕ → R) :
    TH.SimTH (E.proj L 1 4 f) (E.proj L 2 3 f) where
  m_le p := cnt_le_cnt (by norm_num) (by omega)
  op_eq _ _ _ := rfl
  c_le p := cnt_le_cnt (by norm_num) hL
  res_eq _ _ _ := rfl
  prec p k q j hk hj h := by
    simp only [proj] at hk hj h ⊢
    have hk' := (lt_cnt hL).1 hk
    have hj' := (lt_cnt (show 2 < L by omega)).1 hj
    calc E.T p (L * k + 3) < E.T p (L * k + 4) := hw.mono _ _ _ (by omega) hk'
      _ < E.T q (L * j + 1) := h
      _ < E.T q (L * j + 2) := hw.mono _ _ _ (by omega) hj'

/-- The history of `A*` is similar to the history of `A`. -/
theorem simTH_S_A (hw : E.WF) (hL : 5 < L) {R : Type} (f : Fin n → ℕ → R) :
    TH.SimTH (E.proj L 0 5 f) (E.proj L 2 3 f) where
  m_le p := cnt_le_cnt (by norm_num) (by omega)
  op_eq _ _ _ := rfl
  c_le p := cnt_le_cnt (by norm_num) hL
  res_eq _ _ _ := rfl
  prec p k q j hk hj h := by
    simp only [proj] at hk hj h ⊢
    have hk' := (lt_cnt hL).1 hk
    have hj' := (lt_cnt (show 2 < L by omega)).1 hj
    calc E.T p (L * k + 3) < E.T p (L * k + 5) := hw.mono _ _ _ (by omega) hk'
      _ < E.T q (L * j + 0) := h
      _ < E.T q (L * j + 2) := hw.mono _ _ _ (by omega) hj'

/-! ## Prefixes of executions -/

/-- The prefix of an execution consisting of the steps before time `t`. -/
def cut (E : Exec n Op Y T) (t : T) : Exec n Op Y T :=
  { E with len := fun p => ((List.range (E.len p)).filter (fun i => decide (E.T p i < t))).length }

theorem lt_cut_len (hw : E.WF) (t : T) (p : Fin n) (i : ℕ) :
    i < (E.cut t).len p ↔ i < E.len p ∧ E.T p i < t := by
  simp only [cut]
  rw [TH.lt_length_filter_range _ (fun a b hab hb h => by
    simp only [decide_eq_true_eq] at h ⊢; exact lt_trans (hw.mono p a b hab hb) h)]
  simp

theorem WF.cut (hw : E.WF) (t : T) : (E.cut t).WF where
  mono p i j hij hj := hw.mono p i j hij ((lt_cut_len hw t p j).1 hj).1
  inj p q i j hi hj := hw.inj p q i j ((lt_cut_len hw t p i).1 hi).1 ((lt_cut_len hw t q j).1 hj).1

/-- Projections commute with prefixes. -/
theorem proj_cut (hw : E.WF) (t : T) {R : Type} {i r : ℕ} (f : Fin n → ℕ → R) (hir : i < r)
    (hr : r < L) : (E.cut t).proj L i r f = (E.proj L i r f).cut t := by
  have hw' := proj_WF hw f hir hr
  have hi : i < L := lt_trans hir hr
  simp only [proj, TH.cut]
  congr 1
  · funext p
    apply eq_of_forall_lt_iff
    intro k
    rw [lt_cnt hi, lt_cut_len hw]
    have := TH.cut_m_iff hw' t p k
    simp only [proj, TH.cut] at this
    rw [this, lt_cnt hi]
  · funext p
    apply eq_of_forall_lt_iff
    intro k
    rw [lt_cnt hr, lt_cut_len hw]
    have := TH.cut_c_iff hw' t p k
    simp only [proj, TH.cut] at this
    rw [this, lt_cnt hr]

end Exec

/-- Membership in a `GenLin` object transfers along timed similarity. -/
theorem GenLin.mem_of_simTH {n : ℕ} {Op R T T' : Type} [LinearOrder T] [LinearOrder T']
    {O : Set (Hist (Fin n) Op R)} (hO : GenLin O) {h : TH (Fin n) Op R T} {h' : TH (Fin n) Op R T'}
    (hw : h.WF) (hw' : h'.WF) (hs : TH.SimTH h h') (h'O : h'.toList ∈ O) : h.toList ∈ O :=
  hO.mem_of_simS h'O (hs.simS hw hw')

/-- Membership in a `GenLin` object transfers to truncations. -/
theorem GenLin.mem_cut {n : ℕ} {Op R T : Type} [LinearOrder T]
    {O : Set (Hist (Fin n) Op R)} (hO : GenLin O) {h : TH (Fin n) Op R T} (hw : h.WF) (t : T)
    (hhO : h.toList ∈ O) : (h.cut t).toList ∈ O :=
  hO.mem_of_prefix hhO (TH.toList_cut_prefix hw t)

end Podc2023.RuntimeVerification
