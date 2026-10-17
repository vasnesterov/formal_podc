import Mathlib
import Papers.PODC2023.RuntimeVerification.Enforce

/-!
# Infinite executions (Definition 6.1 / Theorem 8.1 as stated)

An infinite execution of `V_O` running `A*`: process `p` performs `len p ∈ ℕ∞` steps (a process
blocked forever inside `A` performs finitely many). Its finite prefixes `E.pre t` (the steps
before time `t`) are finite executions (`Exec`), to which `Theorems.lean` applies.

`thm_8_1_infinite`: completeness and stability in the form of Definition 6.1 / Theorem 8.1, under
the paper's standing assumptions made explicit: no process stops between its `N.Snapshot` and
its `M.Write` (wait-free code, no crash), and the verifier executes infinitely many tests (which is
what lock-freedom of `A` and the absence of crashes give).
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing Sketch

set_option linter.unusedSectionVars false

variable {n : ℕ} {Op Y : Type} [DecidableEq Op] [DecidableEq Y] [Inhabited Op] [Inhabited Y]

/-- An infinite (or finite) execution. -/
structure InfExec (n : ℕ) (Op Y : Type) where
  len : Fin n → ℕ∞
  op : Fin n → ℕ → Op
  y : Fin n → ℕ → Y
  T : Fin n → ℕ → ℕ

namespace InfExec

/-- Well-formedness: steps of a process in order, distinct steps at distinct times. -/
structure WF (E : InfExec n Op Y) : Prop where
  mono : ∀ p (i j : ℕ), i < j → (j : ℕ∞) < E.len p → E.T p i < E.T p j
  inj : ∀ p q (i j : ℕ), (i : ℕ∞) < E.len p → (j : ℕ∞) < E.len q → E.T p i = E.T q j → p = q ∧ i = j

variable {E : InfExec n Op Y}

/-- The prefix of the steps before time `t`. -/
def pre (E : InfExec n Op Y) (t : ℕ) : Exec n Op Y ℕ :=
  ⟨fun p => ((List.range t).filter (fun (i : ℕ) => decide (((i : ℕ) : ℕ∞) < E.len p ∧ E.T p i < t))).length,
    E.op, E.y, E.T⟩

theorem le_T (hw : E.WF) {p : Fin n} : ∀ {i : ℕ}, (i : ℕ∞) < E.len p → i ≤ E.T p i
  | 0, _ => Nat.zero_le _
  | i + 1, h => by
    have h' : (i : ℕ∞) < E.len p := lt_trans (by exact_mod_cast Nat.lt_succ_self i) h
    have := le_T hw h'
    have := hw.mono p i (i + 1) (Nat.lt_succ_self i) h
    omega

theorem lt_pre_len (hw : E.WF) (t : ℕ) (p : Fin n) (i : ℕ) :
    i < (E.pre t).len p ↔ (i : ℕ∞) < E.len p ∧ E.T p i < t := by
  simp only [pre]
  rw [TH.lt_length_filter_range _ (fun a b hab hb h => by
    simp only [decide_eq_true_eq] at h ⊢
    exact ⟨lt_trans (by exact_mod_cast hab) h.1, lt_trans (hw.mono p a b hab h.1) h.2⟩)]
  simp only [decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨lt_of_le_of_lt (le_T hw h.1) h.2, h⟩

theorem pre_WF (hw : E.WF) (t : ℕ) : (E.pre t).WF where
  mono p i j hij hj := hw.mono p i j hij ((lt_pre_len hw t p j).1 hj).1
  inj p q i j hi hj := hw.inj p q i j ((lt_pre_len hw t p i).1 hi).1 ((lt_pre_len hw t q j).1 hj).1

theorem pre_cut (hw : E.WF) {t t' : ℕ} (h : t' ≤ t) : (E.pre t).cut t' = E.pre t' := by
  have hl : ∀ p, ((E.pre t).cut t').len p = (E.pre t').len p := fun p =>
    eq_of_forall_lt_iff fun i => by
      rw [Exec.lt_cut_len (pre_WF hw t), lt_pre_len hw, lt_pre_len hw]
      change ((i : ℕ∞) < E.len p ∧ E.T p i < t) ∧ E.T p i < t' ↔ _
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  exact congrArg (fun l => (⟨l, E.op, E.y, E.T⟩ : Exec n Op Y ℕ)) (funext hl)

/-- The `k`-th test of `p` reports `ERROR`. -/
def Reports (E : InfExec n Op Y) (O : Set (Hist (Fin n) Op Y)) (p : Fin n) (k : ℕ) : Prop :=
  (E.pre (E.T p (8 * k + 7) + 1)).Reports O p k

theorem reports_pre_iff (hw : E.WF) {O : Set (Hist (Fin n) Op Y)} {p : Fin n} {k t : ℕ}
    (h1 : ((8 * k + 7 : ℕ) : ℕ∞) < E.len p) (ht : E.T p (8 * k + 7) < t) :
    (E.pre t).Reports O p k ↔ E.Reports O p k := by
  rw [Reports, ← pre_cut hw (show E.T p (8 * k + 7) + 1 ≤ t by omega)]
  exact (Exec.reports_cut_iff (pre_WF hw t) ((lt_pre_len hw t p _).2 ⟨h1, ht⟩)
    (Nat.lt_succ_self _)).symm

/-- **Theorem 8.1, soundness for correct executions of `A`** (infinite executions): if every
finite prefix of the history of `A` belongs to `O`, nobody reports `ERROR`. -/
theorem no_report_of_correct {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hw : E.WF)
    (hA : ∀ t, ((E.pre t).hA 8).toList ∈ O) (p : Fin n) (k : ℕ) : ¬ E.Reports O p k := by
  intro hr
  set F := E.pre (E.T p (8 * k + 7) + 1)
  have hwF := pre_WF hw (E.T p (8 * k + 7) + 1)
  have hT : (F.hTy 8).toList ∈ O :=
    GenLin.mem_of_simTH hO (Exec.hTy_WF hwF) (Exec.hA_WF hwF)
      (Exec.simTH_T_A hwF (by norm_num) _) (hA _)
  exact hr.2 (Exec.sketch_mem_of_tight hO hwF hT _)

/-- **Theorem 8.1, completeness and stability** (infinite executions, Definition 6.1). Assume
that every process that took its `N.Snapshot` also writes its tuple to `M` (no crash in the
wait-free code), and that tests happen at arbitrarily late times. If some finite prefix of the
history of `A*` is not in `O`, then from some time on *every* test reports `ERROR`, and there is
such a test. -/
theorem thm_8_1_infinite {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hw : E.WF)
    (hfair : ∀ p k, ((8 * k + 4 : ℕ) : ℕ∞) < E.len p → ((8 * k + 6 : ℕ) : ℕ∞) < E.len p)
    (hprog : ∀ t, ∃ p k, ((8 * k + 7 : ℕ) : ℕ∞) < E.len p ∧ t ≤ E.T p (8 * k + 7))
    {t₀ : ℕ} (hbad : ((E.pre t₀).hSy 8).toList ∉ O) :
    ∃ t₁, (∃ p k, ((8 * k + 7 : ℕ) : ℕ∞) < E.len p ∧ t₁ ≤ E.T p (8 * k + 7)) ∧
      ∀ p k, ((8 * k + 7 : ℕ) : ℕ∞) < E.len p → t₁ ≤ E.T p (8 * k + 7) → E.Reports O p k := by
  set D : Finset (Fin n × ℕ) := (Finset.univ : Finset (Fin n)).biUnion fun p =>
    (Finset.range (cnt 8 4 ((E.pre t₀).len p))).image fun k => (p, k)
  set t₁ := max t₀ (D.sup fun x => E.T x.1 (8 * x.2 + 6) + 1)
  refine ⟨t₁, hprog t₁, fun p k hk ht => ?_⟩
  set s := E.T p (8 * k + 7)
  set F := E.pre (s + 1)
  have hwF := pre_WF hw (s + 1)
  have hkF : 8 * k + 7 < F.len p := (lt_pre_len hw _ p _).2 ⟨hk, Nat.lt_succ_self _⟩
  refine ⟨hkF, fun hX => hbad ?_⟩
  have H : ∀ q j, 8 * j + 4 < F.len q → E.T q (8 * j + 4) < t₀ →
      8 * j + 6 < F.len q ∧ E.T q (8 * j + 6) < s := by
    intro q j hj hjt
    have hj' := ((lt_pre_len hw _ q _).1 hj).1
    have hD : (q, j) ∈ D := by
      simp only [D, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_range, Prod.mk.injEq]
      exact ⟨q, j, (lt_cnt (by norm_num)).2 ((lt_pre_len hw _ q _).2 ⟨hj', hjt⟩), rfl, rfl⟩
    have h6 := hfair q j hj'
    have hle : E.T q (8 * j + 6) + 1 ≤ t₁ :=
      le_trans (Finset.le_sup (f := fun x : Fin n × ℕ => E.T x.1 (8 * x.2 + 6) + 1) hD)
        (le_max_right _ _)
    have hs : E.T q (8 * j + 6) < s := by omega
    exact ⟨(lt_pre_len hw _ q _).2 ⟨h6, by omega⟩, hs⟩
  have := Exec.cut_mem_of_sketch hO hwF H hX
  have e1 : (F.cut t₀).hSy 8 = (F.hSy 8).cut t₀ := Exec.proj_cut hwF t₀ _ (by norm_num) (by norm_num)
  rwa [← e1,
    show F.cut t₀ = E.pre t₀ from pre_cut hw (by
      have : t₀ ≤ t₁ := le_max_left _ _
      omega)] at this

end InfExec

end Podc2023.RuntimeVerification
