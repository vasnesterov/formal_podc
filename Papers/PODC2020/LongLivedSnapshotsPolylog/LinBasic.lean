import Papers.PODC2020.LongLivedSnapshotsPolylog.Algorithm
import Papers.PODC2012.LimitedUseSnapshots.CriterionAux

/-!
# Linearizability of Algorithm 1: time-indexed configurations and monotonicity

We index the configurations of an execution `α` of `alg1 n m X` by time: `cfgAt α t` is the
configuration after the first `t` labels. Along a valid execution, `MR_left`, `MR_right`, every
`MA_j` (componentwise) and every timestamp `H[j].ts` are monotone in time (`mono_*`); for the
timestamps this uses the simple invariant `H[j].ts = ts_j` (`basicInv`).
-/

namespace Podc.LongLivedSnapshotsPolylog

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

variable {n m X : ℕ}

/-- Configurations of Algorithm 1. -/
abbrev Cfg (n : ℕ) := Config maxArrObj (objSpec n) (Fin n) (Loc n)

/-- Labels of executions of Algorithm 1. -/
abbrev Lbl (n : ℕ) := Label (Fin n) maxArrObj

/-- Value of `MR_left`. -/
def vL (C : Cfg n) : ℕ := C.mem .mrL
/-- Value of `MR_right`. -/
def vR (C : Cfg n) : ℕ := C.mem .mrR
/-- Value of `MA_j`. -/
def vMA (C : Cfg n) (j : ℕ) : ℕ × ℕ := C.mem (.ma j)
/-- Value of `H[j]`. -/
def vH (C : Cfg n) (j : Fin n) : HEntry := C.mem (.help j)

variable (m X) in
/-- The configuration after the first `t` labels of `α` (the initial configuration if that prefix
is not a valid execution). -/
-- CSLib candidate (time-indexed configurations)
noncomputable def cfgAt (α : List (Lbl n)) (t : ℕ) : Cfg n :=
  ((alg1 n m X).run (α.take t)).getD (alg1 n m X).initCfg

lemma cfgAt_append {α β : List (Lbl n)} {t : ℕ} (ht : t ≤ α.length) :
    cfgAt m X (α ++ β) t = cfgAt m X α t := by
  simp [cfgAt, List.take_append_of_le_length ht]

lemma cfgAt_length {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) :
    cfgAt m X α α.length = C := by
  simp [cfgAt, h]

lemma run_take_eq {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t : ℕ} (ht : t ≤ α.length) :
    (alg1 n m X).run (α.take t) = some (cfgAt m X α t) := by
  obtain ⟨C, hC⟩ := hv
  have : (alg1 n m X).Valid (α.take t) :=
    Impl.valid_of_prefix _ ⟨C, hC⟩ (List.take_prefix t α)
  obtain ⟨D, hD⟩ := this
  simp [cfgAt, hD]

lemma step_cfgAt {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t : ℕ} (ht : t < α.length) :
    (alg1 n m X).step (cfgAt m X α t) α[t] = some (cfgAt m X α (t + 1)) := by
  have h1 := run_take_eq hv (le_of_lt ht)
  have h2 := run_take_eq hv (Nat.succ_le_of_lt ht)
  rw [List.take_succ_eq_append_getElem ht, Impl.run_concat, h1, Option.bind_some] at h2
  exact h2

/-! ### The basic invariant -/

/-- `pend p = none` iff `p` is idle, and `H[j].ts = ts_j`. -/
def BasicInv (C : Cfg n) : Prop :=
  (∀ p, C.pend p = none ↔ (C.loc p).pc = .idle) ∧ ∀ j, (vH C j).1 = (C.loc j).ts

lemma retOf_ne_idle (cs : CS n) (v : ℕ × ℕ) : retOf cs v ≠ .idle := by
  unfold retOf; split <;> simp

lemma afterFail_ne_idle (i : Fin n) (cs : CS n) : afterFail X i cs ≠ .idle := by
  unfold afterFail; split_ifs <;> simp

lemma afterCollect_ne_idle (cs : CS n) (f : Bool) (acc : Fin n → HEntry) :
    afterCollect cs f acc ≠ .idle := by
  unfold afterCollect
  split
  · simp
  · split
    · exact retOf_ne_idle _ _
    · simp

/-- One step from a configuration satisfying the basic invariant: the invariant is preserved,
and `MR_left`, `MR_right`, every `MA_j` and every timestamp `H[j].ts` do not decrease. -/
lemma step_basic {C C' : Cfg n} {ℓ : Lbl n} (hI : BasicInv C)
    (hs : (alg1 n m X).step C ℓ = some C') :
    BasicInv C' ∧ vL C ≤ vL C' ∧ vR C ≤ vR C' ∧ (∀ j, vMA C j ≤ vMA C' j) ∧
      ∀ j, (vH C j).1 ≤ (vH C' j).1 := by
  obtain ⟨hI1, hI2⟩ := hI
  cases ℓ with
  | inv p o =>
    simp only [Impl.step] at hs
    split_ifs at hs with hc
    cases hs
    refine ⟨⟨fun q => ?_, fun j => ?_⟩, le_rfl, le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩
    · by_cases hq : q = p
      · subst hq; cases o <;> simp
      · simp [Function.update_of_ne hq, hI1 q]
    · by_cases hj : j = p
      · subst hj; cases o <;> simp [vH] at hI2 ⊢ <;> exact hI2 j
      · simp [Function.update_of_ne hj, vH] at hI2 ⊢; exact hI2 j
  | ret p r =>
    simp only [Impl.step] at hs
    split_ifs at hs with hc
    rcases hpc : (C.loc p).pc with _ | ⟨_ | _, _⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r' <;>
      simp [act, hpc] at hs
    · exact absurd ((hI1 p).2 hpc) hc
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨⟨fun q => ?_, fun j => ?_⟩, le_rfl, le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩
    · by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq, hI1 q]
    · by_cases hj : j = p
      · subst hj; simpa [vH] using hI2 j
      · simp [Function.update_of_ne hj, vH] at hI2 ⊢; exact hI2 j
  | tau p =>
    simp only [Impl.step] at hs
    split_ifs at hs with hc
    have hidle : (C.loc p).pc ≠ .idle := fun h => hc ((hI1 p).2 h)
    rcases hpc : (C.loc p).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
      ⟨cs, f, k, acc⟩ | r <;>
      simp [act, hpc] at hs <;> subst hs
    all_goals
      refine ⟨⟨fun q => ?_, fun j => ?_⟩, ?_, ?_, fun j => ?_, fun j => ?_⟩
    all_goals (try simp [vL, vR, vMA, vH, Function.update_apply])
    all_goals (try (split_ifs with h <;> (try subst h) <;>
      simp [vH, hc, hI1, afterFail_ne_idle, afterCollect_ne_idle, retOf_ne_idle] at hI2 ⊢ <;>
      (try simp [hI2]) <;> done))
    · rcases eq_or_ne j (idx m l r2) with h | h
      · subst h; simp [Prod.le_def]
      · rw [Function.update_of_ne (by simpa using h)]
    · rcases eq_or_ne j (idx m l r2) with h | h
      · subst h; simp [Prod.le_def]
      · rw [Function.update_of_ne (by simpa using h)]
    · rcases eq_or_ne j p with h | h
      · subst h; simp
      · rw [Function.update_of_ne (by simpa using h)]; simpa [h, vH] using hI2 j
    · rcases eq_or_ne j p with h | h
      · subst h; simp [vH] at hI2 ⊢; simp [hI2]
      · rw [Function.update_of_ne (by simpa using h)]

lemma basicInv_run {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) :
    BasicInv C := by
  refine Impl.invariant_of_run (Inv := BasicInv) ?_ (fun C ℓ C' hC hs => (step_basic hC hs).1) h
  refine ⟨fun p => ?_, fun j => ?_⟩
  · simp [Impl.initCfg]
  · simp [Impl.initCfg, vH, memInit]

lemma basicInv_cfgAt {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t : ℕ} (ht : t ≤ α.length) :
    BasicInv (cfgAt m X α t) :=
  basicInv_run (run_take_eq hv ht)

/-- Monotonicity in time of `MR_left`, `MR_right`, `MA_j` and `H[j].ts`. -/
lemma mono {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t t' : ℕ} (htt : t ≤ t')
    (ht' : t' ≤ α.length) :
    vL (cfgAt m X α t) ≤ vL (cfgAt m X α t') ∧ vR (cfgAt m X α t) ≤ vR (cfgAt m X α t') ∧
      (∀ j, vMA (cfgAt m X α t) j ≤ vMA (cfgAt m X α t') j) ∧
      ∀ j, (vH (cfgAt m X α t) j).1 ≤ (vH (cfgAt m X α t') j).1 := by
  induction t', htt using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩
  | succ k hk ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    obtain ⟨-, s1, s2, s3, s4⟩ :=
      step_basic (basicInv_cfgAt hv (by omega)) (step_cfgAt hv (t := k) (by omega))
    exact ⟨h1.trans s1, h2.trans s2, fun j => (h3 j).trans (s3 j), fun j => (h4 j).trans (s4 j)⟩

lemma monoL {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t t' : ℕ} (htt : t ≤ t')
    (ht' : t' ≤ α.length) : vL (cfgAt m X α t) ≤ vL (cfgAt m X α t') := (mono hv htt ht').1

lemma monoR {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t t' : ℕ} (htt : t ≤ t')
    (ht' : t' ≤ α.length) : vR (cfgAt m X α t) ≤ vR (cfgAt m X α t') := (mono hv htt ht').2.1

lemma monoMA {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t t' : ℕ} (htt : t ≤ t')
    (ht' : t' ≤ α.length) (j : ℕ) : vMA (cfgAt m X α t) j ≤ vMA (cfgAt m X α t') j :=
  (mono hv htt ht').2.2.1 j

lemma monoH {α : List (Lbl n)} (hv : (alg1 n m X).Valid α) {t t' : ℕ} (htt : t ≤ t')
    (ht' : t' ≤ α.length) (j : Fin n) :
    (vH (cfgAt m X α t) j).1 ≤ (vH (cfgAt m X α t') j).1 :=
  (mono hv htt ht').2.2.2 j

end Podc.LongLivedSnapshotsPolylog
