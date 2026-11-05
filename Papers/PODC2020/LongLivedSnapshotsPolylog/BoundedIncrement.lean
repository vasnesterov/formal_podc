import Papers.PODC2020.LongLivedSnapshotsPolylog.Algorithm
import Mathlib.Order.Basic
import Mathlib.Data.List.Basic

/-!
# `ℓ`-bounded-increment executions (Definition 2.1)

Definition 2.1 of the paper: an execution is `ℓ`-bounded-increment for a max register `M` if for
each `WriteMax(v)` on `M` with `v > ℓ` there is a `WriteMax(v')` on `M` that precedes it with
`v - ℓ ≤ v' < v`.

All max registers of our models are atomic, so a `WriteMax` is one step and "precedes" is the
order of the steps. The definition then only depends on the sequence `ws` of values written to
`M`, in order (`BoundedIncr ℓ ws`). We show that it is equivalent to the local condition "every
written value exceeds the maximum of the earlier ones (or `0`) by at most `ℓ`"
(`boundedIncr_iff_stepBounded`); the direction `←` is the argument with `w*` at the end of the
proof of Lemma 4.1.

`wlogFrom I w C α` is the log of all writes performed along the execution `α` from `C`, where
`w p l = some (k, v)` says that process `p` in local state `l` is about to write `v` to the max
register with key `k`; `writesTo I w α k` is the sequence of values written to the register `k`.
-/

namespace Podc.LongLivedSnapshotsPolylog

open Cslib.SharedMemory

/-- Maximum of a list of naturals (`0` for the empty list). -/
def lmax (ws : List ℕ) : ℕ := ws.foldr max 0

@[simp] lemma lmax_nil : lmax [] = 0 := rfl

@[simp] lemma lmax_cons (a : ℕ) (ws : List ℕ) : lmax (a :: ws) = max a (lmax ws) := rfl

lemma lmax_append (as bs : List ℕ) : lmax (as ++ bs) = max (lmax as) (lmax bs) := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, max_assoc]

lemma le_lmax {a : ℕ} {ws : List ℕ} (h : a ∈ ws) : a ≤ lmax ws := by
  induction ws with
  | nil => cases h
  | cons b ws ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · simp [ih h]

lemma lmax_mem {ws : List ℕ} (h : 0 < lmax ws) : lmax ws ∈ ws := by
  induction ws with
  | nil => simp at h
  | cons b ws ih =>
    simp only [lmax_cons] at h ⊢
    rcases le_total b (lmax ws) with hb | hb
    · rw [max_eq_right hb] at h ⊢
      exact List.mem_cons_of_mem _ (ih h)
    · rw [max_eq_left hb]; exact List.mem_cons_self

/-- **Definition 2.1** for an atomic max register, on the sequence `ws` of written values. -/
def BoundedIncr (ℓ : ℕ) (ws : List ℕ) : Prop :=
  ∀ i (hi : i < ws.length), ℓ < ws[i] → ∃ j, ∃ hj : j < i, ws[i] - ℓ ≤ ws[j] ∧ ws[j] < ws[i]

/-- Local version: every written value is at most the maximum of the earlier ones plus `ℓ`. -/
def StepBounded (ℓ : ℕ) (ws : List ℕ) : Prop :=
  ∀ i (hi : i < ws.length), ws[i] ≤ lmax (ws.take i) + ℓ

lemma stepBounded_of_boundedIncr {ℓ : ℕ} {ws : List ℕ} (h : BoundedIncr ℓ ws) :
    StepBounded ℓ ws := by
  intro i hi
  by_cases hv : ℓ < ws[i]
  · obtain ⟨j, hj, h1, -⟩ := h i hi hv
    have : ws[j] ≤ lmax (ws.take i) :=
      le_lmax (List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩)
    omega
  · omega

lemma boundedIncr_of_stepBounded {ℓ : ℕ} {ws : List ℕ} (h : StepBounded ℓ ws) :
    BoundedIncr ℓ ws := by
  intro i hi hv
  classical
  -- `w*`: the first written value `≥ ws[i]`
  have hex : ∃ k, ∃ hk : k < ws.length, ws[i] ≤ ws[k] := ⟨i, hi, le_rfl⟩
  obtain ⟨k, ⟨hk, hk2⟩, hmin', hki⟩ : ∃ k, (∃ hk : k < ws.length, ws[i] ≤ ws[k]) ∧
      (∀ j < k, ¬ ∃ hk : j < ws.length, ws[i] ≤ ws[j]) ∧ k ≤ i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj,
      Nat.find_min' hex ⟨hi, le_rfl⟩⟩
  have hmin : ∀ j (hj : j < k), ∀ hj' : j < ws.length, ws[j] < ws[i] := by
    intro j hj hj'
    have := hmin' j hj
    simp only [not_exists, not_le] at this
    exact this hj'
  have hs := h k hk
  set M := lmax (ws.take k)
  have hMpos : 0 < M := by
    by_contra h0
    have : M = 0 := by omega
    omega
  have hmem := lmax_mem hMpos
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.1 hmem
  simp only [List.length_take] at hj
  have hjk : j < k := by omega
  have hjl : j < ws.length := by omega
  refine ⟨j, by omega, ?_, ?_⟩
  · simp only [List.getElem_take] at hjv
    rw [hjv]; omega
  · simp only [List.getElem_take] at hjv
    exact hmin j hjk hjl

/-- Definition 2.1 is equivalent to its local version. -/
-- CSLib candidate
theorem boundedIncr_iff_stepBounded {ℓ : ℕ} {ws : List ℕ} :
    BoundedIncr ℓ ws ↔ StepBounded ℓ ws :=
  ⟨stepBounded_of_boundedIncr, boundedIncr_of_stepBounded⟩

section Log

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
variable {κ : Type}

/-- The writes to max registers performed along `α` from `C`: `w p l = some (k, v)` iff process
`p` in local state `l` is about to perform `WriteMax(v)` on the register with key `k`. -/
-- CSLib candidate
noncomputable def wlogFrom (I : Impl A B P L) (w : P → L → Option (κ × ℕ)) :
    Config A B P L → List (Label P A) → List (κ × ℕ)
  | _, [] => []
  | C, ℓ :: α =>
    match I.step C ℓ with
    | none => []
    | some C' =>
      (match ℓ with
        | .tau p => (w p (C.loc p)).toList
        | _ => []) ++ wlogFrom I w C' α

/-- The sequence of values written to the max register with key `k` along `α`. -/
noncomputable def writesTo [DecidableEq κ] (I : Impl A B P L) (w : P → L → Option (κ × ℕ))
    (α : List (Label P A)) (k : κ) : List ℕ :=
  (wlogFrom I w I.initCfg α).filterMap (fun e => if e.1 = k then some e.2 else none)

end Log

section Alg1

variable {n : ℕ}

/-- The `WriteMax` of line 4 that process `p` of Algorithm 1 is about to perform: the side
(`false` = left, `true` = right) and the value. -/
def wm1 (_p : Fin n) (lc : Loc n) : Option (Bool × ℕ) :=
  match lc.pc with
  | .wm s v => some (s, v)
  | _ => none

/-- The execution `α` of Algorithm 1 is `ℓ`-bounded-increment (Definition 2.1) for both
`MR_left` and `MR_right`. -/
def BIExec (n m X ℓ : ℕ) (α : List (Label (Fin n) LimitedUseSnapshots.maxArrObj)) : Prop :=
  ∀ s : Bool, BoundedIncr ℓ (writesTo (alg1 n m X) wm1 α s)

end Alg1

end Podc.LongLivedSnapshotsPolylog
