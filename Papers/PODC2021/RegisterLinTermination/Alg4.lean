import Podc.Computability.Distributed.SharedMemory.WriteStrongLin
import Mathlib.Tactic.FinCases

/-!
# Algorithm 4: an MWMR register from SWMR registers with Lamport clocks

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Section 5.

```
Shared: Val[i], i = 1..n: SWMR register, initially (0, ⟨0, i⟩)
write(v) by p_k:  for i = 1..n: (v_i, ts_i) ← Val[i]
                  new_sq ← max{ts_1.sq, …, ts_n.sq} + 1
                  Val[k] ← (v, ⟨new_sq, k⟩); return done
read():           for i = 1..n: (v_i, ts_i) ← Val[i]
                  return v_j with ts_j the lexicographic maximum
```

## Modelling

* Processes and registers `Val[i]` are indexed by `Fin n`; a timestamp is a pair `(sq, pid)`
  compared lexicographically (`tsLt`). The registers `Val[i]` are base registers of CSLib's
  shared-memory model; they are single-writer by the code (only `p_k` writes `Val[k]`).
* One base-object access per step. The implemented object is `register V v₀`; a `write v`
  returns `v` (CSLib's dummy write response), a `read` returns the value.
* The read keeps the best cell seen so far, starting from `(v₀, (0, 0))`, which is below every
  timestamp (the paper takes the maximum of the `n` cells read; this is the same).

## Theorem 13

`alg4_not_writeStronglyLinearizable`: for `n = 3` processes and values in `ℕ` (initially `0`),
Algorithm 4 is not write strongly-linearizable. The histories `G`, `H₁` (Case 1) and `H₂`
(Case 2) are exactly those of the paper's proof: `w₁ = write 1` by `p₁` reads `Val[1]`, `Val[2]`;
`w₂ = write 2` by `p₂` runs to completion. In `H₁`, `w₁` completes and a read returns `2`, forcing
`w₁` before `w₂`; in `H₂`, `p₃` first writes `3`, then `w₁` completes and a read returns `1`,
forcing `w₂` before `w₁`. A write strong-linearization function would have to fix the order of
`w₁` and `w₂` already in `f(G)`.
-/

namespace Podc.RegisterLinTermination.Alg4

open Cslib.SharedMemory List

/-- Timestamps `⟨sq, pid⟩`. -/
abbrev TS (n : ℕ) := ℕ × Fin n

/-- Lexicographic order on timestamps. -/
def tsLt {n : ℕ} (a b : TS n) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))

/-- Contents of a register `Val[i]`: a value with its timestamp. -/
abbrev Cell (V : Type) (n : ℕ) := V × TS n

/-- The base objects `Val[i]` (the initial value of the `ObjSpec` is ignored by CSLib; the
initial memory is `memInit`). -/
abbrev base (V : Type) (v₀ : V) (n : ℕ) [NeZero n] : Fin n → ObjSpec :=
  fun _ => register (Cell V n) (v₀, 0, 0)

/-- Local states (program counters with local variables). -/
inductive Loc (V : Type) (n : ℕ) where
  | idle
  /-- writing `v`: about to read `Val[i]`; `m` is the largest `sq` read so far -/
  | wRead (v : V) (i : Fin n) (m : ℕ)
  /-- writing `v`: about to write `(v, ⟨m + 1, k⟩)` into `Val[k]` -/
  | wWrite (v : V) (m : ℕ)
  | wRet (v : V)
  /-- reading: about to read `Val[i]`; `best` is the cell with the largest timestamp so far -/
  | rRead (i : Fin n) (best : Cell V n)
  | rRet (v : V)

/-- The next register index. -/
def next {n : ℕ} (i : Fin n) : Option (Fin n) :=
  if h : i.val + 1 < n then some ⟨i.val + 1, h⟩ else none

variable {V : Type} (v₀ : V) {n : ℕ} [NeZero n]

/-- The code of process `p_k`. -/
def act (k : Fin n) : Loc V n → Action (register V v₀) (base V v₀ n) (Loc V n)
  | .idle => .ret v₀ .idle
  | .wRead v i m => .access i .read (fun c =>
      match next i with
      | some j => .wRead v j (max m c.2.1)
      | none => .wWrite v (max m c.2.1))
  | .wWrite v m => .access k (.write (v, m + 1, k)) (fun _ => .wRet v)
  | .wRet v => .ret v .idle
  | .rRead i best => .access i .read (fun c =>
      match next i with
      | some j => .rRead j (if tsLt best.2 c.2 then c else best)
      | none => .rRet (if tsLt best.2 c.2 then c else best).1)
  | .rRet v => .ret v .idle

/-- Invocation. -/
def invoke : RWOp V → Loc V n
  | .write v => .wRead v 0 0
  | .read => .rRead 0 (v₀, 0, 0)

/-- **Algorithm 4** of the paper, for `n` processes. -/
def alg4 (V : Type) (v₀ : V) (n : ℕ) [NeZero n] :
    Impl (register V v₀) (base V v₀ n) (Fin n) (Loc V n) where
  memInit i := (v₀, 0, i)
  locInit _ := .idle
  invoke _ _ o := invoke v₀ o
  act k l := act v₀ k l

instance (p : Fin n) (o : RWOp V) : Decidable ((alg4 V v₀ n).allowed p o) :=
  inferInstanceAs (Decidable True)

/-! ## Theorem 13 -/

section Thm13

/-- `G`: `w₁ = write 1` by `p₁` reads `Val[1]`, `Val[2]`; then `w₂ = write 2` by `p₂` runs to
completion (it writes `(2, ⟨1, 2⟩)` into `Val[2]`). (Processes `p₁, p₂, p₃` are `0, 1, 2`.) -/
def histG : List (Label (Fin 3) (register ℕ 0)) :=
  [.inv 0 (.write 1), .tau 0, .tau 0,
   .inv 1 (.write 2), .tau 1, .tau 1, .tau 1, .tau 1, .ret 1 2]

/-- Case 1: `w₁` completes (it writes `(1, ⟨1, 1⟩)`), then `p₃` reads and returns `2`. -/
def histH₁ : List (Label (Fin 3) (register ℕ 0)) :=
  histG ++ [.tau 0, .tau 0, .ret 0 1, .inv 2 .read, .tau 2, .tau 2, .tau 2, .ret 2 2]

/-- Case 2: `p₃` writes `3` (with `⟨2, 3⟩`), then `w₁` completes (it writes `(1, ⟨3, 1⟩)`), then
`p₃` reads and returns `1`. -/
def histH₂ : List (Label (Fin 3) (register ℕ 0)) :=
  histG ++ [.inv 2 (.write 3), .tau 2, .tau 2, .tau 2, .tau 2, .ret 2 3,
    .tau 0, .tau 0, .ret 0 1, .inv 2 .read, .tau 2, .tau 2, .tau 2, .ret 2 1]

lemma valid_H₁ : (alg4 ℕ 0 3).Valid histH₁ := by
  apply Impl.valid_of_crun; decide +kernel

lemma valid_H₂ : (alg4 ℕ 0 3).Valid histH₂ := by
  apply Impl.valid_of_crun; decide +kernel

lemma opsOf_H₁ : ∀ p : Fin 3, opsOf histH₁ p =
    if p = 0 then [.write 1] else if p = 1 then [.write 2] else [.read] := by decide

lemma opsOf_H₂ : ∀ p : Fin 3, opsOf histH₂ p =
    if p = 0 then [.write 1] else if p = 1 then [.write 2] else [.write 3, .read] := by decide

lemma opOf_H₁_write2 (x : OpId (Fin 3)) (h : opOf histH₁ x = some (.write 2)) : x = (1, 0) := by
  obtain ⟨p, k⟩ := x
  simp only [opOf, opsOf_H₁] at h
  fin_cases p <;> rcases k with _ | k <;> simp_all

lemma opOf_H₂_write1 (x : OpId (Fin 3)) (h : opOf histH₂ x = some (.write 1)) : x = (0, 0) := by
  obtain ⟨p, k⟩ := x
  simp only [opOf, opsOf_H₂] at h
  fin_cases p <;> rcases k with _ | _ | k <;> simp_all

lemma nodup_opsFor {P Op : Type} {S : List (OpId P × Op)} (h : (S.map Prod.fst).Nodup)
    (O : Op → Bool) : (opsFor O S).Nodup :=
  (h.of_map _).filter _

/-- An operation that is completed in `α` appears in every linearization of `α` with its
operation. -/
lemma mem_of_completed {P : Type} [DecidableEq P] {A : ObjSpec} {α : List (Label P A)}
    {S : List (OpId P × A.Op)} (hS : IsLinearization α S) {x : OpId P} {o : A.Op}
    (hc : Completed α x) (ho : opOf α x = some o) : (x, o) ∈ S := by
  obtain ⟨⟨x', o'⟩, hy, rfl⟩ := mem_map.1 (hS.complete x hc)
  have := hS.op_eq _ hy
  rw [ho] at this; cases this; exact hy

/-- **Theorem 13** (Hadzilacos–Hu–Toueg, PODC 2021). Algorithm 4 is not a write
strongly-linearizable implementation of a MWMR register (for three processes and natural-number
values with initial value `0`). -/
theorem alg4_not_writeStronglyLinearizable : ¬ (alg4 ℕ 0 3).WriteStronglyLinearizable := by
  rintro ⟨f, hf, hpre⟩
  have hvG : (alg4 ℕ 0 3).Valid histG := (alg4 ℕ 0 3).valid_of_prefix valid_H₁ (prefix_append _ _)
  have hLG := hf _ hvG
  have hL₁ := hf _ valid_H₁
  have hL₂ := hf _ valid_H₂
  -- the two writes
  set e₁ : OpId (Fin 3) × RWOp ℕ := ((0, 0), .write 1)
  set e₂ : OpId (Fin 3) × RWOp ℕ := ((1, 0), .write 2)
  have he₂G : e₂ ∈ opsFor RWOp.isWrite (f histG) :=
    mem_filter.2 ⟨mem_of_completed hLG (by decide) (by decide), rfl⟩
  by_cases hc : [e₁, e₂].Sublist (opsFor RWOp.isWrite (f histG))
  · -- Case 2: `w₁` before `w₂` in `f(G)`; in `H₂` the read forces `w₂` before `w₁`
    have h₂ : [e₂, e₁].Sublist (opsFor RWOp.isWrite (f histH₂)) := by
      refine hL₂.write_before_of_read (r := (2, 1)) (by decide) (by decide) (by decide)
        (fun y hy hyw => opOf_H₂_write1 _ (hyw ▸ hL₂.op_eq y hy))
        (mem_of_completed hL₂ (by decide) (by decide)) (by decide) ?_
      exact hL₂.realtime _ _ (by decide) (hL₂.complete _ (by decide))
    have h₁ : [e₁, e₂].Sublist (opsFor RWOp.isWrite (f histH₂)) :=
      hc.trans (hpre _ _ valid_H₂ (prefix_append _ _)).sublist
    exact not_sublist_pair_both (nodup_opsFor hL₂.nodup _) h₁ h₂
  · -- Case 1: `w₁` not before `w₂` in `f(G)`; in `H₁` the read forces `w₁` before `w₂`
    apply hc
    refine sublist_pair_of_prefix (hpre _ _ valid_H₁ (prefix_append _ _))
      (nodup_opsFor hL₁.nodup _) ?_ he₂G
    refine hL₁.write_before_of_read (r := (2, 0)) (by decide) (by decide) (by decide)
      (fun y hy hyw => opOf_H₁_write2 _ (hyw ▸ hL₁.op_eq y hy))
      (mem_of_completed hL₁ (by decide) (by decide)) (by decide) ?_
    exact hL₁.realtime _ _ (by decide) (hL₁.complete _ (by decide))

end Thm13

end Podc.RegisterLinTermination.Alg4
