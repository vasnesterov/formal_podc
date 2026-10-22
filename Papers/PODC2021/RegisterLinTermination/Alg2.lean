import Podc.Computability.Distributed.SharedMemory.WriteStrongLin
import Papers.PODC2021.RegisterLinTermination.Alg4
import Mathlib.Tactic.FinCases

/-!
# Algorithm 2: a write strongly-linearizable MWMR register from SWMR registers

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Section 4.

```
Shared: Val[i], i = 1..n: SWMR register, initially (0, [0, …, 0])
Local:  new_ts, initially [∞, …, ∞]
write(v) by p_k:  for i = 1..n: new_ts[i] ← Val[i].ts[i] (+ 1 if i = k)
                  Val[k] ← (v, new_ts); new_ts ← [∞, …, ∞]; return done
read():           for i = 1..n: (v_i, ts_i) ← Val[i]
                  return v_j with ts_j the lexicographic maximum
```

## Modelling

* Processes and registers `Val[i]` are indexed by `Fin n`; a vector timestamp is a `List ℕ` (of
  length `n` once complete), compared lexicographically (`List.lt`). While a write is computing its
  timestamp, the local state holds the prefix `pre` computed so far: the paper's `new_ts` is
  `pre` padded with `∞`.
* One base-object access per step. A `write v` returns `v` (CSLib's dummy write response).
* The read keeps the best cell seen so far, starting from `(v₀, [0, …, 0])`, the least timestamp.

## Corollary 11

The paper derives Corollary 11 (Algorithm 2 is not strongly linearizable) from the impossibility
result of Helmi, Higham and Woelfel (PODC 2012). We prove it directly
(`alg2_not_stronglyLinearizable`, three processes, values in `ℕ`): in `G`, a read by `p₃` has
read `Val[1]` (initial) when `p₁` runs `write 1` to completion. If the read then returns `0`
(`H₁`), it must be linearized before `write 1`, hence already in `f(G)`; if instead `p₂` first runs
`write 2` and the read returns `2` (`H₂`), it must be linearized after `write 2`, which follows
`write 1`.
-/

namespace Podc.RegisterLinTermination.Alg2

open Cslib.SharedMemory List

/-- Contents of a register `Val[i]`: a value with its vector timestamp. -/
abbrev Cell (V : Type) := V × List ℕ

/-- The base objects `Val[i]` (the `ObjSpec` initial value is ignored; see `memInit`). -/
abbrev base (V : Type) (v₀ : V) (n : ℕ) : Fin n → ObjSpec :=
  fun _ => register (Cell V) (v₀, [])

/-- Local states (program counters with local variables). -/
inductive Loc (V : Type) (n : ℕ) where
  | idle
  /-- writing `v`: about to read `Val[i]`; `pre` = the components `new_ts[1..i-1]` computed so
  far (the remaining components of `new_ts` are `∞`) -/
  | wRead (v : V) (i : Fin n) (pre : List ℕ)
  /-- writing `v`: about to write `(v, ts)` into `Val[k]` -/
  | wWrite (v : V) (ts : List ℕ)
  | wRet (v : V)
  /-- reading: about to read `Val[i]`; `best` is the cell with the largest timestamp so far -/
  | rRead (i : Fin n) (best : Cell V)
  | rRet (v : V)

variable {V : Type} (v₀ : V) {n : ℕ} [NeZero n]

/-- The code of process `p_k`. -/
def act (k : Fin n) : Loc V n → Action (register V v₀) (base V v₀ n) (Loc V n)
  | .idle => .ret v₀ .idle
  | .wRead v i pre => .access i .read (fun c =>
      match Alg4.next i with
      | some j => .wRead v j (pre ++ [c.2.getD i 0 + if i = k then 1 else 0])
      | none => .wWrite v (pre ++ [c.2.getD i 0 + if i = k then 1 else 0]))
  | .wWrite v ts => .access k (.write (v, ts)) (fun _ => .wRet v)
  | .wRet v => .ret v .idle
  | .rRead i best => .access i .read (fun c =>
      match Alg4.next i with
      | some j => .rRead j (if best.2 < c.2 then c else best)
      | none => .rRet (if best.2 < c.2 then c else best).1)
  | .rRet v => .ret v .idle

/-- Invocation. -/
def invoke : RWOp V → Loc V n
  | .write v => .wRead v 0 []
  | .read => .rRead 0 (v₀, replicate n 0)

/-- **Algorithm 2** of the paper, for `n` processes. -/
def alg2 (V : Type) (v₀ : V) (n : ℕ) [NeZero n] :
    Impl (register V v₀) (base V v₀ n) (Fin n) (Loc V n) where
  memInit _ := (v₀, replicate n 0)
  locInit _ := .idle
  invoke _ _ o := invoke v₀ o
  act k l := act v₀ k l

instance (p : Fin n) (o : RWOp V) : Decidable ((alg2 V v₀ n).allowed p o) :=
  inferInstanceAs (Decidable True)

/-! ## Corollary 11 -/

section Cor11

/-- `G`: `p₃` (process `2`) starts a read and reads `Val[1]`; then `p₁` (process `0`) runs
`write 1` to completion (timestamp `[1, 0, 0]`). -/
def histG : List (Label (Fin 3) (register ℕ 0)) :=
  [.inv 2 .read, .tau 2, .inv 0 (.write 1), .tau 0, .tau 0, .tau 0, .tau 0, .ret 0 1]

/-- `H₁`: the read reads `Val[2]`, `Val[3]` and returns the initial value `0`. -/
def histH₁ : List (Label (Fin 3) (register ℕ 0)) := histG ++ [.tau 2, .tau 2, .ret 2 0]

/-- `H₂`: `p₂` runs `write 2` to completion (timestamp `[1, 1, 0]`); then the read reads
`Val[2]`, `Val[3]` and returns `2`. -/
def histH₂ : List (Label (Fin 3) (register ℕ 0)) :=
  histG ++ [.inv 1 (.write 2), .tau 1, .tau 1, .tau 1, .tau 1, .ret 1 2, .tau 2, .tau 2, .ret 2 2]

lemma valid_H₁ : (alg2 ℕ 0 3).Valid histH₁ := by
  apply Impl.valid_of_crun; decide +kernel

lemma valid_H₂ : (alg2 ℕ 0 3).Valid histH₂ := by
  apply Impl.valid_of_crun; decide +kernel

lemma opsOf_H₁ : ∀ p : Fin 3, opsOf histH₁ p =
    if p = 0 then [.write 1] else if p = 1 then [] else [.read] := by decide

lemma opsOf_H₂ : ∀ p : Fin 3, opsOf histH₂ p =
    if p = 0 then [.write 1] else if p = 1 then [.write 2] else [.read] := by decide

lemma opOf_H₁_ne_write0 (x : OpId (Fin 3)) (h : opOf histH₁ x = some (.write 0)) : False := by
  obtain ⟨p, k⟩ := x
  simp only [opOf, opsOf_H₁] at h
  fin_cases p <;> rcases k with _ | k <;> simp_all

lemma opOf_H₂_write2 (x : OpId (Fin 3)) (h : opOf histH₂ x = some (.write 2)) : x = (1, 0) := by
  obtain ⟨p, k⟩ := x
  simp only [opOf, opsOf_H₂] at h
  fin_cases p <;> rcases k with _ | k <;> simp_all

/-- **Corollary 11** (Hadzilacos–Hu–Toueg, PODC 2021). Algorithm 2 is not a strongly
linearizable implementation of a MWMR register (for three processes and natural-number values
with initial value `0`). Proved directly, without the impossibility result of Helmi et al. -/
theorem alg2_not_stronglyLinearizable : ¬ (alg2 ℕ 0 3).StronglyLinearizable := by
  rintro ⟨f, hf, hpre⟩
  have hvG : (alg2 ℕ 0 3).Valid histG := (alg2 ℕ 0 3).valid_of_prefix valid_H₁ (prefix_append _ _)
  have hLG := hf _ hvG
  have hL₁ := hf _ valid_H₁
  have hL₂ := hf _ valid_H₂
  have hpre₁ := (hpre _ _ valid_H₁ (prefix_append _ _)).map Prod.fst
  have hpre₂ := (hpre _ _ valid_H₂ (prefix_append _ _)).map Prod.fst
  -- in `H₁`, the read is linearized before `write 1`
  have h₁ : [((2 : Fin 3), 0), ((0 : Fin 3), 0)].Sublist ((f histH₁).map Prod.fst) :=
    hL₁.read_before_of_init (u := (0, 0)) (x := 1) (by decide) (by decide)
      (fun y hy hyw => opOf_H₁_ne_write0 _ (hyw ▸ hL₁.op_eq y hy)) (hL₁.complete _ (by decide))
      (Alg4.mem_of_completed hL₁ (by decide) (by decide))
  -- hence already in `f(G)`, and in `f(H₂)`
  have hG : [((2 : Fin 3), 0), ((0 : Fin 3), 0)].Sublist ((f histG).map Prod.fst) :=
    sublist_pair_of_prefix hpre₁ hL₁.nodup h₁ (hLG.complete _ (by decide))
  have h₂ := hG.trans hpre₂.sublist
  -- in `H₂`, `write 1` precedes `write 2`, which is linearized before the read
  have h₃ : [((0 : Fin 3), 0), ((1 : Fin 3), 0)].Sublist ((f histH₂).map Prod.fst) :=
    hL₂.realtime _ _ (by decide) (hL₂.complete _ (by decide))
  have h₄ : [((1 : Fin 3), 0), ((2 : Fin 3), 0)].Sublist ((f histH₂).map Prod.fst) :=
    hL₂.writer_before_read (v := 2) (by decide) (by decide) (by decide)
      (fun y hy hyw => opOf_H₂_write2 _ (hyw ▸ hL₂.op_eq y hy)) (hL₂.complete _ (by decide))
  exact not_sublist_pair_both hL₂.nodup (sublist_pair_trans hL₂.nodup h₃ h₄) h₂

end Cor11

end Podc.RegisterLinTermination.Alg2
