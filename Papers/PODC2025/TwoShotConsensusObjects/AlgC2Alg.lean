import Papers.PODC2025.TwoShotConsensusObjects.AlgC2Pad

/-!
# Class `C₂`, sufficiency: Algorithm 3

Algorithm 3 of the paper (consensus from one two-shot object of class `C₂`), for a witness
`s, f, g, c₀, …, c_N` with `N = 3 ^ k`, `k ≥ 1`. Code at `pᵢ`:

```
 Val[i] ← vᵢ;  v[i][0] ← O.(i = 0 ? f : g);  Ret[i] ← v[i][0]
 op ← i;  for cnt = 0 .. k-1:  Round[i][cnt] ← op;  other ← Round[1-i][cnt];
                               op ← (other ≠ ⊥) ? op + 2·other : 3·op
 Next_op[i] ← op;  v[i][1] ← O.c_op;  v[1-i][0] ← Ret[1-i];  nx ← Next_op[1-i]
 decision (lines 23–39, `decideC2`), then read and return `Val[j]`.
```

with the correction of line 30 (`v[0][1]`, the second response of `p₀`, instead of `v[1][1]`).

Shared objects: one copy of `O` (index `Sum.inr ()`, initially in state `s`) and registers
(index `Sum.inl r`, `r : Reg`), all of the same type `register (RV O.Resp) .bot` (a register
holding a tagged value; `⊥ = .bot`).

The local state `LS` is a record with a program counter `pc` (`0 … 10`). It remembers the list
`rs` of the values read in the rounds of the loop (instead of only `cnt` and `op`; `cnt` is
`rs.length` and `op` is `opOf i rs`). This extra local memory does not change the behaviour.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

/-- Register indices of Algorithm 3. -/
inductive Reg where
  | val (j : Fin 2)
  | ret (j : Fin 2)
  | round (j : Fin 2) (r : ℕ)
  | next (j : Fin 2)
  deriving DecidableEq

/-- Register contents (`bot` is `⊥`). -/
inductive RV (ρ : Type) where
  | bot
  | b (x : Bool)
  | r (x : Option ρ)
  | n (x : ℕ)

namespace RV

variable {ρ : Type}

/-- Decode a natural number (`none` for `⊥`). -/
def nat : RV ρ → Option ℕ
  | .n x => some x
  | _ => none

/-- Decode a response (`none` for `⊥`). -/
def resp : RV ρ → Option ρ
  | .r x => x
  | _ => none

/-- Decode a boolean. -/
def bool : RV ρ → Bool
  | .b x => x
  | _ => false

end RV

/-- The register specification. -/
abbrev RegS (ρ : Type) : Reg → ObjSpec := fun _ => register (RV ρ) .bot

/-- Local states of Algorithm 3. -/
structure LS (ρ : Type) where
  /-- the process identifier `i` -/
  id : Fin 2
  /-- program counter -/
  pc : ℕ
  /-- the input `vᵢ` -/
  inp : Bool
  /-- `v[i][0]` -/
  r0 : Option ρ := none
  /-- the values read from `Round[1-i][0], Round[1-i][1], …` -/
  rs : List (Option ℕ) := []
  /-- `v[i][1]` -/
  r1 : Option ρ := none
  /-- `v[1-i][0]` -/
  w : Option ρ := none
  /-- the decision index: return `Val[dec]` -/
  dec : Fin 2 := 0
  /-- the output value -/
  out : Bool := false

/-- One iteration of the loop on `op` (line 11–14), given the value read. -/
def stepOp (op : ℕ) : Option ℕ → ℕ
  | some x => op + 2 * x
  | none => 3 * op

/-- The value of `op` at `pᵢ` after reading `rs` in the rounds. -/
def opOf (i : Fin 2) (rs : List (Option ℕ)) : ℕ := rs.foldl stepOp i.val

variable {O : ObjSpec} (s : O.State) (f g : O.Op) (N : ℕ) (c : ℕ → O.Op)

/-- `τv(s.σ, o)`: the response of `o` applied after `σ` from `s`. -/
def tv (σ : List O.Op) (o : O.Op) : Option O.Resp :=
  some (O.δ (σ.foldl (fun st x => (O.δ st x).1) s) o).2

open Classical in
/-- The decision procedure (lines 22–39 of Algorithm 3, with line 30 corrected), at process `i`
with `op`, own responses `r0 = v[i][0]`, `r1 = v[i][1]`, the response `w = v[1-i][0]` read from
`Ret[1-i]` and `nx` read from `Next_op[1-i]`. Returns the index `j` of `Val[j]`. -/
noncomputable def decideC2 (i : Fin 2) (op : ℕ) (r0 r1 w : Option O.Resp) (nx : Option ℕ) :
    Fin 2 :=
  let v : Fin 2 → Fin 2 → Option O.Resp := fun p q =>
    if p = i then (if q = 0 then r0 else r1) else (if q = 0 then w else none)
  if op = 0 ∧ v 0 0 = tv s [] f ∧ v 0 1 = tv s [f] (c 0) ∧
      (v 1 0 = none ∨ v 1 0 = tv s [f, c 0] g) then 0
  else if op = 1 ∧ v 1 0 = tv s [f, c 0] g ∧ v 1 1 = tv s [f, c 0, g] (c 1) ∧
      nx = some 0 then 0
  else if op = N ∧ v 1 0 = tv s [] g ∧ v 1 1 = tv s [g] (c N) ∧
      (v 0 0 = none ∨ v 0 0 = tv s [g, c N] f) then 1
  else if op = N - 1 ∧ v 0 0 = tv s [g, c N] f ∧ v 0 1 = tv s [g, c N, f] (c (N - 1)) ∧
      nx = some N then 1
  else match nx with
    | none => if v i 1 = tv s [f, g] (c op) then 0 else 1
    | some j => if v i 1 = tv s [f, g, c j] (c op) ∨ v i 1 = tv s [f, g] (c op) then 0 else 1

/-- The actions of Algorithm 3 (`k` rounds, `N = 3 ^ k`). -/
noncomputable def actC2 (k : ℕ) (l : LS O.Resp) :
    Act (withRW (ιS := Unit) (RegS O.Resp) O) (LS O.Resp) :=
  match l.pc with
  | 0 => .access (.inl (.val l.id)) (RWOp.write (.b l.inp)) (fun _ => { l with pc := 1 })
  | 1 => .access (.inr ()) (if l.id = 0 then f else g) (fun r => { l with pc := 2, r0 := some r })
  | 2 => .access (.inl (.ret l.id)) (RWOp.write (.r l.r0)) (fun _ => { l with pc := 3 })
  | 3 => .access (.inl (.round l.id l.rs.length)) (RWOp.write (.n (opOf l.id l.rs)))
      (fun _ => { l with pc := 4 })
  | 4 => .access (.inl (.round (1 - l.id) l.rs.length)) RWOp.read
      (fun v => { l with pc := if l.rs.length + 1 < k then 3 else 5, rs := l.rs ++ [RV.nat v] })
  | 5 => .access (.inl (.next l.id)) (RWOp.write (.n (opOf l.id l.rs)))
      (fun _ => { l with pc := 6 })
  | 6 => .access (.inr ()) (c (opOf l.id l.rs)) (fun r => { l with pc := 7, r1 := some r })
  | 7 => .access (.inl (.ret (1 - l.id))) RWOp.read (fun v => { l with pc := 8, w := RV.resp v })
  | 8 => .access (.inl (.next (1 - l.id))) RWOp.read
      (fun v => { l with
        pc := 9
        dec := decideC2 s f g N c l.id (opOf l.id l.rs) l.r0 l.r1 l.w (RV.nat v) })
  | 9 => .access (.inl (.val l.dec)) RWOp.read (fun v => { l with pc := 10, out := RV.bool v })
  | _ => .out l.out

/-- **Algorithm 3** with `k` rounds and `N = 3 ^ k`. -/
noncomputable def algC2 (k : ℕ) : Alg 2 (withRW (ιS := Unit) (RegS O.Resp) O) where
  L := LS O.Resp
  init p b := { id := p, pc := 0, inp := b }
  act := actC2 s f g (3 ^ k) c k
  mem₀ := fun i => match i with
    | .inl _ => RV.bot
    | .inr _ => s

end TwoShotCons
