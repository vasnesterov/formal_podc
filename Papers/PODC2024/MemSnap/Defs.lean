import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Model
import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# Jayanti–Jayanti–Jayanti, *MemSnap: A Fast Adaptive Snapshot Algorithm for RMWable
Shared-Memory* (PODC 2024): the checkpointable object and Algorithm 1

* `CWord W` — a hardware memory word whose primitives are given by an arbitrary deterministic
  sequential specification `W` (values `W.State`, primitives `W.Op`, responses `W.Resp`): reads,
  writes, CAS, F&A, FAS, … are all instances. A component can be updated by any of them.
* `checkpointable W K v₀` — the sequential specification of Section 4: the state is a pair
  `(val, snap)` of arrays indexed by the components `K`, initially `(v₀, v₀)`;
  `update i o` applies the primitive `o` to `val i`, `click` copies `val` to `snap`,
  `observe i` returns `snap i`.
* `memSnap W K v₀ σ` — Algorithm 1 (MemSnap) in CSLib's asynchronous shared-memory model, with
  designated scanner `σ`. Base objects: `A[i]` (a word of type `W`, extended by a `read`),
  `B[i]` (a CAS word holding `(val, seq)` pairs) and `X` (a read/write register over `ℕ`).

Every primitive access is one atomic step; local computation is folded into the continuation of
the preceding access. `X ← X + 1` (line 1) is a read of `X` followed by a write of `X`: only the
scanner writes `X`, so this is equivalent to the atomic increment of the paper.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemSnap

open Cslib.SharedMemory

/-! ## The checkpointable object (Section 4) -/

/-- Operations of the checkpointable object with components `K`; `W.Op` are the primitives a
component (a memory word) supports. -/
inductive COp (W : ObjSpec) (K : Type) where
  /-- `update(i, uop, uarg)`: apply the primitive `o` (= `uop(uarg)`) to component `i`. -/
  | update (i : K) (o : W.Op)
  /-- `click()`: take a (implicit) snapshot. -/
  | click
  /-- `observe(i)`: the value of component `i` in the latest snapshot. -/
  | observe (i : K)

/-- Responses of the checkpointable object. -/
inductive CResp (W : ObjSpec) where
  /-- Response of an update: the response of the primitive. -/
  | upd (r : W.Resp)
  /-- Response of a click. -/
  | ack
  /-- Response of an observe. -/
  | obs (v : W.State)

/-- Abstract state `(val, snap)` of the checkpointable object. -/
@[ext]
structure CState (W : ObjSpec) (K : Type) where
  /-- Current values of the components. -/
  val : K → W.State
  /-- Values of the components in the latest snapshot. -/
  snap : K → W.State

variable (W : ObjSpec) (K : Type) [DecidableEq K]

/-- The checkpointable object of Section 4 with components `K`, component primitives `W` and
initial values `v₀` (initial state `(v₀, v₀)`). -/
abbrev checkpointable (v₀ : K → W.State) : ObjSpec where
  State := CState W K
  Op := COp W K
  Resp := CResp W
  init := ⟨v₀, v₀⟩
  δ s o := match o with
    | .update i o => (⟨Function.update s.val i (W.δ (s.val i) o).1, s.snap⟩,
        .upd (W.δ (s.val i) o).2)
    | .click => (⟨s.val, s.val⟩, .ack)
    | .observe i => (s, .obs (s.snap i))

/-! ## Base objects -/

/-- Primitives of the principal words `A[i]`: a `read`, or a primitive of `W`. -/
inductive WOp (W : ObjSpec) where
  | read
  | prim (o : W.Op)

/-- A principal word `A[i]`: a memory word supporting the primitives of `W` and `read`. -/
abbrev CWord (v₀ : W.State) : ObjSpec where
  State := W.State
  Op := WOp W
  Resp := W.State ⊕ W.Resp
  init := v₀
  δ q o := match o with
    | .read => (q, .inl q)
    | .prim o => ((W.δ q o).1, .inr (W.δ q o).2)

/-- Names of the base objects: `A[i]`, `B[i]` and the scan counter `X`. -/
inductive Obj (K : Type) where
  | A (i : K)
  | B (i : K)
  | X
  deriving DecidableEq

/-- The secondary words `B[i]`: compare&swap words over `(val, seq)` pairs. (Decidability of
equality of values is classical; it is only used to define the CAS.) -/
noncomputable abbrev BWord (v₀ : W.State) : ObjSpec :=
  @casObject (W.State × ℕ) (Classical.decEq _) (v₀, 0)

/-- The base objects of MemSnap. -/
noncomputable abbrev base (v₀ : K → W.State) : Obj K → ObjSpec
  | .A i => CWord W (v₀ i)
  | .B i => BWord W (v₀ i)
  | .X => register ℕ 0

/-! ## Algorithm 1 -/

/-- Local states (program counters with the local variables). `u = none` marks a `forward`
called by `observe(i)` (line 3), `u = some o` a `forward` called by `update(i, o)` (line 6);
`k2` is `true` in the second iteration of the for-loop of `forward`.

* `c1` / `c1w x` — line 1, read `X` / write `X ← x + 1`; `c2` — line 2 (return `ack`);
* `f9 … f12` — lines 9–12 of `forward` with the local variables read so far;
* `o4 i` — line 4 (read `B[i].val`), `o5 v` — line 5 (return `v`);
* `u7 i o` — line 7 (apply `o` to `A[i]`), `u8 r` — line 8 (return `r`). -/
inductive Loc (W : ObjSpec) (K : Type) where
  | idle
  | c1
  | c1w (x : ℕ)
  | c2
  | f9 (i : K) (u : Option W.Op) (k2 : Bool)
  | f10 (i : K) (u : Option W.Op) (k2 : Bool) (b : W.State × ℕ)
  | f11 (i : K) (u : Option W.Op) (k2 : Bool) (b : W.State × ℕ) (x : ℕ)
  | f12 (i : K) (u : Option W.Op) (k2 : Bool) (b : W.State × ℕ) (x : ℕ) (a : W.State)
  | o4 (i : K)
  | o5 (v : W.State)
  | u7 (i : K) (o : W.Op)
  | u8 (r : W.Resp)

variable {W K}

/-- Where `forward(i)` returns to: line 4 for `observe`, line 7 for `update`. -/
def fcont (i : K) : Option W.Op → Loc W K
  | none => .o4 i
  | some o => .u7 i o

/-- Did a CAS succeed (decoding the response of a CAS word)? -/
def casOk {α : Type} : α ⊕ Bool → Bool
  | .inl _ => false
  | .inr b => b

variable (W K)

/-- The program of a process (Algorithm 1). The continuations of reads map the impossible
response shapes to `idle`. -/
noncomputable def act (v₀ : K → W.State) :
    Loc W K → Action (checkpointable W K v₀) (base W K v₀) (Loc W K)
  | .idle => .ret .ack .idle
  | .c1 => .access .X .read (fun x => .c1w x)
  | .c1w x => .access .X (.write (x + 1)) (fun _ => .c2)
  | .c2 => .ret .ack .idle
  | .f9 i u k2 => .access (.B i) .read (fun r => match r with
      | .inl b => .f10 i u k2 b
      | .inr _ => .idle)
  | .f10 i u k2 b => .access .X .read (fun x => if b.2 = x then fcont i u else .f11 i u k2 b x)
  | .f11 i u k2 b x => .access (.A i) .read (fun r => match r with
      | .inl a => .f12 i u k2 b x a
      | .inr _ => .idle)
  | .f12 i u k2 b x a => .access (.B i) (.cas b (a, x)) (fun r =>
      if casOk r then fcont i u else if k2 then fcont i u else .f9 i u true)
  | .o4 i => .access (.B i) .read (fun r => match r with
      | .inl b => .o5 b.1
      | .inr _ => .idle)
  | .o5 v => .ret (.obs v) .idle
  | .u7 i o => .access (.A i) (.prim o) (fun r => match r with
      | .inr r => .u8 r
      | .inl _ => .idle)
  | .u8 r => .ret (.upd r) .idle

/-- Invocations: `click` starts at line 1, `observe(i)` and `update(i, o)` call `forward(i)`. -/
def invoke : COp W K → Loc W K
  | .click => .c1
  | .observe i => .f9 i none false
  | .update i o => .f9 i (some o) false

/-- The single-scanner discipline: the designated scanner `σ` only clicks and observes, every
other process (an updater, `π ∈ Π`) only updates. -/
def Allowed {P : Type} (σ : P) (p : P) : COp W K → Prop
  | .update _ _ => p ≠ σ
  | .click => p = σ
  | .observe _ => p = σ

/-- **MemSnap** (Algorithm 1): a single-scanner, RMWable, adaptive snapshot object with
components `K`, component primitives `W`, initial values `v₀` and designated scanner `σ`.
Initially `X = 0`, `A[i] = v₀ i` and `B[i] = (v₀ i, 0)`. -/
noncomputable def memSnap (v₀ : K → W.State) {P : Type} (σ : P) :
    Impl (checkpointable W K v₀) (base W K v₀) P (Loc W K) where
  memInit
    | .A i => v₀ i
    | .B i => (v₀ i, 0)
    | .X => (0 : ℕ)
  locInit _ := .idle
  invoke _ _ o := invoke W K o
  act _ l := act W K v₀ l
  allowed p o := Allowed W K σ p o

end Podc.MemSnap
