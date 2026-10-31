import Papers.PODC2019.ConcurrentSketches.Sketch

/-!
# Fast Concurrent Data Sketches (PODC 2019): processes and base objects

Common ingredients of the two concurrent algorithms of Section 5.2 (Algorithm 2 of the PODC
version, Algorithm 3 of the full version), in CSLib's asynchronous shared-memory model
(`Cslib.SharedMemory.Impl`: interleaving of atomic steps on base objects).

* Processes `Proc N Q`: `N` update threads `upd i` (`t₁, …, t_N`), the propagator `prop` (`t₀`)
  and query threads `qry q` (`q : Q`, any number of them).
* Base objects:
  - the composable global sketch `globalS` (`globObj`): `merge(t)`, `snapshot()`, `calcHint()`;
    the paper requires concurrent executions of `snapshot` and `merge` to be strongly
    linearisable and treats them as atomic steps; we take the global sketch to be atomic;
  - local sketches `localS` (`locObj`): `update(a)`, `read` (the propagator reads the local
    sketch in order to merge it), `reset` (`localS ← empty sketch`);
  - atomic registers `prop_i` (`regObj`): `Option Hint`, where `none` encodes the paper's value
    `0` and `some h` a hint (the paper requires `calcHint() ≠ 0`);
  - (optimised algorithm only) registers `cur_i` holding a `Bool`.
-/

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

/-- Processes: update threads, the propagator thread `t₀`, and query threads. -/
inductive Proc (N : ℕ) (Q : Type) where
  | upd (i : Fin N)
  | prop
  | qry (q : Q)
  deriving DecidableEq

/-- Which operations a process may invoke: update threads `update`, the propagator `propagate`,
query threads `query`. -/
def Proc.allowed {S : Composable} {N : ℕ} {Q : Type} : Proc N Q → SkOp S.toSketch → Prop
  | .upd _, .update _ => True
  | .prop, .propagate => True
  | .qry _, .query _ => True
  | _, _ => False

/-- Operations on the global (composable) sketch. -/
inductive GOp (S : Composable) where
  | merge (t : S.State)
  | snapshot
  | calcHint

/-- Responses of the global sketch. -/
inductive GResp (S : Composable) where
  | unit
  | snap (x : S.Snap)
  | hint (h : S.Hint)

/-- Operations on a local sketch. -/
inductive LOp (S : Composable) where
  | update (a : S.Elem)
  | read
  | reset

/-- Responses of a local sketch. -/
inductive LResp (S : Composable) where
  | unit
  | state (s : S.State)

/-- Operations on a register. -/
inductive ROp (V : Type) where
  | read
  | write (v : V)

/-- The global composable sketch as an atomic base object. -/
abbrev globObj (S : Composable) : ObjSpec where
  State := S.State
  Op := GOp S
  Resp := GResp S
  init := S.init
  δ s o := match o with
    | .merge t => (S.merge s t, .unit)
    | .snapshot => (s, .snap (S.snapshot s))
    | .calcHint => (s, .hint (S.calcHint s))

/-- A local sketch as a base object. -/
abbrev locObj (S : Composable) : ObjSpec where
  State := S.State
  Op := LOp S
  Resp := LResp S
  init := S.init
  δ s o := match o with
    | .update a => (S.update s a, .unit)
    | .read => (s, .state s)
    | .reset => (S.init, .unit)

/-- An atomic register with values in `V` (`write` returns its argument; irrelevant). -/
abbrev regObj (V : Type) (v₀ : V) : ObjSpec where
  State := V
  Op := ROp V
  Resp := V
  init := v₀
  δ v o := match o with
    | .read => (v, v)
    | .write w => (w, w)

end Podc.ConcurrentSketches
