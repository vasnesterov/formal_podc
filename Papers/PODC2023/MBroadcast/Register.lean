import Papers.PODC2023.MBroadcast.Spec
import Podc.Computability.Distributed.SharedMemory.TimestampLin
import Mathlib.Order.WithBot
import Mathlib.Order.Prod.Lex.Basic

/-!
# Algorithm 3: an atomic MWMR register on top of MBroadcast (Section 5, Theorem 2)

The model `CAMP_{n,t}[MB-broadcast]`: asynchronous processes `P` (any linear order: the process
identities break ties between timestamps) that may crash, communicating only through an
MBroadcast layer. A configuration records the local states and the *MBroadcast trace* `log`
(the `bc`/`dl` events of the layer, in real-time order).

The layer is modelled by its specification: any process may mdeliver any message at any time
(`Step.dlv`), and the correctness theorem only considers executions whose trace satisfies the
safety properties of MBroadcast (`Spec.Safe`, which is prefix-closed). The liveness properties of
the layer (Global CS-termination) are assumptions of the termination theorem.

Messages are `synch k` and `write k v c`, tagged with the index `k` of the operation of the
sender that broadcasts them, so that all mbroadcast messages are different (the paper's
assumption). `synchro_mbroadcast(m)` = broadcast `m`, then wait (`Phase.wSync`, `Phase.wFin`,
`Phase.rSync`, `Phase.rFin`) until `m` has been mdelivered by the process itself.

Each block of code between two `wait`s is one atomic step: `write(v)` = `invW` (line 1),
`line2` (lines 2–3, with any date `d` such that `⟨d, i⟩ > clockᵢ`), `retW` (end of line 3);
`read()` = `invR` (line 4), `line5` (lines 5–6), `retR` (line 7); the handler of line 8 runs
atomically with the mdelivery (`dlv`).

Timestamps are `WithBot (Lex (ℕ × P))`: `⊥` is the timestamp of the initial value `v₀`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MBroadcast.Alg3

open Cslib.SharedMemory

/-- Timestamps `⟨date, writer⟩`, ordered lexicographically; `⊥` for the initial value. -/
abbrev TS (P : Type) := WithBot (Lex (ℕ × P))

/-- The timestamp `⟨d, p⟩`. -/
def ts {P : Type} (d : ℕ) (p : P) : TS P := ((toLex (d, p) : Lex (ℕ × P)) : WithBot _)

/-- Messages of Algorithm 3, tagged with the index of the sender's operation. -/
inductive Msg (P V : Type) where
  | synch (k : ℕ)
  | write (k : ℕ) (v : V) (c : TS P)
  deriving DecidableEq

/-- Control position of the current operation. -/
inductive Phase (P V : Type) where
  | idle
  /-- `write(v)`, waiting at line 1 for the own `synch`. -/
  | wSync (v : V)
  /-- `write(v)`, waiting at line 3 for the own `write(v, c)`. -/
  | wFin (v : V) (c : TS P)
  /-- `read()`, waiting at line 4 for the own `synch`. -/
  | rSync
  /-- `read()`, waiting at line 6 for the own `write(v, c)`; will return `v`. -/
  | rFin (v : V) (c : TS P)
  deriving DecidableEq

/-- Local state: `valᵢ`, `clockᵢ`, the number `k` of completed operations (the index of the
current one) and the control position. -/
structure Loc (P V : Type) where
  val : V
  clock : TS P
  k : ℕ
  phase : Phase P V

/-- Configurations: local states, the MBroadcast trace and the crashed processes. -/
structure Cfg (P V : Type) where
  loc : P → Loc P V
  log : List (Ev P (Msg P V))
  crashed : Set P

variable {P V : Type} [LinearOrder P] [DecidableEq V]

/-- Line 8: handler of an mdelivered message. -/
def handle (m : Msg P V) (l : Loc P V) : Loc P V :=
  match m with
  | .write _ v c => if l.clock < c then { l with val := v, clock := c } else l
  | .synch _ => l

/-- The initial configuration (register value `v₀`). -/
def initCfg (v₀ : V) : Cfg P V := ⟨fun _ => ⟨v₀, ⊥, 0, .idle⟩, [], ∅⟩

/-- Update the local state of `p` and append events to the trace. -/
def Cfg.upd (C : Cfg P V) (p : P) (l : Loc P V) (es : List (Ev P (Msg P V))) : Cfg P V :=
  ⟨Function.update C.loc p l, C.log ++ es, C.crashed⟩

/-- Steps of Algorithm 3 (with the history label they produce). -/
inductive Step (v₀ : V) : Cfg P V → Option (Label P (register V v₀)) → Cfg P V → Prop
  /-- `write(v)` invoked; line 1: `mbroadcast synch()`. -/
  | invW (C : Cfg P V) (p : P) (v : V) (hp : p ∉ C.crashed) (hi : (C.loc p).phase = .idle) :
      Step v₀ C (some (.inv p (.write v)))
        (C.upd p { C.loc p with phase := .wSync v } [.bc p (.synch (C.loc p).k)])
  /-- `read()` invoked; line 4: `mbroadcast synch()`. -/
  | invR (C : Cfg P V) (p : P) (hp : p ∉ C.crashed) (hi : (C.loc p).phase = .idle) :
      Step v₀ C (some (.inv p .read))
        (C.upd p { C.loc p with phase := .rSync } [.bc p (.synch (C.loc p).k)])
  /-- `p` mdelivers `m` from `q` and runs line 8. -/
  | dlv (C : Cfg P V) (p q : P) (m : Msg P V) (hp : p ∉ C.crashed) :
      Step v₀ C none (C.upd p (handle m (C.loc p)) [.dl p q m])
  /-- End of the wait of line 1; lines 2–3: choose `d` with `⟨d, p⟩ > clock`, mbroadcast
  `write(v, ⟨d, p⟩)`. -/
  | line2 (C : Cfg P V) (p : P) (v : V) (d : ℕ) (hp : p ∉ C.crashed)
      (hph : (C.loc p).phase = .wSync v) (hs : .dl p p (.synch (C.loc p).k) ∈ C.log)
      (hd : (C.loc p).clock < ts d p) :
      Step v₀ C none
        (C.upd p { C.loc p with phase := .wFin v (ts d p) } [.bc p (.write (C.loc p).k v (ts d p))])
  /-- End of the wait of line 4; lines 5–6: `v ← val`, mbroadcast `write(v, clock)`. -/
  | line5 (C : Cfg P V) (p : P) (hp : p ∉ C.crashed) (hph : (C.loc p).phase = .rSync)
      (hs : .dl p p (.synch (C.loc p).k) ∈ C.log) :
      Step v₀ C none
        (C.upd p { C.loc p with phase := .rFin (C.loc p).val (C.loc p).clock }
          [.bc p (.write (C.loc p).k (C.loc p).val (C.loc p).clock)])
  /-- End of the wait of line 3: `write` returns. -/
  | retW (C : Cfg P V) (p : P) (v : V) (c : TS P) (hp : p ∉ C.crashed)
      (hph : (C.loc p).phase = .wFin v c) (hs : .dl p p (.write (C.loc p).k v c) ∈ C.log) :
      Step v₀ C (some (.ret p v))
        (C.upd p { C.loc p with phase := .idle, k := (C.loc p).k + 1 } [])
  /-- End of the wait of line 6; line 7: `read` returns `v`. -/
  | retR (C : Cfg P V) (p : P) (v : V) (c : TS P) (hp : p ∉ C.crashed)
      (hph : (C.loc p).phase = .rFin v c) (hs : .dl p p (.write (C.loc p).k v c) ∈ C.log) :
      Step v₀ C (some (.ret p v))
        (C.upd p { C.loc p with phase := .idle, k := (C.loc p).k + 1 } [])
  /-- `p` crashes. -/
  | crash (C : Cfg P V) (p : P) :
      Step v₀ C none ⟨C.loc, C.log, insert p C.crashed⟩

/-- `C` is reachable with history `h`. -/
inductive Reach (v₀ : V) : Cfg P V → List (Label P (register V v₀)) → Prop
  | init : Reach v₀ (initCfg v₀) []
  | step {C C' : Cfg P V} {h : List (Label P (register V v₀))} {ℓ : Option _} :
      Reach v₀ C h → Step v₀ C ℓ C' → Reach v₀ C' (h ++ ℓ.toList)

/-- Steps only append to the MBroadcast trace. -/
lemma Step.log_eq {v₀ : V} {C C' : Cfg P V} {ℓ} (h : Step v₀ C ℓ C') :
    ∃ es, C'.log = C.log ++ es := by
  cases h <;> first | exact ⟨_, rfl⟩ | exact ⟨[], by simp⟩

end Podc.MBroadcast.Alg3
