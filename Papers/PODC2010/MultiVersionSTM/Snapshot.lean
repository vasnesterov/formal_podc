import Papers.PODC2010.MultiVersionSTM.Strategy

/-!
# Snapshot STMs

Two simple MV-permissive STMs, used as the competitors `X'` in the proof of Theorem 1 and as the
counterexample to Theorem 3 under the literal reading of Definition 4.

* **Update transactions** read the latest committed version (or their own write), buffer their
  writes, and validate at every read and at commit that every version they read is still the
  latest one; if not they abort (so even aborted transactions see a consistent snapshot), and a
  successful commit installs their versions.
* **Read-only transactions** never abort; they read from a *snapshot*, the prefix of the history
  of length `snap h T`:
  * eager (`lazy = false`): the snapshot is taken at the first step of `T`;
  * lazy (`lazy = true`, as in LSA): `T` reads the latest versions until some version it has read
    is overwritten; the snapshot is then frozen just before that overwriting commit.
* **Versions kept**: the latest version of each object, and, for every live read-only
  transaction, the versions of its snapshot.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type}

/-- The event `e` is a successful commit of a transaction that wrote `o` in `h`. -/
def CommitWrites (h : Hist Tx O) (e : Event Tx O) (o : O) : Prop :=
  (∃ r, e.resp = some r) ∧ ∃ W, e.inv = .commit W ∧ Writes h W o

/-- The latest (last installed) version of `o` after `h`. -/
noncomputable def latest (h : Hist Tx O) (o : O) : Option Tx :=
  (h.foldl (fun acc e => (acc.1 ++ [e], if CommitWrites acc.1 e o then some e.inv.tx else acc.2))
    (([] : Hist Tx O), (none : Option Tx))).2

/-- `T` performed a successful read of `o` in `h`. -/
def ReadsObj (h : Hist Tx O) (T : Tx) (o : O) : Prop := ∃ v, (⟨.read T o, some v⟩ : Event Tx O) ∈ h

/-- The `k`-th event of `h` overwrites an object that `T` read before it. -/
def Freezes (h : Hist Tx O) (T : Tx) (k : ℕ) : Prop :=
  ∃ e, h[k]? = some e ∧ ∃ o, CommitWrites (h.take k) e o ∧ ReadsObj (h.take k) T o

/-- The first event of `h` overwriting an object that `T` read before it. -/
noncomputable def frz (h : Hist Tx O) (T : Tx) : Option ℕ :=
  (List.range h.length).find? (fun k => decide (Freezes h T k))

/-- The index of the first event of `T` in `h` (`h.length` if `T` has not begun). -/
noncomputable def firstIdx (h : Hist Tx O) (T : Tx) : ℕ := h.findIdx (fun e => decide (e.inv.tx = T))

/-- The snapshot of read-only transaction `T` after `h`: the length of the prefix it reads. -/
noncomputable def snap (lazy : Bool) (h : Hist Tx O) (T : Tx) : ℕ :=
  if lazy then (frz h T).getD h.length else firstIdx h T

/-- The read-set validation of update transaction `T` at commit time: every version it read
(not after its own write) is still the latest one. -/
def Validates (h : Hist Tx O) (T : Tx) : Prop :=
  ∀ h₁ o v h₂, h = h₁ ++ ⟨.read T o, some v⟩ :: h₂ → ¬ Writes h₁ T o → v = latest h o

variable [TxSys Tx P]

/-- The response strategy of the snapshot STM. -/
noncomputable def snapResp (lazy : Bool) (h : Hist Tx O) : Inv Tx O → Resp Tx
  | .read T o =>
    if ro T then some (latest (h.take (snap lazy h T)) o)
    else if Writes h T o then some (some T)
    else if Validates h T then some (latest h o) else none
  | .write _ _ => some none
  | .commit T => if ro T then some none else if Validates h T then some none else none

/-- The versions kept by the snapshot STM after `h`. -/
def snapKept (lazy : Bool) (h : Hist Tx O) : Set (Version Tx O) :=
  {v | v.2 = latest h v.1} ∪
    {v | ∃ T, ro T = true ∧ ¬ Terminated h T ∧ v.2 = latest (h.take (snap lazy h T)) v.1}

/-- The snapshot STM, as a full-information STM. -/
noncomputable def snapSTM (lazy : Bool) : STM Tx O P := ofStrategy (snapResp lazy)

/-- The kept versions of the snapshot STM, as a function of its configuration. -/
def snapKeptC (lazy : Bool) (C : Config (snapSTM (Tx := Tx) (O := O) (P := P) lazy)) :
    Set (Version Tx O) :=
  snapKept lazy (C.mem ())

end Podc.MultiVersionSTM
