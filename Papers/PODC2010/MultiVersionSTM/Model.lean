import Mathlib

/-!
# Transactional histories of a multi-versioned STM

Perelman, Fan, Keidar. *On Maintaining Multiple Versions in STM.* PODC 2010 (Technion CCIT
Report #765, May 2010), Sections 3–5.

This file fixes the *history* level of the model.

* **Transactions** are identified by elements of `Tx`. Whether a transaction is read-only is known
  a priori (`TxSys.ro`), and so is the thread that runs it (`TxSys.thr`).
* **Operations** (`Inv`): `read T o`, `write T o`, `commit T`. Every transactional step is
  atomic (Section 3: "all the base steps for running a transactional step appear to execute
  atomically"), so an event is an invocation together with its response.
* **Versions instead of values.** A write does not carry a value: the version of `o` written by
  `W` is named by `W`, and a successful read returns the version it reads (`none` is the initial
  version, `some W` the version written by `W`). This is the paper's notation `oᵢʲ` and the
  standard multiversion abstraction; it is the value semantics on histories in which all written
  values are distinct.
* **Responses** (`Resp`): `none` is the abort response `A(T)`; `some r` is a successful response
  (for a read, `r` is the version read; for a write or a commit, `r` is ignored).
* **Strict serializability** (`StrictSer`) is checked on the complete (committed or aborted)
  transactions, as in the paper: there is an injective position function `pos` on them that
  respects the real-time order and makes every successful read legal (a read after an own write
  returns the own write; otherwise it returns the version of the last committed writer before the
  reader, or the initial version).
* **MV-permissiveness** (Definition 2, `MVPerm`): only update transactions abort, and only when
  they conflict with a *concurrent* update transaction.
* **Versions kept, overwritten versions, and the precedence relation** of Section 7.
-/

namespace Podc.MultiVersionSTM

/-- Static information about transactions: whether a transaction is read-only (known a priori,
Section 3), and the thread `thr T` that runs it. -/
class TxSys (Tx : Type) (P : outParam Type) where
  /-- `ro T` iff `T` is a read-only transaction. -/
  ro : Tx → Bool
  /-- The thread running `T`. -/
  thr : Tx → P

export TxSys (ro thr)

/-- Transactional operations (invocations). -/
inductive Inv (Tx O : Type) where
  | read (T : Tx) (o : O)
  | write (T : Tx) (o : O)
  | commit (T : Tx)
  deriving DecidableEq

namespace Inv

variable {Tx O : Type}

/-- The transaction of an invocation. -/
def tx : Inv Tx O → Tx
  | read T _ => T
  | write T _ => T
  | commit T => T

/-- The transactional object accessed by an invocation. -/
def obj? : Inv Tx O → Option O
  | read _ o => some o
  | write _ o => some o
  | commit _ => none

@[simp] lemma tx_read (T : Tx) (o : O) : (read T o).tx = T := rfl
@[simp] lemma tx_write (T : Tx) (o : O) : (write T o).tx = T := rfl
@[simp] lemma tx_commit (T : Tx) : (commit T : Inv Tx O).tx = T := rfl
@[simp] lemma obj?_read (T : Tx) (o : O) : (read T o).obj? = some o := rfl
@[simp] lemma obj?_write (T : Tx) (o : O) : (write T o).obj? = some o := rfl
@[simp] lemma obj?_commit (T : Tx) : (commit T : Inv Tx O).obj? = none := rfl

end Inv

/-- Responses: `none` is the abort response `A(T)`; `some r` is a successful response, where `r`
is the version read (for reads) and is ignored otherwise. -/
abbrev Resp (Tx : Type) := Option (Option Tx)

/-- An event: an invocation with its response (transactional steps are atomic). -/
structure Event (Tx O : Type) where
  inv : Inv Tx O
  resp : Resp Tx
  deriving DecidableEq

/-- A transactional history. -/
abbrev Hist (Tx O : Type) := List (Event Tx O)

/-- An object version: the object and its writer (`none` = initial version). -/
abbrev Version (Tx O : Type) := O × Option Tx

variable {Tx O P : Type}

/-! ### Transactions in a history -/

/-- `T` has begun in `h` (it has an event). -/
def Began (h : Hist Tx O) (T : Tx) : Prop := ∃ e ∈ h, e.inv.tx = T

/-- `T` committed in `h`. -/
def Committed (h : Hist Tx O) (T : Tx) : Prop := ∃ r, (⟨.commit T, some r⟩ : Event Tx O) ∈ h

/-- `T` was aborted in `h`. -/
def Aborted (h : Hist Tx O) (T : Tx) : Prop := ∃ e ∈ h, e.inv.tx = T ∧ e.resp = none

/-- `T` is complete (committed or aborted) in `h`. -/
def Terminated (h : Hist Tx O) (T : Tx) : Prop := Committed h T ∨ Aborted h T

/-- `T` is live in `h`: it has begun and is not complete. -/
def Live (h : Hist Tx O) (T : Tx) : Prop := Began h T ∧ ¬ Terminated h T

/-- `T` invoked a write to `o` in `h`. -/
def Writes (h : Hist Tx O) (T : Tx) (o : O) : Prop := ∃ r, (⟨.write T o, r⟩ : Event Tx O) ∈ h

/-- `T` invoked a read or a write of `o` in `h`. -/
def Accesses (h : Hist Tx O) (T : Tx) (o : O) : Prop := ∃ e ∈ h, e.inv.tx = T ∧ e.inv.obj? = some o

/-- `W` is a committed transaction that wrote `o`: it created a version of `o`. -/
def CWriter (h : Hist Tx O) (o : O) (W : Tx) : Prop := Committed h W ∧ Writes h W o

/-- Real-time order `A ≺_H B`: the commit of `A` precedes the first step of `B`. -/
def RT (h : Hist Tx O) (A B : Tx) : Prop :=
  Began h B ∧ ∃ h₁ h₂, h = h₁ ++ h₂ ∧ Committed h₁ A ∧ ¬ Began h₁ B

/-- `A` committed before `B` (the order in which versions are installed). -/
def CommitBefore (h : Hist Tx O) (A B : Tx) : Prop :=
  ∃ h₁ h₂, h = h₁ ++ h₂ ∧ Committed h₁ A ∧ ¬ Committed h₁ B

/-- Two transactions are concurrent: both have begun and neither precedes the other in real
time. -/
def Concurrent (h : Hist Tx O) (A B : Tx) : Prop :=
  Began h A ∧ Began h B ∧ ¬ RT h A B ∧ ¬ RT h B A

/-- Two transactions conflict: they access a common object and at least one of them writes it. -/
def Conflict (h : Hist Tx O) (A B : Tx) : Prop :=
  ∃ o, Accesses h A o ∧ Accesses h B o ∧ (Writes h A o ∨ Writes h B o)

/-! ### Strict serializability -/

/-- A read of `o` by `T` returning `v`, that does not follow a write of `T` to `o`, is legal for
the serialization positions `pos`: it returns the version of the last committed writer of `o`
before `T`, or the initial version if there is none. -/
def ExtLegal (h : Hist Tx O) (pos : Tx → ℕ) (T : Tx) (o : O) : Option Tx → Prop
  | none => ∀ W, CWriter h o W → W ≠ T → pos T < pos W
  | some W => W ≠ T ∧ CWriter h o W ∧ pos W < pos T ∧
      ∀ W', CWriter h o W' → W' ≠ T → pos W' < pos T → pos W' ≤ pos W

/-- `pos` serializes the complete (committed or aborted) transactions of `h`: it is injective on
them, respects the real-time order, and makes every successful read of a complete transaction
legal. Only committed transactions install versions (`ExtLegal` uses `CWriter`). -/
def SerWitness (h : Hist Tx O) (pos : Tx → ℕ) : Prop :=
  (∀ A B, Terminated h A → Terminated h B → pos A = pos B → A = B) ∧
  (∀ A B, Committed h A → Terminated h B → RT h A B → pos A < pos B) ∧
  (∀ T, Terminated h T → ∀ h₁ o v h₂, h = h₁ ++ ⟨.read T o, some v⟩ :: h₂ →
    (Writes h₁ T o → v = some T) ∧ (¬ Writes h₁ T o → ExtLegal h pos T o v))

/-- **Strict serializability** (Section 3): `complete(H)`, the committed and aborted
transactions, is equivalent to a legal sequential history that respects the real-time order. -/
def StrictSer (h : Hist Tx O) : Prop := ∃ pos, SerWitness h pos

/-! ### Well-formed histories, MV-permissiveness, reads of written versions -/

section Sys

variable [TxSys Tx P]

/-- The invocation `i` may follow the history `h`: its transaction is not complete, a read-only
transaction does not write, and a thread starts a new transaction only when its previous
transactions are complete (each thread runs at most one transaction at a time). -/
def OKNext (h : Hist Tx O) (i : Inv Tx O) : Prop :=
  ¬ Terminated h i.tx ∧ (∀ T o, i = .write T o → ro T = false) ∧
  (¬ Began h i.tx → ∀ T', T' ≠ i.tx → thr T' = thr i.tx → Began h T' → Terminated h T')

/-- A well-formed history: every invocation may follow the history before it. -/
def WF (h : Hist Tx O) : Prop := ∀ h₁ e h₂, h = h₁ ++ e :: h₂ → OKNext h₁ e.inv

/-- **MV-permissiveness** (Definition 2) of a history: a transaction aborts only when it is an
update transaction that conflicts with another, concurrent, update transaction. -/
def MVPerm (h : Hist Tx O) : Prop :=
  ∀ h₁ i h₂, h = h₁ ++ ⟨i, none⟩ :: h₂ →
    ro i.tx = false ∧ ∃ T', T' ≠ i.tx ∧ ro T' = false ∧
      Concurrent (h₁ ++ [⟨i, none⟩]) i.tx T' ∧ Conflict (h₁ ++ [⟨i, none⟩]) i.tx T'

end Sys

/-- A read returns the initial version or a version whose write has been invoked (in the value
semantics: a read returns the initial value or a value that has been written). -/
def ReadsWritten (h : Hist Tx O) : Prop :=
  ∀ h₁ T o W h₂, h = h₁ ++ ⟨.read T o, some (some W)⟩ :: h₂ → Writes h₁ W o

/-! ### Versions -/

/-- The version exists in `h`: the initial version, or one written by a committed transaction. -/
def VExists (h : Hist Tx O) : Version Tx O → Prop
  | (_, none) => True
  | (o, some W) => CWriter h o W

/-- The version `w` of the same object was written after the version `v` (by a committed
transaction that committed after `v`'s writer). -/
def WrittenAfter (h : Hist Tx O) (v w : Version Tx O) : Prop :=
  w.1 = v.1 ∧ ∃ W', w.2 = some W' ∧ CWriter h v.1 W' ∧ ∀ W, v.2 = some W → CommitBefore h W W'

/-- An *old* (overwritten) version: it exists and a later version of the same object exists. -/
def Old (h : Hist Tx O) (v : Version Tx O) : Prop :=
  VExists h v ∧ ∃ w, WrittenAfter h v w

/-- `W'` is the committed writer that overwrote version `v` of `o` (the next version). -/
def NextWriter (h : Hist Tx O) (o : O) (v : Option Tx) (W' : Tx) : Prop :=
  WrittenAfter h (o, v) (o, some W') ∧
    ∀ W'', WrittenAfter h (o, v) (o, some W'') → W'' ≠ W' → CommitBefore h W' W''

/-! ### The precedence relation of Section 7 -/

/-- One step of the transaction precedence relation of Section 7: real-time order,
read-after-write, write-after-write, and write-after-read (anti-dependence). -/
def PrecEdge (h : Hist Tx O) (A B : Tx) : Prop :=
  RT h A B ∨
  (A ≠ B ∧ ∃ o, (⟨.read B o, some (some A)⟩ : Event Tx O) ∈ h) ∨
  (∃ o, CWriter h o A ∧ CWriter h o B ∧ CommitBefore h A B) ∨
  (A ≠ B ∧ ∃ o v, (⟨.read A o, some v⟩ : Event Tx O) ∈ h ∧ NextWriter h o v B)

/-- The transaction precedence relation of Section 7 (`A` precedes `B`). -/
def Prec (h : Hist Tx O) : Tx → Tx → Prop := Relation.TransGen (PrecEdge h)

end Podc.MultiVersionSTM
