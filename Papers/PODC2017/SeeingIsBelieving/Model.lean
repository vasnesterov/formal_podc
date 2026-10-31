import Mathlib

/-!
# The state-based (client-centric) model of isolation

Crooks, Pu, Alvisi, Clement, *Seeing is Believing: A Client-Centric Specification of Database
Isolation*, PODC 2017, Sections 3–4.

* Keys `K`, transaction identifiers `ι`. Values are *uniquely identifiable* (Section 3): the value
  that transaction `j` writes to key `k` is represented by `some j`, the initial value `⊥` by
  `none`. A transaction writes each key at most once, so `Op.write k` carries no value.
* `TxnSet`: the transactions with their operations in program order (what the clients observe:
  the value returned by every read) and the committed ones (`𝒯`).
* `Execution`: a permutation `e` of `𝒯`; its states `s_0, …, s_n` are indexed by positions
  (`Execution.state i`), the parent state of `T` is `s_{idx T}`, the state it generates
  `s_{idx T + 1}`.
* Read states (Definition 2), `PREREAD` (Definition 3), `COMPLETE` (Definition 4), the commit
  tests of Table 1 for serializability, snapshot isolation, read committed, read uncommitted and
  parallel snapshot isolation (Definition 6), and `TxnSet.Satisfies` (Definition 5).

-- CSLib candidate (together with `Adya.lean`): a transactional key-value history model.
-/

set_option linter.unusedSectionVars false

namespace Podc.SeeingIsBelieving

open Relation

/-- Operations of a transaction. Values are `Option ι`: `none` is the initial value `⊥`, and
`some j` is the (unique) value that transaction `j` writes to the key in question. -/
inductive Op (K ι : Type*) where
  | read (k : K) (v : Option ι)
  | write (k : K)
  deriving DecidableEq

/-- The key accessed by an operation. -/
def Op.key {K ι : Type*} : Op K ι → K
  | .read k _ => k
  | .write k => k

/-- A set of transactions, each with its operations in program order, and the subset `committed`
of committed transactions (the paper's `𝒯`). -/
structure TxnSet (K ι : Type*) where
  ops : ι → List (Op K ι)
  committed : Finset ι

variable {K ι : Type*} [DecidableEq K] [DecidableEq ι]

namespace TxnSet

variable (H : TxnSet K ι)

/-- `T` writes key `k` (`k ∈ 𝒲_T`). -/
def Writes (T : ι) (k : K) : Prop := Op.write k ∈ H.ops T

instance (T : ι) (k : K) : Decidable (H.Writes T k) := by unfold Writes; infer_instance

/-- Well-formedness of the observations, as in Adya's histories: every value read was written by
the transaction it identifies, and a transaction reads its own value of a key only after its write
of that key. -/
structure WellFormed : Prop where
  /-- a value of another transaction that is read was written by it -/
  read_other : ∀ T ∈ H.committed, ∀ k X, Op.read k (some X) ∈ H.ops T → X ≠ T → H.Writes X k
  /-- a transaction reads its own value only after writing it -/
  read_own : ∀ T ∈ H.committed, ∀ m k, (H.ops T)[m]? = some (Op.read k (some T)) →
    Op.write k ∈ (H.ops T).take m

end TxnSet

/-- An execution `e`: a permutation of the committed transactions. -/
structure Execution (H : TxnSet K ι) where
  order : List ι
  nodup : order.Nodup
  mem_iff : ∀ T, T ∈ order ↔ T ∈ H.committed

namespace Execution

variable {H : TxnSet K ι} (e : Execution H)

/-- Position of `T` in `e`: `T`'s parent state is `s_{idx T}`, the state it generates is
`s_{idx T + 1}`. -/
def idx (T : ι) : ℕ := e.order.idxOf T

/-- The state `s_i` of the execution: the value of each key after the first `i` transactions. -/
def state : ℕ → K → Option ι
  | 0, _ => none
  | i + 1, k =>
    match e.order[i]? with
    | some T => if H.Writes T k then some T else state i k
    | none => state i k


lemma idx_lt_length {T : ι} (hT : T ∈ H.committed) : e.idx T < e.order.length :=
  List.idxOf_lt_length_of_mem ((e.mem_iff T).2 hT)

lemma getElem?_eq_some_iff {i : ℕ} {T : ι} :
    e.order[i]? = some T ↔ T ∈ H.committed ∧ e.idx T = i := by
  constructor
  · intro h
    have hi : i < e.order.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
    rw [List.getElem?_eq_getElem hi, Option.some_inj] at h
    subst h
    exact ⟨(e.mem_iff _).1 (List.getElem_mem hi), e.nodup.idxOf_getElem i hi⟩
  · rintro ⟨hT, rfl⟩
    rw [List.getElem?_eq_getElem (e.idx_lt_length hT)]
    simp [idx, List.getElem_idxOf]

lemma idx_inj {T T' : ι} (hT : T ∈ H.committed) (hT' : T' ∈ H.committed)
    (h : e.idx T = e.idx T') : T = T' := by
  have h1 := (e.getElem?_eq_some_iff (i := e.idx T)).2 ⟨hT, rfl⟩
  have h2 := (e.getElem?_eq_some_iff (i := e.idx T)).2 ⟨hT', h.symm⟩
  rw [h1] at h2; exact Option.some_inj.1 h2

/-- Characterization of the states. -/
lemma state_spec (k : K) (i : ℕ) :
    (e.state i k = none ↔ ∀ Z ∈ H.committed, H.Writes Z k → i ≤ e.idx Z) ∧
    ∀ V, (e.state i k = some V ↔ V ∈ H.committed ∧ H.Writes V k ∧ e.idx V < i ∧
      ∀ Z ∈ H.committed, H.Writes Z k → e.idx V < e.idx Z → i ≤ e.idx Z) := by
  induction i with
  | zero => simp [state]
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases h : e.order[i]? with _ | T
    · have hlen : e.order.length ≤ i := by simpa using h
      have hall : ∀ Z ∈ H.committed, e.idx Z < i := fun Z hZ =>
        lt_of_lt_of_le (e.idx_lt_length hZ) hlen
      simp only [state, h]
      refine ⟨ih1.trans ⟨fun H' Z hZ hw => absurd (H' Z hZ hw) (by have := hall Z hZ; omega),
        fun H' Z hZ hw => absurd (H' Z hZ hw) (by have := hall Z hZ; omega)⟩, fun V => ?_⟩
      rw [ih2 V]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, by omega, fun Z hZ hw hlt => absurd (h4 Z hZ hw hlt)
          (by have := hall Z hZ; omega)⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, hall V h1, fun Z hZ hw hlt => absurd (h4 Z hZ hw hlt)
          (by have := hall Z hZ; omega)⟩
    · obtain ⟨hT, hTi⟩ := e.getElem?_eq_some_iff.1 h
      by_cases hw : H.Writes T k
      · simp only [state, h, hw, ite_true]
        refine ⟨⟨fun h => (by cases h), fun H' => absurd (H' T hT hw) (by omega)⟩, fun V => ?_⟩
        constructor
        · rintro ⟨⟩
          exact ⟨hT, hw, by omega, fun Z _ _ hlt => by omega⟩
        · rintro ⟨h1, h2, h3, h4⟩
          by_contra hne
          have hne' : V ≠ T := fun h => hne (by rw [h])
          have : e.idx V ≠ e.idx T := fun h => hne' (e.idx_inj h1 hT h)
          have := h4 T hT hw (by omega)
          omega
      · simp only [state, h, hw, ite_false]
        have key : ∀ Z ∈ H.committed, H.Writes Z k → e.idx Z ≠ i := by
          rintro Z hZ hwZ rfl
          exact hw (e.idx_inj hZ hT hTi.symm ▸ hwZ)
        refine ⟨ih1.trans ⟨fun H' Z hZ hwZ => ?_, fun H' Z hZ hwZ => ?_⟩, fun V => ?_⟩
        · have := H' Z hZ hwZ; have := key Z hZ hwZ; omega
        · have := H' Z hZ hwZ; omega
        rw [ih2 V]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          refine ⟨h1, h2, by omega, fun Z hZ hwZ hlt => ?_⟩
          have := h4 Z hZ hwZ hlt; have := key Z hZ hwZ; omega
        · rintro ⟨h1, h2, h3, h4⟩
          refine ⟨h1, h2, ?_, fun Z hZ hwZ hlt => ?_⟩
          · have := key V h1 h2; omega
          · have := h4 Z hZ hwZ hlt; omega


lemma state_eq_none_iff {k : K} {i : ℕ} :
    e.state i k = none ↔ ∀ Z ∈ H.committed, H.Writes Z k → i ≤ e.idx Z :=
  (e.state_spec k i).1

lemma state_eq_some_iff {k : K} {i : ℕ} {V : ι} :
    e.state i k = some V ↔ V ∈ H.committed ∧ H.Writes V k ∧ e.idx V < i ∧
      ∀ Z ∈ H.committed, H.Writes Z k → e.idx V < e.idx Z → i ≤ e.idx Z :=
  (e.state_spec k i).2 V

/-- A transaction's write is visible in the state it generates. -/
lemma state_idx_succ {V : ι} {k : K} (hV : V ∈ H.committed) (hw : H.Writes V k) :
    e.state (e.idx V + 1) k = some V :=
  e.state_eq_some_iff.2 ⟨hV, hw, by omega, fun _ _ _ h => by omega⟩

/-- If some transaction of `e` writes `k` in positions `[j, i)`, the states `s_j` and `s_i`
differ on `k`. -/
lemma state_ne_of_writer {k : K} {j i : ℕ} {Z : ι} (hZ : Z ∈ H.committed) (hw : H.Writes Z k)
    (hj : j ≤ e.idx Z) (hi : e.idx Z < i) : e.state j k ≠ e.state i k := by
  intro heq
  rcases hs : e.state i k with _ | W
  · have := e.state_eq_none_iff.1 hs Z hZ hw; omega
  · obtain ⟨hW, hwW, hWi, hWmax⟩ := e.state_eq_some_iff.1 hs
    have hZW : e.idx Z ≤ e.idx W := by
      by_contra hc; have := hWmax Z hZ hw (by omega); omega
    rw [hs] at heq
    obtain ⟨-, -, hWj, -⟩ := e.state_eq_some_iff.1 heq
    omega

/-- If no transaction of `e` writes `k` in positions `[j, i)`, then `s_j` and `s_i` agree on `k`. -/
lemma state_eq_of_no_writer {k : K} {j i : ℕ} (hji : j ≤ i)
    (h : ∀ Z ∈ H.committed, H.Writes Z k → e.idx Z < j ∨ i ≤ e.idx Z) :
    e.state j k = e.state i k := by
  rcases hs : e.state i k with _ | W
  · rw [e.state_eq_none_iff] at hs ⊢
    intro Z hZ hw; have := hs Z hZ hw; omega
  · obtain ⟨hW, hwW, hWi, hWmax⟩ := e.state_eq_some_iff.1 hs
    rcases h W hW hwW with hWj | hWj
    · exact e.state_eq_some_iff.2 ⟨hW, hwW, hWj, fun Z hZ hw hlt => by
        have := hWmax Z hZ hw hlt; rcases h Z hZ hw with h' | h' <;> omega⟩
    · omega

/-! ### Read states and commit tests (Section 3, Definitions 2–5, Table 1) -/

/-- **Definition 2** (with the paper's convention for writes and for reads that follow a write
of the same key in `T`). `e.ReadState T m i`: the state `s_i` is a read state of the `m`-th
operation of `T`. -/
def ReadState (T : ι) (m : ℕ) (i : ℕ) : Prop :=
  i ≤ e.idx T ∧
    match (H.ops T)[m]? with
    | some (.read k v) => e.state i k = v ∨ (v = some T ∧ Op.write k ∈ (H.ops T).take m)
    | some (.write _) => True
    | none => False

/-- **Definition 3.** `PREREAD_e(T)`: every operation of `T` has a read state. -/
def PreRead (T : ι) : Prop := ∀ m < (H.ops T).length, ∃ i, e.ReadState T m i

/-- **Definition 4.** `COMPLETE_{e,T}(s_i)`: `s_i` is a read state of every operation of `T`. -/
def Complete (T : ι) (i : ℕ) : Prop := ∀ m < (H.ops T).length, e.ReadState T m i

/-- `NO-CONF_T(s_i)`: `Δ(s_i, s_p) ∩ 𝒲_T = ∅`, where `s_p` is `T`'s parent state. -/
def NoConf (T : ι) (i : ℕ) : Prop := ∀ k, H.Writes T k → e.state i k = e.state (e.idx T) k

/-- Commit test of **serializability**: `COMPLETE_{e,T}(s_p)`. -/
def CTSer (T : ι) : Prop := e.Complete T (e.idx T)

/-- Commit test of **snapshot isolation**: `∃ s ∈ 𝒮_e, COMPLETE_{e,T}(s) ∧ NO-CONF_T(s)`. -/
def CTSI (T : ι) : Prop := ∃ i ≤ e.order.length, e.Complete T i ∧ e.NoConf T i

/-- Commit test of **read committed**: `PREREAD_e(T)`. -/
def CTRC (T : ι) : Prop := e.PreRead T

/-- Commit test of **read uncommitted**: `True`. -/
def CTRU (_e : Execution H) (_T : ι) : Prop := True

/-- `s_i` is the first read state `sf_o` of the `m`-th operation `o` of `T`. -/
def IsFirstReadState (T : ι) (m i : ℕ) : Prop :=
  e.ReadState T m i ∧ ∀ i', e.ReadState T m i' → i ≤ i'

/-- `s_i` is the last read state `sl_o` of the `m`-th operation `o` of `T`. -/
def IsLastReadState (T : ι) (m i : ℕ) : Prop :=
  e.ReadState T m i ∧ ∀ i', e.ReadState T m i' → i' ≤ i

/-- `T' ▶ T` (`T' ∈ D-PREC_e(T)`, Section 4): `T` has an operation whose first read state is the
state generated by `T'`, or `T'` precedes `T` in `e` and they write a common key. -/
def DPrec (T' T : ι) : Prop :=
  T' ∈ H.committed ∧ T ∈ H.committed ∧
    ((∃ m < (H.ops T).length, e.IsFirstReadState T m (e.idx T' + 1)) ∨
      (e.idx T' < e.idx T ∧ ∃ k, H.Writes T k ∧ H.Writes T' k))

/-- **Definition 6.** Commit test of **parallel snapshot isolation**:
`PREREAD_e(T) ∧ ∀ T' ▷ T, ∀ o ∈ Σ_T, o.k ∈ 𝒲_{T'} ⇒ s_{T'} →* sl_o`, where `▷` is the
transitive closure of `▶` and `s_{T'}` is the state generated by `T'`. -/
def CTPSI (T : ι) : Prop :=
  e.PreRead T ∧ ∀ T', TransGen e.DPrec T' T → ∀ m (hm : m < (H.ops T).length),
    H.Writes T' ((H.ops T)[m]).key → ∀ i, e.IsLastReadState T m i → e.idx T' + 1 ≤ i

end Execution

/-- **Definition 5.** The transactions `H` satisfy the isolation level with commit test `CT` iff
`∃ e, ∀ T ∈ 𝒯, CT_I(T, e)`. -/
def TxnSet.Satisfies (H : TxnSet K ι) (CT : Execution H → ι → Prop) : Prop :=
  ∃ e : Execution H, ∀ T ∈ H.committed, CT e T

end Podc.SeeingIsBelieving
