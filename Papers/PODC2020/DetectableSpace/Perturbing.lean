import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Podc.SharedMemory.Objects.MaxRegister
import Podc.SharedMemory.Objects.Queue

/-!
# Doubly-perturbing objects (Definition 3, Lemmas 3–8)

Sequential histories are lists of pairs `(process, operation)`; the sequential specification
does not depend on processes, which only matter for "by a different process" and "`p`-free".

* `PerturbingWrt O H p o p' o'` — `o` by `p` is perturbing w.r.t. `o'` by `p' ≠ p` after `H`;
* `DPWitness O p o`, `DoublyPerturbing O P` — Definition 3;
* Lemma 3 (`register_doublyPerturbing`), Lemma 5 (`counter_doublyPerturbing`, also for the
  bounded counter `bcounter 2`), Lemma 6 (`cas_doublyPerturbing`), Lemma 7
  (`faa_doublyPerturbing`), Lemma 8 (`queue_doublyPerturbing`);
* Lemma 4 (`maxReg_not_doublyPerturbing`): a max register is not doubly-perturbing.
-/

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

variable {P : Type}

/-- State after a sequential history. -/
def stateAfter (O : ObjSpec) (H : List (P × O.Op)) : O.State :=
  O.runOps O.init (H.map Prod.snd)

/-- Response of `o` after the sequential history `H`. -/
def respAfter (O : ObjSpec) (H : List (P × O.Op)) (o : O.Op) : O.Resp :=
  (O.δ (stateAfter O H) o).2

/-- `o` by `p` is perturbing with respect to `o'` by a different process `p'` after `H`:
`o'` returns different responses in `H ∘ o ∘ o'` and in `H ∘ o'`. -/
def PerturbingWrt (O : ObjSpec) (H : List (P × O.Op)) (p : P) (o : O.Op) (p' : P)
    (o' : O.Op) : Prop :=
  p' ≠ p ∧ respAfter O (H ++ [(p, o)]) o' ≠ respAfter O H o'

/-- `o` by `p` is perturbing after `H`. -/
def Perturbing (O : ObjSpec) (H : List (P × O.Op)) (p : P) (o : O.Op) : Prop :=
  ∃ p' o', PerturbingWrt O H p o p' o'

/-- `o` by `p` witnesses that `O` is doubly-perturbing (Definition 3): there are `H₁` and
`o_r` by `r` such that `o` is perturbing w.r.t. `o_r` after `H₁`, and a `p`-free extension `E`
of `H₁ ∘ o ∘ o_r` after which `o` is perturbing again. -/
def DPWitness (O : ObjSpec) (p : P) (o : O.Op) : Prop :=
  ∃ (H₁ : List (P × O.Op)) (r : P) (o_r : O.Op), PerturbingWrt O H₁ p o r o_r ∧
    ∃ E : List (P × O.Op), (∀ x ∈ E, x.1 ≠ p) ∧ Perturbing O (H₁ ++ [(p, o), (r, o_r)] ++ E) p o

/-- Definition 3: `O` is doubly-perturbing (for the process set `P`). -/
def DoublyPerturbing (O : ObjSpec) (P : Type) : Prop := ∃ (p : P) (o : O.Op), DPWitness O p o

lemma stateAfter_append (O : ObjSpec) (H H' : List (P × O.Op)) :
    stateAfter O (H ++ H') = O.runOps (stateAfter O H) (H'.map Prod.snd) := by
  simp [stateAfter, ObjSpec.runOps_append]

/-! ### Lemma 3: read/write registers -/

/-- **Lemma 3.** A read/write register with at least two values is doubly-perturbing
(witness: `write v₁` by `p`, perturbing w.r.t. `read` by `q`). -/
theorem register_doublyPerturbing {V : Type} (v₀ v₁ : V) (hv : v₀ ≠ v₁) (p q : P)
    (hpq : q ≠ p) : DoublyPerturbing (register V v₀) P := by
  refine ⟨p, .write v₁, [], q, .read, ⟨hpq, ?_⟩, [(q, .write v₀)], by simp [hpq], q, .read, hpq, ?_⟩
  · simp [respAfter, stateAfter, ObjSpec.runOps, Ne.symm hv]
  · simp [respAfter, stateAfter, ObjSpec.runOps, Ne.symm hv]

/-! ### Lemma 5: counters -/

/-- Operations of a counter. -/
inductive CtrOp where
  | inc
  | read

/-- A counter (values `ℕ`, initially `0`; `inc` returns `0` as an acknowledgement). -/
abbrev counter : ObjSpec where
  State := ℕ
  Op := CtrOp
  Resp := ℕ
  init := 0
  δ s
    | .inc => (s + 1, 0)
    | .read => (s, s)

/-- A bounded counter with values `0, …, k` (`inc` saturates at `k`). -/
abbrev bcounter (k : ℕ) : ObjSpec where
  State := ℕ
  Op := CtrOp
  Resp := ℕ
  init := 0
  δ s
    | .inc => (min (s + 1) k, 0)
    | .read => (s, s)

/-- **Lemma 5.** A counter is doubly-perturbing (witness: `inc` by `p`, perturbing w.r.t.
`read` by `q`, with the empty extension). -/
theorem counter_doublyPerturbing (p q : P) (hpq : q ≠ p) : DoublyPerturbing counter P :=
  ⟨p, .inc, [], q, .read, ⟨hpq, by simp [respAfter, stateAfter, ObjSpec.runOps]⟩, [],
    by simp, q, .read, hpq, by simp [respAfter, stateAfter, ObjSpec.runOps]⟩

/-- **Lemma 5** for the bounded counter with values `{0, 1, 2}` (the paper's example of a
doubly-perturbing object that is not perturbable). -/
theorem bcounter_doublyPerturbing (p q : P) (hpq : q ≠ p) : DoublyPerturbing (bcounter 2) P :=
  ⟨p, .inc, [], q, .read, ⟨hpq, by simp [respAfter, stateAfter, ObjSpec.runOps]⟩, [],
    by simp, q, .read, hpq, by simp [respAfter, stateAfter, ObjSpec.runOps]⟩

/-! ### Lemma 6: compare-and-swap -/

/-- **Lemma 6.** A CAS object with at least two values is doubly-perturbing (witness:
`cas v₀ v₁` by `p`, perturbing w.r.t. `cas v₀ v₁` by `q`; extension `cas v₁ v₀` by `q`). -/
theorem cas_doublyPerturbing {V : Type} [DecidableEq V] (v₀ v₁ : V) (hv : v₀ ≠ v₁) (p q : P)
    (hpq : q ≠ p) : DoublyPerturbing (casObject V v₀) P := by
  refine ⟨p, .cas v₀ v₁, [], q, .cas v₀ v₁, ⟨hpq, ?_⟩, [(q, .cas v₁ v₀)], by simp [hpq], q,
    .cas v₀ v₁, hpq, ?_⟩
  · simp [respAfter, stateAfter, ObjSpec.runOps, Ne.symm hv]
  · simp [respAfter, stateAfter, ObjSpec.runOps, Ne.symm hv]

/-- Operations of the CAS object of the paper: `read` and `cas old new`. -/
inductive RCOp (V : Type) where
  | read
  | cas (old new : V)

/-- The CAS object of the paper (Sections 4.1–4.2): `read` returns the value (`.inl v`),
`cas old new` returns whether it succeeded (`.inr b`). -/
abbrev casRC (V : Type) [DecidableEq V] (v₀ : V) : ObjSpec where
  State := V
  Op := RCOp V
  Resp := V ⊕ Bool
  init := v₀
  δ s
    | .read => (s, .inl s)
    | .cas old new => if s = old then (new, .inr true) else (s, .inr false)

/-- **Lemma 6** for the read/CAS object `casRC`. -/
theorem casRC_doublyPerturbing {V : Type} [DecidableEq V] (v₀ v₁ : V) (hv : v₀ ≠ v₁) (p q : P)
    (hpq : q ≠ p) : DoublyPerturbing (casRC V v₀) P := by
  refine ⟨p, .cas v₀ v₁, [], q, .cas v₀ v₁, ⟨hpq, ?_⟩, [(q, .cas v₁ v₀)], by simp [hpq], q,
    .cas v₀ v₁, hpq, ?_⟩
  · simp [respAfter, stateAfter, ObjSpec.runOps, Ne.symm hv]
  · simp [respAfter, stateAfter, ObjSpec.runOps, Ne.symm hv]

/-! ### Lemma 7: fetch-and-add -/

/-- Operations of a fetch-and-add object. -/
inductive FAAOp where
  | faa (d : ℤ)
  | read

/-- A fetch-and-add object (values `ℤ`, initially `0`; `faa d` returns the old value). -/
abbrev faaObj : ObjSpec where
  State := ℤ
  Op := FAAOp
  Resp := ℤ
  init := 0
  δ s
    | .faa d => (s + d, s)
    | .read => (s, s)

/-- **Lemma 7.** A fetch-and-add object is doubly-perturbing (witness: `faa 1` by `p`,
perturbing w.r.t. `read` by `q`). -/
theorem faa_doublyPerturbing (p q : P) (hpq : q ≠ p) : DoublyPerturbing faaObj P :=
  ⟨p, .faa 1, [], q, .read, ⟨hpq, by simp [respAfter, stateAfter, ObjSpec.runOps]⟩, [],
    by simp, q, .read, hpq, by simp [respAfter, stateAfter, ObjSpec.runOps]⟩

/-! ### Lemma 8: FIFO queues -/

/-- **Lemma 8.** A FIFO queue with at least two values is doubly-perturbing (witness: `deq` by
`p` after `enq v₀ ∘ enq v₁`, perturbing w.r.t. `deq` by `q`; extension `enq v₀ ∘ enq v₁` by
`q`). -/
theorem queue_doublyPerturbing {V : Type} (v₀ v₁ : V) (hv : v₀ ≠ v₁) (p q : P) (hpq : q ≠ p) :
    DoublyPerturbing (queueObj V) P := by
  refine ⟨p, .deq, [(p, .enq v₀), (p, .enq v₁)], q, .deq, ⟨hpq, ?_⟩,
    [(q, .enq v₀), (q, .enq v₁)], by simp [hpq], q, .deq, hpq, ?_⟩
  · simp [respAfter, stateAfter, ObjSpec.runOps, Ne.symm hv]
  · simp [respAfter, stateAfter, ObjSpec.runOps, Ne.symm hv]

/-! ### Lemma 4: max registers are not doubly-perturbing -/

lemma maxReg_runOps_ge (s : ℕ) (os : List MaxOp) : s ≤ maxRegObj.runOps s os := by
  induction os generalizing s with
  | nil => exact le_rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    refine le_trans ?_ (ih _)
    cases o with
    | writeMax v => exact le_max_left _ _
    | readMax => exact le_rfl

lemma maxReg_stateAfter_read (H : List (P × MaxOp)) (p : P) :
    stateAfter maxRegObj (H ++ [(p, .readMax)]) = stateAfter maxRegObj H := by
  rw [stateAfter_append]; rfl

lemma maxReg_stateAfter_wm (H : List (P × MaxOp)) (p : P) (v : ℕ)
    (h : v ≤ stateAfter maxRegObj H) :
    stateAfter maxRegObj (H ++ [(p, .writeMax v)]) = stateAfter maxRegObj H := by
  rw [stateAfter_append]; exact max_eq_left h

/-- **Lemma 4.** A max register is not doubly-perturbing. -/
theorem maxReg_not_doublyPerturbing : ¬ DoublyPerturbing maxRegObj P := by
  rintro ⟨p, o, H₁, r, o_r, ⟨-, h1⟩, E, -, q, o_q, -, h2⟩
  cases o with
  | readMax =>
    apply h1
    simp only [respAfter]
    rw [maxReg_stateAfter_read]
  | writeMax v =>
    apply h2
    have hge : v ≤ stateAfter maxRegObj (H₁ ++ [(p, .writeMax v), (r, o_r)] ++ E) := by
      have e : H₁ ++ [(p, MaxOp.writeMax v), (r, o_r)] ++ E =
          (H₁ ++ [(p, .writeMax v)]) ++ ((r, o_r) :: E) := by simp
      rw [e, stateAfter_append]
      refine le_trans ?_ (maxReg_runOps_ge _ _)
      rw [stateAfter_append]
      exact le_max_right _ _
    simp only [respAfter]
    rw [maxReg_stateAfter_wm _ _ _ hge]

end Papers.PODC2020.DetectableSpace
