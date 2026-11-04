import Mathlib

/-!
# k-atomicity of read/write histories: basic definitions

Golab, Li, López-Ortiz, Nishimura, *Computing k-Atomicity in Polynomial Time*,
SIAM J. Comput. 47(2), 2018 (journal version of *Computing Weak Consistency in Polynomial Time*,
PODC 2015), Section 3.

## Model

A history on a single read/write register is a finite collection of operations, each an interval
of time `[s op, f op]` with `s op < f op` (times are natural numbers: the paper numbers the events
`1, 2, …`). Under the paper's standing assumption that all written values are distinct
(Assumption 3.2 / "all the values written to a given object are distinct"), a write is identified
with the value it writes, so the operations are `V ⊕ R`:

* `Sum.inl v` is the write `w(v)` of value `v : V` (`V` = the set of written values);
* `Sum.inr r` is the read `r : R`, which returns `H.val r : V`; its unique dictating write is
  `w(H.val r)` (Assumption 3.2 is built into the representation).

`H.hb a b` is Herlihy–Wing's "happens before" `a <_H b`, i.e. `f a < s b`.
-/

namespace Podc.KAtomicityVerification

/-- A history of reads and writes on one register: writes indexed by the (distinct) values they
write, reads indexed by `R`, each read returning a written value (Assumption 3.2). -/
structure History (V R : Type*) where
  /-- The value returned by each read. -/
  val : R → V
  /-- Start (invocation) time of an operation. -/
  s : V ⊕ R → ℕ
  /-- Finish (response) time of an operation. -/
  f : V ⊕ R → ℕ
  s_lt_f : ∀ o, s o < f o

variable {V R : Type*}

namespace History

variable (H : History V R)

/-- Herlihy–Wing's happens-before relation `a <_H b`: `a` finishes before `b` starts. -/
def hb (a b : V ⊕ R) : Prop := H.f a < H.s b

/-- The paper's model: every event (invocation or response) carries a unique time. -/
def DistinctTimes : Prop :=
  Function.Injective (fun e : (V ⊕ R) ⊕ (V ⊕ R) => e.elim H.s H.f)

/-- Assumption 3.3: a value is not read before it is written (`r ≮_H w(val r)`). -/
def Assumption33 : Prop := ∀ r : R, ¬ H.hb (.inr r) (.inl (H.val r))

/-- Assumption 3.4: a read never finishes before its dictating write (`f(w) < f(r)`). -/
def Assumption34 : Prop := ∀ r : R, H.f (.inl (H.val r)) < H.f (.inr r)

/-- Assumption 4.1: every write `w(v)` has a dictated read `r(v)` with `w(v) <_H r(v)`. -/
def Assumption41 : Prop := ∀ v : V, ∃ r : R, H.val r = v ∧ H.hb (.inl v) (.inr r)

/-- Definition 3.7: the write graph `G_W`, edge `(v, v')` iff `w(v) <_H w(v')`. -/
def EW (a b : V) : Prop := H.hb (.inl a) (.inl b)

/-- Definition 3.6: the read value graph `G_R`, edge `(v, v')` iff `v ≠ v'` and some read
`r(v')` of `v'` satisfies `w(v) <_H r(v')`. -/
def ER (a b : V) : Prop := a ≠ b ∧ ∃ r : R, H.val r = b ∧ H.hb (.inl a) (.inr r)

/-- `lt` is a `k`-atomic total order for `H`: a strict total order on the operations that
extends `<_H`, in which every read `r` returns the value of one of the last `k` writes that
precede it, i.e. its dictating write `w(val r)` precedes `r` and fewer than `k` writes lie
strictly between them. -/
def IsKAtomicOrder (k : ℕ) (lt : V ⊕ R → V ⊕ R → Prop) : Prop :=
  IsStrictTotalOrder (V ⊕ R) lt ∧
  (∀ a b, H.hb a b → lt a b) ∧
  ∀ r : R, lt (.inl (H.val r)) (.inr r) ∧
    {v : V | lt (.inl (H.val r)) (.inl v) ∧ lt (.inl v) (.inr r)}.ncard < k

/-- Definition 3.1: `H` is `k`-atomic iff it has a `k`-atomic total order. -/
def KAtomic (k : ℕ) : Prop := ∃ lt, H.IsKAtomicOrder k lt

/-- The condition of Lemma 3.8 on a sequence `T = v₀, v₁, …` of values: `T` lists every written
value exactly once, it is a topological ordering of `G_W`, and every edge `(vᵢ, vⱼ)` of `G_R`
satisfies `j > i - k` (stated as `i < j + k`). Such a `T` is a `k`-atomic value order. -/
structure IsKAtomicValueOrder (k : ℕ) (T : List V) : Prop where
  nodup : T.Nodup
  complete : ∀ v, v ∈ T
  topo : ∀ (i j : ℕ) (hi : i < T.length) (hj : j < T.length), H.EW T[i] T[j] → i < j
  back : ∀ (i j : ℕ) (hi : i < T.length) (hj : j < T.length), H.ER T[i] T[j] → i < j + k

/-- A topological ordering of the write graph `G_W` (all values, each once). -/
structure IsTopoOrder (T : List V) : Prop where
  nodup : T.Nodup
  complete : ∀ v, v ∈ T
  topo : ∀ (i j : ℕ) (hi : i < T.length) (hj : j < T.length), H.EW T[i] T[j] → i < j

/-! ### Elementary facts -/

variable {H}

lemma hb_trans {a b c : V ⊕ R} (hab : H.hb a b) (hbc : H.hb b c) : H.hb a c :=
  lt_trans hab (lt_trans (H.s_lt_f b) hbc)

lemma hb_irrefl (a : V ⊕ R) : ¬ H.hb a a := fun h => absurd (lt_trans h (H.s_lt_f a)) (lt_irrefl _)

lemma hb_asymm {a b : V ⊕ R} (hab : H.hb a b) : ¬ H.hb b a := fun hba => hb_irrefl a (hb_trans hab hba)

/-- `<_H` is an interval order: `a <_H b` and `c <_H d` imply `a <_H d` or `c <_H b`. -/
lemma hb_interval {a b c d : V ⊕ R} (hab : H.hb a b) (hcd : H.hb c d) : H.hb a d ∨ H.hb c b := by
  unfold hb at *
  by_contra h
  simp only [not_or, not_lt] at h
  have := H.s_lt_f b
  have := H.s_lt_f d
  omega

lemma EW_trans {a b c : V} (hab : H.EW a b) (hbc : H.EW b c) : H.EW a c := hb_trans hab hbc

lemma EW_irrefl (a : V) : ¬ H.EW a a := hb_irrefl _

lemma EW_asymm {a b : V} (hab : H.EW a b) : ¬ H.EW b a := hb_asymm hab

/-- Assumption 3.4 implies Assumption 3.3. -/
lemma assumption33_of_assumption34 (h : H.Assumption34) : H.Assumption33 := by
  intro r hr
  have := h r
  have := H.s_lt_f (.inl (H.val r))
  unfold hb at hr
  omega

end History

end Podc.KAtomicityVerification
