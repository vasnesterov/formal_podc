import Cslib.Computability.Distributed.SharedMemory.Objects.Iface
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The `n`-process long-lived approximate agreement object (`n`-LLAA)

Attiya, Castañeda, Hendler, Perrin, *Separating Lock-Freedom from Wait-Freedom*, PODC 2018
(cited as [ACHP18]), Definitions 1 and 2.

Every process belongs to a *side* `0` or `1` and invokes the single operation `output()`, which
returns a real number. In a sequential execution, the *current position* of side `i` is the
output of the last operation of a process of side `i`, or `i` if there is none. The sequential
specification contains the sequential executions every prefix of which satisfies the
*convergence requirement*: the distance between the two current positions is at most `1/2^r`,
where `r` is the number of operations of the prefix.

## Modelling

* The operation invoked by a process of side `i` is `i : Fin 2` (the object "knows" the side of
  the invoking process, as in the paper); `llaaObj` is the interface (operations `Fin 2`,
  responses `ℝ`) and `llaaSpec` the nondeterministic sequential specification. Since the
  specification only depends on the sides, `n`-LLAA and 2-LLAA (Definition 1, one process per
  side) have the same specification.
* `llaaSpec.Legal llaaSpec.init l` is "every prefix of `l` satisfies the convergence
  requirement" (Definition 2).

## Main statements

* `legal_iff_forall` — legality as a bound at every prefix.
* `close_of_legal` — the arithmetic core of Theorem 11: if only one operation of side `0` is
  linearized (with output `v`), every operation of side `1` linearized at position `≥ k + 2`
  (output `x`) satisfies `|x - v| < 1/2^(k+1)`.
* `half_le_of_legal_zero`, `le_three_eighths_of_legal` — the two outputs used in Lemma 10.
-/

namespace Podc.LockFreeVsWaitFree

open Cslib SharedMemory

/-- The interface of the LLAA object: the operation `output()` of a process of side `i` is `i`,
responses are reals. (The deterministic transition function is a dummy; the actual
specification is the nondeterministic `llaaSpec`.) -/
abbrev llaaObj : ObjSpec := ObjSpec.iface (Fin 2) ℝ

/-- States of the LLAA specification: the current positions of the two sides and the number of
operations so far. -/
structure LLAAState where
  /-- Current position of each side. -/
  pos : Fin 2 → ℝ
  /-- Number of operations so far. -/
  cnt : ℕ

/-- The initial state: side `i` is at position `i`, no operations. -/
def llaaInit : LLAAState := ⟨fun i => ((i : ℕ) : ℝ), 0⟩

/-- The sequential specification of `n`-LLAA (Definition 2 of [ACHP18]): an `output()` of side
`i` may return any `x` such that, after it, the two current positions are at distance at most
`1/2^r`, `r` the number of operations so far (this one included). -/
abbrev llaaSpec : NSpec (Fin 2) ℝ where
  State := LLAAState
  init := llaaInit
  Step s i x s' := s' = ⟨Function.update s.pos i x, s.cnt + 1⟩ ∧
    |s'.pos 0 - s'.pos 1| ≤ (1 / 2 : ℝ) ^ (s.cnt + 1)

/-- The state after a sequence of operations with outputs. -/
def upd (s : LLAAState) (a : Fin 2 × ℝ) : LLAAState := ⟨Function.update s.pos a.1 a.2, s.cnt + 1⟩

/-- The state after a sequence of operations with outputs. -/
def runL (s : LLAAState) (l : List (Fin 2 × ℝ)) : LLAAState := l.foldl upd s

@[simp] lemma runL_nil (s : LLAAState) : runL s [] = s := rfl

lemma runL_append (s : LLAAState) (l₁ l₂ : List (Fin 2 × ℝ)) :
    runL s (l₁ ++ l₂) = runL (runL s l₁) l₂ := by
  simp [runL, List.foldl_append]

@[simp] lemma runL_singleton (s : LLAAState) (a : Fin 2 × ℝ) : runL s [a] = upd s a := rfl

lemma runL_cnt (s : LLAAState) (l : List (Fin 2 × ℝ)) : (runL s l).cnt = s.cnt + l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih => simp [runL_append, upd, ih]; omega

/-- Operations of the other side do not move side `i`. -/
lemma runL_pos_of_forall_ne (s : LLAAState) {l : List (Fin 2 × ℝ)} {i : Fin 2}
    (h : ∀ a ∈ l, a.1 ≠ i) : (runL s l).pos i = s.pos i := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [runL_append, runL_singleton]
    simp only [upd]
    rw [Function.update_of_ne (Ne.symm (h a (by simp)))]
    exact ih fun b hb => h b (by simp [hb])

@[simp] lemma upd_pos_self (s : LLAAState) (i : Fin 2) (x : ℝ) : (upd s (i, x)).pos i = x := by
  simp [upd]

lemma upd_pos_ne (s : LLAAState) {i j : Fin 2} (x : ℝ) (h : i ≠ j) :
    (upd s (i, x)).pos j = s.pos j := by
  simp [upd, Function.update_of_ne (Ne.symm h)]

lemma legal_append (s : LLAAState) (l₁ l₂ : List (Fin 2 × ℝ)) :
    llaaSpec.Legal s (l₁ ++ l₂) ↔ llaaSpec.Legal s l₁ ∧ llaaSpec.Legal (runL s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp
  | cons a l₁ ih =>
    obtain ⟨i, x⟩ := a
    simp only [List.cons_append, NSpec.legal_cons]
    constructor
    · rintro ⟨q', ⟨rfl, hb⟩, hl⟩
      exact ⟨⟨_, ⟨rfl, hb⟩, ((ih _).1 hl).1⟩, ((ih _).1 hl).2⟩
    · rintro ⟨⟨q', ⟨rfl, hb⟩, hl⟩, hl₂⟩
      exact ⟨_, ⟨rfl, hb⟩, (ih _).2 ⟨hl, hl₂⟩⟩

lemma legal_singleton (s : LLAAState) (a : Fin 2 × ℝ) :
    llaaSpec.Legal s [a] ↔ |(upd s a).pos 0 - (upd s a).pos 1| ≤ (1 / 2 : ℝ) ^ (s.cnt + 1) := by
  obtain ⟨i, x⟩ := a
  simp only [NSpec.legal_cons, NSpec.legal_nil, and_true]
  constructor
  · rintro ⟨q', ⟨rfl, h⟩⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

/-- The positions after the first `t` operations of `l`. -/
def posAt (l : List (Fin 2 × ℝ)) (t : ℕ) : LLAAState := runL llaaInit (l.take t)

/-- Legality of a sequence: the convergence requirement holds after every prefix. -/
lemma legal_iff_forall (l : List (Fin 2 × ℝ)) :
    llaaSpec.Legal llaaSpec.init l ↔
      ∀ t < l.length, |(posAt l (t + 1)).pos 0 - (posAt l (t + 1)).pos 1| ≤ (1 / 2 : ℝ) ^ (t + 1) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [legal_append, ih, legal_singleton]
    have hcnt : (runL llaaInit l).cnt = l.length := by
      rw [runL_cnt]; simp [llaaInit]
    have hpos : ∀ t ≤ l.length, posAt (l ++ [a]) t = posAt l t := by
      intro t ht; simp [posAt, List.take_append_of_le_length ht]
    have hlast : posAt (l ++ [a]) (l.length + 1) = upd (runL llaaInit l) a := by
      simp [posAt, List.take_of_length_le, runL_append]
    rw [hcnt]
    constructor
    · rintro ⟨h1, h2⟩ t ht
      simp only [List.length_append, List.length_singleton] at ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [hpos _ ht]; exact h1 t ht
      · rw [hlast]; exact h2
    · intro h
      refine ⟨fun t ht => ?_, ?_⟩
      · have := h t (by simp; omega); rwa [hpos _ ht] at this
      · have := h l.length (by simp); rwa [hlast] at this

lemma posAt_succ {l : List (Fin 2 × ℝ)} {t : ℕ} {a : Fin 2 × ℝ} (h : l[t]? = some a) :
    posAt l (t + 1) = upd (posAt l t) a := by
  have ht : t < l.length := by
    by_contra h'; rw [List.getElem?_eq_none (by omega)] at h; cases h
  simp only [posAt]
  rw [List.take_add_one, h]; simp [runL_append]

/-- Side `i` has not moved during the first `t` operations if they all belong to the other
side. -/
lemma posAt_pos_of_forall {l : List (Fin 2 × ℝ)} {i : Fin 2} {t : ℕ}
    (h : ∀ u < t, ∀ a, l[u]? = some a → a.1 ≠ i) : (posAt l t).pos i = ((i : ℕ) : ℝ) := by
  simp only [posAt]
  rw [runL_pos_of_forall_ne]
  · rfl
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_take] at hu
    have := h u (by omega) _ (by rw [List.getElem?_eq_getElem (by omega)])
    simpa using this

/-- After the operation at position `j` (side `i`, output `v`), side `i` stays at `v` as long as
only the other side operates. -/
lemma posAt_pos_after {l : List (Fin 2 × ℝ)} {i : Fin 2} {j t : ℕ} {v : ℝ}
    (hj : l[j]? = some (i, v)) (hjt : j < t)
    (h : ∀ u < t, j < u → ∀ a, l[u]? = some a → a.1 ≠ i) : (posAt l t).pos i = v := by
  induction t, hjt using Nat.le_induction with
  | base => rw [posAt_succ hj]; simp
  | succ t hjt ih =>
    rw [← ih (fun u hu hju a ha => h u (by omega) hju a ha)]
    cases hlt : l[t]? with
    | none =>
      have : l.length ≤ t := by simpa using hlt
      simp [posAt, List.take_of_length_le this, List.take_of_length_le (show l.length ≤ t + 1 by omega)]
    | some a =>
      rw [posAt_succ hlt]
      obtain ⟨i', x⟩ := a
      exact upd_pos_ne _ _ (h t (by omega) (by omega) _ hlt)

/-- The bound at the step of position `t`. -/
lemma bound_at {l : List (Fin 2 × ℝ)} (hl : llaaSpec.Legal llaaSpec.init l) {t : ℕ}
    {a : Fin 2 × ℝ} (ha : l[t]? = some a) :
    |(posAt l (t + 1)).pos 0 - (posAt l (t + 1)).pos 1| ≤ (1 / 2 : ℝ) ^ (t + 1) := by
  have ht : t < l.length := by
    by_contra h'; rw [List.getElem?_eq_none (by omega)] at ha; cases ha
  exact (legal_iff_forall l).1 hl t ht

lemma half_pow_le {m k : ℕ} (h : k ≤ m) : (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ k :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- **Arithmetic core of Theorem 11** ([ACHP18], end of the proof). Let `l` be a legal sequence
in which the only operation of side `0` is at position `j` with output `v`, and the operation at
position `i ≥ k + 2` (of side `1`) has output `x`. Then `|x - v| < 1/2^(k+1)`. -/
theorem close_of_legal {l : List (Fin 2 × ℝ)} (hl : llaaSpec.Legal llaaSpec.init l)
    {i j k : ℕ} {x v : ℝ} (hj : l[j]? = some (0, v))
    (hone : ∀ t a, l[t]? = some a → t ≠ j → a.1 = 1) (hi : l[i]? = some (1, x))
    (hk : k + 2 ≤ i) : |x - v| < (1 / 2 : ℝ) ^ (k + 1) := by
  have hij : i ≠ j := by rintro rfl; rw [hi] at hj; cases hj
  have hside : ∀ u, ∀ a, l[u]? = some a → u ≠ j → a.1 ≠ 0 := by
    intro u a ha hu; rw [hone u a ha hu]; decide
  have hp : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- the operation of `x` is linearized before the operation of side `0`
    have b1 := bound_at hl hi
    rw [posAt_pos_of_forall (i := 0) (fun u hu a ha => hside u a ha (by omega)),
      posAt_succ hi, upd_pos_self] at b1
    have hj0 : 0 < j := by omega
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨a', ha'⟩ : ∃ a', l[j']? = some a' := by
      have : j' < l.length := by
        have : j' + 1 < l.length := by
          by_contra h'; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
        omega
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have b2 := bound_at hl ha'
    rw [posAt_pos_of_forall (i := 0) (fun u hu a ha => hside u a ha (by omega))] at b2
    have b3 := bound_at hl hj
    rw [posAt_succ hj, upd_pos_self, upd_pos_ne _ _ (by decide)] at b3
    set y := (posAt l (j' + 1)).pos 1
    have e1 : (1 / 2 : ℝ) ^ (i + 1) ≤ (1 / 2) ^ (k + 3) := half_pow_le (by omega)
    have e2 : (1 / 2 : ℝ) ^ (j' + 1) ≤ (1 / 2) ^ (k + 3) := half_pow_le (by omega)
    have e3 : (1 / 2 : ℝ) ^ (j' + 1 + 1) ≤ (1 / 2) ^ (k + 4) := half_pow_le (by omega)
    have hpow : (1 / 2 : ℝ) ^ (k + 3) = (1 / 2) ^ (k + 1) / 4 := by ring
    have hpow' : (1 / 2 : ℝ) ^ (k + 4) = (1 / 2) ^ (k + 1) / 8 := by ring
    norm_num at b1 b2
    calc |x - v| ≤ |x - 0| + |0 - y| + |y - v| := by
          have := abs_sub_le x 0 v; have := abs_sub_le 0 y v; linarith
      _ ≤ (1 / 2) ^ (k + 3) + (1 / 2) ^ (k + 3) + (1 / 2) ^ (k + 4) := by
          rw [abs_sub_comm y v]; simp only [sub_zero, zero_sub, abs_neg]; linarith
      _ < (1 / 2) ^ (k + 1) := by rw [hpow, hpow']; linarith
  · -- the operation of `x` is linearized after the operation of side `0`
    have b := bound_at hl hi
    rw [posAt_pos_after (i := 0) hj (by omega) (fun u _ hju a ha => hside u a ha (by omega)),
      posAt_succ hi, upd_pos_self] at b
    have e : (1 / 2 : ℝ) ^ (i + 1) ≤ (1 / 2) ^ (k + 3) := half_pow_le (by omega)
    have hpow : (1 / 2 : ℝ) ^ (k + 3) = (1 / 2) ^ (k + 1) / 4 := by ring
    rw [abs_sub_comm]; linarith

/-- If the only operation of side `0` is linearized first, its output is at least `1/2`
([ACHP18], proof of Lemma 10, solo execution of `p₀`). -/
theorem half_le_of_legal_zero {l : List (Fin 2 × ℝ)} (hl : llaaSpec.Legal llaaSpec.init l)
    {v : ℝ} (hj : l[0]? = some (0, v)) : 1 / 2 ≤ v := by
  have b := bound_at hl hj
  rw [posAt_succ hj, upd_pos_self, upd_pos_ne _ _ (by decide)] at b
  have : (posAt l 0).pos 1 = 1 := by simp [posAt, llaaInit]
  rw [this] at b
  have := (abs_le.1 b).1; norm_num at this ⊢; linarith

/-- If the only operation of side `0` is linearized at a position `j ≥ 2`, its output is at most
`3/8` ([ACHP18], proof of Lemma 10, after two operations of side `1`). -/
theorem le_three_eighths_of_legal {l : List (Fin 2 × ℝ)} (hl : llaaSpec.Legal llaaSpec.init l)
    {j : ℕ} {v : ℝ} (hj : l[j]? = some (0, v))
    (hone : ∀ t a, l[t]? = some a → t ≠ j → a.1 = 1) (h2 : 2 ≤ j) : v ≤ 3 / 8 := by
  have hside : ∀ u, ∀ a, l[u]? = some a → u ≠ j → a.1 ≠ 0 := by
    intro u a ha hu; rw [hone u a ha hu]; decide
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨a', ha'⟩ : ∃ a', l[j']? = some a' := by
    have : j' + 1 < l.length := by
      by_contra h'; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have b2 := bound_at hl ha'
  rw [posAt_pos_of_forall (i := 0) (fun u hu a ha => hside u a ha (by omega))] at b2
  have b3 := bound_at hl hj
  rw [posAt_succ hj, upd_pos_self, upd_pos_ne _ _ (by decide)] at b3
  set y := (posAt l (j' + 1)).pos 1
  have e2 : (1 / 2 : ℝ) ^ (j' + 1) ≤ (1 / 2) ^ 2 := half_pow_le (by omega)
  have e3 : (1 / 2 : ℝ) ^ (j' + 1 + 1) ≤ (1 / 2) ^ 3 := half_pow_le (by omega)
  norm_num at b2
  have h1 := (abs_le.1 b2).2
  have h2 := (abs_le.1 b3).2
  norm_num at e2 e3
  linarith

/-- Non-vacuity: the specification has legal sequences, e.g. side `0` outputs `1/2`, then side
`1` outputs `1/2` (the sequential execution `p₀ : 1/2, p₁ : 1/2`). -/
example : llaaSpec.Legal llaaSpec.init [(0, 1 / 2), (1, 1 / 2)] := by
  refine ⟨_, ⟨rfl, ?_⟩, _, ⟨rfl, ?_⟩, trivial⟩ <;> norm_num [llaaInit, Function.update_apply]

end Podc.LockFreeVsWaitFree
