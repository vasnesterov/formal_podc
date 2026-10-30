/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Foundations/Data/Mazurkiewicz/Equiv.lean
import Podc.Foundations.Data.Mazurkiewicz.Defs

/-!
# Trace equivalence of general schedules

Schedules are lists over an alphabet `α` (repetitions allowed) and `D` is a dependence relation.
Occurrences of letters are pairs `(a, i)`: the `i`-th (0-based) occurrence of `a`.

* `occ s a i`: the position of the `i`-th occurrence of `a` in `s`;
* `OccBefore s x y`: both occurrences exist in `s` and `x` is at a smaller position than `y`;
* `TraceEquiv D s t`: `t` is a permutation of `s` preserving the order of every pair of
  occurrences of dependent letters (the equivalence of schedules of [KST26], Section 4.1).
  It is an equivalence relation for symmetric `D` and a congruence for `++`;
* `SwapStep D`, `SwapEquiv D`: one swap of adjacent independent letters, and its
  reflexive-transitive closure; `traceEquiv_iff_swapEquiv`: the two equivalences coincide
  (for symmetric `D`);
* `respOcc δ q s a i`: the response of the occurrence `(a, i)` when running the deterministic
  machine `δ` on `s` from `q`;
* Lemma 4.1 of [KST26] (`respOcc_eq_of_traceEquiv`, `runState_eq_of_traceEquiv`,
  `respOcc_eq_of_traceEquiv_conflict`): equivalent schedules give the same responses and the same
  final state, provided independent letters commute;
* Lemma 4.2 of [KST26] (`respOcc_eq_of_traceEquiv_append`, `respOcc_eq_of_le_conflict`):
  responses are stable under trace extension;
* bridge to duplicate-free schedules: `traceEquiv_iff_nequiv`, `respFirst_eq_of_nequiv`,
  `runState_eq_of_nequiv`, `respFirst_append_of_mem`, `respFirst_isSome_iff`.

## References

* [KST26] P. Kuznetsov, P. Sutra, G. Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*,
  PODC 2026.
-/

namespace Cslib.Mazurkiewicz

variable {α : Type*} [DecidableEq α]

/-! ### Occurrences -/

section Occ

/-- The position of the `i`-th (0-based) occurrence of `a` in `s` (`none` if `a` occurs at most
`i` times in `s`). -/
def occ : List α → α → ℕ → Option ℕ
  | [], _, _ => none
  | x :: s, a, 0 => if x = a then some 0 else (occ s a 0).map (· + 1)
  | x :: s, a, i + 1 => if x = a then (occ s a i).map (· + 1) else (occ s a (i + 1)).map (· + 1)

@[simp] lemma occ_nil (a : α) (i : ℕ) : occ [] a i = none := rfl

@[simp] lemma occ_cons_self_zero (a : α) (s : List α) : occ (a :: s) a 0 = some 0 := by
  simp [occ]

@[simp] lemma occ_cons_self_succ (a : α) (s : List α) (i : ℕ) :
    occ (a :: s) a (i + 1) = (occ s a i).map (· + 1) := by
  simp [occ]

lemma occ_cons_of_ne {x a : α} (h : x ≠ a) (s : List α) (i : ℕ) :
    occ (x :: s) a i = (occ s a i).map (· + 1) := by
  cases i <;> simp [occ, h]

/-- Prepending a letter `x` shifts the positions by one and the occurrence indices of `x` by
one. -/
lemma occ_cons_add (x : α) (s : List α) (a : α) (i : ℕ) :
    occ (x :: s) a (i + if x = a then 1 else 0) = (occ s a i).map (· + 1) := by
  by_cases h : x = a
  · subst h; simp
  · simp [h, occ_cons_of_ne h]

lemma occ_isSome_iff (s : List α) (a : α) (i : ℕ) : (occ s a i).isSome ↔ i < s.count a := by
  induction s generalizing i with
  | nil => simp
  | cons x s ih =>
    by_cases h : x = a
    · subst h
      cases i with
      | zero => simp
      | succ i => simp [ih]
    · rw [occ_cons_of_ne h]
      simp [ih, h]

lemma occ_eq_none_iff (s : List α) (a : α) (i : ℕ) : occ s a i = none ↔ s.count a ≤ i := by
  rw [← not_lt, ← occ_isSome_iff, Option.not_isSome_iff_eq_none]

lemma getElem?_of_occ {s : List α} {a : α} {i p : ℕ} (h : occ s a i = some p) :
    s[p]? = some a := by
  induction s generalizing i p with
  | nil => simp at h
  | cons x s ih =>
    by_cases hx : x = a
    · subst hx
      cases i with
      | zero => simp at h; subst h; simp
      | succ i =>
        simp only [occ_cons_self_succ, Option.map_eq_some_iff] at h
        obtain ⟨p', hp', rfl⟩ := h
        simpa using ih hp'
    · rw [occ_cons_of_ne hx, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      simpa using ih hp'

lemma occ_lt_length {s : List α} {a : α} {i p : ℕ} (h : occ s a i = some p) : p < s.length := by
  have := getElem?_of_occ h
  rw [List.getElem?_eq_some_iff] at this
  exact this.1

lemma occ_cons_eq_zero {x a : α} {s : List α} {i : ℕ} :
    occ (x :: s) a i = some 0 ↔ x = a ∧ i = 0 := by
  by_cases hx : x = a
  · subst hx
    cases i <;> simp
  · simp [occ_cons_of_ne hx, hx]

lemma occ_cons_eq_succ {x a : α} {s : List α} {i p : ℕ} :
    occ (x :: s) a i = some (p + 1) ↔
      if x = a then ∃ i', i = i' + 1 ∧ occ s a i' = some p else occ s a i = some p := by
  by_cases hx : x = a
  · subst hx
    cases i <;> simp
  · simp [occ_cons_of_ne hx, hx]

/-- Distinct occurrences are at distinct positions. -/
lemma occ_inj {s : List α} {a b : α} {i j p : ℕ} (ha : occ s a i = some p)
    (hb : occ s b j = some p) : a = b ∧ i = j := by
  induction s generalizing i j p with
  | nil => simp at ha
  | cons x s ih =>
    cases p with
    | zero =>
      rw [occ_cons_eq_zero] at ha hb
      exact ⟨ha.1.symm.trans hb.1, ha.2.trans hb.2.symm⟩
    | succ p =>
      rw [occ_cons_eq_succ] at ha hb
      split_ifs at ha hb with hxa hxb hxb
      · obtain ⟨i', rfl, ha⟩ := ha
        obtain ⟨j', rfl, hb⟩ := hb
        exact ⟨hxa.symm.trans hxb, by rw [(ih ha hb).2]⟩
      · obtain ⟨i', rfl, ha⟩ := ha
        exact absurd (hxa.trans (ih ha hb).1) hxb
      · obtain ⟨j', rfl, hb⟩ := hb
        exact absurd (hxb.trans (ih ha hb).1.symm) hxa
      · exact ih ha hb

lemma occ_append_of_lt {s : List α} {a : α} {i : ℕ} (h : i < s.count a) (z : List α) :
    occ (s ++ z) a i = occ s a i := by
  induction s generalizing i with
  | nil => simp at h
  | cons x s ih =>
    by_cases hx : x = a
    · subst hx
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.cons_append, occ_cons_self_succ]
        rw [ih (by simpa using h)]
    · simp only [List.cons_append, occ_cons_of_ne hx]
      rw [ih (by simpa [List.count_cons, hx] using h)]

lemma occ_append_cons_of_not_mem {u : List α} {a : α} (h : a ∉ u) (v : List α) :
    occ (u ++ a :: v) a 0 = some u.length := by
  induction u with
  | nil => simp
  | cons x u ih =>
    simp only [List.mem_cons, not_or] at h
    simp [occ_cons_of_ne (Ne.symm h.1), ih h.2]

/-- The transposition of the positions `n` and `n + 1`. -/
def swapPos (n p : ℕ) : ℕ := if p = n then n + 1 else if p = n + 1 then n else p

lemma swapPos_succ (n p : ℕ) : swapPos (n + 1) (p + 1) = swapPos n p + 1 := by
  unfold swapPos; split_ifs <;> omega

lemma occ_swap {a b : α} (hab : a ≠ b) (x y : List α) (c : α) (k : ℕ) :
    occ (x ++ b :: a :: y) c k = (occ (x ++ a :: b :: y) c k).map (swapPos x.length) := by
  induction x generalizing k with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    by_cases hca : c = a
    · subst hca
      have hcb : b ≠ c := Ne.symm hab
      rcases k with _ | k
      · simp [occ_cons_of_ne hcb, swapPos]
      · simp only [occ_cons_of_ne hcb, occ_cons_self_succ, Option.map_map]
        cases occ y c k <;> simp [swapPos]
    · by_cases hcb : c = b
      · subst hcb
        have hac : a ≠ c := Ne.symm hca
        rcases k with _ | k
        · simp [occ_cons_of_ne hac, swapPos]
        · simp only [occ_cons_of_ne hac, occ_cons_self_succ, Option.map_map]
          cases occ y c k <;> simp [swapPos]
      · simp only [occ_cons_of_ne (Ne.symm hca), occ_cons_of_ne (Ne.symm hcb), Option.map_map]
        cases occ y c k <;> simp [swapPos]
  | cons d x ih =>
    simp only [List.cons_append, List.length_cons]
    by_cases hd : d = c
    · subst hd
      rcases k with _ | k
      · simp [swapPos]
      · simp only [occ_cons_self_succ, ih, Option.map_map]
        cases occ (x ++ a :: b :: y) d k <;> simp [swapPos_succ]
    · simp only [occ_cons_of_ne hd, ih, Option.map_map]
      cases occ (x ++ a :: b :: y) c k <;> simp [swapPos_succ]

/-- The occurrence `x` precedes the occurrence `y` in `s` (both exist). -/
def OccBefore (s : List α) (x y : α × ℕ) : Prop :=
  ∃ p p', occ s x.1 x.2 = some p ∧ occ s y.1 y.2 = some p' ∧ p < p'

lemma OccBefore.irrefl (s : List α) (x : α × ℕ) : ¬ OccBefore s x x := by
  rintro ⟨p, p', h, h', hlt⟩
  rw [h] at h'; cases h'; exact lt_irrefl _ hlt

end Occ

/-! ### Trace equivalence -/

section TraceEquiv

variable (D : α → α → Prop)

/-- Equivalence of schedules ([KST26], Section 4.1): `t` is a permutation of `s` and every pair
of occurrences of dependent letters is ordered in `t` as in `s`. -/
def TraceEquiv (s t : List α) : Prop :=
  s.Perm t ∧ ∀ a b i j, D a b → OccBefore s (a, i) (b, j) → OccBefore t (a, i) (b, j)

variable {D}

namespace TraceEquiv

@[refl] lemma refl (s : List α) : TraceEquiv D s s := ⟨List.Perm.refl s, fun _ _ _ _ _ h => h⟩

lemma rfl' {s : List α} : TraceEquiv D s s := refl s

lemma trans {s t u : List α} (h₁ : TraceEquiv D s t) (h₂ : TraceEquiv D t u) :
    TraceEquiv D s u :=
  ⟨h₁.1.trans h₂.1, fun a b i j hab h => h₂.2 a b i j hab (h₁.2 a b i j hab h)⟩

lemma mono {D' : α → α → Prop} (hD : ∀ a b, D' a b → D a b) {s t : List α}
    (h : TraceEquiv D s t) : TraceEquiv D' s t :=
  ⟨h.1, fun a b i j hab => h.2 a b i j (hD a b hab)⟩

lemma symm [Std.Symm D] {s t : List α} (h : TraceEquiv D s t) : TraceEquiv D t s := by
  refine ⟨h.1.symm, fun a b i j hab ht => ?_⟩
  obtain ⟨p, p', hp, hp', hlt⟩ := ht
  have hc : ∀ c, s.count c = t.count c := fun c => h.1.count_eq c
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1
    ((occ_isSome_iff s a i).2 (by rw [hc]; exact (occ_isSome_iff t a i).1 (by simp [hp])))
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1
    ((occ_isSome_iff s b j).2 (by rw [hc]; exact (occ_isSome_iff t b j).1 (by simp [hp'])))
  rcases lt_trichotomy r r' with hrr | hrr | hrr
  · exact ⟨r, r', hr, hr', hrr⟩
  · subst hrr
    obtain ⟨rfl, rfl⟩ := occ_inj hr hr'
    rw [hp] at hp'; cases hp'; exact absurd hlt (lt_irrefl _)
  · obtain ⟨q, q', hq, hq', hqq⟩ := h.2 b a j i (Std.Symm.symm a b hab) ⟨r', r, hr', hr, hrr⟩
    simp only at hq hq'
    rw [hq] at hp'; rw [hq'] at hp; cases hp; cases hp'
    omega

/-- Cancellation of a common first letter. -/
lemma of_cons {a : α} {s t : List α} (h : TraceEquiv D (a :: s) (a :: t)) :
    TraceEquiv D s t := by
  refine ⟨h.1.cons_inv, fun b c j k hbc hs => ?_⟩
  obtain ⟨p, p', hp, hp', hlt⟩ := hs
  simp only at hp hp'
  have := h.2 b c (j + if a = b then 1 else 0) (k + if a = c then 1 else 0) hbc
    ⟨p + 1, p' + 1, by simp [occ_cons_add, hp], by simp [occ_cons_add, hp'], by omega⟩
  obtain ⟨q, q', hq, hq', hqq⟩ := this
  simp only [occ_cons_add, Option.map_eq_some_iff] at hq hq'
  obtain ⟨r, hr, rfl⟩ := hq
  obtain ⟨r', hr', rfl⟩ := hq'
  exact ⟨r, r', hr, hr', by omega⟩

end TraceEquiv

lemma traceEquiv_equivalence [Std.Symm D] : Equivalence (TraceEquiv (α := α) D) :=
  ⟨TraceEquiv.refl, TraceEquiv.symm, TraceEquiv.trans⟩

/-! ### Swaps of adjacent independent letters -/

variable (D) in
/-- One swap of two adjacent independent letters. -/
def SwapStep (s t : List α) : Prop :=
  ∃ x y a b, ¬ D a b ∧ s = x ++ a :: b :: y ∧ t = x ++ b :: a :: y

variable (D) in
/-- Equivalence generated by swaps of adjacent independent letters. -/
def SwapEquiv : List α → List α → Prop := Relation.ReflTransGen (SwapStep D)

omit [DecidableEq α] in
lemma SwapStep.symm [Std.Symm D] {s t : List α} (h : SwapStep D s t) : SwapStep D t s := by
  obtain ⟨x, y, a, b, hab, rfl, rfl⟩ := h
  exact ⟨x, y, b, a, fun h => hab (Std.Symm.symm _ _ h), rfl, rfl⟩

omit [DecidableEq α] in
lemma SwapStep.append_left {s t : List α} (h : SwapStep D s t) (z : List α) :
    SwapStep D (z ++ s) (z ++ t) := by
  obtain ⟨x, y, a, b, hab, rfl, rfl⟩ := h
  exact ⟨z ++ x, y, a, b, hab, by simp, by simp⟩

omit [DecidableEq α] in
lemma SwapStep.append_right {s t : List α} (h : SwapStep D s t) (z : List α) :
    SwapStep D (s ++ z) (t ++ z) := by
  obtain ⟨x, y, a, b, hab, rfl, rfl⟩ := h
  exact ⟨x, y ++ z, a, b, hab, by simp, by simp⟩

lemma SwapStep.traceEquiv {s t : List α} (h : SwapStep D s t) : TraceEquiv D s t := by
  obtain ⟨x, y, a, b, hab, rfl, rfl⟩ := h
  by_cases hne : a = b
  · subst hne; exact TraceEquiv.refl _
  refine ⟨List.Perm.append_left x (List.Perm.swap b a y), fun c e k l hce hs => ?_⟩
  obtain ⟨p, p', hp, hp', hlt⟩ := hs
  simp only at hp hp'
  refine ⟨swapPos x.length p, swapPos x.length p', by simp [occ_swap hne, hp],
    by simp [occ_swap hne, hp'], ?_⟩
  by_cases h1 : p = x.length ∧ p' = x.length + 1
  · obtain ⟨rfl, rfl⟩ := h1
    have hc := getElem?_of_occ hp
    have he := getElem?_of_occ hp'
    simp at hc he
    subst hc; subst he
    exact absurd hce hab
  · unfold swapPos; split_ifs <;> omega

namespace SwapEquiv

omit [DecidableEq α] in
@[refl] lemma refl (s : List α) : SwapEquiv D s s := Relation.ReflTransGen.refl

omit [DecidableEq α] in
lemma trans {s t u : List α} (h₁ : SwapEquiv D s t) (h₂ : SwapEquiv D t u) : SwapEquiv D s u :=
  Relation.ReflTransGen.trans h₁ h₂

omit [DecidableEq α] in
lemma symm [Std.Symm D] {s t : List α} (h : SwapEquiv D s t) : SwapEquiv D t s := by
  induction h with
  | refl => exact refl _
  | tail _ hst ih => exact (Relation.ReflTransGen.single hst.symm).trans ih

omit [DecidableEq α] in
lemma append_left {s t : List α} (h : SwapEquiv D s t) (z : List α) :
    SwapEquiv D (z ++ s) (z ++ t) := by
  induction h with
  | refl => exact refl _
  | tail _ hst ih => exact ih.tail (hst.append_left z)

omit [DecidableEq α] in
lemma append_right {s t : List α} (h : SwapEquiv D s t) (z : List α) :
    SwapEquiv D (s ++ z) (t ++ z) := by
  induction h with
  | refl => exact refl _
  | tail _ hst ih => exact ih.tail (hst.append_right z)

lemma traceEquiv {s t : List α} (h : SwapEquiv D s t) : TraceEquiv D s t := by
  induction h with
  | refl => exact TraceEquiv.refl _
  | tail _ hst ih => exact ih.trans hst.traceEquiv

omit [DecidableEq α] in
/-- Moving a letter to the right across letters independent of it. -/
lemma cons_append {a : α} {u : List α} (hu : ∀ b ∈ u, ¬ D a b) (v : List α) :
    SwapEquiv D (a :: (u ++ v)) (u ++ a :: v) := by
  induction u with
  | nil => exact refl _
  | cons b u ih =>
    have h1 : SwapStep D (a :: b :: (u ++ v)) (b :: a :: (u ++ v)) :=
      ⟨[], u ++ v, a, b, hu b (by simp), rfl, rfl⟩
    exact (Relation.ReflTransGen.single h1).trans
      ((ih fun c hc => hu c (by simp [hc])).append_left [b])

end SwapEquiv

omit [DecidableEq α] in
/-- Split a list at the first occurrence of a letter. -/
lemma exists_eq_append_cons_of_mem {a : α} {t : List α} (ha : a ∈ t) :
    ∃ u v, a ∉ u ∧ t = u ++ a :: v := by
  classical
  induction t with
  | nil => simp at ha
  | cons x t iht =>
    by_cases hx : x = a
    · exact ⟨[], t, by simp, by simp [hx]⟩
    · obtain ⟨u, v, hu, rfl⟩ := iht (by simpa [Ne.symm hx] using ha)
      exact ⟨x :: u, v, by simp [Ne.symm hx, hu], rfl⟩

/-- Trace-equivalent schedules differ by finitely many swaps of adjacent independent letters. -/
theorem swapEquiv_of_traceEquiv [Std.Symm D] {s t : List α} (h : TraceEquiv D s t) :
    SwapEquiv D s t := by
  induction s generalizing t with
  | nil =>
    obtain rfl := List.nil_perm.1 h.1
    exact SwapEquiv.refl _
  | cons a s ih =>
    have ha : a ∈ t := h.1.subset (by simp)
    -- the first occurrence of `a` in `t`
    obtain ⟨u, v, hau, rfl⟩ := exists_eq_append_cons_of_mem ha
    -- every letter of `u` is independent of `a`
    have hu : ∀ b ∈ u, ¬ D a b := by
      intro b hb hab
      have hba : b ≠ a := fun e => hau (e ▸ hb)
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
        ((occ_isSome_iff u b 0).2 (List.count_pos_iff.2 hb))
      have hp' : occ (u ++ a :: v) b 0 = some p := by
        rw [occ_append_of_lt (List.count_pos_iff.2 hb), hp]
      have hpu := occ_lt_length hp
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1
        ((occ_isSome_iff s b 0).2 (by
          have h1 := h.1.count_eq b
          have h2 : 0 < (u ++ a :: v).count b := List.count_pos_iff.2 (by simp [hb])
          simp only [List.count_cons, beq_iff_eq, Ne.symm hba, ↓reduceIte] at h1
          omega))
      obtain ⟨q, q', hq, hq', hqq⟩ := h.2 a b 0 0 hab
        ⟨0, r + 1, by simp, by simp [occ_cons_of_ne (Ne.symm hba), hr], by omega⟩
      simp only [occ_append_cons_of_not_mem hau, hp', Option.some.injEq] at hq hq'
      omega
    have h1 := SwapEquiv.cons_append hu v
    have h2 : TraceEquiv D (a :: s) (a :: (u ++ v)) := h.trans h1.symm.traceEquiv
    exact ((ih h2.of_cons).append_left [a]).trans h1

/-- Characterisation of trace equivalence by swaps of adjacent independent letters. -/
theorem traceEquiv_iff_swapEquiv [Std.Symm D] {s t : List α} :
    TraceEquiv D s t ↔ SwapEquiv D s t :=
  ⟨swapEquiv_of_traceEquiv, SwapEquiv.traceEquiv⟩

namespace TraceEquiv

lemma append_left [Std.Symm D] {s t : List α} (h : TraceEquiv D s t) (z : List α) :
    TraceEquiv D (z ++ s) (z ++ t) :=
  ((swapEquiv_of_traceEquiv h).append_left z).traceEquiv

lemma append_right [Std.Symm D] {s t : List α} (h : TraceEquiv D s t) (z : List α) :
    TraceEquiv D (s ++ z) (t ++ z) :=
  ((swapEquiv_of_traceEquiv h).append_right z).traceEquiv

/-- Trace equivalence is a congruence for concatenation. -/
lemma append [Std.Symm D] {s t s' t' : List α} (h : TraceEquiv D s t)
    (h' : TraceEquiv D s' t') : TraceEquiv D (s ++ s') (t ++ t') :=
  (h.append_right s').trans (h'.append_left t)

end TraceEquiv

end TraceEquiv

/-! ### Responses of occurrences (Lemmas 4.1 and 4.2) -/

section Resp

variable {Q R : Type*} (δ : Q → α → Q × R)

/-- The response of the `i`-th (0-based) occurrence of `c` when running the schedule `l` from
`q` (`none` if `c` occurs at most `i` times in `l`): `ret*(c⁽ⁱ⁺¹⁾, l)` of [KST26]. -/
def respOcc : Q → List α → α → ℕ → Option R
  | _, [], _, _ => none
  | q, a :: l, c, 0 => if a = c then some (δ q a).2 else respOcc (δ q a).1 l c 0
  | q, a :: l, c, i + 1 => if a = c then respOcc (δ q a).1 l c i else respOcc (δ q a).1 l c (i + 1)

@[simp] lemma respOcc_nil (q : Q) (c : α) (i : ℕ) : respOcc δ q [] c i = none := rfl

@[simp] lemma respOcc_cons_self_zero (q : Q) (a : α) (l : List α) :
    respOcc δ q (a :: l) a 0 = some (δ q a).2 := by simp [respOcc]

@[simp] lemma respOcc_cons_self_succ (q : Q) (a : α) (l : List α) (i : ℕ) :
    respOcc δ q (a :: l) a (i + 1) = respOcc δ (δ q a).1 l a i := by simp [respOcc]

lemma respOcc_cons_of_ne (q : Q) {a c : α} (h : a ≠ c) (l : List α) (i : ℕ) :
    respOcc δ q (a :: l) c i = respOcc δ (δ q a).1 l c i := by
  cases i <;> simp [respOcc, h]

lemma respFirst_eq_respOcc (q : Q) (l : List α) (c : α) :
    respFirst δ q l c = respOcc δ q l c 0 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [respFirst_cons, respOcc, ih]

lemma respOcc_isSome_iff (q : Q) (l : List α) (c : α) (i : ℕ) :
    (respOcc δ q l c i).isSome ↔ i < l.count c := by
  induction l generalizing q i with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = c
    · subst h
      cases i with
      | zero => simp
      | succ i => simp [ih]
    · rw [respOcc_cons_of_ne δ q h]
      simp [ih, h]

lemma respOcc_append_of_lt (q : Q) {s : List α} {a : α} {i : ℕ} (h : i < s.count a)
    (z : List α) : respOcc δ q (s ++ z) a i = respOcc δ q s a i := by
  induction s generalizing q i with
  | nil => simp at h
  | cons x s ih =>
    by_cases hx : x = a
    · subst hx
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.cons_append, respOcc_cons_self_succ]
        rw [ih _ (by simpa using h)]
    · simp only [List.cons_append, respOcc_cons_of_ne δ q hx]
      rw [ih _ (by simpa [List.count_cons, hx] using h)]

omit [DecidableEq α] in
lemma runState_append (q : Q) (x y : List α) :
    runState δ q (x ++ y) = runState δ (runState δ q x) y := by
  induction x generalizing q with
  | nil => rfl
  | cons a x ih => exact ih _

omit [DecidableEq α] in
lemma runState_swap {a b : α} (hab : ∀ q, Commute δ a b q) (q : Q) (x y : List α) :
    runState δ q (x ++ a :: b :: y) = runState δ q (x ++ b :: a :: y) := by
  rw [runState_append, runState_append]
  exact congrArg (runState δ · y) (hab _).1

lemma respOcc_swap {a b : α} (hab : ∀ q, Commute δ a b q) (q : Q) (x y : List α) (c : α)
    (k : ℕ) : respOcc δ q (x ++ a :: b :: y) c k = respOcc δ q (x ++ b :: a :: y) c k := by
  induction x generalizing q k with
  | nil =>
    simp only [List.nil_append]
    obtain ⟨h1, h2, h3⟩ := hab q
    by_cases hab' : a = b
    · subst hab'; rfl
    by_cases hca : a = c
    · subst hca
      rcases k with _ | k
      · simp [respOcc_cons_of_ne δ _ (Ne.symm hab'), h2]
      · simp [respOcc_cons_of_ne δ _ (Ne.symm hab'), h1]
    · by_cases hcb : b = c
      · subst hcb
        rcases k with _ | k
        · simp [respOcc_cons_of_ne δ _ hab', h3]
        · simp [respOcc_cons_of_ne δ _ hab', h1]
      · simp [respOcc_cons_of_ne δ _ hca, respOcc_cons_of_ne δ _ hcb, h1]
  | cons d x ih =>
    simp only [List.cons_append]
    by_cases hd : d = c
    · subst hd
      rcases k with _ | k
      · simp
      · simp [ih]
    · simp [respOcc_cons_of_ne δ _ hd, ih]

variable {δ} {D : α → α → Prop}

lemma SwapEquiv.respOcc_eq_runState_eq (hD : ∀ a b, ¬ D a b → ∀ q, Commute δ a b q)
    {s t : List α} (h : SwapEquiv D s t) :
    (∀ q c i, respOcc δ q s c i = respOcc δ q t c i) ∧ ∀ q, runState δ q s = runState δ q t := by
  induction h with
  | refl => exact ⟨fun _ _ _ => rfl, fun _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨x, y, a, b, hab, rfl, rfl⟩ := hst
    exact ⟨fun q c i => (ih.1 q c i).trans (respOcc_swap δ (hD a b hab) q x y c i),
      fun q => (ih.2 q).trans (runState_swap δ (hD a b hab) q x y)⟩

/-- Lemma 4.1 of [KST26], both parts, for an arbitrary dependence relation `D` such that
independent letters commute in every state. -/
lemma respOcc_eq_runState_eq_of_traceEquiv (hD : ∀ a b, ¬ D a b → ∀ q, Commute δ a b q)
    {s t : List α} (h : TraceEquiv D s t) :
    (∀ q c i, respOcc δ q s c i = respOcc δ q t c i) ∧ ∀ q, runState δ q s = runState δ q t := by
  -- pass to the symmetric dependence relation `D a b ∧ D b a`
  let D' : α → α → Prop := fun a b => D a b ∧ D b a
  have : Std.Symm D' := ⟨fun a b h => ⟨h.2, h.1⟩⟩
  have hD' : ∀ a b, ¬ D' a b → ∀ q, Commute δ a b q := by
    intro a b hab q
    by_cases h : D a b
    · exact (commute_comm δ a b q).2 (hD b a (fun h' => hab ⟨h, h'⟩) q)
    · exact hD a b h q
  exact (swapEquiv_of_traceEquiv (h.mono (D' := D') fun _ _ h => h.1)).respOcc_eq_runState_eq hD'

/-- Lemma 4.1 of [KST26] (general form): equivalent schedules give the same response to every
occurrence, provided letters independent for `D` commute in every state. -/
theorem respOcc_eq_of_traceEquiv (hD : ∀ a b, ¬ D a b → ∀ q, Commute δ a b q) {s t : List α}
    (h : TraceEquiv D s t) (q : Q) (c : α) (i : ℕ) : respOcc δ q s c i = respOcc δ q t c i :=
  (respOcc_eq_runState_eq_of_traceEquiv hD h).1 q c i

/-- Lemma 4.1 of [KST26] (general form), final states: equivalent schedules lead to the same
state. -/
theorem runState_eq_of_traceEquiv (hD : ∀ a b, ¬ D a b → ∀ q, Commute δ a b q) {s t : List α}
    (h : TraceEquiv D s t) (q : Q) : runState δ q s = runState δ q t :=
  (respOcc_eq_runState_eq_of_traceEquiv hD h).2 q

omit [DecidableEq α] in
lemma commute_of_not_conflict {a b : α} (h : ¬ Conflict δ a b) (q : Q) : Commute δ a b q := by
  by_contra hq; exact h ⟨q, hq⟩

/-- Lemma 4.1 of [KST26]: schedules equivalent w.r.t. the conflict relation of `δ` give the same
response to every operation occurrence. -/
theorem respOcc_eq_of_traceEquiv_conflict {s t : List α} (h : TraceEquiv (Conflict δ) s t)
    (q : Q) (c : α) (i : ℕ) : respOcc δ q s c i = respOcc δ q t c i :=
  respOcc_eq_of_traceEquiv (fun _ _ h => commute_of_not_conflict h) h q c i

/-- Lemma 4.1 of [KST26], final states, for the conflict relation of `δ`. -/
theorem runState_eq_of_traceEquiv_conflict {s t : List α} (h : TraceEquiv (Conflict δ) s t)
    (q : Q) : runState δ q s = runState δ q t :=
  runState_eq_of_traceEquiv (fun _ _ h => commute_of_not_conflict h) h q

/-- Lemma 4.2 of [KST26] (general form): if the trace of `s` is a prefix of the trace of `t`
(`t ∼ s · z`), every occurrence of `s` has the same response in `s` and in `t`. -/
theorem respOcc_eq_of_traceEquiv_append (hD : ∀ a b, ¬ D a b → ∀ q, Commute δ a b q)
    {s t z : List α} (h : TraceEquiv D t (s ++ z)) (q : Q) {c : α} {i : ℕ} (hi : i < s.count c) :
    respOcc δ q s c i = respOcc δ q t c i := by
  rw [respOcc_eq_of_traceEquiv hD h, respOcc_append_of_lt δ q hi]

/-- Lemma 4.2 of [KST26], for the conflict relation of `δ`. -/
theorem respOcc_eq_of_le_conflict {s t z : List α} (h : TraceEquiv (Conflict δ) t (s ++ z))
    (q : Q) {c : α} {i : ℕ} (hi : i < s.count c) : respOcc δ q s c i = respOcc δ q t c i :=
  respOcc_eq_of_traceEquiv_append (fun _ _ h => commute_of_not_conflict h) h q hi

end Resp

/-! ### Duplicate-free schedules -/

section Nodup

lemma occ_eq_some_iff_of_nodup {l : List α} (hl : l.Nodup) {a : α} {i p : ℕ} :
    occ l a i = some p ↔ i = 0 ∧ l[p]? = some a := by
  induction l generalizing i p with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    by_cases hx : x = a
    · subst hx
      have hnone : ∀ k, occ l x k = none := fun k =>
        (occ_eq_none_iff l x k).2 (by simp [List.count_eq_zero_of_not_mem hl.1])
      cases i with
      | zero =>
        cases p with
        | zero => simp
        | succ p =>
          simp only [occ_cons_self_zero, Option.some.injEq, List.getElem?_cons_succ, true_and]
          constructor
          · intro h; omega
          · intro h; exact absurd (List.mem_of_getElem? h) hl.1
      | succ i => simp [hnone]
    · rw [occ_cons_of_ne hx]
      cases p with
      | zero => simp [hx]
      | succ p => simp [ih hl.2]

lemma occBefore_iff_of_nodup {l : List α} (hl : l.Nodup) {a b : α} {i j : ℕ} :
    OccBefore l (a, i) (b, j) ↔ i = 0 ∧ j = 0 ∧ Before l a b := by
  simp only [OccBefore, occ_eq_some_iff_of_nodup hl, Before]
  constructor
  · rintro ⟨p, p', ⟨rfl, hp⟩, ⟨rfl, hp'⟩, hlt⟩
    exact ⟨rfl, rfl, p, p', hlt, hp, hp'⟩
  · rintro ⟨rfl, rfl, p, p', hlt, hp, hp'⟩
    exact ⟨p, p', ⟨rfl, hp⟩, ⟨rfl, hp'⟩, hlt⟩

/-- For duplicate-free schedules, trace equivalence is `NEquiv`. -/
theorem traceEquiv_iff_nequiv {D : α → α → Prop} {l l' : List α} (hl : l.Nodup)
    (hl' : l'.Nodup) : TraceEquiv D l l' ↔ NEquiv D l l' := by
  simp only [TraceEquiv, NEquiv, occBefore_iff_of_nodup hl, occBefore_iff_of_nodup hl']
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun a b hab hb => (h a b 0 0 hab ⟨rfl, rfl, hb⟩).2.2⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun a b i j hab ⟨hi, hj, hb⟩ => ⟨hi, hj, h a b hab hb⟩⟩

variable {Q R : Type*} {δ : Q → α → Q × R} {D : α → α → Prop}

/-- Lemma 4.1 of [KST26] for duplicate-free schedules: `ret*(c, l) = ret*(c, l')` whenever
`l ∼ l'`. -/
theorem respFirst_eq_of_nequiv (hD : ∀ a b, ¬ D a b → ∀ q, Commute δ a b q) {l l' : List α}
    (hl : l.Nodup) (hl' : l'.Nodup) (h : NEquiv D l l') (q : Q) (c : α) :
    respFirst δ q l c = respFirst δ q l' c := by
  rw [respFirst_eq_respOcc, respFirst_eq_respOcc,
    respOcc_eq_of_traceEquiv hD ((traceEquiv_iff_nequiv hl hl').2 h)]

/-- Lemma 4.1 of [KST26] for duplicate-free schedules, final states. -/
theorem runState_eq_of_nequiv (hD : ∀ a b, ¬ D a b → ∀ q, Commute δ a b q) {l l' : List α}
    (hl : l.Nodup) (hl' : l'.Nodup) (h : NEquiv D l l') (q : Q) :
    runState δ q l = runState δ q l' :=
  runState_eq_of_traceEquiv hD ((traceEquiv_iff_nequiv hl hl').2 h) q

variable (δ) in
/-- Extending a schedule does not change the response of the first occurrence of a letter that
already occurs in it. -/
theorem respFirst_append_of_mem {l : List α} {c : α} (hc : c ∈ l) (z : List α) (q : Q) :
    respFirst δ q (l ++ z) c = respFirst δ q l c := by
  rw [respFirst_eq_respOcc, respFirst_eq_respOcc,
    respOcc_append_of_lt δ q (List.count_pos_iff.2 hc)]

variable (δ) in
/-- The first occurrence of `c` has a response iff `c` occurs in the schedule. -/
theorem respFirst_isSome_iff (q : Q) (l : List α) (c : α) :
    (respFirst δ q l c).isSome ↔ c ∈ l := by
  rw [respFirst_eq_respOcc, respOcc_isSome_iff, List.count_pos_iff]

end Nodup

end Cslib.Mazurkiewicz
