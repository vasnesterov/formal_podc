import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Find

/-!
# Fast Concurrent Data Sketches (PODC 2019): the `r`-relaxation (Definition 2)

Arik Rinberg, Alexander Spiegelman, Edward Bortnikov, Eshcar Hillel, Idit Keidar, Lee Rhodes,
Hadar Serviansky. *Fast Concurrent Data Sketches.* PODC 2019 (brief announcement),
full version arXiv:1902.10995 / ACM TOPC 9(2), 2022.

Sequential histories are lists of entries (an operation instance with its invocation and
response). Definition 2 of the paper:

> A sequential history `H` is an `r`-relaxation of a sequential history `H'` if `H` is comprised
> of all but at most `r` of the invocations in `H'` and their responses, and each invocation in
> `H` is preceded by all but at most `r` of the invocations that precede the same invocation in
> `H'`.

* `AllButAtMost r S T`: all but at most `r` elements of `S` belong to `T`;
* `Prec H y x`: `y` precedes `x` in `H`;
* `IsRelaxation r H H'` (Definition 2);
* `isRelaxation_of_growing`: the abstract argument of Lemmas 4–7 of the full paper. If a
  "linearization" `L k` grows by at most one entry per step, a "visibility order" `V k` only grows,
  `V k ⊆ L k`, `L n` has no duplicates, and at every step all but at most `r` entries of `L k` are
  in `V k`, then `V n` is an `r`-relaxation of `L n`.
* `isRelaxation_future`: Definition 2 does **not** forbid a relaxed history to move operations
  that come *later* in `H'` in front of an entry: for any list `U` of updates, `U ++ [q]` is a
  `1`-relaxation of `q :: U`, so a query may reflect arbitrarily many *later* updates. The
  paper's error analysis assumes that a query only sees (a subset of) the operations preceding
  it; `PastOnly` states this extra property, and `pastOnly_of_growing` is the abstract argument
  establishing it.
-/

namespace Podc.ConcurrentSketches

variable {X : Type}

/-- All but at most `r` of the elements of `S` belong to `T`. -/
def AllButAtMost (r : ℕ) (S T : List X) : Prop :=
  ∃ D : List X, D.length ≤ r ∧ ∀ y ∈ S, y ∈ T ∨ y ∈ D

/-- `y` precedes `x` in the sequential history `H`. -/
def Prec (H : List X) (y x : X) : Prop := [y, x].Sublist H

/-- **Definition 2 of the paper** (`r`-relaxed history): `H` is an `r`-relaxation of `H'`:
`H` consists of all but at most `r` entries of `H'`, and every entry `x` of `H` is preceded in
`H` by all but at most `r` of the entries preceding `x` in `H'`. -/
def IsRelaxation (r : ℕ) (H H' : List X) : Prop :=
  (∀ x ∈ H, x ∈ H') ∧ AllButAtMost r H' H ∧
    ∀ x ∈ H, ∃ D : List X, D.length ≤ r ∧ ∀ y, Prec H' y x → Prec H y x ∨ y ∈ D

/-- The property that the paper's error analysis (Section 6) actually uses for an entry `x`
satisfying `Q` (a query): everything preceding `x` in the relaxed history `H` already preceded
it in `H'` ("a query may miss up to `r` preceding updates, but sees no later ones"). -/
def PastOnly (Q : X → Prop) (H H' : List X) : Prop :=
  ∀ x ∈ H, Q x → ∀ y, Prec H y x → Prec H' y x

lemma AllButAtMost.mono {r : ℕ} {S S' T : List X} (h : AllButAtMost r S T) (hS : ∀ y ∈ S', y ∈ S) :
    AllButAtMost r S' T := by
  obtain ⟨D, hD, h⟩ := h
  exact ⟨D, hD, fun y hy => h y (hS y hy)⟩

/-- **Definition 2 admits arbitrarily many future operations.** For every list `U`, `U ++ [q]`
is a `1`-relaxation of `q :: U`: every entry of `U` loses only the
predecessor `q`. So in a history of `SeqSketch₁` a query `q` may reflect *all* the updates `U`
that follow it, however many there are. -/
theorem isRelaxation_future (q : X) (U : List X) :
    IsRelaxation 1 (U ++ [q]) (q :: U) := by
  refine ⟨?_, ⟨[], by simp, ?_⟩, ?_⟩
  · intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto
  · intro y hy; left; simp only [List.mem_append, List.mem_cons] at hy ⊢
    tauto
  · intro x _
    refine ⟨[q], by simp, fun y hy => ?_⟩
    simp only [Prec] at hy ⊢
    rcases List.sublist_cons_iff.1 hy with h | ⟨r, h1, h2⟩
    · left; exact h.trans (List.sublist_append_left _ _)
    · simp only [List.cons.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      right; simp

/-- **Definition 2 lets a relaxation drop an operation entirely**, in particular a query: `U`
is a `1`-relaxation of `x :: U`. So in a history of `SeqSketch_r` up to `r` queries may return
arbitrary values (they are simply absent from the witnessing history of `SeqSketch`). -/
theorem isRelaxation_drop (x : X) (U : List X) : IsRelaxation 1 U (x :: U) := by
  refine ⟨fun y hy => List.mem_cons_of_mem _ hy, ⟨[x], by simp, fun y hy => ?_⟩, ?_⟩
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inr (by simp)
    · exact Or.inl hy
  · intro z _
    refine ⟨[x], by simp, fun y hy => ?_⟩
    simp only [Prec] at hy ⊢
    rcases List.sublist_cons_iff.1 hy with h | ⟨r, h1, -⟩
    · exact Or.inl h
    · simp only [List.cons.injEq] at h1
      exact Or.inr (by simp [h1.1])

/-- In a list without duplicates, an element preceding `x` lies in the part before `x`. -/
lemma mem_of_sublist_of_nodup {A B : List X} {x y : X} (hnd : (A ++ x :: B).Nodup)
    (h : [y, x].Sublist (A ++ x :: B)) : y ∈ A := by
  induction A with
  | nil =>
    simp only [List.nil_append] at hnd h
    rcases List.sublist_cons_iff.1 h with h | ⟨r, h1, h2⟩
    · exact absurd (h.subset (by simp)) (List.nodup_cons.1 hnd).1
    · simp only [List.cons.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact absurd (h2.subset (by simp)) (List.nodup_cons.1 hnd).1
  | cons a A ih =>
    simp only [List.cons_append] at hnd h
    rcases List.sublist_cons_iff.1 h with h | ⟨r, h1, h2⟩
    · exact List.mem_cons_of_mem _ (ih (List.nodup_cons.1 hnd).2 h)
    · simp only [List.cons.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact List.mem_cons_self

/-- **The relaxation argument (Lemmas 4–7 of the full paper), abstractly.** `L k` (the
linearization after `k` steps) grows by at most one entry per step and starts empty; `V k` (the
visibility order) only grows; `V k ⊆ L k`; `L n` has no duplicates; and after every step all but
at most `r` entries of `L k` are in `V k`. Then `V n` is an `r`-relaxation of `L n`. -/
theorem isRelaxation_of_growing {r n : ℕ} (L V : ℕ → List X) (hL0 : L 0 = [])
    (hLstep : ∀ k < n, ∃ c, L (k + 1) = L k ++ c ∧ c.length ≤ 1)
    (hV : ∀ k ≤ n, V k <+: V n) (hsub : ∀ k ≤ n, ∀ x ∈ V k, x ∈ L k)
    (hnd : (L n).Nodup) (hcnt : ∀ k ≤ n, AllButAtMost r (L k) (V k)) :
    IsRelaxation r (V n) (L n) := by
  have hLpre : ∀ k ≤ n, L k <+: L n := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => exact List.prefix_refl _
    | of_succ k hk ih =>
      obtain ⟨c, hc, -⟩ := hLstep k hk
      exact (hc ▸ List.prefix_append (L k) c).trans ih
  refine ⟨hsub n le_rfl, hcnt n le_rfl, fun x hx => ?_⟩
  have hex : ∃ k, k ≤ n ∧ x ∈ L k := ⟨n, le_rfl, hsub n le_rfl x hx⟩
  classical
  let k := Nat.find hex
  have hk : k ≤ n ∧ x ∈ L k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h; have := hk.2; rw [h, hL0] at this; simp at this
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hxm : x ∉ L m := fun h =>
    (Nat.find_min hex (show m < k by omega)) ⟨by omega, h⟩
  obtain ⟨c, hc, hc1⟩ := hLstep m (by omega)
  have hcx : c = [x] := by
    have : x ∈ c := by
      have := hk.2; rw [hm, hc, List.mem_append] at this
      exact this.resolve_left hxm
    match c, hc1 with
    | [z], _ => simp_all
  obtain ⟨R, hR⟩ := hLpre (m + 1) (by omega)
  rw [hc, hcx] at hR
  obtain ⟨D, hD, hDcov⟩ := hcnt m (by omega)
  refine ⟨D, hD, fun y hy => ?_⟩
  have hnd' : (L m ++ x :: R).Nodup := by rw [← hR] at hnd; simpa using hnd
  have hy' : y ∈ L m := by
    apply mem_of_sublist_of_nodup hnd'
    unfold Prec at hy; rw [← hR] at hy; simpa using hy
  rcases hDcov y hy' with hyV | hyD
  · left
    obtain ⟨W, hW⟩ := hV m (by omega)
    have hxW : x ∈ W := by
      have h1 : x ∈ V m ++ W := hW ▸ hx
      rcases List.mem_append.1 h1 with h | h
      · exact absurd (hsub m (by omega) x h) hxm
      · exact h
    unfold Prec; rw [← hW]
    exact (List.Sublist.append (List.singleton_sublist.2 hyV) (List.singleton_sublist.2 hxW) :
      List.Sublist ([y] ++ [x]) _)
  · exact Or.inr hyD

/-- **Queries see only the past, abstractly.** Suppose that `V` and `L` grow along the steps,
`V k ⊆ L k`, and every entry `x` with `Q x` enters `V` alone and at the same step as it enters
`L`. Then every entry preceding such an `x` in `V n` precedes it in `L n`. -/
theorem pastOnly_of_growing {n : ℕ} (Q : X → Prop) (L V : ℕ → List X) (hV0 : V 0 = [])
    (hL : ∀ k ≤ n, L k <+: L n)
    (hV : ∀ k ≤ n, V k <+: V n) (hsub : ∀ k ≤ n, ∀ x ∈ V k, x ∈ L k)
    (hQ : ∀ k < n, ∀ x, Q x → x ∈ V (k + 1) → x ∉ V k → V (k + 1) = V k ++ [x] ∧ x ∉ L k)
    (hnd : (V n).Nodup) :
    PastOnly Q (V n) (L n) := by
  intro x hx hQx y hy
  have hex : ∃ k, k ≤ n ∧ x ∈ V k := ⟨n, le_rfl, hx⟩
  classical
  let k := Nat.find hex
  have hk : k ≤ n ∧ x ∈ V k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h; have := hk.2; rw [h, hV0] at this; simp at this
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hxm : x ∉ V m := fun h =>
    (Nat.find_min hex (show m < k by omega)) ⟨by omega, h⟩
  obtain ⟨hVx, hLx⟩ := hQ m (by omega) x hQx (hm ▸ hk.2) hxm
  obtain ⟨R, hR⟩ := hV (m + 1) (by omega)
  rw [hVx] at hR
  have hnd' : (V m ++ x :: R).Nodup := by rw [← hR] at hnd; simpa using hnd
  have hyV : y ∈ V m := by
    apply mem_of_sublist_of_nodup hnd'
    unfold Prec at hy; rw [← hR] at hy; simpa using hy
  have hyL : y ∈ L m := hsub m (by omega) y hyV
  have hxL : x ∈ L n := hsub n le_rfl x hx
  obtain ⟨W, hW⟩ := hL m (by omega)
  have hxW : x ∈ W := by
    rw [← hW] at hxL
    rcases List.mem_append.1 hxL with h | h
    · exact absurd h hLx
    · exact h
  unfold Prec; rw [← hW]
  exact (List.Sublist.append (List.singleton_sublist.2 hyL) (List.singleton_sublist.2 hxW) :
    List.Sublist ([y] ++ [x]) _)

end Podc.ConcurrentSketches
