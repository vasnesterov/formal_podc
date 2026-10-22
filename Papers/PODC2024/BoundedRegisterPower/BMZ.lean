import Papers.PODC2024.BoundedRegisterPower.Alg2
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Relation

/-!
# Biran–Moran–Zaks conditions give path systems

Lemma 5.7 of the full version (Biran, Moran, Zaks 1990), for two processes: a task `Δ` is
`1`-resilient (= wait-free) solvable iff some set `O'` of output vectors satisfies

* *connectivity*: for every input `X`, the graph on `Δ(X) ∩ O'` whose edges join vectors differing
  in at most one entry is connected;
* *covering*: for every partial input `X^i` (input `x_j` of `j = !i` only) there is an output `y_j`
  such that for every input `x_i` some vector of `Δ(x_i, x_j) ∩ O'` has `j`-entry `y_j`.

We only use (and do not prove) the "only if" direction, which the paper cites; this file shows
that the conditions yield path systems (`PathSystem`) of every sufficiently large length, as
assumed in Section 5.2.2 of the full version.
-/

namespace Podc.BoundedRegisterPower

variable {In O : Type}

/-- Output vectors differing in at most one entry. -/
def Adj2 (Y Y' : Bool → O) : Prop := ∃ b, Y (!b) = Y' (!b)

/-- The Biran–Moran–Zaks conditions (Lemma 5.7 of the full version) for a two-process task. -/
def BMZ (Δ : (Bool → In) → (Bool → O) → Prop) : Prop :=
  ∃ O' : Set (Bool → O),
    (∀ X Y Y', Y ∈ O' → Δ X Y → Y' ∈ O' → Δ X Y' →
      Relation.ReflTransGen (fun A B => (A ∈ O' ∧ Δ X A) ∧ (B ∈ O' ∧ Δ X B) ∧ Adj2 A B) Y Y') ∧
    ∀ (i : Bool) (xj : In), ∃ yj : O, ∀ xi : In, ∃ Y ∈ O', Δ (vec (!i) xj xi) Y ∧ Y (!i) = yj

/-- A `ReflTransGen` chain as an indexed sequence. -/
lemma exists_seq_of_reflTransGen {α : Type} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ (n : ℕ) (f : ℕ → α), f 0 = a ∧ f n = b ∧ ∀ m < n, r (f m) (f (m + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | @tail b' c _ hbc ih =>
    obtain ⟨n, f, h0, hn, hr⟩ := ih
    refine ⟨n + 1, fun m => if m ≤ n then f m else c, by simp [h0], by simp, fun m hm => ?_⟩
    by_cases hmn : m + 1 ≤ n
    · simp only [hmn, ite_true, show m ≤ n by omega]; exact hr m (by omega)
    · obtain rfl : m = n := by omega
      simp only [le_refl, ite_true, Nat.not_succ_le_self, ite_false]
      rw [hn]; exact hbc

lemma vec_not (X : Bool → In) (i : Bool) : vec (!i) (X (!i)) (X i) = X := by
  funext b; cases b <;> cases i <;> simp [vec]

/-- The Biran–Moran–Zaks conditions give path systems of every length `L > N` for some `N`. -/
theorem exists_pathSystem [Fintype In] [DecidableEq In] {Δ : (Bool → In) → (Bool → O) → Prop}
    (h : BMZ Δ) : ∃ N, ∀ L, N < L → Nonempty (PathSystem Δ L) := by
  obtain ⟨O', hconn, hcov⟩ := h
  choose yj hyj using hcov
  -- the covering output vector for the full input `X` and the missing process `i`
  have hYc : ∀ X i, ∃ Y ∈ O', Δ X Y ∧ Y (!i) = yj i (X (!i)) := by
    intro X i
    obtain ⟨Y, hY, hΔ, hYi⟩ := hyj i (X (!i)) (X i)
    rw [vec_not] at hΔ
    exact ⟨Y, hY, hΔ, hYi⟩
  choose Yc hYcO hYcΔ hYci using hYc
  -- chains from `δ(X) = Yc X true` to `Yc X i`
  have hch : ∀ X i, ∃ (n : ℕ) (f : ℕ → Bool → O), f 0 = Yc X true ∧ f n = Yc X i ∧
      ∀ m < n, ((f m ∈ O' ∧ Δ X (f m)) ∧ (f (m + 1) ∈ O' ∧ Δ X (f (m + 1))) ∧
        Adj2 (f m) (f (m + 1))) := fun X i =>
    exists_seq_of_reflTransGen
      (hconn X _ _ (hYcO X true) (hYcΔ X true) (hYcO X i) (hYcΔ X i))
  choose n f hf0 hfn hfr using hch
  have hleg : ∀ X i m, m ≤ n X i → Δ X (f X i m) := by
    intro X i m hm
    rcases m with _ | m
    · rw [hf0]; exact hYcΔ X true
    · exact ((hfr X i m (by omega)).2.1).2
  set N := (Finset.univ : Finset ((Bool → In) × Bool)).sup (fun Xi => n Xi.1 Xi.2)
  have hN : ∀ X i, n X i ≤ N := fun X i =>
    Finset.le_sup (f := fun Xi : (Bool → In) × Bool => n Xi.1 Xi.2) (Finset.mem_univ (X, i))
  refine ⟨N, fun L hL => ⟨?_⟩⟩
  have hLn : ∀ X i, min (L - 1) (n X i) = n X i := fun X i => min_eq_right (by have := hN X i; omega)
  exact {
    part := fun i xj _ => yj i xj
    path := fun X i m => if m < L then f X i (min m (n X i)) else fun _ => yj i (X (!i))
    path_zero := fun X i j => by simp [show 0 < L by omega, hf0]
    path_L := fun X i => by simp
    legal := fun X i m hm => by simp only [hm, ite_true]; exact hleg X i _ (min_le_right _ _)
    adj := fun X i m hm => by
      by_cases hm1 : m + 1 < L
      · simp only [hm, hm1, ite_true]
        by_cases hmn : m < n X i
        · rw [min_eq_left hmn.le, min_eq_left (by omega : m + 1 ≤ n X i)]
          exact (hfr X i m hmn).2.2
        · rw [min_eq_right (by omega : n X i ≤ m), min_eq_right (by omega : n X i ≤ m + 1)]
          exact ⟨true, rfl⟩
      · obtain rfl : m = L - 1 := by omega
        simp only [hm, hm1, ite_true, ite_false, hLn, hfn]
        exact ⟨i, hYci X i⟩
    last := fun X i => by
      simp only [show L - 1 < L by omega, lt_irrefl, ite_true, ite_false, hLn, hfn]
      exact hYci X i
    cover := fun X i => ⟨Yc X i, hYcΔ X i, hYci X i⟩ }

end Podc.BoundedRegisterPower
