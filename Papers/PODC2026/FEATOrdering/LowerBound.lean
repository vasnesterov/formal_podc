import Podc.Computability.QueryComplexity.DecisionTree
import Papers.PODC2026.FEATOrdering.Fairness
import Mathlib.Data.Fintype.Perm

/-!
# The `Ω(|T| log |T|)` comparator-query lower bound (Theorem 4.5, Corollary 4.6)

A *comparison-based algorithm* for `n` transactions is a binary decision tree
(`Cslib.DecisionTree`) whose queries are pairs `(i, j)` of positions of the input array (the
transactions in arrival order `π : Fin n ≃ T`); the query `(i, j)` is answered by
`cmp(π i, π j)`, and the leaf outputs the final ordering as a list of positions. This is the
standard comparison model: the algorithm accesses transactions only through the comparator.

* `theorem_4_5_of_linear` — the paper's proof: for the comparator `cmp★` of *any* total order
  on `T`, the expected number of queries under a uniformly random arrival order is
  `≥ log₂ |T|!`.
* `theorem_4_5` — Theorem 4.5: `max_cmp E_π[T_A(cmp, π)] ≥ log₂ |T|! ≥ (|T| log₂ |T|)/2`
  (`|T| ≥ 8`).
* `theorem_4_5_identityAware` — the bound also holds when the algorithm sees the transaction
  identities and the arrival order (any decision tree per arrival order, querying pairs of
  transactions): then we average over the `|T|!` linear comparators instead of fixing one.
* `corollary_4_6` — the same bound for any algorithm that only guarantees comparator-based
  γ-Batch-Order-Fairness (Definition 4.1), not necessarily Adjacent-Comparator Consistency.
-/

namespace Podc.FEATOrdering

open Cslib

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- `N = |T|`. -/
local notation "N" => Fintype.card T

/-- A comparator is a *tournament*: for distinct `a, b` exactly one of `cmp(a,b)`, `cmp(b,a)`
is `True`. -/
def IsTournament (cmp : T → T → Bool) : Prop := ∀ a b, a ≠ b → (cmp a b = true ↔ cmp b a = false)

/-- A *final ordering of `T`*: every transaction exactly once. -/
def IsFinalOrdering (FO : List T) : Prop := FO.Nodup ∧ ∀ t, t ∈ FO

/-- A comparison-based algorithm on `n` inputs: queries are pairs of input positions, the output
is a list of input positions. -/
abbrev CompAlg (n : ℕ) := DecisionTree (Fin n × Fin n) (List (Fin n))

/-- The oracle seen by the algorithm on comparator `cmp` and arrival order `π`. -/
def oracle {n : ℕ} (cmp : T → T → Bool) (π : Fin n ≃ T) : Fin n × Fin n → Bool :=
  fun q => cmp (π q.1) (π q.2)

/-- The final ordering produced by `A` on `(cmp, π)`. -/
def output {n : ℕ} (A : CompAlg n) (cmp : T → T → Bool) (π : Fin n ≃ T) : List T :=
  (A.eval (oracle cmp π)).map π

/-- `T_A(cmp, π)`: the number of comparator queries made by `A` on `(cmp, π)`. -/
def queries {n : ℕ} (A : CompAlg n) (cmp : T → T → Bool) (π : Fin n ≃ T) : ℕ :=
  A.cost (oracle cmp π)

/-- `E_π[T_A(cmp, π)]` for a uniformly random arrival order `π`. -/
noncomputable def expQueries {n : ℕ} (A : CompAlg n) (cmp : T → T → Bool) : ℝ :=
  (∑ π : Fin n ≃ T, (queries A cmp π : ℝ)) / (Fintype.card (Fin n ≃ T) : ℝ)

/-- The transitive tournament `cmp★` induced by the total order `e` (`a < b ↔ e a < e b`). -/
def linCmp {n : ℕ} (e : T ≃ Fin n) (a b : T) : Bool := decide (e a < e b)

omit [Fintype T] [DecidableEq T] in
theorem linCmp_isTournament {n : ℕ} (e : T ≃ Fin n) : IsTournament (linCmp e) := by
  intro a b hab
  have : e a ≠ e b := fun h => hab (e.injective h)
  simp only [linCmp, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
  constructor
  · exact le_of_lt
  · intro h; exact lt_of_le_of_ne h this

omit [Fintype T] [DecidableEq T] in
/-- Under a linear comparator, there is exactly one final ordering with Adjacent-Comparator
Consistency (the sorted order). -/
theorem eq_of_adjConsistent_linCmp {n : ℕ} (e : T ≃ Fin n) {l₁ l₂ : List T}
    (h₁ : IsFinalOrdering l₁) (h₂ : IsFinalOrdering l₂)
    (a₁ : AdjConsistent (linCmp e) l₁) (a₂ : AdjConsistent (linCmp e) l₂) : l₁ = l₂ := by
  have : Trans (fun a b : T => e a < e b) (fun a b : T => e a < e b) (fun a b : T => e a < e b) :=
    ⟨fun h h' => lt_trans h h'⟩
  have p₁ : l₁.Pairwise (fun a b => e a < e b) :=
    (a₁.imp fun a b h => by simpa [linCmp] using h).pairwise
  have p₂ : l₂.Pairwise (fun a b => e a < e b) :=
    (a₂.imp fun a b h => by simpa [linCmp] using h).pairwise
  refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba => absurd (lt_trans hab hba) (lt_irrefl _))
    p₁ p₂ ?_
  exact (List.perm_ext_iff_of_nodup h₁.1 h₂.1).2 fun a => ⟨fun _ => h₂.2 a, fun _ => h₁.2 a⟩

/-- **Theorem 4.5, the paper's proof.** If `A` outputs a final ordering with Adjacent-Comparator
Consistency for every linear comparator, then for each linear comparator `cmp★` the expected
number of queries over a uniformly random arrival order is at least `log₂ |T|!`. -/
theorem theorem_4_5_of_linear (A : CompAlg N)
    (hA : ∀ (e : T ≃ Fin N) (π : Fin N ≃ T),
      IsFinalOrdering (output A (linCmp e) π) ∧ AdjConsistent (linCmp e) (output A (linCmp e) π))
    (e : T ≃ Fin N) :
    Real.logb 2 (Nat.factorial N) ≤ expQueries A (linCmp e) := by
  have hcard : Fintype.card (Fin N ≃ T) = (Nat.factorial N) := by
    rw [Fintype.card_equiv (Fintype.equivFin T).symm, Fintype.card_fin]
  have hinj : Set.InjOn (fun π : Fin N ≃ T => A.eval (oracle (linCmp e) π))
      (Finset.univ : Finset (Fin N ≃ T)) := by
    intro π _ π' _ hππ'
    simp only at hππ'
    obtain ⟨f₁, a₁⟩ := hA e π
    obtain ⟨f₂, a₂⟩ := hA e π'
    have heq := eq_of_adjConsistent_linCmp e f₁ f₂ a₁ a₂
    simp only [output] at heq f₁
    rw [hππ'] at heq f₁
    set L := A.eval (oracle (linCmp e) π')
    have hall : ∀ i : Fin N, i ∈ L := by
      intro i
      obtain ⟨j, hj, hji⟩ := List.mem_map.1 (f₁.2 (π i))
      rw [π.injective hji] at hj; exact hj
    ext i
    exact List.map_inj_left.1 heq i (hall i)
  have h := DecisionTree.logb_card_le_avg_cost A Finset.univ (oracle (linCmp e))
    ⟨(Fintype.equivFin T).symm, Finset.mem_univ _⟩ hinj
  rw [Finset.card_univ, hcard] at h
  simpa [expQueries, queries, hcard] using h

/-- **Theorem 4.5 (expected lower bound in the worst case over comparators).** Every
comparison-based algorithm that outputs, for every tournament comparator and every arrival order,
a final ordering with Adjacent-Comparator Consistency makes, for some tournament comparator, at
least `log₂ |T|!` comparator queries in expectation over a uniformly random arrival order; for
`|T| ≥ 8` this is at least `(|T| log₂ |T|)/2`, i.e. `Ω(|T| log |T|)`. -/
theorem theorem_4_5 (A : CompAlg N)
    (hA : ∀ cmp : T → T → Bool, IsTournament cmp → ∀ π : Fin N ≃ T,
      IsFinalOrdering (output A cmp π) ∧ AdjConsistent cmp (output A cmp π)) :
    ∃ cmp : T → T → Bool, IsTournament cmp ∧ Real.logb 2 (Nat.factorial N) ≤ expQueries A cmp ∧
      (8 ≤ N →
        (N : ℝ) * Real.logb 2 N / 2 ≤ expQueries A cmp) := by
  set e := Fintype.equivFin T
  have h := theorem_4_5_of_linear A (fun e π => hA _ (linCmp_isTournament e) π) e
  exact ⟨linCmp e, linCmp_isTournament e, h, fun h8 =>
    (half_mul_logb_le_logb_factorial h8).trans h⟩

/-! ### Identity-aware algorithms -/

/-- `E_π` of the queries of an identity-aware algorithm: for each arrival order `π` a decision
tree `A π` querying pairs of transactions and outputting a final ordering. -/
noncomputable def expQueries' (A : ((Fin N) ≃ T) → DecisionTree (T × T) (List T))
    (cmp : T → T → Bool) : ℝ :=
  (∑ π, ((A π).cost (fun q => cmp q.1 q.2) : ℝ)) / (Fintype.card (Fin N ≃ T) : ℝ)

/-- **Theorem 4.5, identity-aware version.** The lower bound does not depend on the algorithm
accessing transactions only through positions: even if, for every arrival order `π`, the
algorithm is an arbitrary decision tree over comparator queries on (named) transactions, some
linear comparator forces `≥ log₂ |T|!` expected queries. -/
theorem theorem_4_5_identityAware
    (A : ((Fin N) ≃ T) → DecisionTree (T × T) (List T))
    (hA : ∀ (e : T ≃ Fin N) π,
      IsFinalOrdering ((A π).eval (fun q => linCmp e q.1 q.2)) ∧
      AdjConsistent (linCmp e) ((A π).eval (fun q => linCmp e q.1 q.2))) :
    ∃ cmp : T → T → Bool, IsTournament cmp ∧ Real.logb 2 (Nat.factorial N) ≤ expQueries' A cmp := by
  have hcard : Fintype.card (Fin N ≃ T) = (Nat.factorial N) := by
    rw [Fintype.card_equiv (Fintype.equivFin T).symm, Fintype.card_fin]
  have hcard' : Fintype.card (T ≃ Fin N) = (Nat.factorial N) := by
    rw [Fintype.card_equiv (Fintype.equivFin T)]
  have hpos : (0 : ℝ) < (Nat.factorial N) := by exact_mod_cast (Nat.factorial_pos N)
  -- for each `π`, the output determines the linear order
  have hsum : ∀ π : Fin N ≃ T, ((Nat.factorial N) : ℝ) * Real.logb 2 (Nat.factorial N) ≤
      ∑ e : T ≃ Fin N, ((A π).cost (fun q => linCmp e q.1 q.2) : ℝ) := by
    intro π
    have hinj : Set.InjOn (fun e : T ≃ Fin N => (A π).eval (fun q => linCmp e q.1 q.2))
        (Finset.univ : Finset (T ≃ Fin N)) := by
      intro e _ e' _ hee'
      simp only at hee'
      obtain ⟨f₁, a₁⟩ := hA e π
      obtain ⟨f₂, a₂⟩ := hA e' π
      rw [hee'] at f₁ a₁
      set L := (A π).eval (fun q => linCmp e' q.1 q.2)
      -- `L` is sorted both by `e` and by `e'`; its `i`-th element has `e`-rank `i`.
      have pw : ∀ e₀ : T ≃ Fin N, AdjConsistent (linCmp e₀) L → L = (List.finRange N).map e₀.symm :=
        fun e₀ h => eq_of_adjConsistent_linCmp e₀ f₂ ⟨(List.nodup_finRange N).map e₀.symm.injective,
          fun t => List.mem_map.2 ⟨e₀ t, List.mem_finRange _, by simp⟩⟩ h
          (List.Pairwise.isChain (by
            rw [List.pairwise_map]
            exact (List.pairwise_lt_finRange N).imp fun h => by simpa [linCmp] using h))
      have h1 := pw e a₁
      have h2 := pw e' a₂
      rw [h1] at h2
      have : e.symm = e'.symm := by
        ext i
        have := congrArg (fun l => l[i.val]?) h2
        simpa using this
      exact Equiv.symm_bijective.injective this
    have h := DecisionTree.card_mul_logb_le_sum_cost (A π) Finset.univ
      (fun e : T ≃ Fin N => fun q => linCmp e q.1 q.2) hinj
    rwa [Finset.card_univ, hcard'] at h
  have htot : ∑ _e : T ≃ Fin N, ((Nat.factorial N) : ℝ) * Real.logb 2 (Nat.factorial N) ≤
      ∑ e : T ≃ Fin N, ∑ π : Fin N ≃ T, ((A π).cost (fun q => linCmp e q.1 q.2) : ℝ) := by
    rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, hcard', nsmul_eq_mul]
    calc ((Nat.factorial N) : ℝ) * ((Nat.factorial N) * Real.logb 2 (Nat.factorial N))
        = ∑ _π : Fin N ≃ T, ((Nat.factorial N) : ℝ) * Real.logb 2 (Nat.factorial N) := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun π _ => hsum π
  obtain ⟨e, -, he⟩ := Finset.exists_le_of_sum_le ⟨Fintype.equivFin T, Finset.mem_univ _⟩ htot
  refine ⟨linCmp e, linCmp_isTournament e, ?_⟩
  rw [expQueries', hcard, le_div_iff₀ hpos, mul_comm]
  exact he

/-! ### Corollary 4.6 -/

omit [Fintype T] [DecidableEq T] in
/-- Under a linear comparator every batch is a single transaction, so comparator-based
γ-Batch-Order-Fairness of a final ordering is the same as Adjacent-Comparator Consistency. -/
theorem adjConsistent_of_batchOrderFair_linCmp {n : ℕ} (e : T ≃ Fin n) {G : T → T → Prop}
    {FO : List T} (hnd : FO.Nodup) (h : BatchOrderFair (linCmp e) G FO) :
    AdjConsistent (linCmp e) FO := by
  obtain ⟨B, hflat, hne, hcls, hfwd, -⟩ := h
  -- reachability in a linear order is monotone
  have hreach : ∀ x y, Reach (linCmp e) FO x y → e x ≤ e y := by
    intro x y hxy
    induction hxy with
    | refl => exact le_rfl
    | tail _ hbc ih => exact ih.trans (le_of_lt (by simpa [linCmp] using hbc.2.2))
  -- every block is a singleton
  have hsing : ∀ b ∈ B, ∃ x, b = [x] := by
    intro b hb
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil b (hne b hb)
    have hall : ∀ y ∈ b, y = x := fun y hy => by
      have := (hcls b hb x hx y).1 hy
      exact e.injective (le_antisymm (hreach _ _ this.2) (hreach _ _ this.1))
    have hbnd : b.Nodup := by
      rw [← hflat] at hnd
      exact List.Nodup.sublist (List.sublist_flatten_of_mem hb) hnd
    refine ⟨x, ?_⟩
    rcases b with _ | ⟨a, t⟩
    · exact absurd rfl (hne _ hb)
    · cases t with
      | nil => simp [hall a (by simp)]
      | cons a' t =>
        have h1 := hall a (by simp)
        have h2 := hall a' (by simp)
        exact absurd (by rw [h1.trans h2.symm]; simp) (List.nodup_cons.1 hbnd).1
  have hB : B = FO.map (fun x => [x]) := by
    rw [← hflat]
    clear hflat hfwd hcls hne
    induction B with
    | nil => rfl
    | cons b B ih =>
      obtain ⟨x, rfl⟩ := hsing b (by simp)
      simp only [List.flatten_cons, List.singleton_append, List.map_cons]
      congr 1
      exact ih (fun b hb => hsing b (List.mem_cons_of_mem _ hb))
  rw [hB, List.pairwise_map] at hfwd
  exact (hfwd.imp fun h => h _ (by simp) _ (by simp)).isChain

/-- **Corollary 4.6.** Any comparison-based algorithm that enforces Adjacent-Comparator
Consistency makes `Ω(|T| log |T|)` expected comparator queries in the worst case over
comparators (`theorem_4_5`). In fact the bound already holds for any algorithm that only guarantees
comparator-based γ-Batch-Order-Fairness (Definition 4.1) for every tournament comparator, whether
or not it "relies on" Adjacent-Comparator Consistency. -/
theorem corollary_4_6 (A : CompAlg N)
    (hA : ∀ cmp : T → T → Bool, IsTournament cmp → ∀ π : Fin N ≃ T,
      IsFinalOrdering (output A cmp π) ∧ ∃ G, BatchOrderFair cmp G (output A cmp π)) :
    ∃ cmp : T → T → Bool, IsTournament cmp ∧ Real.logb 2 (Nat.factorial N) ≤ expQueries A cmp ∧
      (8 ≤ N →
        (N : ℝ) * Real.logb 2 N / 2 ≤ expQueries A cmp) := by
  set e := Fintype.equivFin T
  have h := theorem_4_5_of_linear A (fun e π => by
    obtain ⟨hf, G, hG⟩ := hA _ (linCmp_isTournament e) π
    exact ⟨hf, adjConsistent_of_batchOrderFair_linCmp e hf.1 hG⟩) e
  exact ⟨linCmp e, linCmp_isTournament e, h, fun h8 =>
    (half_mul_logb_le_logb_factorial h8).trans h⟩

end Podc.FEATOrdering
