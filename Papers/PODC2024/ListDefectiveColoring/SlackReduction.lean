import Papers.PODC2024.ListDefectiveColoring.ColorSpaceReduction

/-!
# Lemma 4.4 and Lemma A.1 of [FK24]: slack reduction

The nodes are coloured class by class according to a *schedule* `t : V → ℕ` (in Lemma 4.4 the
defective colouring `Ψ` of Lemma 3.4, classes processed in increasing order; in Lemma A.1 the
pair (phase, class) of the step in which a node is coloured). When a node `v` is processed, its
neighbours `u` with `t u < t v` are already coloured; `v` then has

* `a_v(x)` (`FK24.SlackReduction.used`): number of already coloured neighbours with colour `x`,
* `deg~(v)` (`FK24.SlackReduction.earlier`): number of already coloured neighbours,
* `L'_v = {x ∈ L_v | a_v(x) ≤ d_v(x)}`, `d'_v(x) = d_v(x) - a_v(x)` (`FK24.SlackReduction.reduce`),

and the nodes processed simultaneously solve the instance `(L', d')` on `sameClass G t` (edges
between nodes with the same `t`) by a list arbdefective colouring algorithm `A`.

Spec-level results (for *any* solutions of the sub-instances):

* `FK24.SlackReduction.weight_le_weight_reduce_add`: `∑_{L_v} (d_v+1) ≤ ∑_{L'_v} (d'_v+1) + deg~(v)`
  (the first line of the displays in the proofs of Lemma 4.4 and Lemma A.1);
* `FK24.SlackReduction.isListArbdefective_of_reduce`: a solution of the sub-instances, together
  with the orientation "towards the earlier class", solves the original instance;
* `FK24.SlackReduction.exists_of_solver`: if `A` solves every instance with slack `μ` on
  `sameClass G t` and every `(L', d')` has slack `μ`, then the sequential procedure produces a
  solution of the original instance;
* `FK24.lemma44`: Lemma 4.4 (`P_A(2, C)` reduces to `P_A(μ, C)` via a `1/μ`-defective colouring);
* `FK24.SlackReduction.paperA1_counterexample`: the slack claim in the proof of Lemma A.1 is false
  (the test `deg~(v) ≤ Δ/2` must be relative to `deg(v)`, not to `Δ`);
* `FK24.lemmaA1`, `FK24.SlackReduction.lemmaA1_halving`,
  `FK24.SlackReduction.two_pow_le_of_halving`:
  the fixed version of Lemma A.1 (test `deg~(v) ≤ deg(v)/2`, relative to the current residual
  degree) and its `O(log Δ)` phase bound.

Round complexities (`T_A(2,C) ≤ O(μ²) T_A(μ,C) + O(log* q)`, eq. (16), and
`T_A(1,C) ≤ O(μ² log Δ) T_A(μ,C) + O(log* q)`, eq. (22)) are not formalized: they count the
`O(μ²)` classes of the defective colouring of Lemma 3.4 (cited, [Kuh09, KS18]) and the
`O(log Δ)` phases.
-/

open Finset

namespace FK24

namespace SlackReduction

variable {V α : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq α]

/-- `a_v(x)`: the number of neighbours of `v` processed before `v` (`t u < t v`) with colour `x`. -/
def used (t : V → ℕ) (col : V → α) (v : V) (x : α) : ℕ :=
  #{u ∈ G.neighborFinset v | t u < t v ∧ col u = x}

/-- `deg~(v)`: the number of neighbours of `v` processed before `v`. -/
def earlier (t : V → ℕ) (v : V) : ℕ := #{u ∈ G.neighborFinset v | t u < t v}

/-- The residual instance `(L', d')`: `L'_v = {x ∈ L_v | a_v(x) ≤ d_v(x)}`,
`d'_v(x) = d_v(x) - a_v(x)`. At `v` it only depends on the colours of neighbours `u` with
`t u < t v`. -/
def reduce (I : ListInstance V α) (t : V → ℕ) (col : V → α) : ListInstance V α where
  L v := {x ∈ I.L v | used G t col v x ≤ I.d v x}
  d v x := I.d v x - used G t col v x

/-- The final orientation: edges to earlier classes point to the earlier class, edges inside a
class are oriented by `O`. -/
def orient (t : V → ℕ) (O : V → V → Prop) : V → V → Prop :=
  fun u w => t w < t u ∨ (t u = t w ∧ O u w)

omit [DecidableEq α] in
theorem earlier_le (t : V → ℕ) (v : V) : earlier G t v ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]; exact card_filter_le _ _

/-- `∑_{x ∈ s} a_v(x) ≤ deg~(v)`. -/
theorem sum_used_le (t : V → ℕ) (col : V → α) (v : V) (s : Finset α) :
    ∑ x ∈ s, used G t col v x ≤ earlier G t v := by
  unfold used earlier
  simp only [card_filter]
  rw [sum_comm]
  refine sum_le_sum fun u _ => ?_
  by_cases hp : t u < t v
  · simp only [hp, true_and]
    rw [sum_ite_eq]
    split_ifs <;> simp
  · simp [hp]

/-- First line of the displays in the proofs of Lemma 4.4 and Lemma A.1 of [FK24]:
`∑_{x ∈ L'_v} (d'_v(x) + 1) ≥ ∑_{x ∈ L_v} (d_v(x) + 1) - deg~(v)`. -/
theorem weight_le_weight_reduce_add (I : ListInstance V α) (t : V → ℕ) (col : V → α) (v : V) :
    I.weight v ≤ (reduce G I t col).weight v + earlier G t v := by
  unfold ListInstance.weight reduce
  simp only
  rw [sum_filter]
  calc ∑ x ∈ I.L v, (I.d v x + 1)
      ≤ ∑ x ∈ I.L v, ((if used G t col v x ≤ I.d v x then I.d v x - used G t col v x + 1 else 0)
          + used G t col v x) := by
        refine sum_le_sum fun x _ => ?_
        split_ifs <;> omega
    _ ≤ _ := by
        rw [sum_add_distrib]
        exact Nat.add_le_add_left (sum_used_le G t col v _) _

/-- Generic slack of the residual instance: if `μ · deg_{G_t}(v) < W_v - deg~(v)` for every `v`,
then `(L', d')` has slack `μ` on `sameClass G t`, whatever the colours of earlier classes. -/
theorem hasSlack_reduce (I : ListInstance V α) (t : V → ℕ) {μ : ℝ}
    (h : ∀ v, μ * ((sameClass G t).degree v : ℝ) < (I.weight v : ℝ) - earlier G t v)
    (col : V → α) : HasSlack (sameClass G t) (reduce G I t col) μ := by
  intro v
  have h1 : (I.weight v : ℝ) ≤ (reduce G I t col).weight v + earlier G t v := by
    exact_mod_cast weight_le_weight_reduce_add G I t col v
  have := h v
  linarith

/-- Correctness of the sequential procedure (Lemmas 4.4 and A.1 of [FK24]): if `(col, O)` solves
the residual instance `(L', d')` (computed from `col` itself on earlier classes) on
`sameClass G t`, then `col` with the orientation `orient t O` (edges to earlier classes point to
the earlier node) is a list arbdefective colouring of the original instance on `G`. -/
theorem isListArbdefective_of_reduce {I : ListInstance V α} {t : V → ℕ} {col : V → α}
    {O : V → V → Prop} (h : IsListArbdefective (sameClass G t) (reduce G I t col) col O) :
    IsListArbdefective G I col (orient t O) := by
  classical
  obtain ⟨hL, hO, hd⟩ := h
  refine ⟨fun v => (mem_filter.1 (hL v)).1, fun u v huv he => ?_, fun v => ?_⟩
  · rcases lt_trichotomy (t u) (t v) with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases hO ⟨huv, h⟩ he with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inl (Or.inl h)
  · have hle : used G t col v (col v) ≤ I.d v (col v) := (mem_filter.1 (hL v)).2
    have hdv : #{u ∈ (sameClass G t).neighborFinset v | O v u ∧ col u = col v} ≤
        I.d v (col v) - used G t col v (col v) := by
      convert hd v using 2
      · ext u; simp
      · rfl
    suffices #{u ∈ G.neighborFinset v | orient t O v u ∧ col u = col v} ≤ I.d v (col v) by
      convert this
    calc _
        ≤ #({u ∈ G.neighborFinset v | t u < t v ∧ col u = col v} ∪
            {u ∈ (sameClass G t).neighborFinset v | O v u ∧ col u = col v}) := by
          refine card_le_card fun u hu => ?_
          rw [mem_filter] at hu
          obtain ⟨hvu, h | ⟨h, h'⟩, he⟩ := hu
          · exact mem_union_left _ (mem_filter.2 ⟨hvu, h, he⟩)
          · refine mem_union_right _ (mem_filter.2 ⟨?_, h', he⟩)
            rw [SimpleGraph.mem_neighborFinset] at hvu ⊢
            exact ⟨hvu, h⟩
      _ ≤ used G t col v (col v) + (I.d v (col v) - used G t col v (col v)) :=
          (card_union_le _ _).trans (Nat.add_le_add le_rfl hdv)
      _ = I.d v (col v) := by omega

open Classical in
/-- `(col, O)` satisfies the conditions of a list arbdefective colouring of the residual instance
computed from `ref` at the node `v`. -/
def Good (I : ListInstance V α) (t : V → ℕ) (ref col : V → α) (O : V → V → Prop) (v : V) : Prop :=
  col v ∈ (reduce G I t ref).L v ∧
    (∀ u, (sameClass G t).Adj v u → col u = col v → O v u ∨ O u v) ∧
    #{u ∈ (sameClass G t).neighborFinset v | O v u ∧ col u = col v} ≤
      (reduce G I t ref).d v (col v)

theorem good_of_isListArbdefective {I : ListInstance V α} {t : V → ℕ} {ref col : V → α}
    {O : V → V → Prop} (h : IsListArbdefective (sameClass G t) (reduce G I t ref) col O) (v : V) :
    Good G I t ref col O v := by
  classical
  refine ⟨h.1 v, fun u hvu he => (h.2.1 hvu.symm he).symm, ?_⟩
  convert h.2.2 v using 3

theorem isListArbdefective_of_good {I : ListInstance V α} {t : V → ℕ} {col : V → α}
    {O : V → V → Prop} (h : ∀ v, Good G I t col col O v) :
    IsListArbdefective (sameClass G t) (reduce G I t col) col O := by
  classical
  refine ⟨fun v => (h v).1, fun u v huv he => (h u).2.1 v huv he.symm, fun v => ?_⟩
  convert (h v).2.2 using 3

theorem used_congr {t : V → ℕ} {ref ref' : V → α} {v : V}
    (hR : ∀ u, t u < t v → ref' u = ref u) (x : α) :
    used G t ref' v x = used G t ref v x := by
  unfold used
  congr 1
  refine filter_congr fun u _ => ?_
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, (hR u h).symm⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, hR u h⟩

/-- `Good` at `v` only depends on the reference colouring of earlier classes and on the colouring
and orientation inside the class of `v`. -/
theorem Good.congr {I : ListInstance V α} {t : V → ℕ} {ref ref' col col' : V → α}
    {O O' : V → V → Prop} {v : V}
    (hR : ∀ u, t u < t v → ref' u = ref u) (hc : ∀ u, t u = t v → col' u = col u)
    (hO : ∀ u w, t u = t v → t w = t v → (O' u w ↔ O u w))
    (h : Good G I t ref col O v) : Good G I t ref' col' O' v := by
  classical
  have hu := used_congr G hR
  have hL : (reduce G I t ref').L v = (reduce G I t ref).L v := by simp [reduce, hu]
  have hd : (reduce G I t ref').d v = (reduce G I t ref).d v := by
    funext x; simp [reduce, hu]
  obtain ⟨h1, h2, h3⟩ := h
  have hcv := hc v rfl
  refine ⟨by rw [hL, hcv]; exact h1, fun u hvu he => ?_, ?_⟩
  · have htu : t u = t v := hvu.2.symm
    rw [hO v u rfl htu, hO u v htu rfl]
    exact h2 u hvu (by rw [← hc u htu, ← hcv, he])
  · rw [hd, hcv]
    refine le_trans (le_of_eq ?_) h3
    congr 1
    refine filter_congr fun u hu => ?_
    have htu : t u = t v := ((SimpleGraph.mem_neighborFinset _ _ _).1 hu).2.symm
    simp only [hO v u rfl htu, hc u htu]

/-- The sequential procedure of Lemmas 4.4 and A.1 of [FK24] (classes processed in increasing `t`,
each class solved by an algorithm `A` for list arbdefective colouring with slack `μ`): if `A` solves
every instance with slack `μ` on `sameClass G t`, and every residual instance has slack `μ`, then
the original instance has a list arbdefective colouring on `G`. -/
theorem exists_of_solver [Nonempty α] (I : ListInstance V α) (t : V → ℕ) {μ : ℝ}
    (hslack : ∀ col, HasSlack (sameClass G t) (reduce G I t col) μ)
    (hA : ∀ J : ListInstance V α, HasSlack (sameClass G t) J μ →
      ∃ (c : V → α) (O : V → V → Prop), IsListArbdefective (sameClass G t) J c O) :
    ∃ (col : V → α) (O : V → V → Prop), IsListArbdefective G I col O := by
  classical
  -- `P k`: some partial solution is correct on all classes `< k`.
  have key : ∀ k, ∃ (col : V → α) (O : V → V → Prop), ∀ v, t v < k → Good G I t col col O v := by
    intro k
    induction k with
    | zero =>
      exact ⟨fun _ => Classical.arbitrary α, fun _ _ => True, fun v hv => absurd hv (by omega)⟩
    | succ k ih =>
      obtain ⟨col, O, hgood⟩ := ih
      obtain ⟨c, o, hco⟩ := hA _ (hslack col)
      refine ⟨fun v => if t v < k then col v else c v,
        fun u w => if t u < k then O u w else o u w, fun v hv => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
      · refine (hgood v hv).congr G (fun u hu => ?_) (fun u hu => ?_) (fun u w hu _ => ?_)
        · simp [show t u < k by omega]
        · simp [show t u < k by omega]
        · simp [show t u < k by omega]
      · refine (good_of_isListArbdefective G hco v).congr G (fun u hu => ?_) (fun u hu => ?_)
          (fun u w hu _ => ?_)
        · simp [show t u < k by omega]
        · simp [show ¬ t u < k by omega]
        · simp [show ¬ t u < k by omega]
  obtain ⟨col, O, h⟩ := key (univ.sup t + 1)
  exact ⟨col, orient t O, isListArbdefective_of_reduce G
    (isListArbdefective_of_good G fun v => h v (Nat.lt_succ_of_le (le_sup (mem_univ v))))⟩

/-- `exists_of_solver` without `[Nonempty α]`, for an instance with nonnegative slack. -/
theorem exists_of_solver_of_hasSlack (I : ListInstance V α) {S : ℝ} (hS : 0 ≤ S)
    (hI : HasSlack G I S) (t : V → ℕ) {μ : ℝ}
    (hslack : ∀ col, HasSlack (sameClass G t) (reduce G I t col) μ)
    (hA : ∀ J : ListInstance V α, HasSlack (sameClass G t) J μ →
      ∃ (c : V → α) (O : V → V → Prop), IsListArbdefective (sameClass G t) J c O) :
    ∃ (col : V → α) (O : V → V → Prop), IsListArbdefective G I col O := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩
  · exact ⟨fun v => isEmptyElim v, fun _ _ => True,
      ⟨fun v => isEmptyElim v, fun u => isEmptyElim u, fun v => isEmptyElim v⟩⟩
  · have hw := ColorSpace.weight_pos_of_hasSlack G hS hI v
    have : (I.L v).Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty] at hc
      simp [ListInstance.weight, hc] at hw
    have : Nonempty α := ⟨this.choose⟩
    exact exists_of_solver G I t hslack hA

end SlackReduction

open SlackReduction

/-- Lemma 4.4 of [FK24] (slack reduction), spec level. Let `I` have slack `2` on `G`, `μ ≥ 1`, and
let `Ψ` be a defective colouring with `#{u ∈ N(v) | Ψ u = Ψ v} ≤ deg(v)/μ` (Lemma 3.4 with
`ε = 1/μ`, cited; `O(μ²)` classes). Process the classes in increasing order of `Ψ`. Then

1. for every colouring of the earlier classes, the residual instance `(L', d')` has slack `μ` on
   `G_Ψ = sameClass G Ψ`;
2. any list arbdefective colouring of the residual instances, oriented towards earlier classes,
   solves `I` on `G`;
3. hence an algorithm `A` for slack-`μ` instances yields a solution of `I`.

Round complexity `T_A(2, C) ≤ O(μ²) · T_A(μ, C) + O(log* q)` (eq. (16)), not formalized. -/
theorem lemma44 {V α : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq α] (I : ListInstance V α) (hI : HasSlack G I 2) {μ : ℝ} (hμ : 1 ≤ μ)
    (Ψ : V → ℕ) (hΨ : ∀ v, (#{u ∈ G.neighborFinset v | Ψ u = Ψ v} : ℝ) ≤ G.degree v / μ) :
    (∀ col, HasSlack (sameClass G Ψ) (reduce G I Ψ col) μ) ∧
      (∀ col O, IsListArbdefective (sameClass G Ψ) (reduce G I Ψ col) col O →
        IsListArbdefective G I col (orient Ψ O)) ∧
      ((∀ J : ListInstance V α, HasSlack (sameClass G Ψ) J μ →
          ∃ (c : V → α) (O : V → V → Prop), IsListArbdefective (sameClass G Ψ) J c O) →
        ∃ (col : V → α) (O : V → V → Prop), IsListArbdefective G I col O) := by
  have hslack : ∀ col, HasSlack (sameClass G Ψ) (reduce G I Ψ col) μ := by
    refine hasSlack_reduce G I Ψ (fun v => ?_)
    have h1 := hI v
    have h2 : (earlier G Ψ v : ℝ) ≤ G.degree v := by exact_mod_cast earlier_le G Ψ v
    have h3 : μ * ((sameClass G Ψ).degree v : ℝ) ≤ G.degree v := by
      rw [degree_sameClass]
      have := hΨ v
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    linarith
  exact ⟨hslack, fun _ _ h => isListArbdefective_of_reduce G h,
    fun hA => exists_of_solver_of_hasSlack G I (by norm_num) hI Ψ hslack hA⟩

namespace SlackReduction

variable {V α : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq α]

/-! ### Lemma A.1: the paper's version fails -/

namespace A1Counterexample

/-- Edges: `v = 0` with neighbours `1, 2, 3` (earlier class) and `4` (same class); `4` has three
further neighbours `5, 6, 7`; a star with centre `8` and leaves `9, …, 14` makes `Δ = 6`. -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (4, 5), (4, 6), (4, 7),
    (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14)]

/-- The graph of the counterexample. -/
def graph : SimpleGraph (Fin 15) where
  Adj u w := (u.val, w.val) ∈ edges ∨ (w.val, u.val) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The defective colouring (two classes, processed in the order `0, 1`). -/
def cls : Fin 15 → ℕ := fun u => if u.val ∈ [0, 4, 9, 10, 11, 12, 13, 14] then 1 else 0

/-- The colours: the earlier-class neighbours `1, 2, 3` of `v = 0` have colours `1, 2, 3`. -/
def colour : Fin 15 → ℕ := fun u => u.val

/-- All defects are `0`; `v = 0` has the list `{1, …, 5}`, all other nodes `{0, …, 15}`. -/
def inst : ListInstance (Fin 15) ℕ := ⟨fun u => if u = 0 then {1, 2, 3, 4, 5} else range 16,
  fun _ _ => 0⟩

end A1Counterexample

open A1Counterexample in
/-- The proof of Lemma A.1 of [FK24] has an error (the existence of a colouring is unaffected): it
puts into `H_i` the nodes with at most `Δ/2`
coloured neighbours and claims `∑_{L'_v} (d'_v(x)+1) > deg(v) - deg~(v) ≥ Δ - Δ/2 ≥ μ deg_{G_i}(v)`,
but `deg(v) ≥ Δ` need not hold. Here `μ = 2`, `ε = 1/(2μ) = 1/4`, `Δ = 6`:

* `inst` has slack `1` on `graph`; `cls` is a defective colouring with at most `ε · deg(u)`
  neighbours of the same class for every `u`; the earlier class is properly coloured by `colour`;
* node `v = 0` has `deg~(v) = 3 ≤ Δ/2` coloured neighbours, so it belongs to `H_1`;
* but its residual instance has `∑_{L'_v} (d'_v(x)+1) = 2 = μ · deg_{G_1}(v)`, i.e. it does **not**
  have slack `μ`, so algorithm `A` (for slack `μ`) cannot be applied.

(The residual instance still has slack `1`, so this breaks the round complexity claim, not the
existence of a colouring.) -/
theorem paperA1_counterexample :
    HasSlack graph inst 1 ∧
      (∀ u, (#{w ∈ graph.neighborFinset u | cls w = cls u} : ℝ) ≤ 1 / (2 * 2) * graph.degree u) ∧
      (∀ u, cls u = 0 → colour u ∈ inst.L u ∧
        ∀ w, graph.Adj u w → cls w = 0 → colour w ≠ colour u) ∧
      graph.maxDegree = 6 ∧ 2 * earlier graph cls 0 ≤ graph.maxDegree ∧
      ¬ ((2 : ℝ) * (sameClass graph cls).degree 0 < (reduce graph inst cls colour).weight 0) := by
  have hdeg : ∀ u, graph.degree u ≤ 6 := by decide
  have hmax : graph.maxDegree = 6 :=
    le_antisymm (SimpleGraph.maxDegree_le_of_forall_degree_le _ _ hdeg)
      ((show graph.degree 8 = 6 by decide).symm.le.trans (graph.degree_le_maxDegree 8))
  refine ⟨fun u => ?_, fun u => ?_, by decide, hmax, ?_, ?_⟩
  · have : graph.degree u < inst.weight u := by revert u; decide
    rw [one_mul]; exact_mod_cast this
  · have : #{w ∈ graph.neighborFinset u | cls w = cls u} * 4 ≤ graph.degree u := by
      revert u; decide
    rw [show (1 : ℝ) / (2 * 2) * graph.degree u = graph.degree u / 4 by ring,
      le_div_iff₀ (by norm_num)]
    exact_mod_cast this
  · rw [hmax]; decide
  · have h1 : (sameClass graph cls).degree 0 = 1 := by rw [degree_sameClass]; decide
    have h2 : (reduce graph inst cls colour).weight 0 = 2 := by decide
    rw [h1, h2]; norm_num

/-! ### Lemma A.1, fixed -/

omit [DecidableEq α] in
/-- Lemma A.1 of [FK24], fixed slack computation at one node. The current phase starts at rank
`s ≤ t v`; the neighbours `u` with `s ≤ t u` are those uncoloured at the start of the phase
(`r(v)` of them, the degree of `v` in the residual graph), those with `s ≤ t u < t v` are coloured
in this phase before `v`. The **fixed** membership test of `H_i` is "at most `r(v)/2` of them are
coloured" (the paper uses `Δ/2`), and the defective colouring of the phase (Lemma 3.4 with
`ε = 1/(2μ)` on the residual graph) gives `2μ · deg_{G_i}(v) ≤ r(v)`. Then
`∑_{L'_v} (d'_v(x)+1) ≥ W_v - deg~(v) > r(v) - c(v) ≥ r(v)/2 ≥ μ · deg_{G_i}(v)`. -/
theorem lemmaA1_slack_node (I : ListInstance V α) (hI : HasSlack G I 1) {μ : ℝ} (t : V → ℕ)
    (v : V) {s : ℕ} (hs : s ≤ t v)
    (hH : 2 * #{u ∈ G.neighborFinset v | s ≤ t u ∧ t u < t v} ≤
      #{u ∈ G.neighborFinset v | s ≤ t u})
    (hdef : 2 * μ * ((sameClass G t).degree v : ℝ) ≤ #{u ∈ G.neighborFinset v | s ≤ t u}) :
    μ * ((sameClass G t).degree v : ℝ) < (I.weight v : ℝ) - earlier G t v := by
  have e1 := card_filter_add_card_filter_not (s := G.neighborFinset v) (fun u => t u < t v)
  have e2 := card_filter_add_card_filter_not (s := {u ∈ G.neighborFinset v | s ≤ t u})
    (fun u => t u < t v)
  rw [filter_filter, filter_filter] at e2
  have e3 : {u ∈ G.neighborFinset v | s ≤ t u ∧ ¬ t u < t v} =
      {u ∈ G.neighborFinset v | ¬ t u < t v} :=
    filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  rw [e3] at e2
  rw [SimpleGraph.card_neighborFinset_eq_degree] at e1
  have h1 := hI v
  unfold earlier
  set c := #{u ∈ G.neighborFinset v | s ≤ t u ∧ t u < t v}
  set r := #{u ∈ G.neighborFinset v | s ≤ t u}
  set e := #{u ∈ G.neighborFinset v | t u < t v}
  set n := #{u ∈ G.neighborFinset v | ¬ t u < t v}
  have e1' : (e : ℝ) + n = G.degree v := by exact_mod_cast e1
  have e2' : (c : ℝ) + n = r := by exact_mod_cast e2
  have hH' : 2 * (c : ℝ) ≤ r := by exact_mod_cast hH
  linarith

omit [DecidableEq α] in
/-- Lemma A.1 of [FK24], fixed, degree halving: if at the step of `v` (rank `τ`) in the phase
starting at rank `s`, more than half of the `r(v)` neighbours uncoloured at the start of the phase
are already coloured (the fixed test fails, `v` stays uncoloured), then fewer than `r(v)/2`
neighbours are still uncoloured at the start `s' ≥ τ` of the next phase. -/
theorem lemmaA1_halving (t : V → ℕ) (v : V) {s τ s' : ℕ} (hss' : s ≤ s') (hτ : τ ≤ s')
    (hfail : #{u ∈ G.neighborFinset v | s ≤ t u} <
      2 * #{u ∈ G.neighborFinset v | s ≤ t u ∧ t u < τ}) :
    2 * #{u ∈ G.neighborFinset v | s' ≤ t u} < #{u ∈ G.neighborFinset v | s ≤ t u} := by
  have e2 := card_filter_add_card_filter_not (s := {u ∈ G.neighborFinset v | s ≤ t u})
    (fun u => t u < τ)
  rw [filter_filter, filter_filter] at e2
  have hle : #{u ∈ G.neighborFinset v | s' ≤ t u} ≤
      #{u ∈ G.neighborFinset v | s ≤ t u ∧ ¬ t u < τ} :=
    card_le_card (monotone_filter_right _ fun u _ h => ⟨by omega, by omega⟩)
  omega

/-- The phase bound of Lemma A.1: if the residual degree `r k` of a node at least halves strictly
in each of the phases `0, …, n-1` that it survives uncoloured, then `2^n ≤ r 0 + 1`; with
`r 0 ≤ Δ` a node is coloured within `log₂(Δ + 1) + 1` phases (a node with `r = 0` passes the fixed
test). -/
theorem two_pow_le_of_halving (n : ℕ) : ∀ r : ℕ → ℕ, (∀ k < n, 2 * r (k + 1) < r k) →
    2 ^ n ≤ r 0 + 1 := by
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r h
    have h1 := ih (fun k => r (k + 1)) (fun k hk => h (k + 1) (by omega))
    have h2 := h 0 (by omega)
    rw [pow_succ]
    omega

end SlackReduction

open SlackReduction in
/-- Lemma A.1 of [FK24] (modified slack reduction for slack `1`), **fixed** and spec level.
Let `I` have slack `1` on `G` and let `t` be the schedule produced by the phases: `t v` encodes
(phase, class) of the step in which `v` is coloured, and `ps v ≤ t v` is the first rank of that
phase. Assume the fixed test `2 · #{coloured in this phase before v} ≤ r(v)` (where `r(v)` is the
number of neighbours uncoloured at the start of the phase) and the defective colouring bound
`2μ · deg_{G_t}(v) ≤ r(v)` (Lemma 3.4 with `ε = 1/(2μ)` on the residual graph, cited). Then the
residual instances have slack `μ`, solutions combine to a solution of `I`, and an algorithm for
slack-`μ` instances yields a solution of `I`. With `lemmaA1_halving` and `two_pow_le_of_halving`,
`O(log Δ)` phases suffice; round complexity `O(μ² log Δ) · T_A(μ, C) + O(log* q)` (eq. (22)) is not
formalized. (Unformalized remark: as written, the argument recomputes the defective colouring in
each phase, which would give `O(log Δ · log* q)` rather than `+ O(log* q)`.) -/
theorem lemmaA1 {V α : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq α] (I : ListInstance V α) (hI : HasSlack G I 1) {μ : ℝ} (t ps : V → ℕ)
    (hps : ∀ v, ps v ≤ t v)
    (hH : ∀ v, 2 * #{u ∈ G.neighborFinset v | ps v ≤ t u ∧ t u < t v} ≤
      #{u ∈ G.neighborFinset v | ps v ≤ t u})
    (hdef : ∀ v, 2 * μ * ((sameClass G t).degree v : ℝ) ≤ #{u ∈ G.neighborFinset v | ps v ≤ t u}) :
    (∀ col, HasSlack (sameClass G t) (reduce G I t col) μ) ∧
      (∀ col O, IsListArbdefective (sameClass G t) (reduce G I t col) col O →
        IsListArbdefective G I col (orient t O)) ∧
      ((∀ J : ListInstance V α, HasSlack (sameClass G t) J μ →
          ∃ (c : V → α) (O : V → V → Prop), IsListArbdefective (sameClass G t) J c O) →
        ∃ (col : V → α) (O : V → V → Prop), IsListArbdefective G I col O) := by
  have hslack : ∀ col, HasSlack (sameClass G t) (reduce G I t col) μ :=
    hasSlack_reduce G I t fun v => lemmaA1_slack_node G I hI t v (hps v) (hH v) (hdef v)
  exact ⟨hslack, fun _ _ h => isListArbdefective_of_reduce G h,
    fun hA => exists_of_solver_of_hasSlack G I (by norm_num) hI t hslack hA⟩

end FK24
