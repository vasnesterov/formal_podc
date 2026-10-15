import Papers.PODC2018.AsymptoticConsensus.Engine

/-!
# Theorems 1 and 2 of FNS'18: contraction rates `1/3` (two agents) and `1/2` (deaf graphs)

* `H0`, `H1`, `H2`: the three rooted graphs on two agents (Figure 1).
* **Theorem 1** (`theorem1`): with `n = 2` agents, any asymptotic consensus algorithm in a network
  model containing `H0, H1, H2` has contraction rate `≥ 1/3`.
* `deafG G i`: `G` with all edges into `i` removed (`F_i`).
* **Theorem 2** (`theorem2`): with `n ≥ 3` agents, any asymptotic consensus algorithm in a network
  model containing `F_i, F_j, F_l` for three distinct agents (in particular `deaf(G)`) has
  contraction rate `≥ 1/2`. `theorem2_nonsplit`: the model of all non-split graphs.
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Cslib.HeardOf.Chain Filter Topology Set Classical
open scoped ENNReal

variable {σ V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Two agents -/

/-- `H₀`: both messages are delivered. -/
def H0 : Graph (Fin 2) := fun j i => j ≠ i
/-- `H₁`: agent `0` (the paper's agent 1) is deaf, agent `1` hears agent `0`. -/
def H1 : Graph (Fin 2) := fun j i => j = 0 ∧ i = 1
/-- `H₂`: agent `1` is deaf, agent `0` hears agent `1`. -/
def H2 : Graph (Fin 2) := fun j i => j = 1 ∧ i = 0

theorem deaf_H1 : Deaf H1 0 := by intro j h; simp [H1] at h
theorem deaf_H2 : Deaf H2 1 := by intro j h; simp [H2] at h
theorem sameIn_H0_H1 : SameIn H0 H1 1 := by
  intro j; fin_cases j <;> simp [Hears, H0, H1]
theorem sameIn_H0_H2 : SameIn H0 H2 0 := by
  intro j; fin_cases j <;> simp [Hears, H0, H2]

/-- The model `{H₀, H₁, H₂}`. -/
noncomputable def N3 : Finset (Graph (Fin 2)) := {H0, H1, H2}

/-- **Theorem 1 of FNS'18.** For `n = 2`, the contraction rate of any asymptotic consensus
algorithm in a network model including `H₀, H₁, H₂` is at least `1/3`. -/
theorem theorem1 [Nontrivial V] (A : Alg (Fin 2) σ V) {N : Set (Graph (Fin 2))}
    (hN : ({H0, H1, H2} : Set (Graph (Fin 2))) ⊆ N) (hA : A.Solves N) :
    (3 : ℝ≥0∞)⁻¹ ≤ A.rate N := by
  have hKN : ∀ G ∈ N3, G ∈ N := fun G hG => hN (by simpa [N3] using hG)
  have hQ : Pat (N3 : Set (Graph (Fin 2))) ⊆ Pat N := pat_mono fun G hG => hKN G hG
  have m0 : H0 ∈ N3 := by simp [N3]
  have m1 : H1 ∈ N3 := by simp [N3]
  have m2 : H2 ∈ N3 := by simp [N3]
  set Y := fun (C : Fin 2 → σ) (G : Graph (Fin 2)) =>
    A.val (Pat (N3 : Set (Graph (Fin 2)))) (next A.step G C)
  have i01 : ∀ C, A.Reach N C → (Y C H0 ∩ Y C H1).Nonempty := fun C hC =>
    Alg.val_inter_nonempty_of_deaf hA hQ (const_mem_pat (by simpa using m2)) deaf_H2
      (hC.next (hKN _ m0)) (hC.next (hKN _ m1)) (next_eq_of_agree sameIn_H0_H1 fun _ _ => rfl)
  have i02 : ∀ C, A.Reach N C → (Y C H0 ∩ Y C H2).Nonempty := fun C hC =>
    Alg.val_inter_nonempty_of_deaf hA hQ (const_mem_pat (by simpa using m1)) deaf_H1
      (hC.next (hKN _ m0)) (hC.next (hKN _ m2)) (next_eq_of_agree sameIn_H0_H2 fun _ _ => rfl)
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  have h := Alg.le_rate_of_chains (D := 2) hA N3 ⟨_, m0⟩ hKN ?_ (fun i => if i = 0 then v else w) ?_
  · convert h using 2; norm_num
  · intro C hC G hG H hH
    have f1 := i01 C hC; have f2 := i02 C hC
    have e1 := i01 C hC; have e2 := i02 C hC
    rw [inter_comm] at e1 e2
    simp only [N3, Finset.mem_insert, Finset.mem_singleton] at hG hH
    rcases hG with rfl | rfl | rfl <;> rcases hH with rfl | rfl | rfl
    all_goals first
      | exact chainLE_refl (by assumption)
      | exact chainLE_of_inter (by norm_num) (by assumption) (by assumption) (by assumption)
      | exact chainLE_two le_rfl m1 m0 m2 e1 (i02 C hC)
      | exact chainLE_two le_rfl m2 m0 m1 e2 (i01 C hC)
  · rw [← pos_iff_ne_zero, Metric.ediam_pos_iff']
    refine ⟨v, ?_, w, ?_, hvw⟩
    · simpa using hA.mem_val_of_deaf hQ (const_mem_pat (by simpa using m1)) (fun _ => deaf_H1)
        (fun i => if i = 0 then v else w)
    · simpa using hA.mem_val_of_deaf hQ (const_mem_pat (by simpa using m2)) (fun _ => deaf_H2)
        (fun i => if i = 0 then v else w)

/-! ### Deaf graphs -/

variable {α : Type*}

/-- `F_i`: the graph `G` in which agent `i` is made deaf. -/
def deafG (G : Graph α) (i : α) : Graph α := fun j k => G j k ∧ k ≠ i

theorem deaf_deafG (G : Graph α) (i : α) : Deaf (deafG G i) i := by
  intro j h; exact absurd rfl h.2

theorem sameIn_deafG (G : Graph α) {a b l : α} (ha : l ≠ a) (hb : l ≠ b) :
    SameIn (deafG G a) (deafG G b) l := by
  intro j; simp [Hears, deafG, ha, hb]

/-- **Theorem 2 of FNS'18** (with the paper's final remark: three deaf graphs suffice). If `N`
contains `F_i` for every agent `i` of a set `S` of at least three agents, the contraction rate of
any asymptotic consensus algorithm in `N` is at least `1/2`. -/
theorem theorem2 [Nontrivial V] [Fintype α] (A : Alg α σ V) (G : Graph α) (S : Finset α)
    (hS : 3 ≤ S.card) {N : Set (Graph α)} (hN : ∀ i ∈ S, deafG G i ∈ N) (hA : A.Solves N) :
    (2 : ℝ≥0∞)⁻¹ ≤ A.rate N := by
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ S, ∃ j ∈ S, i ≠ j := by
    by_contra h; push Not at h
    have := Finset.card_le_one.2 h; omega
  have : Nonempty α := ⟨i⟩
  set K := S.image (deafG G)
  have hKN : ∀ F ∈ K, F ∈ N := by
    intro F hF; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hF; exact hN a ha
  have hQ : Pat (K : Set (Graph α)) ⊆ Pat N := pat_mono fun F hF => hKN F hF
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  have h := Alg.le_rate_of_chains (D := 1) hA K ⟨_, Finset.mem_image_of_mem _ hi⟩ hKN ?_
    (fun k => if k = i then v else w) ?_
  · convert h using 2; norm_num
  · intro C hC F hF F' hF'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hF
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hF'
    have hab2 : ({a, b} : Finset α).card < S.card := by
      have := Finset.card_insert_le a {b}; simp only [Finset.card_singleton] at this; omega
    obtain ⟨l, hl, hlab⟩ := Finset.exists_mem_notMem_of_card_lt_card hab2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hlab
    refine chainLE_of_inter le_rfl hF hF' ?_
    exact Alg.val_inter_nonempty_of_deaf hA hQ
      (const_mem_pat (Finset.mem_coe.2 (Finset.mem_image_of_mem (deafG G) hl))) (deaf_deafG G l)
      (hC.next (hKN _ hF)) (hC.next (hKN _ hF'))
      (next_eq_of_agree (sameIn_deafG G hlab.1 hlab.2) fun _ _ => rfl)
  · rw [← pos_iff_ne_zero, Metric.ediam_pos_iff']
    refine ⟨v, ?_, w, ?_, hvw⟩
    · simpa using hA.mem_val_of_deaf hQ
        (const_mem_pat (Finset.mem_coe.2 (Finset.mem_image_of_mem (deafG G) hi)))
        (fun _ => deaf_deafG G i) (fun k => if k = i then v else w)
    · simpa [hij.symm] using hA.mem_val_of_deaf hQ
        (const_mem_pat (Finset.mem_coe.2 (Finset.mem_image_of_mem (deafG G) hj)))
        (fun _ => deaf_deafG G j) (fun k => if k = i then v else w)

/-- `deaf(G)` version of Theorem 2: `n ≥ 3` agents and all `F_i ∈ N`. -/
theorem theorem2_deaf [Nontrivial V] [Fintype α] (hn : 3 ≤ Fintype.card α) (A : Alg α σ V)
    (G : Graph α) {N : Set (Graph α)} (hN : ∀ i, deafG G i ∈ N) (hA : A.Solves N) :
    (2 : ℝ≥0∞)⁻¹ ≤ A.rate N :=
  theorem2 A G Finset.univ hn (fun i _ => hN i) hA

/-- A graph is non-split if any two agents have a common in-neighbour. -/
def NonSplit (G : Graph α) : Prop := ∀ i j, ∃ k, Hears G i k ∧ Hears G j k

/-- The complete graph. -/
def complete (α : Type*) : Graph α := fun j i => j ≠ i

theorem nonSplit_deafG_complete (a : α) : NonSplit (deafG (complete α) a) := by
  intro i j
  refine ⟨a, ?_, ?_⟩
  · by_cases h : i = a
    · exact Or.inl h.symm
    · exact Or.inr ⟨fun h' => h h'.symm, h⟩
  · by_cases h : j = a
    · exact Or.inl h.symm
    · exact Or.inr ⟨fun h' => h h'.symm, h⟩

/-- **Theorem 2, non-split corollary**: in the network model of all non-split graphs with `n ≥ 3`
agents, every asymptotic consensus algorithm has contraction rate at least `1/2`. -/
theorem theorem2_nonsplit [Nontrivial V] [Fintype α] (hn : 3 ≤ Fintype.card α)
    (A : Alg α σ V) (hA : A.Solves {G | NonSplit G}) : (2 : ℝ≥0∞)⁻¹ ≤ A.rate {G | NonSplit G} :=
  theorem2_deaf hn A (complete α) (fun i => nonSplit_deafG_complete i) hA

end AsymptoticConsensus
