import Papers.PODC2018.AsymptoticConsensus.Engine

/-!
# Theorem 3 of FNS'18: rooted models, contraction rate `≥ (1/2)^{1/(n-2)}`

Agents `Fin n`, `n ≥ 4`; the paper's agents `1, …, n` are `0, …, n-1` here.
For `u ∈ {0,1,2}`, `Ψ u` (Figure 2) has the edges `j → 3` for `j ≤ 2`, the path
`3 → 4 → ⋯ → n-1`, and `n-1 → k` for `k ∈ {0,1,2} \ {u}`; agent `u` is deaf in `Ψ u` and is its
root. A move is the block `σ_u = (Ψ u)^{n-2}`.

* Lemma 14 (`psi_agree`): after the blocks `σ_a` and `σ_b` from the same configuration, every
  agent `ℓ ∈ {0,1,2} \ {a, b}` is in the same state.
* **Theorem 3** (`theorem3`): if `N` contains the three `Ψ` graphs, every asymptotic consensus
  algorithm has contraction rate `≥ (1/2)^{1/(n-2)}`. `theorem3_rooted`: the model of all rooted
  graphs.
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Cslib.HeardOf.Chain Filter Topology Set Classical
open scoped ENNReal

variable {σ V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

/-- The graph `Ψ_u` of Figure 2 (0-indexed, `u ∈ Fin 3`). -/
def Psi (n : ℕ) (u : Fin 3) : Graph (Fin n) := fun j k =>
  (j.val ≤ 2 ∧ k.val = 3) ∨ (3 ≤ j.val ∧ k.val = j.val + 1) ∨
    (j.val = n - 1 ∧ k.val ≤ 2 ∧ k.val ≠ u.val)

/-- Agent `u ∈ {0,1,2}` as an agent of `Fin n`. -/
def ag (hn : 4 ≤ n) (u : Fin 3) : Fin n := ⟨u.val, by omega⟩

theorem deaf_psi (hn : 4 ≤ n) (u : Fin 3) : Deaf (Psi n u) (ag hn u) := by
  intro j h
  simp only [Psi, ag] at h
  omega

theorem hears_psi_low {u : Fin 3} {k j : Fin n} (hk : k.val ≤ 2) (h : Hears (Psi n u) k j) :
    j = k ∨ j.val = n - 1 := by
  rcases h with h | h
  · exact Or.inl h
  · simp only [Psi] at h; right; omega

theorem hears_psi_high {u : Fin 3} {k j : Fin n} (hk : 4 ≤ k.val) (h : Hears (Psi n u) k j) :
    j = k ∨ j.val + 1 = k.val := by
  rcases h with h | h
  · exact Or.inl h
  · simp only [Psi] at h; right; omega

theorem sameIn_psi {a b : Fin 3} {k : Fin n} (hk : 3 ≤ k.val ∨ (k.val ≠ a.val ∧ k.val ≠ b.val)) :
    SameIn (Psi n a) (Psi n b) k := by
  intro j
  simp only [Hears, Psi]
  constructor <;> rintro (h | h) <;> first | exact Or.inl h | (right; omega)

/-- **Lemma 14 of FNS'18** (strong form): after `s` rounds of `Ψ_a` resp. `Ψ_b`
(`1 ≤ s ≤ n - 2`) from the same configuration, agents `ℓ ∉ {a, b}` and all agents `m ≥ s + 2`
are in the same state. -/
theorem psi_agree_aux {α' : Type*} (step : StepFn (Fin n) α') (hn : 4 ≤ n) (C : Fin n → α')
    {a b ℓ : Fin 3} (ha : ℓ ≠ a) (hb : ℓ ≠ b) :
    ∀ s, 1 ≤ s → s ≤ n - 2 → ∀ m : Fin n, (m = ag hn ℓ ∨ s + 2 ≤ m.val) →
      conf step C (fun _ => Psi n a) s m = conf step C (fun _ => Psi n b) s m := by
  have hla : ℓ.val ≠ a.val := fun h => ha (Fin.ext h)
  have hlb : ℓ.val ≠ b.val := fun h => hb (Fin.ext h)
  intro s hs1 hs2
  induction s with
  | zero => omega
  | succ s ih =>
    intro m hm
    have hsame : SameIn (Psi n a) (Psi n b) m := sameIn_psi (by
      rcases hm with rfl | hm
      · right; exact ⟨hla, hlb⟩
      · left; omega)
    refine next_eq_of_agree hsame fun j hj => ?_
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rfl
    refine ih hs (by omega) j ?_
    rcases hm with rfl | hm
    · rcases hears_psi_low (by simp [ag]; omega) hj with rfl | hj'
      · exact Or.inl rfl
      · right; omega
    · rcases hears_psi_high (by omega) hj with rfl | hj'
      · right; omega
      · right; omega

theorem psi_agree {α' : Type*} (step : StepFn (Fin n) α') (hn : 4 ≤ n) (C : Fin n → α')
    {a b ℓ : Fin 3} (ha : ℓ ≠ a) (hb : ℓ ≠ b) :
    conf step C (fun _ => Psi n a) (n - 2) (ag hn ℓ) =
      conf step C (fun _ => Psi n b) (n - 2) (ag hn ℓ) :=
  psi_agree_aux step hn C ha hb (n - 2) (by omega) le_rfl _ (Or.inl rfl)

/-- **Theorem 3 of FNS'18.** For `n ≥ 4` agents, the contraction rate of any asymptotic
consensus algorithm in a network model containing `Ψ_1, Ψ_2, Ψ_3` is at least
`(1/2)^{1/(n-2)} = (2^{1/(n-2)})⁻¹`. -/
theorem theorem3 [Nontrivial V] (hn : 4 ≤ n) (A : Alg (Fin n) σ V) {N : Set (Graph (Fin n))}
    (hN : ∀ u, Psi n u ∈ N) (hA : A.Solves N) :
    ((2 : ℝ≥0∞) ^ (((n - 2 : ℕ) : ℝ)⁻¹))⁻¹ ≤ A.rate N := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set blk : Fin 3 → ℕ → Graph (Fin n) := fun u _ => Psi n u
  have hL : 0 < n - 2 := by omega
  have hsub : BlockPat ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) blk (n - 2) ⊆ Pat N :=
    blockPat_subset fun u _ _ => hN u
  have hconst : ∀ u, (fun _ => Psi n u) ∈
      BlockPat ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) blk (n - 2) :=
    fun u => ⟨fun _ => u, fun _ => by simp, rfl⟩
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  have h := Alg.le_rate_of_blocks (D := 1) hA Finset.univ Finset.univ_nonempty blk hL
    (fun u _ _ => hN u) ?_ (fun k => if k = ag hn 0 then v else w) ?_
  · convert h using 3; norm_num
  · intro C hC a _ b _
    obtain ⟨ℓ, hla, hlb⟩ : ∃ ℓ : Fin 3, ℓ ≠ a ∧ ℓ ≠ b := by
      have : ∀ a b : Fin 3, ∃ ℓ : Fin 3, ℓ ≠ a ∧ ℓ ≠ b := by decide
      exact this a b
    refine chainLE_of_inter le_rfl (Finset.mem_univ _) (Finset.mem_univ _) ?_
    exact Alg.val_inter_nonempty_of_deaf hA hsub (hconst ℓ) (deaf_psi hn ℓ)
      (hC.conf (const_mem_pat (hN a)) _) (hC.conf (const_mem_pat (hN b)) _)
      (psi_agree A.step hn C hla hlb)
  · rw [← pos_iff_ne_zero, Metric.ediam_pos_iff']
    refine ⟨v, ?_, w, ?_, hvw⟩
    · simpa using hA.mem_val_of_deaf hsub (hconst 0) (fun _ => deaf_psi hn 0)
        (fun k => if k = ag hn 0 then v else w)
    · have hne : ag hn 1 ≠ ag hn 0 := by simp [ag, Fin.ext_iff]
      simpa [hne] using hA.mem_val_of_deaf hsub (hconst 1) (fun _ => deaf_psi hn 1)
        (fun k => if k = ag hn 0 then v else w)

/-- `Ψ_u` is rooted (at `u`). -/
theorem psi_isRoot (hn : 4 ≤ n) (u : Fin 3) : Cslib.DynNet.IsRoot (Psi n u) (ag hn u) := by
  -- `u` reaches every agent `m ≥ 3` along the path, then every agent of `{0,1,2}`
  have high : ∀ k, ∀ m : Fin n, m.val = k + 3 →
      Relation.ReflTransGen (Psi n u) (ag hn u) m := by
    intro k
    induction k with
    | zero =>
      intro m hm
      refine Relation.ReflTransGen.single ?_
      simp only [Psi, ag]; left; omega
    | succ k ih =>
      intro m hm
      refine (ih ⟨k + 3, by omega⟩ rfl).tail ?_
      simp only [Psi]; right; left; omega
  intro m
  by_cases hm : 3 ≤ m.val
  · exact high (m.val - 3) m (by omega)
  · by_cases hmu : m = ag hn u
    · subst hmu; exact Relation.ReflTransGen.refl
    · refine (high (n - 4) ⟨n - 1, by omega⟩ (by simp; omega)).tail ?_
      simp only [Psi]; right; right
      refine ⟨trivial, by omega, fun h => hmu (Fin.ext ?_)⟩
      simp [ag, h]

/-- **Theorem 3**, rooted corollary: in the network model of all rooted graphs on `n ≥ 4`
agents, every asymptotic consensus algorithm has contraction rate `≥ (1/2)^{1/(n-2)}`. -/
theorem theorem3_rooted [Nontrivial V] (hn : 4 ≤ n) (A : Alg (Fin n) σ V)
    (hA : A.Solves {G | ∃ r, Cslib.DynNet.IsRoot G r}) :
    ((2 : ℝ≥0∞) ^ (((n - 2 : ℕ) : ℝ)⁻¹))⁻¹ ≤ A.rate {G | ∃ r, Cslib.DynNet.IsRoot G r} :=
  theorem3 hn A (fun u => ⟨_, psi_isRoot hn u⟩) hA

end AsymptoticConsensus
