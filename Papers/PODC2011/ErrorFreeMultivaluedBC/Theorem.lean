import Papers.PODC2011.ErrorFreeMultivaluedBC.Generation

/-!
# Theorem 1: L-bit consensus, and at most `t(t+1)` diagnosis stages

Liang–Vaidya, PODC 2011 (arXiv:1101.3520), Theorem 1.

The `L`-bit value is split into `N = L/D` parts of `D` bits; part `g` is the input of generation
`g`. We abstract a `D`-bit part as an element of the data type `α` of the code, so an `L`-bit value
is a vector `Fin N → α` (the input of `i` is `fun g => r.inp g i`).

* `Run.goodClique_graph`: the fault-free processors always trust each other (Lemma 4).
* `Run.theorem_1_consensus`: the decisions of the `N` generations solve consensus on the
  `L`-bit values (termination is built in: every processor decides in every generation).
* `Run.theorem_1_numDiag`: in the repaired algorithm the diagnosis stage is performed in at most
  `t(t+1)` generations, however many generations are run. (For the literal pseudo-code this is
  false, see `Counterexample.lean`.)

The counting argument: the potential of a faulty vertex `f` is `0` once `f` is isolated, and
`t + 1 - min(removed f, t)` before. It never increases, starts at most at `t + 1`, and by Lemma 4
(progress) every diagnosis stage strictly decreases the potential of some faulty vertex.
-/

namespace Podc.ErrorFreeMultivaluedBC

open Finset

namespace Run

variable {n t : ℕ} {α β : Type*} (A : Alg n t α β) (r : Run n α β)

/-- **Lemma 4 (invariance), for all generations.** The fault-free processors always trust each
other. Holds for both variants, and needs only `|F| ≤ t`. -/
theorem goodClique_graph (hF : r.F.card ≤ t) : ∀ g, GoodClique r.F (r.graph A g)
  | 0 => fun _ _ _ _ hij => hij
  | g + 1 => by
    rw [graph_succ]
    have ih := goodClique_graph hF g
    unfold Gen.next
    split_ifs
    · exact (r.gen A g).lemma_4_goodClique hF ih
    · exact ih

/-- **Theorem 1 (correctness).** For `3t < n`, the decisions of the first `N` generations solve
consensus on the `N`-part values (any variant). -/
theorem theorem_1_consensus (hnt : 3 * t < n) (hV : r.Valid A) (N : ℕ) :
    Cslib.Byzantine.Problem.Consensus (fun i (g : Fin N) => r.inp g i) (↑r.F)ᶜ
      (fun i (g : Fin N) => (r.gen A g).out i) := by
  have hc : ∀ g, Cslib.Byzantine.Problem.Consensus (r.gen A g).v (↑r.F)ᶜ (r.gen A g).out :=
    fun g => (r.gen A g).consensus hnt hV.1 (r.goodClique_graph A hV.1 g) (hV.2 g)
  refine ⟨fun i hi j hj => funext fun g => (hc g).agreement i hi j hj, fun w hw i hi => ?_⟩
  funext g
  exact (hc g).unanimity (w g) (fun j hj => congrFun (hw j hj) g) i hi

/-! ### Counting diagnosis stages -/

section Potential

variable {n : ℕ}

open Classical

theorem removed_mono {G G' : SimpleGraph (Fin n)} (h : G' ≤ G) (f : Fin n) :
    removed G f ≤ removed G' f :=
  card_le_card fun k hk => by
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact ⟨hk.1, fun h' => hk.2 (h h')⟩

/-- The potential of a vertex `f`: `0` if `f` is isolated, else `t + 1 - min (removed f) t`. -/
noncomputable def pot (t : ℕ) (G : SimpleGraph (Fin n)) (f : Fin n) : ℕ :=
  if Isolated G f then 0 else t + 1 - min (removed G f) t

theorem pot_le (t : ℕ) (G : SimpleGraph (Fin n)) (f : Fin n) : pot t G f ≤ t + 1 := by
  unfold pot; split_ifs <;> omega

theorem pot_mono {t : ℕ} {G G' : SimpleGraph (Fin n)} (h : G' ≤ G) (f : Fin n) :
    pot t G' f ≤ pot t G f := by
  unfold pot
  have := removed_mono h f
  by_cases h1 : Isolated G f
  · have h1' : Isolated G' f := fun k hk => h1 k (h hk)
    simp [h1']
  · simp only [h1, ↓reduceIte]; split_ifs <;> omega

end Potential

/-- In a diagnosis stage, a faulty vertex losing an edge in steps 3(e)–3(f) loses potential. -/
theorem _root_.Podc.ErrorFreeMultivaluedBC.Gen.pot_G3_lt (σ : Gen n t α β) {f k : Fin n}
    (hk : σ.G.Adj f k) (hk2 : ¬σ.G2.Adj f k) : pot t σ.G3 f < pot t σ.G f := by
  classical
  have hni : ¬Isolated σ.G f := fun h => h k hk
  have hlt : removed σ.G f < removed σ.G2 f := by
    apply card_lt_card
    refine ⟨fun m hm => ?_, fun hsub => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hm ⊢
      exact ⟨hm.1, fun h => hm.2 (σ.G1_le (σ.G2_le h))⟩
    · have : k ∈ ({m | m ≠ f ∧ ¬σ.G2.Adj f m} : Finset (Fin n)) := by
        simp only [mem_filter, mem_univ, true_and]; exact ⟨(σ.G.ne_of_adj hk).symm, hk2⟩
      have := hsub this
      simp only [mem_filter, mem_univ, true_and] at this
      exact this.2 hk
  have h23 := removed_mono σ.G3_le f
  unfold pot
  simp only [hni, ↓reduceIte]
  split_ifs with hiso
  · omega
  · by_cases ht : t + 1 ≤ removed σ.G2 f
    · exact absurd (fun m (h : σ.G3.Adj f m) => h.2.1 ht) hiso
    · omega

/-- The total potential of the faulty vertices. -/
noncomputable def potF (G : SimpleGraph (Fin n)) : ℕ := ∑ f ∈ r.F, pot t G f

open Classical in
theorem potF_succ_add (hnt : 3 * t < n) (hV : r.Valid A) (hvar : A.var = .repaired) (g : ℕ) :
    r.potF (t := t) (r.graph A (g + 1)) + (if (r.gen A g).Diagnosed then 1 else 0) ≤
      r.potF (t := t) (r.graph A g) := by
  classical
  rw [graph_succ]
  show (∑ f ∈ r.F, pot t (r.gen A g).next f) + _ ≤ ∑ f ∈ r.F, pot t (r.gen A g).G f
  unfold Gen.next
  split_ifs with hD
  · obtain ⟨f, hf, k, hk, hk2⟩ :=
      (r.gen A g).lemma_4_progress hnt hV.1 hvar ((hV.2 g).1 hD.1) hD.2
    have := Finset.sum_lt_sum (s := r.F) (fun x _ => pot_mono (r.gen A g).G3_le_G x)
      ⟨f, hf, (r.gen A g).pot_G3_lt hk hk2⟩
    omega
  · simp

/-- **Theorem 1 (number of diagnosis stages).** In the repaired algorithm, for `3t < n`, the
diagnosis stage is performed in at most `t(t+1)` of the first `N` generations, for every `N`. -/
theorem theorem_1_numDiag (hnt : 3 * t < n) (hV : r.Valid A) (hvar : A.var = .repaired)
    (N : ℕ) : r.numDiag A N ≤ t * (t + 1) := by
  classical
  have key : ∀ N, r.numDiag A N + r.potF (t := t) (r.graph A N) ≤
      r.potF (t := t) (r.graph A 0) := by
    intro N
    induction N with
    | zero => simp [numDiag]
    | succ N ih =>
      have h := r.potF_succ_add A hnt hV hvar N
      have : r.numDiag A (N + 1) = r.numDiag A N + (if (r.gen A N).Diagnosed then 1 else 0) := by
        unfold numDiag
        rw [range_add_one, filter_insert]
        split_ifs with hD
        · rw [card_insert_of_notMem (by simp)]
        · rfl
      omega
  have h0 : r.potF (t := t) (r.graph A 0) ≤ t * (t + 1) := by
    calc r.potF (t := t) (r.graph A 0) ≤ ∑ _f ∈ r.F, (t + 1) := sum_le_sum fun f _ => pot_le t _ f
      _ = r.F.card * (t + 1) := by simp
      _ ≤ t * (t + 1) := Nat.mul_le_mul_right _ hV.1
  have := key N
  omega

/-- **Theorem 1** of the paper (repaired algorithm): for `3t < n`, `N` generations achieve
consensus on the `N`-part value, and the diagnosis stage is performed at most `t(t+1)` times. -/
theorem theorem_1 (hnt : 3 * t < n) (hV : r.Valid A) (hvar : A.var = .repaired) (N : ℕ) :
    Cslib.Byzantine.Problem.Consensus (fun i (g : Fin N) => r.inp g i) (↑r.F)ᶜ
        (fun i (g : Fin N) => (r.gen A g).out i) ∧
      r.numDiag A N ≤ t * (t + 1) :=
  ⟨r.theorem_1_consensus A hnt hV N, r.theorem_1_numDiag A hnt hV hvar N⟩

end Run

end Podc.ErrorFreeMultivaluedBC
