import Papers.PODC2011.ErrorFreeMultivaluedBC.Theorem

/-!
# The literal pseudo-code: an isolated processor forces a diagnosis in every generation

Liang–Vaidya, PODC 2011 (arXiv:1101.3520), Theorem 1 ("the diagnosis stage performed for at most
`t(t+1)` times") and Lemma 4 ("every time the diagnosis stage is performed, at least one edge
attached to a vertex corresponding to a faulty processor will be removed").

In Algorithm 1 as printed, *every* processor `P_j ∉ P_match` broadcasts `Detected_j` (step 2(b)),
and the diagnosis stage is entered as soon as one of them is `true` (step 2(c)). This includes a
faulty processor whose vertex has already been isolated in the diagnosis graph. Such a processor
is never in `P_match` (the fault-free members of `P_match` do not trust it), so it can announce
`Detected = true` in every generation; the diagnosis stage then removes nothing, because the
processor has no edge left (case 2(a) of the proof of Lemma 4 overlooks this).

The run: `n = 4`, `t = 1`, processor `3` faulty, all fault-free inputs equal to `w`, any MDS code.
Processor `3` sends correct symbols, broadcasts `M_3 = false…false` (so it is in no matching set),
`Detected_3 = true`, correct `R#[3]` and `Trust_3 = true…true`. Generation 0 isolates vertex `3`
(step 3(f)); from then on the diagnosis graph is constant and every generation still runs the
diagnosis stage. So the literal algorithm performs the diagnosis stage in all `N` generations,
`N > t(t+1) = 2` as soon as `N ≥ 3` (`literal_numDiag`, `literal_not_theorem_1`). The repaired
algorithm, run against the same adversary, performs it once (`repaired_numDiag`).

The choice of `P_match` is forced: in every generation `{0, 1, 2}` is the only matching set
(`isMatch_iff`), so the counterexample does not depend on the selection rule of step 1(e).
-/

namespace Podc.ErrorFreeMultivaluedBC

namespace Counterexample

open Finset Cslib

variable {α β : Type*} (C : MDSCode 4 2 α β) (d w : α)

/-- The adversary's choices (the same in every generation). -/
def adv : Adv 4 α β where
  sym j _ := C.enc w j
  M _ _ := False
  det _ := True
  rs j := C.enc w j
  trust _ _ := True
  pmatch := {0, 1, 2}
  pdecide := {0, 1}

/-- The algorithm with code `C`, default `d`, and the given variant. -/
def alg (var : Variant) : Alg 4 1 α β := ⟨C, d, var⟩

/-- The run: processor `3` is faulty, all inputs are `w`. -/
def run : Run 4 α β := ⟨{3}, fun _ _ => w, fun _ => adv C w⟩

/-- The complete graph with vertex `3` isolated. -/
def Gstar : SimpleGraph (Fin 4) := isolate ⊤ {3}

theorem notMem_pm {j : Fin 4} : j ∉ ({0, 1, 2} : Finset (Fin 4)) ↔ j = 3 := by
  fin_cases j <;> simp

variable {C d w} {var : Variant}

theorem card_F : (run C w).F.card ≤ 1 := by simp [run]

theorem goodClique (g : ℕ) : GoodClique (run C w).F ((run C w).graph (alg C d var) g) :=
  (run C w).goodClique_graph _ card_F g

/-- Abbreviation for generation `g`. -/
noncomputable abbrev σ (C : MDSCode 4 2 α β) (d w : α) (var : Variant) (g : ℕ) : Gen 4 1 α β :=
  (run C w).gen (alg C d var) g

theorem mem_F {j : Fin 4} : j ∈ (σ C d w var g).F ↔ j = 3 := by simp [Run.gen, run]

/-- In every generation the matching sets are exactly `{0, 1, 2}`. -/
theorem isMatch_iff (g : ℕ) (P : Finset (Fin 4)) :
    (σ C d w var g).IsMatch P ↔ P = {0, 1, 2} := by
  constructor
  · rintro ⟨hc, hP⟩
    have h3 : (3 : Fin 4) ∉ P := by
      intro h3
      obtain ⟨k, hk, hk3⟩ : ∃ k ∈ P, k ≠ 3 := by
        by_contra h
        push Not at h
        have : P ⊆ {3} := fun k hk => by simp [h k hk]
        have := card_le_card this
        simp at hc this; omega
      have := hP 3 h3 k hk (Ne.symm hk3)
      simp [Gen.M, Run.gen, run, adv] at this
    have hsub : P ⊆ {0, 1, 2} := fun k hk => by
      by_contra h
      exact h3 (notMem_pm.mp h ▸ hk)
    exact eq_of_subset_of_card_le hsub (by simp at hc; rw [hc]; rfl)
  · rintro rfl
    refine ⟨rfl, fun j hj k hk hjk => ?_⟩
    have hj3 : j ∉ (σ C d w var g).F := by
      rw [mem_F]; rintro rfl; exact absurd hj (by decide)
    have hk3 : k ∉ (σ C d w var g).F := by
      rw [mem_F]; rintro rfl; exact absurd hk (by decide)
    rw [Gen.M_of_notMem hj3, Gen.R_of_notMem hk3]
    exact ⟨goodClique g j k hj3 hk3 hjk, by simp [Gen.S, Run.gen, run]⟩

theorem pm_eq (g : ℕ) : (σ C d w var g).Pm = {0, 1, 2} := rfl

theorem matchExists (g : ℕ) : (σ C d w var g).MatchExists :=
  ⟨_, (isMatch_iff g (σ C d w var g).Pm).mpr (pm_eq g)⟩

/-- Generation `g` runs the diagnosis stage iff the announcement of processor `3` is counted. -/
theorem diagnosed_iff (g : ℕ) : (σ C d w var g).Diagnosed ↔ (σ C d w var g).Counted 3 := by
  refine ⟨fun ⟨_, j, hj, hc, _⟩ => ?_, fun h => ⟨matchExists g, 3, by rw [pm_eq]; decide, h, ?_⟩⟩
  · rw [pm_eq, notMem_pm] at hj; exact hj ▸ hc
  · simp [Gen.Det, Run.gen, run, adv]

/-- After a diagnosis stage the graph is `Gstar`. -/
theorem G3_eq (g : ℕ) (hD : (σ C d w var g).Diagnosed) : (σ C d w var g).G3 = Gstar := by
  set s := σ C d w var g with hs
  have hc3 : s.Counted 3 := (diagnosed_iff g).mp hD
  have hcons : s.A.C.Consistent s.Pm s.Rs := ⟨w, fun m hm => by
    have hm3 : m ∉ s.F := by
      rw [hs, mem_F]; rintro rfl; rw [hs, pm_eq] at hm; exact absurd hm (by decide)
    rw [Gen.Rs_of_notMem hm3]; simp [s, Gen.S, Run.gen, run]⟩
  have h3iso : (3 : Fin 4) ∈ s.IsoF := by
    refine ⟨by rw [hs, pm_eq]; decide, hc3, by simp [s, Gen.Det, Run.gen, run, adv],
      fun k hk => ?_⟩
    refine ⟨hk, fun _ => by simp [s, Gen.Trust, Run.gen, run, adv], fun h => ?_⟩
    rw [hs, pm_eq] at h; exact absurd h (by decide)
  have hgc :=
    s.lemma_4_goodClique (card_F (C := C) (w := w)) (goodClique (d := d) (var := var) g)
  ext j k
  simp only [Gstar, isolate_adj, SimpleGraph.top_adj, Set.mem_singleton_iff]
  constructor
  · intro h
    have h2 := s.G3_le h
    unfold Gen.G2 at h2
    simp only [hcons, ↓reduceIte, isolate_adj] at h2
    refine ⟨s.G3.ne_of_adj h, ?_, ?_⟩
    · rintro rfl; exact h2.2.1 h3iso
    · rintro rfl; exact h2.2.2 h3iso
  · rintro ⟨hjk, hj, hk⟩
    exact hgc j k (by rw [hs, mem_F]; exact hj) (by rw [hs, mem_F]; exact hk) hjk

/-- From generation `1` on, the diagnosis graph is `Gstar` (vertex `3` isolated). -/
theorem graph_eq (g : ℕ) : (run C w).graph (alg C d var) (g + 1) = Gstar := by
  induction g with
  | zero =>
    rw [Run.graph_succ]
    have hD : (σ C d w var 0).Diagnosed := (diagnosed_iff 0).mpr <| by
      cases var
      · exact Or.inl rfl
      · exact Or.inr ⟨0, by simp [Run.gen, Run.graph]⟩
    simp only [Gen.next, hD, ↓reduceIte]
    exact G3_eq 0 hD
  | succ g ih =>
    rw [Run.graph_succ]
    unfold Gen.next
    split_ifs with hD
    · exact G3_eq _ hD
    · exact ih

/-- The run is admissible (for both variants). -/
theorem valid : (run C w).Valid (alg C d var) := by
  refine ⟨card_F, fun g => ⟨fun _ => (isMatch_iff g _).mpr (pm_eq g), fun hD => ?_⟩⟩
  refine ⟨show ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2} by decide, rfl, fun j hj k hk hjk => ?_⟩
  change j ∈ ({0, 1} : Finset (Fin 4)) at hj
  change k ∈ ({0, 1} : Finset (Fin 4)) at hk
  rw [G3_eq g hD]
  simp only [Gstar, isolate_adj, SimpleGraph.top_adj, Set.mem_singleton_iff]
  refine ⟨hjk, ?_, ?_⟩
  · rintro rfl; exact absurd hj (by decide)
  · rintro rfl; exact absurd hk (by decide)

/-- **The literal algorithm runs the diagnosis stage in every generation.** -/
theorem literal_diagnosed (g : ℕ) : (σ C d w .literal g).Diagnosed :=
  (diagnosed_iff g).mpr (Or.inl rfl)

theorem literal_numDiag (N : ℕ) : (run C w).numDiag (alg C d .literal) N = N := by
  classical
  unfold Run.numDiag
  rw [filter_true_of_mem fun g _ => literal_diagnosed g, card_range]

/-- **Lemma 4 fails for the literal algorithm**: the diagnosis stage of generation `1` removes no
edge at all. -/
theorem literal_lemma_4_false :
    (σ C d w .literal 1).Diagnosed ∧
      (run C w).graph (alg C d .literal) 2 = (run C w).graph (alg C d .literal) 1 :=
  ⟨literal_diagnosed 1, (graph_eq 1).trans (graph_eq 0).symm⟩

/-- **Theorem 1's bound fails for the literal algorithm**: with `n = 4`, `t = 1` and `3`
generations, the diagnosis stage runs `3 > t(t+1) = 2` times, in an admissible run. -/
theorem literal_not_theorem_1 :
    (run C w).Valid (alg C d .literal) ∧ ¬(run C w).numDiag (alg C d .literal) 3 ≤ 1 * (1 + 1) := by
  refine ⟨valid, ?_⟩
  rw [literal_numDiag]; omega

/-- Against the same adversary, the repaired algorithm runs the diagnosis stage only in
generation `0`. -/
theorem repaired_numDiag (N : ℕ) : (run C w).numDiag (alg C d .repaired) (N + 1) = 1 := by
  classical
  have hnd : ∀ g, (σ C d w .repaired (g + 1)).Diagnosed ↔ False := fun g => by
    rw [diagnosed_iff, iff_false]
    rintro (h | ⟨k, hk⟩)
    · cases h
    · have : (run C w).graph (alg C d .repaired) (g + 1) = Gstar := graph_eq g
      change ((run C w).graph (alg C d .repaired) (g + 1)).Adj 3 k at hk
      rw [this] at hk
      exact hk.2.1 rfl
  have hD0 : (σ C d w .repaired 0).Diagnosed :=
    (diagnosed_iff 0).mpr (Or.inr ⟨0, by simp [Run.gen, Run.graph]⟩)
  unfold Run.numDiag
  rw [card_eq_one]
  refine ⟨0, ext fun g => ?_⟩
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    rcases g with _ | g
    · rfl
    · exact ((hnd g).mp h).elim
  · rintro rfl; exact ⟨by omega, hD0⟩

/-! ### Non-vacuity: a Reed–Solomon code with `n = 4`, `k = 2` -/

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The `(4, 2)` Reed–Solomon code over `ZMod 5` with evaluation points `0, 1, 2, 3`. -/
noncomputable def rs42 : MDSCode 4 2 (Polynomial.degreeLT (ZMod 5) 2) (ZMod 5) :=
  MDSCode.reedSolomon 4 2 ⟨fun i => (i.val : ZMod 5), fun i j h => by
    fin_cases i <;> fin_cases j <;> first | rfl | (revert h; decide)⟩

/-- The counterexample with the concrete Reed–Solomon code `rs42`. -/
theorem literal_not_theorem_1_rs :
    (run rs42 0).Valid (alg rs42 0 .literal) ∧
      ¬(run rs42 0).numDiag (alg rs42 0 .literal) 3 ≤ 1 * (1 + 1) :=
  literal_not_theorem_1

/-- Non-vacuity of Theorem 1: the run above is an admissible run of the repaired algorithm with
`3t < n`, a Reed–Solomon code and an actual Byzantine processor, so `Run.theorem_1` applies. -/
theorem theorem_1_nonvacuous :
    (run rs42 0).Valid (alg rs42 0 .repaired) ∧ 3 * 1 < 4 ∧
      (run rs42 0).numDiag (alg rs42 0 .repaired) 5 = 1 :=
  ⟨valid, by norm_num, repaired_numDiag 4⟩

end Counterexample

end Podc.ErrorFreeMultivaluedBC
