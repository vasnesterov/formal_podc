import Papers.PODC2015.CrashConsensusDigraph.Iterative

/-!
# The graph of Appendix B is not a counterexample for fixed-iteration outputs

If an iterative algorithm *outputs its value after a fixed number `T` of iterations* (as
Algorithm Min-Max does), the step "if `Rᵢ[t]` contains all 0's or all 1's, then `Z(Rᵢ[t])`
should map to 0 or 1" of the proof of Theorem 5 is false, and so is its conclusion for the graph
used there: for `f = 1`, the fixed transition function

  `Z(R) = ¬ max R`   (`notMax`)

with output after iteration `T = 4` solves binary crash consensus on the graph of Appendix B
(source, clique of 2 nodes, leaf), against every crash pattern with at most one crash (including
crashes in the middle of a round with partial delivery). Intuitively, the values alternate
between "true" and "negated", so `¬max` simulates alternating Max and Min rounds.

Proof: the values after 4 iterations only depend on the deliveries in iterations `0, …, 3`; there
are finitely many delivery patterns with at most one crash, and all of them (with all inputs)
are checked by evaluation (`check_ok`, by `decide`).

(Bounded exhaustive search, outside Lean, also confirms `notMax`, `T = 4` for `f = 2`; for `f = 3`
it fails at `T = 4`.)
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open Cslib.ApproxConsensus PNode

/-- `Z(R) = ¬ max R`. -/
def notMax (m : Multiset Bool) : Bool := !decide (true ∈ m)

variable {V : Type*} [DecidableEq V] [Fintype V]

open Classical in
theorem notMax_iter (G : Digraph V) (adv : Adversary V) (inp : V → Bool) (t : ℕ) (w : V) :
    iterState G notMax adv inp (t + 1) w = !(iterState G notMax adv inp t w ||
      decide (∃ u, u ≠ w ∧ Delivers G adv t u w ∧ iterState G notMax adv inp t u = true)) := by
  classical
  show notMax (_ ::ₘ _) = _
  unfold notMax
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, decide_eq_true_iff,
    Multiset.mem_cons, Multiset.mem_map]
  constructor
  · rintro (h | ⟨u, hu, hg⟩)
    · exact Or.inl h.symm
    · simp only [recvSet, Finset.mem_val, mem_filter, mem_univ, true_and] at hu
      exact Or.inr ⟨u, hu.1, hu.2, hg⟩
  · rintro (h | ⟨u, h1, h2, hg⟩)
    · exact Or.inl h.symm
    · refine Or.inr ⟨u, ?_, hg⟩
      simp only [recvSet, Finset.mem_val, mem_filter, mem_univ, true_and]
      exact ⟨h1, h2⟩

/-! ## The concrete simulation for `f = 1` -/

/-- The nodes of the graph for `f = 1`. -/
def nodes1 : List (PNode 1) := [src, cl 0, cl 1, leaf]

theorem mem_nodes1 (u : PNode 1) : u ∈ nodes1 := by
  cases u with
  | src => simp [nodes1]
  | cl i => fin_cases i <;> simp [nodes1]
  | leaf => simp [nodes1]

/-- Boolean adjacency of `pGraph 1`. -/
def adjB : PNode 1 → PNode 1 → Bool
  | src, cl _ => true
  | cl i, cl j => i != j
  | cl _, leaf => true
  | _, _ => false

theorem adjB_iff (u w : PNode 1) : adjB u w = true ↔ (pGraph 1).Adj u w := by
  cases u <;> cases w <;> simp only [adjB, pGraph_adj, PNode.Adj, bne_iff_ne, ne_eq] <;> simp

/-- Delivery in iteration `t` when at most the node `cr` crashes, in iteration `c`, reaching the
nodes `w` with `pt w` in that iteration. -/
def dB (cr : Option (PNode 1)) (c : ℕ) (pt : PNode 1 → Bool) (t : ℕ) (u w : PNode 1) : Bool :=
  adjB u w && (if cr = some u then decide (t < c) || (decide (t = c) && pt w) else true)

/-- The values of `notMax` under the delivery pattern `dB`. -/
def simB (cr : Option (PNode 1)) (c : ℕ) (pt inp : PNode 1 → Bool) : ℕ → PNode 1 → Bool
  | 0, u => inp u
  | t + 1, w => !(simB cr c pt inp t w ||
      nodes1.any fun u => u != w && dB cr c pt t u w && simB cr c pt inp t u)

/-- A function `PNode 1 → Bool` from its four values. -/
def mkF (a b c d : Bool) : PNode 1 → Bool
  | src => a
  | cl i => if i = 0 then b else c
  | leaf => d

theorem mkF_eta (g : PNode 1 → Bool) : mkF (g src) (g (cl 0)) (g (cl 1)) (g leaf) = g := by
  funext u
  cases u with
  | src => rfl
  | cl i => fin_cases i <;> rfl
  | leaf => rfl

/-- Both values of a Boolean predicate. -/
def allB (p : Bool → Bool) : Bool := p false && p true

theorem allB_spec {p : Bool → Bool} (h : allB p = true) (b : Bool) : p b = true := by
  simp only [allB, Bool.and_eq_true] at h
  cases b
  · exact h.1
  · exact h.2

/-- The finite check: for every crash pattern with at most one crash (crash iteration `c ≤ 4`,
`c = 4` meaning "after the output"), all partial-delivery sets and all inputs, the values after
iteration 4 of the non-crashed nodes agree and are inputs. -/
def check : Bool :=
  [none, some src, some (cl 0), some (cl 1), some leaf].all fun cr =>
    (List.range 5).all fun c =>
      allB fun p₁ => allB fun p₂ => allB fun p₃ => allB fun p₄ =>
      allB fun i₁ => allB fun i₂ => allB fun i₃ => allB fun i₄ =>
        nodes1.all fun u => nodes1.all fun w =>
          (cr == some u || cr == some w) ||
            (simB cr c (mkF p₁ p₂ p₃ p₄) (mkF i₁ i₂ i₃ i₄) 4 u ==
                simB cr c (mkF p₁ p₂ p₃ p₄) (mkF i₁ i₂ i₃ i₄) 4 w &&
              nodes1.any fun v => mkF i₁ i₂ i₃ i₄ v == simB cr c (mkF p₁ p₂ p₃ p₄) (mkF i₁ i₂ i₃ i₄) 4 u)

theorem check_ok : check = true := by decide +kernel

/-! ## From arbitrary crash patterns to the concrete ones -/

open Classical in
/-- The run of `notMax` agrees with `simB` as long as the deliveries agree. -/
theorem iter_eq_simB (adv : Adversary (PNode 1)) (inp : PNode 1 → Bool) (cr : Option (PNode 1))
    (c : ℕ) (pt : PNode 1 → Bool) (T : ℕ)
    (hdel : ∀ t < T, ∀ u w, Delivers (pGraph 1) adv t u w ↔ dB cr c pt t u w = true) :
    ∀ t ≤ T, ∀ w, iterState (pGraph 1) notMax adv inp t w = simB cr c pt inp t w := by
  intro t
  induction t with
  | zero => intro _ w; rfl
  | succ t ih =>
    intro ht w
    have key : (∃ u, u ≠ w ∧ Delivers (pGraph 1) adv t u w ∧
        iterState (pGraph 1) notMax adv inp t u = true) ↔
        (nodes1.any fun u => u != w && dB cr c pt t u w && simB cr c pt inp t u) = true := by
      simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
      constructor
      · rintro ⟨u, hu, hd, hx⟩
        exact ⟨u, mem_nodes1 u, ⟨hu, (hdel t (by omega) u w).mp hd⟩,
          by rw [← ih (by omega) u]; exact hx⟩
      · rintro ⟨u, -, ⟨hu, hd⟩, hx⟩
        exact ⟨u, hu, (hdel t (by omega) u w).mpr hd, by rw [ih (by omega) u]; exact hx⟩
    rw [notMax_iter, simB, ih (by omega) w]
    have : decide (∃ u, u ≠ w ∧ Delivers (pGraph 1) adv t u w ∧
        iterState (pGraph 1) notMax adv inp t u = true) =
        (nodes1.any fun u => u != w && dB cr c pt t u w && simB cr c pt inp t u) :=
      Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact key)
    rw [this]

open Classical in
/-- Under an admissible crash pattern with at most one crash, the deliveries of iterations
`t < 4` are those of a concrete pattern `dB`. -/
theorem exists_pattern (adv : Adversary (PNode 1)) (hadm : adv.Admissible 1) :
    ∃ cr : Option (PNode 1), ∃ c ≤ 4, (∀ u, adv.crash u = none → cr ≠ some u) ∧
      ∀ t < 4, ∀ u w, Delivers (pGraph 1) adv t u w ↔
        dB cr c (fun w => decide (∃ x, cr = some x ∧ adv.part x w)) t u w = true := by
  obtain ⟨F, hF, hmem⟩ := hadm
  by_cases hx : ∃ x c, adv.crash x = some c
  · obtain ⟨x, c, hc⟩ := hx
    have huniq : ∀ y c', adv.crash y = some c' → y = x := by
      intro y c' hy
      have h1 := hmem y c' hy
      have h2 := hmem x c hc
      exact Finset.card_le_one.mp hF y h1 x h2
    refine ⟨some x, min c 4, by omega, fun u hu h => by
      simp only [Option.some.injEq] at h; subst h; simp [hu] at hc, fun t ht u w => ?_⟩
    simp only [Delivers, dB, Bool.and_eq_true, adjB_iff, Option.some.injEq]
    apply and_congr_right
    intro _
    by_cases hux : x = u
    · subst hux
      simp only [hc, Option.some.injEq, forall_eq', ↓reduceIte, Bool.or_eq_true,
        decide_eq_true_eq, Bool.and_eq_true, exists_eq_left']
      constructor
      · rintro (h | ⟨rfl, h⟩)
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, h⟩
      · rintro (h | ⟨h1, h⟩)
        · exact Or.inl (by omega)
        · right; refine ⟨by omega, h⟩
    · simp only [hux, ↓reduceIte, iff_true]
      intro c' hc'
      exact absurd (huniq u c' hc').symm hux
  · push Not at hx
    refine ⟨none, 0, by omega, fun _ _ => by simp, fun t _ u w => ?_⟩
    simp only [Delivers, dB, Bool.and_eq_true, adjB_iff, reduceCtorEq, ↓reduceIte, and_true]
    exact ⟨fun h => h.1, fun h => ⟨h, fun c hc => absurd hc (hx u c)⟩⟩

/-- **The fixed-iteration reading of Theorem 5 fails for the paper's graph** (`f = 1`): the graph
of Appendix B satisfies 1 CT node connectivity, and the fixed iterative algorithm `Z = ¬max`,
outputting after iteration 4, solves binary crash consensus on it. -/
theorem notMax_solvesAt : CTConn (pGraph 1) 1 ∧ SolvesAt (pGraph 1) 1 notMax 4 := by
  refine ⟨pGraph_ctConn 1, fun adv hadm inp u w hu hw => ?_⟩
  classical
  obtain ⟨cr, c, hc, hcor, hpat⟩ := exists_pattern adv hadm
  set pt : PNode 1 → Bool := fun w => decide (∃ x, cr = some x ∧ adv.part x w)
  have hrun := iter_eq_simB adv inp cr c pt 4 hpat 4 le_rfl
  rw [hrun u, hrun w]
  have h := check_ok
  simp only [check, List.all_eq_true] at h
  have hcr : cr ∈ [none, some src, some (cl 0), some (cl 1), some leaf] := by
    rcases cr with _ | x
    · simp
    · cases x with
      | src => simp
      | cl i => fin_cases i <;> simp
      | leaf => simp
  have h1 := h cr hcr c (List.mem_range.mpr (by omega))
  have h2 := allB_spec (allB_spec (allB_spec (allB_spec (allB_spec (allB_spec (allB_spec
    (allB_spec h1 (pt src)) (pt (cl 0))) (pt (cl 1))) (pt leaf)) (inp src)) (inp (cl 0)))
    (inp (cl 1))) (inp leaf)
  rw [mkF_eta, mkF_eta] at h2
  simp only [List.all_eq_true] at h2
  have h3 := h2 u (mem_nodes1 u) w (mem_nodes1 w)
  have hu' := hcor u hu
  have hw' := hcor w hw
  simp only [Bool.or_eq_true, beq_iff_eq, hu', hw', or_self, false_or, Bool.and_eq_true,
    List.any_eq_true] at h3
  obtain ⟨h4, v, -, hv⟩ := h3
  exact ⟨by simpa using h4, v, by simpa using hv⟩

end CrashConsensusDigraph
