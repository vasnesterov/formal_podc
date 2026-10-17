import Papers.PODC2026.TreeAA.Protocol

/-!
# Non-vacuity of the black-box hypotheses

The theorems of this folder assume black-box gradecast and RealAA protocols. Here we exhibit
simple protocols satisfying these hypotheses in the failure-free case `t = 0` (one-round
exchange; gradecast: forward the sender's value with grade 2; RealAA: everybody outputs the
minimum of all inputs), and instantiate Theorem 5 on the path with three vertices. (Protocols
for `t ≥ 1` — Ben-Or–Dolev–Hoch gradecast and RealAA for `t < n/3`, or their authenticated
counterparts — are cited by the paper and not formalized.)
-/

namespace TreeAA

open Cslib.Byzantine.LockStep SimpleGraph

variable {P : Type} [Fintype P] [DecidableEq P]

omit [DecidableEq P] in
lemma mem_honest_of_atMost_zero {I M : Type*} {s : Scenario P I M} (h : s.byz ∈ atMost (P := P) 0)
    (p : P) : p ∈ s.honest := by
  simp [Scenario.honest, eq_empty_of_mem_atMost_zero h]

/-- In a reliable failure-free run, the first inbox of `p` contains `q`'s round-0 message. -/
lemma hist_one_of_atMost_zero {I M O : Type*} (alg : Protocol P I M O) {s : Scenario P I M}
    (h : s.byz ∈ atMost (P := P) 0) (hrel : s.Reliable) (p : P) :
    hist ⊤ alg s 1 p = [fun q => if q = p then none else alg.send q (s.input q) [] p] := by
  rw [hist_succ, hist_zero, List.nil_append]
  congr 1
  funext q
  have hq : q ∉ s.byz := by simp [eq_empty_of_mem_atMost_zero h]
  by_cases hqp : q = p
  · subst hqp; simp [deliver]
  · simp [deliver, top_adj, hqp, hq, hrel 0 q p]

/-! ### Gradecast for `t = 0` -/

/-- Trivial gradecast: the sender sends its value in round 0; it outputs `(x, 2)` at once, the
others output the received value with grade 2 after one round. -/
def gcTriv {W : Type} (snd : P) : Protocol P W W (W × Fin 3) where
  send p x h _ := if p = snd ∧ h = [] then some x else none
  decide p x h := if p = snd then some (x, 2) else
    match h with
    | [] => none
    | ib :: _ => some ((ib snd).getD x, 2)

lemma gcTriv_solves {W : Type} (snd : P) :
    SolvesAuthWithin ⊤ (gcTriv (W := W) snd) (Auth.none P W) (atMost 0) noPre (Gradecast snd) 1 := by
  intro s hZ hrel _ _
  have hH := mem_honest_of_atMost_zero hZ
  -- everybody decides `(x snd, 2)`
  have hdec : ∀ p, Decides ⊤ (gcTriv snd) s p (s.input snd, 2) := by
    intro p
    by_cases hp : p = snd
    · subst hp
      exact ⟨0, by simp [status, gcTriv], fun r hr => absurd hr (Nat.not_lt_zero _)⟩
    · refine ⟨1, ?_, fun r hr => ?_⟩
      · simp only [status, hist_one_of_atMost_zero _ hZ hrel p]
        simp [gcTriv, hp, Ne.symm hp]
      · obtain rfl : r = 0 := by omega
        simp [status, gcTriv, hp]
  refine ⟨⟨fun p _ => ⟨_, hdec p⟩, fun _ p _ => hdec p, ?_⟩, ?_⟩
  · intro p _ q _ v w g g' h1 h2
    have e1 := Decides.unique _ _ h1 (hdec p)
    have e2 := Decides.unique _ _ h2 (hdec q)
    simp only [Prod.mk.injEq] at e1 e2
    obtain ⟨rfl, rfl⟩ := e1
    obtain ⟨rfl, rfl⟩ := e2
    exact ⟨by decide, fun _ _ => rfl⟩
  · intro p _
    by_cases hp : p = snd
    · subst hp; exact ⟨0, by omega, (s.input p, 2), by simp [status, gcTriv]⟩
    · exact ⟨1, le_rfl, (s.input snd, 2), by
        simp only [status, hist_one_of_atMost_zero _ hZ hrel p]; simp [gcTriv, hp, Ne.symm hp]⟩

/-! ### RealAA for `t = 0` -/

variable [Nonempty P]

/-- Trivial RealAA: everybody sends its input in round 0 and outputs the minimum of all inputs
after one round. -/
noncomputable def realTriv : Protocol P ℝ ℝ ℝ where
  send _ x h _ := if h = [] then some x else none
  decide p x h :=
    match h with
    | [] => none
    | ib :: _ => some (Finset.univ.inf' Finset.univ_nonempty fun q => if q = p then x else (ib q).getD x)

lemma realTriv_solves (D ε : ℝ) (hε : 0 ≤ ε) :
    SolvesAuthWithin ⊤ realTriv (Auth.none P ℝ) (atMost 0) (Close D) (RealAA ε) 1 := by
  intro s hZ hrel _ _
  have hH := mem_honest_of_atMost_zero hZ
  set m := Finset.univ.inf' Finset.univ_nonempty s.input
  have hdec : ∀ p, Decides ⊤ realTriv s p m := by
    intro p
    refine ⟨1, ?_, fun r hr => ?_⟩
    · simp only [status, hist_one_of_atMost_zero _ hZ hrel p, realTriv]
      congr 1
      apply Finset.inf'_congr _ rfl
      intro q _
      by_cases hq : q = p
      · subst hq; simp
      · simp [hq]
    · obtain rfl : r = 0 := by omega
      simp [status, realTriv]
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty s.input
  refine ⟨⟨fun p _ => ⟨_, hdec p⟩, fun p _ o ho => ?_, fun p _ q _ o o' h1 h2 => ?_⟩, ?_⟩
  · rw [Decides.unique _ _ ho (hdec p), show m = s.input a from ha]
    exact ⟨a, hH a, a, hH a, le_rfl, le_rfl⟩
  · rw [Decides.unique _ _ h1 (hdec p), Decides.unique _ _ h2 (hdec q)]
    simpa using hε
  · intro p _
    obtain ⟨r, hr, hmin⟩ := hdec p
    have hr1 : r ≤ 1 := by
      by_contra h
      have := hmin 1 (by omega)
      simp only [status, hist_one_of_atMost_zero _ hZ hrel p, realTriv] at this
      exact absurd this (by simp)
    exact ⟨r, hr1, m, hr⟩

/-! ### Theorem 5 on a concrete tree -/

instance : DecidableRel (pathGraph 3).Adj := fun _ _ => decidable_of_iff _ pathGraph_adj.symm

lemma pathGraph_three_isTree : (pathGraph 3).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨pathGraph_connected 2, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

/-- Theorem 5's hypotheses are satisfiable: with two parties and `t = 0`, `TreeAA` on the path
with three vertices (built from the trivial gradecast and RealAA) achieves AA within 2 rounds. -/
theorem treeAA_nonvacuous :
    SolvesAuthWithin ⊤
      (treeAA (P := Fin 2) pathGraph_three_isTree 0 0 1 gcTriv realTriv)
      (treeAuth (Auth.none (Fin 2) (List (Fin 3))) (Auth.none (Fin 2) ℝ)) (atMost 0) noPre
      (GraphAA (pathGraph 3)) (1 + 1) :=
  (treeAA_solves pathGraph_three_isTree 0 (by decide) _ _ (fun _ => Protocol.unforging_none _)
    (fun s => gcTriv_solves s) _ _ (Protocol.unforging_none _) (realTriv_solves _ 1 zero_le_one)).2

end TreeAA
