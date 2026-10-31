import Mathlib

/-!
# Odd cycles and the odd girth

-- CSLib candidate: `Cslib/Foundations/Combinatorics/SimpleGraph/OddGirth.lean`
(Mathlib has `egirth`/`girth` but nothing about odd cycles.)

* `SimpleGraph.Walk.exists_isPath_or_odd_cycle`: every walk `u ⟶ v` either shortens to a path of
  the same parity, or contains an odd cycle no longer than the walk.
* `SimpleGraph.Walk.exists_odd_isCycle`: every odd closed walk contains an odd cycle of at most the
  same length.
* `SimpleGraph.oddGirth`: length of a shortest odd cycle (`⊤` if there is none);
  `SimpleGraph.oddGirth_le_length` (odd closed walks are at least as long),
  `SimpleGraph.oddGirth_ne_top_iff` (finite iff not bipartite), `SimpleGraph.exists_oddGirth_eq`
  (for a non-bipartite graph the odd girth is `2ϕ + 1` for some `ϕ ≥ 1`).

Used by `Papers/PODC2015/DeterministicLoadBalancing` (Theorem 4.3: rotor-router lower bound via the
odd girth).
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace Walk

/-- Every walk from `u` to `v` either can be replaced by a path from `u` to `v` that is not longer
and has the same length parity, or it contains an odd cycle that is not longer than the walk. -/
theorem exists_isPath_or_odd_cycle [DecidableEq V] {u v : V} (p : G.Walk u v) :
    (∃ q : G.Walk u v, q.IsPath ∧ q.length ≤ p.length ∧ Even (p.length + q.length)) ∨
      ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ Odd c.length ∧ c.length ≤ p.length := by
  induction p with
  | nil => exact Or.inl ⟨nil, by simp, le_rfl, by simp⟩
  | @cons u w v h p ih =>
    rcases ih with ⟨q, hq, hql, hqe⟩ | ⟨a, c, hc, hco, hcl⟩
    · by_cases hu : u ∈ q.support
      · have hspec := q.take_spec hu
        have hlen : (q.takeUntil u hu).length + (q.dropUntil u hu).length = q.length := by
          conv_rhs => rw [← hspec]
          rw [length_append]
        rcases Nat.even_or_odd (q.takeUntil u hu).length with he | ho
        · -- `u ⟶ w ⟶ … ⟶ u` is an odd cycle
          right
          have hp1 : (q.takeUntil u hu).IsPath := hq.takeUntil hu
          have hne : (q.takeUntil u hu).length ≠ 0 := by
            intro h0
            have := eq_of_length_eq_zero h0
            exact h.ne this.symm
          refine ⟨u, cons h (q.takeUntil u hu), ?_, ?_, ?_⟩
          · rw [isCycle_iff_isPath_tail_and_le_length]
            refine ⟨by simpa using hp1, ?_⟩
            simp only [length_cons]
            obtain ⟨r, hr⟩ := he
            omega
          · simp only [length_cons]; exact he.add_one
          · simp only [length_cons]; omega
        · left
          refine ⟨q.dropUntil u hu, hq.dropUntil hu, by simp only [length_cons]; omega, ?_⟩
          simp only [length_cons]
          rw [Nat.even_iff] at hqe ⊢
          rw [Nat.odd_iff] at ho
          omega
      · left
        refine ⟨cons h q, hq.cons hu, by simp [hql], ?_⟩
        simp only [length_cons]
        rw [Nat.even_iff] at hqe ⊢
        omega
    · exact Or.inr ⟨a, c, hc, hco, by simp only [length_cons]; omega⟩

/-- Every closed walk of odd length contains an odd cycle of at most the same length. -/
theorem exists_odd_isCycle {u : V} (p : G.Walk u u) (hp : Odd p.length) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ Odd c.length ∧ c.length ≤ p.length := by
  classical
  rcases p.exists_isPath_or_odd_cycle with ⟨q, hq, -, hqe⟩ | h
  · have : q = nil := by
      cases q with
      | nil => rfl
      | cons h' q' =>
        exfalso
        have := hq.support_nodup
        simp only [support_cons, List.nodup_cons] at this
        exact this.1 q'.end_mem_support
    subst this
    simp only [length_nil, add_zero] at hqe
    exact absurd hqe (Nat.not_even_iff_odd.2 hp)
  · exact h

end Walk

/-- The *odd girth* of a graph: the length of a shortest odd cycle, or `⊤` if the graph has no odd
cycle (i.e. is bipartite). -/
noncomputable def oddGirth (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (a : V) (c : G.Walk a a) (_ : c.IsCycle) (_ : Odd c.length), (c.length : ℕ∞)

theorem Walk.IsCycle.oddGirth_le_length {a : V} {c : G.Walk a a} (hc : c.IsCycle)
    (ho : Odd c.length) : G.oddGirth ≤ c.length :=
  iInf₂_le_of_le a c <| iInf₂_le_of_le hc ho le_rfl

/-- The odd girth is at most the length of any odd closed walk. -/
theorem oddGirth_le_length {u : V} (p : G.Walk u u) (hp : Odd p.length) :
    G.oddGirth ≤ p.length := by
  obtain ⟨a, c, hc, hco, hcl⟩ := p.exists_odd_isCycle hp
  exact (hc.oddGirth_le_length hco).trans (by exact_mod_cast hcl)

/-- The odd girth is attained by an odd cycle whenever it is finite. -/
theorem exists_isCycle_length_eq_oddGirth (h : G.oddGirth ≠ ⊤) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ Odd c.length ∧ (c.length : ℕ∞) = G.oddGirth := by
  classical
  have hex : ∃ n, ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ Odd c.length ∧ c.length = n := by
    by_contra hne
    push Not at hne
    apply h
    refine eq_top_iff.2 (le_iInf₂ fun a c => le_iInf₂ fun hc ho => ?_)
    exact absurd rfl (hne _ a c hc ho)
  obtain ⟨a, c, hc, ho, hcl⟩ := Nat.find_spec hex
  refine ⟨a, c, hc, ho, le_antisymm ?_ (hc.oddGirth_le_length ho)⟩
  refine le_iInf₂ fun b d => le_iInf₂ fun hd hdo => ?_
  rw [hcl]
  exact_mod_cast Nat.find_min' hex ⟨b, d, hd, hdo, rfl⟩

/-- A graph has finite odd girth iff it is not bipartite. -/
theorem oddGirth_ne_top_iff : G.oddGirth ≠ ⊤ ↔ ¬ G.IsBipartite := by
  constructor
  · intro h hb
    obtain ⟨a, c, -, hco, -⟩ := exists_isCycle_length_eq_oddGirth h
    have := (two_colorable_iff_forall_loop_even.1 hb) a c
    exact Nat.not_even_iff_odd.2 hco this
  · intro hb
    have : ¬ ∀ u (w : G.Walk u u), Even w.length := fun h' =>
      hb (two_colorable_iff_forall_loop_even.2 h')
    push Not at this
    obtain ⟨u, w, hw⟩ := this
    have := oddGirth_le_length w (Nat.not_even_iff_odd.1 hw)
    exact ne_top_of_le_ne_top (by simp) this

/-- For a non-bipartite graph the odd girth is `2ϕ + 1` for some `ϕ ≥ 1`. -/
theorem exists_oddGirth_eq (hb : ¬ G.IsBipartite) : ∃ ϕ : ℕ, 1 ≤ ϕ ∧ G.oddGirth = 2 * ϕ + 1 := by
  obtain ⟨a, c, hc, hco, hcl⟩ := exists_isCycle_length_eq_oddGirth (oddGirth_ne_top_iff.2 hb)
  obtain ⟨ϕ, hϕ⟩ := hco
  have h3 := hc.three_le_length
  refine ⟨ϕ, by omega, ?_⟩
  rw [← hcl, hϕ]; push_cast; ring

end SimpleGraph
