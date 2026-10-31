import Mathlib

/-!
# Graph lemmas

* `colorable_two_of_even_short_loops`: a finite graph is bipartite as soon as every closed walk of
  length `< 2 n` is even (shortest-path parity colouring). -- CSLib candidate
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

/-- A finite graph is 2-colourable if every closed walk of length `< 2 · |V|` has even length.
-- CSLib candidate -/
theorem colorable_two_of_even_short_loops {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : ∀ u (w : G.Walk u u), w.length < 2 * Fintype.card V → Even w.length) :
    G.Colorable 2 := by
  classical
  let r : V → V := fun a => (G.connectedComponentMk a).out
  have hr : ∀ a, G.Reachable (r a) a := fun a =>
    ConnectedComponent.exact (Quot.out_eq _)
  let p : ∀ a, G.Walk (r a) a := fun a => (hr a).some.bypass
  have hp : ∀ a, (p a).length < Fintype.card V := fun a =>
    (Walk.bypass_isPath _).length_lt
  refine ⟨Coloring.mk (fun a => (⟨(p a).length % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
  intro a b hab heq
  have hrab : r a = r b := by
    simp only [r]
    rw [ConnectedComponent.eq.2 hab.reachable]
  have hpar : (p a).length % 2 = (p b).length % 2 := by simpa [Fin.ext_iff] using heq
  let w : G.Walk (r a) (r a) := ((p a).concat hab).append ((p b).reverse.copy rfl hrab.symm)
  have hlen : w.length = (p a).length + 1 + (p b).length := by
    simp [w]
  have := h _ w (by have := hp a; have := hp b; omega)
  rw [hlen] at this
  obtain ⟨k, hk⟩ := this
  omega


/-- A walk whose support has a duplicate splits off a nonempty closed sub-walk. -/
lemma Walk.exists_split_of_not_nodup {V : Type*} [DecidableEq V] {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), ¬ p.support.Nodup →
      ∃ (y : V) (Q : G.Walk u y) (R : G.Walk y y) (Q' : G.Walk y v),
        p = Q.append (R.append Q') ∧ R.length ≠ 0
  | _, _, .nil, h => by simp at h
  | u, _, .cons h p, hnd => by
    rw [Walk.support_cons, List.nodup_cons] at hnd
    by_cases hu : u ∈ p.support
    · refine ⟨u, Walk.nil, Walk.cons h (p.takeUntil u hu), p.dropUntil u hu, ?_, by simp⟩
      simp [Walk.take_spec]
    · obtain ⟨y, Q, R, Q', rfl, hR⟩ := Walk.exists_split_of_not_nodup p (by tauto)
      exact ⟨y, Walk.cons h Q, R, Q', by simp, hR⟩

/-- Every odd closed walk contains an odd cycle. -- CSLib candidate -/
lemma exists_odd_cycle {V : Type*} [DecidableEq V] {G : SimpleGraph V} :
    ∀ (n : ℕ) {x : V} (Z : G.Walk x x), Z.length = n → Odd n →
      ∃ (y : V) (C : G.Walk y y), C.IsCycle ∧ Odd C.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x Z hZ hodd
    cases Z with
    | nil => simp at hZ; subst hZ; exact absurd hodd (by decide)
    | cons h p =>
      rename_i w
      by_cases hp : p.support.Nodup
      · have hpp : p.IsPath := (Walk.isPath_def p).2 hp
        by_cases he : s(x, w) ∈ p.edges
        · exfalso
          have h1 : p.length = 1 := by
            cases p with
            | nil => simp at he
            | cons h' q =>
              rw [Walk.cons_isPath_iff] at hpp
              rw [Walk.edges_cons, List.mem_cons] at he
              rcases he with he | he
              · rw [Sym2.eq_iff] at he
                rcases he with ⟨rfl, -⟩ | ⟨rfl, -⟩
                · exact absurd h (G.irrefl)
                · have := Walk.length_eq_zero_iff.mpr (Walk.isPath_iff_nil.mp hpp.1)
                  simp [this]
              · exact absurd (q.snd_mem_support_of_mem_edges he) hpp.2
          simp only [Walk.length_cons, h1] at hZ
          subst hZ; exact absurd hodd (by decide)
        · exact ⟨x, Walk.cons h p, (Walk.cons_isCycle_iff p h).2 ⟨hpp, he⟩, hZ ▸ hodd⟩
      · obtain ⟨y, Q, R, Q', rfl, hR⟩ := Walk.exists_split_of_not_nodup p hp
        simp only [Walk.length_cons, Walk.length_append] at hZ
        rcases Nat.even_or_odd R.length with hRe | hRo
        · exact ih ((Walk.cons h Q).append Q').length (by simp; omega) _ rfl
            (by simp only [Walk.length_append, Walk.length_cons]
                obtain ⟨r, hr⟩ := hodd; obtain ⟨q, hq⟩ := hRe; exact ⟨r - q, by omega⟩)
        · exact ih R.length (by omega) R rfl hRo

end Podc.HidingColoringCertification
