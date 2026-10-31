import Papers.PODC2018.PartialReplicationCausal.Theorem3

/-!
# Helpers for concrete executions

Steps of explicit executions (used by the counterexamples in `Lemma4.lean` and `Footnote2.lean`):
a write is always possible; an update can be applied as soon as every earlier update on a register
of the receiver has been applied there (then all its dependencies are applied and, by
`ready_of_deps`, the predicate of Step 4 holds).
-/

namespace Podc.PartialReplicationCausal

variable {ι Reg : Type*} {X : ι → Set Reg} {s : State ι Reg}

lemma Reachable.write (hs : Reachable X s) {i : ι} {x : Reg} (hx : x ∈ X i) :
    Reachable X (s.write X i x) := by
  obtain ⟨s', h', h''⟩ := hs; exact ⟨s', h', h''.tail (.write s i x hx)⟩

lemma Reachable.apply (hs : Reachable X s) {i : ι} {u : ℕ}
    (hu : u < s.n) (hki : (s.log u).src ≠ i) (hux : (s.log u).reg ∈ X i) (hnot : u ∉ s.app i)
    (hprev : ∀ a < u, (s.log a).reg ∈ X i → a ∈ s.app i) : Reachable X (s.apply X i u) := by
  have h := Inv.of_reachable hs
  have hen : Enabled X s i u := ⟨hu, hki, hux, hnot, ready_of_deps h hu hki hux hnot
    (fun a ha hau => hprev a (h.hb_lt hau) ha)⟩
  obtain ⟨s', h', h''⟩ := hs; exact ⟨s', h', h''.tail (.apply s i u hen)⟩

/-- If `X_i ⊆ X_k` and `i` is not a neighbour of `j`, then there is no `(i, e_jk)`-loop: the last
pair `(r_t, i)` of condition (iii) (or, if `t = 1`, the adjacency of `j` and `i`) fails. -/
theorem not_isLoop_of_subset {ι Reg : Type*} {X : ι → Set Reg} {i j k : ι} (hsub : X i ⊆ X k)
    (hji : ¬ Adj X j i) (l r : List ι) : ¬ IsLoop X i j k l r := by
  intro hl
  rcases List.eq_nil_or_concat r with rfl | ⟨r', y, rfl⟩
  · have := hl.adj
    rw [show i :: (l ++ k :: j :: []) ++ [i] = (i :: l ++ [k]) ++ j :: i :: [] by simp,
      List.isChain_append_cons_cons] at this
    exact hji this.2.1
  · have := hl.cond_iii
    rw [List.concat_eq_append, show r' ++ [y] ++ [i] = r' ++ y :: i :: [] by simp, List.isChain_append_cons_cons] at this
    obtain ⟨x, ⟨_, hxi⟩, hxk, _⟩ := this.2.1
    exact hxk (hsub hxi)

end Podc.PartialReplicationCausal
