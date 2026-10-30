import Papers.PODC2012.WeakModelsModalLogic.Lemma15

/-!
# Lemma 16 of Hella et al.

If `G` is `k`-regular for an odd `k` and some *consistent* port numbering makes all nodes
bisimilar in `K_{+,+}(G, p)`, then `G` has a 1-factor (perfect matching).

Proof (as in the paper): reading `p` on `V × Fin k` (`PortNumbering.onProd`), bisimilarity of
all nodes forces the remote port number `f(i)` behind port `i` to be the same at every node;
consistency makes `f` an involution of `Fin k`; since `k` is odd, `f` has a fixed point `i`, and
the edges `{v, w}` with `p((v, i)) = (w, i)` form a perfect matching.
-/

namespace Podc.WeakModelsModalLogic

open Function

-- CSLib candidate
/-- An involution of a finite type of odd cardinality has a fixed point. -/
theorem Involutive.exists_fixed_of_odd_card {α : Type*} [Fintype α] {f : α → α}
    (hf : Involutive f) (hodd : Odd (Fintype.card α)) : ∃ x, f x = x := by
  classical
  by_contra hne
  push Not at hne
  let σ : Equiv.Perm α := hf.toPerm
  have h2 : σ ^ 2 = 1 := by
    ext x; simp [σ, sq, hf x]
  have hsupp : σ.support = Finset.univ := by
    ext x; simp [σ, Equiv.Perm.mem_support, hne x]
  have := Equiv.Perm.two_dvd_card_support h2
  rw [hsupp, Finset.card_univ] at this
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)

-- CSLib candidate
/-- An involution `m` of `V` with `G.Adj v (m v)` for all `v` (hence fixed-point-free) gives a
perfect matching. -/
theorem exists_perfectMatching_of_involutive {V : Type*} {G : SimpleGraph V} (m : V → V)
    (hm : Involutive m) (hadj : ∀ v, G.Adj v (m v)) : ∃ M : G.Subgraph, M.IsPerfectMatching := by
  let M : G.Subgraph :=
    { verts := Set.univ
      Adj := fun u w => m u = w
      adj_sub := by rintro u w rfl; exact hadj u
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨by rintro u w rfl; exact hm u⟩ }
  refine ⟨M, fun v _ => ⟨m v, rfl, fun w (hw : m v = w) => hw.symm⟩, fun v => Set.mem_univ v⟩

variable {V : Type*}

/-- Lemma 16 of [Hella et al.]. If `G` is `k`-regular for an odd `k` and there is a consistent
port numbering of `G` such that all its nodes are bisimilar in `K_{+,+}(G, p)`, then `G` has a
1-factor. -/
theorem lemma16 [Finite V] (G : SimpleGraph V) (k : ℕ) (hodd : Odd k) (hk : ∀ v, deg G v = k)
    (P : PortNumbering G) (hc : P.Consistent) (hb : ∀ u v, P.BisimilarPP u v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨u₀⟩⟩
  · exact ⟨⊥, fun v => isEmptyElim v, fun v => isEmptyElim v⟩
  let q := P.onProd hk
  have hq : ∀ x, q (q x) = x := by
    intro x; simp [q, PortNumbering.onProd, hc _]
  have hR : ∀ (i j : Fin k) (u v : V), P.R i j u v ↔ q (v, j) = (u, i) := by
    intro i j u v
    rw [P.R_iff_onProd hk]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨i.2, j.2, h⟩⟩
  -- The remote port behind port `i` does not depend on the node.
  have hconst : ∀ (u u' : V) (i : Fin k), (q (u', i)).2 = (q (u, i)).2 := by
    intro u u' i
    obtain ⟨Z, hZ, huu'⟩ := hb u u'
    have h1 : P.R i (q (u, i)).2 u (q (u, i)).1 := by
      rw [hR]; exact hq _
    obtain ⟨w', hw', -⟩ := (hZ u u' huu').2.1 _ _ _ h1
    rw [hR] at hw'
    rw [← hw', hq]
  let f : Fin k → Fin k := fun i => (q (u₀, i)).2
  have hf : Involutive f := by
    intro i
    simp only [f]
    rw [hconst (q (u₀, i)).1 u₀, ← hq (u₀, i)]
    simp [hq]
  obtain ⟨i₀, hi₀⟩ := Involutive.exists_fixed_of_odd_card hf (by simpa using hodd)
  have hfix : ∀ u, (q (u, i₀)).2 = i₀ := fun u => (hconst u₀ u i₀).trans hi₀
  have hqu : ∀ u, q (u, i₀) = ((q (u, i₀)).1, i₀) := fun u => Prod.ext rfl (hfix u)
  let m : V → V := fun u => (q (u, i₀)).1
  refine exists_perfectMatching_of_involutive m (fun u => ?_) (fun u => ?_)
  · simp only [m]
    rw [← hqu, hq]
  · have := P.adj ((portEquivOfRegular hk).symm (u, i₀))
    simpa [m, q, PortNumbering.onProd] using this

end Podc.WeakModelsModalLogic
