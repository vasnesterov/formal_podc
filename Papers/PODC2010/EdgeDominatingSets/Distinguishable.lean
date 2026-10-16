import Papers.PODC2010.EdgeDominatingSets.Basic

/-!
# Distinguishable neighbours (§5 of the paper)

For a node `v` of a port-numbered graph, the *label pair* of the edge behind port `i` is the
unordered pair `{i, rport v i}`. Port `i` is *uniquely labelled* if no other port of `v` has the
same label pair; the *distinguishable neighbour* of `v` is the neighbour behind the smallest
uniquely labelled port (`dn v = some i`), if any.

* `dnOf d rp`: the distinguishable port, computed from the degree and the remote port numbers
  only — i.e. from information a node has after one communication round.
* Lemma 1 (`dn_isSome_of_odd`): a node of odd degree has a distinguishable neighbour.
* `M G i j` (the paper's `M_G(i, j)`): the edges `{v, u}` with `p(v, i) = (u, j)` such that `u` is
  the distinguishable neighbour of `v`.
* Lemma 2 (`M_matching`): each `M G i j` is a matching (in a simple graph).
* `edge_mem_M_iff`: whether the edge behind port `q` of `v` is in `M G i j` can be decided by `v`
  from its own distinguishable port, its remote port numbers, and the distinguishable ports of its
  neighbours (two rounds of communication).
-/

namespace Podc.EdgeDominatingSets

open Cslib.PortNumbering Finset

/-- Port `i` is uniquely labelled among ports `0, …, d - 1` with remote ports `rp`. -/
def IsUniq (d : ℕ) (rp : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ j < d, j ≠ i → s(j, rp j) ≠ s(i, rp i)

instance (d : ℕ) (rp : ℕ → ℕ) (i : ℕ) : Decidable (IsUniq d rp i) := by
  unfold IsUniq; infer_instance

/-- The distinguishable port: the smallest uniquely labelled port, if any. -/
def dnOf (d : ℕ) (rp : ℕ → ℕ) : Option ℕ :=
  (List.range d).find? fun i => decide (IsUniq d rp i)

theorem dnOf_spec {d : ℕ} {rp : ℕ → ℕ} {i : ℕ} (h : dnOf d rp = some i) :
    i < d ∧ IsUniq d rp i := by
  unfold dnOf at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [decide_eq_true_eq] at h1
  exact ⟨List.mem_range.1 h2, h1⟩

/-- `dnOf d rp` only depends on `rp` below `d`. -/
theorem dnOf_congr {d : ℕ} {rp rp' : ℕ → ℕ} (h : ∀ i < d, rp i = rp' i) :
    dnOf d rp = dnOf d rp' := by
  unfold dnOf
  apply List.find?_congr
  intro i hi
  have hi := List.mem_range.1 hi
  rw [decide_eq_decide]
  unfold IsUniq
  constructor <;> intro H j hj hji <;> have := H j hj hji
  · rwa [h j hj, h i hi] at this
  · rwa [← h j hj, ← h i hi] at this

theorem dnOf_isSome {d : ℕ} {rp : ℕ → ℕ} {i : ℕ} (hi : i < d) (h : IsUniq d rp i) :
    (dnOf d rp).isSome := by
  unfold dnOf
  rw [List.find?_isSome]
  exact ⟨i, List.mem_range.2 hi, by simpa using h⟩

/-- **Lemma 1** (combinatorial core). If no port among `0, …, d-1` is uniquely labelled and the
remote ports `rp i` are `< d`... then `d` is even: the map `i ↦ rp i` pairs up the ports. -/
theorem even_of_forall_not_isUniq {d : ℕ} {rp : ℕ → ℕ} (h : ∀ i < d, ¬ IsUniq d rp i) :
    Even d := by
  -- each port `i` has a partner `j ≠ i` with the same label pair, hence `j = rp i`, `rp j = i`
  have key : ∀ i < d, rp i < d ∧ rp i ≠ i ∧ rp (rp i) = i := by
    intro i hi
    have := h i hi
    simp only [IsUniq, not_forall, not_not] at this
    obtain ⟨j, hj, hji, he⟩ := this
    rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact absurd h1 hji
    · subst h1; exact ⟨hj, hji, h2⟩
  have := Finset.sum_involution (s := Finset.range d) (f := fun _ => (1 : ZMod 2))
    (fun i _ => rp i) (fun _ _ => by decide)
    (fun i hi _ => (key i (Finset.mem_range.1 hi)).2.1)
    (fun i hi => Finset.mem_range.2 (key i (Finset.mem_range.1 hi)).1)
    (fun i hi => (key i (Finset.mem_range.1 hi)).2.2)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  exact (ZMod.natCast_eq_zero_iff_even).1 this

end Podc.EdgeDominatingSets

namespace Cslib.PortNumbering.PNGraph

open Podc.EdgeDominatingSets

variable {V : Type*} (G : PNGraph V)

/-- The distinguishable port of `v` (the port leading to its distinguishable neighbour). -/
def dn (v : V) : Option ℕ := dnOf (G.deg v) (G.rport v)

theorem dn_spec {v : V} {i : ℕ} (h : G.dn v = some i) :
    i < G.deg v ∧ IsUniq (G.deg v) (G.rport v) i := dnOf_spec h

/-- **Lemma 1.** A node of odd degree has a distinguishable neighbour. -/
theorem dn_isSome_of_odd {v : V} (h : Odd (G.deg v)) : (G.dn v).isSome := by
  by_contra hn
  have : ∀ i < G.deg v, ¬ IsUniq (G.deg v) (G.rport v) i :=
    fun i hi hu => hn (dnOf_isSome hi hu)
  exact (Nat.not_even_iff_odd.2 h) (even_of_forall_not_isUniq this)

end Cslib.PortNumbering.PNGraph

namespace Podc.EdgeDominatingSets

open Cslib.PortNumbering Finset

variable {V : Type*} [Fintype V]

open Classical in
/-- `M_G(i, j)`: the edges `{v, u}` with `p(v, i) = (u, j)` such that `u` is the distinguishable
neighbour of `v`. -/
noncomputable def M (G : PNGraph V) (i j : ℕ) : Finset (Sym2 V) :=
  univ.filter fun e => ∃ v, G.dn v = some i ∧ G.rport v i = j ∧ G.edge v i = e

theorem mem_M {G : PNGraph V} {i j : ℕ} {e : Sym2 V} :
    e ∈ M G i j ↔ ∃ v, G.dn v = some i ∧ G.rport v i = j ∧ G.edge v i = e := by
  classical
  simp [M]

/-- **Lemma 2.** `M_G(i, j)` is a matching: two different edges of `M_G(i, j)` have no common
endpoint. (Simplicity of `G` is not needed.) -/
theorem M_matching {G : PNGraph V} {i j : ℕ} {e₁ e₂ : Sym2 V}
    (h₁ : e₁ ∈ M G i j) (h₂ : e₂ ∈ M G i j) (hne : e₁ ≠ e₂) {x : V} (hx₁ : x ∈ e₁) :
    x ∉ e₂ := by
  obtain ⟨v, hv, hvj, rfl⟩ := mem_M.1 h₁
  obtain ⟨w, hw, hwj, rfl⟩ := mem_M.1 h₂
  obtain ⟨hiv, huv⟩ := G.dn_spec hv
  obtain ⟨hiw, huw⟩ := G.dn_spec hw
  -- if `w` is the neighbour of `v` behind port `i` and `p(v, i) = (w, j)`, then the edges coincide
  -- unless `i ≠ j`, in which case port `j` of `w`... we argue case by case.
  have aux : ∀ v w : V, G.dn v = some i → G.rport v i = j → G.dn w = some i →
      G.rport w i = j → G.edge v i ≠ G.edge w i → G.nbr v i ≠ w := by
    intro v w hv hvj hw hwj hne h
    obtain ⟨hiv, -⟩ := G.dn_spec hv
    obtain ⟨hiw, huw⟩ := G.dn_spec hw
    -- `p(v, i) = (w, j)`, so `p(w, j) = (v, i)`.
    have hwj' : G.nbr w j = v := by rw [← h, ← hvj]; exact G.nbr_nbr hiv
    have hrj : G.rport w j = i := by rw [← h, ← hvj]; exact G.rport_rport hiv
    have hjw : j < G.deg w := by rw [← h, ← hvj]; exact G.rport_lt hiv
    by_cases hij : j = i
    · subst hij
      apply hne
      simp only [PNGraph.edge, h, hwj']
      exact Sym2.eq_swap
    · apply huw j hjw hij
      rw [hrj, hwj, Sym2.eq_swap]
  simp only [PNGraph.edge, Sym2.mem_iff] at hx₁ ⊢
  rintro (rfl | hx₂) <;> rcases hx₁ with rfl | hx₁
  · exact hne rfl
  · exact aux v x hv hvj hw hwj hne hx₁.symm
  · exact aux w x hw hwj hv hvj (Ne.symm hne) hx₂.symm
  · -- common neighbour `u = nbr v i = nbr w i`; port `j` of `u` leads to both `v` and `w`
    have h1 : G.nbr (G.nbr v i) j = v := by rw [← hvj]; exact G.nbr_nbr hiv
    have h2 : G.nbr (G.nbr w i) j = w := by rw [← hwj]; exact G.nbr_nbr hiw
    rw [← hx₁, hx₂] at h1
    rw [h1] at h2
    exact hne (by rw [h2])

/-- Every node with a distinguishable neighbour is covered by `⋃ M_G(i, j)`. -/
theorem edge_dn_mem_M {G : PNGraph V} {v : V} {i : ℕ} (h : G.dn v = some i) :
    G.edge v i ∈ M G i (G.rport v i) :=
  mem_M.2 ⟨v, h, rfl, rfl⟩

/-- Local characterisation of `M_G(i, j)`: the edge behind port `q` of `v` is in `M_G(i, j)` iff
either `q = i` is the distinguishable port of `v` and the remote port is `j`, or the neighbour
behind `q` has its distinguishable port `rport v q = i` pointing to `v`, and `q = j`. -/
theorem edge_mem_M_iff {G : PNGraph V} (hG : G.IsSimple) {v : V} {q : ℕ} (hq : q < G.deg v)
    {i j : ℕ} :
    G.edge v q ∈ M G i j ↔
      (G.dn v = some q ∧ q = i ∧ G.rport v q = j) ∨
        (G.dn (G.nbr v q) = some (G.rport v q) ∧ G.rport v q = i ∧ q = j) := by
  constructor
  · intro h
    obtain ⟨w, hw, hwj, he⟩ := mem_M.1 h
    obtain ⟨hiw, -⟩ := G.dn_spec hw
    by_cases hvw : w = v
    · subst hvw
      have : i = q := by
        have h' : s(w, G.nbr w i) = s(w, G.nbr w q) := he
        rw [Sym2.congr_right] at h'
        exact hG.2 w i q hiw hq h'
      subst this
      exact Or.inl ⟨hw, rfl, hwj⟩
    · have h' : s(w, G.nbr w i) = s(v, G.nbr v q) := he
      rcases Sym2.eq_iff.1 h' with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact absurd h1 hvw
      · -- `w = nbr v q` and `nbr w i = v`
        have hr : G.rport v q = i := by
          have e1 : G.nbr w (G.rport v q) = v := by rw [h1]; exact G.nbr_nbr hq
          have hr' : G.rport v q < G.deg w := by rw [h1]; exact G.rport_lt hq
          exact hG.2 w _ _ hr' hiw (e1.trans h2.symm)
        refine Or.inr ⟨by rw [← h1, hr]; exact hw, hr, ?_⟩
        rw [← hwj, ← hr, h1]
        exact (G.rport_rport hq).symm
  · rintro (⟨hdn, rfl, rfl⟩ | ⟨hdn, rfl, rfl⟩)
    · exact edge_dn_mem_M hdn
    · have := edge_dn_mem_M hdn
      rwa [G.rport_rport hq, G.edge_nbr hq] at this

end Podc.EdgeDominatingSets
