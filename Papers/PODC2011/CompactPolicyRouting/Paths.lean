import Papers.PODC2011.CompactPolicyRouting.Algebra

/-!
# Path weights and preferred paths (Section 4.2.1)

A weighted graph is a `SimpleGraph V` with edge weights `wt : Sym2 V → W`. The weight of a walk is the
`⊕`-composition of its edge weights, computed in the extended weights `A.Ext` (the empty walk has weight `1`).
A preferred `s – t` path is a path of minimum weight among all `s – t` paths; `pw A wt s t` is its weight
(the *preferred weight*; `φ` if `t` is unreachable).
-/

namespace Podc.CompactPolicyRouting

open SimpleGraph RoutingAlgebra

universe u v

variable {W : Type u} [LinearOrder W] (A : RoutingAlgebra W) {V : Type v} {G : SimpleGraph V}
  (wt : Sym2 V → W)

/-- The weight `w(p) = ⊕_{e ∈ p} w(e)` of a walk (`1` for the empty walk). -/
def weight {s t : V} (p : G.Walk s t) : A.Ext := (p.edges.map fun e => A.emb (wt e)).prod

/-- A preferred `s – t` path: a path whose weight is `⪯` the weight of every `s – t` path. -/
def IsPreferred {s t : V} (p : G.Walk s t) : Prop :=
  p.IsPath ∧ ∀ q : G.Walk s t, q.IsPath → weight A wt p ≤ weight A wt q

variable {A wt}

@[simp] theorem weight_nil {s : V} : weight A wt (Walk.nil : G.Walk s s) = 1 := rfl

@[simp] theorem weight_cons {s x t : V} (h : G.Adj s x) (p : G.Walk x t) :
    weight A wt (Walk.cons h p) = A.emb (wt s(s, x)) * weight A wt p := by
  simp [weight]

theorem weight_append {s x t : V} (p : G.Walk s x) (q : G.Walk x t) :
    weight A wt (p.append q) = weight A wt p * weight A wt q := by
  simp [weight, Walk.edges_append]

theorem weight_eq_multiset_prod {s t : V} (p : G.Walk s t) :
    weight A wt p = ((p.edges : Multiset (Sym2 V)).map fun e => A.emb (wt e)).prod := by
  simp [weight]

theorem weight_reverse {s t : V} (p : G.Walk s t) : weight A wt p.reverse = weight A wt p := by
  rw [weight_eq_multiset_prod, weight_eq_multiset_prod, Walk.edges_reverse]
  simp

theorem weight_mapLe {H : SimpleGraph V} (hGH : G ≤ H) {s t : V} (p : G.Walk s t) :
    weight A wt (p.mapLe hGH) = weight A wt p := by
  simp [weight, Walk.mapLe, Walk.edges_map]

theorem weight_eq_of_edges_eq {H : SimpleGraph V} {s t s' t' : V} (p : G.Walk s t) (q : H.Walk s' t')
    (h : p.edges = q.edges) : weight A wt p = weight A wt q := by
  simp [weight, h]

/-- Under monotonicity, a sub-multiset of edges weighs at most as much. -/
theorem weight_le_of_le (hM : A.IsMonotone) {H : SimpleGraph V} {s t s' t' : V} (p : G.Walk s t)
    (q : H.Walk s' t') (h : (p.edges : Multiset (Sym2 V)) ≤ q.edges) :
    weight A wt p ≤ weight A wt q := by
  rw [weight_eq_multiset_prod, weight_eq_multiset_prod]
  obtain ⟨r, hr⟩ := Multiset.le_iff_exists_add.1 h
  rw [hr, Multiset.map_add, Multiset.prod_add]
  exact hM.le_mul' _ _

/-- Under monotonicity, a path whose edges are among the edges of a walk weighs at most as much. -/
theorem weight_le_of_subset (hM : A.IsMonotone) {H : SimpleGraph V} {s t s' t' : V} (p : G.Walk s t)
    (hp : p.IsPath) (q : H.Walk s' t') (h : p.edges ⊆ q.edges) : weight A wt p ≤ weight A wt q :=
  weight_le_of_le hM p q ((Multiset.le_iff_subset (by simpa using hp.edges_nodup)).2 h)

theorem weight_bypass_le [DecidableEq V] (hM : A.IsMonotone) {s t : V} (p : G.Walk s t) :
    weight A wt p.bypass ≤ weight A wt p :=
  weight_le_of_subset hM _ p.bypass_isPath p p.edges_bypass_subset_edges

/-- Preferred paths exist between reachable nodes (finite graphs). -/
theorem exists_isPreferred [Finite V] {s t : V} (h : G.Reachable s t) :
    ∃ p : G.Walk s t, IsPreferred A wt p := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have : Nonempty (G.Path s t) := by
    obtain ⟨p⟩ := h
    exact ⟨⟨p.bypass, p.bypass_isPath⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_min (fun p : G.Path s t => weight A wt p.1)
  exact ⟨p.1, p.2, fun q hq => hp ⟨q, hq⟩⟩

open Classical in
/-- The preferred weight `w(p*_{st})` (`φ` if `t` is unreachable from `s`). -/
noncomputable def pw {V : Type v} [Finite V] (A : RoutingAlgebra W) (wt : Sym2 V → W)
    (G : SimpleGraph V) (s t : V) : A.Ext :=
  if h : G.Reachable s t then weight A wt (exists_isPreferred (A := A) (wt := wt) h).choose
  else A.emb A.phi

section pw

variable [Finite V]

theorem IsPreferred.weight_eq {s t : V} {p : G.Walk s t} (hp : IsPreferred A wt p) :
    weight A wt p = pw A wt G s t := by
  have hr : G.Reachable s t := ⟨p⟩
  classical
  rw [pw, dif_pos hr]
  have hc := (exists_isPreferred (A := A) (wt := wt) hr).choose_spec
  exact le_antisymm (hp.2 _ hc.1) (hc.2 _ hp.1)

theorem pw_le_weight_of_isPath {s t : V} (q : G.Walk s t) (hq : q.IsPath) :
    pw A wt G s t ≤ weight A wt q := by
  obtain ⟨p, hp⟩ := exists_isPreferred (A := A) (wt := wt) (⟨q⟩ : G.Reachable s t)
  rw [← hp.weight_eq]; exact hp.2 q hq

theorem exists_isPreferred_weight {s t : V} (h : G.Reachable s t) :
    ∃ p : G.Walk s t, IsPreferred A wt p ∧ weight A wt p = pw A wt G s t := by
  obtain ⟨p, hp⟩ := exists_isPreferred (A := A) (wt := wt) h
  exact ⟨p, hp, hp.weight_eq⟩

theorem isPreferred_iff {s t : V} (p : G.Walk s t) :
    IsPreferred A wt p ↔ p.IsPath ∧ weight A wt p = pw A wt G s t := by
  refine ⟨fun hp => ⟨hp.1, hp.weight_eq⟩, fun ⟨hp, he⟩ => ⟨hp, fun q hq => ?_⟩⟩
  rw [he]; exact pw_le_weight_of_isPath q hq

/-- Under monotonicity, every walk weighs at least the preferred weight. -/
theorem pw_le_weight (hM : A.IsMonotone) {s t : V} (q : G.Walk s t) :
    pw A wt G s t ≤ weight A wt q := by
  classical
  exact (pw_le_weight_of_isPath _ q.bypass_isPath).trans (weight_bypass_le hM q)

@[simp] theorem pw_self (s : V) : pw A wt G s s = 1 := by
  have : IsPreferred A wt (Walk.nil : G.Walk s s) :=
    ⟨Walk.IsPath.nil, fun q _ => by rw [weight_nil]; exact one_le _⟩
  rw [← this.weight_eq, weight_nil]

theorem pw_comm (s t : V) : pw A wt G s t = pw A wt G t s := by
  by_cases h : G.Reachable s t
  · obtain ⟨p, hp, hpw⟩ := exists_isPreferred_weight (A := A) (wt := wt) h
    obtain ⟨q, hq, hqw⟩ := exists_isPreferred_weight (A := A) (wt := wt) h.symm
    rw [← hpw, ← hqw]
    apply le_antisymm
    · rw [← weight_reverse q]; exact hp.2 _ hq.1.reverse
    · rw [← weight_reverse p]; exact hq.2 _ hp.1.reverse
  · have h' : ¬ G.Reachable t s := fun h' => h h'.symm
    classical
    rw [pw, pw, dif_neg h, dif_neg h']

/-- The triangle inequality `w(p*_{uv}) ⪯ w(p*_{ux}) ⊕ w(p*_{xv})` (needs monotonicity, since the
concatenation of two paths is only a walk). -/
theorem pw_triangle (hM : A.IsMonotone) {u x v : V} (h₁ : G.Reachable u x) (h₂ : G.Reachable x v) :
    pw A wt G u v ≤ pw A wt G u x * pw A wt G x v := by
  obtain ⟨p, -, hp⟩ := exists_isPreferred_weight (A := A) (wt := wt) h₁
  obtain ⟨q, -, hq⟩ := exists_isPreferred_weight (A := A) (wt := wt) h₂
  rw [← hp, ← hq, ← weight_append]
  exact pw_le_weight hM _

theorem pw_le_emb_phi (s t : V) : pw A wt G s t ≤ A.emb A.phi := le_emb_phi _

/-- Preferred weights between distinct nodes are genuine weights. -/
theorem pw_ne_one {s t : V} (hst : s ≠ t) : pw A wt G s t ≠ 1 := by
  by_cases h : G.Reachable s t
  · obtain ⟨p, -, hp⟩ := exists_isPreferred_weight (A := A) (wt := wt) h
    rw [← hp]
    cases p with
    | nil => exact absurd rfl hst
    | cons h q =>
      rw [weight_cons]; exact emb_mul_ne_one _ _
  · classical
    rw [pw, dif_neg h]; exact emb_ne_one _

variable (A wt) in
/-- Definition 4.13 (for one path): a walk `p` from `s` to `t` is within stretch `k` if
`w(p) ⪯ (w(p*_{st}))^k`, where `x^k = x ⊕ ⋯ ⊕ x` (`k` times). -/
def IsWithinStretch (k : ℕ) {s t : V} (p : G.Walk s t) : Prop :=
  weight A wt p ≤ pw A wt G s t ^ k

end pw

end Podc.CompactPolicyRouting
