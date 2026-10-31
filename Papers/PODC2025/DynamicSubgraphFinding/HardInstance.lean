import Papers.PODC2025.DynamicSubgraphFinding.Model

/-!
# The hard instances of Section 4.1

Parameters: `q = s - 2 ≥ 1`, `t` cliques `K^i` (`K i k`, `i : Fin t`, `k : Fin q`) and the
independent set `I` (all other identifiers). `create(x, K^i, y)` adds the edges `x – K i k` in
rounds `ct q i 0 k = 2qi + k + 1` and `y – K i k` in rounds `ct q i 1 k = 2qi + q + k + 1`, i.e.
inside the paper's interval `[2(s-2)(i-1)+1, 2(s-2)i]` (0-based `i` here). After the last
interval, in round `T = 2qt + 1` (`t_final`), the "final" edges are inserted.

A scenario is a `Spec`: at most one creation per index `i` (`cr i`), the final edges `fin`, and
whether all nodes are present from the start (`full`, the edge-insertion model) or a node of `I`
appears with its first edge (the node-insertion model: "nodes in `I` without incident edges are
considered as not yet inserted").
-/

namespace Podc.DynamicSubgraphFinding

open Classical

namespace Hard

variable {V : Type} {q t : ℕ} (K : Fin t → Fin q → V)

/-- `v` belongs to one of the cliques. -/
def IsK (v : V) : Prop := ∃ i k, K i k = v

/-- Round in which the `k`-th edge of side `e` of `create(·, K^i, ·)` is inserted. -/
def ct (q i e k : ℕ) : ℕ := 2 * q * i + q * e + k + 1

/-- A hard scenario. -/
structure Spec (V : Type) (t : ℕ) where
  cr : Fin t → Option (V × V)
  fin : V → V → Prop
  full : Prop

variable {K}

/-- The (directed) edge relation of a scenario in round `r`. -/
def Rel (K : Fin t → Fin q → V) (sp : Spec V t) (r : ℕ) (u v : V) : Prop :=
  (∃ i k k', k ≠ k' ∧ u = K i k ∧ v = K i k') ∨
  (∃ i x y k, sp.cr i = some (x, y) ∧ v = K i k ∧
      ((u = x ∧ ct q i 0 k ≤ r) ∨ (u = y ∧ ct q i 1 k ≤ r))) ∨
  (2 * q * t + 1 ≤ r ∧ sp.fin u v)

lemma Rel.mono {sp : Spec V t} {r r' : ℕ} (h : r ≤ r') {u v : V} (huv : Rel K sp r u v) :
    Rel K sp r' u v := by
  rcases huv with h1 | ⟨i, x, y, k, hc, hv, hu⟩ | ⟨hT, hf⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨i, x, y, k, hc, hv, ?_⟩)
    rcases hu with ⟨hu, hr⟩ | ⟨hu, hr⟩
    · exact Or.inl ⟨hu, by omega⟩
    · exact Or.inr ⟨hu, by omega⟩
  · exact Or.inr (Or.inr ⟨by omega, hf⟩)

/-- Adjacency of a scenario. -/
def Adj (K : Fin t → Fin q → V) (sp : Spec V t) (r : ℕ) (u v : V) : Prop :=
  u ≠ v ∧ (Rel K sp r u v ∨ Rel K sp r v u)

/-- The dynamic network of a scenario. -/
def net (K : Fin t → Fin q → V) (sp : Spec V t) : InsNet V where
  pres r v := sp.full ∨ IsK K v ∨ ∃ u, Adj K sp r u v
  adj := Adj K sp
  symm := fun _ _ _ ⟨h1, h2⟩ => ⟨Ne.symm h1, h2.symm⟩
  irrefl := fun _ _ h => h.1 rfl
  pres_of_adj := fun _ u v h => Or.inr (Or.inr ⟨v, Ne.symm h.1, h.2.symm⟩)
  pres_mono := by
    rintro r v (h | h | ⟨u, hne, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨u, hne, ?_⟩)
      rcases h with h | h
      · exact Or.inl (h.mono (Nat.le_succ r))
      · exact Or.inr (h.mono (Nat.le_succ r))
  adj_mono := by
    rintro r u v ⟨hne, h | h⟩
    · exact ⟨hne, Or.inl (h.mono (Nat.le_succ r))⟩
    · exact ⟨hne, Or.inr (h.mono (Nat.le_succ r))⟩

/-! ### Arithmetic of the creation rounds -/

lemma ct_le {i e k : ℕ} (hi : i < t) (he : e ≤ 1) (hk : k < q) : ct q i e k ≤ 2 * q * t := by
  unfold ct
  have h1 : 2 * q * i + 2 * q ≤ 2 * q * t := by
    have := Nat.mul_le_mul_left (2 * q) (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at this; exact this
  have h2 : q * e ≤ q := by simpa using Nat.mul_le_mul_left q he
  omega

lemma ct_pos (i e k : ℕ) : 1 ≤ ct q i e k := by unfold ct; omega

lemma ct_inj {i e k i' e' k' : ℕ} (he : e ≤ 1) (hk : k < q) (he' : e' ≤ 1) (hk' : k' < q)
    (h : ct q i e k = ct q i' e' k') : i = i' ∧ e = e' ∧ k = k' := by
  unfold ct at h
  have hq : 0 < q := by omega
  have hr1 : q * e + k < 2 * q := by
    have : q * e ≤ q := by simpa using Nat.mul_le_mul_left q he
    omega
  have hr2 : q * e' + k' < 2 * q := by
    have : q * e' ≤ q := by simpa using Nat.mul_le_mul_left q he'
    omega
  have h' : (q * e + k) + 2 * q * i = (q * e' + k') + 2 * q * i' := by omega
  have hd : ((q * e + k) + 2 * q * i) / (2 * q) = ((q * e' + k') + 2 * q * i') / (2 * q) := by
    rw [h']
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt hr1, Nat.div_eq_of_lt hr2] at hd
  simp only [Nat.zero_add] at hd; subst hd
  have h2 : q * e + k = q * e' + k' := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he' with rfl | rfl <;> simp at h2 ⊢ <;> omega


/-! ### Well-formed scenarios -/

/-- The cliques are disjoint and of size `q`. -/
def KInj (K : Fin t → Fin q → V) : Prop := ∀ i k i' k', K i k = K i' k' → i = i' ∧ k = k'

/-- Well-formed scenario: creation endpoints are distinct nodes of `I`, different creations use
disjoint endpoints, and the final edges join nodes of `I`. -/
structure WF (K : Fin t → Fin q → V) (sp : Spec V t) : Prop where
  cr_I : ∀ i x y, sp.cr i = some (x, y) → ¬ IsK K x ∧ ¬ IsK K y ∧ x ≠ y
  cr_disj : ∀ i j x y x' y', i ≠ j → sp.cr i = some (x, y) → sp.cr j = some (x', y') →
    x ≠ x' ∧ x ≠ y' ∧ y ≠ x' ∧ y ≠ y'
  fin_I : ∀ u v, sp.fin u v → ¬ IsK K u ∧ ¬ IsK K v

variable {sp sp' : Spec V t}

lemma adj_K_iff (hK : KInj K) (hw : WF K sp) (r : ℕ) (u : V) (i : Fin t) (k : Fin q) :
    (net K sp).adj r u (K i k) ↔ (∃ k', k' ≠ k ∧ u = K i k') ∨
      ∃ x y, sp.cr i = some (x, y) ∧ ((u = x ∧ ct q i 0 k ≤ r) ∨ (u = y ∧ ct q i 1 k ≤ r)) := by
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨i', k1, k2, hk, rfl, he⟩ | ⟨i', x, y, k', hc, he, hu⟩ | ⟨_, hf⟩
      · obtain ⟨rfl, rfl⟩ := hK _ _ _ _ he
        exact Or.inl ⟨k1, hk, rfl⟩
      · obtain ⟨rfl, rfl⟩ := hK _ _ _ _ he
        exact Or.inr ⟨x, y, hc, hu⟩
      · exact absurd ⟨i, k, rfl⟩ (hw.fin_I _ _ hf).2
    · rcases h with ⟨i', k1, k2, hk, he, rfl⟩ | ⟨i', x, y, k', hc, rfl, hu⟩ | ⟨_, hf⟩
      · obtain ⟨rfl, rfl⟩ := hK _ _ _ _ he
        exact Or.inl ⟨k2, Ne.symm hk, rfl⟩
      · exfalso
        obtain ⟨hx, hy, -⟩ := hw.cr_I _ _ _ hc
        rcases hu with ⟨hu, -⟩ | ⟨hu, -⟩
        · exact hx ⟨i, k, hu⟩
        · exact hy ⟨i, k, hu⟩
      · exact absurd ⟨i, k, rfl⟩ (hw.fin_I _ _ hf).1
  · rintro (⟨k', hk, rfl⟩ | ⟨x, y, hc, hu⟩)
    · refine ⟨fun h => hk (hK _ _ _ _ h).2, Or.inl (Or.inl ⟨i, k', k, hk, rfl, rfl⟩)⟩
    · obtain ⟨hx, hy, -⟩ := hw.cr_I _ _ _ hc
      refine ⟨?_, Or.inl (Or.inr (Or.inl ⟨i, x, y, k, hc, rfl, hu⟩))⟩
      rintro rfl
      rcases hu with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hx ⟨i, k, rfl⟩
      · exact hy ⟨i, k, rfl⟩

lemma adj_I_iff (r : ℕ) (u v : V) (hv : ¬ IsK K v) :
    (net K sp).adj r u v ↔
      (∃ i x y k, sp.cr i = some (x, y) ∧ u = K i k ∧
        ((v = x ∧ ct q i 0 k ≤ r) ∨ (v = y ∧ ct q i 1 k ≤ r))) ∨
      (u ≠ v ∧ 2 * q * t + 1 ≤ r ∧ (sp.fin u v ∨ sp.fin v u)) := by
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨i', k1, k2, -, -, rfl⟩ | ⟨i', x, y, k', hc, rfl, hu⟩ | ⟨hr, hf⟩
      · exact absurd ⟨i', k2, rfl⟩ hv
      · exact absurd ⟨i', k', rfl⟩ hv
      · exact Or.inr ⟨hne, hr, Or.inl hf⟩
    · rcases h with ⟨i', k1, k2, -, rfl, -⟩ | ⟨i', x, y, k', hc, rfl, hu⟩ | ⟨hr, hf⟩
      · exact absurd ⟨i', k1, rfl⟩ hv
      · exact Or.inl ⟨i', x, y, k', hc, rfl, hu⟩
      · exact Or.inr ⟨hne, hr, Or.inr hf⟩
  · rintro (⟨i, x, y, k, hc, rfl, hu⟩ | ⟨hne, hr, hf | hf⟩)
    · refine ⟨fun h => hv ⟨i, k, h⟩, Or.inr (Or.inr (Or.inl ⟨i, x, y, k, hc, rfl, hu⟩))⟩
    · exact ⟨hne, Or.inl (Or.inr (Or.inr ⟨hr, hf⟩))⟩
    · exact ⟨hne, Or.inr (Or.inr (Or.inr ⟨hr, hf⟩))⟩

/-- All well-formed scenarios with the same `full` flag have the same `G⁰`. -/
lemma g0_eq (hK : KInj K) (hw : WF K sp) (hw' : WF K sp') (hf : sp.full ↔ sp'.full) :
    (net K sp).pres 0 = (net K sp').pres 0 ∧ (net K sp).adj 0 = (net K sp').adj 0 := by
  have hadj : ∀ u v, (net K sp).adj 0 u v ↔ (net K sp').adj 0 u v := by
    intro u v
    by_cases hv : IsK K v
    · obtain ⟨i, k, rfl⟩ := hv
      rw [adj_K_iff hK hw, adj_K_iff hK hw']
      have h1 := ct_pos (q := q) i 0 k
      have h2 := ct_pos (q := q) i 1 k
      constructor <;> rintro (h | ⟨x, y, -, h | h⟩) <;> first | exact Or.inl h | omega
    · rw [adj_I_iff _ _ _ hv, adj_I_iff _ _ _ hv]
      constructor <;> rintro (⟨i, x, y, k, -, -, h | h⟩ | ⟨-, h, -⟩) <;>
        first | (have := ct_pos (q := q) i 0 k; have := ct_pos (q := q) i 1 k; omega) | omega
  have hadj' : (net K sp).adj 0 = (net K sp').adj 0 := by
    funext u v; exact propext (hadj u v)
  refine ⟨?_, hadj'⟩
  funext v
  show (sp.full ∨ IsK K v ∨ ∃ u, (net K sp).adj 0 u v) = (sp'.full ∨ IsK K v ∨ ∃ u, (net K sp').adj 0 u v)
  rw [hadj']
  exact propext (by rw [hf])

/-! ### Components -/

/-- The component of `create(x, K^i, y)`. -/
def Comp (K : Fin t → Fin q → V) (i : Fin t) (x y : V) (v : V) : Prop :=
  v = x ∨ v = y ∨ ∃ k, v = K i k

/-- Before round `T`, a creation is an isolated component whose evolution depends only on the
creation itself. -/
lemma comp_adj (hK : KInj K) (hw : WF K sp) (hw' : WF K sp') {i : Fin t} {x y : V}
    (hc : sp.cr i = some (x, y)) (hc' : sp'.cr i = some (x, y)) {r : ℕ} (hr : r ≤ 2 * q * t)
    (u v : V) (hv : Comp K i x y v) :
    ((net K sp).adj r u v ↔ (net K sp').adj r u v) ∧ ((net K sp).adj r u v → Comp K i x y u) := by
  rcases hv with rfl | rfl | ⟨k, rfl⟩
  · obtain ⟨hx, -, -⟩ := hw.cr_I _ _ _ hc
    have key : ∀ (s : Spec V t), WF K s → s.cr i = some (v, y) →
        ((net K s).adj r u v ↔ ∃ k, u = K i k ∧ ct q i 0 k ≤ r) := by
      intro s hs hcs
      rw [adj_I_iff _ _ _ hx]
      constructor
      · rintro (⟨j, x', y', k, hc2, rfl, h⟩ | ⟨-, h, -⟩)
        · by_cases hij : j = i
          · subst hij
            rw [hcs] at hc2
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc2)
            rcases h with ⟨-, h⟩ | ⟨h1, -⟩
            · exact ⟨k, rfl, h⟩
            · exact absurd h1 (hs.cr_I _ _ _ hcs).2.2
          · have := hs.cr_disj _ _ _ _ _ _ (Ne.symm hij) hcs hc2
            rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact absurd h1 this.1
            · exact absurd h1 this.2.1
        · omega
      · rintro ⟨k, rfl, h⟩
        exact Or.inl ⟨i, v, y, k, hcs, rfl, Or.inl ⟨rfl, h⟩⟩
    rw [key sp hw hc, key sp' hw' hc']
    exact ⟨Iff.rfl, fun ⟨k, h, _⟩ => Or.inr (Or.inr ⟨k, h⟩)⟩
  · obtain ⟨-, hy, hne⟩ := hw.cr_I _ _ _ hc
    have key : ∀ (s : Spec V t), WF K s → s.cr i = some (x, v) →
        ((net K s).adj r u v ↔ ∃ k, u = K i k ∧ ct q i 1 k ≤ r) := by
      intro s hs hcs
      rw [adj_I_iff _ _ _ hy]
      constructor
      · rintro (⟨j, x', y', k, hc2, rfl, h⟩ | ⟨-, h, -⟩)
        · by_cases hij : j = i
          · subst hij
            rw [hcs] at hc2
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc2)
            rcases h with ⟨h1, -⟩ | ⟨-, h⟩
            · exact absurd h1.symm (hs.cr_I _ _ _ hcs).2.2
            · exact ⟨k, rfl, h⟩
          · have := hs.cr_disj _ _ _ _ _ _ (Ne.symm hij) hcs hc2
            rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact absurd h1 this.2.2.1
            · exact absurd h1 this.2.2.2
        · omega
      · rintro ⟨k, rfl, h⟩
        exact Or.inl ⟨i, x, v, k, hcs, rfl, Or.inr ⟨rfl, h⟩⟩
    rw [key sp hw hc, key sp' hw' hc']
    exact ⟨Iff.rfl, fun ⟨k, h, _⟩ => Or.inr (Or.inr ⟨k, h⟩)⟩
  · rw [adj_K_iff hK hw, adj_K_iff hK hw', hc, hc']
    refine ⟨Iff.rfl, ?_⟩
    rintro (⟨k', -, rfl⟩ | ⟨x', y', he, h | h⟩)
    · exact Or.inr (Or.inr ⟨k', rfl⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact Or.inl h.1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact Or.inr (Or.inl h.1)

/-- Clique nodes see the same neighbourhood in every round (also after `T`). -/
lemma K_adj (hK : KInj K) (hw : WF K sp) (hw' : WF K sp') {i : Fin t} {x y : V}
    (hc : sp.cr i = some (x, y)) (hc' : sp'.cr i = some (x, y)) (r : ℕ) (u : V) (k : Fin q) :
    (net K sp).adj r u (K i k) ↔ (net K sp').adj r u (K i k) := by
  rw [adj_K_iff hK hw, adj_K_iff hK hw', hc, hc']

lemma loc_eq_of_adj {sp sp' : Spec V t} (hf : sp.full ↔ sp'.full) (r : ℕ) (v : V)
    (h : ∀ u, (net K sp).adj r u v ↔ (net K sp').adj r u v) :
    (net K sp).loc r v = (net K sp').loc r v := by
  have hs : {u | (net K sp).adj r u v} = {u | (net K sp').adj r u v} := Set.ext h
  have hp : (net K sp).pres r v ↔ (net K sp').pres r v := by
    show (sp.full ∨ IsK K v ∨ ∃ u, (net K sp).adj r u v) ↔ (sp'.full ∨ IsK K v ∨ ∃ u, (net K sp').adj r u v)
    simp only [hf, h]
  unfold InsNet.loc
  by_cases h1 : (net K sp).pres r v
  · rw [ite_eq_left h1, ite_eq_left (hp.1 h1), hs]
  · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (hp.2 h2))]

section Exec

variable {M O : Type} (A : Algorithm V M O)

/-- **States of a creation component.** Up to round `T - 1 = 2qt`, the nodes of a creation
`create(x, K^i, y)` are in the same states in all well-formed scenarios containing it. -/
lemma comp_state (hK : KInj K) (hw : WF K sp) (hw' : WF K sp') (hf : sp.full ↔ sp'.full)
    {i : Fin t} {x y : V} (hc : sp.cr i = some (x, y)) (hc' : sp'.cr i = some (x, y))
    {r : ℕ} (hr : r ≤ 2 * q * t) (v : V) (hv : Comp K i x y v) :
    A.state (net K sp) r v = A.state (net K sp') r v :=
  A.state_eq_of_closed (g0_eq hK hw hw' hf) (Comp K i x y) (2 * q * t)
    (fun k hk v hv => loc_eq_of_adj hf k v (fun u => (comp_adj hK hw hw' hc hc' hk u v hv).1))
    (fun k hk u v hv => (comp_adj hK hw hw' hc hc' hk u v hv).1)
    (fun k hk u v hv => (comp_adj hK hw hw' hc hc' hk u v hv).2) r hr v hv

/-- **Messages of clique nodes in round `T`.** -/
lemma K_send_T (hK : KInj K) (hw : WF K sp) (hw' : WF K sp') (hf : sp.full ↔ sp'.full)
    {i : Fin t} {x y : V} (hc : sp.cr i = some (x, y)) (hc' : sp'.cr i = some (x, y))
    (k : Fin q) (w : V) :
    A.send (2 * q * t + 1) (A.state (net K sp) (2 * q * t) (K i k)) ((net K sp).loc (2 * q * t + 1) (K i k)) w =
      A.send (2 * q * t + 1) (A.state (net K sp') (2 * q * t) (K i k))
        ((net K sp').loc (2 * q * t + 1) (K i k)) w := by
  rw [comp_state A hK hw hw' hf hc hc' le_rfl _ (Or.inr (Or.inr ⟨k, rfl⟩)),
    loc_eq_of_adj hf _ _ (fun u => K_adj hK hw hw' hc hc' _ u k)]

end Exec


/-! ### Validity: one change per round -/

lemma newEdge_cases (hK : KInj K) (hw : WF K sp) {r : ℕ} {u v : V}
    (h : (net K sp).NewEdge r u v) :
    (∃ (i : Fin t) (x y : V) (k : Fin q) (e : ℕ), sp.cr i = some (x, y) ∧ e ≤ 1 ∧ ct q i e k = r + 1 ∧
      s(u, v) = s(if e = 0 then x else y, K i k)) ∨
    (r + 1 = 2 * q * t + 1 ∧ (sp.fin u v ∨ sp.fin v u)) := by
  obtain ⟨h1, h2⟩ := h
  by_cases hv : IsK K v
  · obtain ⟨i, k, rfl⟩ := hv
    rw [adj_K_iff hK hw] at h1 h2
    rcases h1 with h1 | ⟨x, y, hc, hu⟩
    · exact absurd (Or.inl h1) h2
    · left
      rcases hu with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
      · refine ⟨i, u, y, k, 0, hc, by omega, ?_, by simp⟩
        by_contra hne
        exact h2 (Or.inr ⟨u, y, hc, Or.inl ⟨rfl, by omega⟩⟩)
      · refine ⟨i, x, u, k, 1, hc, le_rfl, ?_, by simp⟩
        by_contra hne
        exact h2 (Or.inr ⟨x, u, hc, Or.inr ⟨rfl, by omega⟩⟩)
  · by_cases hu : IsK K u
    · obtain ⟨i, k, rfl⟩ := hu
      have h1' := (net K sp).symm _ _ _ h1
      have h2' : ¬ (net K sp).adj r v (K i k) := fun h => h2 ((net K sp).symm _ _ _ h)
      rw [adj_K_iff hK hw] at h1' h2'
      rcases h1' with h1' | ⟨x, y, hc, hu⟩
      · exact absurd (Or.inl h1') h2'
      · left
        rcases hu with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
        · refine ⟨i, v, y, k, 0, hc, by omega, ?_, by simp [Sym2.eq_swap]⟩
          by_contra hne
          exact h2' (Or.inr ⟨v, y, hc, Or.inl ⟨rfl, by omega⟩⟩)
        · refine ⟨i, x, v, k, 1, hc, le_rfl, ?_, by simp [Sym2.eq_swap]⟩
          by_contra hne
          exact h2' (Or.inr ⟨x, v, hc, Or.inr ⟨rfl, by omega⟩⟩)
    · rw [adj_I_iff _ _ _ hv] at h1 h2
      rcases h1 with ⟨i, x, y, k, -, rfl, -⟩ | ⟨hne, hr, hf⟩
      · exact absurd ⟨i, k, rfl⟩ hu
      · right
        refine ⟨?_, hf⟩
        by_contra hne'
        exact h2 (Or.inr ⟨hne, by omega, hf⟩)

/-- Before and after round `T`, at most one edge is inserted per round. -/
lemma newEdge_unique_ne_T (hK : KInj K) (hw : WF K sp) {r : ℕ} (hr : r + 1 ≠ 2 * q * t + 1)
    {u v u' v' : V} (h : (net K sp).NewEdge r u v) (h' : (net K sp).NewEdge r u' v') :
    s(u, v) = s(u', v') := by
  rcases newEdge_cases hK hw h with ⟨i, x, y, k, e, hc, he, hct, hs⟩ | ⟨h1, -⟩
  · rcases newEdge_cases hK hw h' with ⟨i', x', y', k', e', hc', he', hct', hs'⟩ | ⟨h1, -⟩
    · obtain ⟨h1, h2, h3⟩ := ct_inj he k.2 he' k'.2 (hct.trans hct'.symm)
      have hi : i = i' := Fin.ext h1
      have hk : k = k' := Fin.ext h3
      subst hi hk h2
      rw [hc] at hc'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc')
      rw [hs, hs']
    · exact absurd h1 hr
  · exact absurd h1 hr

/-- A node that becomes present gets a new edge. -/
lemma newEdge_of_newPres {r : ℕ} {z : V} (h1 : (net K sp).pres (r + 1) z)
    (h2 : ¬ (net K sp).pres r z) : ∃ u, (net K sp).NewEdge r u z := by
  rcases h1 with h | h | ⟨u, hu⟩
  · exact absurd (Or.inl h) h2
  · exact absurd (Or.inr (Or.inl h)) h2
  · exact ⟨u, hu, fun h => h2 (Or.inr (Or.inr ⟨u, h⟩))⟩

lemma newEdge_K_mem (hK : KInj K) (hw : WF K sp) {r : ℕ} {u v : V}
    (h : (net K sp).NewEdge r u v) (hr : r + 1 ≠ 2 * q * t + 1) : IsK K u ∨ IsK K v := by
  rcases newEdge_cases hK hw h with ⟨i, x, y, k, e, hc, he, hct, hs⟩ | ⟨h1, -⟩
  · rcases Sym2.eq_iff.mp hs with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact Or.inr ⟨i, k, rfl⟩
    · exact Or.inl ⟨i, k, rfl⟩
  · exact absurd h1 hr

/-- How the final round `T` changes the network. -/
def FinStep (K : Fin t → Fin q → V) (sp : Spec V t) : Prop :=
  (∃ a b, (∀ u v, sp.fin u v → u = a ∧ v = b) ∧
      (net K sp).pres (2 * q * t) a ∧ (net K sp).pres (2 * q * t) b) ∨
  (∃ c, ¬ (net K sp).pres (2 * q * t) c ∧
      ∀ u v, sp.fin u v → (u = c ∧ (net K sp).pres (2 * q * t) v) ∨
        (v = c ∧ (net K sp).pres (2 * q * t) u))

lemma pres_K {r : ℕ} {v : V} (hv : IsK K v) : (net K sp).pres r v := Or.inr (Or.inl hv)

/-- Validity in the node-and-edge-insertion model. -/
lemma nodeEdgeIns (hK : KInj K) (hw : WF K sp) (hfs : FinStep K sp) :
    (net K sp).NodeEdgeIns := by
  intro r
  by_cases hr : r + 1 = 2 * q * t + 1
  · have hr' : r = 2 * q * t := by omega
    subst hr'
    rcases hfs with ⟨a, b, hab, ha, hb⟩ | ⟨c, hc, hfc⟩
    · left
      refine ⟨fun z h1 => ?_, fun u v u' v' h h' => ?_⟩
      · by_contra h2
        obtain ⟨u, hu⟩ := newEdge_of_newPres h1 h2
        rcases newEdge_cases hK hw hu with ⟨i, x, y, k, e, -, he, hct, -⟩ | ⟨-, hf | hf⟩
        · have := ct_le i.2 he k.2 (q := q); omega
        · exact h2 (by rw [(hab _ _ hf).2]; exact hb)
        · exact h2 (by rw [(hab _ _ hf).1]; exact ha)
      · have key : ∀ u v, (net K sp).NewEdge (2 * q * t) u v → s(u, v) = s(a, b) := by
          intro u v h
          rcases newEdge_cases hK hw h with ⟨i, x, y, k, e, -, he, hct, -⟩ | ⟨-, hf | hf⟩
          · have := ct_le i.2 he k.2 (q := q); omega
          · obtain ⟨rfl, rfl⟩ := hab _ _ hf; rfl
          · obtain ⟨rfl, rfl⟩ := hab _ _ hf; exact Sym2.eq_swap
        rw [key _ _ h, key _ _ h']
    · right
      refine ⟨c, hc, fun z h1 => ?_, fun u v h => ?_⟩
      · by_cases h2 : (net K sp).pres (2 * q * t) z
        · exact Or.inl h2
        · right
          obtain ⟨u, hu⟩ := newEdge_of_newPres h1 h2
          rcases newEdge_cases hK hw hu with ⟨i, x, y, k, e, -, he, hct, -⟩ | ⟨-, hf | hf⟩
          · have := ct_le i.2 he k.2 (q := q); omega
          · rcases hfc _ _ hf with ⟨-, h⟩ | ⟨rfl, -⟩
            · exact absurd h h2
            · rfl
          · rcases hfc _ _ hf with ⟨rfl, -⟩ | ⟨-, h⟩
            · rfl
            · exact absurd h h2
      · rcases newEdge_cases hK hw h with ⟨i, x, y, k, e, -, he, hct, -⟩ | ⟨-, hf | hf⟩
        · have := ct_le i.2 he k.2 (q := q); omega
        · rcases hfc _ _ hf with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rcases hfc _ _ hf with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact Or.inr rfl
          · exact Or.inl rfl
  · by_cases hnew : ∃ z, (net K sp).pres (r + 1) z ∧ ¬ (net K sp).pres r z
    · obtain ⟨z, h1, h2⟩ := hnew
      obtain ⟨u, hu⟩ := newEdge_of_newPres h1 h2
      have hzK : ¬ IsK K z := fun h => h2 (pres_K h)
      right
      refine ⟨z, h2, fun z' h1' => ?_, fun u' v' h => ?_⟩
      · by_cases h2' : (net K sp).pres r z'
        · exact Or.inl h2'
        · right
          obtain ⟨u'', hu''⟩ := newEdge_of_newPres h1' h2'
          have hz'K : ¬ IsK K z' := fun h => h2' (pres_K h)
          have := newEdge_unique_ne_T hK hw hr hu hu''
          rcases Sym2.eq_iff.mp this with ⟨-, h⟩ | ⟨rfl, -⟩
          · exact h.symm
          · rcases newEdge_K_mem hK hw hu hr with h | h
            · exact absurd h hz'K
            · exact absurd h hzK
      · have := newEdge_unique_ne_T hK hw hr hu h
        rcases Sym2.eq_iff.mp this with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
    · push_neg at hnew
      left
      exact ⟨hnew, fun u v u' v' h h' => newEdge_unique_ne_T hK hw hr h h'⟩

/-- Validity in the edge-insertion model (all nodes present from the start). -/
lemma edgeIns (hK : KInj K) (hw : WF K sp) (hfull : sp.full)
    (hfin : ∃ a b, ∀ u v, sp.fin u v → u = a ∧ v = b) : (net K sp).EdgeIns := by
  intro r
  refine ⟨fun v _ => Or.inl hfull, fun u v u' v' h h' => ?_⟩
  by_cases hr : r + 1 = 2 * q * t + 1
  · obtain ⟨a, b, hab⟩ := hfin
    have key : ∀ u v, (net K sp).NewEdge r u v → s(u, v) = s(a, b) := by
      intro u v h
      rcases newEdge_cases hK hw h with ⟨i, x, y, k, e, -, he, hct, -⟩ | ⟨-, hf | hf⟩
      · have := ct_le i.2 he k.2 (q := q); omega
      · obtain ⟨rfl, rfl⟩ := hab _ _ hf; rfl
      · obtain ⟨rfl, rfl⟩ := hab _ _ hf; exact Sym2.eq_swap
    rw [key _ _ h, key _ _ h']
  · exact newEdge_unique_ne_T hK hw hr h h'


/-! ### Degrees -/

/-- `v` is an endpoint of some creation. -/
def InCr (sp : Spec V t) (v : V) : Prop := ∃ j x y, sp.cr j = some (x, y) ∧ (v = x ∨ v = y)

lemma ncard_le_of_subset_finset {s : Set V} {S : Finset V} {n : ℕ} (h : s ⊆ ↑S) (hS : S.card ≤ n) :
    s.ncard ≤ n :=
  (Set.ncard_le_ncard h S.finite_toSet).trans (by rw [Set.ncard_coe_finset]; exact hS)

lemma card_image_K_le (i : Fin t) : (Finset.univ.image (K i)).card ≤ q :=
  Finset.card_image_le.trans (by simp)

/-- Maximum degree `q + 1 = s - 1`, provided creation endpoints have at most one final
neighbour and other nodes at most `q + 1`. -/
lemma degLE (hK : KInj K) (hw : WF K sp)
    (hF : ∀ v, ¬ IsK K v → ∃ F : Finset V, (∀ u, sp.fin u v ∨ sp.fin v u → u ∈ F) ∧
      F.card ≤ (if InCr sp v then 1 else q + 1)) :
    (net K sp).DegLE (q + 1) := by
  intro r v
  by_cases hv : IsK K v
  · obtain ⟨i, k, rfl⟩ := hv
    let E : Finset V := match sp.cr i with
      | some (x, y) => {x, y}
      | none => ∅
    have hE : E.card ≤ 2 := by
      dsimp only [E]
      split
      · exact Finset.card_le_two
      · simp
    refine ncard_le_of_subset_finset (S := (Finset.univ.image (K i)).erase (K i k) ∪ E) ?_ ?_
    · intro u hu
      rw [Set.mem_setOf_eq, adj_K_iff hK hw] at hu
      simp only [Finset.coe_union, Finset.coe_erase, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_union, Set.mem_diff, Set.mem_range, Set.mem_singleton_iff]
      rcases hu with ⟨k', hk, rfl⟩ | ⟨x, y, hc, hu⟩
      · exact Or.inl ⟨⟨k', rfl⟩, fun h => hk (hK _ _ _ _ h).2⟩
      · right
        dsimp only [E]
        rw [hc]
        rcases hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    · have h1 := Finset.card_union_le ((Finset.univ.image (K i)).erase (K i k)) E
      have h2 : ((Finset.univ.image (K i)).erase (K i k)).card ≤ q - 1 := by
        rw [Finset.card_erase_of_mem (by simp)]
        have := card_image_K_le (K := K) i
        omega
      have := k.2
      omega
  · obtain ⟨F, hF1, hF2⟩ := hF v hv
    by_cases hin : InCr sp v
    · obtain ⟨j, x, y, hc, hxy⟩ := hin
      rw [if_pos ⟨j, x, y, hc, hxy⟩] at hF2
      refine ncard_le_of_subset_finset (S := Finset.univ.image (K j) ∪ F) ?_ ?_
      · intro u hu
        rw [Set.mem_setOf_eq, adj_I_iff _ _ _ hv] at hu
        simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
          Set.mem_union, Set.mem_range, Finset.mem_coe]
        rcases hu with ⟨j', x', y', k, hc', rfl, hh⟩ | ⟨-, -, hf⟩
        · left
          by_cases hj : j' = j
          · subst hj; exact ⟨k, rfl⟩
          · exfalso
            have := hw.cr_disj _ _ _ _ _ _ hj hc' hc
            rcases hxy with rfl | rfl <;> rcases hh with ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all
        · exact Or.inr (hF1 u hf)
      · have := Finset.card_union_le (Finset.univ.image (K j)) F
        have := card_image_K_le (K := K) j
        omega
    · rw [if_neg hin] at hF2
      refine ncard_le_of_subset_finset (S := F) ?_ hF2
      intro u hu
      rw [Set.mem_setOf_eq, adj_I_iff _ _ _ hv] at hu
      rcases hu with ⟨j', x', y', k, hc', rfl, hh⟩ | ⟨-, -, hf⟩
      · exfalso
        rcases hh with ⟨h, -⟩ | ⟨h, -⟩
        · exact hin ⟨j', x', y', hc', Or.inl h⟩
        · exact hin ⟨j', x', y', hc', Or.inr h⟩
      · exact hF1 u hf

/-! ### Cliques -/

/-- `create(x, K^i, y)` followed by the final edge `{x, y}` forms an `s`-clique. -/
lemma isNClique_create (hK : KInj K) (hw : WF K sp) {i : Fin t} {x y : V}
    (hc : sp.cr i = some (x, y)) (hf : sp.fin x y) {r : ℕ} (hr : 2 * q * t + 1 ≤ r) :
    ((net K sp).graph r).IsNClique (q + 2) (Finset.univ.image (K i) ∪ {x, y}) := by
  obtain ⟨hx, hy, hxy⟩ := hw.cr_I _ _ _ hc
  have hKx : ∀ k, (net K sp).adj r (K i k) x := fun k =>
    (net K sp).symm _ _ _ ((adj_K_iff hK hw r x i k).2
      (Or.inr ⟨x, y, hc, Or.inl ⟨rfl, by have := ct_le i.2 (zero_le_one) k.2 (q := q); omega⟩⟩))
  have hKy : ∀ k, (net K sp).adj r (K i k) y := fun k =>
    (net K sp).symm _ _ _ ((adj_K_iff hK hw r y i k).2
      (Or.inr ⟨x, y, hc, Or.inr ⟨rfl, by have := ct_le i.2 le_rfl k.2 (q := q); omega⟩⟩))
  have hxy' : (net K sp).adj r x y :=
    ⟨hxy, Or.inl (Or.inr (Or.inr ⟨hr, hf⟩))⟩
  rw [SimpleGraph.isNClique_iff]
  constructor
  · intro u hu v hv huv
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Finset.coe_insert, Finset.coe_singleton, Set.mem_union, Set.mem_range, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu hv
    show (net K sp).adj r u v
    rcases hu with ⟨k, rfl⟩ | rfl | rfl <;> rcases hv with ⟨k', rfl⟩ | rfl | rfl
    · exact (adj_K_iff hK hw r _ i k').2 (Or.inl ⟨k, fun h => huv (by rw [h]), rfl⟩)
    · exact hKx k
    · exact hKy k
    · exact (net K sp).symm _ _ _ (hKx k')
    · exact absurd rfl huv
    · exact hxy'
    · exact (net K sp).symm _ _ _ (hKy k')
    · exact (net K sp).symm _ _ _ hxy'
    · exact absurd rfl huv
  · rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective, Finset.card_univ,
      Fintype.card_fin, Finset.card_pair hxy]
    · intro k k' h; exact (hK _ _ _ _ h).2
    · rw [Finset.disjoint_left]
      intro u hu hu'
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton] at hu hu'
      obtain ⟨k, rfl⟩ := hu
      rcases hu' with h | h
      · exact hx ⟨i, k, h⟩
      · exact hy ⟨i, k, h⟩

/-- An `s`-clique contains at most `q` clique nodes, hence two adjacent nodes of `I`, which must
be joined by a final edge. -/
lemma clique_fin (hK : KInj K) (hw : WF K sp) {r : ℕ} {Q : Finset V}
    (hQ : ((net K sp).graph r).IsNClique (q + 2) Q) :
    ∃ u ∈ Q, ∃ v ∈ Q, u ≠ v ∧ ¬ IsK K u ∧ ¬ IsK K v ∧ (sp.fin u v ∨ sp.fin v u) := by
  rw [SimpleGraph.isNClique_iff] at hQ
  obtain ⟨hcl, hcard⟩ := hQ
  have hK' : (Q.filter (IsK K)).card ≤ q := by
    by_cases hne : (Q.filter (IsK K)).Nonempty
    · obtain ⟨w, hw'⟩ := hne
      rw [Finset.mem_filter] at hw'
      obtain ⟨hwQ, i0, k0, rfl⟩ := hw'
      refine le_trans (Finset.card_le_card (t := Finset.univ.image (K i0)) ?_) (card_image_K_le i0)
      intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨hzQ, j, k, rfl⟩ := hz
      by_cases hzw : K j k = K i0 k0
      · rw [hzw]; simp
      · have hadj : (net K sp).adj r (K j k) (K i0 k0) := hcl hzQ hwQ hzw
        rw [adj_K_iff hK hw] at hadj
        rcases hadj with ⟨k', -, h⟩ | ⟨x, y, hc, h | h⟩
        · rw [h]; simp
        · exact absurd ⟨j, k, h.1⟩ (hw.cr_I _ _ _ hc).1
        · exact absurd ⟨j, k, h.1⟩ (hw.cr_I _ _ _ hc).2.1
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  have hI : 1 < (Q.filter (fun v => ¬ IsK K v)).card := by
    have := Finset.card_filter_add_card_filter_not (s := Q) (p := IsK K)
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hI
  rw [Finset.mem_filter] at hu hv
  have hadj : (net K sp).adj r u v := hcl hu.1 hv.1 huv
  rw [adj_I_iff _ _ _ hv.2] at hadj
  rcases hadj with ⟨i, x, y, k, -, rfl, -⟩ | ⟨-, -, hf⟩
  · exact absurd ⟨i, k, rfl⟩ hu.2
  · exact ⟨u, hu.1, v, hv.1, huv, hu.2, hv.2, hf⟩

end Hard

end Podc.DynamicSubgraphFinding
