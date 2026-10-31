import Papers.PODC2025.DynamicSubgraphFinding.FullHist

/-!
# The algorithm of Theorem 1.7 is unsound

Theorem 1.7 claims a one-round `List(K₃)` algorithm under node *and* edge insertions. In the case
`t_uv - t_uw ≤ d` of its correctness proof, node `v` lists the triangle `{u, v, w}` "by the same
argument as for node `v` in the proof of Theorem 1.4": `v` receives `R^d_edge(u) ∋ j` from its new
neighbour `u` (Step 3) and `j ∈ R^d_signal(v)` because `w` sent `(Signal)` `j` rounds ago
(Step 1), and infers the edge `{u, w}` "by the fact that in each round at most one topological
change occurs". With node insertions this inference is wrong: the single change `j` rounds ago
may be the insertion of a *new node* `x` adjacent to both `u` and `w`.

Counterexample (`scenarioB`, maximum degree 2): `G⁰` has the edge `{v, w}`; in round 2 the node `x`
is inserted with edges `{x, u}`, `{x, w}`; in round 3 the edge `{u, v}` is inserted. In round 3,
`u` sends `R_edge(u) = {1}` to `v` and `w` had sent `(Signal)` to `v` in round 2, so `v` lists
`{u, v, w}`, which is not a triangle.

`alg17` is the algorithm family: messages consist of `(Signal)` (Step 1) and `R^d_edge` sent to a
new neighbour (Step 3), as in the paper, plus an *arbitrary* further component `oth` (which can
implement Steps 2 and 4, the bit reports and the periodic `1-DBList` updates, in any way); outputs
are the triangles found by the paper's rule for `v`, plus arbitrary further triangles `extra`.
`theorem_1_7_algorithm_unsound`: no member of the family solves `List(K₃)`.
-/

namespace Podc.DynamicSubgraphFinding

open Classical

namespace Alg17

variable {V Mo : Type}

/-- Messages: `(Signal)` bit, `R^d_edge` (only to a new neighbour), any further component. -/
abbrev Msg (Mo : Type) := Bool × Option (Finset ℕ) × Mo

/-- Neighbours in round `k` according to the history `h` and the current input `x`
(round `h.r + 1`). -/
def nbrsAt (h : Hist V (Msg Mo)) (x : Option (Set V)) (k : ℕ) : Set V :=
  match (if k = h.r + 1 then x else h.locH k) with
  | some N => N
  | none => ∅

/-- The node obtained a new neighbour in round `k ≥ 1`. -/
def GotNew (h : Hist V (Msg Mo)) (x : Option (Set V)) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ y, y ∈ nbrsAt h x k ∧ y ∉ nbrsAt h x (k - 1)

/-- `R^d_edge`: the ages `a ∈ [1, d]` of the rounds in which the node obtained a new edge. -/
noncomputable def rEdge (d : ℕ) (h : Hist V (Msg Mo)) (x : Option (Set V)) (r : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter (fun a => 1 ≤ a ∧ a < r ∧ GotNew h x (r - a))

/-- The message function: Step 1 (`(Signal)` to all neighbours if a new neighbour appeared),
Step 3 (`R^d_edge` to the new neighbour), and an arbitrary further component. -/
noncomputable def snd (d : ℕ) (oth : ℕ → Hist V (Msg Mo) → Option (Set V) → V → Mo) (r : ℕ)
    (h : Hist V (Msg Mo)) (x : Option (Set V)) (w : V) : Msg Mo :=
  (decide (GotNew h x r),
    if w ∈ nbrsAt h x r ∧ w ∉ nbrsAt h x (r - 1) then some (rEdge d h x r) else none,
    oth r h x w)

/-- Neighbours in round `k` according to a history (after the round). -/
def nb (h : Hist V (Msg Mo)) (k : ℕ) : Set V :=
  match h.locH k with
  | some N => N
  | none => ∅

/-- **The rule of the paper for node `v`** (case `t_uv - t_uw ≤ d` of the proof of Theorem 1.7,
i.e. the case of node `v` in the proof of Theorem 1.4): in some round `t`, `u` is a new neighbour
and sends `R_edge(u) ∋ j`, and `j` rounds earlier the neighbour `w ≠ u` sent `(Signal)`; then
`{u, v, w}` is listed. -/
def VRule (d : ℕ) (h : Hist V (Msg Mo)) (Q : Finset V) : Prop :=
  ∃ t u w j R m1 m2 b,
    1 ≤ j ∧ j ≤ d ∧ j < t ∧ t ≤ h.r ∧ u ∈ nb h t ∧ u ∉ nb h (t - 1) ∧ w ∈ nb h (t - j) ∧ w ≠ u ∧
    h.inbH t u = some (b, some R, m1) ∧ j ∈ R ∧ h.inbH (t - j) w = some (true, m2) ∧
    Q = {h.id, u, w}

/-- The algorithm family of Theorem 1.7 (Steps 1 and 3 as in the paper, everything else free). -/
noncomputable def alg17 (d : ℕ) (oth : ℕ → Hist V (Msg Mo) → Option (Set V) → V → Mo)
    (extra : Hist V (Msg Mo) → Set (Finset V)) : Algorithm V (Msg Mo) (Set (Finset V)) :=
  histAlg (snd d oth) (fun h => {Q | VRule d h Q} ∪ extra h)

/-! ### The counterexample network -/

variable (v w u x : V)

/-- (B): `G⁰ = {v, w}` (and `x` absent), round 2 inserts `x` with edges to `u` and `w`,
round 3 inserts `{u, v}`. -/
def scenarioB (hd : [v, w, u, x].Nodup) : InsNet V where
  pres r z := z ≠ x ∨ 2 ≤ r
  adj r a b := s(a, b) = s(v, w) ∨ (2 ≤ r ∧ (s(a, b) = s(x, u) ∨ s(a, b) = s(x, w))) ∨
    (3 ≤ r ∧ s(a, b) = s(u, v))
  symm := by
    intro r a b h
    simpa [Sym2.eq_swap (a := a)] using h
  irrefl := by
    intro r a h
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at hd
    rcases h with h | ⟨-, h | h⟩ | ⟨-, h⟩ <;>
      · rw [Sym2.eq_iff] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> simp_all
  pres_of_adj := by
    intro r a b h
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at hd
    rcases h with h | ⟨hr, -⟩ | ⟨hr, -⟩
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Ne.symm hd.1.2.2) |>.elim (fun h => Or.inl (by tauto)) (fun h => Or.inr h)
      · exact Or.inl (by tauto)
    · exact Or.inr hr
    · exact Or.inr (by omega)
  pres_mono := by
    rintro r z (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)
  adj_mono := by
    rintro r a b (h | ⟨hr, h⟩ | ⟨hr, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨by omega, h⟩)
    · exact Or.inr (Or.inr ⟨by omega, h⟩)

section Hist

variable {d : ℕ} {oth : ℕ → Hist V (Msg Mo) → Option (Set V) → V → Mo}
  {extra : Hist V (Msg Mo) → Set (Finset V)} (D : InsNet V)

lemma alg17_r (r : ℕ) (z : V) : ((alg17 d oth extra).state D r z).r = r :=
  histAlg_r _ _ D r z

lemma alg17_id (r : ℕ) (z : V) : ((alg17 d oth extra).state D r z).id = z :=
  histAlg_id _ _ D r z

lemma alg17_locH {r k : ℕ} (hk : k ≤ r) (z : V) :
    ((alg17 d oth extra).state D r z).locH k = D.loc k z :=
  histAlg_locH _ _ D hk z

lemma alg17_inbH {k : ℕ} (z y : V) (h : D.adj (k + 1) y z) :
    ((alg17 d oth extra).state D (k + 1) z).inbH (k + 1) y =
      some (snd d oth (k + 1) ((alg17 d oth extra).state D k y) (D.loc (k + 1) y) z) := by
  have h1 := congrFun (histAlg_inbH (snd d oth) (fun h => {Q | VRule d h Q} ∪ extra h) D
    (r := k + 1) (k := k + 1) (by omega) le_rfl z) y
  simp only [Nat.add_sub_cancel] at h1
  exact h1.trans ((histAlg_inbox _ _ D k z y).trans (if_pos h))

lemma alg17_inbH_le {r k : ℕ} (hk : k + 1 ≤ r) (z y : V) (h : D.adj (k + 1) y z) :
    ((alg17 d oth extra).state D r z).inbH (k + 1) y =
      some (snd d oth (k + 1) ((alg17 d oth extra).state D k y) (D.loc (k + 1) y) z) := by
  have h1 := congrFun (histAlg_inbH (snd d oth) (fun h => {Q | VRule d h Q} ∪ extra h) D
    (r := r) (k := k + 1) (by omega) hk z) y
  simp only [Nat.add_sub_cancel] at h1
  exact h1.trans ((histAlg_inbox _ _ D k z y).trans (if_pos h))

end Hist

variable {v w u x}

section B

variable (hd : [v, w, u, x].Nodup)
include hd

lemma nodup4 : (v ≠ w ∧ v ≠ u ∧ v ≠ x) ∧ (w ≠ u ∧ w ≠ x) ∧ u ≠ x := by
  simpa using hd

/-- (B) is a valid network in the node-and-edge-insertion model. -/
lemma scenarioB_valid : (scenarioB v w u x hd).NodeEdgeIns := by
  obtain ⟨⟨hvw, hvu, hvx⟩, ⟨hwu, hwx⟩, hux⟩ := nodup4 hd
  intro r
  by_cases hr : r = 1
  · subst hr
    right
    refine ⟨x, ?_, ?_, ?_⟩
    · simp [scenarioB]
    · intro z hz
      by_cases hzx : z = x
      · exact Or.inr hzx
      · exact Or.inl (Or.inl hzx)
    · rintro a b ⟨h1, h2⟩
      simp only [scenarioB] at h1 h2
      rcases h1 with h | ⟨-, h | h⟩ | ⟨h, -⟩
      · exact absurd (Or.inl h) h2
      · rw [Sym2.eq_iff] at h; rcases h with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp
      · rw [Sym2.eq_iff] at h; rcases h with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp
      · omega
  · left
    refine ⟨fun z hz => ?_, fun a b a' b' h h' => ?_⟩
    · rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (by omega)
    · have key : ∀ a b, (scenarioB v w u x hd).NewEdge r a b → s(a, b) = s(u, v) := by
        rintro a b ⟨h1, h2⟩
        simp only [scenarioB] at h1 h2
        rcases h1 with h | ⟨h3, h⟩ | ⟨h3, h⟩
        · exact absurd (Or.inl h) h2
        · exact absurd (Or.inr (Or.inl ⟨by omega, h⟩)) h2
        · by_cases h4 : 3 ≤ r
          · exact absurd (Or.inr (Or.inr ⟨h4, h⟩)) h2
          · exact h
      rw [key _ _ h, key _ _ h']

lemma scenarioB_deg : (scenarioB v w u x hd).DegLE 2 := by
  obtain ⟨⟨hvw, hvu, hvx⟩, ⟨hwu, hwx⟩, hux⟩ := nodup4 hd
  intro r z
  have hsub : {a | (scenarioB v w u x hd).adj r a z} ⊆
      ↑(if z = v then ({w, u} : Finset V) else if z = w then {v, x} else if z = u then {x, v}
        else if z = x then {u, w} else ∅) := by
    intro a ha
    simp only [scenarioB, Set.mem_setOf_eq, Sym2.eq_iff] at ha
    split_ifs with h1 h2 h3 h4 <;> subst_vars <;> simp only [Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_empty,
      Set.mem_empty_iff_false] <;> aesop
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  split_ifs <;> first | exact Finset.card_le_two | simp

/-- In (B), `u`, `v`, `w` do not form a triangle in round 3. -/
lemma scenarioB_not_triangle : ¬ ((scenarioB v w u x hd).graph 3).IsNClique 3 {v, u, w} := by
  obtain ⟨⟨hvw, hvu, hvx⟩, ⟨hwu, hwx⟩, hux⟩ := nodup4 hd
  intro h
  have : (scenarioB v w u x hd).adj 3 u w := h.isClique (by simp) (by simp) (Ne.symm hwu)
  simp only [scenarioB, Sym2.eq_iff] at this
  aesop

end B

/-- **The algorithm of Theorem 1.7 is incorrect.** For every window `d ≥ 1`, every way of
implementing the remaining message parts (Steps 2 and 4) and every additional output rule, the
algorithm that sends `(Signal)` and `R^d_edge` as in Steps 1 and 3 and lists the triangles found by
the paper's rule for node `v` does not solve one-round `List(K₃)` under node and edge insertions,
already on networks of maximum degree 2 with four non-isolated nodes. -/
theorem theorem_1_7_algorithm_unsound {V Mo : Type} (v w u x : V) (hd : [v, w, u, x].Nodup)
    (d : ℕ) (hd1 : 1 ≤ d) (oth : ℕ → Hist V (Msg Mo) → Option (Set V) → V → Mo)
    (extra : Hist V (Msg Mo) → Set (Finset V)) :
    ¬ Solves (alg17 d oth extra) InsNet.NodeEdgeIns 2 ListOK := by
  obtain ⟨⟨hvw, hvu, hvx⟩, ⟨hwu, hwx⟩, hux⟩ := nodup4 hd
  intro hA
  set D := scenarioB v w u x hd
  have hOK := (hA D (scenarioB_valid hd) (scenarioB_deg hd) 3).2 v (Or.inl hvx) {v, u, w}
  refine scenarioB_not_triangle hd (hOK (Or.inl ?_))
  -- the rule for `v` fires in round 3
  have hpres : ∀ z r, z ≠ x → D.pres r z := fun z r h => Or.inl h
  have hloc : ∀ z r, z ≠ x → D.loc r z = some {a | D.adj r a z} := by
    intro z r h; simp [InsNet.loc, hpres z r h]
  have hnb : ∀ k, k ≤ 3 → nb ((alg17 d oth extra).state D 3 v) k = {a | D.adj k a v} := by
    intro k hk
    simp only [nb, alg17, histAlg_locH _ _ D hk, hloc v k hvx]
  have huv3 : D.adj 3 u v := Or.inr (Or.inr ⟨le_rfl, rfl⟩)
  have hwv2 : D.adj 2 w v := Or.inl Sym2.eq_swap
  have hnuv : ¬ D.adj 2 u v := by
    simp only [D, scenarioB, Sym2.eq_iff]; aesop
  have hxu2 : D.adj 2 x u := Or.inr (Or.inl ⟨le_rfl, Or.inl rfl⟩)
  have hxu1 : ¬ D.adj 1 x u := by
    simp only [D, scenarioB, Sym2.eq_iff]; aesop
  have hxw2 : D.adj 2 x w := Or.inr (Or.inl ⟨le_rfl, Or.inr rfl⟩)
  have hxw1 : ¬ D.adj 1 x w := by
    simp only [D, scenarioB, Sym2.eq_iff]; aesop
  -- `u`'s message to `v` in round 3 carries `R_edge(u) ∋ 1`
  set hu2 := (alg17 d oth extra).state D 2 u
  have hnbu3 : nbrsAt hu2 (D.loc 3 u) 3 = {a | D.adj 3 a u} := by
    simp [nbrsAt, hu2, alg17_r, hloc u 3 hux]
  have hnbu2 : nbrsAt hu2 (D.loc 3 u) 2 = {a | D.adj 2 a u} := by
    simp [nbrsAt, hu2, alg17_r, alg17_locH D (le_refl 2), hloc u 2 hux]
  have hnbu1 : nbrsAt hu2 (D.loc 3 u) 1 = {a | D.adj 1 a u} := by
    simp [nbrsAt, hu2, alg17_r, alg17_locH D (show 1 ≤ 2 by norm_num), hloc u 1 hux]
  have hR : 1 ∈ rEdge d hu2 (D.loc 3 u) 3 := by
    simp only [rEdge, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, le_rfl, by norm_num, by norm_num, x, ?_, ?_⟩
    · rw [hnbu2]; exact hxu2
    · rw [show 2 - 1 = 1 from rfl, hnbu1]; exact hxu1
  have hsnd3 : snd d oth 3 hu2 (D.loc 3 u) v =
      (decide (GotNew hu2 (D.loc 3 u) 3), some (rEdge d hu2 (D.loc 3 u) 3), oth 3 hu2 (D.loc 3 u) v) := by
    have e1 : v ∈ nbrsAt hu2 (D.loc 3 u) 3 := by rw [hnbu3]; exact D.symm _ _ _ huv3
    have e2 : v ∉ nbrsAt hu2 (D.loc 3 u) (3 - 1) := by
      rw [show 3 - 1 = 2 from rfl, hnbu2]; exact fun h => hnuv (D.symm _ _ _ h)
    simp only [snd]
    rw [if_pos ⟨e1, e2⟩]
  -- `w`'s message to `v` in round 2 is a `(Signal)`
  set hw1 := (alg17 d oth extra).state D 1 w
  have hsig : decide (GotNew hw1 (D.loc 2 w) 2) = true := by
    rw [decide_eq_true_iff]
    refine ⟨by norm_num, x, ?_, ?_⟩
    · simp only [nbrsAt, hw1, alg17_r, if_pos rfl, hloc w 2 hwx]; exact hxw2
    · simp only [nbrsAt, hw1, alg17_r, show 2 - 1 = 1 from rfl,
        alg17_locH D (le_refl 1), hloc w 1 hwx]
      simp only [if_neg (show (1 : ℕ) ≠ 1 + 1 by norm_num)]
      exact hxw1
  refine ⟨3, u, w, 1, rEdge d hu2 (D.loc 3 u) 3, oth 3 hu2 (D.loc 3 u) v,
    (if v ∈ nbrsAt hw1 (D.loc 2 w) 2 ∧ v ∉ nbrsAt hw1 (D.loc 2 w) (2 - 1) then
      some (rEdge d hw1 (D.loc 2 w) 2) else none, oth 2 hw1 (D.loc 2 w) v),
    decide (GotNew hu2 (D.loc 3 u) 3), le_rfl, hd1, by norm_num, ?_, ?_, ?_, ?_, hwu,
    ?_, hR, ?_, ?_⟩
  · rw [alg17_r]
  · rw [hnb 3 le_rfl]; exact huv3
  · rw [show 3 - 1 = 2 from rfl, hnb 2 (by norm_num)]; exact hnuv
  · rw [show 3 - 1 = 2 from rfl, hnb 2 (by norm_num)]; exact hwv2
  · rw [alg17_inbH D v u huv3, hsnd3]
  · rw [show 3 - 1 = 2 from rfl, alg17_inbH_le D (show 1 + 1 ≤ 3 by norm_num) v w hwv2]
    exact congrArg some (Prod.ext hsig rfl)
  · rw [alg17_id]

end Alg17

end Podc.DynamicSubgraphFinding
