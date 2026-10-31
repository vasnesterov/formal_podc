import Papers.PODC2025.DynamicSubgraphFinding.HardInstance

/-!
# The four scenarios (S1)–(S4) of Section 4.1

* `S1 full x i y`: `create(x, K^i, y)` and insert `{x, y}` at round `T`.
* `S2 full a i c d i' b`: `create(a, K^i, c)`, `create(d, K^{i'}, b)`, insert `{a, b}` at `T`.
* `S3 full a i c d i' b`: `create(d, K^i, b)`, `create(a, K^{i'}, c)`, insert `{a, b}` at `T`.
* `S4 a i b c`: `create(a, K^i, b)` and insert the node `c` with edges `{a, c}`, `{c, b}` at `T`.

`full = True`: all nodes present from the start (edge insertions only, Theorem 1.3);
`full = False`: nodes of `I` are inserted with their first edge (Theorem 1.6).
For each scenario: well-formedness, validity in the model, maximum degree `s - 1 = q + 1`, and
which `s`-cliques exist at round `T`.
-/

namespace Podc.DynamicSubgraphFinding

open Classical

namespace Hard

variable {V : Type} {q t : ℕ} {K : Fin t → Fin q → V}

/-- One creation. -/
def crOne (i : Fin t) (x y : V) : Fin t → Option (V × V) :=
  fun j => if j = i then some (x, y) else none

/-- Two creations. -/
def crTwo (i : Fin t) (x y : V) (i' : Fin t) (x' y' : V) : Fin t → Option (V × V) :=
  fun j => if j = i then some (x, y) else if j = i' then some (x', y') else none

/-- (S1) `create(x, K^i, y)`, then the edge `{x, y}`. -/
def S1 (full : Prop) (x : V) (i : Fin t) (y : V) : Spec V t :=
  ⟨crOne i x y, fun u v => u = x ∧ v = y, full⟩

/-- (S2) `create(a, K^i, c)`, `create(d, K^{i'}, b)`, then the edge `{a, b}`. -/
def S2 (full : Prop) (a : V) (i : Fin t) (c d : V) (i' : Fin t) (b : V) : Spec V t :=
  ⟨crTwo i a c i' d b, fun u v => u = a ∧ v = b, full⟩

/-- (S3) `create(d, K^i, b)`, `create(a, K^{i'}, c)`, then the edge `{a, b}`. -/
def S3 (full : Prop) (a : V) (i : Fin t) (c d : V) (i' : Fin t) (b : V) : Spec V t :=
  ⟨crTwo i d b i' a c, fun u v => u = a ∧ v = b, full⟩

/-- (S4) `create(a, K^i, b)`, then the node `c` with edges `{a, c}` and `{c, b}`. -/
def S4 (a : V) (i : Fin t) (b c : V) : Spec V t :=
  ⟨crOne i a b, fun u v => (u = a ∧ v = c) ∨ (u = b ∧ v = c), False⟩

lemma crOne_eq_some {i j : Fin t} {x y x' y' : V} (h : crOne i x y j = some (x', y')) :
    j = i ∧ x' = x ∧ y' = y := by
  unfold crOne at h
  split_ifs at h with hj
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
  exact ⟨hj, rfl, rfl⟩

lemma crTwo_eq_some {i i' j : Fin t} {x y x' y' u w : V}
    (h : crTwo i x y i' x' y' j = some (u, w)) :
    (j = i ∧ u = x ∧ w = y) ∨ (j ≠ i ∧ j = i' ∧ u = x' ∧ w = y') := by
  unfold crTwo at h
  split_ifs at h with h1 h2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
    exact Or.inl ⟨h1, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
    exact Or.inr ⟨h1, h2, rfl, rfl⟩

/-! ### Well-formedness -/

lemma wf_S1 {full : Prop} {x y : V} {i : Fin t} (hx : ¬ IsK K x) (hy : ¬ IsK K y)
    (hxy : x ≠ y) : WF K (S1 full x i y) where
  cr_I := by
    intro j u w h
    obtain ⟨-, rfl, rfl⟩ := crOne_eq_some h
    exact ⟨hx, hy, hxy⟩
  cr_disj := by
    intro j j' u w u' w' hjj h h'
    obtain ⟨rfl, -⟩ := crOne_eq_some h
    obtain ⟨rfl, -⟩ := crOne_eq_some h'
    exact absurd rfl hjj
  fin_I := by
    rintro u v ⟨rfl, rfl⟩
    exact ⟨hx, hy⟩

lemma wf_crTwo {i i' : Fin t} {x y x' y' : V} (hii : i ≠ i') (hx : ¬ IsK K x) (hy : ¬ IsK K y)
    (hx' : ¬ IsK K x') (hy' : ¬ IsK K y') (hxy : x ≠ y) (hxy' : x' ≠ y')
    (hd : x ≠ x' ∧ x ≠ y' ∧ y ≠ x' ∧ y ≠ y') (fin : V → V → Prop) (full : Prop)
    (hfin : ∀ u v, fin u v → ¬ IsK K u ∧ ¬ IsK K v) :
    WF K ⟨crTwo i x y i' x' y', fin, full⟩ where
  cr_I := by
    intro j u w h
    rcases crTwo_eq_some h with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
    · exact ⟨hx, hy, hxy⟩
    · exact ⟨hx', hy', hxy'⟩
  cr_disj := by
    intro j j' u w u' w' hjj h h'
    rcases crTwo_eq_some h with ⟨rfl, rfl, rfl⟩ | ⟨h1, rfl, rfl, rfl⟩ <;>
    rcases crTwo_eq_some h' with ⟨rfl, rfl, rfl⟩ | ⟨h1', rfl, rfl, rfl⟩
    · exact absurd rfl hjj
    · exact hd
    · exact ⟨Ne.symm hd.1, Ne.symm hd.2.2.1, Ne.symm hd.2.1, Ne.symm hd.2.2.2⟩
    · exact absurd rfl hjj
  fin_I := hfin

lemma wf_S2 {full : Prop} {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup) :
    WF K (S2 full a i c d i' b) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hdist
  refine wf_crTwo hii ha hc hd hb (by tauto) (by tauto) ⟨by tauto, by tauto, by tauto, by tauto⟩
    _ _ ?_
  rintro u v ⟨rfl, rfl⟩
  exact ⟨ha, hb⟩

lemma wf_S3 {full : Prop} {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup) :
    WF K (S3 full a i c d i' b) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hdist
  refine wf_crTwo hii hd hb ha hc (by tauto) (by tauto) ⟨by tauto, by tauto, by tauto, by tauto⟩
    _ _ ?_
  rintro u v ⟨rfl, rfl⟩
  exact ⟨ha, hb⟩

lemma wf_S4 {a b c : V} {i : Fin t} (ha : ¬ IsK K a) (hb : ¬ IsK K b) (hc : ¬ IsK K c)
    (hab : a ≠ b) : WF K (S4 a i b c) where
  cr_I := by
    intro j u w h
    obtain ⟨-, rfl, rfl⟩ := crOne_eq_some h
    exact ⟨ha, hb, hab⟩
  cr_disj := by
    intro j j' u w u' w' hjj h h'
    obtain ⟨rfl, -⟩ := crOne_eq_some h
    obtain ⟨rfl, -⟩ := crOne_eq_some h'
    exact absurd rfl hjj
  fin_I := by
    rintro u v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨ha, hc⟩
    · exact ⟨hb, hc⟩

/-! ### Presence before the final round -/

/-- A creation endpoint is present at round `2qt` (it has an edge to `K i 0`). -/
lemma pres_of_cr (hK : KInj K) {sp : Spec V t} (hw : WF K sp) (hq : 1 ≤ q) {i : Fin t}
    {x y v : V} (hc : sp.cr i = some (x, y)) (hv : v = x ∨ v = y) :
    (net K sp).pres (2 * q * t) v := by
  refine Or.inr (Or.inr ⟨K i ⟨0, hq⟩, (net K sp).symm _ _ _ ((adj_K_iff hK hw _ _ _ _).2
    (Or.inr ⟨x, y, hc, ?_⟩))⟩)
  rcases hv with rfl | rfl
  · exact Or.inl ⟨rfl, ct_le i.2 zero_le_one (by simp; omega)⟩
  · exact Or.inr ⟨rfl, ct_le i.2 le_rfl (by simp; omega)⟩

/-! ### Validity -/

section Validity

variable (hK : KInj K) (hq : 1 ≤ q)
include hK

lemma edgeIns_S1 {x y : V} {i : Fin t} (hx : ¬ IsK K x) (hy : ¬ IsK K y) (hxy : x ≠ y) :
    (net K (S1 True x i y)).EdgeIns :=
  edgeIns hK (wf_S1 hx hy hxy) trivial ⟨x, y, fun _ _ h => h⟩

lemma edgeIns_S2 {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup) :
    (net K (S2 True a i c d i' b)).EdgeIns :=
  edgeIns hK (wf_S2 hii ha hb hc hd hdist) trivial ⟨a, b, fun _ _ h => h⟩

include hq

lemma nodeEdgeIns_S1 {x y : V} {i : Fin t} (hx : ¬ IsK K x) (hy : ¬ IsK K y) (hxy : x ≠ y) :
    (net K (S1 False x i y)).NodeEdgeIns := by
  have hw := wf_S1 (full := False) (i := i) hx hy hxy
  have hc : (S1 False x i y).cr i = some (x, y) := by simp [S1, crOne]
  exact nodeEdgeIns hK hw (Or.inl ⟨x, y, fun _ _ h => h, pres_of_cr hK hw hq hc (Or.inl rfl),
    pres_of_cr hK hw hq hc (Or.inr rfl)⟩)

lemma nodeEdgeIns_S2 {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup) :
    (net K (S2 False a i c d i' b)).NodeEdgeIns := by
  have hw := wf_S2 (full := False) hii ha hb hc hd hdist
  have h1 : (S2 False a i c d i' b).cr i = some (a, c) := by simp [S2, crTwo]
  have h2 : (S2 False a i c d i' b).cr i' = some (d, b) := by simp [S2, crTwo, Ne.symm hii]
  exact nodeEdgeIns hK hw (Or.inl ⟨a, b, fun _ _ h => h, pres_of_cr hK hw hq h1 (Or.inl rfl),
    pres_of_cr hK hw hq h2 (Or.inr rfl)⟩)

lemma nodeEdgeIns_S3 {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup) :
    (net K (S3 False a i c d i' b)).NodeEdgeIns := by
  have hw := wf_S3 (full := False) hii ha hb hc hd hdist
  have h1 : (S3 False a i c d i' b).cr i = some (d, b) := by simp [S3, crTwo]
  have h2 : (S3 False a i c d i' b).cr i' = some (a, c) := by simp [S3, crTwo, Ne.symm hii]
  exact nodeEdgeIns hK hw (Or.inl ⟨a, b, fun _ _ h => h, pres_of_cr hK hw hq h2 (Or.inl rfl),
    pres_of_cr hK hw hq h1 (Or.inr rfl)⟩)

lemma nodeEdgeIns_S4 {a b c : V} {i : Fin t} (ha : ¬ IsK K a) (hb : ¬ IsK K b)
    (hc : ¬ IsK K c) (hdist : [a, b, c].Nodup) :
    (net K (S4 a i b c)).NodeEdgeIns := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hdist
  have hw := wf_S4 (i := i) ha hb hc hdist.1.1
  have h1 : (S4 a i b c).cr i = some (a, b) := by simp [S4, crOne]
  refine nodeEdgeIns hK hw (Or.inr ⟨c, ?_, ?_⟩)
  · rintro (h | h | ⟨u, hu⟩)
    · exact h
    · exact hc h
    · change (net K _).adj _ u c at hu
      rw [adj_I_iff _ _ _ hc] at hu
      rcases hu with ⟨j, x, y, k, hj, -, h | h⟩ | ⟨-, h, -⟩
      · obtain ⟨-, rfl, -⟩ := crOne_eq_some hj; exact hdist.1.2 h.1.symm
      · obtain ⟨-, -, rfl⟩ := crOne_eq_some hj; exact hdist.2 h.1.symm
      · omega
  · rintro u v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨rfl, pres_of_cr hK hw hq h1 (Or.inl rfl)⟩
    · exact Or.inr ⟨rfl, pres_of_cr hK hw hq h1 (Or.inr rfl)⟩

end Validity

/-! ### Degrees -/

section Degree

variable (hK : KInj K)
include hK

lemma degLE_S1 {full : Prop} {x y : V} {i : Fin t} (hx : ¬ IsK K x) (hy : ¬ IsK K y)
    (hxy : x ≠ y) : (net K (S1 full x i y)).DegLE (q + 1) := by
  refine degLE hK (wf_S1 hx hy hxy) (fun v _ => ?_)
  refine ⟨if v = x then {y} else if v = y then {x} else ∅, ?_, ?_⟩
  · rintro u (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [Ne.symm hxy]
    · simp
  · split_ifs <;> simp

lemma degLE_crTwo {full : Prop} {x y x' y' a b : V} {i i' : Fin t} (hii : i ≠ i')
    (hw : WF K ⟨crTwo i x y i' x' y', fun u v => u = a ∧ v = b, full⟩) (hab : a ≠ b) :
    (net K ⟨crTwo i x y i' x' y', fun u v => u = a ∧ v = b, full⟩).DegLE (q + 1) := by
  refine degLE hK hw (fun v _ => ?_)
  refine ⟨if v = a then {b} else if v = b then {a} else ∅, ?_, ?_⟩
  · rintro u (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [Ne.symm hab]
    · simp
  · split_ifs <;> simp

lemma degLE_S2 {full : Prop} {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup) :
    (net K (S2 full a i c d i' b)).DegLE (q + 1) :=
  degLE_crTwo hK hii (wf_S2 hii ha hb hc hd hdist) (by simp at hdist; tauto)

lemma degLE_S3 {full : Prop} {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup) :
    (net K (S3 full a i c d i' b)).DegLE (q + 1) :=
  degLE_crTwo hK hii (wf_S3 hii ha hb hc hd hdist) (by simp at hdist; tauto)

lemma degLE_S4 (hq : 1 ≤ q) {a b c : V} {i : Fin t} (ha : ¬ IsK K a) (hb : ¬ IsK K b)
    (hc : ¬ IsK K c) (hdist : [a, b, c].Nodup) : (net K (S4 a i b c)).DegLE (q + 1) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hdist
  refine degLE hK (wf_S4 ha hb hc hdist.1.1) (fun v _ => ?_)
  have hin : ∀ v, InCr (S4 a i b c) v ↔ v = a ∨ v = b := by
    intro v
    constructor
    · rintro ⟨j, x, y, h, hv⟩
      obtain ⟨-, rfl, rfl⟩ := crOne_eq_some h
      exact hv
    · intro hv
      exact ⟨i, a, b, by simp [S4, crOne], hv⟩
  refine ⟨if v = c then {a, b} else {c}, ?_, ?_⟩
  · rintro u ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;> simp_all
  · by_cases hvc : v = c
    · subst hvc
      rw [if_pos rfl, if_neg (by rw [hin]; tauto)]
      exact Finset.card_le_two.trans (by omega)
    · rw [if_neg hvc]
      split_ifs <;> simp

end Degree

/-! ### Cliques at the final round -/

lemma clique_S1 (hK : KInj K) {full : Prop} {x y : V} {i : Fin t} (hx : ¬ IsK K x)
    (hy : ¬ IsK K y) (hxy : x ≠ y) :
    ((net K (S1 full x i y)).graph (2 * q * t + 1)).IsNClique (q + 2)
      (Finset.univ.image (K i) ∪ {x, y}) :=
  isNClique_create hK (wf_S1 hx hy hxy) (by simp [S1, crOne]) ⟨rfl, rfl⟩ le_rfl

/-- A node of `I` adjacent to `K j k` is an endpoint of the creation at `j`. -/
lemma index_of_adj_K (hK : KInj K) {sp : Spec V t} (hw : WF K sp) {a : V} (haK : ¬ IsK K a)
    {r : ℕ} {j : Fin t} {k : Fin q} (h : (net K sp).adj r (K j k) a) {i : Fin t} {x y : V}
    (h1 : sp.cr i = some (x, y)) (ha : a = x ∨ a = y) : j = i := by
  have h' := (net K sp).symm _ _ _ h
  rw [adj_K_iff hK hw] at h'
  rcases h' with ⟨k', -, rfl⟩ | ⟨x', y', hc, hh⟩
  · exact absurd ⟨j, k', rfl⟩ haK
  · by_contra hji
    have := hw.cr_disj _ _ _ _ _ _ hji hc h1
    rcases ha with rfl | rfl <;> rcases hh with ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all

/-- No `s`-clique when the final edge joins endpoints of two different creations. -/
lemma no_clique_two (hK : KInj K) {sp : Spec V t} (hw : WF K sp) (hq : 1 ≤ q) {a b : V}
    (hfin : ∀ u v, sp.fin u v → u = a ∧ v = b) {i i' : Fin t} (hii : i ≠ i')
    {x y x' y' : V} (h1 : sp.cr i = some (x, y)) (ha : a = x ∨ a = y)
    (h2 : sp.cr i' = some (x', y')) (hb : b = x' ∨ b = y') (r : ℕ) (Q : Finset V) :
    ¬ ((net K sp).graph r).IsNClique (q + 2) Q := by
  intro hQ
  obtain ⟨u, hu, v, hv, huv, hu', hv', hf⟩ := clique_fin hK hw hQ
  have hab : a ∈ Q ∧ b ∈ Q := by
    rcases hf with hf | hf <;> obtain ⟨rfl, rfl⟩ := hfin _ _ hf
    · exact ⟨hu, hv⟩
    · exact ⟨hv, hu⟩
  have hne : a ≠ b := by
    rcases hf with hf | hf <;> obtain ⟨rfl, rfl⟩ := hfin _ _ hf
    · exact huv
    · exact huv.symm
  have hcard := hQ.card_eq
  obtain ⟨w, hw', hwa, hwb⟩ : ∃ w ∈ Q, w ≠ a ∧ w ≠ b := by
    by_contra hcon
    push_neg at hcon
    have : Q ⊆ {a, b} := fun w hw' => by
      by_cases h : w = a
      · simp [h]
      · simp [hcon w hw' h]
    have := Finset.card_le_card this
    have := Finset.card_le_two (a := a) (b := b)
    omega
  have hwa' : (net K sp).adj r w a := hQ.isClique hw' hab.1 hwa
  have hwb' : (net K sp).adj r w b := hQ.isClique hw' hab.2 hwb
  have haK : ¬ IsK K a := by
    rcases ha with rfl | rfl
    · exact (hw.cr_I _ _ _ h1).1
    · exact (hw.cr_I _ _ _ h1).2.1
  by_cases hwK : IsK K w
  · obtain ⟨j, k, rfl⟩ := hwK
    have hbK : ¬ IsK K b := by
      rcases hb with rfl | rfl
      · exact (hw.cr_I _ _ _ h2).1
      · exact (hw.cr_I _ _ _ h2).2.1
    exact hii ((index_of_adj_K hK hw haK hwa' h1 ha).symm.trans (index_of_adj_K hK hw hbK hwb' h2 hb))
  · rw [adj_I_iff _ _ _ haK] at hwa'
    rcases hwa' with ⟨j, x, y, k, -, rfl, -⟩ | ⟨-, -, hf | hf⟩
    · exact hwK ⟨j, k, rfl⟩
    · exact hwa (hfin _ _ hf).1
    · exact hwb (hfin _ _ hf).2


section NoClique

variable (hK : KInj K) (hq : 1 ≤ q) {a b c d : V} {i i' : Fin t} (hii : i ≠ i')
  (ha : ¬ IsK K a) (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d)
include hK hq hii ha hb hc hd

lemma no_clique_S2 {full : Prop} (hdist : [a, b, c, d].Nodup) (r : ℕ) (Q : Finset V) :
    ¬ ((net K (S2 full a i c d i' b)).graph r).IsNClique (q + 2) Q :=
  no_clique_two hK (wf_S2 hii ha hb hc hd hdist) hq (fun _ _ h => h) hii
    (show (S2 full a i c d i' b).cr i = some (a, c) by simp [S2, crTwo]) (Or.inl rfl)
    (show (S2 full a i c d i' b).cr i' = some (d, b) by simp [S2, crTwo, Ne.symm hii]) (Or.inr rfl) r Q

lemma no_clique_S3 {full : Prop} (hdist : [a, b, c, d].Nodup) (r : ℕ) (Q : Finset V) :
    ¬ ((net K (S3 full a i c d i' b)).graph r).IsNClique (q + 2) Q :=
  no_clique_two hK (wf_S3 hii ha hb hc hd hdist) hq (fun _ _ h => h) (Ne.symm hii)
    (show (S3 full a i c d i' b).cr i' = some (a, c) by simp [S3, crTwo, Ne.symm hii]) (Or.inl rfl)
    (show (S3 full a i c d i' b).cr i = some (d, b) by simp [S3, crTwo]) (Or.inr rfl) r Q

end NoClique

lemma no_clique_S4 (hK : KInj K) (hq : 1 ≤ q) {a b c : V} {i : Fin t} (ha : ¬ IsK K a) (hb : ¬ IsK K b)
    (hc : ¬ IsK K c) (hdist : [a, b, c].Nodup) (r : ℕ) (Q : Finset V) :
    ¬ ((net K (S4 a i b c)).graph r).IsNClique (q + 2) Q := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hdist
  have hw := wf_S4 (i := i) ha hb hc hdist.1.1
  intro hQ
  obtain ⟨u, hu, v, hv, huv, -, -, hf⟩ := clique_fin hK hw hQ
  have hcQ : c ∈ Q := by
    rcases hf with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> assumption
  -- every other member of `Q` is a neighbour of `c`, i.e. `a` or `b`
  have hnb : ∀ z ∈ Q, z = a ∨ z = b ∨ z = c := by
    intro z hz
    by_cases hzc : z = c
    · exact Or.inr (Or.inr hzc)
    have hadj : (net K (S4 a i b c)).adj r z c := hQ.isClique hz hcQ hzc
    rw [adj_I_iff _ _ _ hc] at hadj
    rcases hadj with ⟨j, x, y, k, hj, -, h | h⟩ | ⟨-, -, hf⟩
    · obtain ⟨-, rfl, -⟩ := crOne_eq_some hj; exact absurd h.1.symm hdist.1.2
    · obtain ⟨-, -, rfl⟩ := crOne_eq_some hj; exact absurd h.1.symm hdist.2
    · rcases hf with (⟨rfl, -⟩ | ⟨rfl, -⟩) | (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd h.symm hdist.1.2
      · exact absurd h.symm hdist.2
  have hsub : Q ⊆ {a, b, c} := fun z hz => by
    rcases hnb z hz with rfl | rfl | rfl <;> simp
  have hcard := hQ.card_eq
  have haQ : a ∈ Q := by
    by_contra haQ
    have : Q ⊆ {b, c} := fun z hz => by
      rcases hnb z hz with rfl | rfl | rfl
      · exact absurd hz haQ
      · simp
      · simp
    have := Finset.card_le_card this
    have := Finset.card_le_two (a := b) (b := c)
    omega
  have hbQ : b ∈ Q := by
    by_contra hbQ
    have : Q ⊆ {a, c} := fun z hz => by
      rcases hnb z hz with rfl | rfl | rfl
      · simp
      · exact absurd hz hbQ
      · simp
    have := Finset.card_le_card this
    have := Finset.card_le_two (a := a) (b := c)
    omega
  have hab : (net K (S4 a i b c)).adj r a b := hQ.isClique haQ hbQ hdist.1.1
  rw [adj_I_iff _ _ _ hb] at hab
  rcases hab with ⟨j, x, y, k, -, rfl, -⟩ | ⟨-, -, hf⟩
  · exact ha ⟨j, k, rfl⟩
  · rcases hf with (⟨-, h⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨-, h⟩)
    · exact hdist.2 h
    · exact hdist.1.1 h
    · exact hdist.1.1 h.symm
    · exact hdist.1.2 h

end Hard

end Podc.DynamicSubgraphFinding
