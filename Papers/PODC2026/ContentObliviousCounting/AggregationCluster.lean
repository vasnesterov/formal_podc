import Papers.PODC2026.ContentObliviousCounting.AggregationMIS

/-!
# One aggregation step: clusters around an MIS of a virtual ring

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, step 3 of the proof of Theorem 1.

Every active node `p` owns a *cluster* `{u | o u = p}` and holds the encoding `E X` of the
aggregate of the multiset `X` of the inputs of its cluster. Given an MIS `M` of the virtual ring,
a node outside `M` joins the cluster of its clockwise neighbour if that neighbour is in `M`,
otherwise of its counter-clockwise neighbour (`cen`); the centres combine the received values
(`combine`). `combine_eq`: every centre then holds the encoding of the aggregate of its new
cluster. `card_mis_le`: an MIS of a virtual ring of `m ≥ 2` nodes has at most `m / 2` nodes.
-/

namespace Podc.ContentOblivious.Aggregation

open Finset

variable {V U : Type*} [Fintype V] [DecidableEq V] {act : V → Bool} {nxt prv : V → V}
  {M : V → Bool}

omit [Fintype V] [DecidableEq V] in
lemma filter_or_eq_add {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    {s : Multiset α} (h : ∀ a ∈ s, ¬ (p a ∧ q a)) :
    Multiset.filter (fun a => p a ∨ q a) s = Multiset.filter p s + Multiset.filter q s := by
  rw [Multiset.filter_add_filter, Multiset.filter_eq_nil.2 h, add_zero]

/-- The cluster centre chosen by an active node. -/
def cen (M : V → Bool) (nxt prv : V → V) (p : V) : V :=
  if M p then p else if M (nxt p) then nxt p else prv p

/-- The multiset of inputs of the cluster of `p` (owner map `o`). -/
def clusterVals (val : V → U) (o : V → V) (p : V) : Multiset U :=
  ((univ.filter fun u => o u = p).val).map val

omit [Fintype V] [DecidableEq V] in
lemma cen_eq_iff (hR : RingAx act nxt prv)
    {c p : V} (hc : act c = true) (hMc : M c = true) (hp : act p = true) :
    cen M nxt prv p = c ↔ p = c ∨ (p = prv c ∧ M (prv c) = false) ∨
      (p = nxt c ∧ M (nxt c) = false ∧ M (nxt (nxt c)) = false) := by
  unfold cen
  constructor
  · intro h
    cases h1 : M p
    · cases h2 : M (nxt p)
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
        subst h
        right; right
        rw [hR.nxt_prv p hp]; exact ⟨rfl, h1, h2⟩
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
        subst h
        right; left
        rw [hR.prv_nxt p hp]; exact ⟨rfl, h1⟩
    · simp only [h1, ↓reduceIte] at h; exact Or.inl h
  · rintro (rfl | ⟨rfl, h1⟩ | ⟨rfl, h1, h2⟩)
    · simp [hMc]
    · simp [h1, hR.nxt_prv c hc, hMc]
    · simp [h1, h2, hR.prv_nxt c hc]

omit [Fintype V] [DecidableEq V] in
lemma act_cen (hR : RingAx act nxt prv)
    (hdom : ∀ v, act v = true → M v = false → M (prv v) = true ∨ M (nxt v) = true)
    {p : V} (hp : act p = true) : act (cen M nxt prv p) = true ∧ M (cen M nxt prv p) = true := by
  unfold cen
  cases h1 : M p
  · cases h2 : M (nxt p)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hdom p hp h1 with h | h
      · exact ⟨hR.prv_act p hp, h⟩
      · rw [h] at h2; cases h2
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hR.nxt_act p hp, h2⟩
  · simp only [↓reduceIte]; exact ⟨hp, h1⟩

omit [Fintype V] [DecidableEq V] in
lemma cen_self {p : V} (hMp : M p = true) : cen M nxt prv p = p := by
  simp [cen, hMp]

/-- The new cluster of a centre `c` is the union of the old clusters of `c` and of the neighbours
that chose `c`. -/
lemma clusterVals_cen (hR : RingAx act nxt prv)
    (val : V → U) {o : V → V} (ho : ∀ u, act (o u) = true) {c : V} (hc : act c = true)
    (hMc : M c = true) :
    clusterVals val (fun u => cen M nxt prv (o u)) c =
      (if M (prv c) = false then clusterVals val o (prv c) else 0) +
        (clusterVals val o c +
          (if M (nxt c) = false ∧ M (nxt (nxt c)) = false then clusterVals val o (nxt c)
            else 0)) := by
  have hpc : prv c ≠ c := hR.prv_ne c hc
  have hnc : nxt c ≠ c := hR.nxt_ne c hc
  have hpn : nxt (prv c) = c := hR.nxt_prv c hc
  unfold clusterVals
  simp only [Finset.filter_val]
  have key : ∀ u, (cen M nxt prv (o u) = c) ↔
      (o u = prv c ∧ M (prv c) = false) ∨ (o u = c ∨
        (o u = nxt c ∧ M (nxt c) = false ∧ M (nxt (nxt c)) = false)) := by
    intro u
    rw [cen_eq_iff hR hc hMc (ho u)]
    tauto
  rw [Multiset.filter_congr (fun u _ => key u)]
  have e1 : ∀ s : Multiset V, Multiset.filter (fun u => (o u = prv c ∧ M (prv c) = false) ∨
      (o u = c ∨ (o u = nxt c ∧ M (nxt c) = false ∧ M (nxt (nxt c)) = false))) s =
      Multiset.filter (fun u => o u = prv c ∧ M (prv c) = false) s +
        (Multiset.filter (fun u => o u = c) s +
          Multiset.filter (fun u => o u = nxt c ∧ M (nxt c) = false ∧
            M (nxt (nxt c)) = false) s) := by
    intro s
    rw [filter_or_eq_add (by
          rintro u - ⟨⟨h1, -⟩, h2 | ⟨h2, -, h3⟩⟩
          · exact hpc (h1.symm.trans h2)
          · have : nxt c = prv c := h2.symm.trans h1
            rw [this, hpn, hMc] at h3; cases h3),
      filter_or_eq_add (by
          rintro u - ⟨h1, h2, -⟩
          exact hnc (h2.symm.trans h1))]
  rw [e1, Multiset.map_add, Multiset.map_add]
  congr 1
  · split_ifs with h
    · simp [h]
    · simp only [Bool.not_eq_false] at h
      rw [Multiset.filter_eq_nil.2 (fun u _ hu => by rw [hu.2] at h; cases h)]; simp
  · congr 1
    split_ifs with h
    · simp [h]
    · rw [Multiset.filter_eq_nil.2 (fun u _ hu => h ⟨hu.2.1, hu.2.2⟩)]; simp

lemma clusterVals_ne_zero (val : V → U) {o : V → V} {p : V} (hp : o p = p) :
    clusterVals val o p ≠ 0 := by
  unfold clusterVals
  intro h
  have : p ∈ (univ.filter fun u => o u = p) := by simp [hp]
  rw [Multiset.map_eq_zero, Finset.val_eq_zero] at h
  rw [h] at this; simp at this

/-- After the aggregation round of `misAlg`, every centre holds the encoding of the aggregate
of its new cluster. -/
lemma combine_eq (hR : RingAx act nxt prv)
    (hindep : ∀ v, act v = true → M v = true → M (nxt v) = false)
    (op2 : List Bool → List Bool → List Bool) (E : Multiset U → List Bool)
    (hop2 : ∀ X Y, X ≠ 0 → Y ≠ 0 → op2 (E X) (E Y) = E (X + Y))
    (val : V → U) {o : V → V} (ho : ∀ u, act (o u) = true) (hoself : ∀ p, act p = true → o p = p)
    {w : V → List Bool} (hw : ∀ p, act p = true → w p = E (clusterVals val o p))
    {c : V} (hc : act c = true) (hMc : M c = true) :
    combine op2 (aggMsg (M (prv c)) (M (nxt (prv c))) (w (prv c))).1
        (aggMsg (M (nxt c)) (M (nxt (nxt c))) (w (nxt c))).2 (w c) =
      E (clusterVals val (fun u => cen M nxt prv (o u)) c) := by
  have hpa := hR.prv_act c hc
  have hna := hR.nxt_act c hc
  have hpn : nxt (prv c) = c := hR.nxt_prv c hc
  rw [clusterVals_cen hR val ho hc hMc, hpn, hMc]
  have ne : ∀ p, act p = true → clusterVals val o p ≠ 0 :=
    fun p hp => clusterVals_ne_zero val (hoself p hp)
  unfold combine aggMsg
  have hnn := hindep c hc hMc
  rw [hw c hc, hw _ hpa, hw _ hna]
  rcases hP : M (prv c) <;> rcases hN2 : M (nxt (nxt c)) <;>
    simp [hnn, hop2, ne _ hpa, ne _ hc, ne _ hna, add_eq_zero]

omit [DecidableEq V] in
/-- An independent set of a virtual ring has at most half of its nodes. -/
lemma card_mis_le (hR : RingAx act nxt prv)
    (hindep : ∀ v, act v = true → M v = true → M (nxt v) = false) :
    2 * (univ.filter fun v => act v = true ∧ M v = true).card ≤
      (univ.filter fun v => act v = true).card := by
  have h1 : (univ.filter fun v => act v = true ∧ M v = true).card ≤
      (univ.filter fun v => act v = true ∧ M v = false).card := by
    refine Finset.card_le_card_of_injOn nxt ?_ ?_
    · intro v hv
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
      exact ⟨hR.nxt_act v hv.1, hindep v hv.1 hv.2⟩
    · intro v hv w hw h
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
      rw [← hR.prv_nxt v hv.1, ← hR.prv_nxt w hw.1, h]
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun v => act v = true)
    (fun v => M v = true)
  simp only [Finset.filter_filter, Bool.not_eq_true] at h2
  omega

end Podc.ContentOblivious.Aggregation
