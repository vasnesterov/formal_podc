import Papers.PODC2011.LocallyCheckableProofs.Theorem51

/-!
# Theorem 5.1 for graph problems with edge labels: spanning trees

The marked edges `S` of a labelled cycle correspond to the marked nodes (`card_edgeSet_cyc`), so the
glued `2n`-cycle of two spanning paths carries `2n - 2` marked edges and cannot be a spanning tree.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset Filter Asymptotics

variable {L : Type*}

/-- The marked edges of a labelled cycle are the edges `{x, nxt x}` of the marked nodes `x`. -/
lemma card_edgeSet_cyc {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length) (lab : ℕ → L)
    (mk : ℕ → Bool) :
    Nat.card (cyc l lab mk).S.edgeSet = (l.toFinset.filter fun x => mk x = true).card := by
  classical
  set f : ℕ → Sym2 ℕ := fun x => s(x, nxt l x)
  have hset : (cyc l lab mk).S.edgeSet = ↑((l.toFinset.filter fun x => mk x = true).image f) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
    simp only [mem_edgeSet, cyc_sadj, Finset.coe_image, Finset.coe_filter, List.mem_toFinset,
      Set.mem_image, Set.mem_setOf_eq, f]
    constructor
    · rintro ⟨-, ⟨hs, hm⟩ | ⟨hs, hm⟩⟩
      · obtain ⟨hu, rfl⟩ := (succ_iff_nxt hl).1 hs
        exact ⟨u, ⟨hu, hm⟩, rfl⟩
      · obtain ⟨hv, rfl⟩ := (succ_iff_nxt hl).1 hs
        exact ⟨v, ⟨hv, hm⟩, Sym2.eq_swap⟩
    · rintro ⟨x, ⟨hx, hm⟩, he⟩
      have hs : Succ l x (nxt l x) := (succ_iff_nxt hl).2 ⟨hx, rfl⟩
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hs.ne hl (by omega), Or.inl ⟨hs, hm⟩⟩
      · exact ⟨(hs.ne hl (by omega)).symm, Or.inr ⟨hs, hm⟩⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  refine Finset.card_image_of_injOn fun x hx y hy he => ?_
  simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq] at hx hy
  by_contra hne
  rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hne h1
  · -- `x = nxt y` and `y = nxt x`: impossible on a cycle of length `≥ 3`
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx.1
    have e1 : nxt l l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
      rw [nxt, hl.idxOf_getElem, List.getD_eq_getElem]
    rw [e1] at h2
    have e2 : nxt l (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))) =
        l[((i + 1) % l.length + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
      rw [nxt, hl.idxOf_getElem, List.getD_eq_getElem]
    rw [← h2, e2] at h1
    have := (List.Nodup.getElem_inj_iff hl).1 h1
    rcases Nat.lt_or_ge (i + 1) l.length with h | h
    · rw [Nat.mod_eq_of_lt h] at this
      rcases Nat.lt_or_ge (i + 2) l.length with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at this; omega
      · rw [show i + 1 + 1 = l.length by omega, Nat.mod_self] at this; omega
    · rw [show i + 1 = l.length by omega, Nat.mod_self, zero_add,
        Nat.mod_eq_of_lt (by omega)] at this
      omega

/-- The edges of `S` restricted to the nodes: same number as the edges of `S`. -/
lemma card_edgeSet_induce (I : Inst L) :
    Nat.card (I.S.induce (I.V : Set ℕ)).edgeSet = Nat.card I.S.edgeSet := by
  refine Nat.card_eq_of_bijective (Embedding.induce (G := I.S) (I.V : Set ℕ)).mapEdgeSet
    ⟨(Embedding.mapEdgeSet _).injective, ?_⟩
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
  have hu : u ∈ I.V := I.sub (I.S_le he)
  have hv : v ∈ I.V := I.sub' (I.S_le he)
  refine ⟨⟨s(⟨u, hu⟩, ⟨v, hv⟩), by simpa using he⟩, ?_⟩
  simp [Embedding.mapEdgeSet, Hom.mapEdgeSet]

/-- The spanning tree problem: the marked edges form a spanning tree of the nodes. -/
def SpanningTree : Set (Inst L) := {I | (I.S.induce (I.V : Set ℕ)).IsTree}

/-- A spanning tree of a labelled cycle has `n - 1` marked nodes. -/
lemma marks_of_spanningTree {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length) {lab : ℕ → L}
    {mk : ℕ → Bool} (h : cyc l lab mk ∈ SpanningTree) :
    (l.toFinset.filter fun x => mk x = true).card + 1 = l.length := by
  have := (isTree_iff_connected_and_card.1 h).2
  rw [card_edgeSet_induce, card_edgeSet_cyc hl h3] at this
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset, cyc_V, List.toFinset_card_of_nodup hl]

/-- Family hypothesis for graph problems with edge labels: all cycles with identifiers in
`{1,…,n²}` and arbitrary labels and marked edges. -/
def CycleFamily (F : Set (Inst L)) : Prop := ∀ I : Inst L, I.IsCycle → I.IdBound 2 → I ∈ F

/-- **Theorem 5.1 (spanning trees).** On any family of graphs with edge labels containing all
cycles (identifiers in `{1,…,n²}`), every weak (hence every strong) proof labelling scheme for
spanning trees has size `s(n) ≥ c log n - C`; in particular `s ≠ o(log n)`. -/
theorem theorem_5_1_spanningTree {F : Set (Inst Unit)} (hF : CycleFamily F) {s : ℕ → ℕ}
    (h : AdmitsWeakLCP F SpanningTree s) :
    (∃ c > (0 : ℝ), ∃ C : ℝ, ∀ n : ℕ, c * Real.log n - C ≤ s n) ∧
      ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) := by
  classical
  obtain ⟨r, hr⟩ := lowerBound_bound (fun _ => True) h
    (fun n hn _ a b => by
      have hnd := (goodLists_blk n).nodup_lst a b
      have hlen := lstN_length n a b
      unfold lstN at hlen
      set l := lst (blkA n) (blkB n) a b
      let xl := l[l.length - 1]'(by omega)
      -- the spanning path: all edges but the last one
      let mk : ℕ → Bool := fun x => decide (x ≠ xl)
      refine ⟨cyc l (fun _ => ()) mk, hF _ (cyc_isCycle hnd (by omega) _ _)
          (cyc_idBound hnd _ _ fun x hx => by rw [hlen]; exact mem_lstN_bound hx), ?_, rfl, rfl⟩
      rw [SpanningTree, Set.mem_setOf_eq, isTree_iff_connected_and_card]
      constructor
      · -- connected: walk along the list
        have hadj : ∀ (i : ℕ) (hi : i + 1 < l.length), (cyc l (fun _ => ()) mk).S.Adj l[i] l[i + 1] :=
          fun i hi => by
            rw [cyc_sadj]
            refine ⟨fun he => ?_, Or.inl ⟨⟨i, by omega, rfl, by simp [Nat.mod_eq_of_lt hi]⟩, ?_⟩⟩
            · have := (List.Nodup.getElem_inj_iff hnd).1 he; omega
            · simp only [mk, xl, ne_eq, decide_eq_true_eq]
              intro he
              have := (List.Nodup.getElem_inj_iff hnd).1 he; omega
        have hmem : ∀ (i : ℕ) (hi : i < l.length), l[i] ∈ ((cyc l (fun _ => ()) mk).V : Set ℕ) :=
          fun i hi => by simp [List.getElem_mem]
        have hreach : ∀ (i : ℕ) (hi : i < l.length),
            ((cyc l (fun _ => ()) mk).S.induce ((cyc l (fun _ => ()) mk).V : Set ℕ)).Reachable
              ⟨l[0]'(by omega), hmem 0 (by omega)⟩ ⟨l[i], hmem i hi⟩ := by
          intro i
          induction i with
          | zero => intro _; rfl
          | succ i ih =>
            intro hi
            exact (ih (by omega)).trans (Adj.reachable (by rw [induce_adj]; exact hadj i hi))
        haveI : Nonempty ((cyc l (fun _ => ()) mk).V : Set ℕ) :=
          ⟨⟨l[0]'(by omega), hmem 0 (by omega)⟩⟩
        refine ⟨fun u v => ?_⟩
        · obtain ⟨u, hu⟩ := u
          obtain ⟨v, hv⟩ := v
          simp only [cyc_V, Finset.coe_sort_coe, List.coe_toFinset, Set.mem_setOf_eq,
            List.mem_toFinset] at hu hv
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
          exact (hreach i hi).symm.trans (hreach j hj)
      · rw [card_edgeSet_induce, card_edgeSet_cyc hnd (by omega), Nat.card_coe_set_eq,
          Set.ncard_coe_finset, cyc_V, List.toFinset_card_of_nodup hnd]
        have : (l.toFinset.filter fun x => mk x = true) = l.toFinset.erase xl := by
          ext x; simp [mk, and_comm]
        rw [this, Finset.card_erase_of_mem (by simp [xl, List.getElem_mem]),
          List.toFinset_card_of_nodup hnd]
        omega)
    (fun n hn _ lab mk hpieces a₁ a₂ b₁ b₂ ha hb => ⟨hF _ (glued_isCycle (by omega) ha hb)
      (glued_idBound ha hb), by
        intro hP
        have hG := goodLists_blk n
        have hm1 := marks_of_spanningTree (hG.nodup_lst a₁ b₁)
          (by have := lstN_length n a₁ b₁; unfold lstN at this; omega) (hpieces a₁ b₁).2
        have hm2 := marks_of_spanningTree (hG.nodup_lst a₂ b₂)
          (by have := lstN_length n a₂ b₂; unfold lstN at this; omega) (hpieces a₂ b₂).2
        have hgl := marks_of_spanningTree (glued_nodup ha hb)
          (by rw [glued_length]; omega) hP
        rw [glued_length, List.toFinset_append, Finset.filter_union,
          Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (glued_disjoint ha hb))]
          at hgl
        have e1 : ((lstN n a₁ b₁).toFinset.filter fun v =>
            piece (lst (blkA n) (blkB n) a₁ b₁) (mk a₁ b₁) (mk a₂ b₂) v = true) =
            ((lstN n a₁ b₁).toFinset.filter fun v => mk a₁ b₁ v = true) := by
          refine Finset.filter_congr fun v hv => ?_
          rw [piece_of_mem (List.mem_toFinset.1 hv)]
        have e2 : ((lstN n a₂ b₂).toFinset.filter fun v =>
            piece (lst (blkA n) (blkB n) a₁ b₁) (mk a₁ b₁) (mk a₂ b₂) v = true) =
            ((lstN n a₂ b₂).toFinset.filter fun v => mk a₂ b₂ v = true) := by
          refine Finset.filter_congr fun v hv => ?_
          have : v ∉ lst (blkA n) (blkB n) a₁ b₁ := fun h' =>
            Finset.disjoint_left.1 (glued_disjoint ha hb) (List.mem_toFinset.2 h') hv
          rw [piece_of_not_mem this]
        rw [e1, e2] at hgl
        have l1 := lstN_length n a₁ b₁
        have l2 := lstN_length n a₂ b₂
        unfold lstN at l1 l2 hm1 hm2 hgl e1 e2
        omega⟩)
  obtain ⟨c, hc, C, hC⟩ := logBound_of_bound (M := 1) le_rfl
    (fun n hn _ => by simpa using hr n hn trivial)
  exact ⟨⟨c, hc, C, fun n => hC n trivial⟩, not_isLittleO_log hc (fun n _ => hC n trivial)
    (Filter.Frequently.of_forall fun _ => trivial)⟩

end Podc.LocallyCheckableProofs

/-! ### Maximum matchings on cycles -/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset Filter Asymptotics

variable {L : Type*}

lemma nxt_getElem {l : List ℕ} (hl : l.Nodup) (i : ℕ) (hi : i < l.length) :
    nxt l l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  rw [nxt, hl.idxOf_getElem, List.getD_eq_getElem]

lemma nxt_mem {l : List ℕ} (hl : l.Nodup) {x : ℕ} (hx : x ∈ l) : nxt l x ∈ l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [nxt_getElem hl]; exact List.getElem_mem _

lemma nxt_injOn {l : List ℕ} (hl : l.Nodup) {x y : ℕ} (hx : x ∈ l) (hy : y ∈ l)
    (h : nxt l x = nxt l y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  rw [nxt_getElem hl, nxt_getElem hl] at h
  have := (List.Nodup.getElem_inj_iff hl).1 h
  have : i = j := by
    rcases Nat.lt_or_ge (i + 1) l.length with h1 | h1 <;>
    rcases Nat.lt_or_ge (j + 1) l.length with h2 | h2
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this; omega
    · rw [Nat.mod_eq_of_lt h1, show j + 1 = l.length by omega, Nat.mod_self] at this; omega
    · rw [Nat.mod_eq_of_lt h2, show i + 1 = l.length by omega, Nat.mod_self] at this; omega
    · omega
  subst this; rfl

lemma nxt_nxt_ne {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length) {x : ℕ} (hx : x ∈ l) :
    nxt l (nxt l x) ≠ x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [nxt_getElem hl, nxt_getElem hl]
  intro h
  have := (List.Nodup.getElem_inj_iff hl).1 h
  rcases Nat.lt_or_ge (i + 1) l.length with h | h
  · rw [Nat.mod_eq_of_lt h] at this
    rcases Nat.lt_or_ge (i + 2) l.length with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at this; omega
    · rw [show i + 1 + 1 = l.length by omega, Nat.mod_self] at this; omega
  · rw [show i + 1 = l.length by omega, Nat.mod_self, zero_add,
      Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- `M` is a matching: every node has at most one `M`-neighbour. -/
def IsMatching (M : SimpleGraph ℕ) : Prop := ∀ ⦃x y z : ℕ⦄, M.Adj x y → M.Adj x z → y = z

/-- Maximum matching: the marked edges form a matching of maximum size among the matchings of
the graph. -/
def MaxMatching : Set (Inst L) :=
  {I | IsMatching I.S ∧ ∀ M ≤ I.G, IsMatching M → Nat.card M.edgeSet ≤ Nat.card I.S.edgeSet}

/-- A matching of a labelled cycle has no two consecutive marked nodes, so at most `n/2` marks. -/
lemma two_mul_marks_le {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length) {lab : ℕ → L}
    {mk : ℕ → Bool} (hM : IsMatching (cyc l lab mk).S) :
    2 * (l.toFinset.filter fun x => mk x = true).card ≤ l.length := by
  classical
  set Mk := l.toFinset.filter fun x => mk x = true
  set U := l.toFinset.filter fun x => mk x = false
  have hsum : Mk.card + U.card = l.length := by
    rw [← List.toFinset_card_of_nodup hl, ← Finset.card_union_of_disjoint]
    · congr 1; ext x; simp [Mk, U]; cases mk x <;> simp
    · exact Finset.disjoint_filter.2 fun x _ h1 h2 => by simp_all
  have hle : Mk.card ≤ U.card := by
    refine Finset.card_le_card_of_injOn (nxt l) (fun x hx => ?_) (fun x hx y hy h => ?_)
    · have hx' : x ∈ l ∧ mk x = true := by simpa [Mk] using hx
      clear hx
      have hx := hx'
      refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 (nxt_mem hl hx.1), ?_⟩
      by_contra hm
      have hs1 : Succ l x (nxt l x) := (succ_iff_nxt hl).2 ⟨hx.1, rfl⟩
      have hs2 : Succ l (nxt l x) (nxt l (nxt l x)) := (succ_iff_nxt hl).2 ⟨nxt_mem hl hx.1, rfl⟩
      have a1 : (cyc l lab mk).S.Adj (nxt l x) x := by
        rw [cyc_sadj]; exact ⟨(hs1.ne hl (by omega)).symm, Or.inr ⟨hs1, hx.2⟩⟩
      have a2 : (cyc l lab mk).S.Adj (nxt l x) (nxt l (nxt l x)) := by
        rw [cyc_sadj]; exact ⟨hs2.ne hl (by omega), Or.inl ⟨hs2, by simpa using hm⟩⟩
      exact nxt_nxt_ne hl h3 hx.1 (hM a1 a2).symm
    · simp only [Mk, Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq] at hx hy
      exact nxt_injOn hl hx.1 hy.1 h
  omega

/-- Every matching of the cycle on `l` has at most `|l|/2` edges. -/
lemma two_mul_card_matching_le {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length)
    {M : SimpleGraph ℕ} (hMG : M ≤ cycGraph l) (hM : IsMatching M) :
    2 * Nat.card M.edgeSet ≤ l.length := by
  let J : Inst Unit := { cyc l (fun _ => ()) (fun _ => false) with S := M, S_le := hMG }
  have hJ := eq_cyc hl J rfl rfl
  have hS : M = (cyc l J.lab (markOf J l)).S := by
    have := congrArg Inst.S hJ; exact this
  rw [hS, card_edgeSet_cyc hl h3]
  exact two_mul_marks_le hl h3 (hS ▸ hM)

/-- The alternating marks: positions `0, 2, 4, …` (but not the last position). -/
def altMarks (l : List ℕ) (x : ℕ) : Bool := decide (l.idxOf x % 2 = 0 ∧ l.idxOf x + 1 < l.length)

lemma isMatching_alt {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length) (lab : ℕ → L) :
    IsMatching (cyc l lab (altMarks l)).S := by
  -- the predecessor is unique
  have succ_left : ∀ {y z x : ℕ}, Succ l y x → Succ l z x → y = z := by
    intro y z x hy hz
    obtain ⟨hy', rfl⟩ := (succ_iff_nxt hl).1 hy
    obtain ⟨hz', he⟩ := (succ_iff_nxt hl).1 hz
    exact nxt_injOn hl hy' hz' he
  have key : ∀ {x z : ℕ}, Succ l z x → altMarks l z = true → altMarks l x = false := by
    intro x z hs hz
    obtain ⟨i, hi, rfl, rfl⟩ := hs
    simp only [altMarks, decide_eq_true_eq, hl.idxOf_getElem, decide_eq_false_iff_not,
      not_and] at hz ⊢
    rw [Nat.mod_eq_of_lt hz.2]
    omega
  intro x y z hy hz
  rw [cyc_sadj] at hy hz
  rcases hy with ⟨-, ⟨hs1, hm1⟩ | ⟨hs1, hm1⟩⟩ <;> rcases hz with ⟨-, ⟨hs2, hm2⟩ | ⟨hs2, hm2⟩⟩
  · obtain ⟨-, rfl⟩ := (succ_iff_nxt hl).1 hs1
    obtain ⟨-, rfl⟩ := (succ_iff_nxt hl).1 hs2; rfl
  · rw [key hs2 hm2] at hm1; exact absurd hm1 (by simp)
  · rw [key hs1 hm1] at hm2; exact absurd hm2 (by simp)
  · exact succ_left hs1 hs2

lemma card_altMarks {l : List ℕ} (hl : l.Nodup) :
    (l.toFinset.filter fun x => altMarks l x = true).card = l.length / 2 := by
  classical
  have hinj : Set.InjOn (fun x => l.idxOf x) (l.toFinset.filter fun x => altMarks l x = true) := by
    intro x hx y hy h
    simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq] at hx hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx.1
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy.1
    simp only [hl.idxOf_getElem] at h
    subst h; rfl
  rw [← Finset.card_image_of_injOn hinj]
  have : (l.toFinset.filter fun x => altMarks l x = true).image (fun x => l.idxOf x) =
      (Finset.range (l.length / 2)).image (fun k => 2 * k) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset, Finset.mem_range, altMarks,
      decide_eq_true_eq]
    constructor
    · rintro ⟨x, ⟨hx, h1, h2⟩, rfl⟩
      exact ⟨l.idxOf x / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨l[2 * k]'(by omega), ⟨List.getElem_mem _, ?_⟩, hl.idxOf_getElem _ _⟩
      rw [hl.idxOf_getElem]; omega
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]

lemma card_edgeSet_alt {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length) (lab : ℕ → L) :
    Nat.card (cyc l lab (altMarks l)).S.edgeSet = l.length / 2 := by
  rw [card_edgeSet_cyc hl h3, card_altMarks hl]

/-- A maximum matching of an odd cycle has `(n-1)/2` marks. -/
lemma marks_of_maxMatching {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length) {lab : ℕ → L}
    {mk : ℕ → Bool} (h : cyc l lab mk ∈ MaxMatching) :
    (l.toFinset.filter fun x => mk x = true).card = l.length / 2 := by
  have h1 := two_mul_marks_le hl h3 h.1
  have h2 := h.2 _ (cyc l lab (altMarks l)).S_le (isMatching_alt hl h3 lab)
  rw [card_edgeSet_alt hl h3, card_edgeSet_cyc hl h3] at h2
  omega

/-- **Theorem 5.1 (maximum matching on cycles, Section 5.4).** On any family containing all cycles
with edge labels (identifiers in `{1,…,n²}`), every weak (hence every strong) proof labelling scheme
for maximum matchings has size `s(n) ≥ c log n - C` for all odd `n`; in particular
`s ≠ o(log n)`. -/
theorem theorem_5_1_maxMatching {F : Set (Inst Unit)} (hF : CycleFamily F) {s : ℕ → ℕ}
    (h : AdmitsWeakLCP F MaxMatching s) :
    (∃ c > (0 : ℝ), ∃ C : ℝ, ∀ n : ℕ, Odd n → c * Real.log n - C ≤ s n) ∧
      ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) := by
  classical
  obtain ⟨r, hr⟩ := lowerBound_bound (fun n => Odd n) h
    (fun n hn _ a b => by
      have hnd := (goodLists_blk n).nodup_lst a b
      have hlen := lstN_length n a b
      unfold lstN at hlen
      refine ⟨cyc _ (fun _ => ()) (altMarks (lst (blkA n) (blkB n) a b)),
        hF _ (cyc_isCycle hnd (by omega) _ _)
          (cyc_idBound hnd _ _ fun x hx => by rw [hlen]; exact mem_lstN_bound hx),
        ⟨isMatching_alt hnd (by omega) _, fun M hM hMm => ?_⟩, rfl, rfl⟩
      have := two_mul_card_matching_le hnd (by omega) hM hMm
      rw [card_edgeSet_alt hnd (by omega)]
      omega)
    (fun n hn hodd lab mk hpieces a₁ a₂ b₁ b₂ ha hb => ⟨hF _ (glued_isCycle (by omega) ha hb)
      (glued_idBound ha hb), by
        intro hP
        have hG := goodLists_blk n
        have hm1 := marks_of_maxMatching (hG.nodup_lst a₁ b₁)
          (by have := lstN_length n a₁ b₁; unfold lstN at this; omega) (hpieces a₁ b₁).2
        have hm2 := marks_of_maxMatching (hG.nodup_lst a₂ b₂)
          (by have := lstN_length n a₂ b₂; unfold lstN at this; omega) (hpieces a₂ b₂).2
        have hgl := hP.2 _ (cyc (lstN n a₁ b₁ ++ lstN n a₂ b₂) (fun _ => ())
          (altMarks (lstN n a₁ b₁ ++ lstN n a₂ b₂))).S_le
          (isMatching_alt (glued_nodup ha hb) (by rw [glued_length]; omega) _)
        rw [card_edgeSet_alt (glued_nodup ha hb) (by rw [glued_length]; omega), glued_length,
          glued, card_edgeSet_cyc (glued_nodup ha hb) (by rw [glued_length]; omega),
          List.toFinset_append, Finset.filter_union,
          Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (glued_disjoint ha hb))]
          at hgl
        have e1 : ((lstN n a₁ b₁).toFinset.filter fun v =>
            piece (lst (blkA n) (blkB n) a₁ b₁) (mk a₁ b₁) (mk a₂ b₂) v = true) =
            ((lstN n a₁ b₁).toFinset.filter fun v => mk a₁ b₁ v = true) := by
          refine Finset.filter_congr fun v hv => ?_
          rw [piece_of_mem (List.mem_toFinset.1 hv)]
        have e2 : ((lstN n a₂ b₂).toFinset.filter fun v =>
            piece (lst (blkA n) (blkB n) a₁ b₁) (mk a₁ b₁) (mk a₂ b₂) v = true) =
            ((lstN n a₂ b₂).toFinset.filter fun v => mk a₂ b₂ v = true) := by
          refine Finset.filter_congr fun v hv => ?_
          have : v ∉ lst (blkA n) (blkB n) a₁ b₁ := fun h' =>
            Finset.disjoint_left.1 (glued_disjoint ha hb) (List.mem_toFinset.2 h') hv
          rw [piece_of_not_mem this]
        rw [e1, e2] at hgl
        have l1 := lstN_length n a₁ b₁
        have l2 := lstN_length n a₂ b₂
        unfold lstN at l1 l2 hm1 hm2 hgl e1 e2
        rw [hm1, hm2, l1, l2] at hgl
        obtain ⟨k, rfl⟩ := hodd
        omega⟩)
  obtain ⟨c, hc, C, hC⟩ := logBound_of_bound (M := 1) le_rfl (by simpa using hr)
  refine ⟨⟨c, hc, C, hC⟩, not_isLittleO_log hc hC ?_⟩
  exact Filter.frequently_atTop.2 fun N => ⟨2 * N + 1, by omega, odd_two_mul_add_one N⟩

end Podc.LocallyCheckableProofs
