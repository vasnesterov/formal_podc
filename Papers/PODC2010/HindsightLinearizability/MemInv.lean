import Papers.PODC2010.HindsightLinearizability.Algorithm

/-!
# The memory invariant

`MemInv m` is the inductive invariant of the thread-shared state behind Theorem 4.1. Its core
is an explicit backbone list `L` (`IsBB m L`): a heap path `H = 1 → … → T = 0` whose nodes are
exactly the unmarked allocated nodes. With `φ_<` (keys strictly increase along every link) it
implies all state properties of Fig. 4.

This file proves the invariant for the initialized state and its preservation by the two atomic
sections, and computes their effect on the abstraction function `Abs` (the heart of the
linearizability proof of add and remove, Theorem 7.5).
-/

namespace Podc.HindsightLinearizability

open HeapState

/-- `L` is the backbone list of `m`: a heap path from `H = 1` to `T = 0` consisting of allocated
nodes, which are exactly the unmarked allocated nodes. -/
structure IsBB (m : Mem) (L : List ℕ) : Prop where
  head : L.head? = some 1
  last : L.getLast? = some 0
  chain : L.IsChain m.hs.Link
  lt : ∀ u ∈ L, u < m.cnt
  mark : ∀ u < m.cnt, (m.mark u = false ↔ u ∈ L)

/-- The memory invariant. -/
structure MemInv (m : Mem) : Prop where
  T_eq : m.T = 0
  H_eq : m.H = 1
  two_le : 2 ≤ m.cnt
  keyT : m.key 0 = ⊤
  keyH : m.key 1 = ⊥
  nextT : m.next 0 = none
  next_none : ∀ u, m.cnt ≤ u → m.next u = none
  next_lt : ∀ u < m.cnt, u ≠ 0 → ∃ v < m.cnt, m.next u = some v ∧ m.key u < m.key v
  key_fin : ∀ u < m.cnt, u ≠ 0 → u ≠ 1 → ∃ z, m.key u = fin z
  bb : ∃ L, IsBB m L

lemma memInv_init : MemInv initMem where
  T_eq := rfl
  H_eq := rfl
  two_le := le_rfl
  keyT := rfl
  keyH := rfl
  nextT := rfl
  next_none u hu := by simp [initMem] at hu ⊢; omega
  next_lt u hu h0 := ⟨0, by simp [initMem], by
    simp only [initMem] at hu ⊢
    have : u = 1 := by omega
    subst this; simp⟩
  key_fin u hu h0 h1 := by simp [initMem] at hu; omega
  bb := ⟨[1, 0], rfl, rfl, by simp [List.isChain_pair, HeapState.Link, Mem.hs, initMem],
    by simp [initMem], by
      intro u hu; simp only [initMem] at hu ⊢; simp; omega⟩

namespace MemInv

variable {m : Mem} (hm : MemInv m)
include hm

lemma closed {u v : ℕ} (hu : u < m.cnt) (h : m.next u = some v) : v < m.cnt := by
  by_cases h0 : u = 0
  · subst h0; simp [hm.nextT] at h
  · obtain ⟨w, hw, hw', -⟩ := hm.next_lt u hu h0; rw [hw'] at h; cases h; exact hw

lemma lt_key {u v : ℕ} (hu : u < m.cnt) (h : m.next u = some v) : m.key u < m.key v := by
  by_cases h0 : u = 0
  · subst h0; simp [hm.nextT] at h
  · obtain ⟨w, -, hw', hk⟩ := hm.next_lt u hu h0; rw [hw'] at h; cases h; exact hk

lemma ne_zero_of_key_lt {u : ℕ} {z : ℤ} (h : m.key u < fin z) : u ≠ 0 := by
  rintro rfl; rw [hm.keyT] at h; exact absurd h (not_lt.2 le_top)

lemma hs_closed : m.hs.Closed := fun _ hu _ h => hm.closed hu h
lemma hs_phiLt : m.hs.PhiLt := fun _ hu _ h => hm.lt_key hu h

/-- Links out of unallocated nodes do not exist. -/
lemma alloc_of_link {u v : ℕ} (h : m.hs.Link u v) : u < m.cnt := by
  by_contra hc; simp [HeapState.Link, hm.next_none u (by omega)] at h

namespace IsBB

variable {L : List ℕ} (hL : IsBB m L)
include hL

lemma ne_nil : L ≠ [] := by rintro rfl; have := hL.head; simp at this

lemma eq_cons : L = 1 :: L.tail := by
  obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil (ne_nil hm hL)
  have := hL.head
  simp only [List.head?_cons, Option.some.injEq] at this
  subst this; rfl

/-- The backbone nodes are the nodes of `L`. -/
lemma backbone_iff (u : ℕ) : m.hs.Backbone u ↔ u ∈ L := by
  have h1 := eq_cons hm hL
  have hc := hL.chain
  rw [h1] at hc ⊢
  unfold Backbone
  rw [Mem.hs_H, hm.H_eq]
  refine reach_iff_mem_of_isChain hc ?_ u
  have hl := hL.last
  rw [h1, List.getLast?_eq_getLast (List.cons_ne_nil _ _)] at hl
  simp only [Option.some.injEq] at hl
  rw [hl]; exact hm.nextT

/-- Keys strictly increase along `L`. -/
lemma pairwise : L.Pairwise (fun a b => m.key a < m.key b) := by
  have : (L.map m.key).IsChain (· < ·) := by
    rw [List.isChain_map]
    exact hL.chain.imp_of_mem_imp (fun a b ha _ h => hm.lt_key (hL.lt a ha) h)
  rw [List.isChain_iff_pairwise, List.pairwise_map] at this
  exact this

lemma nodup : L.Nodup :=
  (pairwise hm hL).imp (fun h he => by subst he; exact lt_irrefl _ h)

lemma key_injOn {u v : ℕ} (hu : u ∈ L) (hv : v ∈ L) (h : m.key u = m.key v) : u = v := by
  by_contra hne
  have H := List.pairwise_iff_getElem.1 (pairwise hm hL)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact (H i j hi hj hij).ne h
  · exact hne rfl
  · exact (H j i hj hi hij).ne h.symm

/-- If `p` is on the backbone and `p.n = c`, then `L = l₁ ++ p :: c :: l₂`. -/
lemma split {p c : ℕ} (hp : p ∈ L) (hc : m.next p = some c) :
    ∃ l₁ l₂, L = l₁ ++ p :: c :: l₂ := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hp
  rcases t with _ | ⟨c', t⟩
  · have := hL.last
    rw [hst, List.getLast?_append] at this
    simp only [List.getLast?_singleton, Option.some_or, Option.some.injEq] at this
    subst this; simp [hm.nextT] at hc
  · have hch := hL.chain
    rw [hst, List.isChain_append_cons_cons] at hch
    have : m.next p = some c' := hch.2.1
    rw [hc] at this; cases this
    exact ⟨s, t, hst⟩

/-- The local window on the backbone list. -/
lemma window {l₁ l₂ : List ℕ} {p c : ℕ} (hs : L = l₁ ++ p :: c :: l₂) {u : ℕ} (hu : u ∈ L) :
    m.key u ≤ m.key p ∨ m.key c ≤ m.key u := by
  have hpw := pairwise hm hL
  rw [hs] at hpw hu
  rw [List.pairwise_append] at hpw
  obtain ⟨h1, h2, h3⟩ := hpw
  simp only [List.mem_append, List.mem_cons] at hu
  rcases hu with hu | rfl | rfl | hu
  · exact Or.inl (h3 u hu p (by simp)).le
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl
  · rw [List.pairwise_cons] at h2
    exact Or.inr (List.rel_of_pairwise_cons h2.2 hu).le

lemma mem_Abs_iff (z : ℤ) : z ∈ Abs m ↔ ∃ u ∈ L, m.key u = fin z := by
  simp only [Abs, backboneKeys, Set.mem_setOf_eq, Set.mem_image, Mem.hs_key]
  constructor
  · rintro ⟨u, hu, h⟩; exact ⟨u, (backbone_iff hm hL u).1 hu, h⟩
  · rintro ⟨u, hu, h⟩; exact ⟨u, (backbone_iff hm hL u).2 hu, h⟩

end IsBB

/-- `φ_{UB}`. -/
lemma unmarked_iff_backbone {u : ℕ} (hu : u < m.cnt) : m.mark u = false ↔ m.hs.Backbone u := by
  obtain ⟨L, hL⟩ := hm.bb
  rw [hL.mark u hu, IsBB.backbone_iff hm hL]

lemma backbone_lt {u : ℕ} (h : m.hs.Backbone u) : u < m.cnt := by
  obtain ⟨L, hL⟩ := hm.bb
  exact hL.lt u ((IsBB.backbone_iff hm hL u).1 h)

/-- The local window at a backbone link `p.n ↦ c` of the current memory: if
`p.k < k ≤ c.k` then `k ∈ Abs ↔ c.k = k`. -/
lemma mem_Abs_iff_of_link {p c : ℕ} (hp : m.hs.Backbone p) (hc : m.next p = some c) {k : ℤ}
    (hpk : m.key p < fin k) (hck : fin k ≤ m.key c) : k ∈ Abs m ↔ m.key c = fin k := by
  obtain ⟨L, hL⟩ := hm.bb
  have hpL := (IsBB.backbone_iff hm hL p).1 hp
  obtain ⟨l₁, l₂, hs⟩ := IsBB.split hm hL hpL hc
  rw [IsBB.mem_Abs_iff hm hL]
  constructor
  · rintro ⟨u, hu, hk⟩
    rcases IsBB.window hm hL hs hu with h | h
    · rw [hk] at h; exact absurd (lt_of_le_of_lt h hpk) (lt_irrefl _)
    · rw [hk] at h; exact le_antisymm h hck
  · intro h; exact ⟨c, by rw [hs]; simp, h⟩

end MemInv

/-! ### The atomic section of `add` -/

section Add

variable {m : Mem} {p c : ℕ} {k : ℤ}

/-- Preservation of `IsChain` along a list, when the new relation agrees with the old one on all
sources in the list. -/
lemma isChain_congr_of_mem {R S : ℕ → ℕ → Prop} {l : List ℕ} (h : l.IsChain R)
    (H : ∀ a ∈ l, ∀ b, R a b → S a b) : l.IsChain S :=
  h.imp_of_mem_imp (fun a b ha _ hr => H a ha b hr)

/-- Same, for `l ++ [x]`, where only the sources in `l` matter. -/
lemma isChain_append_singleton_congr {R S : ℕ → ℕ → Prop} {l : List ℕ} {x : ℕ}
    (h : (l ++ [x]).IsChain R) (H : ∀ a ∈ l, ∀ b, R a b → S a b) : (l ++ [x]).IsChain S := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append] at h ⊢
    rw [List.isChain_cons] at h ⊢
    refine ⟨fun y hy => H a (by simp) y (h.1 y hy), ih h.2 (fun a' ha' => H a' (by simp [ha']))⟩

theorem insertAfter_spec (hm : MemInv m) (hp : m.hs.Backbone p) (hc : m.next p = some c)
    (hpk : m.key p < fin k) (hck : fin k < m.key c) :
    MemInv (m.insertAfter p c k) ∧ Abs (m.insertAfter p c k) = insert k (Abs m) ∧
      k ∉ Abs m := by
  obtain ⟨L, hL⟩ := hm.bb
  have hpL := (MemInv.IsBB.backbone_iff hm hL p).1 hp
  have hplt := hL.lt p hpL
  have hclt := hm.closed hplt hc
  have hp0 : p ≠ 0 := hm.ne_zero_of_key_lt hpk
  obtain ⟨l₁, l₂, hs⟩ := MemInv.IsBB.split hm hL hpL hc
  have hnd := MemInv.IsBB.nodup hm hL
  rw [hs] at hnd
  have hp1 : p ∉ l₁ := by
    intro h; rw [List.nodup_append] at hnd; exact hnd.2.2 p h p (by simp) rfl
  have hp2 : p ∉ c :: l₂ := by
    rw [List.nodup_append, List.nodup_cons] at hnd; exact hnd.2.1.1
  set t := m.cnt with ht
  have htL : ∀ u ∈ L, u ≠ t := fun u hu => (hL.lt u hu).ne
  set m' := m.insertAfter p c k with hm'
  have hnext : ∀ u, m'.next u = if u = p then some t else if u = t then some c else m.next u := by
    intro u
    simp only [hm', Mem.insertAfter, Function.update_apply]
    split_ifs <;> simp_all
  have hkey : ∀ u, m'.key u = if u = t then fin k else m.key u := by
    intro u; simp only [hm', Mem.insertAfter, Function.update_apply]; rfl
  have hmark : ∀ u, m'.mark u = if u = t then false else m.mark u := by
    intro u; simp only [hm', Mem.insertAfter, Function.update_apply]; rfl
  have hcnt : m'.cnt = t + 1 := rfl
  have hpt : p ≠ t := (hplt).ne
  have hct : c ≠ t := hclt.ne
  -- the new backbone list
  set L' := l₁ ++ p :: t :: c :: l₂ with hL'
  have hmemL' : ∀ u, u ∈ L' ↔ u ∈ L ∨ u = t := by
    intro u; rw [hs, hL']; simp only [List.mem_append, List.mem_cons]; tauto
  have hbb : IsBB m' L' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := hL.head; rw [hs] at this; rw [hL']
      rcases l₁ with _ | ⟨a, l₁⟩ <;> simpa using this
    · have := hL.last; rw [hs] at this; rw [hL']
      simp only [List.getLast?_append, List.getLast?_cons_cons] at this ⊢
      exact this
    · have hch := hL.chain
      rw [hs, List.isChain_append_cons_cons] at hch
      rw [hL', List.isChain_append_cons_cons, List.isChain_cons_cons]
      refine ⟨isChain_append_singleton_congr hch.1 ?_, ?_, ?_, isChain_congr_of_mem hch.2.2 ?_⟩
      · intro a ha b hab
        have hat : a ≠ t := htL a (by rw [hs]; simp [ha])
        have hap : a ≠ p := fun h => hp1 (h ▸ ha)
        show m'.next a = some b
        rw [hnext]; simpa [hap, hat, HeapState.Link] using hab
      · show m'.next p = some t; rw [hnext]; simp
      · show m'.next t = some c; rw [hnext]; simp [hpt.symm]
      · intro a ha b hab
        have hat : a ≠ t := htL a (by rw [hs]; simp [ha])
        have hap : a ≠ p := fun h => hp2 (h ▸ ha)
        show m'.next a = some b
        rw [hnext]; simpa [hap, hat, HeapState.Link] using hab
    · intro u hu
      rw [hcnt]
      rcases (hmemL' u).1 hu with hu | rfl
      · exact Nat.lt_succ_of_lt (hL.lt u hu)
      · exact Nat.lt_succ_self _
    · intro u hu
      rw [hcnt] at hu
      rw [hmark, hmemL']
      by_cases hut : u = t
      · simp [hut]
      · simp only [hut, if_false, or_false]
        exact hL.mark u (by omega)
  have hinv : MemInv m' := by
    refine ⟨hm.T_eq, hm.H_eq, by simp [hcnt]; have := hm.two_le; omega, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨L', hbb⟩⟩
    · rw [hkey]; simp only [show (0 : ℕ) ≠ t by have := hm.two_le; omega, if_false]; exact hm.keyT
    · rw [hkey]; simp only [show (1 : ℕ) ≠ t by have := hm.two_le; omega, if_false]; exact hm.keyH
    · rw [hnext]
      simp only [show (0 : ℕ) ≠ p from Ne.symm hp0, show (0 : ℕ) ≠ t by have := hm.two_le; omega,
        if_false]
      exact hm.nextT
    · intro u hu
      rw [hcnt] at hu
      rw [hnext]
      simp only [show u ≠ p by omega, show u ≠ t by omega, if_false]
      exact hm.next_none u (by omega)
    · intro u hu hu0
      rw [hcnt] at hu
      by_cases hup : u = p
      · subst hup
        refine ⟨t, by omega, by rw [hnext]; simp, ?_⟩
        rw [hkey, hkey]; simp [hpt, hpk]
      by_cases hut : u = t
      · subst hut
        refine ⟨c, by omega, by rw [hnext]; simp [hpt.symm], ?_⟩
        rw [hkey, hkey]; simp [hct, hck]
      obtain ⟨v, hv, hv', hk'⟩ := hm.next_lt u (by omega) hu0
      refine ⟨v, by omega, by rw [hnext]; simp [hup, hut, hv'], ?_⟩
      rw [hkey, hkey]; simp [hut, show v ≠ t from hv.ne, hk']
    · intro u hu hu0 hu1
      rw [hcnt] at hu
      rw [hkey]
      by_cases hut : u = t
      · simp [hut]
      · simp only [hut, if_false]; exact hm.key_fin u (by omega) hu0 hu1
  refine ⟨hinv, ?_, ?_⟩
  · ext z
    rw [MemInv.IsBB.mem_Abs_iff hinv hbb, Set.mem_insert_iff,
      MemInv.IsBB.mem_Abs_iff hm hL]
    constructor
    · rintro ⟨u, hu, hk'⟩
      rw [hkey] at hk'
      rcases (hmemL' u).1 hu with hu | rfl
      · simp only [htL u hu, if_false] at hk'; exact Or.inr ⟨u, hu, hk'⟩
      · simp only [if_true, fin_inj] at hk'; exact Or.inl hk'.symm
    · rintro (rfl | ⟨u, hu, hk'⟩)
      · exact ⟨t, (hmemL' t).2 (Or.inr rfl), by rw [hkey]; simp⟩
      · exact ⟨u, (hmemL' u).2 (Or.inl hu), by rw [hkey]; simp [htL u hu, hk']⟩
  · rw [hm.mem_Abs_iff_of_link hp hc hpk hck.le]; exact hck.ne'

end Add

/-! ### The atomic section of `remove` -/

section Remove

variable {m : Mem} {p c : ℕ} {k : ℤ}

theorem unlink_spec (hm : MemInv m) (hp : m.hs.Backbone p) (hc : m.next p = some c)
    (hpk : m.key p < fin k) (hck : m.key c = fin k) :
    MemInv (m.unlink p c) ∧ Abs (m.unlink p c) = Abs m \ {k} ∧ k ∈ Abs m := by
  obtain ⟨L, hL⟩ := hm.bb
  have hpL := (MemInv.IsBB.backbone_iff hm hL p).1 hp
  have hplt := hL.lt p hpL
  have hclt := hm.closed hplt hc
  have hp0 : p ≠ 0 := hm.ne_zero_of_key_lt hpk
  have hc0 : c ≠ 0 := by rintro rfl; rw [hm.keyT] at hck; exact fin_ne_top k hck.symm
  obtain ⟨d, hdlt, hcd, hkcd⟩ := hm.next_lt c hclt hc0
  obtain ⟨l₁, l₂, hs⟩ := MemInv.IsBB.split hm hL hpL hc
  -- `l₂ = d :: l₃`
  obtain ⟨l₃, hl₂⟩ : ∃ l₃, l₂ = d :: l₃ := by
    rcases l₂ with _ | ⟨d', l₃⟩
    · have := hL.last
      rw [hs] at this
      simp [List.getLast?_append] at this
      exact absurd this hc0
    · have hch := hL.chain
      rw [hs, List.isChain_append_cons_cons, List.isChain_cons_cons] at hch
      have : m.next c = some d' := hch.2.2.1
      rw [hcd] at this; cases this
      exact ⟨l₃, rfl⟩
  subst hl₂
  have hnd := MemInv.IsBB.nodup hm hL
  rw [hs] at hnd
  have hp1 : p ∉ l₁ := by
    intro h; rw [List.nodup_append] at hnd; exact hnd.2.2 p h p (by simp) rfl
  have hp2 : p ∉ c :: d :: l₃ := by
    rw [List.nodup_append, List.nodup_cons] at hnd; exact hnd.2.1.1
  have hc1 : c ∉ l₁ := by
    intro h; rw [List.nodup_append] at hnd; exact hnd.2.2 c h c (by simp) rfl
  have hc2 : c ∉ d :: l₃ := by
    rw [List.nodup_append, List.nodup_cons, List.nodup_cons] at hnd; exact hnd.2.1.2.1
  have hcp : c ≠ p := fun h => hp2 (h ▸ List.mem_cons_self)
  set m' := m.unlink p c with hm'
  have hnext : ∀ u, m'.next u = if u = p then some d else m.next u := by
    intro u; simp only [hm', Mem.unlink, Function.update_apply, hcd]
  have hkey : ∀ u, m'.key u = m.key u := fun _ => rfl
  have hmark : ∀ u, m'.mark u = if u = c then true else m.mark u := by
    intro u; simp only [hm', Mem.unlink, Function.update_apply]
  have hcnt : m'.cnt = m.cnt := rfl
  set L' := l₁ ++ p :: d :: l₃ with hL'
  have hmemL' : ∀ u, u ∈ L' ↔ u ∈ L ∧ u ≠ c := by
    intro u; rw [hs, hL']; simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | rfl | rfl | h)
      · exact ⟨Or.inl h, fun e => hc1 (e ▸ h)⟩
      · exact ⟨Or.inr (Or.inl rfl), hcp.symm⟩
      · exact ⟨by tauto, fun e => hc2 (e ▸ List.mem_cons_self)⟩
      · exact ⟨by tauto, fun e => hc2 (e ▸ List.mem_cons_of_mem _ h)⟩
    · rintro ⟨h, hne⟩; tauto
  have hbb : IsBB m' L' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := hL.head; rw [hs] at this; rw [hL']
      rcases l₁ with _ | ⟨a, l₁⟩ <;> simpa using this
    · have := hL.last; rw [hs] at this; rw [hL']
      simp only [List.getLast?_append, List.getLast?_cons_cons] at this ⊢
      exact this
    · have hch := hL.chain
      rw [hs, List.isChain_append_cons_cons, List.isChain_cons_cons] at hch
      rw [hL', List.isChain_append_cons_cons]
      refine ⟨isChain_append_singleton_congr hch.1 ?_, ?_, isChain_congr_of_mem hch.2.2.2 ?_⟩
      · intro a ha b hab
        have hap : a ≠ p := fun h => hp1 (h ▸ ha)
        show m'.next a = some b
        rw [hnext]; simpa [hap, HeapState.Link] using hab
      · show m'.next p = some d; rw [hnext]; simp
      · intro a ha b hab
        have hap : a ≠ p := fun h => hp2 (h ▸ List.mem_cons_of_mem _ ha)
        show m'.next a = some b
        rw [hnext]; simpa [hap, HeapState.Link] using hab
    · intro u hu; rw [hcnt]; exact hL.lt u ((hmemL' u).1 hu).1
    · intro u hu
      rw [hcnt] at hu
      rw [hmark, hmemL']
      by_cases huc : u = c
      · simp [huc]
      · simp only [huc, if_false, ne_eq, not_false_eq_true, and_true]
        exact hL.mark u hu
  have hinv : MemInv m' := by
    refine ⟨hm.T_eq, hm.H_eq, hm.two_le, hm.keyT, hm.keyH, ?_, ?_, ?_, hm.key_fin, ⟨L', hbb⟩⟩
    · rw [hnext]; simp only [show (0 : ℕ) ≠ p from Ne.symm hp0, if_false]; exact hm.nextT
    · intro u hu
      rw [hnext]; simp only [show u ≠ p by omega, if_false]; exact hm.next_none u hu
    · intro u hu hu0
      by_cases hup : u = p
      · subst hup
        exact ⟨d, hdlt, by rw [hnext]; simp, (hm.lt_key hplt hc).trans hkcd⟩
      · obtain ⟨v, hv, hv', hk'⟩ := hm.next_lt u hu hu0
        exact ⟨v, hv, by rw [hnext]; simp [hup, hv'], hk'⟩
  have hkA : k ∈ Abs m := (MemInv.IsBB.mem_Abs_iff hm hL k).2 ⟨c, by rw [hs]; simp, hck⟩
  refine ⟨hinv, ?_, hkA⟩
  ext z
  rw [MemInv.IsBB.mem_Abs_iff hinv hbb, Set.mem_diff, MemInv.IsBB.mem_Abs_iff hm hL]
  simp only [hkey, hmemL', Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, ⟨hu, huc⟩, hk'⟩
    refine ⟨⟨u, hu, hk'⟩, fun hz => huc ?_⟩
    subst hz
    exact MemInv.IsBB.key_injOn hm hL hu (by rw [hs]; simp) (hk'.trans hck.symm)
  · rintro ⟨⟨u, hu, hk'⟩, hz⟩
    exact ⟨u, ⟨hu, fun e => hz (by subst e; rw [hck] at hk'; exact (fin_inj.1 hk').symm)⟩, hk'⟩

end Remove

end Podc.HindsightLinearizability
