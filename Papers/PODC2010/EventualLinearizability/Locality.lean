import Papers.PODC2010.EventualLinearizability.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Locality of weak consistency and of `t`-linearizability (Lemmas 1 and 2)

Serafini, Dobre, Majuntke, Bokor and Suri, *Eventually Linearizable Shared Objects*
(PODC 2010), Section 3.2.

* **Lemma 1** (`weaklyConsistent_restrictX`, `weaklyConsistent_of_restrictX`,
  `weaklyConsistent_iff_restrictX`): `H` is weakly consistent iff every object subhistory `H|x`
  is.
* **Lemma 2** (`IsTLin.restrictX`, `tLinearizable_restrictX`, `tLinearizable_of_restrictX`,
  `tLinearizable_of_restrictX_after`): if `H|x` is `t_x`-linearizable for every object `x` then
  `H` is `t_max`-linearizable for every `t_max ≥ t_x`; conversely a `t`-linearization of `H`
  restricts to `t`-linearizations of the `H|x`. We prove this for arbitrary sets of "late"
  operations (`A ⊆ A_x` for all `x` corresponds to `t_max ≥ t_x`).

Histories are assumed well-formed (as in the paper). The "only if" directions additionally need
the empty history to be legal for every object (`hnil`): with CSLib's `Legal`, a sequential
history of operations of `x` is legal only if its (empty) restriction to every other object is
in that object's specification.

## Differences with the paper's proofs

* **Lemma 1, "if" direction.** The paper reuses, for an operation `o` of `p_i` on `x`, the
  sequential history `τ_x(i, o)` of `H|x` as `τ(i, o)` for `H`. This violates condition (iii)
  across objects: for an earlier operation `o'` of `p_i` on another object `y`,
  `τ(i, o') = τ_y(i, o')` consists of operations of `y` and is not contained in `τ_x(i, o)`.
  We use instead (`wcGlue`) the concatenation, over all objects `y ≠ x`, of `τ_y(i, b_y)` where
  `b_y` is the last operation of `p_i` on `y` that precedes `o` in real time (`wcLast`; nothing
  if there is none), followed by `τ_x(i, o)`.
* **Lemma 2, "if" direction.** Instead of the paper's minimal-cycle argument, we merge the
  `t_x`-linearizations `L_x` by a stable sort on a key (`tKey`): the key of an entry `a` of `L_x`
  is the largest invocation time of a late operation at or before `a` in `L_x`. Keys are
  monotone along each `L_x` and strictly increase along `<_{H,t}` (`tKey_lt`), so the sorted
  concatenation (`tMerge`) contains each `L_x` as its subsequence of operations of `x` and
  respects `<_{H,t}`.
-/

-- CSLib candidate: locality of weak consistency and t-linearizability (with Defs.lean).
namespace Podc.EventualLinearizability

open Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]
  {spec : SeqSpec P X Op Res} {H : History P X Op Res}

/-! ### Auxiliary facts -/

lemma obj_mem_of_invoked {a : OpId P X} (h : Invoked H a) : a.x ∈ H.map Event.obj := by
  obtain ⟨o, h1, -⟩ := tInv_spec h
  exact List.mem_map.2 ⟨.inv a.p a.x o, List.mem_of_getElem? h1, rfl⟩

omit [DecidableEq P] in
lemma IdSeq.ids_filter (L : IdSeq P X Op Res) (y : X) :
    IdSeq.ids (L.filter (·.1.x = y)) = L.ids.filter (·.x = y) := by
  simp only [IdSeq.ids, List.filter_map]; rfl

omit [DecidableEq P] in
lemma IdSeq.recs_filter {L : IdSeq P X Op Res} (hL : ∀ u ∈ L, u.2.x = u.1.x) (y : X) :
    L.recs.filter (·.x = y) = IdSeq.recs (L.filter (·.1.x = y)) := by
  simp only [IdSeq.recs, List.filter_map]
  congr 1
  exact List.filter_congr fun u hu => by simp [Function.comp, hL u hu]

/-- A list of entries is duplicate-free as soon as its restriction to each object is. -/
lemma IdSeq.nodup_of_filter {L : IdSeq P X Op Res}
    (h : ∀ y, (IdSeq.ids (L.filter (·.1.x = y))).Nodup) : L.ids.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro a
  have := List.nodup_iff_count_le_one.1 (h a.x) a
  rwa [IdSeq.ids_filter, List.count_filter (by simp)] at this

omit [DecidableEq P] in
/-- Filtering a concatenation of per-object blocks by an object. -/
lemma filter_flatMap_obj {l : List X} (hl : l.Nodup) (g : X → IdSeq P X Op Res)
    (hg : ∀ z ∈ l, ∀ u ∈ g z, u.1.x = z) (y : X) :
    (l.flatMap g).filter (·.1.x = y) = if y ∈ l then g y else [] := by
  induction l with
  | nil => simp
  | cons z l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.filter_append,
      ih hl.2 (fun z' hz' => hg z' (List.mem_cons_of_mem _ hz'))]
    by_cases hz : z = y
    · subst hz
      rw [List.filter_eq_self.2 (fun u hu => by simp [hg z (by simp) u hu])]
      simp [hl.1]
    · rw [List.filter_eq_nil_iff.2 (fun u hu => by simp [hg z (by simp) u hu, hz])]
      simp [Ne.symm hz]

namespace IsSeqOf

lemma invoked {L : IdSeq P X Op Res} (h : IsSeqOf spec H L) {u} (hu : u ∈ L) : Invoked H u.1 :=
  Invoked.of_opOf (h.ofHist u hu).2.2

lemma obj_eq {x : X} {L : IdSeq P X Op Res} (h : IsSeqOf spec (restrictX H x) L) {u}
    (hu : u ∈ L) : u.1.x = x ∧ u.2.x = x := by
  have h1 := (invoked_restrictX.1 (h.invoked hu)).1
  exact ⟨h1, (h.ofHist u hu).2.1.trans h1⟩

lemma ids_obj {x : X} {L : IdSeq P X Op Res} (h : IsSeqOf spec (restrictX H x) L) {c : OpId P X}
    (hc : c ∈ L.ids) : c.x = x ∧ Invoked H c := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
  exact invoked_restrictX.1 (h.invoked hu)

/-- Gluing per-object sequential histories: `L` is a legal sequential history of operations of
`H` if each restriction `L|y` is one of `H|y` (or is empty, with the empty history legal for
`y`). -/
lemma of_filter {L : IdSeq P X Op Res}
    (h : ∀ y, IsSeqOf spec (restrictX H y) (L.filter (·.1.x = y)) ∨
      (L.filter (·.1.x = y) = [] ∧ [] ∈ spec y)) :
    IsSeqOf spec H L := by
  have hof : ∀ u ∈ L, u.2.p = u.1.p ∧ u.2.x = u.1.x ∧ opOf H u.1 = some u.2.o := by
    intro u hu
    have hu' : u ∈ L.filter (·.1.x = u.1.x) := List.mem_filter.2 ⟨hu, by simp⟩
    rcases h u.1.x with h' | ⟨h', -⟩
    · have := h'.ofHist u hu'
      rwa [opOf_restrictX rfl] at this
    · rw [h'] at hu'; simp at hu'
  refine ⟨hof, IdSeq.nodup_of_filter fun y => ?_, ?_⟩
  · rcases h y with h' | ⟨h', -⟩
    · exact h'.nodup
    · rw [h']; exact List.nodup_nil
  · rw [legal_seqHist_iff]
    intro y
    rw [IdSeq.recs_filter (fun u hu => (hof u hu).2.1) y]
    rcases h y with h' | ⟨h', hnil⟩
    · have := (legal_seqHist_iff spec _).1 h'.legal y
      have hself : (IdSeq.recs (L.filter (·.1.x = y))).filter (·.x = y) =
          IdSeq.recs (L.filter (·.1.x = y)) := by
        rw [List.filter_eq_self]
        intro e he
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 he
        simp [(h'.obj_eq hu).2]
      rwa [hself] at this
    · rw [h']; exact hnil

/-- Restricting a legal sequential history of operations of `H` to an object `x`. -/
lemma restrict (hnil : ∀ y, [] ∈ spec y) {L : IdSeq P X Op Res} (h : IsSeqOf spec H L)
    (x : X) : IsSeqOf spec (restrictX H x) (L.filter (·.1.x = x)) := by
  refine ⟨fun u hu => ?_, ?_, ?_⟩
  · obtain ⟨hu, hux⟩ := List.mem_filter.1 hu
    rw [opOf_restrictX (by simpa using hux)]; exact h.ofHist u hu
  · exact h.nodup.sublist ((List.filter_sublist).map _)
  · rw [legal_seqHist_iff]
    intro y
    have hof : ∀ u ∈ L.filter (·.1.x = x), u.2.x = u.1.x :=
      fun u hu => (h.ofHist u (List.mem_filter.1 hu).1).2.1
    rw [IdSeq.recs_filter hof, List.filter_filter]
    by_cases hy : y = x
    · subst hy
      have := (legal_seqHist_iff spec _).1 h.legal y
      rw [IdSeq.recs_filter (fun u hu => (h.ofHist u hu).2.1)] at this
      convert this using 4
      simp
    · convert hnil y
      rw [List.filter_eq_nil_iff.2]
      · rfl
      · intro u hu
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro h1 h2; exact hy (h1.symm.trans h2)

end IsSeqOf

/-! ### Program order -/

/-- `d` precedes the invoked operation `a` iff `d` completes before `a` is invoked. -/
lemma precedes_iff_lt {a d : OpId P X} (ha : Invoked H a) :
    Precedes H d a ↔ d.k < (ressOf (H.take (tInv H a)) d.p d.x).length := by
  change _ ↔ Completed (H.take (tInv H a)) d
  rw [precedes_iff, completed_take_iff]
  constructor
  · rintro ⟨hc, h⟩; exact ⟨hc, h.le⟩
  · rintro ⟨hc, h⟩; exact ⟨hc, lt_of_le_of_ne h (fun h' => tInv_ne_tRes ha hc h'.symm)⟩

/-- Program order: operations of the same process on the same object are ordered by index. -/
lemma precedes_of_k_lt (hH : WellFormed H) {d e : OpId P X} (hp : d.p = e.p) (hx : d.x = e.x)
    (he : Invoked H e) (hk : d.k < e.k) : Precedes H d e := by
  have hd : Invoked H d := by unfold Invoked at he ⊢; rw [hp, hx]; omega
  have hne : d ≠ e := fun h => by subst h; omega
  rcases precedes_or_precedes hH hp hd he hne with h | h
  · exact h
  · exfalso
    rw [precedes_iff_lt hd, ← hp, ← hx] at h
    have : ¬ Completed (H.take (tInv H d)) d := by
      rw [completed_take_iff]; rintro ⟨hc, hle⟩; have := tInv_lt_tRes hH hc; omega
    exact this (by unfold Completed; omega)

/-! ### Lemma 1: weak consistency is local -/

/-- **Lemma 1** of [Serafini et al., PODC 2010], "only if" direction: if `H` is weakly
consistent, so is every `H|x` (the witness is `τ(i, o)|x`). -/
theorem weaklyConsistent_restrictX (hnil : ∀ y, [] ∈ spec y) (h : WeaklyConsistent spec H)
    (x : X) : WeaklyConsistent spec (restrictX H x) := by
  obtain ⟨τ, hτ⟩ := h
  refine ⟨fun a => (τ a).filter (·.1.x = x), fun a ha => ?_⟩
  obtain ⟨hax, ha⟩ := completed_restrictX.1 ha
  obtain ⟨hs, ⟨e, hlast, hres⟩, h2, h3⟩ := hτ a ha
  refine ⟨hs.restrict hnil x, ⟨e, ?_, by rwa [resOf_restrictX hax]⟩, ?_, ?_⟩
  · obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 hlast
    dsimp only
    rw [hl, List.filter_append, List.getLast?_append]; simp [hax]
  · intro b hb
    rw [IdSeq.ids_filter, List.mem_filter] at hb
    rw [precedes_restrictX hax (by simpa using hb.2)]
    exact h2 b hb.1
  · intro b hbp hba c hc
    have hbx : b.x = x := (completed_restrictX.1 hba.completed).1
    rw [precedes_restrictX hbx hax] at hba
    rw [IdSeq.ids_filter, List.mem_filter] at hc ⊢
    exact ⟨h3 b hbp hba c hc.1, hc.2⟩

/-- The number of operations of `a.p` on `y` completed before `a` is invoked. -/
def nBefore (H : History P X Op Res) (a : OpId P X) (y : X) : ℕ :=
  (ressOf (H.take (tInv H a)) a.p y).length

/-- The last operation of `a.p` on `y` up to `a`: `a` itself if `y = a.x`, otherwise the last
operation of `a.p` on `y` that precedes `a` (if any). -/
def wcLast (H : History P X Op Res) (a : OpId P X) (y : X) : Option (OpId P X) :=
  if y = a.x then some a
  else if nBefore H a y = 0 then none else some ⟨a.p, y, nBefore H a y - 1⟩

lemma wcLast_spec (hH : WellFormed H) {a : OpId P X} (ha : Completed H a) {y : X} {d : OpId P X}
    (h : wcLast H a y = some d) :
    d.p = a.p ∧ d.x = y ∧ Completed H d ∧ (d = a ∨ Precedes H d a) := by
  unfold wcLast at h
  split_ifs at h with h1 h2
  · cases h; exact ⟨rfl, h1.symm, ha, Or.inl rfl⟩
  · cases h
    have hp : Precedes H ⟨a.p, y, nBefore H a y - 1⟩ a :=
      (precedes_iff_lt (hH.invoked_of_completed ha)).2 (by
        change nBefore H a y - 1 < nBefore H a y; omega)
    exact ⟨rfl, rfl, hp.completed, Or.inr hp⟩

/-- Every operation `d` of `a.p` preceding `a` is at or before the last operation of `a.p` on
`d.x` up to `a`. -/
lemma exists_wcLast (hH : WellFormed H) {a d : OpId P X} (ha : Completed H a) (hp : d.p = a.p)
    (hda : Precedes H d a) :
    ∃ d', wcLast H a d.x = some d' ∧ (d = d' ∨ Precedes H d d') := by
  by_cases hx : d.x = a.x
  · exact ⟨a, by simp [wcLast, hx], Or.inr hda⟩
  · have haI := hH.invoked_of_completed ha
    have hk := (precedes_iff_lt haI).1 hda
    rw [hp] at hk
    change d.k < nBefore H a d.x at hk
    refine ⟨⟨a.p, d.x, nBefore H a d.x - 1⟩, by simp [wcLast, hx]; omega, ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt hk) with h | h
    · right
      have hd' : Precedes H ⟨a.p, d.x, nBefore H a d.x - 1⟩ a :=
        (precedes_iff_lt haI).2 (by change nBefore H a d.x - 1 < nBefore H a d.x; omega)
      exact precedes_of_k_lt hH hp rfl (hH.invoked_of_completed hd'.completed) (by dsimp only; omega)
    · left; cases d; simp_all

/-- The block of `τ(a)` for object `y`: `τ_y(d)` for the last operation `d` of `a.p` on `y` up
to `a` (empty if there is none). -/
def wcBlock (τ : X → OpId P X → IdSeq P X Op Res) (H : History P X Op Res) (a : OpId P X)
    (y : X) : IdSeq P X Op Res :=
  match wcLast H a y with
  | none => []
  | some d => τ y d

/-- The objects of `H` other than `a.x`, followed by `a.x`. -/
def wcObjs (H : History P X Op Res) (a : OpId P X) : List X :=
  (H.map Event.obj).dedup.filter (· ≠ a.x) ++ [a.x]

/-- The glued witness: `τ(a)` is the concatenation of the blocks `wcBlock τ H a y` over the
objects `y` of `H` other than `a.x`, followed by `τ_{a.x}(a)`. -/
def wcGlue (τ : X → OpId P X → IdSeq P X Op Res) (H : History P X Op Res) (a : OpId P X) :
    IdSeq P X Op Res :=
  (wcObjs H a).flatMap (wcBlock τ H a)

omit [DecidableEq P] in
lemma wcObjs_nodup (H : History P X Op Res) (a : OpId P X) : (wcObjs H a).Nodup := by
  unfold wcObjs
  rw [List.nodup_append]
  refine ⟨(List.nodup_dedup _).filter _, List.nodup_singleton _, ?_⟩
  simp

section Glue

variable {τ : X → OpId P X → IdSeq P X Op Res} (hH : WellFormed H)
  (hτ : ∀ x, WCWitness spec (restrictX H x) (τ x))
include hH hτ

lemma wcBlock_cases {a : OpId P X} (ha : Completed H a) (y : X) :
    wcBlock τ H a y = [] ∨ ∃ d, wcLast H a y = some d ∧ wcBlock τ H a y = τ y d ∧
      d.p = a.p ∧ d.x = y ∧ (d = a ∨ Precedes H d a) ∧
      IsSeqOf spec (restrictX H y) (τ y d) ∧ (∀ c ∈ (τ y d).ids, ¬ Precedes H d c) := by
  unfold wcBlock
  cases hd : wcLast H a y with
  | none => exact Or.inl rfl
  | some d =>
    obtain ⟨hdp, hdx, hdc, hda⟩ := wcLast_spec hH ha hd
    have hdc' : Completed (restrictX H y) d := completed_restrictX.2 ⟨hdx, hdc⟩
    obtain ⟨hs, -, h2, -⟩ := hτ y d hdc'
    refine Or.inr ⟨d, rfl, rfl, hdp, hdx, hda, hs, fun c hc => ?_⟩
    rw [← precedes_restrictX hdx (hs.ids_obj hc).1]; exact h2 c hc

lemma wcBlock_obj {a : OpId P X} (ha : Completed H a) (y : X) :
    ∀ u ∈ wcBlock τ H a y, u.1.x = y := by
  intro u hu
  rcases wcBlock_cases hH hτ ha y with h | ⟨d, -, h, -, -, -, hs, -⟩
  · rw [h] at hu; simp at hu
  · rw [h] at hu; exact (hs.obj_eq hu).1

/-- The restriction of the glued witness to `y` is its block for `y`. -/
lemma wcGlue_filter {a : OpId P X} (ha : Completed H a) (y : X) :
    (wcGlue τ H a).filter (·.1.x = y) = wcBlock τ H a y := by
  unfold wcGlue
  rw [filter_flatMap_obj (wcObjs_nodup H a) _ (fun z _ => wcBlock_obj hH hτ ha z)]
  split_ifs with hy
  · rfl
  · rcases wcBlock_cases hH hτ ha y with h | ⟨d, -, h, -, hdx, hda, -, -⟩
    · exact h.symm
    · exfalso; apply hy
      have hdc : Completed H d := by rcases hda with rfl | h; exacts [ha, h.completed]
      subst hdx
      unfold wcObjs
      by_cases hya : d.x = a.x
      · simp [hya]
      · simp [hya, obj_mem_of_invoked (hH.invoked_of_completed hdc)]

lemma mem_wcGlue_ids {a : OpId P X} (ha : Completed H a) {c : OpId P X} :
    c ∈ (wcGlue τ H a).ids ↔ c ∈ (wcBlock τ H a c.x).ids := by
  rw [← wcGlue_filter hH hτ ha c.x, IdSeq.ids_filter, List.mem_filter]; simp

/-- The glued family satisfies (i)–(iii) for `H`. -/
theorem wcGlue_spec : WCWitness spec H (wcGlue τ H) := by
  intro a ha
  have haa : wcBlock τ H a a.x = τ a.x a := by simp [wcBlock, wcLast]
  have hca : Completed (restrictX H a.x) a := completed_restrictX.2 ⟨rfl, ha⟩
  obtain ⟨hsa, ⟨e, hlast, hres⟩, -, -⟩ := hτ a.x a hca
  refine ⟨IsSeqOf.of_filter fun y => ?_, ⟨e, ?_, by rwa [resOf_restrictX rfl] at hres⟩, ?_, ?_⟩
  · rw [wcGlue_filter hH hτ ha y]
    rcases wcBlock_cases hH hτ ha y with h | ⟨d, -, h, -, -, -, hs, -⟩
    · refine Or.inr ⟨h, ?_⟩
      by_cases hy : y = a.x
      · subst hy; rw [haa] at h; simp [h] at hlast
      · have := (legal_seqHist_iff spec _).1 hsa.legal y
        rwa [List.filter_eq_nil_iff.2] at this
        intro r hr
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
        simp [(hsa.obj_eq hu).2, Ne.symm hy]
    · left; rw [h]; exact hs
  · unfold wcGlue wcObjs
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, haa,
      List.getLast?_append, hlast]
    rfl
  · intro c hc hac
    rw [mem_wcGlue_ids hH hτ ha] at hc
    rcases wcBlock_cases hH hτ ha c.x with h | ⟨d, -, h, -, -, hda, -, h2⟩
    · rw [h] at hc; simp at hc
    · rw [h] at hc
      rcases hda with rfl | hda
      · exact h2 c hc hac
      · exact h2 c hc (hda.trans hH hac)
  · intro b hbp hba c hc
    have hb := hba.completed
    rw [mem_wcGlue_ids hH hτ hb] at hc
    rw [mem_wcGlue_ids hH hτ ha]
    rcases wcBlock_cases hH hτ hb c.x with h | ⟨d', -, h, hd'p, hd'x, hd'b, -, -⟩
    · rw [h] at hc; simp at hc
    rw [h] at hc
    have hd'a : Precedes H d' a := by
      rcases hd'b with rfl | h; exacts [hba, h.trans hH hba]
    obtain ⟨d, hd, hdd⟩ := exists_wcLast hH ha (hd'p.trans hbp) hd'a
    rw [hd'x] at hd
    have hblk : wcBlock τ H a c.x = τ c.x d := by simp [wcBlock, hd]
    rw [hblk]
    rcases hdd with rfl | hdd
    · exact hc
    · obtain ⟨hdp, hdx, hdc, -⟩ := wcLast_spec hH ha hd
      exact (hτ c.x d (completed_restrictX.2 ⟨hdx, hdc⟩)).2.2.2 d'
        (hd'p.trans (hbp.trans hdp.symm)) ((precedes_restrictX hd'x hdx).2 hdd) c hc

end Glue

/-- **Lemma 1** of [Serafini et al., PODC 2010], "if" direction: if every `H|x` is weakly
consistent, so is `H`. (The witness is `wcGlue`, not the paper's `τ_x(i, o)`; see the module
docstring.) -/
theorem weaklyConsistent_of_restrictX (hH : WellFormed H)
    (h : ∀ x, WeaklyConsistent spec (restrictX H x)) : WeaklyConsistent spec H := by
  choose τ hτ using h
  exact ⟨wcGlue τ H, wcGlue_spec hH hτ⟩

/-- **Lemma 1** of [Serafini et al., PODC 2010]: weak consistency is local. -/
theorem weaklyConsistent_iff_restrictX (hH : WellFormed H) (hnil : ∀ y, [] ∈ spec y) :
    WeaklyConsistent spec H ↔ ∀ x, WeaklyConsistent spec (restrictX H x) :=
  ⟨weaklyConsistent_restrictX hnil, weaklyConsistent_of_restrictX hH⟩

/-! ### Lemma 2: `t`-linearizability is local -/

/-- **Lemma 2** of [Serafini et al., PODC 2010], "only if" direction: a `t`-linearization of
`H`, restricted to `x`, is a `t`-linearization of `H|x`. -/
theorem IsTLin.restrictX (hnil : ∀ y, [] ∈ spec y) {A : Set (OpId P X)} {L : IdSeq P X Op Res}
    (hL : IsTLin spec H A L) (x : X) :
    IsTLin spec (Cslib.SharedMemory.HerlihyWing.restrictX H x) A (L.filter (·.1.x = x)) := by
  refine ⟨⟨hL.toIsSeqOf.restrict hnil x, fun a ha => ?_, fun a b hab => ?_⟩,
    fun a e hae ha hc => ?_⟩
  · obtain ⟨hax, ha⟩ := invoked_restrictX.1 ha
    rw [IdSeq.ids_filter, List.mem_filter]; exact ⟨hL.all a ha, by simp [hax]⟩
  · obtain ⟨hbA, hbI, hp⟩ := hab
    obtain ⟨hbx, hbI⟩ := invoked_restrictX.1 hbI
    have hax := (completed_restrictX.1 hp.completed).1
    rw [precedes_restrictX hax hbx] at hp
    have := (hL.order a b ⟨hbA, hbI, hp⟩).filter (fun c : OpId P X => decide (c.x = x))
    rw [IdSeq.ids_filter]; simpa [hax, hbx] using this
  · obtain ⟨hae, hax⟩ := List.mem_filter.1 hae
    have hax : a.x = x := by simpa using hax
    rw [resOf_restrictX hax]; exact hL.results a e hae ha (completed_restrictX.1 hc).2

/-- **Lemma 2** of [Serafini et al., PODC 2010], "only if" direction. -/
theorem tLinearizable_restrictX (hnil : ∀ y, [] ∈ spec y) {A : Set (OpId P X)}
    (h : TLinearizable spec H A) (x : X) : TLinearizable spec (restrictX H x) A :=
  h.elim fun _ hL => ⟨_, hL.restrictX hnil x⟩

open Classical in
/-- The sort key of an entry `a` of `L_{a.x}`: the largest invocation time of a late operation
(in `A`) at or before `a` in `L_{a.x}` (`0` if there is none). -/
noncomputable def tKey (H : History P X Op Res) (A : Set (OpId P X))
    (Ls : X → IdSeq P X Op Res) (a : OpId P X) : ℕ :=
  ((Ls a.x).ids.toFinset.filter fun c => c ∈ A ∧ (c = a ∨ [c, a].Sublist (Ls a.x).ids)).sup
    (tInv H)

/-- The merged `t`-linearization: the concatenation of the `L_x` stably sorted by `tKey`. -/
noncomputable def tMerge (H : History P X Op Res) (A : Set (OpId P X))
    (Ls : X → IdSeq P X Op Res) : IdSeq P X Op Res :=
  ((H.map Event.obj).dedup.flatMap Ls).mergeSort
    (fun u v => decide (tKey H A Ls u.1 ≤ tKey H A Ls v.1))

section Merge

variable {A : Set (OpId P X)} {Ax : X → Set (OpId P X)} {Ls : X → IdSeq P X Op Res}

/-- Keys are monotone along each `L_x`. -/
lemma tKey_mono (hLs : ∀ x, IsTLin spec (restrictX H x) (Ax x) (Ls x)) {x : X}
    {a b : OpId P X} (hab : [a, b].Sublist (Ls x).ids) : tKey H A Ls a ≤ tKey H A Ls b := by
  have hax := ((hLs x).toIsSeqOf.ids_obj (hab.subset (by simp : a ∈ [a, b]))).1
  have hbx := ((hLs x).toIsSeqOf.ids_obj (hab.subset (by simp : b ∈ [a, b]))).1
  unfold tKey; rw [hax, hbx]
  apply Finset.sup_mono
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  refine ⟨hc.1, hc.2.1, Or.inr ?_⟩
  rcases hc.2.2 with rfl | h
  · exact hab
  · exact pair_sublist_trans (hLs x).nodup h hab

/-- Keys strictly increase along `<_{H,t}`. -/
lemma tKey_lt (hH : WellFormed H) (hA : ∀ x, A ⊆ Ax x)
    (hLs : ∀ x, IsTLin spec (restrictX H x) (Ax x) (Ls x)) {a b : OpId P X}
    (hab : RTAfter H A a b) : tKey H A Ls a < tKey H A Ls b := by
  obtain ⟨hbA, hbI, hp⟩ := hab
  have ha := hp.completed
  have hbL : b ∈ (Ls b.x).ids := (hLs b.x).all b (invoked_restrictX.2 ⟨rfl, hbI⟩)
  have hrb : tRes H a < tInv H b := (precedes_iff.1 hp).2
  have h1 : tInv H b ≤ tKey H A Ls b := by
    unfold tKey
    exact Finset.le_sup (f := tInv H) (by simp [hbL, hbA])
  have h2 : tKey H A Ls a < tInv H b := by
    unfold tKey
    rw [Finset.sup_lt_iff (by simpa using tInv_pos H b)]
    intro c hc
    simp only [Finset.mem_filter, List.mem_toFinset] at hc
    obtain ⟨hcL, hcA, hca⟩ := hc
    suffices tInv H c < tRes H a by omega
    rcases hca with rfl | hca
    · exact tInv_lt_tRes hH ha
    · obtain ⟨hcx, hcI⟩ := (hLs a.x).toIsSeqOf.ids_obj hcL
      by_contra hge
      have hlt : tRes H a < tInv H c :=
        lt_of_le_of_ne (not_lt.1 hge) (fun h => tInv_ne_tRes hcI ha h.symm)
      have hac : RTAfter (restrictX H a.x) (Ax a.x) a c :=
        ⟨hA _ hcA, invoked_restrictX.2 ⟨hcx, hcI⟩,
          (precedes_restrictX rfl hcx).2 (precedes_iff.2 ⟨ha, hlt⟩)⟩
      exact pair_sublist_asymm (hLs a.x).nodup ((hLs a.x).order a c hac) hca
  omega

lemma flatMap_filter_Ls (hLs : ∀ x, IsTLin spec (restrictX H x) (Ax x) (Ls x)) (y : X) :
    ((H.map Event.obj).dedup.flatMap Ls).filter (·.1.x = y) = Ls y := by
  rw [filter_flatMap_obj (List.nodup_dedup _) Ls
    (fun z _ u hu => ((hLs z).toIsSeqOf.obj_eq hu).1)]
  split_ifs with hy
  · rfl
  · rcases hL : Ls y with _ | ⟨u, l⟩
    · rfl
    · exfalso; apply hy
      have hu : u ∈ Ls y := by simp [hL]
      obtain ⟨hux, huI⟩ := invoked_restrictX.1 ((hLs y).toIsSeqOf.invoked hu)
      rw [List.mem_dedup, ← hux]; exact obj_mem_of_invoked huI

private lemma key_trans (u v w : OpId P X × OpRec P X Op Res)
    (h1 : decide (tKey H A Ls u.1 ≤ tKey H A Ls v.1) = true)
    (h2 : decide (tKey H A Ls v.1 ≤ tKey H A Ls w.1) = true) :
    decide (tKey H A Ls u.1 ≤ tKey H A Ls w.1) = true := by
  simp only [decide_eq_true_eq] at *; omega

private lemma key_total (u v : OpId P X × OpRec P X Op Res) :
    (decide (tKey H A Ls u.1 ≤ tKey H A Ls v.1) ||
      decide (tKey H A Ls v.1 ≤ tKey H A Ls u.1)) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]; omega

lemma tMerge_pairwise :
    (tMerge H A Ls).Pairwise (fun u v => tKey H A Ls u.1 ≤ tKey H A Ls v.1) := by
  simpa [tMerge] using List.pairwise_mergeSort key_trans key_total
    ((H.map Event.obj).dedup.flatMap Ls)

/-- The merged sequence restricted to `y` is `L_y`. -/
lemma tMerge_filter (hLs : ∀ x, IsTLin spec (restrictX H x) (Ax x) (Ls x)) (y : X) :
    (tMerge H A Ls).filter (·.1.x = y) = Ls y := by
  have hpw : (Ls y).Pairwise
      (fun u v => decide (tKey H A Ls u.1 ≤ tKey H A Ls v.1) = true) := by
    rw [List.pairwise_iff_forall_sublist]
    intro u v huv
    simpa using tKey_mono (A := A) hLs (by simpa using huv.map Prod.fst)
  have hsub : (Ls y).Sublist (tMerge H A Ls) := List.sublist_mergeSort key_trans key_total hpw
    (by rw [← flatMap_filter_Ls hLs y]; exact List.filter_sublist)
  have hsub' : (Ls y).Sublist ((tMerge H A Ls).filter (·.1.x = y)) := by
    have := hsub.filter (fun u => decide (u.1.x = y))
    rwa [List.filter_eq_self.2 (fun u hu => by simp [((hLs y).toIsSeqOf.obj_eq hu).1])] at this
  have hperm : (tMerge H A Ls).Perm ((H.map Event.obj).dedup.flatMap Ls) :=
    List.mergeSort_perm _ _
  refine (hsub'.eq_of_length ?_).symm
  rw [(hperm.filter _).length_eq, flatMap_filter_Ls hLs y]

/-- The merged sequence is a `t`-linearization of `H` (for any `A ⊆ A_x`). -/
theorem isTLin_tMerge (hH : WellFormed H) (hA : ∀ x, A ⊆ Ax x)
    (hLs : ∀ x, IsTLin spec (restrictX H x) (Ax x) (Ls x)) :
    IsTLin spec H A (tMerge H A Ls) := by
  have hs : IsSeqOf spec H (tMerge H A Ls) :=
    IsSeqOf.of_filter fun y => Or.inl (by rw [tMerge_filter hLs y]; exact (hLs y).toIsSeqOf)
  have hall : ∀ a, Invoked H a → a ∈ (tMerge H A Ls).ids := by
    intro a ha
    have : a ∈ (Ls a.x).ids := (hLs a.x).all a (invoked_restrictX.2 ⟨rfl, ha⟩)
    rw [← tMerge_filter hLs a.x, IdSeq.ids_filter] at this
    exact (List.mem_filter.1 this).1
  refine ⟨⟨hs, hall, fun a b hab => ?_⟩, fun a e hae ha hc => ?_⟩
  · have hlt := tKey_lt hH hA hLs hab
    have haI : Invoked H a := hH.invoked_of_completed hab.2.2.completed
    have hne : a ≠ b := by rintro rfl; omega
    rcases pair_sublist_total hs.nodup (hall a haI) (hall b hab.2.1) hne with h | h
    · exact h
    · exfalso
      have := List.pairwise_iff_forall_sublist.1 ((List.pairwise_map (f := Prod.fst)
        (R := fun a b => tKey H A Ls a ≤ tKey H A Ls b)).2 tMerge_pairwise) h
      omega
  · have hae' : (a, e) ∈ Ls a.x := by
      rw [← tMerge_filter hLs a.x]; exact List.mem_filter.2 ⟨hae, by simp⟩
    have := (hLs a.x).results a e hae' (hA _ ha) (completed_restrictX.2 ⟨rfl, hc⟩)
    rwa [resOf_restrictX rfl] at this

end Merge

/-- **Lemma 2** of [Serafini et al., PODC 2010], "if" direction, for arbitrary sets of late
operations: if every `H|x` is linearizable w.r.t. late operations `A_x`, then `H` is
linearizable w.r.t. any `A ⊆ ⋂ₓ A_x`. -/
theorem tLinearizable_of_restrictX (hH : WellFormed H) {A : Set (OpId P X)}
    {Ax : X → Set (OpId P X)} (hA : ∀ x, A ⊆ Ax x)
    (h : ∀ x, TLinearizable spec (restrictX H x) (Ax x)) : TLinearizable spec H A := by
  choose Ls hLs using h
  exact ⟨_, isTLin_tMerge hH hA hLs⟩

/-- **Lemma 2** of [Serafini et al., PODC 2010]: if `H|x` is `t_x`-linearizable for every object
`x`, then `H` is `t_max`-linearizable for every `t_max ≥ t_x` (for all `x`). -/
theorem tLinearizable_of_restrictX_after (hH : WellFormed H) (invTime : OpId P X → ℕ)
    (t : X → ℕ) (tmax : ℕ)
    (h : ∀ x, TLinearizable spec (restrictX H x) (after invTime (t x)))
    (htmax : ∀ x, t x ≤ tmax) : TLinearizable spec H (after invTime tmax) :=
  tLinearizable_of_restrictX hH (fun x => after_anti invTime (htmax x)) h

/-- `t`-linearizability (for a fixed set of late operations) is local. -/
theorem tLinearizable_iff_restrictX (hH : WellFormed H) (hnil : ∀ y, [] ∈ spec y)
    {A : Set (OpId P X)} :
    TLinearizable spec H A ↔ ∀ x, TLinearizable spec (restrictX H x) A :=
  ⟨tLinearizable_restrictX hnil, tLinearizable_of_restrictX hH (fun _ => subset_rfl)⟩

/-- Lemmas 1 and 2 combined: "weakly consistent and `t_max`-linearizable" follows from the same
property of every object subhistory with `t_x ≤ t_max`. -/
theorem weaklyConsistent_and_tLinearizable_of_restrictX (hH : WellFormed H)
    (invTime : OpId P X → ℕ) (t : X → ℕ) (tmax : ℕ)
    (h : ∀ x, WeaklyConsistent spec (restrictX H x) ∧
      TLinearizable spec (restrictX H x) (after invTime (t x)))
    (htmax : ∀ x, t x ≤ tmax) :
    WeaklyConsistent spec H ∧ TLinearizable spec H (after invTime tmax) :=
  ⟨weaklyConsistent_of_restrictX hH fun x => (h x).1,
    tLinearizable_of_restrictX_after hH invTime t tmax (fun x => (h x).2) htmax⟩

end Podc.EventualLinearizability
