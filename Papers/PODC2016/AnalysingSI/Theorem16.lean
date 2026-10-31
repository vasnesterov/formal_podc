import Papers.PODC2016.AnalysingSI.SpliceLemmas
import Papers.PODC2016.AnalysingSI.Robustness

/-!
# Theorem 16: the dynamic chopping criterion (Cerone–Gotsman, PODC 2016, §5 and §A.5)

If `G ∈ GraphSI` and `DCG(G)` contains no critical cycle, then `splice(G) ∈ GraphSI`; in
particular `G` is spliceable.

Proof (as in §A.5): a cycle of `(WR ∪ WW) ; RW?` in `splice(G)` gives (Theorem 19's translation,
`DepGraph.acyclic_si_iff`) a cycle of `splice(G)` without adjacent anti-dependencies, hence
(Lemma 24) a simple one. Each of its edges comes from a conflict edge of `G` between transactions
of the two sessions (equation (2), Lemma 17); joining consecutive representatives by session-order
edges gives a simple cycle of `DCG(G)`. If one of the joining edges is a predecessor edge, the
cycle is critical; otherwise it is a cycle of `G` without adjacent anti-dependencies,
contradicting `G ∈ GraphSI`.
-/

namespace Podc.AnalysingSI

open Relation

set_option linter.unusedSectionVars false

variable {Obj V : Type*} [DecidableEq Obj] {ι : Type*}

/-- A relation transported along a map of the list. -/
theorem cycAdj_of_map {L L' : Type*} {P : L' → L' → Prop} (f : L → L') {ls : List L}
    (h : CycAdj P (ls.map f)) : CycAdj (fun a b => P (f a) (f b)) ls := by
  rcases h with ⟨pre, a, b, suf, he, hab⟩ | ⟨a, mid, b, he, hba⟩
  · obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.map_eq_append_iff.1 he
    obtain ⟨a', l₃, rfl, rfl, h3⟩ := List.map_eq_cons_iff.1 h2
    obtain ⟨b', l₄, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 h3
    exact Or.inl ⟨l₁, a', b', l₄, rfl, hab⟩
  · obtain ⟨a', l₃, rfl, rfl, h3⟩ := List.map_eq_cons_iff.1 he
    obtain ⟨l₁, l₂, rfl, rfl, h2⟩ := List.map_eq_append_iff.1 h3
    obtain ⟨b', l₄, rfl, rfl, h4⟩ := List.map_eq_cons_iff.1 h2
    simp only [List.map_eq_nil_iff] at h4
    subst h4
    exact Or.inr ⟨a', l₁, b', rfl, hba⟩

theorem CycAdj.mono {L : Type*} {P Q : L → L → Prop} (hPQ : ∀ a b, P a b → Q a b) {ls : List L}
    (h : CycAdj P ls) : CycAdj Q ls := by
  rcases h with ⟨pre, a, b, suf, he, hab⟩ | ⟨a, mid, b, he, hba⟩
  · exact Or.inl ⟨pre, a, b, suf, he, hPQ _ _ hab⟩
  · exact Or.inr ⟨a, mid, b, he, hPQ _ _ hba⟩

namespace Chopped

/-- Labels of `splice(G)` as labels of `DCG(G)`. -/
def toC : DLbl → CLbl
  | .so => .succ
  | .wr => .wr
  | .ww => .ww
  | .rw => .rw

/-- Labels of `DCG(G)` as labels of `G` (successor edges are session-order edges). -/
def toD : CLbl → DLbl
  | .succ => .so
  | .pred => .so
  | .wr => .wr
  | .ww => .ww
  | .rw => .rw

@[simp] theorem toD_toC (l : DLbl) : toD (toC l) = l := by cases l <;> rfl

theorem toD_ne_so_iff (l : CLbl) : toD l ≠ .so ↔ l.IsConflict := by
  cases l <;> simp [toD, CLbl.IsConflict]

theorem toC_isConflict {l : DLbl} (hl : l ≠ .so) : (toC l).IsConflict := by
  cases l <;> simp_all [toC, CLbl.IsConflict]

theorem toC_eq_rw {l : DLbl} (h : toC l = .rw) : l = .rw := by
  cases l <;> simp_all [toC]

variable {C : Chopped ι Obj V} {WR WW : Obj → C.Tid → C.Tid → Prop}

/-- A segment of the lifted cycle for the edge `e = (l, v)` of `splice(G)`: the conflict edge into
a transaction `b` of session `v`, optionally followed by a session-order edge to another
transaction `d` of session `v`. -/
def SegR (e : DLbl × ι) (seg : List (CLbl × C.Tid)) : Prop :=
  e.1 ≠ .so ∧ ((∃ b : C.Tid, b.1.1 = e.2 ∧ seg = [(toC e.1, b)]) ∨
    (∃ b d : C.Tid, ∃ sib : CLbl, b.1.1 = e.2 ∧ d.1.1 = e.2 ∧ b ≠ d ∧
      (sib = .succ ∨ sib = .pred) ∧ seg = [(toC e.1, b), (sib, d)]))

namespace Hyp

variable (h : Hyp C WR WW)
include h

/-- Every edge of `splice(G)` comes from a conflict edge of `DCG(G)` (equation (2), Lemma 17). -/
theorem rep {l : DLbl} {s t : ι} (he : (C.spliceGraph WR WW).edge l s t) :
    l ≠ .so ∧ s ≠ t ∧ ∃ a b : C.Tid, a.1.1 = s ∧ b.1.1 = t ∧ dcg (C.graph WR WW) (toC l) a b := by
  cases l with
  | so => exact he.elim
  | wr =>
    obtain ⟨x, hne, p, q, rfl, rfl, hpq⟩ := he
    exact ⟨by decide, hne, p, q, rfl, rfl, ⟨x, hpq⟩, hne⟩
  | ww =>
    obtain ⟨x, hne, p, q, rfl, rfl, hpq⟩ := he
    exact ⟨by decide, hne, p, q, rfl, rfl, ⟨x, hpq⟩, hne⟩
  | rw =>
    obtain ⟨x, hx⟩ := he
    obtain ⟨hne, p, q, rfl, rfl, hpq⟩ := h.lemma17 hx
    exact ⟨by decide, hne, p, q, rfl, rfl, ⟨x, hpq⟩, hne⟩

end Hyp

/-- One step of the lifting: prepend the segment for an edge `(l, v)`. -/
theorem lift_step {l : DLbl} {v : ι} (hl : l ≠ .so) {a₁ b₁ a' fin : C.Tid}
    (hd : dcg (C.graph WR WW) (toC l) a₁ b₁) (hb₁ : b₁.1.1 = v) (ha' : a'.1.1 = v)
    {W : List (CLbl × C.Tid)} (hW : Walk (dcg (C.graph WR WW)) a' W fin) :
    ∃ seg, SegR (l, v) seg ∧ Walk (dcg (C.graph WR WW)) a₁ (seg ++ W) fin := by
  by_cases hba : b₁ = a'
  · subst hba
    exact ⟨_, ⟨hl, Or.inl ⟨b₁, hb₁, rfl⟩⟩, Walk.cons hd hW⟩
  · rcases tid_trich (WR := WR) (WW := WW) (p := b₁) (q := a') (hb₁.trans ha'.symm) with
      e | so | so
    · exact absurd e hba
    · exact ⟨_, ⟨hl, Or.inr ⟨b₁, a', .succ, hb₁, ha', hba, Or.inl rfl, rfl⟩⟩,
        Walk.cons hd (Walk.cons (l := CLbl.succ) so hW)⟩
    · exact ⟨_, ⟨hl, Or.inr ⟨b₁, a', .pred, hb₁, ha', hba, Or.inr rfl, rfl⟩⟩,
        Walk.cons hd (Walk.cons (l := CLbl.pred) so hW)⟩

/-- Lifting a walk of `splice(G)` to a walk of `DCG(G)` ending at a prescribed transaction. -/
theorem Hyp.lift (h : Hyp C WR WW) {s t : ι} {w : List (DLbl × ι)}
    (hw : Walk (C.spliceGraph WR WW).edge s w t) :
    ∀ fin : C.Tid, fin.1.1 = t → ∃ a : C.Tid, ∃ segs : List (List (CLbl × C.Tid)),
      a.1.1 = s ∧ Walk (dcg (C.graph WR WW)) a segs.flatten fin ∧ List.Forall₂ SegR w segs := by
  induction hw with
  | nil a =>
    intro fin hfin
    exact ⟨fin, [], hfin, Walk.nil _, List.Forall₂.nil⟩
  | cons he _ ih =>
    intro fin hfin
    obtain ⟨a', segs', ha', hW', hF'⟩ := ih fin hfin
    obtain ⟨hl, -, a₁, b₁, ha₁, hb₁, hd⟩ := h.rep he
    obtain ⟨seg, hseg, hW⟩ := lift_step hl hd hb₁ ha' hW'
    exact ⟨a₁, seg :: segs', ha₁, by simpa using hW, List.Forall₂.cons hseg hF'⟩

/-! ### Properties of lifted cycles -/

theorem segs_sess {w : List (DLbl × ι)} {segs : List (List (CLbl × C.Tid))}
    (hF : List.Forall₂ SegR w segs) :
    ∀ x ∈ segs.flatten.map Prod.snd, x.1.1 ∈ w.map Prod.snd := by
  induction hF with
  | nil => simp
  | cons hseg _ ih =>
    rename_i e seg w' segs'
    intro x hx
    simp only [List.flatten_cons, List.map_append, List.mem_append] at hx
    rcases hx with hx | hx
    · rcases hseg with ⟨-, ⟨b, hb, rfl⟩ | ⟨b, d, sib, hb, hd, -, -, rfl⟩⟩
      · simp at hx; subst hx; simp [hb]
      · simp at hx; rcases hx with rfl | rfl <;> simp [hb, hd]
    · exact List.mem_cons_of_mem _ (ih x hx)

theorem segs_nodup {w : List (DLbl × ι)} {segs : List (List (CLbl × C.Tid))}
    (hF : List.Forall₂ SegR w segs) (hw : (w.map Prod.snd).Nodup) :
    (segs.flatten.map Prod.snd).Nodup := by
  induction hF with
  | nil => simp
  | cons hseg hF' ih =>
    rename_i e seg w' segs'
    simp only [List.map_cons, List.nodup_cons] at hw
    simp only [List.flatten_cons, List.map_append, List.nodup_append]
    have hsess := segs_sess hF'
    have hin : ∀ x ∈ seg.map Prod.snd, x.1.1 = e.2 := by
      rcases hseg with ⟨-, ⟨b, hb, rfl⟩ | ⟨b, d, sib, hb, hd, -, -, rfl⟩⟩
      · simpa using hb
      · simp [hb, hd]
    refine ⟨?_, ih hw.2, ?_⟩
    · rcases hseg with ⟨-, ⟨b, hb, rfl⟩ | ⟨b, d, sib, hb, hd, hbd, -, rfl⟩⟩
      · simp
      · simpa using hbd
    · intro x hx y hy hxy
      subst hxy
      exact hw.1 (by rw [← hin x hx]; exact hsess x hy)

theorem segs_filter {w : List (DLbl × ι)} {segs : List (List (CLbl × C.Tid))}
    (hF : List.Forall₂ SegR w segs) :
    (labels segs.flatten).filter (fun l => decide l.IsConflict) = (labels w).map toC := by
  induction hF with
  | nil => simp [labels]
  | cons hseg _ ih =>
    rename_i e seg w' segs'
    simp only [labels, List.flatten_cons, List.map_append, List.filter_append, List.map_cons] at ih ⊢
    rw [ih]
    rcases hseg with ⟨hl, ⟨b, hb, rfl⟩ | ⟨b, d, sib, hb, hd, -, hsib, rfl⟩⟩
    · simp [toC_isConflict hl]
    · rcases hsib with rfl | rfl <;>
      · simp only [List.map_cons, List.map_nil, List.filter_cons,
          decide_eq_true (toC_isConflict hl)]
        simp [CLbl.IsConflict]

theorem segs_head {w : List (DLbl × ι)} {segs : List (List (CLbl × C.Tid))}
    (hF : List.Forall₂ SegR w segs) :
    ∀ seg ∈ segs, ∃ c x rest, seg = (c, x) :: rest ∧ c.IsConflict ∧
      (rest = [] ∨ ∃ sib d, rest = [(sib, d)] ∧ (sib = .succ ∨ sib = .pred)) := by
  induction hF with
  | nil => simp
  | cons hseg _ ih =>
    intro seg' hseg'
    rcases List.mem_cons.1 hseg' with rfl | hm
    · rcases hseg with ⟨hl, ⟨b, hb, rfl⟩ | ⟨b, d, sib, hb, hd, -, hsib, rfl⟩⟩
      · exact ⟨_, _, _, rfl, toC_isConflict hl, Or.inl rfl⟩
      · exact ⟨_, _, _, rfl, toC_isConflict hl, Or.inr ⟨sib, d, rfl, hsib⟩⟩
    · exact ih seg' hm

/-- Condition (ii) of critical cycles for a lifted cycle containing a predecessor edge. -/
theorem segs_cpc {w : List (DLbl × ι)} {segs : List (List (CLbl × C.Tid))}
    (hF : List.Forall₂ SegR w segs) (hlen : 2 ≤ segs.length)
    (hpred : CLbl.pred ∈ labels segs.flatten) :
    ∃ k c₁ c₂ rest, (labels segs.flatten).rotate k = c₁ :: .pred :: c₂ :: rest ∧
      c₁.IsConflict ∧ c₂.IsConflict := by
  have hhead := segs_head hF
  simp only [labels, List.map_flatten, List.mem_flatten, List.mem_map] at hpred
  obtain ⟨_, ⟨seg, hseg, rfl⟩, hmem⟩ := hpred
  obtain ⟨c, x, rest, rfl, hc, hrest⟩ := hhead seg hseg
  rcases hrest with rfl | ⟨sib, d, rfl, hsib⟩
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
    subst hmem; exact absurd hc (by simp [CLbl.IsConflict])
  · have hsibp : sib = .pred := by
      simp only [List.map_cons, List.map_nil, List.mem_cons, 
        List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1
      · subst h1; exact absurd hc (by simp [CLbl.IsConflict])
      · exact h1.symm
    subst hsibp
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hseg
    have hBA : B ++ A ≠ [] := by
      intro h0
      simp only [List.append_eq_nil_iff] at h0
      obtain ⟨rfl, rfl⟩ := h0
      simp at hlen
    obtain ⟨seg0, rest0, hsr⟩ := List.exists_cons_of_ne_nil hBA
    obtain ⟨c₂, y, rest', hseg0, hc₂, -⟩ := hhead seg0 (by
      have : seg0 ∈ B ++ A := by rw [hsr]; exact List.mem_cons_self
      simp only [List.mem_append] at this ⊢
      rcases this with h1 | h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)
      · exact Or.inl h1)
    refine ⟨(A.flatten.map Prod.fst).length, c, c₂,
      (rest'.map Prod.fst) ++ (rest0.flatten.map Prod.fst), ?_, hc, hc₂⟩
    have key : ((B ++ A).flatten.map Prod.fst) = c₂ :: ((rest'.map Prod.fst) ++
        (rest0.flatten.map Prod.fst)) := by
      rw [hsr, List.flatten_cons, hseg0]; simp
    simp only [labels, List.flatten_append, List.flatten_cons, List.map_append] at key ⊢
    rw [List.rotate_append_length_eq]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [key]

/-! ### Theorem 16 -/

/-- **Theorem 16** of Cerone–Gotsman, in the form proved in §A.5: if `G ∈ GraphSI` and `DCG(G)`
contains no critical cycle, then `splice(G) ∈ GraphSI`. -/
theorem theorem16_splice (C : Chopped ι Obj V) (WR WW : Obj → C.Tid → C.Tid → Prop)
    (hG : (C.graph WR WW).IsSI) (hcrit : ∀ w, ¬ IsCritical (C.graph WR WW) w) :
    (C.spliceGraph WR WW).IsSI := by
  have h : Hyp C WR WW := ⟨hG.1, hG.2.1, hG.2.2, hcrit⟩
  refine ⟨h.lemma26, h.lemma27, ?_⟩
  rw [DepGraph.acyclic_si_iff]
  intro w hw
  by_contra hn
  obtain ⟨w₁, hw₁, hs₁, hn₁⟩ := lemma24 (P := fun a b => a = DLbl.rw ∧ b = DLbl.rw)
    (fun a b c d h1 h2 => ⟨h1.1, h2.2⟩) hw hn
  obtain ⟨hne, s₀, hwalk⟩ := hw₁
  obtain ⟨⟨l₁, s₁⟩, w', rfl⟩ := List.exists_cons_of_ne_nil hne
  cases hwalk with
  | cons he hw' =>
  obtain ⟨hl₁, hss, a₁, b₁, ha₁, hb₁, hd₁⟩ := h.rep he
  obtain ⟨a', segs', ha', hW', hF'⟩ := h.lift hw' a₁ ha₁
  obtain ⟨seg₁, hseg₁, hW⟩ := lift_step hl₁ hd₁ hb₁ ha' hW'
  have hF : List.Forall₂ SegR ((l₁, s₁) :: w') (seg₁ :: segs') := List.Forall₂.cons hseg₁ hF'
  have hWalk : Walk (dcg (C.graph WR WW)) a₁ (seg₁ :: segs').flatten a₁ := by simpa using hW
  have hlen : 2 ≤ (seg₁ :: segs').length := by
    have := hF'.length_eq
    cases w' with
    | nil => cases hw'; exact absurd rfl hss
    | cons _ _ => simp only [List.length_cons] at this ⊢; omega
  have hWne : (seg₁ :: segs').flatten ≠ [] := by
    rcases hseg₁ with ⟨-, ⟨b, -, rfl⟩ | ⟨b, d, sib, -, -, -, -, rfl⟩⟩ <;> simp
  by_cases hpred : CLbl.pred ∈ labels (seg₁ :: segs').flatten
  · -- a predecessor edge: the lifted cycle is critical
    refine hcrit _ ⟨⟨hWne, a₁, hWalk⟩, segs_nodup hF hs₁, segs_cpc hF hlen hpred, ?_⟩
    intro k mid rest hrot
    by_contra hno
    push Not at hno
    obtain ⟨k', hk'⟩ := exists_filter_rotate (fun l : CLbl => decide (CLbl.IsConflict l))
      (labels (seg₁ :: segs').flatten) k
    rw [hrot, segs_filter hF] at hk'
    have hmid : ∀ c ∈ mid.filter (fun l => decide l.IsConflict), c = CLbl.rw := by
      intro c hc
      simp only [List.mem_filter, decide_eq_true_eq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      obtain ⟨n1, n2⟩ := hno c hc1
      cases c <;> simp_all [CLbl.IsConflict]
    have hadj : CycAdj (fun a b => a = CLbl.rw ∧ b = CLbl.rw)
        ((CLbl.rw :: (mid ++ CLbl.rw :: rest)).filter (fun l => decide l.IsConflict)) := by
      have hrwp : decide CLbl.rw.IsConflict = true := by decide
      cases hm : mid.filter (fun l => decide l.IsConflict) with
      | nil =>
        exact Or.inl ⟨[], .rw, .rw, rest.filter (fun l => decide l.IsConflict),
          by simp only [List.filter_cons, List.filter_append, hm, hrwp, ↓reduceIte,
            List.nil_append], rfl, rfl⟩
      | cons c t =>
        have hc : c = .rw := hmid c (by rw [hm]; exact List.mem_cons_self)
        subst hc
        exact Or.inl ⟨[], .rw, .rw, t ++ .rw :: rest.filter (fun l => decide l.IsConflict),
          by simp only [List.filter_cons, List.filter_append, hm, hrwp, ↓reduceIte,
            List.cons_append, List.nil_append], rfl, rfl⟩
    rw [hk', cycAdj_rotate_iff] at hadj
    exact hn₁ ((cycAdj_of_map toC hadj).mono fun a b hab => ⟨toC_eq_rw hab.1, toC_eq_rw hab.2⟩)
  · -- only successor edges: a cycle of `G` without adjacent anti-dependencies
    have hWG : Walk (C.graph WR WW).edge a₁ ((seg₁ :: segs').flatten.map (Prod.map toD id))
        a₁ := by
      refine Walk.map toD (fun l hl x y hxy => ?_) hWalk
      cases l with
      | succ => exact hxy
      | pred => exact absurd hl hpred
      | wr => exact hxy.1
      | ww => exact hxy.1
      | rw => exact hxy.1
    have hadj := (DepGraph.acyclic_si_iff (C.graph WR WW)).1 hG.2.2 _
      ⟨by simpa using hWne, a₁, hWG⟩
    unfold DepGraph.HasAdjRW at hadj
    have hlab : labels ((seg₁ :: segs').flatten.map (Prod.map toD id)) =
        (labels (seg₁ :: segs').flatten).map toD := by
      simp only [labels, List.map_map]
      rfl
    rw [hlab] at hadj
    have hf := hadj.filter (p := fun l => decide (l ≠ DLbl.so))
      (fun a b hab => by simp [hab.1, hab.2])
    rw [List.filter_map] at hf
    have hfe : List.filter ((fun l => decide (l ≠ DLbl.so)) ∘ toD)
        (labels (seg₁ :: segs').flatten) =
        (labels (seg₁ :: segs').flatten).filter (fun l => decide l.IsConflict) := by
      congr 1
      funext l
      cases l <;> rfl
    rw [hfe, segs_filter hF, List.map_map] at hf
    have hid : toD ∘ toC = id := funext toD_toC
    rw [hid, List.map_id] at hf
    exact hn₁ hf

/-- **Theorem 16** of Cerone–Gotsman: for `G ∈ GraphSI`, if `DCG(G)` contains no critical cycles,
then `G` is spliceable. -/
theorem theorem16 (C : Chopped ι Obj V) (WR WW : Obj → C.Tid → C.Tid → Prop)
    (hG : (C.graph WR WW).IsSI) (hcrit : ∀ w, ¬ IsCritical (C.graph WR WW) w) :
    C.Spliceable :=
  ⟨_, _, theorem16_splice C WR WW hG hcrit⟩

end Chopped

end Podc.AnalysingSI
