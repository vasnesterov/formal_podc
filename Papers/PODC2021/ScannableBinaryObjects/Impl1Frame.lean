import Papers.PODC2021.ScannableBinaryObjects.Impl1Lin
import Cslib.Computability.Distributed.SharedMemory.History

/-!
# Implementation 1: frame lemmas for the linearizability invariant

How the per-process invariant `PInvL` of a process `p` survives a step of another process,
for the three ways the linearization changes: unchanged, an update appended (its linearization
point), a scan inserted retroactively.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable.Impl1

open List

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P] {Sc Up : Finset P}
  {α : List (Label P (scannable O))} {ℓ : Label P (scannable O)} {p : P}

variable {L L₁ L₂ : List (OpId P × ScanOp O)} {x : OpId P} {o : ScanOp O}

lemma Cut.append (hx : opOf α x = some o) (h : Cut α L x L₁ L₂) :
    Cut (α ++ [ℓ]) L x L₁ L₂ :=
  ⟨h.1, fun y hy => not_precedes_append (.of_opOf_eq_some hx) (h.2 y hy)⟩

lemma Cut.push (hx : opOf α x = some o) {y : OpId P × ScanOp O}
    (hy : ¬ Completed (α ++ [ℓ]) y.1) (h : Cut α L x L₁ L₂) :
    Cut (α ++ [ℓ]) (L ++ [y]) x L₁ (L₂ ++ [y]) := by
  refine ⟨by rw [h.1, append_assoc], fun y' hy' => ?_⟩
  rcases mem_append.1 hy' with hy' | hy'
  · exact not_precedes_append (.of_opOf_eq_some hx) (h.2 y' hy')
  · simp only [mem_singleton] at hy'; subst hy'
    exact fun hp => hy hp.completed

lemma Cut.insert (hx : opOf α x = some o) {z : OpId P} (hz : ¬ Completed (α ++ [ℓ]) z)
    {W₁ W₂ : List (OpId P × ScanOp O)} (hW : L = W₁ ++ W₂) (h : Cut α L x L₁ L₂) :
    ∃ L₁' L₂', Cut (α ++ [ℓ]) (W₁ ++ (z, .scan) :: W₂) x L₁' L₂' ∧ linSt L₁' = linSt L₁ ∧
      (∀ y ∈ L₂', y ∈ L₂ ∨ y = (z, .scan)) ∧ (∀ y ∈ L₂, y ∈ L₂') := by
  obtain ⟨L₁', L₂', he, h2, h3, h4⟩ := split_insert (h.1.symm.trans hW) (z, ScanOp.scan)
  refine ⟨L₁', L₂', ⟨he, fun y hy => ?_⟩, ?_, h2, h3⟩
  · rcases h2 y hy with hy | rfl
    · exact not_precedes_append (.of_opOf_eq_some hx) (h.2 y hy)
    · exact fun hp => hz hp.completed
  · rcases h4 with rfl | ⟨A, B, rfl, rfl⟩
    · rfl
    · rw [linState_insert_scan]

/-! ### Dangerous updates -/

lemma numDanger_le {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)} {q : P}
    (hloc : ∀ r, r ≠ q → C'.loc r = C.loc r) (hq : dang p (C'.loc q) = true → dang p (C.loc q) = true) :
    numDanger Up C' p ≤ numDanger Up C p := by
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter] at hr ⊢
  refine ⟨hr.1, ?_⟩
  by_cases hrq : r = q
  · subst hrq; exact hq hr.2
  · rw [← hloc r hrq]; exact hr.2

lemma numDanger_lt {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)} {q : P}
    (hloc : ∀ r, r ≠ q → C'.loc r = C.loc r) (hq' : dang p (C'.loc q) = false)
    (hq : dang p (C.loc q) = true) (hqU : q ∈ Up) :
    numDanger Up C' p + 1 ≤ numDanger Up C p := by
  apply Finset.card_lt_card
  refine ⟨fun r hr => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at hr ⊢
    refine ⟨hr.1, ?_⟩
    by_cases hrq : r = q
    · subst hrq; rw [hq'] at hr; exact absurd hr.2 (by simp)
    · rw [← hloc r hrq]; exact hr.2
  · have := hsub (Finset.mem_filter.2 ⟨hqU, hq⟩)
    simp only [Finset.mem_filter, hq'] at this
    exact absurd this.2 (by simp)

lemma numDanger_le_card (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) :
    numDanger Up C p ≤ Up.card := Finset.card_filter_le _ _

/-! ### Frame lemma -/

/-- The per-process invariant of `p` survives a step of another process, given how the
linearization changed. -/
lemma pinv_frame {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)}
    {L L' : List (OpId P × ScanOp O)} (hpq : ℓ.proc ≠ p)
    (hloc : C'.loc p = C.loc p) (hpend : C'.pend p = C.pend p)
    (hmemL : ∀ x ∈ L'.map Prod.fst, x ∈ L.map Prod.fst ∨ x.1 = ℓ.proc)
    (hdone : ∀ L₁ L₂ o, L = L₁ ++ (curOp α p, o) :: L₂ →
      ∃ L₁' L₂', L' = L₁' ++ (curOp α p, o) :: L₂' ∧ linSt L₁' = linSt L₁)
    (hscan : ∀ c m b, ∀ hp : p ∈ Sc, C'.mem (.inr ⟨p, hp⟩) = false →
      C.mem (.inr ⟨p, hp⟩) = false ∧ (opOf α (curOp α p) = some .scan →
        ScanInv Up α C L p c m b → ScanInv Up (α ++ [ℓ]) C' L' p c m b))
    (h : PInvL Sc Up α C L p (C.loc p)) : PInvL Sc Up (α ++ [ℓ]) C' L' p (C'.loc p) := by
  have hcur := curOp_append_of_proc_ne α hpq
  have hnot : curOp α p ∉ L.map Prod.fst → curOp α p ∉ L'.map Prod.fst := by
    intro h1 h2
    rcases hmemL _ h2 with h3 | h3
    · exact h1 h3
    · exact hpq (by rw [← h3])
  rw [hloc]
  cases hl : C.loc p with
  | idle => simp only [PInvL, hl] at h ⊢; rw [hpend]; exact h
  | upd i o' rest =>
    simp only [PInvL, hl] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨hpend ▸ h1, h2, hcur ▸ hnot h3, hcur ▸ opOf_append_of_eq_some h4 _⟩
  | scan1 m b =>
    simp only [PInvL, hl] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨hpend ▸ h1, h2, hcur ▸ hnot h3, hcur ▸ opOf_append_of_eq_some h4 _⟩
  | scan2 c m b =>
    simp only [PInvL, hl] at h ⊢
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
    refine ⟨⟨hpend ▸ h1, h2, hcur ▸ hnot h3, hcur ▸ opOf_append_of_eq_some h4 _⟩, fun hp hR => ?_⟩
    obtain ⟨hR', himp⟩ := hscan c m b hp hR
    exact himp h4 (h5 hp hR')
  | done r =>
    simp only [PInvL, hl] at h ⊢
    obtain ⟨h1, L₁, L₂, o', hs, hr⟩ := h
    obtain ⟨L₁', L₂', hs', hst⟩ := hdone L₁ L₂ o' hs
    exact ⟨hpend ▸ h1, L₁', L₂', o', hcur ▸ hs', hst ▸ hr⟩

/-! ### `ScanInv` under steps of other processes -/

section ScanFrame

variable {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)} {c m : ℕ} {b : Fin k → Bool}

lemma scanInv_same (hx : opOf α (curOp α p) = some o) (hcur : curOp (α ++ [ℓ]) p = curOp α p)
    (hD : numDanger Up C' p ≤ numDanger Up C p) (h : ScanInv Up α C L p c m b) :
    ScanInv Up (α ++ [ℓ]) C' L p c m b := by
  obtain ⟨S₁, S₂, d, hcut, hclean, hN, hW⟩ := h
  refine ⟨S₁, S₂, d, hcur ▸ hcut.append hx, hclean, by omega, ?_⟩
  rcases hW with ⟨W₁, W₂, hc, hb⟩ | hW
  · exact Or.inl ⟨W₁, W₂, hcur ▸ hc.append hx, hb⟩
  · exact Or.inr hW

lemma scanInv_push (hx : opOf α (curOp α p) = some o) (hcur : curOp (α ++ [ℓ]) p = curOp α p)
    {y : OpId P × ScanOp O} (hys : y.2.isScan = false) (hy : ¬ Completed (α ++ [ℓ]) y.1)
    (hD : numDanger Up C' p + 1 ≤ numDanger Up C p) (h : ScanInv Up α C L p c m b) :
    ScanInv Up (α ++ [ℓ]) C' (L ++ [y]) p c m b := by
  obtain ⟨S₁, S₂, d, hcut, hclean, hN, hW⟩ := h
  refine ⟨S₁, S₂ ++ [y], d + 1, hcur ▸ hcut.push hx hy, fun hall => ?_, by omega, ?_⟩
  · have := hall y (by simp); rw [hys] at this; cases this
  · rcases hW with ⟨W₁, W₂, hc, hb⟩ | ⟨h1, -⟩
    · exact Or.inl ⟨W₁, W₂ ++ [y], hcur ▸ hc.push hx hy, hb⟩
    · exact Or.inr ⟨by omega, fun _ => by omega⟩

lemma scanInv_insert (hx : opOf α (curOp α p) = some o) (hcur : curOp (α ++ [ℓ]) p = curOp α p)
    {z : OpId P} (hz : ¬ Completed (α ++ [ℓ]) z)
    {W₁ W₂ : List (OpId P × ScanOp O)} (hWL : L = W₁ ++ W₂)
    (hD : numDanger Up C' p ≤ numDanger Up C p) (h : ScanInv Up α C L p c m b) :
    ScanInv Up (α ++ [ℓ]) C' (W₁ ++ (z, .scan) :: W₂) p c m b := by
  obtain ⟨S₁, S₂, d, hcut, hclean, hN, hW⟩ := h
  obtain ⟨S₁', S₂', hcut', hst, h2, h3⟩ := hcut.insert hx hz hWL
  refine ⟨S₁', S₂', d, hcur ▸ hcut', fun hall i hi => ?_, by omega, ?_⟩
  · rw [hst]; exact hclean (fun y hy => hall y (h3 y hy)) i hi
  · rcases hW with ⟨V₁, V₂, hc, hb⟩ | ⟨h1, h4⟩
    · obtain ⟨V₁', V₂', hc', hst', -, -⟩ := hc.insert hx hz hWL
      exact Or.inl ⟨V₁', V₂', hcur ▸ hc', hst' ▸ hb⟩
    · refine Or.inr ⟨h1, fun ⟨y, hy, hys⟩ => h4 ⟨y, ?_, hys⟩⟩
      rcases h2 y hy with hy | rfl
      · exact hy
      · simp [ScanOp.isScan] at hys

end ScanFrame

/-- Frame lemma when the linearization does not change. -/
lemma pinv_frame_same {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)}
    {L : List (OpId P × ScanOp O)} (hpq : ℓ.proc ≠ p)
    (hloc : C'.loc p = C.loc p) (hpend : C'.pend p = C.pend p)
    (hR : ∀ hp : p ∈ Sc, C'.mem (.inr ⟨p, hp⟩) = false →
      C.mem (.inr ⟨p, hp⟩) = false ∧ numDanger Up C' p ≤ numDanger Up C p)
    (h : PInvL Sc Up α C L p (C.loc p)) : PInvL Sc Up (α ++ [ℓ]) C' L p (C'.loc p) := by
  refine pinv_frame hpq hloc hpend (fun x hx => Or.inl hx)
    (fun L₁ L₂ o hs => ⟨L₁, L₂, hs, rfl⟩)
    (fun c m b hp hR' => ⟨(hR hp hR').1, fun hx hs =>
      scanInv_same hx (curOp_append_of_proc_ne _ hpq) (hR hp hR').2 hs⟩) h

/-- Frame lemma when an update `y` of the stepping process is linearized (appended). -/
lemma pinv_frame_push {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)}
    {L : List (OpId P × ScanOp O)} (hpq : ℓ.proc ≠ p)
    (hloc : C'.loc p = C.loc p) (hpend : C'.pend p = C.pend p)
    (hR : ∀ hp : p ∈ Sc, C'.mem (.inr ⟨p, hp⟩) = C.mem (.inr ⟨p, hp⟩))
    (hD : numDanger Up C' p + 1 ≤ numDanger Up C p)
    {y : OpId P × ScanOp O} (hy1 : y.1.1 = ℓ.proc) (hys : y.2.isScan = false)
    (hyc : ¬ Completed (α ++ [ℓ]) y.1)
    (h : PInvL Sc Up α C L p (C.loc p)) : PInvL Sc Up (α ++ [ℓ]) C' (L ++ [y]) p (C'.loc p) := by
  refine pinv_frame hpq hloc hpend (fun x hx => ?_)
    (fun L₁ L₂ o hs => ⟨L₁, L₂ ++ [y], by rw [hs]; simp, rfl⟩)
    (fun c m b hp hR' => ⟨(hR hp) ▸ hR', fun hx hs =>
      scanInv_push hx (curOp_append_of_proc_ne _ hpq) hys hyc hD hs⟩) h
  simp only [map_append, map_cons, map_nil, mem_append, mem_singleton] at hx
  rcases hx with hx | rfl
  · exact Or.inl hx
  · exact Or.inr hy1

/-- Frame lemma when a scan `z` of the stepping process is inserted retroactively. -/
lemma pinv_frame_insert {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)}
    {L : List (OpId P × ScanOp O)} (hpq : ℓ.proc ≠ p)
    (hloc : C'.loc p = C.loc p) (hpend : C'.pend p = C.pend p)
    (hR : ∀ hp : p ∈ Sc, C'.mem (.inr ⟨p, hp⟩) = C.mem (.inr ⟨p, hp⟩))
    (hD : numDanger Up C' p ≤ numDanger Up C p)
    {z : OpId P} (hz1 : z.1 = ℓ.proc) (hzc : ¬ Completed (α ++ [ℓ]) z)
    {W₁ W₂ : List (OpId P × ScanOp O)} (hWL : L = W₁ ++ W₂)
    (h : PInvL Sc Up α C L p (C.loc p)) :
    PInvL Sc Up (α ++ [ℓ]) C' (W₁ ++ (z, .scan) :: W₂) p (C'.loc p) := by
  refine pinv_frame hpq hloc hpend (fun x hx => ?_) (fun L₁ L₂ o hs => ?_)
    (fun c m b hp hR' => ⟨(hR hp) ▸ hR', fun hx hs =>
      scanInv_insert hx (curOp_append_of_proc_ne _ hpq) hzc hWL hD hs⟩) h
  · simp only [map_append, map_cons, mem_append, mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact Or.inl (by rw [hWL]; simp [hx])
    · exact Or.inr hz1
    · exact Or.inl (by rw [hWL]; simp [hx])
  · obtain ⟨L₁', L₂', he, h4⟩ := split_cons_insert (hs.symm.trans hWL) (z, ScanOp.scan)
    refine ⟨L₁', L₂', he, ?_⟩
    rcases h4 with rfl | ⟨A, B, rfl, rfl⟩
    · rfl
    · rw [linState_insert_scan]

end Cslib.SharedMemory.Scannable.Impl1
