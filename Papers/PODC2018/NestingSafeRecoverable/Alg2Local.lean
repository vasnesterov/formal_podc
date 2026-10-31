import Papers.PODC2018.NestingSafeRecoverable.Alg2Inv

/-!
# Algorithm 2 of [ABH18]: the invariant is preserved — steps that do not write

Steps of a process `p` that do not change the shared memory: reads of `C` (with a linearization
point for `READ` and for `CAS` failing at line 3), the tests, the failed `cas` of line 7, the
recovery loop, and the responses.
-/

namespace Podc.NestingSafeRecoverable.Alg2

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] [Fintype P]

variable {C : (alg2 P V).Cfg} {W : List (Cnt P V)} {L L' : Lin P V} {p : P}

/-- A local step of `p` that keeps `p` pending. -/
lemma Inv.move (hI : Inv C W L) {s'} (hlin : IsLinearization (N C.hist) L')
    (hlst : lst L' = lst L) (hm : ∀ q, q ≠ p → LMono L L' (curOp (N C.hist) q))
    (hp : PInv W (memC C) (memR C) L' (N C.hist) p (some s')) :
    Inv { C with st := Function.update C.st p (some s') } W L' :=
  hI.of_local (p := p) rfl (fun q hq => by simp [hq]) (fun q hq => ⟨rfl, rfl⟩) (fun _ _ h => h)
    hlin hlst hm (by simp only [Function.update_self]; exact hp)

lemma Inv.move' (hI : Inv C W L) {s'} (hp : PInv W (memC C) (memR C) L (N C.hist) p (some s')) :
    Inv { C with st := Function.update C.st p (some s') } W L :=
  hI.move hI.lin rfl (fun _ _ => LMono.refl _ _) hp

lemma Inv.mem_W (hI : Inv C W L) : memC C ∈ W := List.mem_of_getLast? hI.wlast

lemma Inv.pinv (hI : Inv C W L) {o pc v} (hs : C.st p = some (o, pc, v)) :
    opOf (N C.hist) (curOp (N C.hist) p) = some o ∧
      LocInv W (memC C) (fun k => memR C k p) L (curOp (N C.hist) p) p o pc v ∧
      ∀ old new, o = .cas old new → Succ pc v → (some p, some new) ∈ W →
        NoAfter W (some p, some new) p ∧ GSucc W (memR C) p new := by
  have h := hI.proc p; rw [hs] at h; exact h

section CAS

variable {old : Option V} {new : V}

lemma Inv.step_c2 {v} (hI : Inv C W L) (hs : C.st p = some (.cas old new, .c2, v)) :
    ∃ L', Inv (C.ev (.step p)) W L' := by
  obtain ⟨hop, hloc, -⟩ := hI.pinv hs
  simp only [LocInv] at hloc
  obtain ⟨hx, hw⟩ := hloc
  rw [ev_c2 hs]
  by_cases h2 : (memC C).2 = old
  · refine ⟨L, hI.move' ⟨hop, ?_, fun _ _ _ h => by simp [Succ] at h⟩⟩
    simp only [LocInv]
    exact ⟨memC C, rfl, hI.mem_W, noAfter_last hI.wnd hI.wlast p, hw, fun h => absurd h2 h,
      fun _ => ⟨fun _ => hx, fun h => absurd rfl h⟩⟩
  · have hl : lst L = (memC C).2 := hI.lst_eq
    have hro : (casRObj V).δ (lst L) (.cas old new) = (lst L, .inl false) := by
      rw [δ_cas, hl, ite_eq_right h2]
    refine ⟨L ++ [(curOp (N C.hist) p, .cas old new)],
      hI.move (hI.lin.push hop hx (not_completed_curOp _ _)) (lst_push_ro hro)
        (fun q hq => LMono.append _ (by simp [curOp_ne hq])) ⟨hop, ?_, fun _ _ _ h => by
          simp [Succ] at h⟩⟩
    simp only [LocInv]
    refine ⟨memC C, rfl, hI.mem_W, noAfter_last hI.wnd hI.wlast p, hw,
      fun _ => ⟨L, [], rfl, hro⟩, fun h => absurd h h2⟩

lemma Inv.step_c3_ret {c : Cnt P V} (hI : Inv C W L)
    (hs : C.st p = some (.cas old new, .c3, .inl c)) (h2 : c.2 ≠ old) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨-, hloc, -⟩ := hI.pinv hs
  simp only [LocInv, Sum.inl.injEq, exists_eq_left'] at hloc
  rw [ev_c3_ret hs h2]
  exact hI.ret (hloc.2.2.2.1 h2).at

lemma Inv.step_c3_none {val : Option V} (hI : Inv C W L)
    (hs : C.st p = some (.cas old new, .c3, .inl (none, val))) (h2 : val = old) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨hop, hloc, -⟩ := hI.pinv hs
  simp only [LocInv, Sum.inl.injEq, exists_eq_left'] at hloc
  obtain ⟨h1, h2', h3, -, h5⟩ := hloc
  rw [ev_c3_none hs h2]
  refine hI.move' ⟨hop, ?_, fun _ _ _ h => by simp [Succ] at h⟩
  simp only [LocInv, Sum.inl.injEq, exists_eq_left']
  exact ⟨h2, h1, h2', h3, fun k h => by simp at h, h5 h2⟩

lemma Inv.step_c7_fail {c : Cnt P V} (hI : Inv C W L)
    (hs : C.st p = some (.cas old new, .c7, .inl c)) (hm : memC C ≠ c) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨hop, hloc, -⟩ := hI.pinv hs
  simp only [LocInv, Sum.inl.injEq, exists_eq_left'] at hloc
  obtain ⟨-, -, -, hw, -, h7⟩ := hloc
  rw [ev_c7_fail hs hm]
  refine hI.move' ⟨hop, ?_, fun _ _ _ h => by simp [Succ] at h⟩
  simp only [LocInv]
  exact Or.inr ⟨trivial, hw, h7.2 hm⟩

lemma Inv.step_c8 {b : Bool} (hI : Inv C W L) (hs : C.st p = some (.cas old new, .c8, .inr b)) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨-, hloc, -⟩ := hI.pinv hs
  simp only [LocInv] at hloc
  rw [ev_c8 hs]
  rcases hloc with ⟨h, -, hat⟩ | ⟨h, -, hro⟩
  · cases h; exact hI.ret hat
  · cases h; exact hI.ret hro.at

lemma Inv.step_r13 {v} (hI : Inv C W L) (hs : C.st p = some (.cas old new, .r13, v)) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨hop, hloc, hdone⟩ := hI.pinv hs
  simp only [LocInv] at hloc
  rw [ev_r13 hs]
  refine hI.move' ⟨hop, ?_, fun o' n' ho _ hw => hdone o' n' ho trivial hw⟩
  simp only [LocInv]
  exact ⟨hloc, memC C, rfl, hI.mem_W, fun h _ => h⟩

lemma Inv.step_r14 {v} (hI : Inv C W L) (hs : C.st p = some (.cas old new, .r14, v)) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨hop, hloc, hdone⟩ := hI.pinv hs
  simp only [LocInv] at hloc
  obtain ⟨hR, c, rfl, hc, hne⟩ := hloc
  by_cases h : c = (some p, some new)
  · subst h
    rw [ev_r14_ret hs]
    exact hI.ret (hR.1 hc)
  · rw [ev_r14_go hs (fun h' => h (Sum.inl_injective h'))]
    refine hI.move' ⟨hop, ?_, fun o' n' ho _ hw => hdone o' n' ho trivial hw⟩
    simp only [LocInv]
    exact ⟨hR, fun hw => ⟨hne h hw, fun j hj => by simp at hj⟩⟩

lemma Inv.step_rR {i : ℕ} {v} (hI : Inv C W L) (hs : C.st p = some (.cas old new, .rR i, v)) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨hop, hloc, hdone⟩ := hI.pinv hs
  simp only [LocInv] at hloc
  obtain ⟨hR, hloop⟩ := hloc
  by_cases hi : i < (procs P).length
  · rw [ev_rR_read hs hi]
    refine hI.move' ⟨hop, ?_, fun o' n' ho _ hw => hdone o' n' ho trivial hw⟩
    simp only [LocInv]
    refine ⟨hR, hloop, hi, _, rfl, fun h => hI.reg p _ new h, fun h hw => ?_⟩
    intro W₁ c W₂ hsp hc
    exact h ((hdone old new rfl trivial hw).2 W₁ c W₂ _ hsp hc)
  · rw [ev_rR_end hs hi]
    have hw : (some p, some new) ∉ W := by
      intro hw
      obtain ⟨hne, hl⟩ := hloop hw
      obtain ⟨W₁, c, W₂, hsp⟩ := exists_succ hw (by rw [hI.wlast]; simpa using hne)
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (hI.wtail c (mem_tail_of_split hsp))
      have hkm : k ∈ (procs P).take i := by
        rw [List.take_of_length_le (by omega)]
        simp [procs]
      exact hl k hkm W₁ c W₂ hsp hk
    refine hI.move' ⟨hop, ?_, fun _ _ _ h => by simp [Succ] at h⟩
    simp only [LocInv]
    exact ⟨hR.2 hw, hw⟩

lemma Inv.step_rT {i : ℕ} {v} (hI : Inv C W L) (hs : C.st p = some (.cas old new, .rT i, v)) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨hop, hloc, hdone⟩ := hI.pinv hs
  simp only [LocInv] at hloc
  obtain ⟨hR, hloop, hi, r, rfl, h1, h2⟩ := hloc
  by_cases h : r = some new
  · subst h
    rw [ev_rT_ret hs]
    exact hI.ret (hR.1 (h1 rfl))
  · rw [ev_rT_go hs (fun h' => h (Prod.mk.inj (Sum.inl_injective h')).2)]
    refine hI.move' ⟨hop, ?_, fun o' n' ho _ hw => hdone o' n' ho trivial hw⟩
    simp only [LocInv]
    refine ⟨hR, fun hw => ⟨(hloop hw).1, fun j hj => ?_⟩⟩
    rw [List.take_add_one, List.getElem?_eq_getElem hi] at hj
    rcases List.mem_append.1 hj with hj | hj
    · exact (hloop hw).2 j hj
    · simp only [Option.toList_some, List.mem_singleton] at hj
      subst hj; exact h2 h hw

end CAS

lemma Inv.step_rd10 {v} (hI : Inv C W L) (hs : C.st p = some (.read, .rd10, v)) :
    ∃ L', Inv (C.ev (.step p)) W L' := by
  obtain ⟨hop, hloc, -⟩ := hI.pinv hs
  simp only [LocInv] at hloc
  rw [ev_rd10 hs]
  have hl : lst L = (memC C).2 := hI.lst_eq
  have hro : (casRObj V).δ (lst L) .read = (lst L, .inr (memC C).2) := by rw [δ_read, hl]
  refine ⟨L ++ [(curOp (N C.hist) p, .read)],
    hI.move (hI.lin.push hop hloc (not_completed_curOp _ _)) (lst_push_ro hro)
      (fun q hq => LMono.append _ (by simp [curOp_ne hq])) ⟨hop, ?_, fun _ _ h => by cases h⟩⟩
  simp only [LocInv]
  exact ⟨memC C, rfl, L, [], rfl, hro⟩

lemma Inv.step_rd11 {c : Cnt P V} (hI : Inv C W L) (hs : C.st p = some (.read, .rd11, .inl c)) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨-, hloc, -⟩ := hI.pinv hs
  simp only [LocInv, Sum.inl.injEq, exists_eq_left'] at hloc
  rw [ev_rd11 hs]
  exact hI.ret hloc.at

end Podc.NestingSafeRecoverable.Alg2
