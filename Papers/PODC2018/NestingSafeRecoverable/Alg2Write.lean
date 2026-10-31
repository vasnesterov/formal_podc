import Papers.PODC2018.NestingSafeRecoverable.Alg2Local

/-!
# Algorithm 2 of [ABH18]: the invariant is preserved — writes

* `Inv.step_c3_write`: the helping write `R[id][p] ← val` of line 6. The key point: the process
  `p` that overwrote `<q, new>` (a successful but pending `CAS` of `q`) never overwrites
  `R[q][p] = new` afterwards, because every content of `q` read by `p` after its own write is
  `<q, new>` itself (`eq_of_noAfter`).
* `Inv.step_c7_succ`: a successful `cas` of line 7. The `CAS` of `p` is linearized, followed by
  the (speculative, failed) linearization of every pending `CAS` that read the overwritten
  content with `val = old` and has not applied its `cas` yet (`tgts`).
-/

namespace Podc.NestingSafeRecoverable.Alg2

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] [Fintype P]

variable {C : (alg2 P V).Cfg} {W : List (Cnt P V)} {L : Lin P V} {p : P}

/-! ### Line 6 -/

lemma Inv.step_c3_write {old : Option V} {new : V} {k : P} {val : Option V} (hI : Inv C W L)
    (hs : C.st p = some (.cas old new, .c3, .inl (some k, val))) (h2 : val = old) :
    Inv (C.ev (.step p)) W L := by
  obtain ⟨hop, hloc, -⟩ := hI.pinv hs
  simp only [LocInv, Sum.inl.injEq, exists_eq_left'] at hloc
  obtain ⟨hcW, hna, hw, -, h7⟩ := hloc
  obtain ⟨hc, hr, hst, hh⟩ := ev_c3_write_spec hs h2
  generalize C.ev (.step p) = C' at hc hr hst hh ⊢
  have hN : N C'.hist = N C.hist := by rw [hh]
  refine ⟨by rw [hN]; exact hI.lin, by rw [hc]; exact hI.lst_eq, hI.wnd,
    by rw [hc]; exact hI.wlast, hI.wtail, by rw [hN]; exact hI.wops, fun a b w h => ?_,
    fun q => ?_⟩
  · rw [hr] at h
    split_ifs at h with hab
    · obtain ⟨rfl, rfl⟩ := hab; subst h; exact hcW
    · exact hI.reg a b w h
  · rw [hc, hN]
    by_cases hq : q = p
    · subst hq
      rw [hst, Function.update_self]
      refine ⟨hop, ?_, fun _ _ _ h => by simp [Succ] at h⟩
      simp only [LocInv, Sum.inl.injEq, exists_eq_left']
      refine ⟨h2, hcW, hna, hw, fun k' hk => ?_, h7 h2⟩
      cases hk; rw [hr]; simp
    · rw [hst, Function.update_of_ne hq]
      have hP := hI.proc q
      rcases hsq : C.st q with _ | ⟨o, pc, v⟩
      · trivial
      · rw [hsq] at hP
        obtain ⟨hop', hloc', hdone'⟩ := hP
        have hcol : (fun j => memR C' j q) = (fun j => memR C j q) := by
          funext j; rw [hr]; simp [hq]
        refine ⟨hop', by rw [hcol]; exact hloc', fun o' n' ho hS hw' => ?_⟩
        obtain ⟨hNA, hG⟩ := hdone' o' n' ho hS hw'
        refine ⟨hNA, fun W₁ c W₂ j hsp hc' => ?_⟩
        rw [hr]
        split_ifs with hkj
        · obtain ⟨rfl, rfl⟩ := hkj
          have := eq_of_noAfter hsp hc' hcW rfl hna hNA
          simp only [Prod.mk.injEq] at this
          exact this.2
        · exact hG W₁ c W₂ j hsp hc'

/-! ### Line 7: the targets of speculation -/

open Classical in
/-- A pending `CAS` of `q ≠ p` that read the current content of `C` with `val = old` and has
not applied its `cas`. -/
noncomputable def tgt (C : (alg2 P V).Cfg) (p q : P) : Option (OpId P × (casRObj V).Op) :=
  if q = p then none else
    match C.st q with
    | some (.cas old' new', pc, .inl c) =>
      if (pc = .c3 ∨ pc = .c7) ∧ c = memC C ∧ c.2 = old' then
        some (curOp (N C.hist) q, .cas old' new')
      else none
    | _ => none

/-- All targets of speculation. -/
noncomputable def tgts (C : (alg2 P V).Cfg) (p : P) : Lin P V := (procs P).filterMap (tgt C p)

lemma tgt_eq_some {q : P} {y : OpId P × (casRObj V).Op} (h : tgt C p q = some y) :
    q ≠ p ∧ ∃ old' new' pc c, C.st q = some (.cas old' new', pc, .inl c) ∧
      (pc = .c3 ∨ pc = .c7) ∧ c = memC C ∧ c.2 = old' ∧
      y = (curOp (N C.hist) q, .cas old' new') := by
  unfold tgt at h
  split_ifs at h with hq
  refine ⟨hq, ?_⟩
  rcases hst : C.st q with _ | ⟨o, pc, v⟩
  · rw [hst] at h; simp at h
  · rw [hst] at h
    rcases o with ⟨old', new'⟩ | _
    · rcases v with c | b
      · simp only at h
        split_ifs at h with hc
        · cases h; exact ⟨old', new', pc, c, rfl, hc.1, hc.2.1, hc.2.2, rfl⟩
      · simp at h
    · simp at h

lemma mem_tgts {y : OpId P × (casRObj V).Op} (h : y ∈ tgts C p) :
    ∃ q, q ≠ p ∧ ∃ old' new' pc c, C.st q = some (.cas old' new', pc, .inl c) ∧
      (pc = .c3 ∨ pc = .c7) ∧ c = memC C ∧ c.2 = old' ∧
      y = (curOp (N C.hist) q, .cas old' new') := by
  obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 h
  exact ⟨q, tgt_eq_some hq⟩

lemma tgt_mem {q : P} (hq : q ≠ p) {old' : Option V} {new' : V} {pc : Loc} {c : Cnt P V}
    (hst : C.st q = some (.cas old' new', pc, .inl c)) (hpc : pc = .c3 ∨ pc = .c7)
    (hc : c = memC C) (h2 : c.2 = old') :
    (curOp (N C.hist) q, (CasROp.cas old' new' : (casRObj V).Op)) ∈ tgts C p := by
  refine List.mem_filterMap.2 ⟨q, by simp [procs], ?_⟩
  unfold tgt
  rw [ite_eq_right hq, hst]
  simp only
  rw [ite_eq_left ⟨hpc, hc, h2⟩]

lemma tgts_nodup : ((tgts C p).map Prod.fst).Nodup := by
  unfold tgts
  rw [List.map_filterMap]
  refine List.Nodup.filterMap ?_ (Finset.nodup_toList _)
  intro a a' b ha ha'
  simp only [Option.mem_def, Option.map_eq_some_iff] at ha ha'
  obtain ⟨y, hy, hyb⟩ := ha
  obtain ⟨y', hy', hyb'⟩ := ha'
  obtain ⟨-, o1, n1, pc1, c1, -, -, -, -, h1⟩ := tgt_eq_some hy
  obtain ⟨-, o2, n2, pc2, c2, -, -, -, -, h2⟩ := tgt_eq_some hy'
  subst h1 h2
  have := hyb.trans hyb'.symm
  simp only [curOp, Prod.mk.injEq] at this
  exact this.1

end Podc.NestingSafeRecoverable.Alg2
