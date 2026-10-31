import Papers.PODC2018.NestingSafeRecoverable.Alg2Step

/-!
# Algorithm 2 of [ABH18]: the invariant is preserved — invocations, responses, crashes

`Inv.of_local`: the frame lemma for events that do not change the shared memory; the initial
configuration; invocations (`Inv.ev_inv`); responses (`Inv.ret`); crashes (`Inv.ev_crash`).
-/

namespace Podc.NestingSafeRecoverable.Alg2

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] [Fintype P]

variable {C C' : (alg2 P V).Cfg} {W : List (Cnt P V)} {L L' : Lin P V} {p : P}

/-- The current instance of an idle process is not linearized. -/
lemma Inv.idle (hI : Inv C W L) (hwf : Alg.WFInv C) {q : P} (h : C.st q = none) :
    curOp (N C.hist) q ∉ L.map Prod.fst := by
  intro hx
  have h1 := hI.lin.mem_invoked hx
  have h2 := hwf.pend q
  simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero] at h2
  simp only [Invoked] at h1
  omega

lemma curOp_ne {α : List (Label P (casRObj V))} {q : P} (hq : q ≠ p) :
    curOp α q ≠ curOp α p := by
  simp [curOp, hq]

/-- Frame lemma: an event of `p` that changes neither the shared memory nor `W`. -/
lemma Inv.of_local (hI : Inv C W L) (hmem : C'.mem = C.mem)
    (hst : ∀ q, q ≠ p → C'.st q = C.st q)
    (hN : ∀ q, q ≠ p → opsOf (N C'.hist) q = opsOf (N C.hist) q ∧
      respsOf (N C'.hist) q = respsOf (N C.hist) q)
    (hops : ∀ x o, opOf (N C.hist) x = some o → opOf (N C'.hist) x = some o)
    (hlin : IsLinearization (N C'.hist) L') (hlst : lst L' = lst L)
    (hm : ∀ q, q ≠ p → LMono L L' (curOp (N C.hist) q))
    (hp : PInv W (memC C) (memR C) L' (N C'.hist) p (C'.st p)) : Inv C' W L' := by
  have hc : memC C' = memC C := by unfold memC; rw [hmem]
  have hr : memR C' = memR C := by funext a b; unfold memR; rw [hmem]
  refine ⟨hlin, by rw [hlst, hI.lst_eq, hc], hI.wnd, by rw [hc]; exact hI.wlast, hI.wtail,
    fun q w hw => ?_, fun q j w h => hI.reg q j w (by rw [← hr]; exact h), fun q => ?_⟩
  · obtain ⟨i, old, h⟩ := hI.wops q w hw
    exact ⟨i, old, hops _ _ h⟩
  · rw [hc, hr]
    by_cases hq : q = p
    · subst hq; exact hp
    · rw [hst q hq]
      exact (hI.proc q).mono (hN q hq).1 (hN q hq).2 (hm q hq)

/-- The initial configuration. -/
lemma inv_init : Inv (alg2 P V).init [(none, none)] [] := by
  refine ⟨isLinearization_nil, rfl, by simp, rfl, by simp, by simp, ?_, fun q => trivial⟩
  intro q j w h; simp [memR, Alg.init, alg2] at h

/-- Responses: the returning instance is linearized with the returned response. -/
lemma Inv.ret (hI : Inv C W L) {o : (casRObj V).Op} {r : (casRObj V).Resp}
    (hAt : At L (curOp (N C.hist) p) o r) :
    Inv { C with st := Function.update C.st p none, hist := C.hist ++ [.res p r] } W L := by
  obtain ⟨L₁, L₂, hs, hr⟩ := hAt
  refine hI.of_local (p := p) rfl (fun q hq => by simp [hq]) (fun q hq => ?_)
    (fun x o' h => ?_) ?_ rfl (fun q _ => LMono.refl _ _) (by simp [PInv])
  · simp only [N_append, N_res]
    exact ⟨opsOf_concat_of_ne (by simp), respsOf_concat_of_ne (by simp [Ne.symm hq])⟩
  · simp only [N_append, N_res]
    exact (opOf_append_of_invoked (Invoked.of_opOf_eq_some h)).trans h
  · simp only [N_append, N_res]
    exact hI.lin.append_ret L₁ L₂ o hs hr

lemma mem_opsOf_of_opOf {α : List (Label P (casRObj V))} {q : P} {i : ℕ} {o}
    (h : opOf α (q, i) = some o) : o ∈ opsOf α q := List.mem_of_getElem? h

/-- Invocations. -/
lemma Inv.ev_inv (hI : Inv C W L) (hwf : Alg.WFInv C) (o : (casRObj V).Op)
    (henv : Env2 (N (C.ev (.inv p o)).hist)) : Inv (C.ev (.inv p o)) W L := by
  rcases hs : C.st p with _ | x
  · rw [Alg.ev_inv_of_none C o hs] at henv ⊢
    have hlen : (opsOf (N C.hist) p).length = (respsOf (N C.hist) p).length := by
      have := hwf.pend p; simpa [hs] using this
    have hidle := hI.idle hwf hs
    refine hI.of_local (p := p) rfl (fun q hq => by simp [hq]) (fun q hq => ?_)
      (fun x o' h => ?_) (by simpa using hI.lin.append_inv p o) rfl (fun q _ => LMono.refl _ _) ?_
    · simp only [N_append, N_inv]
      exact ⟨opsOf_concat_of_ne (by simp [Ne.symm hq]), respsOf_concat_of_ne (by simp)⟩
    · simp only [N_append, N_inv]
      exact (opOf_append_of_invoked (Invoked.of_opOf_eq_some h)).trans h
    · simp only [Function.update_self, N_append, N_inv]
      have hop : opOf (N C.hist ++ [Label.inv p o]) (curOp (N C.hist) p) = some o := by
        rw [opOf_concat_inv]; simp [curOp, hlen]
      rcases o with ⟨old, new⟩ | _
      · show PInv _ _ _ _ _ _ (some (.cas old new, .c2, v0))
        simp only [PInv, LocInv, curOp_append_inv]
        refine ⟨hop, ⟨hidle, fun hw => ?_⟩, fun _ _ _ h => by simp [Succ] at h⟩
        obtain ⟨i, old', hi⟩ := hI.wops p new hw
        have hnd := (henv p).1
        simp only [N_append] at hnd
        rw [N_inv, opsOf_concat] at hnd
        simp only [Label.invOf_inv, ↓reduceIte, Option.toList_some, List.filterMap_append] at hnd
        have hm : new ∈ (opsOf (N C.hist) p).filterMap newOf :=
          List.mem_filterMap.2 ⟨_, mem_opsOf_of_opOf hi, rfl⟩
        exact (List.nodup_append.1 hnd).2.2 _ hm new (by simp [newOf]) rfl
      · show PInv _ _ _ _ _ _ (some (.read, .rd10, v0))
        simp only [PInv, LocInv, curOp_append_inv]
        exact ⟨hop, hidle, fun _ _ h => by cases h⟩
  · rw [Alg.ev_inv_of_some C o hs]; exact hI

lemma not_mem_erase {L₁ L₂ : Lin P V} {x : OpId P} {o : (casRObj V).Op}
    (hnd : ((L₁ ++ (x, o) :: L₂).map Prod.fst).Nodup) : x ∉ (L₁ ++ L₂).map Prod.fst := by
  simp only [List.map_append, List.map_cons] at hnd
  rw [List.nodup_middle, List.nodup_cons] at hnd
  rw [List.map_append]; exact hnd.1

/-- Crashes: the crashed operation is retracted if it was speculatively linearized. -/
lemma Inv.ev_crash (hI : Inv C W L) : ∃ L', Inv (C.ev (.crash p)) W L' := by
  rcases hs : C.st p with _ | ⟨o, pc, v⟩
  · rw [Alg.ev_crash_of_none C hs]; exact ⟨L, hI⟩
  · have hP := hI.proc p
    rw [hs] at hP
    obtain ⟨hop, hloc, hdone⟩ := hP
    set x := curOp (N C.hist) p with hx
    have keep : PInv W (memC C) (memR C) L (N C.hist) p
        (some (o, (alg2 P V).recover p o pc)) →
        ∃ L', Inv (C.ev (.crash p)) W L' := fun h => by
      rw [Alg.ev_crash_of_some C hs]
      exact ⟨L, hI.of_local (p := p) rfl (fun q hq => by simp [hq]) (fun q hq => by simp)
        (fun x o h => by simpa using h) (by simpa using hI.lin) rfl
        (fun _ _ => LMono.refl _ _)
        (by simp only [Function.update_self, N_append, N_crash_rec, List.append_nil]; exact h)⟩
    have erase : ∀ r, ROAt L x o r → (∀ L' : Lin P V, x ∉ L'.map Prod.fst →
        PInv W (memC C) (memR C) L' (N C.hist) p (some (o, (alg2 P V).recover p o pc))) →
        ∃ L', Inv (C.ev (.crash p)) W L' := by
      intro r ⟨L₁, L₂, hL, hro⟩ h
      rw [Alg.ev_crash_of_some C hs]
      have hnd := hI.lin.nodup
      rw [hL] at hnd
      have hlin := hI.lin
      rw [hL] at hlin
      refine ⟨L₁ ++ L₂, hI.of_local (p := p) rfl (fun q hq => by simp [hq]) (fun q hq => by simp)
        (fun x o h => by simpa using h)
        (by simpa using hlin.erase_ro (not_completed_curOp _ _) (congrArg Prod.fst hro))
        (by rw [hL]; exact (lst_erase' L₁ L₂ hro).symm)
        (fun q hq => hL ▸ LMono.erase hro (curOp_ne hq))
        (by simp only [Function.update_self, N_append, N_crash_rec, List.append_nil]
            exact h _ (not_mem_erase hnd))⟩
    rcases o with ⟨old, new⟩ | _
    · have tgt : ∀ L' : Lin P V, Rec W L' x p old new →
          PInv W (memC C) (memR C) L' (N C.hist) p (some (.cas old new, (alg2 P V).recover p (.cas old new) pc)) := by
        intro L' hR
        show PInv _ _ _ _ _ _ (some (.cas old new, .r13, v0))
        refine ⟨hop, hR, fun old' new' ho _ hw => ?_⟩
        cases ho
        rcases pc with _ | _ | _ | _ | _ | _ | i | i | _ | _ <;> simp only [LocInv] at hloc
        · exact absurd hw hloc.2
        · obtain ⟨c, -, -, -, h, -⟩ := hloc; exact absurd hw h
        · obtain ⟨c, -, -, -, -, h, -⟩ := hloc; exact absurd hw h
        · rcases hloc with ⟨rfl, -, -⟩ | ⟨-, h, -⟩
          · exact hdone old new rfl rfl hw
          · exact absurd hw h
        all_goals first | exact hloc.elim | exact hdone old new rfl trivial hw
      have notin : ∀ L' : Lin P V, (some p, some new) ∉ W → x ∉ L'.map Prod.fst →
          Rec W L' x p old new := fun L' hw hx => ⟨fun h => absurd h hw, fun _ => hx⟩
      rcases pc with _ | _ | _ | _ | _ | _ | i | i | _ | _ <;> simp only [LocInv] at hloc
      · exact keep (tgt L (notin L hloc.2 hloc.1))
      · obtain ⟨c, rfl, -, -, hw, hne, heq⟩ := hloc
        by_cases h2 : c.2 = old
        · by_cases hm : memC C = c
          · exact keep (tgt L (notin L hw ((heq h2).1 hm)))
          · exact erase _ ((heq h2).2 hm) fun L' hx => tgt L' (notin L' hw hx)
        · exact erase _ (hne h2) fun L' hx => tgt L' (notin L' hw hx)
      · obtain ⟨c, rfl, -, -, -, hw, -, heq⟩ := hloc
        by_cases hm : memC C = c
        · exact keep (tgt L (notin L hw (heq.1 hm)))
        · exact erase _ (heq.2 hm) fun L' hx => tgt L' (notin L' hw hx)
      · rcases hloc with ⟨-, hw, hat⟩ | ⟨-, hw, hro⟩
        · exact keep (tgt L ⟨fun _ => hat, fun h => absurd hw h⟩)
        · exact erase _ hro fun L' hx => tgt L' (notin L' hw hx)
      · exact keep (tgt L hloc)
      · exact keep (tgt L hloc.1)
      · exact keep (tgt L hloc.1)
      · exact keep (tgt L hloc.1)
    · rcases pc with _ | _ | _ | _ | _ | _ | i | i | _ | _ <;> simp only [LocInv] at hloc
      · exact keep ⟨hop, hloc, fun _ _ h => by cases h⟩
      · obtain ⟨c, -, hro⟩ := hloc
        exact erase _ hro fun L' hx => ⟨hop, hx, fun _ _ h => by cases h⟩

end Podc.NestingSafeRecoverable.Alg2
