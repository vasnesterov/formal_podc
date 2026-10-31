import Papers.PODC2018.NestingSafeRecoverable.Alg2Write

/-!
# Algorithm 2 of [ABH18]: the invariant is preserved — a successful `cas`

`Inv.step_c7_succ`: the successful `cas` of line 7 by `p` appends `<p, new>` to `W`; the `CAS`
of `p` is linearized (successfully), followed by every target of speculation (`tgts`), which
is linearized as a failed `CAS` (the state is now `new ≠ old`). `LocInv.succ_frame` is the
frame lemma for the other processes.
-/

namespace Podc.NestingSafeRecoverable.Alg2

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] [Fintype P]

lemma lst_append (L M : Lin P V) :
    lst (L ++ M) = (casRObj V).runOps (lst L) (M.map Prod.snd) := by
  unfold lst; rw [linState_append]

/-- Frame lemma for the other processes at a successful `cas` that writes the new content `n`
and extends the linearization by `K`. -/
lemma LocInv.succ_frame {W : List (Cnt P V)} {mc : Cnt P V} {Rc : P → Option V} {L K : Lin P V}
    {x : OpId P} {q : P} {o : (casRObj V).Op} {pc : Loc} {v : Vars P V} {n : Cnt P V}
    (h : LocInv W mc Rc L x q o pc v) (hnW : n ∉ W) (hnq : n.1 ≠ some q)
    (hl : W.getLast? = some mc)
    (hK : x ∈ K.map Prod.fst → ∃ old' new' c, o = .cas old' new' ∧ (pc = .c3 ∨ pc = .c7) ∧
      v = .inl c ∧ c = mc ∧ c.2 = old')
    (htgt : ∀ old' new' c, o = .cas old' new' → (pc = .c3 ∨ pc = .c7) → v = .inl c → c = mc →
      c.2 = old' → ROAt (L ++ K) x o (.inl false)) :
    LocInv (W ++ [n]) n Rc (L ++ K) x q o pc v := by
  have hne : ∀ new' : V, n ≠ (some q, some new') := fun new' h => hnq (by rw [h])
  have hmW : ∀ new' : V, (some q, some new') ∈ W ++ [n] → (some q, some new') ∈ W := by
    intro new' h
    rcases List.mem_append.1 h with h | h
    · exact h
    · simp only [List.mem_singleton] at h; exact absurd h.symm (hne new')
  have hnmW : ∀ new' : V, (some q, some new') ∉ W → (some q, some new') ∉ W ++ [n] :=
    fun new' h h' => h (hmW new' h')
  have notin : ¬ (pc = .c3 ∨ pc = .c7) → x ∉ L.map Prod.fst → x ∉ (L ++ K).map Prod.fst := by
    intro hpc hx hx'
    rw [List.map_append, List.mem_append] at hx'
    rcases hx' with hx' | hx'
    · exact hx hx'
    · obtain ⟨-, -, -, -, h, -⟩ := hK hx'; exact hpc h
  have hRec : ∀ old' new', ¬ (pc = .c3 ∨ pc = .c7) → Rec W L x q old' new' →
      Rec (W ++ [n]) (L ++ K) x q old' new' := fun old' new' hpc hR =>
    ⟨fun hw => (hR.1 (hmW _ hw)).append K, fun hw => notin hpc (hR.2 fun h => hw
      (List.mem_append_left _ h))⟩
  have hlast : ∀ new' : V, mc ≠ (some q, some new') →
      W.getLast? ≠ some (some q, some new') := by
    intro new' h h'; rw [hl] at h'; exact h (Option.some_inj.1 h')
  rcases o with ⟨old', new'⟩ | _ <;> rcases pc with _ | _ | _ | _ | _ | _ | i | i | _ | _ <;>
    simp only [LocInv] at h ⊢
  · exact ⟨notin (by simp) h.1, hnmW _ h.2⟩
  · obtain ⟨c, rfl, hcW, hna, hw, hne', hsp⟩ := h
    refine ⟨c, rfl, List.mem_append_left _ hcW, hna.concat hcW hnW hnq, hnmW _ hw,
      fun h2 => (hne' h2).append K, fun h2 => ⟨fun hnc => absurd (by rw [hnc]; exact hcW) hnW,
      fun _ => ?_⟩⟩
    by_cases hmc : mc = c
    · exact htgt old' new' c rfl (Or.inl rfl) rfl hmc.symm h2
    · exact ((hsp h2).2 hmc).append K
  · obtain ⟨c, rfl, h2, hcW, hna, hw, hR, hsp⟩ := h
    refine ⟨c, rfl, h2, List.mem_append_left _ hcW, hna.concat hcW hnW hnq, hnmW _ hw, hR,
      fun hnc => absurd (by rw [hnc]; exact hcW) hnW, fun _ => ?_⟩
    by_cases hmc : mc = c
    · exact htgt old' new' c rfl (Or.inr rfl) rfl hmc.symm h2
    · exact (hsp.2 hmc).append K
  · rcases h with ⟨rfl, hw, hat⟩ | ⟨rfl, hw, hro⟩
    · exact Or.inl ⟨rfl, List.mem_append_left _ hw, hat.append K⟩
    · exact Or.inr ⟨rfl, hnmW _ hw, hro.append K⟩
  · exact hRec old' new' (by simp) h
  · obtain ⟨hR, c, rfl, hcW, -⟩ := h
    exact ⟨hRec old' new' (by simp) hR, c, rfl, List.mem_append_left _ hcW,
      fun _ _ => hne new'⟩
  · obtain ⟨hR, hL⟩ := h
    refine ⟨hRec old' new' (by simp) hR, fun hw => ⟨hne new', fun j hj => ?_⟩⟩
    obtain ⟨h1, h2⟩ := hL (hmW _ hw)
    exact (h2 j hj).concat (hlast new' h1)
  · obtain ⟨hR, hL, hi, r, rfl, h1, h2⟩ := h
    refine ⟨hRec old' new' (by simp) hR, fun hw => ⟨hne new', fun j hj => ?_⟩, hi, r, rfl,
      fun h => List.mem_append_left _ (h1 h), fun hr hw => ?_⟩
    · obtain ⟨h1, h2⟩ := hL (hmW _ hw)
      exact (h2 j hj).concat (hlast new' h1)
    · exact (h2 hr (hmW _ hw)).concat (hlast new' (hL (hmW _ hw)).1)
  · exact notin (by simp) h
  · obtain ⟨c, rfl, hro⟩ := h
    exact ⟨c, rfl, hro.append K⟩

variable {C : (alg2 P V).Cfg} {W : List (Cnt P V)} {L : Lin P V} {p : P}

/-- A target of speculation is not linearized yet. -/
lemma Inv.tgt_notin (hI : Inv C W L) {q : P} {old' : Option V} {new' : V} {pc : Loc}
    {c : Cnt P V} (hst : C.st q = some (.cas old' new', pc, .inl c)) (hpc : pc = .c3 ∨ pc = .c7)
    (hc : c = memC C) (h2 : c.2 = old') : curOp (N C.hist) q ∉ L.map Prod.fst := by
  have h := (hI.pinv hst).2.1
  rcases hpc with rfl | rfl <;> simp only [LocInv, Sum.inl.injEq, exists_eq_left'] at h
  · exact ((h.2.2.2.2 h2).1 hc.symm)
  · exact h.2.2.2.2.2.1 hc.symm

/-- Line 7, successful `cas`. -/
lemma Inv.step_c7_succ {old : Option V} {new : V} {c : Cnt P V} (hI : Inv C W L)
    (henv : Env2 (N C.hist)) (hs : C.st p = some (.cas old new, .c7, .inl c)) (hm : memC C = c) :
    ∃ W' L', Inv (C.ev (.step p)) W' L' := by
  obtain ⟨hop, hloc, -⟩ := hI.pinv hs
  simp only [LocInv, Sum.inl.injEq, exists_eq_left'] at hloc
  obtain ⟨h2, hcW, -, hw, hR, h7⟩ := hloc
  have hold : old ≠ some new := (henv p).2 old new (mem_opsOf_of_opOf hop)
  have hl : lst L = old := by rw [hI.lst_eq, hm, h2]
  have hx : curOp (N C.hist) p ∉ L.map Prod.fst := h7.1 hm
  -- the targets of speculation
  have hM : ∀ y ∈ tgts C p, ∃ q, q ≠ p ∧ ∃ new', y = (curOp (N C.hist) q, .cas old new') ∧
      opOf (N C.hist) (curOp (N C.hist) q) = some (.cas old new') ∧
      curOp (N C.hist) q ∉ L.map Prod.fst := by
    intro y hy
    obtain ⟨q, hq, old', new', pc, c', hst, hpc, hc', h2', rfl⟩ := mem_tgts hy
    have : old' = old := by rw [← h2', hc', hm, h2]
    subst this
    exact ⟨q, hq, new', rfl, (hI.pinv hst).1, hI.tgt_notin hst hpc hc' h2'⟩
  have hconst : ∀ y ∈ tgts C p, (casRObj V).δ (some new) y.2 = (some new, .inl false) := by
    intro y hy
    obtain ⟨q, -, new', rfl, -, -⟩ := hM y hy
    simp [Ne.symm hold]
  have hl0 : lst (L ++ [(curOp (N C.hist) p, (CasROp.cas old new : (casRObj V).Op))]) =
      some new := by
    rw [lst_append, hl, List.map_cons, List.map_nil, ObjSpec.runOps_cons, ObjSpec.runOps_nil]
    simp
  have hlinM : IsLinearization (N C.hist)
      (L ++ [(curOp (N C.hist) p, (CasROp.cas old new : (casRObj V).Op))] ++ tgts C p) := by
    refine (hI.lin.push hop hx (not_completed_curOp _ _)).push_list _ (fun y hy => ?_)
      tgts_nodup (fun y hy => ?_)
    · obtain ⟨q, -, new', rfl, hop', -⟩ := hM y hy
      exact ⟨hop', not_completed_curOp _ _⟩
    · obtain ⟨q, hq, new', rfl, -, hxq⟩ := hM y hy
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton, not_or]
      exact ⟨hxq, by simp [hq]⟩
  set K : Lin P V := (curOp (N C.hist) p, CasROp.cas old new) :: tgts C p with hK
  have hLK : L ++ [(curOp (N C.hist) p, (CasROp.cas old new : (casRObj V).Op))] ++ tgts C p =
      L ++ K := by simp [hK]
  rw [hLK] at hlinM
  have hlK : lst (L ++ K) = some new := by
    rw [← hLK, lst_append, hl0]
    exact ObjSpec.runOps_map_snd_const _ hconst
  -- targets get a failed response
  have hro : ∀ q, q ≠ p → ∀ old' new' pc c', C.st q = some (.cas old' new', pc, .inl c') →
      (pc = .c3 ∨ pc = .c7) → c' = memC C → c'.2 = old' →
      ROAt (L ++ K) (curOp (N C.hist) q) (.cas old' new') (.inl false) := by
    intro q hq old' new' pc c' hst hpc hc' h2'
    obtain ⟨M₁, M₂, hM12⟩ := List.append_of_mem (tgt_mem hq hst hpc hc' h2')
    refine ⟨L ++ (curOp (N C.hist) p, CasROp.cas old new) :: M₁, M₂, by simp [hK, hM12], ?_⟩
    have hold' : old' = old := by rw [← h2', hc', hm, h2]
    have hs1 : lst (L ++ (curOp (N C.hist) p, (CasROp.cas old new : (casRObj V).Op)) :: M₁) =
        some new := by
      rw [show L ++ (curOp (N C.hist) p, (CasROp.cas old new : (casRObj V).Op)) :: M₁ =
        (L ++ [(curOp (N C.hist) p, CasROp.cas old new)]) ++ M₁ by simp, lst_append, hl0]
      exact ObjSpec.runOps_map_snd_const _ fun y hy => hconst y (by rw [hM12]; simp [hy])
    rw [hs1, hold']
    simp [Ne.symm hold]
  obtain ⟨hc', hr', hst', hh'⟩ := ev_c7_succ_spec hs hm
  generalize C.ev (.step p) = C' at hc' hr' hst' hh' ⊢
  have hN : N C'.hist = N C.hist := by rw [hh']
  have hnW : ((some p, some new) : Cnt P V) ∉ W := hw
  have hwnd : (W ++ [((some p, some new) : Cnt P V)]).Nodup := by
    rw [List.nodup_append]
    exact ⟨hI.wnd, List.nodup_singleton _, fun a ha b hb hab => by
      simp only [List.mem_singleton] at hb; subst hb hab; exact hnW ha⟩
  have hwl : (W ++ [((some p, some new) : Cnt P V)]).getLast? = some (some p, some new) := by
    simp
  have hWne : W ≠ [] := fun h => by simp [h] at hcW
  refine ⟨W ++ [(some p, some new)], L ++ K, ⟨by rw [hN]; exact hlinM, by rw [hlK, hc'], hwnd,
    by rw [hc']; exact hwl, fun c₀ hc₀ => ?_, fun q w hqw => ?_, fun q j w hj => ?_, fun q => ?_⟩⟩
  · rw [List.tail_append_of_ne_nil hWne] at hc₀
    rcases List.mem_append.1 hc₀ with h | h
    · exact hI.wtail c₀ h
    · simp only [List.mem_singleton] at h; subst h; rfl
  · rw [hN]
    rcases List.mem_append.1 hqw with h | h
    · exact hI.wops q w h
    · simp only [List.mem_singleton, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, old, hop⟩
  · rw [hr'] at hj; exact List.mem_append_left _ (hI.reg q j w hj)
  · rw [hc', hr', hN]
    by_cases hq : q = p
    · subst q
      rw [hst', Function.update_self]
      refine ⟨hop, ?_, fun o' n' ho _ _ => ?_⟩
      · simp only [LocInv]
        refine Or.inl ⟨trivial, by simp, L, tgts C p, by simp [hK], ?_⟩
        simp [hl]
      · cases ho
        refine ⟨noAfter_last hwnd hwl p, fun W₁ c₁ W₂ k hsp _ => ?_⟩
        rcases succ_concat hsp with ⟨W₂', hsp'⟩ | ⟨hsp', -, -⟩
        · exact absurd (by rw [hsp']; simp) hnW
        · exact absurd (by rw [hsp']; simp) hnW
    · rw [hst', Function.update_of_ne hq]
      have hP := hI.proc q
      rcases hsq : C.st q with _ | ⟨o', pc', v'⟩
      · trivial
      · rw [hsq] at hP
        obtain ⟨hop', hloc', hdone'⟩ := hP
        refine ⟨hop', hloc'.succ_frame hnW (by simp [Ne.symm hq]) hI.wlast ?_ ?_, ?_⟩
        · intro hxK
          simp only [hK, List.map_cons, List.mem_cons] at hxK
          rcases hxK with hxK | hxK
          · exact absurd hxK (curOp_ne hq)
          · obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hxK
            obtain ⟨q', hq', old'', new'', pc'', c'', hst'', hpc'', hc'', h2'', rfl⟩ :=
              mem_tgts hy
            have : q' = q := by simp only [curOp, Prod.mk.injEq] at hyx; exact hyx.1
            subst this
            rw [hsq] at hst''
            simp only [Option.some.injEq, Prod.mk.injEq] at hst''
            obtain ⟨rfl, rfl, rfl⟩ := hst''
            exact ⟨old'', new'', c'', rfl, hpc'', rfl, hc'', h2''⟩
        · intro old'' new'' c'' ho hpc hv hc'' h2''
          subst ho hv
          exact hro q hq old'' new'' pc' c'' hsq hpc hc'' h2''
        · intro o'' n'' ho hS hw'
          have hw'' : (some q, some n'') ∈ W := by
            rcases List.mem_append.1 hw' with h | h
            · exact h
            · simp only [List.mem_singleton, Prod.mk.injEq, Option.some.injEq] at h
              exact absurd h.1 hq
          obtain ⟨hNA, hG⟩ := hdone' o'' n'' ho hS hw''
          refine ⟨hNA.concat hw'' hnW (by simp [Ne.symm hq]), hG.concat fun hlast k hk => ?_⟩
          simp only [Option.some.injEq] at hk
          subst hk
          rw [hI.wlast, Option.some_inj] at hlast
          have hcq : c = (some q, some n'') := by rw [← hm, hlast]
          rw [hR q (by rw [hcq]), hcq]

end Podc.NestingSafeRecoverable.Alg2
