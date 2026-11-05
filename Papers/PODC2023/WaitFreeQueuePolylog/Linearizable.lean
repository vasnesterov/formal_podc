import Papers.PODC2023.WaitFreeQueuePolylog.StepProc

/-!
# Theorem 18: the (repaired) queue is linearizable

`Inv` holds in every reachable configuration (with a suitable ghost state, `exists_inv`); its
component `Inv.lin` says that the linearization ordering `L` of (3.2) — the operations of the
root blocks, each block's enqueues before its dequeues — is a linearization of the execution
(Lemmas 15 and 17).
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

/-- The implementation of the repaired algorithm. -/
abbrev Q (H np : ℕ) (V : Type) :
    Impl (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V) :=
  queueImpl H Variant.fixed np

lemma cnt_initMem (n : ℕ) : cnt (initMem : Mem V) n = 0 := by
  simp [cnt, initMem]

lemma shape_init (_hnp : np ≤ 2 ^ H) : Shape H np (initMem : Mem V) := by
  refine ⟨fun n => by simp [initMem], fun n => by simp [initMem], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro n i; rw [cnt_initMem]; simp [initMem]
  · intro n i hi; simp [cnt_initMem] at hi
  · intro n i hi
    simp only [cnt_initMem, Nat.le_zero] at hi; subst hi
    simp [initMem, Mem.bk, Blk.zero]
  · intro n _ i hi
    simp only [cnt_initMem, Nat.le_zero] at hi; subst hi
    simp [initMem, Mem.bk, Blk.zero]
  · intro n _ i h1 hi; simp [cnt_initMem] at hi; omega
  · intro n i h1 hi; simp [cnt_initMem] at hi; omega
  · intro i h1 hi; simp [cnt_initMem] at hi; omega
  · intro n _; exact cnt_initMem n
  · intro n _ i; simp only [initMem, Mem.bk]; split_ifs <;> simp [Blk.zero]

lemma rootLin_init : rootLin H np (initMem : Mem V) = [] := by
  simp [rootLin, rootBatches, cnt_initMem, batchLin]

lemma initCfg_mem : (Q H np V).initCfg.mem () = initMem := rfl

theorem inv_init (hnp : np ≤ 2 ^ H) : Inv H np [] (Q H np V).initCfg (Ghost.init np) := by
  refine ⟨shape_init hnp, ?_, ?_, ?_, ?_⟩
  · rw [initCfg_mem]
    refine ⟨fun _ _ _ => rfl, ?_, fun _ _ s hs => by simp [initMem] at hs,
      fun _ _ _ _ _ hs => by simp [initMem] at hs⟩
    intro n _ i h1 hi; simp [initMem] at hi; omega
  · rw [initCfg_mem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n _ _ j h1 h2; rw [cnt_initMem] at h2; omega
    · intro n _ _ j h1 h2; rw [cnt_initMem] at h2; omega
    · intro n _ _ j j' _ _ _; simp [Ghost.init]
    · intro n _ _ j _; simp [Ghost.init]
    · intro n _ b h1 h2; rw [cnt_initMem] at h2; omega
    · intro n _ _ b h1 h2; rw [cnt_initMem] at h2; omega
  · rw [initCfg_mem, rootLin_init]; exact isLinearization_nil
  · intro p
    refine ⟨fun j h1 h2 => by rw [initCfg_mem, cnt_initMem] at h2; omega, ?_⟩
    simp only [Impl.initCfg, queueImpl]
    refine ⟨trivial, rfl, ?_, ?_⟩
    · rw [cnt_initMem]; rfl
    · rw [cnt_initMem]; rfl

lemma mem_rootLin_pre {M : Mem V} {y : OpId (Fin np) × FifoOp V} (hy : y ∈ rootLin H np M) :
    y ∈ pre H np M 1 (cnt M 1) := by
  simp only [rootLin, batchLin, rootBatches, List.flatMap_map, List.mem_flatMap,
    List.mem_append, List.mem_map] at hy
  obtain ⟨b, hb, h⟩ := hy
  refine (mem_pre_iff M 1 _ y).2 ⟨b, ?_, ?_, ?_⟩
  · simp [List.mem_range'] at hb; omega
  · simp [List.mem_range'] at hb; omega
  · simp only [rootBatch] at h
    rcases h with ⟨e, he, rfl⟩ | ⟨k, hk, rfl⟩
    · simp only [enqs, List.mem_filterMap] at he
      obtain ⟨z, hz, hz'⟩ := he
      obtain ⟨x, o⟩ := z
      cases o <;> simp at hz'
      subst hz'; exact hz
    · simp only [deqs, List.mem_filterMap] at hk
      obtain ⟨z, hz, hz'⟩ := hk
      obtain ⟨x, o⟩ := z
      cases o <;> simp at hz'
      subst hz'; exact hz

lemma CtxInv.pend {os : List (FifoOp V)} {rs : List (Option V)} {M : Mem V} {G : Ghost np}
    {p : Fin np} {pend : Option (FifoOp V)} {l : Loc V} {c : Ctx} {w hw : ℕ}
    (h : CtxInv H os rs M G p pend l c w hw) : pend = some l.cur := by
  cases c with
  | app => exact h.2.1.1
  | ref => exact h.2.1.1.1
  | own => exact h.2.1.1.1

lemma PInv.idle_of_none {os : List (FifoOp V)} {rs : List (Option V)} {M : Mem V}
    {G : Ghost np} {p : Fin np} {l : Loc V} (h : PInv H os rs M G p none l) : l.pc = .idle := by
  obtain ⟨-, hpc⟩ := h
  obtain ⟨pc, cur, lh⟩ := l
  cases pc with
  | idle => rfl
  | app0 => exact absurd hpc.1 (by simp)
  | app1 => exact absurd hpc.1.1 (by simp)
  | app2 => exact absurd hpc.1.1 (by simp)
  | app3 => exact hpc.elim
  | adv0 => exact absurd hpc.2.2.pend (by simp)
  | adv1 => exact absurd hpc.2.2.2.2.pend (by simp)
  | adv2 => exact absurd hpc.2.2.pend (by simp)
  | r25 => exact absurd hpc.2.1.1 (by simp)
  | r27 => exact absurd hpc.2.1.1.1 (by simp)
  | r28 => exact absurd hpc.2.1.1.1 (by simp)
  | c43 => exact absurd hpc.2.1.1.1 (by simp)
  | c44 => exact absurd hpc.2.1.1.1 (by simp)
  | r35 => exact absurd hpc.2.1.1.1 (by simp)
  | idx => exact absurd hpc.1.1.1 (by simp)
  | fr => exact absurd hpc.1.1.1 (by simp)
  | ge => exact absurd hpc.1.1.1 (by simp)
  | done => exact absurd hpc.1.1.1 (by simp)

lemma act_ret_cases {var : Variant} {p : ℕ} {l l' : Loc V} {r : Option V}
    (h : act H var p l = .ret r l') :
    l.pc = .idle ∨ (l.pc = .done r ∧ l' = ⟨.idle, l.cur, l.lh⟩) := by
  obtain ⟨pc, cur, lh⟩ := l
  cases pc <;> simp [act] at h
  · exact Or.inl rfl
  · split_ifs at h
  · obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨rfl, rfl⟩

/-- The inductive step. -/
theorem inv_step (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) {α : List (Label (Fin np) (queueObj V))}
    {C C' : Config (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V)} {G : Ghost np}
    {ℓ : Label (Fin np) (queueObj V)} (hrun : (Q H np V).run α = some C)
    (hI : Inv H np α C G) (hs : (Q H np V).step C ℓ = some C') :
    Inv H np (α ++ [ℓ]) C' (gstep H C G ℓ) := by
  cases ℓ with
  | inv p o =>
    obtain ⟨hpn, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
    have hP := hI.proc p
    rw [hpn] at hP
    have hidle := hP.idle_of_none
    obtain ⟨hlf, hpc⟩ := hP
    rw [hidle] at hpc
    obtain ⟨-, hc1, hc2, hc3⟩ := hpc
    refine ⟨by rw [hmem]; exact hI.shape, by rw [hmem]; exact hI.minv,
      by rw [hmem]; exact hI.ginv, by rw [hmem]; exact hI.lin.append_inv p o, fun q => ?_⟩
    rw [hmem, hpend, hloc]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self, opsOf_append, respsOf_append]
      simp only [opsOf, respsOf, List.filterMap_cons, Label.invOf_inv, Label.retOf_inv,
        List.filterMap_nil, ite_true]
      simp only [opsOf, respsOf] at hc1 hc2 hlf
      refine ⟨fun j h1 h2 => ?_, rfl, by simp; omega, by simp; omega, hc3⟩
      rw [List.getElem?_append_left (by omega)]; exact hlf j h1 h2
    · simp only [Function.update_of_ne hq, opsOf_append, respsOf_append]
      simp only [opsOf, respsOf, List.filterMap_cons, Label.invOf_inv, Label.retOf_inv,
        List.filterMap_nil, Ne.symm hq, ite_false, List.append_nil]
      exact hI.proc q
  | ret p r =>
    obtain ⟨hpn, hpend, hmem, l', hact, hloc⟩ := Impl.step_ret hs
    have hP := hI.proc p
    rcases act_ret_cases hact with hidle | ⟨hdone, hl'⟩
    · exfalso; obtain ⟨-, hpc⟩ := hP; rw [hidle] at hpc; exact hpn hpc.1
    obtain ⟨hlf, hpc⟩ := hP
    rw [hdone] at hpc
    obtain ⟨⟨⟨hb1, hb2, hb3, hb4⟩, hb5⟩, hresp⟩ := hpc
    refine ⟨by rw [hmem]; exact hI.shape, by rw [hmem]; exact hI.minv,
      by rw [hmem]; exact hI.ginv, by rw [hmem]; exact hI.lin.append_ret_of_respIn hresp,
      fun q => ?_⟩
    rw [hmem, hpend, hloc]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self, hl']
      simp only [opsOf, respsOf, List.filterMap_append, List.filterMap_cons, Label.invOf_ret,
        Label.retOf_ret, List.filterMap_nil, ite_true, List.append_nil]
      simp only [opsOf, respsOf] at hb2 hb3 hlf
      refine ⟨hlf, rfl, by simp; omega, by simp; omega, by rw [hb5]⟩
    · simp only [Function.update_of_ne hq]
      simp only [opsOf, respsOf, List.filterMap_append, List.filterMap_cons, Label.invOf_ret,
        Label.retOf_ret, List.filterMap_nil, Ne.symm hq, ite_false, List.append_nil]
      exact hI.proc q
  | tau p =>
    obtain ⟨hpn, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
    have hcur : ∀ o, C.pend p = some o → (opsOf α p)[(respsOf α p).length]? = some o :=
      fun o ho => ((Q H np V).run_pend_curOp hrun ho).2.2
    have hact' : act H Variant.fixed p.val (C.loc p) = .access i o k := hact
    have hR := stepRes hH hnp hI.shape hI.minv hI.ginv (hI.proc p) hcur ⟨i, o, k, hact'⟩
    have hM' : C'.mem () = (stepLoc H p (C.loc p) (C.mem ())).1 := by
      rw [hmem]; simp only [Function.update_self, stepLoc, hact']; rfl
    have hL' : C'.loc p = (stepLoc H p (C.loc p) (C.mem ())).2 := by
      rw [hloc]; simp only [Function.update_self, stepLoc, hact']; rfl
    show Inv H np (α ++ [.tau p]) C' (gstepLoc H (C.mem ()) G p (C.loc p))
    rw [← hM', ← hL'] at hR
    have hops : ∀ q, opsOf (α ++ [.tau p]) q = opsOf α q := fun q => opsOf_append_tau α p q
    have hresps : ∀ q, respsOf (α ++ [.tau p]) q = respsOf α q :=
      fun q => respsOf_append_tau α p q
    have hproc : ∀ q, PInv H (opsOf α q) (respsOf α q) (C'.mem ())
        (gstepLoc H (C.mem ()) G p (C.loc p)) q (C'.pend q) (C'.loc q) := by
      intro q
      rw [hpend]
      by_cases hq : q = p
      · subst hq; exact hR.pinv
      · rw [hloc, Function.update_of_ne hq]
        exact (hI.proc q).frame hI.shape hR.upd (hR.upd.keeps hq)
    refine ⟨hR.shape, hR.minv, hR.ginv, ?_, fun q => by rw [hops, hresps]; exact hproc q⟩
    obtain ⟨E, hE⟩ := hR.upd.lin_ext
    have hnd := nodup_rootLin hR.shape
    rw [hE, List.map_append, List.nodup_append] at hnd
    rw [hE]
    refine (hI.lin.append_tau p).push_list E (fun y hy => ?_) hnd.2.1
      (fun y hy hmem' => hnd.2.2 _ hmem' _ (List.mem_map.2 ⟨y, hy, rfl⟩) rfl)
    have hyL : y ∈ rootLin H np (C'.mem ()) := by rw [hE]; exact List.mem_append_right _ hy
    obtain ⟨h1, h2⟩ := mem_pre_prov hR.shape le_rfl (mem_rootLin_pre hyL)
    have hlf := (hproc y.1.1).1 (y.1.2 + 1) (by omega) h1
    simp only [Nat.add_sub_cancel] at hlf
    refine ⟨?_, fun hc => ?_⟩
    · simp only [opOf, hops]; rw [h2]; exact hlf
    · have hc' : Completed α y.1 := by
        simpa [Completed, respsOf_append_tau] using hc
      exact hnd.2.2 _ (hI.lin.complete _ hc') _ (List.mem_map.2 ⟨y, hy, rfl⟩) rfl

end Podc.WaitFreeQueuePolylog

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

/-- The invariant holds in every reachable configuration. -/
theorem exists_inv (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) {α : List (Label (Fin np) (queueObj V))}
    {C : Config (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V)}
    (h : (Q H np V).run α = some C) : ∃ G, Inv H np α C G := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at h; subst h
    exact ⟨_, inv_init hnp⟩
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (Q H np V).runFrom (Q H np V).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      obtain ⟨G, hG⟩ := ih hα
      exact ⟨_, inv_step hH hnp hα hG h⟩

/-- **Theorem 18** (for the repaired algorithm, `Variant.fixed`). The queue implementation is
linearizable: for every finite execution, the root-block order `L` of (3.2) is a
linearization. Here the ordering tree has height `H ≥ 1` and `np ≤ 2^H` processes. -/
theorem theorem_18 (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) :
    (queueImpl H Variant.fixed np : Impl (queueObj V) (fun _ : Unit => memObj V) (Fin np)
      (Loc V)).Linearizable :=
  Impl.linearizable_of_run (fun α C h => by
    obtain ⟨G, hG⟩ := exists_inv hH hnp h
    exact ⟨_, hG.lin⟩)

/-- Lemmas 15 and 17 combined: in every reachable configuration the linearization ordering
`L` (3.2) itself linearizes the execution. -/
theorem lemma_15_17 (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) {α : List (Label (Fin np) (queueObj V))}
    {C : Config (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V)}
    (h : (Q H np V).run α = some C) : IsLinearization α (rootLin H np (C.mem ())) := by
  obtain ⟨G, hG⟩ := exists_inv hH hnp h
  exact hG.lin

end Podc.WaitFreeQueuePolylog
