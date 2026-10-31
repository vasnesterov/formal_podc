import Papers.PODC2018.NestingSafeRecoverable.Alg1Local

/-!
# Algorithm 1: the write of `R` (line 4)

When `p` writes `val` to `R`, every other pending `WRITE` that becomes linearized by this write
(`Armed`: it was not linearized before and is afterwards — the paper's "a write by a different
process `q` occurred between the two reads of `R` by `p`") is linearized *immediately before*
`p`'s write, as a phantom entry; if `p` itself had a phantom entry, it is retracted first.
-/

set_option linter.unusedSectionVars false

namespace Podc.NestingSafeRecoverable.Alg1

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] {v₀ : V}

/-- Entries of a list of writes followed by a write are followed by writes. -/
lemma fw_of_writes {K : Type} {M : List (K × RWOp V)} (hM : ∀ y ∈ M, ∃ u, y.2 = .write u)
    {x : K} {o : RWOp V} (hx : (x, o) ∈ M) (z : K) (u : V) : FW (M ++ [(z, .write u)]) x o := by
  induction M with
  | nil => simp at hx
  | cons a M ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · rcases M with _ | ⟨⟨b1, b2⟩, M⟩
      · exact ⟨[], z, u, [], rfl⟩
      · obtain ⟨u', hu'⟩ := hM (b1, b2) (by simp)
        simp only at hu'; subst hu'
        exact ⟨[], b1, u', M ++ [(z, .write u)], rfl⟩
    · exact (ih (fun y hy => hM y (List.mem_cons_of_mem _ hy)) hx).cons a

lemma mem_procs {α : List (Label P (register V v₀))} {x : OpId P} {o : RWOp V}
    (h : opOf α x = some o) : x.1 ∈ α.map Label.proc := by
  have ho : o ∈ opsOf α x.1 := List.mem_of_getElem? h
  simp only [opsOf, List.mem_filterMap] at ho
  obtain ⟨ℓ, hℓ, he⟩ := ho
  refine List.mem_map.2 ⟨ℓ, hℓ, ?_⟩
  cases ℓ with
  | inv q o' => by_cases hq : q = x.1 <;> simp_all [Label.invOf, Label.proc]
  | ret q r => simp [Label.invOf] at he
  | tau q => simp [Label.invOf] at he

section Pure

variable {G : Set V} {R : V} {s : Bool × Option V} {w val : V} {pc : PC1} {v : Loc1 V}
  {α : List (Label P (register V v₀))}

lemma linW_mono (h : LinW G R s w pc v) (hsi : SInv α G s) (hloc : LocW G R s w pc v)
    (hval : val ∉ G) : LinW (insert val G) val s w pc v := by
  rcases h with h | h | ⟨c, hc, -⟩ | ⟨rfl, -⟩
  · exact Or.inl (Set.mem_insert_of_mem _ h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, fun e => hval (e ▸ hsi.1 c hc)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, fun e => hval (e ▸ hloc.2.2)⟩))

lemma locW_other (h : LocW G R s w pc v) (hsi : SInv α G s) (hval : val ∉ G) (hwv : w ≠ val) :
    LocW (insert val G) val s w pc v := by
  have hw : w ∈ insert val G ↔ w ∈ G := by simp [hwv]
  cases pc with
  | w2 => exact ⟨hw.not.2 h.1, h.2⟩
  | w3 => exact ⟨hw.not.2 h.1, h.2.1, Set.mem_insert_of_mem _ h.2.2⟩
  | w4 => exact ⟨hw.not.2 h.1, h.2⟩
  | w5 => exact Set.mem_insert_of_mem _ h
  | w6 => exact ⟨Set.mem_insert_of_mem _ h.1, h.2⟩
  | r8 => exact h.elim
  | r9 => exact h.elim
  | c11 => trivial
  | c12 => exact h
  | c14 => exact h
  | c15 =>
    refine ⟨h.1, h.2.1, fun c hc => ⟨fun _ e => hval (e ▸ hsi.1 c (Prod.ext h.1 hc)), fun e => ?_⟩⟩
    exact hw.not.2 ((h.2.2 c hc).2 e)
  | c16 => exact linW_mono h hsi h hval
  | c17 => exact h

lemma winv_other {L L' : List (OpId P × RWOp V)} {x : OpId P}
    (h : WInv L G R s x w pc v) (hsi : SInv α G s) (hval : val ∉ G) (hwv : w ≠ val)
    (hmem : x ∈ L'.map Prod.fst ↔
      x ∈ L.map Prod.fst ∨ (¬ LinW G R s w pc v ∧ LinW (insert val G) val s w pc v))
    (hfw : ∀ o, FW L x o → FW L' x o)
    (hfwM : ¬ LinW G R s w pc v → LinW (insert val G) val s w pc v → FW L' x (.write w)) :
    WInv L' (insert val G) val s x w pc v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hw : w ∈ insert val G ↔ w ∈ G := by simp [hwv]
  refine ⟨⟨fun hx => ?_, fun hl => ?_⟩, fun hx hwG => ?_, fun h1 h2 => hw.not.2 (h3 h1 h2),
    fun c hc _ e => hval (e ▸ hsi.1 c hc), locW_other h5 hsi hval hwv⟩
  · rcases hmem.1 hx with hx | ⟨-, hl⟩
    · exact linW_mono (h1.1 hx) hsi h5 hval
    · exact hl
  · by_cases hl' : LinW G R s w pc v
    · exact hmem.2 (Or.inl (h1.2 hl'))
    · exact hmem.2 (Or.inr ⟨hl', hl⟩)
  · by_cases hl' : LinW G R s w pc v
    · exact hfw _ (h2 (h1.2 hl') (hw.not.1 hwG))
    · rcases hmem.1 hx with hx | ⟨-, hl⟩
      · exact absurd (h1.1 hx) hl'
      · exact hfwM hl' hl

end Pure

/-- The process `q` becomes linearized (as a phantom) by the write of `val` to `R` by `p`. -/
def Armed (C : (alg1 P V v₀).Cfg) (G : Set V) (p : P) (val : V) (q : P) : Prop :=
  q ≠ p ∧ ∃ w pc v, C.st q = some (.write w, pc, v) ∧ ¬ LinW G (Rv C) (Sv C q) w pc v ∧
    LinW (insert val G) val (Sv C q) w pc v

variable {C : (alg1 P V v₀).Cfg} {L : List (OpId P × RWOp V)} {G : Set V}

/-- The write of `R` in line 4. -/
theorem Inv.step_w4 (hI : Inv C L G) (henv : Env1 v₀ (N C.hist)) {p : P} {val : V}
    {v : Loc1 V} (h : C.st p = some (.write val, .w4, v)) :
    ∃ L' G', Inv (C.ev (.step p)) L' G' := by
  classical
  set α := N C.hist with hα
  set xp := curOp α p with hxp
  have hw := hI.wInv h
  obtain ⟨hpw1, hpw2, -, -, hval, hs1⟩ := hw
  obtain ⟨hopp, hcp⟩ := hI.cur h
  -- retract the phantom entry of `p`, if any
  obtain ⟨L₀, hL₀, hsame, hxp₀⟩ : ∃ L₀, IsLinearization α L₀ ∧ LSame (v₀ := v₀) p L L₀ ∧
      xp ∉ L₀.map Prod.fst := by
    by_cases hx : xp ∈ L.map Prod.fst
    · obtain ⟨L₀, h1, -, h3, h4⟩ := hI.retract h hx (Or.inr (hpw2 hx hval))
      exact ⟨L₀, h1, h3, h4⟩
    · exact ⟨L, hI.lin, LSame.rfl' _ _, hx⟩
  -- the processes linearized by this write
  have hQmem : ∀ q, q ∈ ((α.map Label.proc).dedup.filter (fun q => decide (Armed C G p val q)))
      ↔ Armed C G p val q := by
    intro q
    simp only [List.mem_filter, List.mem_dedup, decide_eq_true_eq, and_iff_right_iff_imp]
    rintro ⟨-, w, pc, v', hq, -⟩
    exact mem_procs (hI.cur hq).1
  set Q := (α.map Label.proc).dedup.filter (fun q => decide (Armed C G p val q)) with hQ
  let wv : P → V := fun q => match C.st q with | some (o, _, _) => wval v₀ o | none => v₀
  set M := Q.map (fun q => (curOp α q, RWOp.write (wv q))) with hM
  have hwv : ∀ q w pc v', C.st q = some (.write w, pc, v') → wv q = w := by
    intro q w pc v' hq; simp only [wv, hq]; rfl
  have hMmem : ∀ k, k ∈ M.map Prod.fst ↔ ∃ q, Armed C G p val q ∧ k = curOp α q := by
    intro k
    simp only [hM, List.map_map, List.mem_map, Function.comp_def, hQmem]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  have hMw : ∀ y ∈ M, ∃ u, y.2 = .write u := by
    intro y hy; simp only [hM, List.mem_map] at hy; obtain ⟨q, -, rfl⟩ := hy; exact ⟨_, rfl⟩
  have hMop : ∀ y ∈ M, opOf α y.1 = some y.2 ∧ ¬ Completed α y.1 := by
    intro y hy
    simp only [hM, List.mem_map, hQmem] at hy
    obtain ⟨q, ⟨-, w, pc, v', hq, -⟩, rfl⟩ := hy
    rw [hwv q w pc v' hq]; exact hI.cur hq
  have hMnd : (M.map Prod.fst).Nodup := by
    simp only [hM, List.map_map]
    refine List.Nodup.map (fun a b hab => by simpa [curOp] using congrArg Prod.fst hab) ?_
    exact (List.nodup_dedup _).filter _
  have hMdisj : ∀ y ∈ M, y.1 ∉ L₀.map Prod.fst := by
    intro y hy hy0
    have : y.1 ∈ M.map Prod.fst := List.mem_map_of_mem hy
    obtain ⟨q, ⟨hqp, w, pc, v', hq, hn, -⟩, he⟩ := (hMmem _).1 this
    rw [he] at hy0
    have hw' := hI.wInv hq
    exact hn (hw'.1.1 ((hsame _ hqp).1.1 hy0))
  have hxpM : xp ∉ M.map Prod.fst := by
    intro hx
    obtain ⟨q, ⟨hqp, -⟩, he⟩ := (hMmem _).1 hx
    exact hqp (congrArg Prod.fst he).symm
  have hlin' : IsLinearization α (L₀ ++ M ++ [(xp, .write val)]) := by
    refine (hL₀.push_list M hMop hMnd hMdisj).push hopp ?_ hcp
    rw [List.map_append, List.mem_append, not_or]; exact ⟨hxp₀, hxpM⟩
  -- the new configuration
  obtain ⟨hR', hS', hst', hh'⟩ := ev_R_write (k := fun _ => v) (w := val) h rfl
  have hN : N (C.ev (.step p)).hist = α := by rw [hh']
  refine ⟨L₀ ++ M ++ [(xp, .write val)], insert val G, hI.wf.ev _, hI.pend.ev _, hN ▸ hlin',
    by rw [hR']; exact runOps_concat_write _ _ _ _, by rw [hR']; exact Set.mem_insert _ _,
    ?_, fun q => ?_, fun q => ?_⟩
  · intro w hw
    rw [hN]
    rcases (Set.mem_insert_iff.1 hw) with rfl | hw
    · exact Or.inr ⟨xp, hopp⟩
    · exact hI.gV w hw
  · rw [hN, hS' q]
    obtain ⟨h1, h2, h3⟩ := hI.sinv q
    exact ⟨fun c hc => Set.mem_insert_of_mem _ (h1 c hc), h2, h3⟩
  · rw [hN, hR', hS' q, hst']
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self]
      refine ⟨⟨fun _ => Or.inl (Set.mem_insert _ _), fun _ => by simp [hxp]⟩, fun _ h => absurd
        (Set.mem_insert _ _) h, fun h1 _ _ => (by rw [hs1] at h1; cases h1), fun c hc _ e => ?_,
        Set.mem_insert _ _⟩
      exact hval (e ▸ (hI.sinv q).1 c hc)
    simp only [Function.update_of_ne hqp]
    have hP := hI.proc q
    have hsame' := hsame (curOp α q) hqp
    rcases hq : C.st q with _ | ⟨_ | w, pc, v'⟩
    · rw [hq] at hP; exact hP
    · rw [hq] at hP
      obtain ⟨hs0, hr⟩ := hP
      refine ⟨hs0, ?_⟩
      rcases hr with ⟨rfl, hx⟩ | ⟨rfl, hr⟩
      · refine Or.inl ⟨rfl, ?_⟩
        rw [List.map_append, List.map_append, List.mem_append, List.mem_append, not_or, not_or]
        refine ⟨⟨fun h0 => hx (hsame'.1.1 h0), fun hm => ?_⟩, ?_⟩
        · obtain ⟨q', ⟨-, w, pc, v'', hq', -⟩, he⟩ := (hMmem _).1 hm
          have : q' = q := (congrArg Prod.fst he).symm
          subst this; rw [hq] at hq'; cases hq'
        · simp only [List.map_cons, List.map_nil, List.mem_singleton]
          intro he; exact hqp (congrArg Prod.fst he)
      · refine Or.inr ⟨rfl, ?_⟩
        rw [List.append_assoc, ObjSpec.respIn_append_of_mem
          (ObjSpec.mem_of_respIn_eq_some (hsame'.2.1 ▸ hr)), hsame'.2.1, hr]
    · rw [hq] at hP
      have hwv' : w ≠ val := by
        intro e; subst e
        have := henv.2 _ _ _ (hI.cur hq).1 hopp
        exact hqp (congrArg Prod.fst this)
      refine winv_other hP (hI.sinv q) hval hwv' ?_ ?_ ?_
      · rw [List.map_append, List.map_append, List.mem_append, List.mem_append, hsame'.1, hMmem]
        simp only [List.map_cons, List.map_nil, List.mem_singleton]
        constructor
        · rintro ((h0 | ⟨q', ⟨-, w', pc', v'', hq', hn, hl⟩, he⟩) | he)
          · exact Or.inl h0
          · have : q' = q := (congrArg Prod.fst he).symm
            subst this; rw [hq] at hq'; cases hq'; exact Or.inr ⟨hn, hl⟩
          · exact absurd (congrArg Prod.fst he) hqp
        · rintro (h0 | ⟨hn, hl⟩)
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr ⟨q, ⟨hqp, w, pc, v', hq, hn, hl⟩, rfl⟩)
      · intro o hfw
        rw [List.append_assoc]; exact (hsame'.2.2 o hfw).append _
      · intro hn hl
        have hmem : (curOp α q, RWOp.write w) ∈ M := by
          simp only [hM, List.mem_map, hQmem]
          exact ⟨q, ⟨hqp, w, pc, v', hq, hn, hl⟩, by rw [hwv q w pc v' hq]⟩
        obtain ⟨L₁, y, u, L₂, he⟩ := fw_of_writes hMw hmem xp val
        exact ⟨L₀ ++ L₁, y, u, L₂, by rw [List.append_assoc, he]; simp⟩

end Podc.NestingSafeRecoverable.Alg1
