import Papers.PODC2018.NestingSafeRecoverable.Alg1Inv

/-!
# Algorithm 1: the steps of a process that do not write `R`

Transitions of the per-process invariant `WInv` (pure reasoning on the views), the retraction of a
pending entry, and the preservation of `Inv` by the steps that do not write `R`.
-/

set_option linter.unusedSectionVars false

namespace Podc.NestingSafeRecoverable.Alg1

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] {v₀ : V}

section Pure

variable {L : List (OpId P × RWOp V)} {G : Set V} {R : V} {s : Bool × Option V} {x : OpId P}
  {val : V} {v : Loc1 V} {α : List (Label P (register V v₀))}

lemma winv_w2 (h : WInv L G R s x val .w2 v) (hR : R ∈ G) :
    WInv L G R s x val .w3 { v with temp := R } := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.trans ?_, h2, h3, h4, h5, h6, hR⟩
  simp [LinW]

lemma winv_w3_keep (h : WInv L G R s x val .w3 v) (hn : ¬ (x ∈ L.map Prod.fst ∧ v.temp = R)) :
    WInv L G R (true, some v.temp) x val .w4 v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨⟨fun hx => ?_, fun hl => ?_⟩, h2, by simp, by simp [h5], h5, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨v.temp, rfl, fun e => hn ⟨hx, e.symm⟩⟩))
  · rcases hl with hl | hl | ⟨c, hc, hl⟩ | ⟨hl, -⟩
    · exact absurd hl h5
    · simp at hl
    · simp only [Prod.mk.injEq, Option.some.injEq, true_and] at hc; subst hc
      exact h1.2 (Or.inr (Or.inr (Or.inr ⟨rfl, Ne.symm hl⟩)))
    · cases hl

lemma winv_w3_retract {L' : List (OpId P × RWOp V)} (h : WInv L G R s x val .w3 v)
    (he : v.temp = R) (hx' : x ∉ L'.map Prod.fst) :
    WInv L' G R (true, some v.temp) x val .w4 v := by
  obtain ⟨-, -, -, -, h5, -, -⟩ := h
  refine ⟨⟨fun hx => absurd hx hx', fun hl => ?_⟩, fun hx => absurd hx hx', by simp,
    by simp [h5], h5, rfl⟩
  rcases hl with hl | hl | ⟨c, hc, hl⟩ | ⟨hl, -⟩
  · exact absurd hl h5
  · simp at hl
  · simp only [Prod.mk.injEq, Option.some.injEq, true_and] at hc; subst hc
    exact absurd he.symm hl
  · cases hl

lemma winv_w5 (h : WInv L G R s x val .w5 v) : WInv L G R (false, some val) x val .w6 v := by
  obtain ⟨h1, -, -, -, h5⟩ := h
  have hl : LinW G R s val .w5 v := Or.inl h5
  refine ⟨⟨fun _ => Or.inl h5, fun _ => h1.2 hl⟩, fun _ hv => absurd h5 hv, by simp, by simp,
    h5, rfl⟩

lemma winv_c11 (h : WInv L G R s x val .c11 v) :
    WInv L G R s x val .c12 { v with flag := s.1, curr := s.2 } := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  exact ⟨h1.trans (by simp [LinW]), h2, h3, h4, rfl, rfl⟩

lemma winv_c12_w2 (h : WInv L G R s x val .c12 v)
    (hc : v.flag = false ∧ v.curr ≠ some val) : WInv L G R s x val .w2 v := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [h5] at hc; rw [h6] at hc
  refine ⟨h1.trans (by simp [LinW]), h2, h3, h4, h3 hc.1 hc.2, fun e => ?_⟩
  rw [e] at hc; exact hc.2 rfl

lemma winv_c12_c14 (h : WInv L G R s x val .c12 v) (hc : v.flag = true) :
    WInv L G R s x val .c14 v := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1.trans (by simp [LinW]), h2, h3, h4, h5 ▸ hc, h6⟩

lemma winv_c12_c16 (h : WInv L G R s x val .c12 v)
    (hc : ¬ (v.flag = false ∧ v.curr ≠ some val)) (hc' : ¬ v.flag = true) :
    WInv L G R s x val .c16 v := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hs : s = (false, some val) := by
    simp only [Bool.not_eq_true] at hc'
    rw [hc', not_and, not_not] at hc
    rw [Prod.ext_iff]; exact ⟨h5 ▸ hc', h6 ▸ hc rfl⟩
  have hl : LinW G R s val .c16 v := Or.inr (Or.inl hs)
  exact ⟨⟨fun _ => hl, fun _ => h1.2 (by simp [LinW] at hl ⊢; tauto)⟩, h2, h3, h4, hl⟩

lemma winv_c14 (h : WInv L G R s x val .c14 v) :
    WInv L G R s x val .c15 { v with temp := R } := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.trans (by simp [LinW]), h2, h3, h4, h5, h6, fun c hc => ⟨fun h => h, ?_⟩⟩
  intro e hv
  exact h4 c (Prod.ext h5 hc) hv e

lemma winv_c15_w2 (h : WInv L G R s x val .c15 v) (hc : v.curr = some v.temp) :
    WInv L G R s x val .w2 v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1.trans (by simp [LinW]), h2, h3, h4, (h7 v.temp (h6 ▸ hc)).2 rfl, fun e => ?_⟩
  rw [e] at h5; cases h5

lemma winv_c15_c16 (h : WInv L G R s x val .c15 v) (hc : ¬ v.curr = some v.temp)
    (hs : SInv α G s) : WInv L G R s x val .c16 v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  obtain ⟨c, hc'⟩ : ∃ c, s.2 = some c := by
    rcases hs2 : s.2 with _ | c
    · exact absurd (Prod.ext h5 hs2) hs.2.1
    · exact ⟨c, rfl⟩
  have hR : R ≠ c := (h7 c hc').1 (fun e => hc (by rw [h6, hc', e]))
  have hl : LinW G R s val .c16 v := Or.inr (Or.inr (Or.inl ⟨c, Prod.ext h5 hc', hR⟩))
  exact ⟨⟨fun _ => hl, fun _ => h1.2 (by simp [LinW] at hl ⊢; tauto)⟩, h2, h3, h4, hl⟩

lemma winv_c16 (h : WInv L G R s x val .c16 v) : WInv L G R (false, some val) x val .c17 v := by
  obtain ⟨h1, h2, -, -, h5⟩ := h
  have hx : x ∈ L.map Prod.fst := h1.2 h5
  exact ⟨⟨fun _ => Or.inr (Or.inl rfl), fun _ => hx⟩, h2, by simp, by simp, rfl⟩

end Pure

section Inv

variable {C : (alg1 P V v₀).Cfg} {L : List (OpId P × RWOp V)} {G : Set V}

lemma Inv.cur (hI : Inv C L G) {p : P} {o : RWOp V} {pc : PC1} {v : Loc1 V}
    (h : C.st p = some (o, pc, v)) :
    opOf (N C.hist) (curOp (N C.hist) p) = some o ∧ ¬ Completed (N C.hist) (curOp (N C.hist) p) :=
  Alg.opOf_curOp hI.wf hI.pend h

lemma Inv.retract (hI : Inv C L G) {p : P} {o : RWOp V} {pc : PC1} {v : Loc1 V}
    (h : C.st p = some (o, pc, v)) (hx : curOp (N C.hist) p ∈ L.map Prod.fst)
    (hph : o = .read ∨ FW L (curOp (N C.hist) p) o) :
    ∃ L', IsLinearization (N C.hist) L' ∧
      (register V v₀).runOps v₀ (L'.map Prod.snd) = (register V v₀).runOps v₀ (L.map Prod.snd) ∧
      LSame (v₀ := v₀) p L L' ∧ curOp (N C.hist) p ∉ L'.map Prod.fst := by
  obtain ⟨hop, hc⟩ := hI.cur h
  obtain ⟨L', h1, h2, h3, h4, h5⟩ := hI.lin.retract hc hx hph hop
  refine ⟨L', h1, h2, fun k hk => ?_, fun hx' => ((h3 _).1 hx').2 rfl⟩
  have hkx : k ≠ curOp (N C.hist) p := fun e => hk (by rw [e])
  exact ⟨by rw [h3]; simp [hkx], h4 k hkx, fun o' => h5 k o' hkx⟩

lemma Inv.wInv (hI : Inv C L G) {p : P} {val : V} {pc : PC1} {v : Loc1 V}
    (h : C.st p = some (.write val, pc, v)) :
    WInv L G (Rv C) (Sv C p) (curOp (N C.hist) p) val pc v := by
  have := hI.proc p; rw [h] at this; exact this

lemma Inv.rInv (hI : Inv C L G) {p : P} {pc : PC1} {v : Loc1 V}
    (h : C.st p = some (.read, pc, v)) :
    RInv (v₀ := v₀) L (Sv C p) (curOp (N C.hist) p) pc v := by
  have := hI.proc p; rw [h] at this; exact this

/-- Steps that only change the local state of `p` (internal steps and reads of `R`, `S_p`
with `L` unchanged). -/
lemma Inv.local_step (hI : Inv C L G) {p : P} {C' : (alg1 P V v₀).Cfg} (hC : C' = C.ev (.step p))
    {o : RWOp V} {pc : PC1} {v : Loc1 V}
    (he : C' = { C with st := Function.update C.st p (some (o, pc, v)) })
    (hP : PInv (v₀ := v₀) L G (Rv C) (Sv C p) (curOp (N C.hist) p) (some (o, pc, v))) :
    Inv C' L G := by
  have hwf := hI.wf.ev (.step p); have hpe := hI.pend.ev (.step p)
  rw [← hC, he] at hwf hpe; rw [he]
  exact hI.frame hwf hpe rfl rfl (fun q _ => rfl) (fun q hq => by simp [hq]) hI.lin rfl
    (LSame.rfl' _ _) (hI.sinv p) (by simp only [Function.update_self]; exact hP)

lemma sinv_true {α : List (Label P (register V v₀))} {t : V} (ht : t ∈ G) :
    SInv α G (true, some t) :=
  ⟨fun c hc => by simp only [Prod.mk.injEq, Option.some.injEq, true_and] at hc; exact hc ▸ ht,
    by simp, by simp⟩

lemma sinv_false {α : List (Label P (register V v₀))} {y : OpId P} {w : V}
    (hy : opOf α y = some (.write w)) : SInv α G (false, some w) :=
  ⟨by simp, by simp, fun c hc => by
    simp only [Prod.mk.injEq, Option.some.injEq, true_and] at hc; exact ⟨y, hc ▸ hy⟩⟩

/-- A step of `p` that writes `S_p`. -/
lemma Inv.s_step (hI : Inv C L G) {p : P} {C' : (alg1 P V v₀).Cfg} (hC : C' = C.ev (.step p))
    {o : RWOp V} {pc : PC1} {v : Loc1 V} {s : Bool × Option V} (hR : Rv C' = Rv C)
    (hSp : Sv C' p = s) (hS : ∀ q, q ≠ p → Sv C' q = Sv C q)
    (hst : C'.st = Function.update C.st p (some (o, pc, v))) (hh : C'.hist = C.hist)
    {L' : List (OpId P × RWOp V)} (hlin : IsLinearization (N C.hist) L')
    (hstate : (register V v₀).runOps v₀ (L'.map Prod.snd) =
      (register V v₀).runOps v₀ (L.map Prod.snd))
    (hsame : LSame (v₀ := v₀) p L L') (hsi : SInv (N C.hist) G s)
    (hP : PInv (v₀ := v₀) L' G (Rv C) s (curOp (N C.hist) p) (some (o, pc, v))) :
    Inv C' L' G := by
  have hwf := hI.wf.ev (.step p); have hpe := hI.pend.ev (.step p)
  rw [← hC] at hwf hpe
  exact hI.frame hwf hpe (by rw [hh]) hR hS (fun q hq => by rw [hst]; simp [hq]) hlin hstate
    hsame (hSp ▸ hsi) (by rw [hst, hSp]; simp only [Function.update_self]; exact hP)

/-- A response step of `p`. -/
lemma Inv.ret_step (hI : Inv C L G) {p : P} {r : V} {C' : (alg1 P V v₀).Cfg}
    (hC : C' = C.ev (.step p))
    (he : C' = { C with st := Function.update C.st p none, hist := C.hist ++ [.res p r] })
    (hr : (register V v₀).respIn v₀ L (curOp (N C.hist) p) = some r)
    (hs : (Sv C p).1 = false) : Inv C' L G := by
  have hwf := hI.wf.ev (.step p); have hpe := hI.pend.ev (.step p)
  rw [← hC, he] at hwf hpe; rw [he]
  have hN : N (C.hist ++ [.res p r]) = N C.hist ++ [.ret p r] := by simp
  refine ⟨hwf, hpe, ?_, hI.state, hI.gR, ?_, fun q => ?_, fun q => ?_⟩
  · rw [hN]; exact hI.lin.append_ret_of_respIn hr
  · intro w hw; rw [hN]; simpa using hI.gV w hw
  · obtain ⟨h1, h2, h3⟩ := hI.sinv q
    exact ⟨h1, h2, fun c hc => by rw [hN]; simpa using h3 c hc⟩
  · by_cases hq : q = p
    · subst hq; simp only [Function.update_self]; exact hs
    · simp only [Function.update_of_ne hq]
      have : curOp (N (C.hist ++ [.res p r])) q = curOp (N C.hist) q := by
        rw [hN]; simp [curOp, respsOf_append_ret_of_ne _ _ hq]
      rw [this]; exact hI.proc q

end Inv

end Podc.NestingSafeRecoverable.Alg1
