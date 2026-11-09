import Papers.PODC2012.OptimismConcurrency.ImplModel

/-!
# Observable schedules (§6) and the schedule `σ_bad`

A schedule `σ` is *observable* (§6) "if it has an extension `σ'` such that for all `v ∈ ℤ`, `σ'`
extended with a complete execution of `contains(v)` that returns a matching response is
LS-linearizable".

* `Observable`: the literal reading (the `contains(v)` execution is any solo sequential run of
  `contains(v)` of `LL`, from any memory).
* `ObservableStrong`: a much stronger reading, in the spirit of "no lost updates": there is an
  honest history `H` exporting an extension of `σ`, and for every `v` the history `H` followed by
  `contains(v)` run solo on the *actual* final memory of `H` is LS-linearizable.
  `ObservableStrong.observable`: the strong reading implies the literal one.

`sigmaBad`: from `{1, 3, 4}`, `contains(4)` (process 1) reads `head` and `X₁`; then `remove(3)`
(process 2) runs completely (unlinks `X₃` by writing `X₁`); then `contains(4)` reads `X₃`, `X₄` and
returns `true`. `sigmaBad_observableStrong`: this schedule is observable even in the strong sense.
(`IRM.lean` shows that `I_RM` rejects it.)
-/

namespace Podc.OptimismConcurrency

variable {P : Type} [DecidableEq P]

/-- `C` is a complete execution of `contains(v)` by `p`, run alone from memory `m` with the code
`LL` (reads return `m`). -/
def SoloContains (m : Mem) (p : P) (v : ℤ) (C : LHist P) : Prop :=
  C.head? = some (.inv p () (.contains v)) ∧ (C.filter Ev.isInv).length = 1 ∧
    ∃ m', seqRun ⟨m, none, none⟩ C = some ⟨m', none, none⟩

/-- **Observable schedule** (§6), literal reading. -/
def Observable (σ : LSched P) : Prop :=
  ∃ σ', σ <+: σ' ∧ ∀ v : ℤ, ∃ (m : Mem) (p : P) (C : LHist P), SoloContains m p v C ∧
    LSLSched SigLL (specSet P) (σ' ++ C.map Ev.erase)

/-- **Observable schedule**, strong reading: the extension is exported by an honest history `H`,
and `contains(v)` runs on the actual final memory of `H`. -/
def ObservableStrong (σ : LSched P) : Prop :=
  ∃ (H : LHist P) (c : HCfg P), honRun hcfg0 H = some c ∧ σ <+: sched H ∧
    ∀ v : ℤ, ∃ (p : P) (C : LHist P), SoloContains c.mem p v C ∧ LSL_LL (H ++ C) ∧
      Honest (H ++ C) ∧ sched (H ++ C) = sched H ++ C.map Ev.erase

/-- The strong reading implies the literal one. -/
theorem ObservableStrong.observable {σ : LSched P} (h : ObservableStrong σ) : Observable σ := by
  obtain ⟨H, c, -, hσ, hv⟩ := h
  refine ⟨sched H, hσ, fun v => ?_⟩
  obtain ⟨p, C, hC, hlsl, -, hs⟩ := hv v
  exact ⟨c.mem, p, C, hC, H ++ C, hlsl, hs⟩

/-! ## Helper lemmas on histories -/

section Helpers

variable {X Op Res Obj Val : Type} [DecidableEq X]

lemma lookFilter_append {α : Type*} (f : α → List α → Bool) (A B : List α)
    (h : ∀ i (hi : i < A.length), f A[i] (A.drop (i + 1) ++ B) = f A[i] (A.drop (i + 1))) :
    lookFilter f (A ++ B) = lookFilter f A ++ lookFilter f B := by
  induction A with
  | nil => simp [lookFilter]
  | cons a A ih =>
    have h0 : f a (A ++ B) = f a A := h 0 (by simp)
    have ih' := ih (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simpa only [List.getElem_cons_succ, List.drop_succ_cons] using this)
    simp only [List.cons_append, lookFilter, h0, ih']
    split <;> rfl

lemma termOf_append_of_isSome (p : P) (x : X) (A B : Hist P X Op Res Obj Val)
    (h : (termOf p x A).isSome) : termOf p x (A ++ B) = termOf p x A := by
  unfold termOf at *
  rw [List.find?_append]
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 h
  rw [he]; rfl

end Helpers

lemma seqRun_append (c : SCfg P) (A B : LHist P) :
    seqRun c (A ++ B) = (seqRun c A).bind (fun c' => seqRun c' B) := by
  induction A generalizing c with
  | nil => simp [seqRun]
  | cons a A ih =>
    simp only [List.cons_append, seqRun]
    cases seqStep c a <;> simp [ih]

lemma honRun_append (c : HCfg P) (A B : LHist P) :
    honRun c (A ++ B) = (honRun c A).bind (fun c' => honRun c' B) := by
  induction A generalizing c with
  | nil => simp [honRun]
  | cons a A ih =>
    simp only [List.cons_append, honRun]
    cases honStep c a <;> simp [ih]

/-! ## The schedule `σ_bad` -/

/-- A history exporting `σ_bad`. -/
def histBad : LHist ℕ :=
  pre134 ++
  [.inv 1 () (.contains 4)] ++ rd 1 headL ⟨.ninf, Xl 1⟩ ++ rd 1 (Xl 1) ⟨.fin 1, Xl 3⟩ ++
  [.inv 2 () (.remove 3)] ++ rd 2 headL ⟨.ninf, Xl 1⟩ ++ rd 2 (Xl 1) ⟨.fin 1, Xl 3⟩ ++
    rd 2 (Xl 3) ⟨.fin 3, Xl 4⟩ ++ wr 2 (Xl 1) ⟨.fin 1, Xl 4⟩ ++ [.res 2 () true] ++
  rd 1 (Xl 3) ⟨.fin 3, Xl 4⟩ ++ rd 1 (Xl 4) ⟨.fin 4, tailL⟩ ++ [.res 1 () true]

/-- **The schedule `σ_bad`**: `remove(3)` runs entirely between two reads of `contains(4)`; the
read of the removed node `X₃` by `contains(4)` starts after `remove(3)` has returned. -/
def sigmaBad : LSched ℕ := histBad.map Ev.erase

end Podc.OptimismConcurrency

namespace Podc.OptimismConcurrency

section Append

variable {P X Op Res Obj Val : Type} [DecidableEq P] [DecidableEq X]

lemma keepHL_append (e : Ev P X Op Res Obj Val) (l B : Hist P X Op Res Obj Val)
    (h : e.isInv = true → (termOf e.proc e.obj l).isSome) : keepHL e (l ++ B) = keepHL e l := by
  cases e with
  | inv p x o => simp only [keepHL]; rw [termOf_append_of_isSome p x _ _ (h rfl)]
  | _ => rfl

lemma keepC_append (e : Ev P X Op Res Obj Val) (l B : Hist P X Op Res Obj Val)
    (h : (termOf e.proc e.obj (e :: l)).isSome) : keepC e (l ++ B) = keepC e l := by
  simp only [keepC]; rw [← List.cons_append, termOf_append_of_isSome _ _ _ _ h]

lemma hl_append (A B : Hist P X Op Res Obj Val)
    (hA : ∀ i (hi : i < A.length), A[i].isInv = true →
      (termOf A[i].proc A[i].obj (A.drop (i + 1))).isSome) :
    hl (A ++ B) = hl A ++ hl B := by
  unfold hl
  rw [lookFilter_append _ _ _ fun i hi => keepHL_append _ _ _ (hA i hi), List.filterMap_append]

lemma complete_append (A B : Hist P X Op Res Obj Val)
    (hA : ∀ i (hi : i < A.length), (termOf A[i].proc A[i].obj (A[i] :: A.drop (i + 1))).isSome) :
    complete (A ++ B) = complete A ++ complete B := by
  unfold complete
  exact lookFilter_append _ _ _ fun i hi => keepC_append _ _ _ (hA i hi)

end Append

/-! ## `σ_bad` is observable -/

/-- A complete execution of `contains(v)` by process `3` on the list `head → X₁ → X₄ → tail`
(reads follow `LL`). -/
def contC (v : ℤ) : LHist ℕ :=
  [.inv 3 () (.contains v)] ++ rd 3 headL ⟨.ninf, Xl 1⟩ ++ rd 3 (Xl 1) ⟨.fin 1, Xl 4⟩ ++
  (if v ≤ 1 then [.res 3 () (decide (v = 1))]
   else rd 3 (Xl 4) ⟨.fin 4, tailL⟩ ++
     (if v ≤ 4 then [.res 3 () (decide (v = 4))]
      else rd 3 tailL ⟨.pinf, tailL⟩ ++ [.res 3 () false]))

/-- `complete(contC v) = contC v`. -/
lemma complete_contC (v : ℤ) : complete (contC v) = contC v := by
  unfold contC; split_ifs <;> simp [complete, lookFilter, keepC, termOf, rd, Ev.isTerm, Ev.isRes, Ev.isAbort, Ev.proc, Ev.obj]

/-- The high-level history of `contC v`. -/
lemma hl_contC (v : ℤ) : hl (contC v) = [.inv 3 () (.contains v), .res 3 () (decide (v = 1 ∨ v = 4))] := by
  unfold contC; split_ifs <;> simp [hl, lookFilter, keepHL, termOf, rd, Ev.isTerm, Ev.isRes, Ev.isAbort, toHW] <;> omega

/-- Sequential run of `contains(v)` on a memory representing `{1, 4}`. -/
lemma seqRun_contC (m : Mem) (h0 : m headL = some ⟨.ninf, Xl 1⟩) (h1 : m (Xl 1) = some ⟨.fin 1, Xl 4⟩)
    (h4 : m (Xl 4) = some ⟨.fin 4, tailL⟩) (ht : m tailL = some ⟨.pinf, tailL⟩) (v : ℤ) :
    seqRun (⟨m, none, none⟩ : SCfg ℕ) (contC v) = some ⟨m, none, none⟩ := by
  unfold contC; split_ifs with ha hb
  · have : ¬ (1 < v) := by omega
    have e : decide ((1:ℤ) = v) = decide (v = 1) := by simp [eq_comm]
    simp [seqRun, seqStep, rd, act, onRead, h0, h1, Key.ltZ, finish, SetOp.arg, this, e]
  · have : 1 < v := by omega
    have h2 : ¬ (4 < v) := by omega
    have e : decide ((4:ℤ) = v) = decide (v = 4) := by simp [eq_comm]
    simp [seqRun, seqStep, rd, act, onRead, h0, h1, h4, Key.ltZ, finish, SetOp.arg, this, h2, e]
  · have : 1 < v := by omega
    have h2 : 4 < v := by omega
    simp [seqRun, seqStep, rd, act, onRead, h0, h1, h4, ht, Key.ltZ, finish, SetOp.arg, this, h2]


open Cslib.SharedMemory

instance : DecidableEq setObj.Resp := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq setObj.Op := inferInstanceAs (DecidableEq SetOp)
instance : DecidableEq setObj.State := inferInstanceAs (DecidableEq (Finset ℤ))

/-- The high-level history of `histBad`, annotated with linearization points. -/
def annBad : List (LPLabel ℕ setObj) :=
  [.inv 0 (SetOp.insert 4), .lin 0, .ret 0 true, .inv 0 (SetOp.insert 3), .lin 0, .ret 0 true,
   .inv 0 (SetOp.insert 1), .lin 0, .ret 0 true,
   .inv 1 (SetOp.contains 4), .lin 1, .inv 2 (SetOp.remove 3), .lin 2, .ret 2 true, .ret 1 true]


lemma sched_histBad : sched histBad = sigmaBad := by
  unfold sched sigmaBad; rw [show complete histBad = histBad by decide]

/-- The `remove(3)` operation of `histBad`. -/
def removeOp : LHist ℕ :=
  [.inv 2 () (.remove 3)] ++ rd 2 headL ⟨.ninf, Xl 1⟩ ++ rd 2 (Xl 1) ⟨.fin 1, Xl 3⟩ ++
    rd 2 (Xl 3) ⟨.fin 3, Xl 4⟩ ++ wr 2 (Xl 1) ⟨.fin 1, Xl 4⟩ ++ [.res 2 () true]

/-- Memory representing the list `head → X₁ → X₄ → tail`. -/
structure MemBad (m : Mem) : Prop where
  h0 : m headL = some ⟨.ninf, Xl 1⟩
  h1 : m (Xl 1) = some ⟨.fin 1, Xl 4⟩
  h4 : m (Xl 4) = some ⟨.fin 4, tailL⟩
  ht : m tailL = some ⟨.pinf, tailL⟩

lemma seqRun_pre_remove :
    ∃ m, seqRun scfg0 (pre134 ++ removeOp) = some ⟨m, none, none⟩ ∧ MemBad m := by
  have h : (seqRun scfg0 (pre134 ++ removeOp)).map (fun c =>
      (c.cur.isNone && c.pend.isNone, c.mem headL, c.mem (Xl 1), c.mem (Xl 4), c.mem tailL)) =
      some (true, some ⟨.ninf, Xl 1⟩, some ⟨.fin 1, Xl 4⟩, some ⟨.fin 4, tailL⟩,
        some ⟨.pinf, tailL⟩) := by decide
  cases hc : seqRun scfg0 (pre134 ++ removeOp) with
  | none => simp [hc] at h
  | some c =>
    obtain ⟨m, cur, pend⟩ := c
    simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at h
    obtain ⟨⟨rfl, rfl⟩, h0, h1, h4, ht⟩ := h
    exact ⟨m, rfl, ⟨h0, h1, h4, ht⟩⟩

lemma honRun_histBad : ∃ c, honRun hcfg0 histBad = some c ∧ MemBad c.mem := by
  have h : (honRun hcfg0 histBad).map (fun c =>
      (c.mem headL, c.mem (Xl 1), c.mem (Xl 4), c.mem tailL)) =
      some (some ⟨.ninf, Xl 1⟩, some ⟨.fin 1, Xl 4⟩, some ⟨.fin 4, tailL⟩,
        some ⟨.pinf, tailL⟩) := by decide
  cases hc : honRun hcfg0 histBad with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h0, h1, h4, ht⟩ := h
    exact ⟨c, rfl, ⟨h0, h1, h4, ht⟩⟩

lemma honRun_contC (c : HCfg ℕ) (hm : MemBad c.mem) (v : ℤ) : (honRun c (contC v)).isSome := by
  unfold contC
  split_ifs <;> simp [honRun, honStep, rd, hm.h0, hm.h1, hm.h4, hm.ht]

lemma lpRun_annBad : ∃ c, lpRun (setObj.init, fun _ => .idle) annBad = some c ∧
    (show Finset ℤ from c.1) = {1, 4} ∧ c.2 3 = .idle := by
  have h : (lpRun (setObj.init, fun _ => .idle) annBad).map (fun c =>
      ((c.1 : Finset ℤ), match c.2 3 with | .idle => true | _ => false)) =
      some (({1, 4} : Finset ℤ), true) := by decide
  cases hc : lpRun (setObj.init, fun _ => .idle) annBad with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.map_some, Option.some.injEq] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    refine ⟨c, rfl, h1, ?_⟩
    generalize c.2 3 = s at h2 ⊢
    cases s <;> simp_all

lemma restrictPX_contC (v : ℤ) : restrictPX (contC v) 3 () = contC v := by
  unfold contC restrictPX; split_ifs <;> simp [rd]

lemma restrictPX_contC_ne (v : ℤ) (p : ℕ) (hp : p ≠ 3) : restrictPX (contC v) p () = [] := by
  unfold contC restrictPX; split_ifs <;> simp [rd, Ne.symm hp]

lemma restrictPX_histBad_ge (p : ℕ) (hp : 3 ≤ p) : restrictPX histBad p () = [] := by
  have h : ∀ e ∈ histBad, e.proc < 3 := by decide
  unfold restrictPX
  rw [List.filter_eq_nil_iff]
  intro e he; have := h e he; simp; omega

lemma splitOps_contC (v : ℤ) : splitOps (contC v) = [contC v] := by
  unfold contC splitOps; split_ifs <;> simp [rd, Ev.isInv]

lemma locSer_bad (v : ℤ) : LocSer SigLL (histBad ++ contC v) := by
  intro p x k hk
  cases x
  by_cases hp : p = 3
  · subst hp
    have hr : restrictPX (histBad ++ contC v) 3 () = contC v := by
      rw [restrictPX, List.filter_append, ← restrictPX, ← restrictPX,
        restrictPX_histBad_ge 3 le_rfl, restrictPX_contC]; rfl
    rw [numOps, hr, splitOps_contC] at hk
    simp only [List.length_singleton, Nat.lt_one_iff] at hk; subst hk
    obtain ⟨m, hs, hm⟩ := seqRun_pre_remove
    refine ⟨pre134 ++ removeOp, ?_⟩
    have hl : localView (histBad ++ contC v) 3 () 0 = contC v := by
      rw [localView, hr, splitOps_contC]
      simp only [List.getD_cons_zero]
      unfold dropAbort contC; split_ifs <;> simp_all [rd, Ev.isAbort]
    rw [hl]
    show (seqRun scfg0 _).isSome = true
    rw [seqRun_append, hs, Option.bind_some, seqRun_contC m hm.h0 hm.h1 hm.h4 hm.ht]; rfl
  · have hr : restrictPX (histBad ++ contC v) p () = restrictPX histBad p () := by
      rw [restrictPX, List.filter_append, ← restrictPX, ← restrictPX,
        restrictPX_contC_ne v p hp, List.append_nil]
    rw [numOps, hr] at hk
    rw [localView, hr]
    by_cases h3 : 3 ≤ p
    · rw [restrictPX_histBad_ge p h3] at hk; simp [splitOps] at hk
    · have key : ∀ p < 3, ∀ k < (splitOps (restrictPX histBad p ())).length,
          (if p = 0 then pre134.take (10 * k) else pre134) ++
            dropAbort ((splitOps (restrictPX histBad p ())).getD k []) ∈ SigLL := by decide
      exact ⟨_, key p (by omega) k hk⟩

lemma lin_bad (v : ℤ) :
    Cslib.SharedMemory.HerlihyWing.Linearizable (specSet ℕ) (hl (histBad ++ contC v)) := by
  have hcond : ∀ i (hi : i < histBad.length), histBad[i].isInv = true →
      (termOf histBad[i].proc histBad[i].obj (histBad.drop (i + 1))).isSome := by decide
  rw [hl_append _ _ hcond, hl_contC]
  obtain ⟨c, hc, hc1, hc2⟩ := lpRun_annBad
  have hrun : lpRun (setObj.init, fun _ => .idle)
      (annBad ++ [.inv 3 (SetOp.contains v), .lin 3, .ret 3 (decide (v = 1 ∨ v = 4))]) ≠ none := by
    rw [lpRun_append, hc, Option.bind_some]
    obtain ⟨s, st⟩ := c
    simp only at hc1 hc2
    subst hc1
    simp only [lpRun, lpStep, hc2, Option.bind_some, Function.update_self]
    simp [setObj, setδ]
  obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.1 hrun
  refine hwLinearizable_of_lpRun' hc' ?_
  rw [List.filterMap_append]
  have h1 : Cslib.SharedMemory.HerlihyWing.toHist (annBad.filterMap LPLabel.erase) = hl histBad := by
    rfl
  simp only [Cslib.SharedMemory.HerlihyWing.toHist, List.flatMap_append] at h1 ⊢
  rw [h1]; rfl

/-- **`σ_bad` is observable**, even in the strong sense. -/
theorem sigmaBad_observableStrong : ObservableStrong sigmaBad := by
  obtain ⟨c, hc, hm⟩ := honRun_histBad
  have hcondC : ∀ i (hi : i < histBad.length),
      (termOf histBad[i].proc histBad[i].obj (histBad[i] :: histBad.drop (i + 1))).isSome := by
    decide
  refine ⟨histBad, c, hc, by rw [sched_histBad], fun v => ⟨3, contC v, ?_, ⟨locSer_bad v, lin_bad v⟩,
    ?_, ?_⟩⟩
  · refine ⟨?_, ?_, c.mem, seqRun_contC c.mem hm.h0 hm.h1 hm.h4 hm.ht v⟩
    · unfold contC; split_ifs <;> rfl
    · unfold contC; split_ifs <;> rfl
  · show (honRun hcfg0 _).isSome = true
    rw [honRun_append, hc, Option.bind_some]; exact honRun_contC c hm v
  · unfold sched; rw [complete_append _ _ hcondC, complete_contC, List.map_append]

/-- `σ_bad` is observable (literal reading of §6). -/
theorem sigmaBad_observable : Observable sigmaBad := sigmaBad_observableStrong.observable

end Podc.OptimismConcurrency
