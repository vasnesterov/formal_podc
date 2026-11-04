import Papers.PODC2014.WritableObjects.Lemma48Exec5

/-!
# Lemma 4.8 of [AGW14] (thesis numbering)

The wait-free algorithm of Figure 4.5 follows the template of Figure 4.4 (`Template`) and
satisfies condition (C) of Lemma 4.5 (`CondC`) in every execution.

The proof is an invariant proof (`Inv`, files `Lemma48*.lean`); the invariant encodes the claims
of Section 4.4.2 of the thesis:

* Claims 4.9–4.15 (queues of `recycle()`): `QOK`, `Hold`, `Inv.qok`, `Inv.chosen`;
* Claims 4.16–4.17 (an index read in `Annc`, `H`, `H'` is not recycled): `Loc.SlotProt` and
  `Loc.r27_slot`/`r29_slot`/`r31_slot`;
* Claims 4.18–4.20 (stable hints): `Bcore`, `PSide`, `Cprog`, `Inv.bcore_frame`,
  `Inv.a1_frame`;
* Claims 4.21–4.23 (an index in use is not written): `Inv.ptrProt`, `Inv.swf`, `Inv.swdone`;
* Claims 4.24–4.25 (a hint used by `Exec` was put into use during the `Exec`): `I39`,
  `Inv.i39_frame`, `Inv.fresh`, `Inv.reset`;
* the two cases of the proof of Lemma 4.8: `Inv.exec_own` (lines 40–42).
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec} [NeZero n] {W : Writable T} {c c' : Cfg n T}

/-! ## Condition (C) along the transcript -/

lemma condC_concat {tr : List (Ev (Fin n) (Idx n) T)} {ev : Ev (Fin n) (Idx n) T}
    (h : CondC tr) (hne1 : ∀ q i o, ev ≠ .opinv q i o) (hne2 : ∀ p i v, ev ≠ .swinv p i v) :
    CondC (tr ++ [ev]) := by
  intro e t q o o' i het he ht hk
  rcases get_concat_iff.1 ht with ht | ⟨-, rfl⟩
  swap; · exact absurd rfl (hne1 q i o)
  have htl := lt_of_get ht
  have he' : tr[e]? = some (.einv q o') := by
    rcases get_concat_iff.1 he with he | ⟨he1, -⟩
    · exact he
    · omega
  obtain ⟨ts, h1, h2, h3, h4⟩ := h e t q o o' i het he' ht (fun k hk1 hk2 hk3 => by
    have := hk k (by simp; omega) hk2 hk3
    rwa [getElem_concat_lt hk1] at this)
  refine ⟨ts, h1, h2, by rw [ptrAt_concat_le (by omega)]; exact h3, fun a p v ha => ?_⟩
  rcases get_concat_iff.1 ha with ha | ⟨-, rfl⟩
  · rcases h4 a p v ha with ⟨b, r, e1, e2, e3⟩ | ⟨c, r, e1, e2, e3⟩
    · exact Or.inl ⟨b, r, e1, e2, get_concat_of e3⟩
    · exact Or.inr ⟨c, r, e1, e2, get_concat_of e3⟩
  · exact absurd rfl (hne2 p i v)

theorem Inv.condC_step (hI : Inv W c) (hs : Step W c c') : CondC c'.tr := by
  have h0 := hI.condC
  cases hs
  case swinv p v f hpc =>
    intro e t q o o' i het he ht hk
    rcases get_concat_iff.1 ht with ht | ⟨-, hev⟩
    swap; · simp at hev
    have htl := lt_of_get ht
    have he' : c.tr[e]? = some (.einv q o') := by
      rcases get_concat_iff.1 he with he | ⟨he1, -⟩
      · exact he
      · omega
    obtain ⟨ts, h1, h2, h3, h4⟩ := h0 e t q o o' i het he' ht (fun k hk1 hk2 hk3 => by
      have := hk k (by simp; omega) hk2 hk3
      rwa [getElem_concat_lt hk1] at this)
    refine ⟨ts, h1, h2, by rw [ptrAt_concat_le (by omega)]; exact h3, fun a p' v' ha => ?_⟩
    rcases get_concat_iff.1 ha with ha | ⟨ha1, hev⟩
    · rcases h4 a p' v' ha with ⟨b, r, e1, e2, e3⟩ | ⟨c', r, e1, e2, e3⟩
      · exact Or.inl ⟨b, r, e1, e2, get_concat_of e3⟩
      · exact Or.inr ⟨c', r, e1, e2, get_concat_of e3⟩
    · -- a new `A[f].SWrite`: the `Oper` on `A[i]` has returned (Lemma 4.8(b))
      simp only [Ev.swinv.injEq] at hev
      obtain ⟨rfl, rfl, rfl⟩ := hev
      rcases hI.opRet t q f o ht with ⟨c', r, e1, e2⟩ | ⟨x, ts', hq⟩
      · exact Or.inr ⟨c', r, e1, by rw [ha1]; exact lt_of_get e2, get_concat_of e2⟩
      · exfalso
        have hx := hI.exec q
        simp only [ExecInv, hq] at hx
        obtain ⟨π, hπ, -⟩ := hx.2.1.2.2.2.1
        obtain ⟨hf1, -, -⟩ := hI.chosen p f (by simp [hpc, curF])
        rw [hf1, hI.prePtr p f (by simp [hpc, curF]) (by simp [hpc, isPrePtr])] at hπ
        simp at hπ
  case opinv q o x i ts hpc =>
    intro e t q' o₁ o' i' het he ht hk
    rcases get_concat_iff.1 ht with ht | ⟨htl, hev⟩
    · have htl := lt_of_get ht
      have he' : c.tr[e]? = some (.einv q' o') := by
        rcases get_concat_iff.1 he with he | ⟨he1, -⟩
        · exact he
        · omega
      obtain ⟨ts, h1, h2, h3, h4⟩ := h0 e t q' o₁ o' i' het he' ht (fun k hk1 hk2 hk3 => by
        have := hk k (by simp; omega) hk2 hk3
        rwa [getElem_concat_lt hk1] at this)
      refine ⟨ts, h1, h2, by rw [ptrAt_concat_le (by omega)]; exact h3, fun a p v ha => ?_⟩
      rcases get_concat_iff.1 ha with ha | ⟨-, hev⟩
      · rcases h4 a p v ha with ⟨b, r, e1, e2, e3⟩ | ⟨c', r, e1, e2, e3⟩
        · exact Or.inl ⟨b, r, e1, e2, get_concat_of e3⟩
        · exact Or.inr ⟨c', r, e1, e2, get_concat_of e3⟩
      · simp at hev
    · -- the new `Oper` invocation of `q`: the point `ts` of Lemma 4.8
      simp only [Ev.opinv.injEq] at hev
      obtain ⟨rfl, rfl, rfl⟩ := hev
      have hx := hI.exec q
      simp only [ExecInv, hpc] at hx
      obtain ⟨⟨eq1, ⟨o2, ho2⟩, eq3⟩, -, ⟨c1, c2, c3, ⟨π, hπ, hπts⟩, -⟩⟩ := hx
      have he' : c.tr[e]? = some (.einv q o') := by
        rcases get_concat_iff.1 he with he | ⟨he1, -⟩
        · exact he
        · omega
      have hel := lt_of_get he'
      -- the invocation of this `Exec` is the last invocation of `q`
      have heq : e = (c.loc q).eq := by
        rcases lt_trichotomy e (c.loc q).eq with h1 | h1 | h1
        · exfalso
          obtain ⟨hl, hv⟩ := List.getElem?_eq_some_iff.1 ho2
          have := hk (c.loc q).eq (by simp; omega) h1 (by omega)
          rw [getElem_concat_lt hl, hv] at this
          exact this rfl
        · exact h1
        · exfalso
          obtain ⟨hl, hv⟩ := List.getElem?_eq_some_iff.1 he'
          have := eq3 e hl h1
          rw [hv] at this
          exact this rfl
      subst heq
      obtain ⟨-, -, hswf⟩ := hI.swf _ _ _ hπ
      refine ⟨ts, c1, by rw [htl]; exact c2, by rw [ptrAt_concat_le c2]; exact c3,
        fun a p v ha => ?_⟩
      rcases get_concat_iff.1 ha with ha | ⟨-, hev⟩
      · obtain ⟨b, r, e1, e2, e3⟩ := (hswf.mono hπts) a p v ha
        exact Or.inl ⟨b, r, e1, e2, get_concat_of e3⟩
      · simp at hev
  all_goals first
    | exact h0
    | exact condC_concat h0 (by simp) (by simp)

/-! ## The invariant holds in every reachable configuration -/

theorem Inv.step (hI : Inv W c) (hs : Step W c c') : Inv W c' where
  qok := hI.qok_step hs
  chosen := hI.chosen_step hs
  prePtr := hI.prePtr_step hs
  w21 := hI.w21_step hs
  ptrEq := hI.ptrEq_step hs
  sEq := hI.sEq_step hs
  tau35 := hI.tau35_step hs
  ptrProt := hI.ptrProt_step hs
  swf := hI.swf_step hs
  swdone := hI.swdone_step hs
  hint := hI.hint_step hs
  hint' := hI.hint'_step hs
  reset := hI.reset_step hs
  pairIn := hI.pairIn_step hs
  pairOut := hI.pairOut_step hs
  mono := hI.mono_step hs
  locRd := hI.locRd_step hs
  exec := fun q => by
    by_cases hq : c'.loc q = c.loc q
    · exact hI.exec_frame hs hq
    · exact hI.exec_own hs hq
  condC := hI.condC_step hs
  tmpl := hI.tmpl_step hs
  notInUse := hI.notInUse_step hs
  opRet := hI.opRet_step hs

lemma QOK.init (p : Fin n) : QOK p (QS.init p) where
  len _ := by simp [QS.init]
  cnt i := by simp [QS.init, occ, List.count_replicate]
  own o x hx := by simp [QS.init] at hx
  freeOwn x hx := by simpa [QS.init] using hx

theorem Inv.init : Inv W (Cfg.init : Cfg n T) where
  qok p := QOK.init p
  chosen p f h := by simp [Cfg.init, Loc.init, curF] at h
  prePtr p f h := by simp [Cfg.init, Loc.init, curF] at h
  w21 p _ _ _ _ _ _ h := by simp [Cfg.init, Loc.init] at h
  ptrEq := by simp [Cfg.init, ptrAt]
  sEq q := by simp [Cfg.init, Loc.init, Sval]
  tau35 q := by simp [Cfg.init, Loc.init]
  ptrProt i h := by simp [Cfg.init] at h
  swf p i π h := by simp [Cfg.init, Loc.init] at h
  swdone a p i v h := by simp [Cfg.init] at h
  hint p q h hh := by simp [Cfg.init] at hh
  hint' p q b hb := by simp [Cfg.init] at hb
  reset p q h hh := by simp [Cfg.init] at hh
  pairIn p q h := by simp [Cfg.init, Loc.init, isW1921] at h
  pairOut p q _ h b hh := by simp [Cfg.init] at hh
  mono p m14 h := by simp [Cfg.init, Loc.init, m14Of] at h
  locRd p := by
    refine ⟨fun _ _ h => ?_, fun _ h => ?_, fun _ h => ?_, fun _ _ _ _ _ _ h => ?_,
      fun _ _ _ h => ?_⟩ <;> simp [Cfg.init, Loc.init, smOf, oldsOf, olds'Of, s19Of] at h
  exec q := by simp [ExecInv, Cfg.init, Loc.init]
  condC e t q o o' i _ he := by simp [Cfg.init] at he
  tmpl := ⟨fun _ _ => .idle, fun p => ⟨rfl, fun t ht => by simp [Cfg.init] at ht,
    by simp [Cfg.init, Loc.init, absPC]⟩⟩
  notInUse t p f v h := by simp [Cfg.init] at h
  opRet t q i o h := by simp [Cfg.init] at h

theorem Inv.of_reachFrom {c₀ c : Cfg n T} (h0 : Inv W c₀) (h : ReachFrom W c₀ c) : Inv W c := by
  induction h with
  | refl => exact h0
  | step _ hs ih => exact ih.step hs

theorem Inv.of_reach {c : Cfg n T} (h : Reach W c) : Inv W c := Inv.init.of_reachFrom h

/-! ## Main results -/

/-- Lemma 4.8 of [AGW14] (thesis numbering), together with the template conditions of
Figure 4.4: in every execution of the algorithm of Figure 4.5 (from the depicted initial
configuration), the transcript follows the template of Figure 4.4 (every process runs the
template automaton; only the owner of `A[f]` invokes `A[f].SWrite`, and only while `A[f]` is
not in use) and satisfies condition (C) of Lemma 4.5: for every `Exec` that invokes
`A[i].Oper()` there is a point `t*` between the invocation of the `Exec` and that of the
`Oper()` with `Ptr = i` at `t*` such that no `A[i].SWrite()` overlaps `[t*, Oper()@rsp]`. -/
theorem lemma_4_8 (W : Writable T) (c : Cfg n T) (hc : Reach W c) :
    Template W owner c.tr ∧ CondC c.tr := by
  have hI := Inv.of_reach hc
  obtain ⟨σ, hσ⟩ := hI.tmpl
  exact ⟨⟨⟨σ, fun p => ⟨(hσ p).1, (hσ p).2.1⟩⟩, hI.notInUse⟩, hI.condC⟩

lemma ReachFrom.trans' {c₀ c₁ c : Cfg n T} (h₁ : ReachFrom W c₀ c₁) (h : ReachFrom W c₁ c) :
    ReachFrom W c₀ c := by
  induction h with
  | refl => exact h₁
  | step _ hs ih => exact .step ih hs

/-- Lemma 4.8 for the executions considered in the paper: the initial `Write(v0)` of process `0`
followed by an arbitrary sequence of steps. -/
theorem lemma_4_8_exec (W : Writable T) (v0 : T.State) (c : Cfg n T)
    (hc : IsExecution W v0 c) : Template W owner c.tr ∧ CondC c.tr := by
  obtain ⟨c₁, ⟨h₁, -⟩, h⟩ := hc
  exact lemma_4_8 W c (h₁.trans' h)

/-! ## Non-vacuity: the initial `Write(v0)` exists -/

/-- The solo initial `Write(v0)` of process `0` can be executed (so `IsExecution` is not
vacuous). -/
theorem exists_initialized (W : Writable T) (v0 : T.State) :
    ∃ c : Cfg n T, Initialized W v0 c := by
  let p0 : Fin n := ⟨0, Nat.pos_of_neZero n⟩
  let f : Idx n := (p0, ⟨0, by omega⟩)
  have hf : f ∈ ((Cfg.init : Cfg n T).loc p0).qs.free := by
    simp [Cfg.init, Loc.init, QS.init, f]
  refine ⟨_, ⟨ReachFrom.step (ReachFrom.step (ReachFrom.step (ReachFrom.step (ReachFrom.step
    (ReachFrom.step (ReachFrom.step (ReachFrom.step (ReachFrom.step (ReachFrom.step
    (ReachFrom.step (ReachFrom.step (ReachFrom.step (ReachFrom.step ReachFrom.refl
    (Step.winv _ p0 v0 (by simp [Cfg.init, Loc.init])))
    (Step.rec27 _ p0 v0 f (by simp) (by simpa using hf)))
    (Step.rec29 _ p0 v0 f (by simp)))
    (Step.rec31 _ p0 v0 f (by simp)))
    (Step.swinv _ p0 v0 f (by simp)))
    (Step.swret _ p0 v0 f (W.wresp v0) (by simp)))
    (Step.l14 _ p0 v0 f (by simp)))
    (Step.l15 _ p0 v0 f (-1) 0 (by
      simp [Cfg.init, Loc.init, Function.update_apply]; split_ifs <;> rfl)))
    (Step.l16w _ p0 v0 f (-1) 0 none (by simp [Cfg.init]) (Or.inl (by simp))))
    (Step.l18 _ p0 v0 f (-1) 0 none none (by simp [Cfg.init])))
    (Step.l19 _ p0 v0 f (by simp)))
    (Step.l20 _ p0 v0 f (-1) 0 3 (by
      simp [Cfg.init, Loc.init, Function.update_apply]; split_ifs <;> rfl)))
    (Step.l21 _ p0 v0 f (-1) 0 3 3 (by simp; rfl)))
    (Step.wret _ p0 v0 (by simp)), ?_, f, W.wresp v0, ?_⟩⟩
  · intro p
    by_cases hp : p = p0
    · subst hp; simp
    · simp [Function.update_of_ne hp, Cfg.init, Loc.init]
  · simp [Cfg.init, p0]

/-- After the initial `Write(v0)`, `Ptr ≠ ⊥` (so line 38 is always defined). -/
theorem ptr_ne_none (W : Writable T) (v0 : T.State) (c : Cfg n T) (hc : IsExecution W v0 c) :
    c.ptr ≠ none := by
  obtain ⟨c₁, ⟨h₁, -, f, r, htr⟩, h⟩ := hc
  have hI := Inv.of_reach (h₁.trans' h)
  have hpre : ∃ t, c.tr = c₁.tr ++ t := by
    clear h₁ hI
    induction h with
    | refl => exact ⟨[], by simp⟩
    | step _ hs ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht'⟩ := Inv.tr_ext hs
      exact ⟨t ++ t', by rw [ht', ht, List.append_assoc]⟩
  obtain ⟨t, ht⟩ := hpre
  rw [hI.ptrEq, ht, htr]
  unfold ptrAt
  rw [List.take_length, List.filterMap_append]
  simp [Ev.ptrVal]

end Podc.WritableObjects.WF

namespace Podc.WritableObjects.WF

/-- Claims 4.15(b) and 4.16 are false as literally stated: in one call of `recycle()` the
dequeue of `usedQ` (line 26) can add `i` to `free_p` at the same point at which `i` is read from
`Annc[ctr]` and enqueued into `anncQ` (lines 27–28). Here `n = 1`, `p = 0`, the only copy of
`i = (0,0)` is at the head of `usedQ`, and `Annc[ctr] = i`; after the step, `i` is both in
`anncQ` and in `free_p`. -/
example :
    let i : Idx 1 := (0, 0)
    let j : Idx 1 := (0, 1)
    let s : QS 1 := ⟨fun o => if o = 0 then [some i, none, none, none] else [none, none, none, none],
      fun k => if k = i then 1 else 0, {j}⟩
    let s' := upd 0 1 (some i) (upd 0 0 (some j) { s with free := s.free.erase j })
    some i ∈ s'.q 1 ∧ i ∈ s'.free := by
  decide

end Podc.WritableObjects.WF
