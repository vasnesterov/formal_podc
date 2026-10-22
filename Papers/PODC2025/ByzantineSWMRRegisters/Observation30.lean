import Papers.PODC2025.ByzantineSWMRRegisters.Objects
import Podc.Computability.Distributed.SharedMemory.Byzantine.Restrict
import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# Observation 30 of Hu–Toueg (PODC 2025): test-or-set from a signature-like object

For any object `R` with a `SigTest` structure (verifiable, authenticated or sticky register), the
one-shot test-or-set object (setter `s`) has a simple wait-free implementation from a single atomic
copy of `R`, which is correct (Byzantine linearizable and terminating) against any number of
Byzantine processes (who may apply to `R` every operation they are allowed to):

* `Set`: apply the set operations `T.setOps` in order, then return `done`;
* `Test`: apply `T.testOp` and return `1` iff the response is positive.

Linearization points: the `Set` is linearized at the first step after which the state of `R`
satisfies `T.R m` (`m = T.setOps.length`); this step is an access of the correct setter, or a
`byz` step of a Byzantine setter, in which case a `Set` operation of the setter is inserted into
the history `h'` of Definition 7. A `Test` is linearized at its access.
-/

namespace Podc.ByzantineSWMRRegisters

open Cslib.SharedMemory Cslib.SharedMemory.Byzantine

/-- Local states of the test-or-set implementation. -/
inductive TosLoc where
  | idle
  | setting (k : ℕ)
  | testing
  | answer (b : Bool)
  deriving DecidableEq

noncomputable section

open Classical

variable {P : Type} [DecidableEq P] {R : ObjSpec} {allowedR : P → R.Op → Prop} {s : P}

/-- The implementation of test-or-set (setter `s`) from one atomic object `R` with a `SigTest`
structure `T` (Observation 30). -/
def tosImpl (T : SigTest R allowedR s) : Impl testOrSet (fun _ : Unit => R) P TosLoc where
  memInit _ := R.init
  locInit _ := .idle
  invoke _ _ o := match o with
    | .set => .setting 0
    | .test => .testing
  act p l := match l with
    | .idle => .ret .done .idle
    | .setting k =>
      if h : p = s ∧ k < T.setOps.length then
        .access () (T.setOps[k]'h.2) (fun _ => .setting (k + 1))
      else .ret .done .idle
    | .testing =>
      if p ≠ s then .access () T.testOp (fun r => .answer (decide (T.pos r)))
      else .ret .done .idle
    | .answer b => .ret (.bit b) .idle
  allowed := tosAllowed s

/-- Access rights to the atomic object `R`: those of its specification. -/
def accR (allowedR : P → R.Op → Prop) : Access P (fun _ : Unit => R) := fun p _ o => allowedR p o

lemma tosImpl_respects (T : SigTest R allowedR s) : (tosImpl T).RespectsAccess (accR allowedR) := by
  intro p l i o k h
  cases l with
  | idle => simp [tosImpl] at h
  | setting j =>
    simp only [tosImpl] at h
    split_ifs at h with hj
    · cases h; obtain ⟨rfl, hj⟩ := hj
      exact T.allowed_set _ (List.getElem_mem _)
  | testing =>
    simp only [tosImpl] at h
    split_ifs at h with hp
    · cases h; exact T.allowed_test _ hp
  | answer b => simp [tosImpl] at h

lemma tos_runOps (q : Bool) (os : List TosOp) :
    testOrSet.runOps q os = (q || decide (TosOp.set ∈ os)) := by
  induction os generalizing q with
  | nil => rw [ObjSpec.runOps_nil]; simp
  | cons o os ih =>
    rw [ObjSpec.runOps_cons, ih]
    cases o <;> simp [testOrSet]

/-! ## Termination (wait-freedom) -/

/-- A measure on local states that decreases with every step of a pending process. -/
def tosMeasure (m : ℕ) : TosLoc → ℕ
  | .idle => 0
  | .setting j => m - j + 1
  | .testing => 2
  | .answer _ => 1

variable (T : SigTest R allowedR s)

lemma tos_step_progress {C C' : Config testOrSet (fun _ : Unit => R) P TosLoc}
    {e : Event P testOrSet (fun _ : Unit => R)} {p : P} (he : e.IsStepOf p)
    (h : (tosImpl T).bstep (accR allowedR) C e = some C') (hp : C.pend p ≠ none) :
    C'.pend p = none ∨ (C'.pend p ≠ none ∧
      tosMeasure T.setOps.length (C'.loc p) < tosMeasure T.setOps.length (C.loc p)) := by
  cases e with
  | inv q o => exact absurd he (by simp [Event.IsStepOf])
  | byz q i o => exact absurd he (by simp [Event.IsStepOf])
  | ret q r =>
    simp only [Event.IsStepOf] at he; subst he
    simp only [Impl.bstep] at h
    split_ifs at h
    split at h
    · simp at h
    · split_ifs at h; cases h; left; simp
  | tau q =>
    simp only [Event.IsStepOf] at he; subst he
    simp only [Impl.bstep] at h
    split at h
    · rename_i i o k hact
      cases h
      right
      refine ⟨by simpa using hp, ?_⟩
      simp only [Function.update_self]
      cases hl : C.loc q with
      | idle => simp [tosImpl, hl] at hact
      | setting j =>
        simp only [tosImpl, hl] at hact
        split_ifs at hact with hj
        cases hact
        simp [tosMeasure]; omega
      | testing =>
        simp only [tosImpl, hl] at hact
        split_ifs at hact with hj
        cases hact
        simp [tosMeasure]
      | answer b => simp [tosImpl, hl] at hact
    · split_ifs at h with h1
      exact absurd h1 hp

/-- Every operation of a correct process completes in every fair execution (the implementation
is wait-free). -/
theorem tos_termination {f : ℕ} {Bz : Finset P} (_ : Bz.card ≤ f)
    (ev : ℕ → Event P testOrSet (fun _ : Unit => R))
    (hval : ∀ k, (tosImpl T).BExec (accR allowedR) Bz (pre ev k)) (hfair : Fair Bz ev)
    (p : P) (hp : p ∉ Bz) (k : ℕ) :
    ∃ m ≥ k, ∀ C, (tosImpl T).brun (accR allowedR) (pre ev m) = some C → C.pend p = none := by
  set I := tosImpl T
  let cfg : ℕ → Config testOrSet (fun _ : Unit => R) P TosLoc :=
    fun k => Classical.choose (hval k).1
  have hcfg : ∀ k, I.brun (accR allowedR) (pre ev k) = some (cfg k) :=
    fun k => Classical.choose_spec (hval k).1
  have hstep : ∀ k, I.bstep (accR allowedR) (cfg k) (ev k) = some (cfg (k + 1)) := by
    intro k
    have := hcfg (k + 1)
    rw [Impl.pre_succ, Impl.brun] at this
    obtain ⟨C', h1, h2⟩ := I.brunFrom_append_eq_some _ this
    rw [← Impl.brun, hcfg k] at h1
    cases h1
    rwa [Impl.brunFrom_singleton] at h2
  have hresp : ∀ k, (ev k).Respects Bz := fun k =>
    (hval (k + 1)).2 _ (by simp only [pre, List.mem_map, List.mem_range]; exact ⟨k, by omega, rfl⟩)
  -- events other than steps of `p` do not change `p` while it is pending
  have hother : ∀ i, ¬ (ev i).IsStepOf p → (cfg i).pend p ≠ none →
      (cfg (i + 1)).pend p = (cfg i).pend p ∧ (cfg (i + 1)).loc p = (cfg i).loc p := by
    intro i hns hpend
    by_cases hpr : (ev i).proc = p
    · exfalso
      have h1 := hstep i
      have h2 := hresp i
      cases hev : ev i with
      | inv q o =>
        rw [hev] at h1 hpr; simp only [Event.proc] at hpr; subst hpr
        simp only [Impl.bstep] at h1; split_ifs at h1 with h3; exact hpend h3.1
      | ret q r => rw [hev] at hns hpr; simp [Event.IsStepOf, Event.proc] at hns hpr; exact hns hpr
      | tau q => rw [hev] at hns hpr; simp [Event.IsStepOf, Event.proc] at hns hpr; exact hns hpr
      | byz q i o =>
        rw [hev] at h2 hpr; simp only [Event.Respects] at h2; simp only [Event.proc] at hpr
        exact hp (hpr ▸ h2)
    · exact I.bstep_pend_ne _ (hstep i) hpr
  suffices H : ∀ n, ∀ k, tosMeasure T.setOps.length ((cfg k).loc p) ≤ n →
      ∃ m ≥ k, (cfg m).pend p = none by
    obtain ⟨m, hm, h⟩ := H _ k le_rfl
    exact ⟨m, hm, fun C hC => by rw [hcfg m] at hC; cases hC; exact h⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k hk
  by_cases hpk : (cfg k).pend p = none
  · exact ⟨k, le_rfl, hpk⟩
  have hex : ∃ j, k ≤ j ∧ (ev j).IsStepOf p := hfair p hp k
  let j := Nat.find hex
  have hj : k ≤ j ∧ (ev j).IsStepOf p := Nat.find_spec hex
  have hmin : ∀ i, k ≤ i → i < j → ¬ (ev i).IsStepOf p := fun i hi hij hs =>
    Nat.find_min hex hij ⟨hi, hs⟩
  -- `p` is unchanged between `k` and `j`
  have hsame : ∀ i, k ≤ i → i ≤ j →
      (cfg i).pend p = (cfg k).pend p ∧ (cfg i).loc p = (cfg k).loc p := by
    intro i hi hij
    induction i, hi using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ i hki ih' =>
      obtain ⟨h1, h2⟩ := ih' (by omega)
      obtain ⟨h3, h4⟩ := hother i (hmin i hki (by omega)) (by rw [h1]; exact hpk)
      exact ⟨h3.trans h1, h4.trans h2⟩
  obtain ⟨hpj, hlj⟩ := hsame j hj.1 le_rfl
  rcases tos_step_progress T hj.2 (hstep j) (by rw [hpj]; exact hpk) with h | ⟨-, hlt⟩
  · exact ⟨j + 1, by omega, h⟩
  · rw [hlj] at hlt
    obtain ⟨m, hm, h⟩ := ih _ (lt_of_lt_of_le hlt hk) (j + 1) le_rfl
    exact ⟨m, by omega, h⟩

/-! ## Byzantine linearizability: the invariant -/

/-- The invariant relating a configuration `C` reached by an execution with history `h`, the
history `h'` of Definition 7 and its linearization `L`. -/
structure TosInv (Bz : Finset P) (C : Config testOrSet (fun _ : Unit => R) P TosLoc)
    (h h' : List (Label P testOrSet)) (L : List (OpId P × testOrSet.Op)) : Prop where
  lin : IsLinearization h' L
  wf : WellFormed h'
  allow : ∀ p o, Label.inv p o ∈ h' → tosAllowed s p o
  filt : h'.filter (fun ℓ => ℓ.proc ∉ Bz) = h.filter (fun ℓ => ℓ.proc ∉ Bz)
  setL : ((s, 0), TosOp.set) ∈ L ↔ T.R T.setOps.length (C.mem ())
  onlySet : ∀ y ∈ L, y.2 = TosOp.set → y.1 = (s, 0)
  byzS : s ∈ Bz → ¬ T.R T.setOps.length (C.mem ()) → opsOf h' s = [] ∧ respsOf h' s = []
  idle : ∀ p ∉ Bz, C.pend p = none ↔ C.loc p = .idle
  setting : ∀ p ∉ Bz, ∀ k, C.loc p = .setting k → p = s ∧ k ≤ T.setOps.length ∧
    T.R k (C.mem ()) ∧ opOf h' (s, 0) = some TosOp.set ∧ respsOf h' s = []
  testing : ∀ p ∉ Bz, C.loc p = .testing → p ≠ s ∧ (p, 0) ∉ L.map Prod.fst ∧
    opOf h' (p, 0) = some TosOp.test ∧ respsOf h' p = []
  answer : ∀ p ∉ Bz, ∀ b, C.loc p = .answer b → p ≠ s ∧ respsOf h' p = [] ∧
    ∃ L₁ L₂, L = L₁ ++ ((p, 0), TosOp.test) :: L₂ ∧
      (testOrSet.δ (testOrSet.runOps testOrSet.init (L₁.map Prod.snd)) TosOp.test).2 = .bit b

lemma tosInv_init (Bz : Finset P) :
    TosInv T Bz (tosImpl T).initCfg [] [] [] where
  lin := ⟨by simp, by simp, fun a ha => by simp [Completed] at ha, fun a b h hb => by simp at hb,
    trivial⟩
  wf := fun β ℓ γ h => by simp at h
  allow := by simp
  filt := rfl
  setL := by simpa [Impl.initCfg, tosImpl] using T.not_R_init
  onlySet := by simp
  byzS := by simp
  idle := by simp [Impl.initCfg, tosImpl]
  setting := by simp [Impl.initCfg, tosImpl]
  testing := by simp [Impl.initCfg, tosImpl]
  answer := by simp [Impl.initCfg, tosImpl]

/-- The response of a test at the end of a sequential history. -/
lemma tos_test_resp (L : List (OpId P × testOrSet.Op)) :
    (testOrSet.δ (testOrSet.runOps testOrSet.init (L.map Prod.snd)) TosOp.test).2 =
      .bit (decide (TosOp.set ∈ L.map Prod.snd)) := by
  rw [tos_runOps]; simp [testOrSet]

variable {T}

lemma TosInv.set_mem_iff {Bz : Finset P} {C : Config testOrSet (fun _ : Unit => R) P TosLoc}
    {h h' : List (Label P testOrSet)} {L : List (OpId P × testOrSet.Op)}
    (hI : TosInv T Bz C h h' L) :
    TosOp.set ∈ L.map Prod.snd ↔ T.R T.setOps.length (C.mem ()) := by
  rw [← hI.setL]
  constructor
  · intro hm
    obtain ⟨y, hy, hy2⟩ := List.mem_map.1 hm
    have := hI.onlySet y hy hy2
    obtain ⟨y1, y2⟩ := y
    simp only at this hy2; subst this hy2; exact hy
  · intro hm; exact List.mem_map.2 ⟨_, hm, rfl⟩

section Steps

variable {Bz : Finset P} {C D : Config testOrSet (fun _ : Unit => R) P TosLoc}
  {h h' : List (Label P testOrSet)} {L : List (OpId P × testOrSet.Op)}

/-- Invocation step. -/
lemma TosInv.step_inv (hI : TosInv T Bz D h h' L)
    (hc : ∀ q, (opsOf h q).length = (respsOf h q).length + if D.pend q = none then 0 else 1)
    {p : P} {o : testOrSet.Op} (hp : p ∉ Bz)
    (hone : (opsOf (h ++ [.inv p o]) p).length ≤ 1)
    (he : (tosImpl T).bstep (accR allowedR) D (.inv p o) = some C) :
    ∃ h'' L', TosInv T Bz C (h ++ [.inv p o]) h'' L' := by
  simp only [Impl.bstep] at he
  split_ifs at he with hen
  cases he
  obtain ⟨hpend, hall⟩ := hen
  change tosAllowed s p o at hall
  have hops0 : opsOf h p = [] := by
    rw [opsOf_append, List.length_append] at hone
    have : (opsOf [Label.inv p o] p).length = 1 := by simp
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hresp0 : respsOf h p = [] := by
    have := hc p; rw [if_pos hpend, hops0] at this
    exact List.eq_nil_of_length_eq_zero (by simp at this; omega)
  have hops' : opsOf h' p = [] := by rw [opsOf_eq_of_filter_eq hI.filt hp, hops0]
  have hresp' : respsOf h' p = [] := by rw [respsOf_eq_of_filter_eq hI.filt hp, hresp0]
  have hnotL : (p, 0) ∉ L.map Prod.fst := fun hm => by
    have := hI.lin.mem_invoked hm; simp [Invoked, hops'] at this
  have hopOf_old : ∀ x, (opOf h' x).isSome → opOf (h' ++ [.inv p o]) x = opOf h' x := by
    intro x hx
    apply opOf_append_of_invoked
    simp only [opOf, Option.isSome_iff_exists, List.getElem?_eq_some_iff] at hx
    obtain ⟨_, hx, -⟩ := hx; exact hx
  refine ⟨h' ++ [.inv p o], L, ?_⟩
  refine
    { lin := hI.lin.append_inv p o
      wf := hI.wf.append_inv (by rw [hops', hresp']; rfl)
      allow := fun q o' hq => ?_
      filt := by rw [List.filter_append, List.filter_append, hI.filt]
      setL := hI.setL
      onlySet := hI.onlySet
      byzS := fun hs hQ => ?_
      idle := fun q hq => ?_
      setting := fun q hq k hk => ?_
      testing := fun q hq hk => ?_
      answer := fun q hq b hk => ?_ }
  · rcases List.mem_append.1 hq with hq | hq
    · exact hI.allow q o' hq
    · simp at hq; obtain ⟨rfl, rfl⟩ := hq; exact hall
  · have hps : p ≠ s := fun h => hp (h ▸ hs)
    obtain ⟨h1, h2⟩ := hI.byzS hs hQ
    simp [h1, h2, hps]
  · by_cases hqp : q = p
    · subst hqp; cases o <;> simp [tosImpl]
    · simpa [Function.update_of_ne hqp] using hI.idle q hq
  · by_cases hqp : q = p
    · subst hqp
      cases o with
      | test => simp [tosImpl] at hk
      | set =>
        simp [tosImpl] at hk; subst hk
        change q = s at hall; subst hall
        refine ⟨rfl, Nat.zero_le _, T.R_zero _, ?_, by simpa using hresp'⟩
        simp [opOf, hops']
    · simp only [Function.update_of_ne hqp] at hk
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI.setting q hq k hk
      refine ⟨h1, h2, h3, by rw [hopOf_old _ (by simp [h4])]; exact h4, ?_⟩
      have : s ≠ p := fun h => hqp (h1.trans h)
      simp [h5, this]
  · by_cases hqp : q = p
    · subst hqp
      cases o with
      | set => simp [tosImpl] at hk
      | test =>
        change q ≠ s at hall
        refine ⟨hall, hnotL, by simp [opOf, hops'], by simpa using hresp'⟩
    · simp only [Function.update_of_ne hqp] at hk
      obtain ⟨h1, h2, h3, h4⟩ := hI.testing q hq hk
      exact ⟨h1, h2, by rw [hopOf_old _ (by simp [h3])]; exact h3, by simp [h4]⟩
  · by_cases hqp : q = p
    · subst hqp; cases o <;> simp [tosImpl] at hk
    · simp only [Function.update_of_ne hqp] at hk
      obtain ⟨h1, h2, h3⟩ := hI.answer q hq b hk
      exact ⟨h1, by simp [h2], h3⟩

/-- Response step. -/
lemma TosInv.step_ret (hI : TosInv T Bz D h h' L) {p : P} {r : testOrSet.Resp} (hp : p ∉ Bz)
    (hone : (opsOf h p).length ≤ 1)
    (he : (tosImpl T).bstep (accR allowedR) D (.ret p r) = some C) :
    ∃ h'' L', TosInv T Bz C (h ++ [.ret p r]) h'' L' := by
  simp only [Impl.bstep] at he
  split_ifs at he with hpend
  split at he
  · simp at he
  rename_i r' l hact
  split_ifs at he with hr
  subst hr
  cases he
  have hloc : D.loc p ≠ .idle := fun h => hpend ((hI.idle p hp).2 h)
  obtain ⟨L₁, L₂, o, hsplit, hresp, hres, hl⟩ : ∃ L₁ L₂ o, L = L₁ ++ ((p, 0), o) :: L₂ ∧
      (testOrSet.δ (testOrSet.runOps testOrSet.init (L₁.map Prod.snd)) o).2 = r ∧
      respsOf h' p = [] ∧ l = .idle := by
    cases hl : D.loc p with
    | idle => exact absurd hl hloc
    | setting k =>
      rw [hl] at hact
      obtain ⟨rfl, hk, hR, -, hres⟩ := hI.setting p hp k hl
      simp only [tosImpl] at hact
      split_ifs at hact with hk'
      cases hact
      have hkm : k = T.setOps.length := by
        by_contra hne; exact hk' ⟨by trivial, by omega⟩
      subst hkm
      obtain ⟨L₁, L₂, hL⟩ := List.append_of_mem (hI.setL.2 hR)
      exact ⟨L₁, L₂, _, hL, by simp [testOrSet], hres, rfl⟩
    | testing =>
      rw [hl] at hact
      obtain ⟨hps, -⟩ := hI.testing p hp hl
      simp [tosImpl, hps] at hact
    | answer b =>
      rw [hl] at hact
      obtain ⟨-, hres, L₁, L₂, hL, hb⟩ := hI.answer p hp b hl
      simp only [tosImpl] at hact
      cases hact
      exact ⟨L₁, L₂, _, hL, hb, hres, rfl⟩
  subst hl
  have hops : (opsOf h' p).length = 1 := by
    have h1 := hI.lin.op_eq ((p, 0), o) (by rw [hsplit]; simp)
    have h2 : 0 < (opsOf h' p).length := by
      simp only [opOf, List.getElem?_eq_some_iff] at h1; exact h1.1
    rw [opsOf_eq_of_filter_eq hI.filt hp] at h2 ⊢; omega
  have hres_old : ∀ q, q ≠ p → respsOf (h' ++ [.ret p r]) q = respsOf h' q := by
    intro q hq; simp [Ne.symm hq]
  have hop_old : ∀ x, opOf (h' ++ [.ret p r]) x = opOf h' x := by
    intro x; simp [opOf]
  refine ⟨h' ++ [.ret p r], L, ?_⟩
  refine
    { lin := hI.lin.append_ret L₁ L₂ o (by rw [hres]; exact hsplit) hresp
      wf := hI.wf.append_ret (by rw [hops, hres]; rfl)
      allow := fun q o' hq => ?_
      filt := by rw [List.filter_append, List.filter_append, hI.filt]
      setL := hI.setL
      onlySet := hI.onlySet
      byzS := fun hs hQ => ?_
      idle := fun q hq => ?_
      setting := fun q hq k hk => ?_
      testing := fun q hq hk => ?_
      answer := fun q hq b hk => ?_ }
  · rcases List.mem_append.1 hq with hq | hq
    · exact hI.allow q o' hq
    · simp at hq
  · have hps : s ≠ p := fun h => hp (h ▸ hs)
    obtain ⟨h1, h2⟩ := hI.byzS hs hQ
    exact ⟨by simp [h1], by rw [hres_old s hps, h2]⟩
  · by_cases hqp : q = p
    · subst hqp; simp
    · simpa [Function.update_of_ne hqp] using hI.idle q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hk
    · simp only [Function.update_of_ne hqp] at hk
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI.setting q hq k hk
      refine ⟨h1, h2, h3, by rw [hop_old]; exact h4, ?_⟩
      rw [hres_old s (fun h => hqp (h1.trans h)), h5]
  · by_cases hqp : q = p
    · subst hqp; simp at hk
    · simp only [Function.update_of_ne hqp] at hk
      obtain ⟨h1, h2, h3, h4⟩ := hI.testing q hq hk
      exact ⟨h1, h2, by rw [hop_old]; exact h3, by rw [hres_old q hqp, h4]⟩
  · by_cases hqp : q = p
    · subst hqp; simp at hk
    · simp only [Function.update_of_ne hqp] at hk
      obtain ⟨h1, h2, h3⟩ := hI.answer q hq b hk
      exact ⟨h1, by rw [hres_old q hqp, h2], h3⟩

/-- Algorithm step (base-object access or stutter). -/
lemma TosInv.step_tau (hI : TosInv T Bz D h h' L) {p : P} (hp : p ∉ Bz)
    (he : (tosImpl T).bstep (accR allowedR) D (.tau p) = some C) :
    ∃ L', TosInv T Bz C h h' L' := by
  simp only [Impl.bstep] at he
  split at he
  swap
  · split_ifs at he; cases he; exact ⟨L, hI⟩
  rename_i i o k hact
  cases he
  have hloc_ne : D.loc p ≠ .idle := fun hl => by simp [hl, tosImpl] at hact
  have hpend : D.pend p ≠ none := fun h => hloc_ne ((hI.idle p hp).1 h)
  cases hl : D.loc p with
  | idle => exact absurd hl hloc_ne
  | answer b => rw [hl] at hact; simp [tosImpl] at hact
  | setting j =>
    rw [hl] at hact
    simp only [tosImpl] at hact
    split_ifs at hact with hj
    cases hact
    obtain ⟨rfl, hjm⟩ := hj
    obtain ⟨-, -, hRj, hop, hres⟩ := hI.setting _ hp j hl
    set q := D.mem ()
    set q' := (R.δ q (T.setOps[j]'hjm)).1 with hq'
    have hRj' : T.R (j + 1) q' := T.R_succ j hjm q hRj
    obtain ⟨L', hlin, hsetL, hmemL, E, hext⟩ : ∃ L', IsLinearization h' L' ∧
        (((p, 0), TosOp.set) ∈ L' ↔ T.R T.setOps.length q') ∧
        (∀ y ∈ L', y ∈ L ∨ y = ((p, 0), TosOp.set)) ∧ ∃ E, L' = L ++ E := by
      by_cases hsw : ¬ T.R T.setOps.length q ∧ T.R T.setOps.length q'
      · have hnot : (p, 0) ∉ L.map Prod.fst := by
          intro hm
          obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hm
          have h1 := hI.lin.op_eq y hy
          rw [hy1, hop] at h1
          obtain ⟨y1, y2⟩ := y
          simp only at hy1 h1; subst hy1; cases h1
          exact hsw.1 (hI.setL.1 hy)
        have hnc : ¬ Completed h' (p, 0) := by simp [Completed, hres]
        exact ⟨_, hI.lin.push hop hnot hnc, by simp [hsw.2], by simp, _, rfl⟩
      · refine ⟨L, hI.lin, ?_, fun y hy => Or.inl hy, [], by simp⟩
        rw [hI.setL]
        constructor
        · exact fun hQ => T.R_stable _ _ _ hQ
        · intro hQ'; by_contra hQ; exact hsw ⟨hQ, hQ'⟩
    refine ⟨L', ?_⟩
    have hmemC : (Function.update D.mem () q') () = q' := by simp
    refine
      { lin := hlin
        wf := hI.wf
        allow := hI.allow
        filt := hI.filt
        setL := by simpa using hsetL
        onlySet := fun y hy hy2 => ?_
        byzS := fun hs => absurd hs hp
        idle := fun r hr => ?_
        setting := fun r hr k hk => ?_
        testing := fun r hr hk => ?_
        answer := fun r hr b hk => ?_ }
    · rcases hmemL y hy with hy | rfl
      · exact hI.onlySet y hy hy2
      · rfl
    · by_cases hrp : r = p
      · subst hrp; simp [hpend]
      · simpa [Function.update_of_ne hrp] using hI.idle r hr
    · by_cases hrp : r = p
      · subst hrp; simp at hk; subst hk
        exact ⟨rfl, by omega, by simpa using hRj', hop, hres⟩
      · simp only [Function.update_of_ne hrp] at hk
        exact absurd (hI.setting r hr k hk).1 hrp
    · by_cases hrp : r = p
      · subst hrp; simp at hk
      · simp only [Function.update_of_ne hrp] at hk
        obtain ⟨h1, h2, h3, h4⟩ := hI.testing r hr hk
        refine ⟨h1, fun hm => ?_, h3, h4⟩
        obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hm
        rcases hmemL y hy with hy | rfl
        · exact h2 (List.mem_map.2 ⟨y, hy, hy1⟩)
        · simp at hy1; exact hrp hy1.symm
    · by_cases hrp : r = p
      · subst hrp; simp at hk
      · simp only [Function.update_of_ne hrp] at hk
        obtain ⟨h1, h2, L₁, L₂, hL, hb⟩ := hI.answer r hr b hk
        exact ⟨h1, h2, L₁, L₂ ++ E, by rw [hext, hL]; simp, hb⟩
  | testing =>
    rw [hl] at hact
    simp only [tosImpl] at hact
    split_ifs at hact with hps
    cases hact
    obtain ⟨-, hnot, hop, hres⟩ := hI.testing _ hp hl
    set q := D.mem ()
    set q' := (R.δ q T.testOp).1 with hq'
    have hQiff : T.R T.setOps.length q' ↔ T.R T.setOps.length q := by
      constructor
      · intro hQ'; by_contra hQ
        exact hps (T.only_setter q T.testOp p hQ hQ' (T.allowed_test p hps))
      · exact fun hQ => T.R_stable _ _ _ hQ
    have hnc : ¬ Completed h' (p, 0) := by simp [Completed, hres]
    refine ⟨L ++ [((p, 0), TosOp.test)], ?_⟩
    have hmemC : (Function.update D.mem () q') () = q' := by simp
    refine
      { lin := hI.lin.push hop hnot hnc
        wf := hI.wf
        allow := hI.allow
        filt := hI.filt
        setL := ?_
        onlySet := fun y hy hy2 => ?_
        byzS := fun hs hQ => hI.byzS hs (fun h => hQ (by simpa using hQiff.2 h))
        idle := fun r hr => ?_
        setting := fun r hr k hk => ?_
        testing := fun r hr hk => ?_
        answer := fun r hr b hk => ?_ }
    · simp only [hmemC, hQiff, ← hI.setL, List.mem_append, List.mem_singleton]
      simp
      exact hI.setL
    · rcases List.mem_append.1 hy with hy | hy
      · exact hI.onlySet y hy hy2
      · simp at hy; subst hy; simp at hy2
    · by_cases hrp : r = p
      · subst hrp; simp [hpend]
      · simpa [Function.update_of_ne hrp] using hI.idle r hr
    · by_cases hrp : r = p
      · subst hrp; simp at hk
      · simp only [Function.update_of_ne hrp] at hk
        obtain ⟨h1, h2, h3, h4, h5⟩ := hI.setting r hr k hk
        exact ⟨h1, h2, by simpa using T.R_stable k q _ h3, h4, h5⟩
    · by_cases hrp : r = p
      · subst hrp; simp at hk
      · simp only [Function.update_of_ne hrp] at hk
        obtain ⟨h1, h2, h3, h4⟩ := hI.testing r hr hk
        refine ⟨h1, ?_, h3, h4⟩
        simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
          List.mem_singleton, not_or]
        exact ⟨h2, by simp [hrp]⟩
    · by_cases hrp : r = p
      · subst hrp
        simp only [Function.update_self, TosLoc.answer.injEq] at hk
        refine ⟨hps, hres, L, [], by simp, ?_⟩
        rw [tos_test_resp, ← hk]
        congr 1
        simp only [decide_eq_decide]
        rw [hI.set_mem_iff, T.pos_iff]
      · simp only [Function.update_of_ne hrp] at hk
        obtain ⟨h1, h2, L₁, L₂, hL, hb⟩ := hI.answer r hr b hk
        exact ⟨h1, h2, L₁, L₂ ++ [((p, 0), TosOp.test)], by rw [hL]; simp, hb⟩

/-- Byzantine step. -/
lemma TosInv.step_byz (hI : TosInv T Bz D h h' L) {p : P} {i : Unit} {o : R.Op} (hp : p ∈ Bz)
    (he : (tosImpl T).bstep (accR allowedR) D (.byz p i o) = some C) :
    ∃ h'' L', TosInv T Bz C h h'' L' := by
  obtain ⟨hacc, rfl⟩ := Impl.bstep_byz_eq _ _ he
  cases i
  change allowedR p o at hacc
  set q := D.mem ()
  set q' := (R.δ q o).1 with hq'
  have hmemC : (Function.update D.mem () q') () = q' := by simp
  by_cases hsw : ¬ T.R T.setOps.length q ∧ T.R T.setOps.length q'
  · have hps : p = s := T.only_setter q o p hsw.1 hsw.2 hacc
    subst hps
    obtain ⟨hops, hres⟩ := hI.byzS hp hsw.1
    have hop : opOf (h' ++ [.inv p TosOp.set]) (p, 0) = some TosOp.set := by simp [opOf, hops]
    have hnot : (p, 0) ∉ L.map Prod.fst := by
      intro hm
      obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hm
      have h1 := hI.lin.op_eq y hy
      rw [hy1] at h1; simp [opOf, hops] at h1
    have hres1 : respsOf (h' ++ [.inv p TosOp.set]) p = [] := by simp [hres]
    have hnc : ¬ Completed (h' ++ [.inv p TosOp.set]) (p, 0) := by simp [Completed, hres1]
    have hlin := ((hI.lin.append_inv p TosOp.set).push hop hnot hnc).append_ret (r := TosResp.done)
      L [] TosOp.set (by rw [hres1]; rfl) (by simp [testOrSet])
    have hwf := (hI.wf.append_inv (p := p) (o := TosOp.set) (by rw [hops, hres]; rfl)).append_ret
      (p := p) (r := TosResp.done) (by simp [hops, hres])
    have hother : ∀ r, r ≠ p → opsOf (h' ++ [.inv p TosOp.set] ++ [.ret p TosResp.done]) r =
        opsOf h' r ∧ respsOf (h' ++ [.inv p TosOp.set] ++ [.ret p TosResp.done]) r =
        respsOf h' r := by
      intro r hr; simp [Ne.symm hr]
    refine ⟨h' ++ [.inv p TosOp.set] ++ [.ret p TosResp.done], L ++ [((p, 0), TosOp.set)], ?_⟩
    refine
      { lin := hlin
        wf := hwf
        allow := fun r o' hr => ?_
        filt := ?_
        setL := by simp [hsw.2]
        onlySet := fun y hy hy2 => ?_
        byzS := fun _ hQ => absurd (by simpa using hsw.2) hQ
        idle := fun r hr => hI.idle r hr
        setting := fun r hr k hk => absurd ((hI.setting r hr k hk).1 ▸ hp) hr
        testing := fun r hr hk => ?_
        answer := fun r hr b hk => ?_ }
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with (hr | hr) | hr
      · exact hI.allow r o' hr
      · cases hr; rfl
      · cases hr
    · rw [List.filter_append, List.filter_append, hI.filt]; simp [hp, Label.proc]
    · rcases List.mem_append.1 hy with hy | hy
      · exact hI.onlySet y hy hy2
      · simp at hy; subst hy; rfl
    · have hrp : r ≠ p := fun h => hr (h ▸ hp)
      obtain ⟨h1, h2, h3, h4⟩ := hI.testing r hr hk
      refine ⟨h1, ?_, by simp only [opOf, (hother r hrp).1]; exact h3, by rw [(hother r hrp).2, h4]⟩
      simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_singleton, not_or]
      exact ⟨h2, by simp [hrp]⟩
    · have hrp : r ≠ p := fun h => hr (h ▸ hp)
      obtain ⟨h1, h2, L₁, L₂, hL, hb⟩ := hI.answer r hr b hk
      exact ⟨h1, by rw [(hother r hrp).2, h2], L₁, L₂ ++ [((p, 0), TosOp.set)],
        by rw [hL]; simp, hb⟩
  · have hiff : T.R T.setOps.length q' ↔ T.R T.setOps.length q := by
      constructor
      · intro hQ'; by_contra hQ; exact hsw ⟨hQ, hQ'⟩
      · exact fun hQ => T.R_stable _ _ _ hQ
    refine ⟨h', L, ?_⟩
    refine
      { lin := hI.lin
        wf := hI.wf
        allow := hI.allow
        filt := hI.filt
        setL := by simp only [hmemC, hiff]; exact hI.setL
        onlySet := hI.onlySet
        byzS := fun hs hQ => hI.byzS hs (fun h => hQ (by simpa using hiff.2 h))
        idle := hI.idle
        setting := fun r hr k hk => ?_
        testing := hI.testing
        answer := hI.answer }
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI.setting r hr k hk
    exact ⟨h1, h2, by simpa using T.R_stable k q o h3, h4, h5⟩

end Steps

/-- The invariant holds along every execution in which correct processes invoke at most one
operation. -/
theorem tosInv_exec {Bz : Finset P} :
    ∀ (α : List (Event P testOrSet (fun _ : Unit => R)))
      (C : Config testOrSet (fun _ : Unit => R) P TosLoc),
      (tosImpl T).brun (accR allowedR) α = some C → (∀ e ∈ α, e.Respects Bz) →
      (∀ p ∉ Bz, (opsOf (hist α) p).length ≤ 1) → ∃ h' L, TosInv T Bz C (hist α) h' L := by
  intro α
  induction α using List.reverseRecOn with
  | nil =>
    intro C hC _ _
    simp only [Impl.brun, Impl.brunFrom_nil, Option.some.injEq] at hC; subst hC
    exact ⟨[], [], tosInv_init T Bz⟩
  | append_singleton α e ih =>
    intro C hC hresp hone
    obtain ⟨D, hD, he⟩ := (tosImpl T).brunFrom_append_eq_some _ hC
    rw [Impl.brunFrom_singleton] at he
    have hhist : hist (α ++ [e]) = hist α ++ e.hist.toList := by
      simp only [hist, List.filterMap_append]; cases h : e.hist <;> simp [h]
    have hone' : ∀ p ∉ Bz, (opsOf (hist α) p).length ≤ 1 := fun p hp => by
      have := hone p hp
      rw [hhist, opsOf_append, List.length_append] at this; omega
    obtain ⟨h', L, hI⟩ := ih D hD (fun e' he' => hresp e' (by simp [he'])) hone'
    have hc := (tosImpl T).bcounts (accR allowedR) hD
    have hre := hresp e (by simp)
    rw [hhist]
    cases e with
    | inv p o =>
      have hp : p ∉ Bz := hre
      simpa using hI.step_inv hc hp (by simpa [hhist] using hone p hp) he
    | ret p r =>
      have hp : p ∉ Bz := hre
      simpa using hI.step_ret hp (hone' p hp) he
    | tau p =>
      obtain ⟨L', hL'⟩ := hI.step_tau hre he
      exact ⟨h', L', by simpa using hL'⟩
    | byz p i o =>
      obtain ⟨h'', L', hL'⟩ := hI.step_byz hre he
      exact ⟨h'', L', by simpa using hL'⟩

variable (T) in
/-- **Observation 30** of [Hu–Toueg, PODC 2025], for every signature-like object: the
implementation `tosImpl T` of the one-shot test-or-set object from one atomic object with a
`SigTest` structure is correct (Byzantine linearizable and wait-free) against any number `f` of
Byzantine processes, which may apply to the object every operation they are allowed to. -/
theorem observation30 (f : ℕ) : (tosImpl T).ByzCorrect (accR allowedR) f oneShot := by
  refine ⟨fun Bz _ α hα hadm => ?_, fun Bz hBz ev hval hfair _ p hp k =>
    tos_termination T hBz ev hval hfair p hp k⟩
  obtain ⟨⟨C, hC⟩, hresp⟩ := hα
  obtain ⟨h', L, hI⟩ := tosInv_exec α C hC hresp hadm
  exact ⟨h', hI.wf, hI.allow, hI.filt, L, hI.lin⟩

/-- **Observation 30** of [Hu–Toueg, PODC 2025], verifiable registers: test-or-set (setter `s`)
from an atomic SWMR verifiable register with writer `s` (`Set = Write(v); Sign(v)`,
`Test = Verify(v)`) is correct against any number of Byzantine processes. -/
theorem observation30_verifiable {V : Type} (v₀ v : V) (s : P) (f : ℕ) :
    (tosImpl (verSig v₀ s v)).ByzCorrect (accR (verAllowed s)) f oneShot :=
  observation30 _ f

/-- **Observation 30** of [Hu–Toueg, PODC 2025], authenticated registers (`Set = Write(v)`,
`Test = Verify(v)`, `v ≠ v₀`). -/
theorem observation30_authenticated {V : Type} {v₀ v : V} (hv : v ≠ v₀) (s : P) (f : ℕ) :
    (tosImpl (authSig (v₀ := v₀) s hv)).ByzCorrect (accR (authAllowed s)) f oneShot :=
  observation30 _ f

/-- **Observation 30** of [Hu–Toueg, PODC 2025], sticky registers (`Set = Write(v)`,
`Test = Read ≠ ⊥`). -/
theorem observation30_sticky {V : Type} (v : V) (s : P) (f : ℕ) :
    (tosImpl (stickySig s v)).ByzCorrect (accR (stickyAllowed s)) f oneShot :=
  observation30 _ f

end

end Podc.ByzantineSWMRRegisters
