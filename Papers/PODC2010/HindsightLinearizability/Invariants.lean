import Papers.PODC2010.HindsightLinearizability.MemInv

/-!
# Theorem 4.1: memory safety and the integrity invariants of Fig. 4

`Inv C` is an inductive invariant of the configurations of the set algorithm: the memory
invariant `MemInv` plus, for every thread with a pending operation, a local invariant on its
program counter and local variables (`LocInv`). From it we derive

* `theorem_4_1_memSafe`: no thread ever dereferences `null` (the local state `err` is never
  reached);
* `theorem_4_1_state`: all state properties of Fig. 4 hold in every reachable state;
* `theorem_4_1_step`: all step properties of Fig. 4 hold for every step from a reachable state.
-/

namespace Podc.HindsightLinearizability

open Cslib.SharedMemory HeapState

/-- Local invariant of a thread whose pending operation is `o`, in local state `l`, w.r.t. the
memory `m`. -/
def LocInv (m : Mem) (o : SetOp) : Loc → Prop
  | .idle => False
  | .start o' => o' = o
  | .cross o' p => o' = o ∧ p < m.cnt ∧ m.key p < fin o.key
  | .test o' p c => o' = o ∧ p < m.cnt ∧ c < m.cnt ∧ m.key p < fin o.key ∧ m.key p < m.key c
  | .sec o' p c => o' = o ∧ (∀ k, o ≠ .contains k) ∧ p < m.cnt ∧ c < m.cnt ∧
      m.key p < fin o.key ∧ fin o.key ≤ m.key c
  | .done _ => True
  | .err => False

lemma LocInv.mono {m m' : Mem} (hc : m.cnt ≤ m'.cnt) (hk : ∀ u < m.cnt, m'.key u = m.key u)
    {o : SetOp} {l : Loc} (h : LocInv m o l) : LocInv m' o l := by
  cases l with
  | idle => exact h
  | start => exact h
  | cross o' p =>
    obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by omega, by rw [hk p h2]; exact h3⟩
  | test o' p c =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, by omega, by omega, by rw [hk p h2]; exact h4, by rw [hk p h2, hk c h3]; exact h5⟩
  | sec o' p c =>
    obtain ⟨h1, h0, h2, h3, h4, h5⟩ := h
    exact ⟨h1, h0, by omega, by omega, by rw [hk p h2]; exact h4, by rw [hk c h3]; exact h5⟩
  | done => exact h
  | err => exact h

variable {P : Type} [DecidableEq P]

/-- The invariant of configurations. -/
def Inv (C : Config setSpec (fun _ : Unit => heapObj) P Loc) : Prop :=
  MemInv (C.mem ()) ∧ ∀ q, (C.pend q = none → C.loc q = .idle) ∧
    ∀ o, C.pend q = some o → LocInv (C.mem ()) o (C.loc q)

/-- A step of thread `q` that accesses the heap. -/
lemma step_tau' {C C' : Config setSpec (fun _ : Unit => heapObj) P Loc} {q : P}
    (h : (impl P).step C (.tau q) = some C') :
    C.pend q ≠ none ∧ C'.pend = C.pend ∧ ∃ op k, act (C.loc q) = .access () op k ∧
      C'.mem () = (heapδ (C.mem ()) op).1 ∧
      C'.loc = Function.update C.loc q (k (heapδ (C.mem ()) op).2) := by
  obtain ⟨h1, h2, i, o, k, h3, h4, h5⟩ := Impl.step_tau h
  cases i
  exact ⟨h1, h2, o, k, h3, by rw [h4]; rfl, h5⟩

/-- The effect on the memory of a step of a thread satisfying its local invariant: either
nothing changes, or one of the two atomic sections succeeds and changes the memory as described
by `insertAfter_spec` / `unlink_spec`. -/
inductive MemEffect (m : Mem) : Mem → Prop
  | same : MemEffect m m
  | add (p c : ℕ) (k : ℤ) (hp : m.hs.Backbone p) (hc : m.next p = some c)
      (hpk : m.key p < fin k) (hck : fin k < m.key c) : MemEffect m (m.insertAfter p c k)
  | remove (p c : ℕ) (k : ℤ) (hp : m.hs.Backbone p) (hc : m.next p = some c)
      (hpk : m.key p < fin k) (hck : m.key c = fin k) : MemEffect m (m.unlink p c)

lemma MemEffect.memInv {m m' : Mem} (hm : MemInv m) (h : MemEffect m m') : MemInv m' := by
  cases h with
  | same => exact hm
  | add p c k hp hc hpk hck => exact (insertAfter_spec hm hp hc hpk hck).1
  | remove p c k hp hc hpk hck => exact (unlink_spec hm hp hc hpk hck).1

lemma MemEffect.cnt_le {m m' : Mem} (h : MemEffect m m') : m.cnt ≤ m'.cnt := by
  cases h <;> simp [Mem.insertAfter, Mem.unlink]

lemma MemEffect.key_eq {m m' : Mem} (h : MemEffect m m') {u : ℕ} (hu : u < m.cnt) :
    m'.key u = m.key u := by
  cases h with
  | same => rfl
  | add => simp [Mem.insertAfter, Function.update_apply, hu.ne]
  | remove => rfl

/-- One step of a thread: the new memory and its new local state. -/
lemma local_step {m : Mem} (hm : MemInv m) {o : SetOp} {l : Loc} (hl : LocInv m o l)
    {op : HOp} {k : HResp → Loc} (hact : act l = .access () op k) :
    MemEffect m (heapδ m op).1 ∧
      (LocInv (heapδ m op).1 o (k (heapδ m op).2) ∨ ∃ b, k (heapδ m op).2 = .done b) := by
  cases l with
  | idle => exact hl.elim
  | err => exact hl.elim
  | done b => simp [act] at hact
  | start o' =>
    simp only [act, Action.access.injEq, heq_eq_eq, true_and] at hact
    obtain ⟨rfl, rfl⟩ := hact
    refine ⟨.same, Or.inl ⟨hl, ?_, ?_⟩⟩
    · simp [heapδ, hm.H_eq]; have := hm.two_le; omega
    · simp [heapδ, hm.H_eq, hm.keyH]
  | cross o' p =>
    simp only [act, Action.access.injEq, heq_eq_eq, true_and] at hact
    obtain ⟨rfl, rfl⟩ := hact
    obtain ⟨rfl, hp, hpk⟩ := hl
    obtain ⟨v, hv, hv', hpv⟩ := hm.next_lt p hp (hm.ne_zero_of_key_lt hpk)
    refine ⟨.same, Or.inl ?_⟩
    simp only [heapδ, hv']
    exact ⟨rfl, hp, hv, hpk, hpv⟩
  | test o' p c =>
    simp only [act, Action.access.injEq, heq_eq_eq, true_and] at hact
    obtain ⟨rfl, rfl⟩ := hact
    obtain ⟨rfl, hp, hc, hpk, -⟩ := hl
    refine ⟨.same, ?_⟩
    simp only [heapδ, afterKey]
    split_ifs with hck
    · exact Or.inl ⟨rfl, hc, hck⟩
    · cases o' with
      | contains k => exact Or.inr ⟨_, rfl⟩
      | add k =>
        exact Or.inl ⟨rfl, (fun _ h => by cases h), hp, hc, hpk, not_lt.1 hck⟩
      | remove k =>
        exact Or.inl ⟨rfl, (fun _ h => by cases h), hp, hc, hpk, not_lt.1 hck⟩
  | sec o' p c =>
    simp only [act, Action.access.injEq, heq_eq_eq, true_and] at hact
    obtain ⟨rfl, rfl⟩ := hact
    obtain ⟨rfl, hnc, hp, hc, hpk, hck⟩ := hl
    cases o' with
    | contains k => exact absurd rfl (hnc k)
    | add k =>
      simp only [secOp, heapδ]
      split_ifs with hv hne
      · have hpb := (hm.unmarked_iff_backbone hp).1 hv.2
        exact ⟨.add p c k hpb hv.1 hpk (lt_of_le_of_ne hck (Ne.symm hne)), Or.inr ⟨_, rfl⟩⟩
      · exact ⟨.same, Or.inr ⟨_, rfl⟩⟩
      · exact ⟨.same, Or.inl rfl⟩
    | remove k =>
      simp only [secOp, heapδ]
      split_ifs with hv heq
      · have hpb := (hm.unmarked_iff_backbone hp).1 hv.2
        exact ⟨.remove p c k hpb hv.1 hpk heq, Or.inr ⟨_, rfl⟩⟩
      · exact ⟨.same, Or.inr ⟨_, rfl⟩⟩
      · exact ⟨.same, Or.inl rfl⟩

lemma inv_init : Inv (impl P).initCfg := by
  refine ⟨memInv_init, fun q => ⟨fun _ => rfl, fun o h => ?_⟩⟩
  simp [Impl.initCfg] at h

/-- A step changes the memory as described by `MemEffect`. -/
lemma memEffect_of_step {C C' : Config setSpec (fun _ : Unit => heapObj) P Loc}
    (hC : Inv C) {ℓ : Label P setSpec} (hs : (impl P).step C ℓ = some C') :
    MemEffect (C.mem ()) (C'.mem ()) := by
  cases ℓ with
  | inv q o => rw [(Impl.step_inv hs).2.2.2.2]; exact .same
  | ret q r => rw [(Impl.step_ret hs).2.2.1]; exact .same
  | tau q =>
    obtain ⟨h1, -, op, k, hact, hmem, -⟩ := step_tau' hs
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h1
    rw [hmem]
    exact (local_step hC.1 ((hC.2 q).2 o ho) hact).1

lemma inv_step {C C' : Config setSpec (fun _ : Unit => heapObj) P Loc}
    (hC : Inv C) {ℓ : Label P setSpec} (hs : (impl P).step C ℓ = some C') : Inv C' := by
  have heff := memEffect_of_step hC hs
  have hm' := heff.memInv hC.1
  refine ⟨hm', fun q => ?_⟩
  have hframe : ∀ o l, LocInv (C.mem ()) o l → LocInv (C'.mem ()) o l :=
    fun o l h => h.mono heff.cnt_le (fun u hu => heff.key_eq hu)
  by_cases hq : ℓ.proc = q
  · cases ℓ with
    | inv q' o =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, h1, h2, -⟩ := Impl.step_inv hs
      refine ⟨fun h => by simp [h1] at h, fun o' ho' => ?_⟩
      simp only [h1, Function.update_self, Option.some.injEq] at ho'
      subst ho'
      simp only [h2, Function.update_self]
      rfl
    | ret q' r =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, h1, -, l, hact, h2⟩ := Impl.step_ret hs
      have hl : l = .idle := by
        cases hlq : C.loc q' <;> simp only [impl, act, hlq] at hact <;>
          first | (cases hact; done) | (injection hact with _ h; exact h.symm)
      refine ⟨fun _ => by simp [h2, hl], fun o' ho' => by simp [h1] at ho'⟩
    | tau q' =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨h1, h2, op, k, hact, hmem, hloc⟩ := step_tau' hs
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h1
      refine ⟨fun h => absurd (h2 ▸ h) h1, fun o' ho' => ?_⟩
      rw [h2, ho, Option.some.injEq] at ho'
      subst ho'
      rw [hloc, Function.update_self, hmem]
      rcases (local_step hC.1 ((hC.2 q').2 o ho) hact).2 with h | ⟨b, hb⟩
      · exact h
      · rw [hb]; trivial
  · obtain ⟨hl, hp⟩ := Impl.step_other hs hq
    rw [hl, hp]
    exact ⟨(hC.2 q).1, fun o ho => hframe o _ ((hC.2 q).2 o ho)⟩

theorem inv_of_run {α : List (Label P setSpec)} {C : Config setSpec (fun _ : Unit => heapObj) P Loc}
    (h : (impl P).run α = some C) : Inv C :=
  Impl.invariant_of_run inv_init (fun _ _ _ hC hs => inv_step hC hs) h

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1 (memory safety).** In every execution of the set algorithm no thread ever
dereferences `null`: the error state is never reached. -/
theorem theorem_4_1_memSafe {α : List (Label P setSpec)}
    {C : Config setSpec (fun _ : Unit => heapObj) P Loc} (h : (impl P).run α = some C) (q : P) :
    C.loc q ≠ .err := by
  intro he
  obtain ⟨-, hq⟩ := inv_of_run h
  rcases hp : C.pend q with _ | o
  · have := (hq q).1 hp; rw [he] at this; cases this
  · have := (hq q).2 o hp; rw [he] at this; exact this

/-- All state properties of Fig. 4. -/
def StateProps (σ : HeapState ℕ Key) : Prop :=
  σ.PhiH ∧ σ.PhiT ∧ σ.PhiTn ∧ σ.PhiN ∧ σ.PhiInf ∧ σ.PhiNegInf ∧ σ.PhiLt ∧ σ.PhiRT ∧
    σ.PhiAc ∧ σ.PhiS ∧ σ.PhiUB ∧ σ.Closed

/-- All step properties of Fig. 4. -/
def StepProps (σ σ' : HeapState ℕ Key) : Prop :=
  DeltaH σ σ' ∧ DeltaT σ σ' ∧ DeltaK σ σ' ∧ DeltaM σ σ' ∧ DeltaE σ σ' ∧ DeltaEN σ σ' ∧
    DeltaBN σ σ' ∧ NoReclaim σ σ'

lemma MemInv.stateProps {m : Mem} (hm : MemInv m) : StateProps m.hs := by
  have h2 := hm.two_le
  have hlt := hm.hs_phiLt
  have hc := hm.hs_closed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlt, ?_, ?_, ?_, ?_, hc⟩
  · show m.H < m.cnt; rw [hm.H_eq]; omega
  · show m.T < m.cnt; rw [hm.T_eq]; omega
  · show m.next m.T = none; rw [hm.T_eq]; exact hm.nextT
  · intro u hu hT
    obtain ⟨v, -, hv, -⟩ := hm.next_lt u hu (by simpa [hm.T_eq] using hT)
    exact ⟨v, hv⟩
  · show m.key m.T = ⊤; rw [hm.T_eq]; exact hm.keyT
  · show m.key m.H = ⊥; rw [hm.H_eq]; exact hm.keyH
  · exact phiRT_of hlt hc (fun u hu hT => by
      obtain ⟨v, -, hv, -⟩ := hm.next_lt u hu (by simpa [hm.T_eq] using hT)
      exact ⟨v, hv⟩) (Set.finite_lt_nat _)
  · intro u hu
    by_cases hua : u < m.cnt
    · exact not_cycle_of_phiLt hlt hc hua hu
    · obtain ⟨v, hv, -⟩ := (Relation.TransGen.head'_iff).1 hu
      exact hua (hm.alloc_of_link hv)
  · intro u v huv
    by_cases hua : u < m.cnt
    · exact phiS_of_phiLt hlt hc u hua v huv
    · rcases huv.cases_head with rfl | ⟨w, hw, -⟩
      · exact le_rfl
      · exact absurd (hm.alloc_of_link hw) hua
  · intro u hu; exact hm.unmarked_iff_backbone hu

/-- **Theorem 4.1 (state properties).** Every reachable state satisfies all state properties of
Fig. 4. -/
theorem theorem_4_1_state {α : List (Label P setSpec)}
    {C : Config setSpec (fun _ : Unit => heapObj) P Loc} (h : (impl P).run α = some C) :
    StateProps (C.mem ()).hs :=
  (inv_of_run h).1.stateProps

/-- Step properties follow from the memory invariants of the two states and a few local
facts about the step. -/
lemma stepProps_of {m m' : Mem} (hm : MemInv m) (hm' : MemInv m') (hH : m'.H = m.H)
    (hT : m'.T = m.T) (hcnt : m.cnt ≤ m'.cnt) (hkey : ∀ u < m.cnt, m'.key u = m.key u)
    (hmark : ∀ u < m.cnt, m.mark u = true → m'.mark u = true)
    (hnext : ∀ u < m.cnt, m'.next u ≠ m.next u → m.mark u = false ∧ m'.mark u = false) :
    StepProps m.hs m'.hs := by
  refine ⟨hH, hT, hkey, hmark, ?_, ?_, ?_, fun u (hu : u < m.cnt) => (by
    show u < m'.cnt; omega)⟩
  · rintro u ⟨hu, hb⟩ hb'
    have hu' : u < m.cnt := hu
    have h1 : m.mark u = true := by
      by_contra h; exact hb ((hm.unmarked_iff_backbone hu').1 (by simpa using h))
    have := (hm'.unmarked_iff_backbone (by omega)).2 hb'
    rw [hmark u hu' h1] at this; cases this
  · rintro u ⟨hu, hb⟩
    by_contra hne
    exact hb ((hm.unmarked_iff_backbone hu).1 (hnext u hu hne).1)
  · intro u hb hne
    have hu := hm.backbone_lt hb
    exact (hm'.unmarked_iff_backbone (by omega)).1 (hnext u hu hne).2

lemma MemEffect.stepProps {m m' : Mem} (hm : MemInv m) (h : MemEffect m m') :
    StepProps m.hs m'.hs := by
  have hm' := h.memInv hm
  cases h with
  | same =>
    exact stepProps_of hm hm rfl rfl le_rfl (fun _ _ => rfl) (fun _ _ h => h)
      (fun _ _ h => absurd rfl h)
  | add p c k hp hc hpk hck =>
    have hp' := hm.backbone_lt hp
    refine stepProps_of hm hm' rfl rfl (by simp [Mem.insertAfter])
      (fun u hu => by simp [Mem.insertAfter, Function.update_apply, hu.ne])
      (fun u hu h => by simp [Mem.insertAfter, Function.update_apply, hu.ne, h]) ?_
    intro u hu hne
    have hup : u = p := by
      by_contra hup
      apply hne
      simp [Mem.insertAfter, Function.update_apply, hup, hu.ne]
    subst hup
    have := (hm.unmarked_iff_backbone hu).2 hp
    exact ⟨this, by simp [Mem.insertAfter, Function.update_apply, hu.ne, this]⟩
  | remove p c k hp hc hpk hck =>
    have hp' := hm.backbone_lt hp
    have hpc : p ≠ c := by rintro rfl; rw [hck] at hpk; exact lt_irrefl _ hpk
    refine stepProps_of hm hm' rfl rfl le_rfl (fun _ _ => rfl)
      (fun u hu h => by simp [Mem.unlink, Function.update_apply, h]) ?_
    intro u hu hne
    have hup : u = p := by
      by_contra hup
      apply hne
      simp [Mem.unlink, Function.update_apply, hup]
    subst hup
    have := (hm.unmarked_iff_backbone hu).2 hp
    exact ⟨this, by simp [Mem.unlink, Function.update_apply, hpc, this]⟩

/-- **Theorem 4.1 (step properties).** Every step from a reachable configuration satisfies all
step properties of Fig. 4. -/
theorem theorem_4_1_step {α : List (Label P setSpec)}
    {C C' : Config setSpec (fun _ : Unit => heapObj) P Loc} (h : (impl P).run α = some C)
    {ℓ : Label P setSpec} (hs : (impl P).step C ℓ = some C') :
    StepProps (C.mem ()).hs (C'.mem ()).hs :=
  (memEffect_of_step (inv_of_run h) hs).stepProps (inv_of_run h).1

end Podc.HindsightLinearizability
