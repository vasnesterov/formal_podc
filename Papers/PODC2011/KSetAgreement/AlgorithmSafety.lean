import Papers.PODC2011.KSetAgreement.Algorithm

/-!
# Safety of the initially-dead k-set agreement algorithm

The global invariant `Inv`: every message content in flight or buffered is *good* (stage-1
senders are woken, stage-2 messages carry the sender's input and actual in-list), and the local
state of every woken process satisfies `LocalGood` and `PostGood` relative to the actual in-lists
`IL s`. In particular every decided value is the input of a *frozen root* `m` of the in-list
graph, and distinct frozen roots have disjoint ancestor sets (source components) of size
`≥ d + 1`, so at most `n / (d + 1)` values are decided (`decVals_ncard_le`).
-/

namespace KSetAgreement.InitDeadAlg

open Cslib Cslib.FLP Relation SourceComp

variable {n : ℕ} {V : Type}

/-- Global states of the compiled algorithm. -/
abbrev GS (n : ℕ) (V : Type) := State (Fin n) (Msg n V) (Loc (Msg n V) (St n V) V)

/-- The in-list chosen in a local state (if woken). -/
def ilLoc : Loc (Msg n V) (St n V) V → Option (Finset (Fin n))
  | Sum.inl _ => none
  | Sum.inr st => st.1.inl

/-- The actual in-lists in a global state. -/
def IL (s : GS n V) : InLists n := fun r => ilLoc (s.proc r).state

/-- The woken processes in a global state. -/
def Wk (s : GS n V) (r : Fin n) : Prop := (s.proc r).state.isRight

/-- Invariant of a local state. -/
def LocOK (x : Fin n → V) (d : ℕ) (IL : InLists n) (W : Fin n → Prop) (p : Fin n) :
    Loc (Msg n V) (St n V) V → Prop
  | Sum.inl buf => ∀ c ∈ buf, GoodMsg x IL W c
  | Sum.inr st => LocalGood x d IL W p st.1 st.2 ∧ PostGood d p st.1 st.2

theorem LocOK.mono {x : Fin n → V} {d : ℕ} {IL IL' : InLists n} {W W' : Fin n → Prop}
    {p : Fin n} {l : Loc (Msg n V) (St n V) V} (h : Ext IL IL') (hW : ∀ r, W r → W' r)
    (hl : LocOK x d IL W p l) : LocOK x d IL' W' p l := by
  rcases l with buf | st
  · exact fun c hc => (hl c hc).mono h hW
  · exact ⟨hl.1.mono h hW, hl.2⟩

/-- **The global invariant.** -/
structure Inv (x : Fin n → V) (d : ℕ) (s : GS n V) : Prop where
  msgs : ∀ m ∈ s.msgs, ∀ c, m.msg = Sum.inr c → GoodMsg x (IL s) (Wk s) c
  loc : ∀ r, LocOK x d (IL s) (Wk s) r (s.proc r).state

/-- The compiled algorithm with inputs `x`. -/
noncomputable abbrev algC (d : ℕ) (x : Fin n → V) :
    Algorithm (Fin n) (Msg n V) (Loc (Msg n V) (St n V) V) :=
  (alg (V := V) d).algX x

theorem inv_start (d : ℕ) (x : Fin n → V) (inp : Fin n → Bool) :
    Inv x d ((algC d x).start inp) := by
  refine ⟨fun m hm c hc => ?_, fun r => ?_⟩
  · simp only [Algorithm.start, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at hm
    obtain ⟨p, rfl⟩ := hm
    simp at hc
  · simp [Algorithm.start, LocOK, KAlgorithm.alg]

theorem localGood_init (x : Fin n → V) (d : ℕ) (IL : InLists n) (W : Fin n → Prop) (p : Fin n) :
    LocalGood x d IL W p ((alg (V := V) d).init p (x p)) none where
  input := rfl
  notMem_heard := by simp [alg]
  heard := by simp [alg]
  inl := by simp [alg]
  know := by intro r v I h; simp [alg] at h
  dec := by simp

theorem ilLoc_nextLoc (d : ℕ) (x : Fin n → V) (p : Fin n) (msg : Bool ⊕ Msg n V)
    {l : Loc (Msg n V) (St n V) V} {I : Finset (Fin n)} (h : ilLoc l = some I) :
    ilLoc ((alg (V := V) d).nextLoc (fun p _ => x p) p msg l) = some I := by
  rcases l with buf | st
  · simp [ilLoc] at h
  · rcases msg with b | c
    · simpa [KAlgorithm.nextLoc] using h
    · simp only [KAlgorithm.nextLoc, ilLoc, KAlgorithm.apply]
      exact step_inl_of_some d p _ h

theorem isRight_nextLoc (d : ℕ) (x : Fin n → V) (p : Fin n) (msg : Bool ⊕ Msg n V)
    {l : Loc (Msg n V) (St n V) V} (h : l.isRight) :
    ((alg (V := V) d).nextLoc (fun p _ => x p) p msg l).isRight := by
  rcases l with buf | st
  · simp at h
  · rcases msg with b | c <;> simp [KAlgorithm.nextLoc]

/-- The receiving process: its new local state is good and so are the messages it sends. -/
theorem nextLoc_ok {x : Fin n → V} {d : ℕ} {IL : InLists n} {W : Fin n → Prop} {p : Fin n}
    {msg : Bool ⊕ Msg n V} {l : Loc (Msg n V) (St n V) V} (hl : LocOK x d IL W p l)
    (hm : ∀ c, msg = Sum.inr c → GoodMsg x IL W c)
    (hIL : IL p = ilLoc ((alg (V := V) d).nextLoc (fun p _ => x p) p msg l))
    (hW : ((alg (V := V) d).nextLoc (fun p _ => x p) p msg l).isRight → W p) :
    LocOK x d IL W p ((alg (V := V) d).nextLoc (fun p _ => x p) p msg l) ∧
      ∀ qc ∈ (alg (V := V) d).sendLoc (fun p _ => x p) p msg l, GoodMsg x IL W qc.2 := by
  rcases msg with b | c <;> rcases l with buf | st
  · simp only [KAlgorithm.nextLoc, KAlgorithm.sendLoc] at hIL hW ⊢
    have hW' := hW (by simp)
    obtain ⟨h1, h2⟩ := run_good hW' (none :: buf.map some) _ none (localGood_init x d IL W p)
      (by
        intro c hc
        simp only [List.mem_cons, reduceCtorEq, List.mem_map, Option.some.injEq,
          exists_eq_right, false_or] at hc
        exact hl c hc)
      (fun I hI => by rw [hIL]; exact hI)
    exact ⟨⟨h1, run_postGood d p _ _ _⟩, h2⟩
  · simp only [KAlgorithm.nextLoc, KAlgorithm.sendLoc]
    exact ⟨hl, fun qc hqc => by simp at hqc⟩
  · simp only [KAlgorithm.nextLoc, KAlgorithm.sendLoc]
    refine ⟨fun c' hc' => ?_, fun qc hqc => by simp at hqc⟩
    rcases List.mem_append.1 hc' with hc' | hc'
    · exact hl c' hc'
    · rw [List.mem_singleton.1 hc']
      exact hm c rfl
  · simp only [KAlgorithm.nextLoc, KAlgorithm.sendLoc] at hIL hW ⊢
    obtain ⟨h1, h2⟩ := apply_good (e := some c) hl.1 (hW (by simp))
      (fun c' hc' => by cases hc'; exact hm c rfl) (fun I hI => by rw [hIL]; exact hI)
    exact ⟨⟨h1, apply_postGood d p _ _⟩, h2⟩

variable [DecidableEq V]

theorem recv_proc (d : ℕ) (x : Fin n → V) (m : Message (Fin n) (Msg n V)) (s : GS n V)
    (r : Fin n) : (((algC d x).recvMsg m s).proc r).state =
      if r = m.dest then
        (alg (V := V) d).nextLoc (fun p _ => x p) m.dest m.msg (s.proc m.dest).state
      else (s.proc r).state := by
  simp only [Algorithm.recvMsg]
  split_ifs <;> rfl

/-- One transition preserves the invariant. -/
theorem inv_tr {d : ℕ} {x : Fin n → V} {s s' : GS n V} {a : Action (Fin n) (Msg n V)}
    (hs : Inv x d s) (htr : (algC d x).lts.Tr s a s') : Inv x d s' := by
  cases a with
  | none =>
    have : s' = s := htr
    subst this; exact hs
  | some m =>
    obtain ⟨hm, rfl⟩ := htr
    set p := m.dest
    have hproc := recv_proc d x m s
    have hext : Ext (IL s) (IL ((algC d x).recvMsg m s)) := by
      intro r I hI
      simp only [IL, hproc] at hI ⊢
      split_ifs with hr
      · subst hr; exact ilLoc_nextLoc d x _ _ hI
      · exact hI
    have hW : ∀ r, Wk s r → Wk ((algC d x).recvMsg m s) r := by
      intro r hr
      simp only [Wk, hproc] at hr ⊢
      split_ifs with h
      · subst h; exact isRight_nextLoc d x _ _ hr
      · exact hr
    have hp := nextLoc_ok (msg := m.msg) (p := p) ((hs.loc p).mono hext hW)
      (fun c hc => (hs.msgs m hm c hc).mono hext hW)
      (by simp only [IL, hproc, p, ↓reduceIte])
      (by intro h; simp only [Wk, hproc, p, ↓reduceIte]; exact h)
    refine ⟨fun m' hm' c hc => ?_, fun r => ?_⟩
    · simp only [Algorithm.recvMsg, Multiset.mem_add] at hm'
      rcases hm' with hm' | hm'
      · exact (hs.msgs m' (Multiset.mem_of_mem_erase hm') c hc).mono hext hW
      · simp only [KAlgorithm.alg, Multiset.mem_map] at hm'
        obtain ⟨qc, hqc, rfl⟩ := hm'
        simp only [KAlgorithm.wrap, Sum.inr.injEq] at hc
        subst hc
        exact hp.2 qc hqc
    · rw [hproc]
      split_ifs with hr
      · subst hr; exact hp.1
      · exact (hs.loc r).mono hext hW

theorem inv_mTr {d : ℕ} {x : Fin n → V} {s s' : GS n V} {xl : List (Action (Fin n) (Msg n V))}
    (hs : Inv x d s) (h : (algC d x).lts.MTr s xl s') : Inv x d s' := by
  induction h with
  | refl => exact hs
  | stepL htr _ ih => exact ih (inv_tr hs htr)

theorem inv_of_reachable {d : ℕ} {x : Fin n → V} {inp : Fin n → Bool} {s : GS n V}
    (h : (algC d x).Reachable inp s) : Inv x d s := by
  obtain ⟨xl, hxl⟩ := h
  exact inv_mTr (inv_start d x inp) hxl

/-! ### Counting the decided values -/

omit [DecidableEq V] in
theorem dec_frozen {d : ℕ} {x : Fin n → V} {s : GS n V} (hs : Inv x d s) {p : Fin n} {v : V}
    (h : dec s p = some v) : ∃ m, v = x m ∧ FrozenRoot (IL s) m := by
  have hl := hs.loc p
  simp only [dec] at h
  revert hl h
  rcases (s.proc p).state with buf | ⟨st, dv⟩
  · simp [KAlgorithm.decOf]
  · intro h hl
    exact hl.1.dec v h

omit [DecidableEq V] in
/-- In-lists in a reachable state have at least `d` elements and do not contain their owner. -/
theorem IL_spec {d : ℕ} {x : Fin n → V} {s : GS n V} (hs : Inv x d s) {r : Fin n}
    {I : Finset (Fin n)} (h : IL s r = some I) : d ≤ I.card ∧ r ∉ I ∧ ∀ u ∈ I, Wk s u := by
  have hl := hs.loc r
  simp only [IL] at h
  revert hl h
  rcases (s.proc r).state with buf | ⟨st, dv⟩
  · simp [ilLoc]
  · intro h hl
    obtain ⟨-, rfl, hd, -⟩ := hl.1.inl I h
    exact ⟨hd, hl.1.notMem_heard, hl.1.heard⟩

omit [DecidableEq V] in
/-- The number of frozen roots is at most `n / (d + 1)`. -/
theorem card_frozenRoots_le {d : ℕ} {x : Fin n → V} {s : GS n V} (hs : Inv x d s) :
    {m | FrozenRoot (IL s) m}.ncard ≤ n / (d + 1) := by
  classical
  set F := Finset.univ.filter fun m => FrozenRoot (IL s) m
  have hF : {m | FrozenRoot (IL s) m} = ↑F := by ext; simp [F]
  have hinj : Set.InjOn (anc (Edge (IL s))) ↑F := by
    intro m hm m' hm' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, F] at hm hm'
    have h1 : m ∈ anc (Edge (IL s)) m' := he ▸ mem_anc.2 ReflTransGen.refl
    have h2 : m' ∈ anc (Edge (IL s)) m := he ▸ mem_anc.2 ReflTransGen.refl
    exact le_antisymm (hm.min _ (mem_anc.1 h2)) (hm'.min _ (mem_anc.1 h1))
  rw [hF, Set.ncard_coe_finset, ← Finset.card_image_of_injOn hinj]
  have := card_sourceComponents_le (E := Edge (IL s)) (F.image (anc (Edge (IL s)))) d ?_
  · simpa using this
  intro C hC
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hC
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, F] at hm
  refine ⟨isSourceComponent_anc hm.root, ?_⟩
  obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 (hm.frozen m ReflTransGen.refl)
  obtain ⟨hd, hmI, -⟩ := IL_spec hs hI
  have hset : (Finset.univ.filter fun u => Edge (IL s) u m) = I := by
    ext u; simp [Edge, hI]
  have := (isSourceComponent_anc hm.root).card_ge (mem_anc.2 ReflTransGen.refl)
    (by simpa [Edge, hI] using hmI)
  rw [hset] at this
  omega

omit [DecidableEq V] in
theorem decVals_subset {d : ℕ} {x : Fin n → V} {s : GS n V} (hs : Inv x d s) :
    decVals s ⊆ x '' {m | FrozenRoot (IL s) m} := by
  rintro v ⟨p, hp⟩
  obtain ⟨m, rfl, hm⟩ := dec_frozen hs hp
  exact ⟨m, hm, rfl⟩

omit [DecidableEq V] in
theorem decVals_ncard_le {d : ℕ} {x : Fin n → V} {s : GS n V} (hs : Inv x d s) :
    (decVals s).ncard ≤ n / (d + 1) :=
  (Set.ncard_le_ncard (decVals_subset hs) ((Set.toFinite _).image _)).trans
    (Set.ncard_image_le (Set.toFinite _) |>.trans (card_frozenRoots_le hs))

/-- **Safety** (k-agreement and validity) of the algorithm with `d = n - f - 1`, provided
`(k + 1) f < k n`. -/
theorem kSafe (n f k : ℕ) (hk : (k + 1) * f < k * n) :
    KSafe (alg (n := n) (V := V) (n - f - 1)) k := by
  intro x inp s hs
  have hinv := inv_of_reachable hs
  refine ⟨(decVals_ncard_le hinv).trans ?_, fun p v hp => ?_⟩
  · have hfn : f < n := by
      by_contra h
      push Not at h
      have : k * n ≤ k * f := Nat.mul_le_mul_left k h
      nlinarith
    have hd : n - f - 1 + 1 = n - f := by omega
    rw [hd, Nat.le_iff_lt_add_one, Nat.div_lt_iff_lt_mul (by omega)]
    have e1 : (k + 1) * (n - f) = (k + 1) * n - (k + 1) * f := Nat.mul_sub _ _ _
    have e2 : (k + 1) * n = k * n + n := by ring
    omega
  · obtain ⟨m, rfl, -⟩ := dec_frozen hinv hp
    exact ⟨m, rfl⟩

end KSetAgreement.InitDeadAlg
