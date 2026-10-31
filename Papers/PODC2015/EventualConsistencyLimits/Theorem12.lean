import Papers.PODC2015.EventualConsistencyLimits.Final

/-!
# Theorem 12: messages of unbounded size

**Theorem 12 of [AEM15].** A causally and eventually consistent data store with invisible reads
and op-driven messages, providing `s` MVRs on `n` replicas, sends, for every `k`, a message of at
least `n' lg k` bits in some execution, where `n' = min (n - 2, s - 1)`.

The construction (Figure 4 of the paper). Writers `R_p` (`p < n'`) each write `⟨j, p⟩` to `x_p`
and broadcast, for `j < k`. For `g : [n'] → [k]`, replica `a` (`R_{n-1}`) receives, for every
`p`, the first `g p + 1` messages of `R_p`, reads `x_p`, then writes `y` and broadcasts `m_g`.
Decoding: replica `b` (`R_n`) receives the first `g p + 1` messages of every `R_p` and `m_g`, and
reads `y` and `x_i`.

Our proof of the decoding step differs from the paper's (which delivers `R_i`'s messages one by
one and is completed only in the full version): `b`'s state is final (it has heard everything in
the sub-execution in which every `R_p` stopped after `g p + 1` rounds), so its reads return
`{1}` and `{⟨g i, i⟩}`; if `m_g = m_{g'}` with `g i < g' i`, the same state of `b` occurs in an
execution where `a` read `⟨g' i, i⟩` before writing `y`, and causal consistency forces `b`'s read
of `x_i` to see `⟨g' i, i⟩`, which overwrites `⟨g i, i⟩`.
-/

namespace Podc.EventualConsistencyLimits

open Store

variable {ι Obj V M St : Type*} [DecidableEq ι]

/-- The data of the construction of Theorem 12: a data store with its availability hypotheses,
`n'` writer replicas `rr p` writing distinct values `val p j` to distinct objects `x p`, two more
replicas `a ≠ b`, a further object `y` and a fresh value `one`. -/
structure Cx (ι Obj V M St : Type*) (n' : ℕ) where
  D : Store ι Obj V M St
  hAv : D.Available
  hRecv : D.RecvEnabled
  rr : Fin n' → ι
  x : Fin n' → Obj
  val : Fin n' → ℕ → V
  a : ι
  b : ι
  y : Obj
  one : V
  rr_inj : Function.Injective rr
  a_ne_b : a ≠ b
  rr_ne_a : ∀ p, rr p ≠ a
  rr_ne_b : ∀ p, rr p ≠ b
  x_inj : Function.Injective x
  x_ne_y : ∀ p, x p ≠ y
  val_inj : ∀ p j p' j', val p j = val p' j' → p = p' ∧ j = j'
  val_ne_one : ∀ p j, val p j ≠ one

namespace Cx

variable {n' : ℕ} (C : Cx ι Obj V M St n') [Nonempty M]

/-! ### Writers -/

/-- Actions of writer `p` for rounds `js`: write `val p j` to `x p`, then send. -/
def wActs (p : Fin n') (js : List ℕ) : List (Act Obj V M) :=
  js.flatMap fun j => [.wr (C.x p) (C.val p j), .snd]

/-- Writer `p` after `J` rounds: events and state. -/
noncomputable def wRun (p : Fin n') (J : ℕ) : List (Ev Obj V M) × St :=
  C.D.acts C.hAv C.hRecv (C.rr p) (C.D.init (C.rr p)) (C.wActs p (List.range J))

/-- State of writer `p` after `j` rounds. -/
noncomputable def wSt (p : Fin n') (j : ℕ) : St := (C.wRun p j).2

/-- Response of the write of round `j`. -/
noncomputable def wResp (p : Fin n') (j : ℕ) : Resp V :=
  Classical.choose (C.hAv (C.rr p) (C.wSt p j) (C.x p) (.write (C.val p j)))

/-- State of writer `p` right after the write of round `j`. -/
noncomputable def wSt' (p : Fin n') (j : ℕ) : St :=
  (C.D.act1 C.hAv C.hRecv (C.rr p) (C.wSt p j) (.wr (C.x p) (C.val p j))).2

/-- Message `m^p_j` broadcast in round `j`. -/
noncomputable def msg (p : Fin n') (j : ℕ) : M := C.D.sendOf (C.rr p) (C.wSt' p j)

/-- The write event of round `j`. -/
noncomputable def wEvt (p : Fin n') (j : ℕ) : Ev Obj V M := .do_ ⟨C.x p, .write (C.val p j), C.wResp p j⟩

/-- Closed form of the events of writer `p` in its first `J` rounds. -/
noncomputable def wEvC (p : Fin n') (J : ℕ) : List (Ev Obj V M) :=
  (List.range J).flatMap fun j => [C.wEvt p j, .send (C.msg p j)]

lemma wRun_succ (p : Fin n') (J : ℕ) :
    C.wRun p (J + 1) = ((C.wRun p J).1 ++ [C.wEvt p J] ++
      (C.D.act1 C.hAv C.hRecv (C.rr p) (C.wSt' p J) .snd).1,
      (C.D.act1 C.hAv C.hRecv (C.rr p) (C.wSt' p J) .snd).2) := by
  simp only [wRun, List.range_succ, wActs, List.flatMap_append, List.flatMap_singleton]
  rw [acts_append, acts_cons, acts_cons, acts_nil]
  simp only [List.append_nil, List.append_assoc]
  rfl

@[simp] lemma wEvC_zero (p : Fin n') : C.wEvC p 0 = [] := rfl

lemma wEvC_succ (p : Fin n') (J : ℕ) :
    C.wEvC p (J + 1) = C.wEvC p J ++ [C.wEvt p J, .send (C.msg p J)] := by
  simp [wEvC, List.range_succ]

lemma length_wEvC (p : Fin n') (J : ℕ) : (C.wEvC p J).length = 2 * J := by
  induction J with
  | zero => rfl
  | succ J ih => rw [wEvC_succ]; simp [ih]; omega

lemma getElem_wEvC (p : Fin n') {J j : ℕ} (hj : j < J) :
    (C.wEvC p J)[2 * j]'(by rw [length_wEvC]; omega) = C.wEvt p j := by
  induction J with
  | zero => omega
  | succ J ih =>
    simp only [wEvC_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem_append_left (by rw [length_wEvC]; omega)]
      exact ih h
    · rw [List.getElem_append_right (by rw [length_wEvC])]
      simp [length_wEvC]

lemma wvals_tag_wEvC (p : Fin n') (J : ℕ) :
    wvals (tag (C.rr p) (C.wEvC p J)) = (List.range J).map (C.val p) := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [wEvC_succ, tag_append, wvals_append, ih, List.range_succ, List.map_append]
    simp [wvals, tag, wv, wEvt]

lemma mem_wEvC {p : Fin n'} {J : ℕ} {e : Ev Obj V M} (h : e ∈ C.wEvC p J) :
    ∃ j < J, e = C.wEvt p j ∨ e = .send (C.msg p j) := by
  simp only [wEvC, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at h
  obtain ⟨j, hj, h⟩ := h
  exact ⟨j, hj, h⟩

/-- Hypotheses on the data store used throughout. -/
structure Good (P : AE ι Obj V → Prop) : Prop where
  ec : C.D.EventuallyConsistent P
  ir : C.D.InvisibleReads
  od : C.D.OpDriven
  sc : C.D.SendClears

variable {C}

lemma wSt_zero (p : Fin n') : C.wSt p 0 = C.D.init (C.rr p) := rfl

lemma wSt_succ (p : Fin n') (J : ℕ) :
    C.wSt p (J + 1) = (C.D.act1 C.hAv C.hRecv (C.rr p) (C.wSt' p J) .snd).2 := by
  simp [wSt, wRun_succ]

lemma step_wEvt (p : Fin n') (J : ℕ) :
    C.D.step (C.rr p) (C.wSt p J) (C.wEvt p J) = some (C.wSt' p J) :=
  Classical.choose_spec (Classical.choose_spec
    (C.hAv (C.rr p) (C.wSt p J) (C.x p) (.write (C.val p J))))

lemma wSt_not_pending {P : AE ι Obj V → Prop} (H : C.Good P) (p : Fin n') (J : ℕ)
    (hp : ∀ j < J, C.D.Pending (C.rr p) (C.wSt' p j)) : ¬ C.D.Pending (C.rr p) (C.wSt p J) := by
  cases J with
  | zero => exact H.od.1 _
  | succ J =>
    rw [wSt_succ]
    exact H.sc _ _ _ _ (act1_snd_of_pending (hp J (by omega))).2

lemma wRun_fst_succ (p : Fin n') (J : ℕ) (hJ : (C.wRun p J).1 = C.wEvC p J)
    (hp : C.D.Pending (C.rr p) (C.wSt' p J)) : (C.wRun p (J + 1)).1 = C.wEvC p (J + 1) := by
  rw [wRun_succ, wEvC_succ, hJ, (act1_snd_of_pending hp).1]
  simp [msg]

/-- A solo writer's run is an execution. -/
lemma isExec_solo (p : Fin n') (J : ℕ) (hJ : (C.wRun p J).1 = C.wEvC p J) :
    C.D.IsExec (tag (C.rr p) (C.wEvC p J)) ∧
      C.D.state (C.rr p) (tag (C.rr p) (C.wEvC p J)) = some (C.wSt p J) := by
  have := IsExec.append_block (α := []) (i := C.rr p) .nil (state_nil _ _)
    (hJ ▸ acts_run (D := C.D) (hAv := C.hAv) (hRecv := C.hRecv) (C.rr p) _ _)
    (fun m hm => by obtain ⟨j, -, h | h⟩ := C.mem_wEvC hm <;> cases h)
  simpa [wSt, wRun] using this

/-- Every write of a writer is followed by a pending message (Lemma 5), so the writer's events
are `wEvC`. -/
theorem w_main [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) (p : Fin n') :
    ∀ J, (C.wRun p J).1 = C.wEvC p J ∧ C.D.Pending (C.rr p) (C.wSt' p J) := by
  intro J
  induction J using Nat.strong_induction_on with
  | _ J ih =>
  have hJ : (C.wRun p J).1 = C.wEvC p J := by
    cases J with
    | zero => rfl
    | succ J => exact wRun_fst_succ p J (ih J (by omega)).1 (ih J (by omega)).2
  refine ⟨hJ, ?_⟩
  obtain ⟨hα, hσ⟩ := isExec_solo p J hJ
  have hwv := wvals_tag_wEvC C p J
  refine lemma5 H.ec H.ir H.od C.hAv C.hRecv (R' := C.a) (C.rr_ne_a p) hα hσ (step_wEvt p J)
    (fresh_of_not_mem_wvals ?_) (dist_of_nodup_wvals ?_) ?_ ?_
  · rw [hwv]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro j hj h
    have := (C.val_inj _ _ _ _ h).2
    omega
  · rw [hwv]
    exact List.nodup_range.map fun j j' h => (C.val_inj _ _ _ _ h).2
  · intro i σi h
    by_cases hi : i = C.rr p
    · subst hi
      rw [hσ] at h
      cases h
      exact wSt_not_pending H p J fun j hj => (ih j hj).2
    · rw [state_congr C.D (β := []) (proj_tag_ne (Ne.symm hi) _)] at h
      cases h
      exact H.od.1 i
  · intro j m hj hjR
    exact absurd (mem_tag.1 hj).1 hjR

/-! ### Blocks of writers -/

variable (C) in
/-- The writers in `ps`, one after the other, writer `p` running `J p` rounds. -/
noncomputable def blocks (ps : List (Fin n')) (J : Fin n' → ℕ) : List (ι × Ev Obj V M) :=
  ps.flatMap fun p => tag (C.rr p) (C.wEvC p (J p))

lemma blocks_append (ps ps' : List (Fin n')) (J : Fin n' → ℕ) :
    C.blocks (ps ++ ps') J = C.blocks ps J ++ C.blocks ps' J := by
  simp [blocks, List.flatMap_append]

lemma blocks_cons (p : Fin n') (ps : List (Fin n')) (J : Fin n' → ℕ) :
    C.blocks (p :: ps) J = tag (C.rr p) (C.wEvC p (J p)) ++ C.blocks ps J := by
  simp [blocks]

@[simp] lemma blocks_nil (J : Fin n' → ℕ) : C.blocks [] J = [] := rfl

lemma mem_blocks {ps : List (Fin n')} {J : Fin n' → ℕ} {z : ι × Ev Obj V M} :
    z ∈ C.blocks ps J ↔ ∃ p ∈ ps, z.1 = C.rr p ∧ z.2 ∈ C.wEvC p (J p) := by
  simp [blocks, List.mem_flatMap, mem_tag]

lemma send_mem_blocks {ps : List (Fin n')} {J : Fin n' → ℕ} {p : Fin n'} (hp : p ∈ ps) {j : ℕ}
    (hj : j < J p) : (C.rr p, .send (C.msg p j)) ∈ C.blocks ps J := by
  rw [mem_blocks]
  refine ⟨p, hp, rfl, ?_⟩
  simp only [wEvC, List.mem_flatMap, List.mem_range]
  exact ⟨j, hj, by simp⟩

lemma mem_blocks_send {ps : List (Fin n')} {J : Fin n' → ℕ} {i : ι} {m : M}
    (h : (i, .send m) ∈ C.blocks ps J) : ∃ p ∈ ps, ∃ j < J p, i = C.rr p ∧ m = C.msg p j := by
  obtain ⟨p, hp, h1, h2⟩ := mem_blocks.1 h
  obtain ⟨j, hj, h | h⟩ := C.mem_wEvC h2
  · cases h
  · cases h; exact ⟨p, hp, j, hj, h1, rfl⟩

lemma mem_blocks_write {ps : List (Fin n')} {J : Fin n' → ℕ} {i : ι} {o : Obj} {v : V}
    {r : Resp V} (h : (i, .do_ ⟨o, .write v, r⟩) ∈ C.blocks ps J) :
    ∃ p ∈ ps, ∃ j < J p, i = C.rr p ∧ o = C.x p ∧ v = C.val p j := by
  obtain ⟨p, hp, h1, h2⟩ := mem_blocks.1 h
  obtain ⟨j, hj, h | h⟩ := C.mem_wEvC h2
  · simp only [wEvt, Ev.do_.injEq, DoEv.mk.injEq, Op.write.injEq] at h
    exact ⟨p, hp, j, hj, h1, h.1, h.2.1⟩
  · cases h

lemma not_mem_blocks_recv {ps : List (Fin n')} {J : Fin n' → ℕ} {i : ι} {m : M} :
    (i, .recv m) ∉ C.blocks ps J := by
  intro h
  obtain ⟨p, -, -, h2⟩ := mem_blocks.1 h
  obtain ⟨j, -, h | h⟩ := C.mem_wEvC h2 <;> cases h

lemma wvals_blocks (ps : List (Fin n')) (J : Fin n' → ℕ) :
    wvals (C.blocks ps J) = ps.flatMap fun p => (List.range (J p)).map (C.val p) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [blocks_cons, wvals_append, ih, wvals_tag_wEvC]; simp

lemma nodup_wvals_blocks {ps : List (Fin n')} (hps : ps.Nodup) (J : Fin n' → ℕ) :
    (wvals (C.blocks ps J)).Nodup := by
  rw [wvals_blocks, List.nodup_flatMap]
  refine ⟨fun p _ => List.nodup_range.map fun j j' h => (C.val_inj _ _ _ _ h).2, ?_⟩
  refine hps.pairwise_of_forall_ne fun p _ q _ hpq => ?_
  simp only [Function.onFun, List.disjoint_iff_ne, List.mem_map, List.mem_range]
  rintro _ ⟨j, -, rfl⟩ _ ⟨j', -, rfl⟩ h
  exact hpq (C.val_inj _ _ _ _ h).1

lemma state_blocks_of_not_mem {ps : List (Fin n')} {J : Fin n' → ℕ} {i : ι}
    (hi : ∀ p ∈ ps, C.rr p ≠ i) : C.D.state i (C.blocks ps J) = some (C.D.init i) := by
  rw [state_congr C.D (β := []) (proj_eq_nil fun z hz => ?_)]
  · rfl
  obtain ⟨p, hp, h1, -⟩ := mem_blocks.1 hz
  rw [h1]; exact hi p hp

/-- Blocks of distinct writers form an execution at the end of which nobody has a message
pending; writer `p ∈ ps` is in state `wSt p (J p)`. -/
theorem blocks_exec [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) {ps : List (Fin n')}
    (hps : ps.Nodup) (J : Fin n' → ℕ) :
    C.D.IsExec (C.blocks ps J) ∧ (∀ p ∈ ps, C.D.state (C.rr p) (C.blocks ps J) =
      some (C.wSt p (J p))) ∧
      ∀ i σ, C.D.state i (C.blocks ps J) = some σ → ¬ C.D.Pending i σ := by
  induction ps using List.reverseRecOn with
  | nil =>
    refine ⟨.nil, by simp, fun i σ h => ?_⟩
    cases h; exact H.od.1 i
  | append_singleton ps p ih =>
    rw [List.nodup_append] at hps
    have hp : p ∉ ps := fun h => hps.2.2 p h p (by simp) rfl
    obtain ⟨ih1, ih2, ih3⟩ := ih hps.1
    have hinit : C.D.state (C.rr p) (C.blocks ps J) = some (C.D.init (C.rr p)) :=
      state_blocks_of_not_mem fun q hq h => hp (C.rr_inj h ▸ hq)
    obtain ⟨hW, hP⟩ := w_main H p (J p)
    have hrun := acts_run (D := C.D) (hAv := C.hAv) (hRecv := C.hRecv) (C.rr p)
      (C.D.init (C.rr p)) (C.wActs p (List.range (J p)))
    rw [show C.D.acts C.hAv C.hRecv (C.rr p) (C.D.init (C.rr p)) (C.wActs p (List.range (J p)))
      = C.wRun p (J p) from rfl, hW] at hrun
    obtain ⟨hE, hS⟩ := IsExec.append_block ih1 hinit hrun
      (fun m hm => by obtain ⟨j, -, h | h⟩ := C.mem_wEvC hm <;> cases h)
    have hne : ∀ i, i ≠ C.rr p → C.D.state i (C.blocks (ps ++ [p]) J) =
        C.D.state i (C.blocks ps J) := by
      intro i hi
      rw [blocks_append, blocks_cons, blocks_nil, List.append_nil]
      exact state_append_of_not_mem _ _ _ fun z hz => by rw [(mem_tag.1 hz).1]; exact Ne.symm hi
    rw [blocks_append, blocks_cons, blocks_nil, List.append_nil] at hne ⊢
    refine ⟨hE, fun q hq => ?_, fun i σ h => ?_⟩
    · rcases List.mem_append.1 hq with hq | hq
      · rw [hne _ fun h => hp (C.rr_inj h ▸ hq)]; exact ih2 q hq
      · simp at hq; subst hq; exact hS
    · by_cases hi : i = C.rr p
      · subst hi; rw [hS] at h; cases h
        exact wSt_not_pending H p _ fun j _ => (w_main H p j).2
      · rw [hne i hi] at h; exact ih3 i σ h

/-! ### The replica `a` (`R_{n-1}` in the paper) -/

variable (C) in
/-- Receive the first `G + 1` messages of writer `p`. -/
noncomputable def rcvs (p : Fin n') (G : ℕ) : List (Act Obj V M) :=
  (List.range (G + 1)).map fun j => .rcv (C.msg p j)

variable (C) in
/-- Actions of `a` before writing `y`: for every writer `p`, receive its first `g p + 1`
messages, then read `x p`. -/
noncomputable def aPre (g : Fin n' → ℕ) : List (Act Obj V M) :=
  (List.finRange n').flatMap fun p => C.rcvs p (g p) ++ [.rd (C.x p)]

variable (C) in
noncomputable def aSt (g : Fin n' → ℕ) : St :=
  (C.D.acts C.hAv C.hRecv C.a (C.D.init C.a) (C.aPre g)).2

variable (C) in
noncomputable def aEvPre (g : Fin n' → ℕ) : List (Ev Obj V M) :=
  (C.D.acts C.hAv C.hRecv C.a (C.D.init C.a) (C.aPre g)).1

variable (C) in
noncomputable def aResp (g : Fin n' → ℕ) : Resp V :=
  Classical.choose (C.hAv C.a (C.aSt g) C.y (.write C.one))

variable (C) in
noncomputable def aSt' (g : Fin n' → ℕ) : St :=
  (C.D.act1 C.hAv C.hRecv C.a (C.aSt g) (.wr C.y C.one)).2

variable (C) in
/-- The message `m_g`. -/
noncomputable def mg (g : Fin n' → ℕ) : M := C.D.sendOf C.a (C.aSt' g)

variable (C) in
/-- All events of `a`. -/
noncomputable def aEv (g : Fin n' → ℕ) : List (Ev Obj V M) :=
  C.aEvPre g ++ [.do_ ⟨C.y, .write C.one, C.aResp g⟩, .send (C.mg g)]

lemma aPre_rcv_rd (g : Fin n' → ℕ) :
    ∀ x ∈ C.aPre g, (∃ m, x = .rcv m) ∨ ∃ o, x = .rd o := by
  intro x hx
  simp only [aPre, rcvs, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at hx
  obtain ⟨p, -, ⟨j, -, rfl⟩ | rfl⟩ := hx
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

lemma mem_aPre_rcv {g : Fin n' → ℕ} {m : M} (h : Act.rcv m ∈ C.aPre g) :
    ∃ p j, j ≤ g p ∧ m = C.msg p j := by
  simp only [aPre, rcvs, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at h
  obtain ⟨p, -, ⟨j, hj, h⟩ | h⟩ := h
  · cases h; exact ⟨p, j, by omega, rfl⟩
  · cases h

lemma rcv_mem_aPre (g : Fin n' → ℕ) (p : Fin n') {j : ℕ} (hj : j ≤ g p) :
    Act.rcv (C.msg p j) ∈ C.aPre g := by
  simp only [aPre, rcvs, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton]
  exact ⟨p, List.mem_finRange p, Or.inl ⟨j, by omega, rfl⟩⟩

lemma aEvPre_events {g : Fin n' → ℕ} {e : Ev Obj V M} (he : e ∈ C.aEvPre g) :
    (∃ p j, j ≤ g p ∧ e = .recv (C.msg p j)) ∨ ∃ o r, e = .do_ ⟨o, .read, r⟩ := by
  rcases acts_rcv_rd_events (C.aPre_rcv_rd g) he with ⟨m, rfl, hm⟩ | h
  · obtain ⟨p, j, hj, rfl⟩ := mem_aPre_rcv hm
    exact Or.inl ⟨p, j, hj, rfl⟩
  · exact Or.inr h

/-- `a`'s actions before the write can be appended to any execution in which `a` is still in
its initial state and the needed messages have been sent. -/
lemma a_exec {g : Fin n' → ℕ} {β : List (ι × Ev Obj V M)} (hβ : C.D.IsExec β)
    (hβa : C.D.state C.a β = some (C.D.init C.a))
    (hsent : ∀ p j, j ≤ g p → (C.rr p, .send (C.msg p j)) ∈ β) :
    C.D.IsExec (β ++ tag C.a (C.aEvPre g)) ∧
      C.D.state C.a (β ++ tag C.a (C.aEvPre g)) = some (C.aSt g) := by
  refine IsExec.append_block hβ hβa (acts_run _ _ _) fun m hm => ?_
  obtain ⟨p, j, hj, rfl⟩ := mem_aPre_rcv (mem_acts_recv hm)
  exact ⟨C.rr p, C.rr_ne_a p, hsent p j hj⟩

lemma state_blocks_a (ps : List (Fin n')) (J : Fin n' → ℕ) :
    C.D.state C.a (C.blocks ps J) = some (C.D.init C.a) :=
  state_blocks_of_not_mem fun p _ => C.rr_ne_a p

lemma state_blocks_b (ps : List (Fin n')) (J : Fin n' → ℕ) :
    C.D.state C.b (C.blocks ps J) = some (C.D.init C.b) :=
  state_blocks_of_not_mem fun p _ => C.rr_ne_b p

lemma tag_not_mem {i : ι} {l : List (Ev Obj V M)} {j : ι} (h : j ≠ i) :
    ∀ z ∈ tag i l, z.1 ≠ j := fun z hz => by rw [(mem_tag.1 hz).1]; exact Ne.symm h

variable (C) in
/-- The execution in which every writer `p` runs `g p + 1` rounds and `a` then receives and
reads. -/
noncomputable def αA (g : Fin n' → ℕ) : List (ι × Ev Obj V M) :=
  C.blocks (List.finRange n') (fun p => g p + 1) ++ tag C.a (C.aEvPre g)

lemma αA_exec [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) (g : Fin n' → ℕ) :
    C.D.IsExec (C.αA g) ∧ C.D.state C.a (C.αA g) = some (C.aSt g) ∧
      ∀ i σ, C.D.state i (C.αA g) = some σ → ¬ C.D.Pending i σ := by
  obtain ⟨hB, -, hBp⟩ := blocks_exec H (List.nodup_finRange n') (fun p => g p + 1)
  obtain ⟨hE, hS⟩ := a_exec (g := g) hB (C.state_blocks_a _ _) fun p j hj =>
    send_mem_blocks (J := fun p => g p + 1) (List.mem_finRange p) (by omega)
  refine ⟨hE, hS, fun i σ h => ?_⟩
  by_cases hi : i = C.a
  · subst hi
    rw [αA, hS] at h
    cases h
    exact not_pending_acts H.od H.ir (C.aPre_rcv_rd g) (H.od.1 _)
  · rw [αA, state_append_of_not_mem _ _ _ (tag_not_mem hi)] at h
    exact hBp i σ h

/-- Lemma 5 for `a`'s write of `y`: `a` broadcasts `m_g`. -/
theorem a_pending [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) (g : Fin n' → ℕ) :
    C.D.Pending C.a (C.aSt' g) := by
  obtain ⟨hE, hS, hnp⟩ := C.αA_exec H g
  have hw : wvals (C.αA g) = wvals (C.blocks (List.finRange n') fun p => g p + 1) := by
    rw [αA, wvals_append, wvals_eq_nil (α := tag C.a (C.aEvPre g)), List.append_nil]
    intro z hz o v r h
    rcases aEvPre_events (mem_tag.1 hz).2 with ⟨p, j, -, h'⟩ | ⟨o', r', h'⟩ <;>
      rw [h'] at h <;> cases h
  refine lemma5 H.ec H.ir H.od C.hAv C.hRecv C.a_ne_b hE hS
    (Classical.choose_spec (Classical.choose_spec (C.hAv C.a (C.aSt g) C.y (.write C.one))))
    (fresh_of_not_mem_wvals ?_) (dist_of_nodup_wvals ?_) hnp ?_
  · rw [hw, wvals_blocks]
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, not_exists, not_and]
    intro p _ j _ h
    exact C.val_ne_one _ _ h
  · rw [hw]; exact nodup_wvals_blocks (List.nodup_finRange n') _
  · intro j m hj hja
    rcases List.mem_append.1 hj with hj | hj
    · obtain ⟨p, -, jj, hjj, -, rfl⟩ := mem_blocks_send hj
      exact List.mem_append_right _ (mem_tag.2 ⟨rfl, mem_acts_of_rcv (rcv_mem_aPre g p
        (by omega))⟩)
    · exact absurd (mem_tag.1 hj).1 hja

lemma acts_aFull (g : Fin n' → ℕ) (hp : C.D.Pending C.a (C.aSt' g)) :
    C.D.acts C.hAv C.hRecv C.a (C.D.init C.a) (C.aPre g ++ [.wr C.y C.one, .snd]) =
      (C.aEv g, (C.D.act1 C.hAv C.hRecv C.a (C.aSt' g) .snd).2) := by
  have h1 := (act1_snd_of_pending (D := C.D) (hAv := C.hAv) (hRecv := C.hRecv) hp).1
  rw [acts_append, acts_cons, acts_cons, acts_nil]
  simp only [List.append_nil]
  change (_ ++ (_ ++ (C.D.act1 C.hAv C.hRecv C.a (C.aSt' g) .snd).1),
    (C.D.act1 C.hAv C.hRecv C.a (C.aSt' g) .snd).2) = _
  rw [h1]
  rfl

/-- All of `a`'s events, appended to an execution that provides the needed messages. -/
lemma a_full_exec [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) {g : Fin n' → ℕ}
    {β : List (ι × Ev Obj V M)} (hβ : C.D.IsExec β)
    (hβa : C.D.state C.a β = some (C.D.init C.a))
    (hsent : ∀ p j, j ≤ g p → (C.rr p, .send (C.msg p j)) ∈ β) :
    C.D.IsExec (β ++ tag C.a (C.aEv g)) ∧ ∀ σ, C.D.state C.a (β ++ tag C.a (C.aEv g)) = some σ →
      ¬ C.D.Pending C.a σ := by
  have hp := C.a_pending H g
  have hrun := acts_run (D := C.D) (hAv := C.hAv) (hRecv := C.hRecv) C.a (C.D.init C.a)
    (C.aPre g ++ [.wr C.y C.one, .snd])
  rw [acts_aFull g hp] at hrun
  obtain ⟨hE, hS⟩ := IsExec.append_block hβ hβa hrun fun m hm => by
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨p, j, hj, rfl⟩ := mem_aPre_rcv (mem_acts_recv hm)
      exact ⟨C.rr p, C.rr_ne_a p, hsent p j hj⟩
    · simp at hm
  refine ⟨hE, fun σ h => ?_⟩
  rw [hS] at h
  cases h
  exact H.sc _ _ _ _ (act1_snd_of_pending hp).2

lemma blocks_split {ps₁ ps₂ : List (Fin n')} {i : Fin n'} (J : Fin n' → ℕ) (hJ : 0 < J i) :
    C.blocks (ps₁ ++ i :: ps₂) J = (C.blocks ps₁ J ++ tag (C.rr i) (C.wEvC i (J i - 1))) ++
      (C.rr i, C.wEvt i (J i - 1)) :: ((C.rr i, .send (C.msg i (J i - 1))) :: C.blocks ps₂ J) := by
  obtain ⟨K, hK⟩ : ∃ K, J i = K + 1 := ⟨J i - 1, by omega⟩
  rw [blocks_append, blocks_cons, hK, wEvC_succ]
  simp

lemma finRange_split (i : Fin n') :
    ∃ ps₁ ps₂, List.finRange n' = ps₁ ++ i :: ps₂ := List.append_of_mem (List.mem_finRange i)

/-- **Fact 0.** `a`'s read of `x_i`, after receiving the first `g i + 1` messages of `R_i`,
returns exactly `⟨g i, i⟩`. -/
theorem a_read [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) (g : Fin n' → ℕ)
    (i : Fin n') : ∃ E₁ E₂, C.aEvPre g =
      E₁ ++ .do_ ⟨C.x i, .read, .vals {C.val i (g i)}⟩ :: E₂ := by
  obtain ⟨ps₁, ps₂, hfr⟩ := finRange_split i
  have hnd : (ps₁ ++ i :: ps₂).Nodup := hfr ▸ List.nodup_finRange n'
  set f : Fin n' → List (Act Obj V M) := fun p => C.rcvs p (g p) ++ [.rd (C.x p)]
  set pre₁ := ps₁.flatMap f ++ C.rcvs i (g i)
  have hpre : C.aPre g = pre₁ ++ .rd (C.x i) :: ps₂.flatMap f := by
    simp [aPre, hfr, pre₁, f, List.flatMap_append]
  have hsub : ∀ z ∈ pre₁, z ∈ C.aPre g := fun z hz => by rw [hpre]; simp [hz]
  set σ₁ := (C.D.acts C.hAv C.hRecv C.a (C.D.init C.a) pre₁).2
  obtain ⟨r, hr1, hr2⟩ := act1_rd (D := C.D) (hAv := C.hAv) (hRecv := C.hRecv) C.a σ₁ (C.x i)
  have hr2' : C.D.step C.a σ₁ (rd (C.x i) r) = some σ₁ := by
    have := hr2; rw [act1_rd_state H.ir] at this; exact this
  refine ⟨(C.D.acts C.hAv C.hRecv C.a (C.D.init C.a) pre₁).1,
    (C.D.acts C.hAv C.hRecv C.a (C.D.act1 C.hAv C.hRecv C.a σ₁ (.rd (C.x i))).2
      (ps₂.flatMap f)).1, ?_⟩
  have hev : C.aEvPre g = (C.D.acts C.hAv C.hRecv C.a (C.D.init C.a) pre₁).1 ++
      .do_ ⟨C.x i, .read, r⟩ :: (C.D.acts C.hAv C.hRecv C.a
        (C.D.act1 C.hAv C.hRecv C.a σ₁ (.rd (C.x i))).2 (ps₂.flatMap f)).1 := by
    rw [aEvPre, hpre, acts_append, acts_cons, hr1]; rfl
  rw [hev]
  congr 4
  -- the sub-execution: writers in `ps₁ ++ [i]`, then `a` up to the read
  set J : Fin n' → ℕ := fun p => g p + 1
  have hnd₁ : (ps₁ ++ [i]).Nodup := by
    rw [List.nodup_append] at hnd ⊢
    refine ⟨hnd.1, by simp, fun a ha b hb => ?_⟩
    simp at hb; subst hb; exact hnd.2.2 a ha b (by simp)
  obtain ⟨hB, -, hBp⟩ := blocks_exec H hnd₁ J
  have hsent : ∀ m, Ev.recv m ∈ (C.D.acts C.hAv C.hRecv C.a (C.D.init C.a) pre₁).1 →
      ∃ j, j ≠ C.a ∧ (j, .send m) ∈ C.blocks (ps₁ ++ [i]) J := by
    intro m hm
    have hm' := mem_acts_recv hm
    simp only [pre₁, f, rcvs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
      List.mem_singleton] at hm'
    rcases hm' with ⟨p, hp, ⟨j, hj, h⟩ | h⟩ | ⟨j, hj, h⟩
    · cases h
      exact ⟨_, C.rr_ne_a p, send_mem_blocks (by simp [hp]) (by simp [J]; omega)⟩
    · cases h
    · cases h
      exact ⟨_, C.rr_ne_a i, send_mem_blocks (by simp) (by simp [J]; omega)⟩
  obtain ⟨hE, hS⟩ := IsExec.append_block hB (C.state_blocks_a _ _) (acts_run _ _ _) hsent
  have hrr : ∀ z ∈ pre₁, (∃ m, z = .rcv m) ∨ ∃ o, z = .rd o :=
    fun z hz => C.aPre_rcv_rd g z (hsub z hz)
  set E₁ := (C.D.acts C.hAv C.hRecv C.a (C.D.init C.a) pre₁).1
  have hαeq : C.blocks (ps₁ ++ [i]) J ++ tag C.a E₁ =
      (C.blocks ps₁ J ++ tag (C.rr i) (C.wEvC i (g i))) ++ (C.rr i, C.wEvt i (g i)) ::
        ((C.rr i, .send (C.msg i (g i))) :: tag C.a E₁) := by
    rw [show (ps₁ ++ [i]) = ps₁ ++ i :: [] from rfl,
      C.blocks_split (ps₁ := ps₁) (ps₂ := []) (i := i) J (by simp [J])]
    simp [J]
  have hnp : ∀ j σj, C.D.state j (C.blocks (ps₁ ++ [i]) J ++ tag C.a E₁) = some σj →
      ¬ C.D.Pending j σj := by
    intro j σj h
    by_cases hj : j = C.a
    · subst hj; rw [hS] at h; cases h
      exact not_pending_acts H.od H.ir hrr (H.od.1 _)
    · rw [state_append_of_not_mem _ _ _ (tag_not_mem hj)] at h
      exact hBp j σj h
  have hrcv : ∀ j m, (j, Ev.send m) ∈ C.blocks (ps₁ ++ [i]) J ++ tag C.a E₁ → j ≠ C.a →
      (C.a, Ev.recv m) ∈ C.blocks (ps₁ ++ [i]) J ++ tag C.a E₁ := by
    intro j m hj hja
    rcases List.mem_append.1 hj with hj | hj
    · obtain ⟨p, hp, jj, hjj, -, rfl⟩ := mem_blocks_send hj
      refine List.mem_append_right _ (mem_tag.2 ⟨rfl, mem_acts_of_rcv ?_⟩)
      simp only [J] at hjj
      simp only [pre₁, f, rcvs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
        List.mem_singleton]
      rcases List.mem_append.1 hp with hp | hp
      · exact Or.inl ⟨p, hp, Or.inl ⟨jj, hjj, rfl⟩⟩
      · simp at hp; subst hp; exact Or.inr ⟨jj, hjj, rfl⟩
    · exact absurd (mem_tag.1 hj).1 hja
  have hall : ∀ z ∈ C.blocks (ps₁ ++ [i]) J ++ tag C.a E₁, ∀ v r',
      z.2 = .do_ ⟨C.x i, .write v, r'⟩ → z.1 = C.rr i := by
    rintro ⟨j, e⟩ hz v r' he
    simp only at he
    subst he
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨p, -, jj, -, rfl, hx, -⟩ := mem_blocks_write hz
      rw [C.x_inj hx]
    · rcases acts_rcv_rd_events hrr (mem_tag.1 hz).2 with ⟨m, h, -⟩ | ⟨o, r, h⟩ <;> cases h
  rw [hαeq] at hE hS hnp hrcv hall
  refine final_read' H.ec H.od C.hRecv hE hS hr2' hnp hrcv hall ?_
  intro z hz v r' h
  rcases List.mem_cons.1 hz with rfl | hz
  · cases h
  · have := (mem_tag.1 hz).1
    rw [h] at this
    exact C.rr_ne_a i this

/-! ### The replica `b` (`R_n` in the paper) and decoding -/

variable (C) in
/-- `b` receives the first `g p + 1` messages of every writer `p`, then `m`. -/
noncomputable def bPre (g : Fin n' → ℕ) (m : M) : List (Act Obj V M) :=
  (List.finRange n').flatMap (fun p => C.rcvs p (g p)) ++ [.rcv m]

variable (C) in
noncomputable def bSt (g : Fin n' → ℕ) (m : M) : St :=
  (C.D.acts C.hAv C.hRecv C.b (C.D.init C.b) (C.bPre g m)).2

variable (C) in
noncomputable def bEvPre (g : Fin n' → ℕ) (m : M) : List (Ev Obj V M) :=
  (C.D.acts C.hAv C.hRecv C.b (C.D.init C.b) (C.bPre g m)).1

variable (C) in
/-- `b`'s read of `y` (in state `bSt g m`). -/
noncomputable def ry (g : Fin n' → ℕ) (m : M) : Resp V :=
  Classical.choose (C.hAv C.b (C.bSt g m) C.y .read)

variable (C) in
/-- `b`'s read of `x_i` (in state `bSt g m`). -/
noncomputable def rx (g : Fin n' → ℕ) (m : M) (i : Fin n') : Resp V :=
  Classical.choose (C.hAv C.b (C.bSt g m) (C.x i) .read)

lemma step_ry {P : AE ι Obj V → Prop} (H : C.Good P) (g : Fin n' → ℕ) (m : M) :
    C.D.step C.b (C.bSt g m) (rd C.y (C.ry g m)) = some (C.bSt g m) := by
  have h := Classical.choose_spec (Classical.choose_spec (C.hAv C.b (C.bSt g m) C.y .read))
  have e := H.ir _ _ _ _ _ h
  rw [e] at h; exact h

lemma step_rx {P : AE ι Obj V → Prop} (H : C.Good P) (g : Fin n' → ℕ) (m : M) (i : Fin n') :
    C.D.step C.b (C.bSt g m) (rd (C.x i) (C.rx g m i)) = some (C.bSt g m) := by
  have h := Classical.choose_spec (Classical.choose_spec (C.hAv C.b (C.bSt g m) (C.x i) .read))
  have e := H.ir _ _ _ _ _ h
  rw [e] at h; exact h

lemma bPre_rcv (g : Fin n' → ℕ) (m : M) : ∀ z ∈ C.bPre g m, (∃ m, z = .rcv m) ∨ ∃ o, z = .rd o := by
  intro z hz
  simp only [bPre, rcvs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_singleton] at hz
  rcases hz with ⟨p, -, j, -, rfl⟩ | rfl <;> exact Or.inl ⟨_, rfl⟩

lemma mem_bPre_rcv {g : Fin n' → ℕ} {m m' : M} (h : Act.rcv m' ∈ C.bPre g m) :
    m' = m ∨ ∃ p j, j ≤ g p ∧ m' = C.msg p j := by
  simp only [bPre, rcvs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_singleton] at h
  rcases h with ⟨p, -, j, hj, h⟩ | h <;> cases h
  · exact Or.inr ⟨p, j, by omega, rfl⟩
  · exact Or.inl rfl

lemma rcv_mem_bPre (g : Fin n' → ℕ) (m : M) (p : Fin n') {j : ℕ} (hj : j ≤ g p) :
    Act.rcv (C.msg p j) ∈ C.bPre g m := by
  simp only [bPre, rcvs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_singleton]
  exact Or.inl ⟨p, List.mem_finRange p, j, by omega, rfl⟩

lemma rcv_mem_bPre' (g : Fin n' → ℕ) (m : M) : Act.rcv m ∈ C.bPre g m := by
  simp [bPre]

/-- `b`'s block after an execution `β` in which `b` is initial and all needed messages were
sent by other replicas. -/
lemma b_exec {g : Fin n' → ℕ} {m : M} {β : List (ι × Ev Obj V M)} (hβ : C.D.IsExec β)
    (hβb : C.D.state C.b β = some (C.D.init C.b))
    (hsent : ∀ p j, j ≤ g p → (C.rr p, .send (C.msg p j)) ∈ β) (hm : (C.a, .send m) ∈ β) :
    C.D.IsExec (β ++ tag C.b (C.bEvPre g m)) ∧
      C.D.state C.b (β ++ tag C.b (C.bEvPre g m)) = some (C.bSt g m) := by
  refine IsExec.append_block hβ hβb (acts_run _ _ _) fun m' hm' => ?_
  rcases mem_bPre_rcv (mem_acts_recv hm') with rfl | ⟨p, j, hj, rfl⟩
  · exact ⟨C.a, C.a_ne_b, hm⟩
  · exact ⟨C.rr p, C.rr_ne_b p, hsent p j hj⟩

variable (C) in
/-- The decoding execution: writers run `g p + 1` rounds, `a` runs completely (sending `m_g`),
`b` receives everything. -/
noncomputable def αB (g : Fin n' → ℕ) : List (ι × Ev Obj V M) :=
  C.blocks (List.finRange n') (fun p => g p + 1) ++ tag C.a (C.aEv g) ++
    tag C.b (C.bEvPre g (C.mg g))

/-- **Decoding.** In state `bSt g m_g`, `b` reads `{1}` from `y` and `⟨g i, i⟩` from `x_i`. -/
theorem decode [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) (g : Fin n' → ℕ) :
    C.ry g (C.mg g) = .vals {C.one} ∧ ∀ i, C.rx g (C.mg g) i = .vals {C.val i (g i)} := by
  set J : Fin n' → ℕ := fun p => g p + 1
  obtain ⟨hB, -, hBp⟩ := blocks_exec H (List.nodup_finRange n') J
  have hsent : ∀ p j, j ≤ g p → (C.rr p, .send (C.msg p j)) ∈ C.blocks (List.finRange n') J :=
    fun p j hj => send_mem_blocks (List.mem_finRange p) (by simp [J]; omega)
  obtain ⟨hA, hAp⟩ := a_full_exec H hB (C.state_blocks_a _ _) hsent
  have hmg : (C.a, .send (C.mg g)) ∈ C.blocks (List.finRange n') J ++ tag C.a (C.aEv g) :=
    List.mem_append_right _ (mem_tag.2 ⟨rfl, by simp [aEv]⟩)
  obtain ⟨hE, hS⟩ := b_exec (g := g) hA
    (by rw [state_append_of_not_mem _ _ _ (tag_not_mem C.a_ne_b.symm)]
        exact C.state_blocks_b _ _)
    (fun p j hj => List.mem_append_left _ (hsent p j hj)) hmg
  -- facts about `αB`
  have hnp : ∀ j σj, C.D.state j (C.αB g) = some σj → ¬ C.D.Pending j σj := by
    intro j σj h
    by_cases hjb : j = C.b
    · subst hjb; rw [αB, hS] at h; cases h
      exact not_pending_acts H.od H.ir (C.bPre_rcv g _) (H.od.1 _)
    · rw [αB, state_append_of_not_mem _ _ _ (tag_not_mem hjb)] at h
      by_cases hja : j = C.a
      · subst hja; exact hAp σj h
      · rw [state_append_of_not_mem _ _ _ (tag_not_mem hja)] at h
        exact hBp j σj h
  have hrcv : ∀ j m, (j, Ev.send m) ∈ C.αB g → j ≠ C.b → (C.b, Ev.recv m) ∈ C.αB g := by
    intro j m hj hjb
    refine List.mem_append_right _ (mem_tag.2 ⟨rfl, mem_acts_of_rcv ?_⟩)
    rcases List.mem_append.1 hj with hj | hj
    · rcases List.mem_append.1 hj with hj | hj
      · obtain ⟨p, -, jj, hjj, -, rfl⟩ := mem_blocks_send hj
        exact rcv_mem_bPre g _ p (by simp [J] at hjj; omega)
      · have := (mem_tag.1 hj).2
        simp only [aEv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with h | h | h
        · rcases aEvPre_events h with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
        · cases h
        · cases h; exact rcv_mem_bPre' g _
    · exact absurd (mem_tag.1 hj).1 hjb
  have hbw : ∀ z ∈ tag C.b (C.bEvPre g (C.mg g)), ∀ o v r', z.2 ≠ .do_ ⟨o, .write v, r'⟩ := by
    intro z hz o v r' h
    rcases acts_rcv_rd_events (C.bPre_rcv g _) (mem_tag.1 hz).2 with ⟨m, h', -⟩ | ⟨o', r, h'⟩ <;>
      rw [h] at h' <;> cases h'
  constructor
  · -- `y`
    have hαeq : C.αB g = (C.blocks (List.finRange n') J ++ tag C.a (C.aEvPre g)) ++
        (C.a, .do_ ⟨C.y, .write C.one, C.aResp g⟩) ::
          ((C.a, .send (C.mg g)) :: tag C.b (C.bEvPre g (C.mg g))) := by
      simp [αB, aEv, J]
    have hall : ∀ z ∈ C.αB g, ∀ v r', z.2 = .do_ ⟨C.y, .write v, r'⟩ → z.1 = C.a := by
      rintro ⟨j, e⟩ hz v r' he
      simp only at he
      subst he
      rcases List.mem_append.1 hz with hz | hz
      · rcases List.mem_append.1 hz with hz | hz
        · obtain ⟨p, -, -, -, -, hx, -⟩ := mem_blocks_write hz
          exact absurd hx.symm (C.x_ne_y p)
        · exact (mem_tag.1 hz).1
      · exact absurd rfl (hbw _ hz C.y v r')
    rw [hαeq] at hnp hrcv hall
    rw [show C.blocks (List.finRange n') J ++ tag C.a (C.aEv g) ++ tag C.b (C.bEvPre g (C.mg g))
      = C.αB g from rfl, hαeq] at hE hS
    refine final_read' H.ec H.od C.hRecv hE hS (step_ry H g _) hnp hrcv hall ?_
    intro z hz v r' h
    rcases List.mem_cons.1 hz with rfl | hz
    · cases h
    · have := (mem_tag.1 hz).1
      rw [h] at this
      exact C.a_ne_b (by simpa using this)
  · -- `x_i`
    intro i
    obtain ⟨ps₁, ps₂, hfr⟩ := finRange_split i
    have hnd : (ps₁ ++ i :: ps₂).Nodup := hfr ▸ List.nodup_finRange n'
    have hαeq : C.αB g = (C.blocks ps₁ J ++ tag (C.rr i) (C.wEvC i (g i))) ++
        (C.rr i, C.wEvt i (g i)) :: ((C.rr i, .send (C.msg i (g i))) ::
          (C.blocks ps₂ J ++ tag C.a (C.aEv g) ++ tag C.b (C.bEvPre g (C.mg g)))) := by
      rw [αB, hfr, C.blocks_split J (by simp [J])]
      simp [J]
    have hall : ∀ z ∈ C.αB g, ∀ v r', z.2 = .do_ ⟨C.x i, .write v, r'⟩ → z.1 = C.rr i := by
      rintro ⟨j, e⟩ hz v r' he
      simp only at he
      subst he
      rcases List.mem_append.1 hz with hz | hz
      · rcases List.mem_append.1 hz with hz | hz
        · obtain ⟨p, -, -, -, rfl, hx, -⟩ := mem_blocks_write hz
          rw [C.x_inj hx]
        · have := (mem_tag.1 hz).2
          simp only [aEv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this
          rcases this with h | h | h
          · rcases aEvPre_events h with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
          · simp only [Ev.do_.injEq, DoEv.mk.injEq] at h
            exact absurd h.1 (C.x_ne_y i)
          · cases h
      · exact absurd rfl (hbw _ hz (C.x i) v r')
    have h₂ : ∀ z ∈ (C.rr i, Ev.send (C.msg i (g i))) ::
        (C.blocks ps₂ J ++ tag C.a (C.aEv g) ++ tag C.b (C.bEvPre g (C.mg g))),
        ∀ v r', z ≠ (C.rr i, .do_ ⟨C.x i, .write v, r'⟩) := by
      intro z hz v r' h
      subst h
      rcases List.mem_cons.1 hz with h | hz
      · cases h
      rcases List.mem_append.1 hz with hz | hz
      · rcases List.mem_append.1 hz with hz | hz
        · obtain ⟨p, hp, -, -, hrr, -, -⟩ := mem_blocks_write hz
          have := C.rr_inj hrr
          subst this
          rw [List.nodup_append] at hnd
          exact (List.nodup_cons.1 hnd.2.1).1 hp
        · exact C.rr_ne_a i (mem_tag.1 hz).1
      · exact C.rr_ne_b i (mem_tag.1 hz).1
    rw [hαeq] at hnp hrcv hall
    rw [show C.blocks (List.finRange n') J ++ tag C.a (C.aEv g) ++ tag C.b (C.bEvPre g (C.mg g))
      = C.αB g from rfl, hαeq] at hE hS
    exact final_read' H.ec H.od C.hRecv hE hS (step_rx H g _ i) hnp hrcv hall h₂

/-! ### The contradiction -/

lemma wEvC_prefix (p : Fin n') {j J : ℕ} (h : j ≤ J) : ∃ R, C.wEvC p J = C.wEvC p j ++ R := by
  induction J, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ J _ ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R ++ [C.wEvt p J, .send (C.msg p J)], by rw [wEvC_succ, hR]; simp⟩

lemma wEvC_split (p : Fin n') {j J : ℕ} (h : j < J) :
    ∃ R, C.wEvC p J = C.wEvC p j ++ C.wEvt p j :: R := by
  obtain ⟨R, hR⟩ := C.wEvC_prefix p (show j + 1 ≤ J by omega)
  exact ⟨.send (C.msg p j) :: R, by rw [hR, wEvC_succ]; simp⟩

lemma getElem_of_eq {α : Type*} {l l₁ l₂ : List α} {x : α} (h : l = l₁ ++ x :: l₂) :
    ∃ hl : l₁.length < l.length, l[l₁.length] = x :=
  ⟨by rw [h]; simp, by simp [h]⟩

/-- If `m_g = m_{g'}` and `g i < g' i`, causal consistency fails in the execution where the
writers run `k` rounds, `a` acts as for `g'`, and `b` receives as for `g` and reads `y`, `x_i`. -/
theorem key [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) (hCC : C.D.CausallyConsistent)
    {k : ℕ} {g g' : Fin n' → ℕ} (hg : ∀ p, g p < k) (hg' : ∀ p, g' p < k) {i : Fin n'}
    (hi : g i < g' i) (hm : C.mg g = C.mg g') : False := by
  set K : Fin n' → ℕ := fun _ => k
  set B := C.blocks (List.finRange n') K
  obtain ⟨hB, -, -⟩ := blocks_exec H (List.nodup_finRange n') K
  have hsentK : ∀ (h : Fin n' → ℕ), (∀ p, h p < k) → ∀ p j, j ≤ h p →
      (C.rr p, .send (C.msg p j)) ∈ B :=
    fun h hh p j hj => send_mem_blocks (List.mem_finRange p) (by simp [K]; have := hh p; omega)
  obtain ⟨hA, -⟩ := a_full_exec H hB (C.state_blocks_a _ _) (hsentK g' hg')
  have hmg : (C.a, .send (C.mg g')) ∈ B ++ tag C.a (C.aEv g') :=
    List.mem_append_right _ (mem_tag.2 ⟨rfl, by simp [aEv]⟩)
  obtain ⟨hE, hS⟩ := b_exec (g := g) hA
    (by rw [state_append_of_not_mem _ _ _ (tag_not_mem C.a_ne_b.symm)]
        exact C.state_blocks_b _ _)
    (fun p j hj => List.mem_append_left _ (hsentK g hg p j hj)) hmg
  set ry' := C.ry g (C.mg g')
  set rx' := C.rx g (C.mg g') i
  set E2 := B ++ tag C.a (C.aEv g') ++ tag C.b (C.bEvPre g (C.mg g')) ++
    [(C.b, rd C.y ry'), (C.b, rd (C.x i) rx')]
  have hE2 : C.D.IsExec E2 := by
    have h1 := IsExec.snoc hE hS (step_ry H g _) (fun m h => by cases h)
    have h2 := IsExec.snoc h1 (by rw [state_snoc_self C.D hS, step_ry H g _]) (step_rx H g _ i)
      (fun m h => by cases h)
    simpa [E2] using h2
  obtain ⟨hdy, hdx⟩ := decode H g
  rw [hm] at hdy hdx
  have hry : ry' = .vals {C.one} := hdy
  have hrx : rx' = .vals {C.val i (g i)} := hdx i
  obtain ⟨E₁, E₂, hE₁⟩ := C.a_read H g' i
  -- unique writers in `E2`
  have hnd : (wvals E2).Nodup := by
    have h1 : wvals (tag C.a (C.aEv g')) = [C.one] := by
      rw [aEv, tag_append, wvals_append, wvals_eq_nil]
      · simp [wvals, tag, wv]
      · intro z hz o v r h
        rcases aEvPre_events (mem_tag.1 hz).2 with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;>
          rw [h'] at h <;> cases h
    have h2 : wvals (tag C.b (C.bEvPre g (C.mg g'))) = [] := by
      apply wvals_eq_nil
      intro z hz o v r h
      rcases acts_rcv_rd_events (C.bPre_rcv g _) (mem_tag.1 hz).2 with ⟨m, h', -⟩ | ⟨o', r', h'⟩ <;>
        rw [h'] at h <;> cases h
    have h3 : wvals ([(C.b, rd C.y ry'), (C.b, rd (C.x i) rx')] : List (ι × Ev Obj V M)) = [] :=
      rfl
    simp only [E2, wvals_append, h1, h2, h3, List.append_nil]
    rw [List.nodup_append]
    refine ⟨nodup_wvals_blocks (List.nodup_finRange n') K, List.nodup_singleton _, ?_⟩
    intro u hu w hw
    simp only [List.mem_singleton] at hw
    subst hw
    rw [wvals_blocks] at hu
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hu
    obtain ⟨p, -, j, -, rfl⟩ := hu
    exact C.val_ne_one p j
  have hdist := dist_of_nodup_wvals hnd
  -- the abstract execution
  obtain ⟨A, hOn, hWF, hCor, hTr⟩ := hCC E2 hE2
  have hwho : ∀ c (q : ℕ) (hq : q < E2.length) j o' r' u, A.dom c → (A.ev c).op = .write u →
      E2[q] = (j, .do_ ⟨o', .write u, r'⟩) → c = q := by
    intro c q hq j o' r' u hc hcu hqe
    obtain ⟨hcl, j', d, hcd, -, hev⟩ := hOn.of_domL hc
    rw [hev] at hcu
    obtain ⟨o'', op'', r''⟩ := d
    simp only at hcu
    subst hcu
    exact hdist c q hcl hq j' j o'' o' u r'' r' hcd hqe
  have hret : ∀ e o S u (q : ℕ) (hq : q < E2.length) j o' r', A.dom e →
      A.ev e = ⟨o, .read, .vals S⟩ → u ∈ S → E2[q] = (j, .do_ ⟨o', .write u, r'⟩) →
      q ∈ A.ctxW e ∧ ∀ b ∈ A.ctxW e, ¬ A.vis q b := by
    intro e o S u q hq j o' r' he hev hu hqe
    rw [AE.Correct.read (hA := hCor) he hev] at hu
    obtain ⟨c, hc, hcu, hmax⟩ := hu
    have := hwho c q hq j o' r' u (hWF.vis_dom hc.1).1 hcu hqe
    subst this
    exact ⟨hc, hmax⟩
  -- positions
  obtain ⟨ps₁, ps₂, hfr⟩ := finRange_split i
  obtain ⟨R0, hR0⟩ := C.wEvC_split i (hg i)
  obtain ⟨R1, hR1⟩ := C.wEvC_split i (hg' i)
  have hBeq : B = C.blocks ps₁ K ++ tag (C.rr i) (C.wEvC i k) ++ C.blocks ps₂ K := by
    simp [B, K, hfr, blocks_append, blocks_cons]
  set T := tag C.a (C.aEv g') ++ tag C.b (C.bEvPre g (C.mg g')) ++
    [(C.b, rd C.y ry'), (C.b, rd (C.x i) rx')]
  have hE2T : E2 = B ++ T := by simp [E2, T]
  obtain ⟨h0l, h0⟩ := getElem_of_eq (l := E2)
    (l₁ := C.blocks ps₁ K ++ tag (C.rr i) (C.wEvC i (g i))) (x := (C.rr i, C.wEvt i (g i)))
    (l₂ := tag (C.rr i) R0 ++ C.blocks ps₂ K ++ T) (by rw [hE2T, hBeq, hR0]; simp)
  obtain ⟨h1l, h1⟩ := getElem_of_eq (l := E2)
    (l₁ := C.blocks ps₁ K ++ tag (C.rr i) (C.wEvC i (g' i))) (x := (C.rr i, C.wEvt i (g' i)))
    (l₂ := tag (C.rr i) R1 ++ C.blocks ps₂ K ++ T) (by rw [hE2T, hBeq, hR1]; simp)
  obtain ⟨h2l, h2⟩ := getElem_of_eq (l := E2) (l₁ := B ++ tag C.a E₁)
    (x := (C.a, .do_ ⟨C.x i, .read, .vals {C.val i (g' i)}⟩))
    (l₂ := tag C.a E₂ ++ tag C.a [.do_ ⟨C.y, .write C.one, C.aResp g'⟩, .send (C.mg g')] ++
      tag C.b (C.bEvPre g (C.mg g')) ++ [(C.b, rd C.y ry'), (C.b, rd (C.x i) rx')])
    (by rw [hE2T]; simp [T, aEv, hE₁])
  obtain ⟨h3l, h3⟩ := getElem_of_eq (l := E2) (l₁ := B ++ tag C.a (C.aEvPre g'))
    (x := (C.a, .do_ ⟨C.y, .write C.one, C.aResp g'⟩))
    (l₂ := (C.a, .send (C.mg g')) :: tag C.b (C.bEvPre g (C.mg g')) ++
      [(C.b, rd C.y ry'), (C.b, rd (C.x i) rx')])
    (by rw [hE2T]; simp [T, aEv])
  obtain ⟨h4l, h4⟩ := getElem_of_eq (l := E2)
    (l₁ := B ++ tag C.a (C.aEv g') ++ tag C.b (C.bEvPre g (C.mg g')))
    (x := (C.b, rd C.y ry')) (l₂ := [(C.b, rd (C.x i) rx')]) (by simp [E2])
  obtain ⟨h5l, h5⟩ := getElem_of_eq (l := E2)
    (l₁ := B ++ tag C.a (C.aEv g') ++ tag C.b (C.bEvPre g (C.mg g')) ++ [(C.b, rd C.y ry')])
    (x := (C.b, rd (C.x i) rx')) (l₂ := []) (by simp [E2])
  have hP01 : (C.blocks ps₁ K ++ tag (C.rr i) (C.wEvC i (g i))).length <
      (C.blocks ps₁ K ++ tag (C.rr i) (C.wEvC i (g' i))).length := by
    simp only [List.length_append, length_tag, length_wEvC]; omega
  have hP23 : (B ++ tag C.a E₁).length < (B ++ tag C.a (C.aEvPre g')).length := by
    simp [hE₁]
  have hP45 : (B ++ tag C.a (C.aEv g') ++ tag C.b (C.bEvPre g (C.mg g'))).length <
      (B ++ tag C.a (C.aEv g') ++ tag C.b (C.bEvPre g (C.mg g')) ++ [(C.b, rd C.y ry')]).length := by
    simp
  obtain ⟨d0, r0, e0⟩ := hOn.atL h0l h0
  obtain ⟨d1, r1, e1⟩ := hOn.atL h1l h1
  obtain ⟨d2, r2, e2⟩ := hOn.atL h2l h2
  obtain ⟨d3, r3, e3⟩ := hOn.atL h3l h3
  obtain ⟨d4, r4, e4⟩ := hOn.atL h4l h4
  obtain ⟨d5, r5, e5⟩ := hOn.atL h5l h5
  rw [hry] at e4
  rw [hrx] at e5
  -- `⟨g' i, i⟩ →vis r^i` at `a`, hence `→vis w_y`
  have v12 := (hret _ _ _ _ _ h1l _ _ _ d2 e2 rfl h1).1.1
  have v13 := hWF.vis_mono v12 (hOn.2.2 _ _ d2 d3 (by rw [r2, r3]) hP23) (by rw [r2, r3])
  -- `w_y →vis r_y` at `b`
  have v34 := (hret _ _ _ _ _ h3l _ _ _ d4 e4 rfl h3).1.1
  have v14 := hTr _ _ _ v13 v34
  have v15 := hWF.vis_mono v14 (hOn.2.2 _ _ d4 d5 (by rw [r4, r5]) hP45) (by rw [r4, r5])
  -- `r_x` returns `⟨g i, i⟩`, which is overwritten by `⟨g' i, i⟩`
  have hmax := (hret _ _ _ _ _ h0l _ _ _ d5 e5 rfl h0).2
  have hP1ctx := (⟨v15, by rw [e1, e5], _, by rw [e1]⟩ :
    (C.blocks ps₁ K ++ tag (C.rr i) (C.wEvC i (g' i))).length ∈ A.ctxW
      (B ++ tag C.a (C.aEv g') ++ tag C.b (C.bEvPre g (C.mg g')) ++ [(C.b, rd C.y ry')]).length)
  exact hmax _ hP1ctx (hWF.vis_sess (hOn.2.2 _ _ d0 d1 (by rw [r0, r1]) hP01) (by rw [r0, r1]))

/-- `m_g` determines `g`. -/
theorem mg_injective [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P)
    (hCC : C.D.CausallyConsistent) (k : ℕ) :
    Function.Injective fun g : Fin n' → Fin k => C.mg fun p => (g p : ℕ) := by
  intro g g' hm
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hi) with h | h
  · exact key H hCC (fun p => (g p).2) (fun p => (g' p).2) h hm
  · exact key H hCC (fun p => (g' p).2) (fun p => (g p).2) h hm.symm

/-- The execution `α_g` ends with `a` broadcasting `m_g`. -/
theorem αB_exec [Fintype ι] {P : AE ι Obj V → Prop} (H : C.Good P) (g : Fin n' → ℕ) :
    C.D.IsExec (C.αB g) ∧ (C.a, .send (C.mg g)) ∈ C.αB g := by
  set J : Fin n' → ℕ := fun p => g p + 1
  obtain ⟨hB, -, -⟩ := blocks_exec H (List.nodup_finRange n') J
  have hsent : ∀ p j, j ≤ g p → (C.rr p, .send (C.msg p j)) ∈ C.blocks (List.finRange n') J :=
    fun p j hj => send_mem_blocks (List.mem_finRange p) (by simp [J]; omega)
  obtain ⟨hA, -⟩ := a_full_exec H hB (C.state_blocks_a _ _) hsent
  have hmg : (C.a, .send (C.mg g)) ∈ C.blocks (List.finRange n') J ++ tag C.a (C.aEv g) :=
    List.mem_append_right _ (mem_tag.2 ⟨rfl, by simp [aEv]⟩)
  obtain ⟨hE, -⟩ := b_exec (g := g) hA
    (by rw [state_append_of_not_mem _ _ _ (tag_not_mem C.a_ne_b.symm)]
        exact C.state_blocks_b _ _)
    (fun p j hj => List.mem_append_left _ (hsent p j hj)) hmg
  exact ⟨hE, List.mem_append_left _ hmg⟩

end Cx

/-- Counting: an injective map from a type with `N ≥ 1` elements to bit strings takes a value of
length at least `⌊lg N⌋`. -/
lemma exists_le_length {α : Type*} [Fintype α] (f : α → List Bool) (hf : Function.Injective f)
    (hN : 0 < Fintype.card α) : ∃ a, Nat.log 2 (Fintype.card α) ≤ (f a).length := by
  by_contra hcon
  push_neg at hcon
  set L := Nat.log 2 (Fintype.card α)
  set T : Finset (List Bool) := (Finset.range L).biUnion fun n =>
    (Finset.univ : Finset (List.Vector Bool n)).image List.Vector.toList
  have hmem : ∀ a, f a ∈ T := fun a => by
    refine Finset.mem_biUnion.2 ⟨(f a).length, Finset.mem_range.2 (hcon a), ?_⟩
    rw [Finset.mem_image]
    exact ⟨⟨f a, rfl⟩, Finset.mem_univ _, rfl⟩
  have h1 : Fintype.card α ≤ T.card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card_of_injOn f (fun a _ => hmem a) hf.injOn
  have h2 : T.card ≤ ∑ n ∈ Finset.range L, 2 ^ n := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun n _ => ?_)
    refine Finset.card_image_le.trans ?_
    exact (Finset.card_univ (α := List.Vector Bool n)).trans_le
      (by rw [card_vector, Fintype.card_bool])
  have h3 : ∀ L, ∑ n ∈ Finset.range L, 2 ^ n < 2 ^ L := by
    intro L
    induction L with
    | zero => simp
    | succ L ih => rw [Finset.sum_range_succ, pow_succ]; omega
  have h4 : 2 ^ L ≤ Fintype.card α := Nat.pow_log_le_self 2 hN.ne'
  have := h3 L
  omega

/-- **Theorem 12 of [AEM15].** Let `D` be a causally consistent and eventually consistent data
store with invisible reads and op-driven messages, on `n ≥ 3` replicas and `s ≥ 2` MVRs, whose
messages are bit strings (`enc` injective). Then for every `k ≥ 1` some execution sends a message
of at least `⌊n' lg k⌋` bits, `n' = min (n - 2, s - 1)`. -/
theorem theorem12 [Fintype ι] [Fintype Obj] [Infinite V] {D : Store ι Obj V M St}
    {P : AE ι Obj V → Prop} (hCC : D.CausallyConsistent) (hEC : D.EventuallyConsistent P)
    (hIR : D.InvisibleReads) (hOD : D.OpDriven) (hSC : D.SendClears) (hAv : D.Available)
    (hRecv : D.RecvEnabled) (enc : M → List Bool) (henc : Function.Injective enc)
    (hn : 3 ≤ Fintype.card ι) (hs : 2 ≤ Fintype.card Obj) {k : ℕ} (hk : 0 < k) :
    ∃ α, D.IsExec α ∧ ∃ i m, (i, Ev.send m) ∈ α ∧
      Nat.log 2 (k ^ min (Fintype.card ι - 2) (Fintype.card Obj - 1)) ≤ (enc m).length := by
  set n := Fintype.card ι
  set s := Fintype.card Obj
  set n' := min (n - 2) (s - 1)
  set eι := Fintype.equivFin ι
  set eO := Fintype.equivFin Obj
  set emb := Infinite.natEmbedding V
  have hn' : n' ≤ n - 2 := min_le_left _ _
  have hs' : n' ≤ s - 1 := min_le_right _ _
  let C : Cx ι Obj V M St n' :=
    { D := D, hAv := hAv, hRecv := hRecv
      rr := fun p => eι.symm ⟨p, by omega⟩
      x := fun p => eO.symm ⟨p, by omega⟩
      val := fun p j => emb (Nat.pair p j + 1)
      a := eι.symm ⟨n - 2, by omega⟩
      b := eι.symm ⟨n - 1, by omega⟩
      y := eO.symm ⟨s - 1, by omega⟩
      one := emb 0
      rr_inj := fun p q h => by
        have := congrArg Fin.val (eι.symm.injective h); exact Fin.ext this
      a_ne_b := fun h => by have := congrArg Fin.val (eι.symm.injective h); simp at this; omega
      rr_ne_a := fun p h => by
        have := congrArg Fin.val (eι.symm.injective h); simp at this; omega
      rr_ne_b := fun p h => by
        have := congrArg Fin.val (eι.symm.injective h); simp at this; omega
      x_inj := fun p q h => by
        have := congrArg Fin.val (eO.symm.injective h); exact Fin.ext this
      x_ne_y := fun p h => by
        have := congrArg Fin.val (eO.symm.injective h); simp at this; omega
      val_inj := fun p j p' j' h => by
        have h' := emb.injective h
        simp only [add_left_inj] at h'
        have := Nat.pair_eq_pair.1 h'
        exact ⟨Fin.ext this.1, this.2⟩
      val_ne_one := fun p j h => by have := emb.injective h; omega }
  have H : C.Good P := ⟨hEC, hIR, hOD, hSC⟩
  -- messages exist
  have : Nonempty M := by
    obtain ⟨r, σw, hw⟩ := hAv C.a (D.init C.a) C.y (.write C.one)
    obtain ⟨m, -⟩ := lemma5 hEC hIR hOD hAv hRecv C.a_ne_b (α := []) .nil rfl hw
      (by simp) (by simp) (fun i σ h => by cases h; exact hOD.1 i) (by simp)
    exact ⟨m⟩
  obtain ⟨g, hg⟩ := exists_le_length (fun g : Fin n' → Fin k => enc (C.mg fun p => (g p : ℕ)))
    (henc.comp (Cx.mg_injective H hCC k)) (by simp; positivity)
  obtain ⟨hE, hmem⟩ := Cx.αB_exec H fun p => (g p : ℕ)
  refine ⟨_, hE, _, _, hmem, ?_⟩
  simpa [Fintype.card_fun] using hg

end Podc.EventualConsistencyLimits
