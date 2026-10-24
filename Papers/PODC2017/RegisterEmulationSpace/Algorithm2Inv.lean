import Papers.PODC2017.RegisterEmulationSpace.Algorithm2

/-!
# Algorithm 2: step specifications and the generic per-client invariant

`ActSpec` describes the possible steps of a client, `CI` is an invariant of every client in every
run (relating the bookkeeping sets `pw, q, wr, cov` to the pending low-level operations).
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

variable {C B S V : Type*} [DecidableEq C] [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

/-- The possible steps of a client with write set `Rc`. -/
inductive ActSpec (δ : B → S) (f : ℕ) (Rc : Finset B) : Loc B V → Act B (ℕ × V) V → Loc B V → Prop
  | trigW (l : Loc B V) (b : B) : b ∈ l.q →
      ActSpec δ f Rc l (.trig b (.write (l.ts, l.val))) { l with q := l.q.erase b, pw := insert b l.pw }
  | trigR (l : Loc B V) (b : B) : l.q = ∅ → l.mode.isColl → b ∈ l.rq →
      ActSpec δ f Rc l (.trig b .read) { l with rq := l.rq.erase b }
  | retR (l : Loc B V) : l.q = ∅ → l.mode = .rd → l.rq = ∅ → Done δ f l.got →
      ActSpec δ f Rc l (.ret l.best.2) { l with mode := .idle }
  | toWp (l : Loc B V) (v : V) : l.q = ∅ → l.mode = .wc v → l.rq = ∅ → Done δ f l.got →
      ActSpec δ f Rc l .skip { l with ts := l.best.1 + 1, val := v, cov := l.pw, wr := ∅,
                                      q := Rc \ l.pw, mode := .wp }
  | retW (l : Loc B V) : l.q = ∅ → l.mode = .wp → #Rc ≤ #l.wr + f →
      ActSpec δ f Rc l (.ret l.val) { l with mode := .idle }
  | skip (l : Loc B V) : l.q = ∅ → (l.mode.isColl → l.rq = ∅ ∧ ¬ Done δ f l.got) →
      (l.mode = .wp → ¬ #Rc ≤ #l.wr + f) → ActSpec δ f Rc l .skip l

variable (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V)

lemma act_spec (c : C) (l : Loc B V) :
    ActSpec δ f (R c) l ((alg δ f R v₀).act c l).1 ((alg δ f R v₀).act c l).2 := by
  simp only [alg]
  rcases hq : pick l.q with _ | b
  · have hq' := pick_eq_none hq
    simp only [afterQ]
    rcases hm : l.mode with _ | _ | v | _ <;> dsimp only
    · exact ActSpec.skip l hq' (by simp [hm]) (by simp [hm])
    · rcases hr : pick l.rq with _ | b <;> dsimp only
      · split_ifs with hd
        · exact ActSpec.retR l hq' hm (pick_eq_none hr) hd
        · exact ActSpec.skip l hq' (fun _ => ⟨pick_eq_none hr, hd⟩) (by simp [hm])
      · have h := ActSpec.trigR (δ := δ) (f := f) (Rc := R c) l b hq' (by simp [hm]) (pick_mem hr)
        rw [hm] at h; exact h
    · rcases hr : pick l.rq with _ | b <;> dsimp only
      · split_ifs with hd
        · exact ActSpec.toWp l v hq' hm (pick_eq_none hr) hd
        · exact ActSpec.skip l hq' (fun _ => ⟨pick_eq_none hr, hd⟩) (by simp [hm])
      · have h := ActSpec.trigR (δ := δ) (f := f) (Rc := R c) l b hq' (by simp [hm]) (pick_mem hr)
        rw [hm] at h; exact h
    · split_ifs with hd
      · exact ActSpec.retW l hq' hm hd
      · exact ActSpec.skip l hq' (by simp [hm]) (fun _ => hd)
  · exact ActSpec.trigW l b (pick_mem hq)

/-- Mode and pending high-level operation agree. -/
def ModeOK : Option (HOp V) → Mode V → Prop
  | none, .idle => True
  | some .read, .rd => True
  | some (.write v), .wc v' => v = v'
  | some (.write _), .wp => True
  | _, _ => False

lemma ModeOK.none_iff {o : Option (HOp V)} {m : Mode V} (h : ModeOK o m) :
    o = none ↔ m = .idle := by
  rcases o with _ | _ | _ <;> rcases m with _ | _ | _ | _ <;> simp_all [ModeOK]

/-- The generic invariant of a client with write set `Rc`, local state `l`, pending low-level
operations `P` and pending high-level operation `o`. -/
structure CI (Rc : Finset B) (f : ℕ) (l : Loc B V) (P : List (POp B (ℕ × V)))
    (o : Option (HOp V)) : Prop where
  mode : ModeOK o l.mode
  part : l.pw ∪ l.q ∪ l.wr = Rc
  dpq : Disjoint l.pw l.q
  dpw : Disjoint l.pw l.wr
  dqw : Disjoint l.q l.wr
  cov : l.cov ⊆ l.pw
  pw : ∀ b, b ∈ l.pw ↔ ∃ p ∈ P, p.reg = b ∧ p.op.IsWrite
  uniq : ∀ p ∈ P, ∀ p' ∈ P, p.op.IsWrite → p'.op.IsWrite → p.reg = p'.reg → p = p'
  coll : l.mode.isColl → ∀ b, b ∈ l.rq ∨ b ∈ l.got ∨ ∃ p ∈ P, p.reg = b ∧ p.op = .read
  fwr : l.mode ≠ .wp → #Rc ≤ #l.wr + f

namespace CI

variable {Rc : Finset B} {f : ℕ} {l : Loc B V} {P : List (POp B (ℕ × V))} {o : Option (HOp V)}

lemma pw_sub (h : CI Rc f l P o) : l.pw ⊆ Rc := fun b hb => h.part ▸ by simp [hb]
lemma q_sub (h : CI Rc f l P o) : l.q ⊆ Rc := fun b hb => h.part ▸ by simp [hb]
lemma wr_sub (h : CI Rc f l P o) : l.wr ⊆ Rc := fun b hb => h.part ▸ by simp [hb]

/-- The registers covered (or about to be rewritten) by the client: `Rc` minus `wrSet`. -/
lemma card_U (h : CI Rc f l P o) : #(l.pw ∪ l.q) + #l.wr = #Rc := by
  rw [← h.part, card_union_of_disjoint (disjoint_union_left.2 ⟨h.dpw, h.dqw⟩),
    card_union_of_disjoint h.dpq]

/-- Observation 3: a client that is not in its write phase covers at most `f` registers. -/
lemma card_U_le (h : CI Rc f l P o) (hm : l.mode ≠ .wp) : #(l.pw ∪ l.q) ≤ f := by
  have := h.card_U; have := h.fwr hm; omega

lemma mem_pw_of (h : CI Rc f l P o) {p : POp B (ℕ × V)} (hp : p ∈ P) (hw : p.op.IsWrite) :
    p.reg ∈ l.pw := (h.pw _).2 ⟨p, hp, rfl, hw⟩

/-- Invocation. -/
lemma invoke (h : CI Rc f l P none) (op : HOp V) :
    CI Rc f ((alg δ f R v₀).invoke c op l) P (some op) := by
  have hm : l.mode = .idle := (h.mode.none_iff).1 rfl
  simp only [alg, hm]
  rcases op with _ | v
  · exact { h with
      mode := by simp [startCollect, ModeOK]
      coll := fun _ b => Or.inl (by simp [startCollect])
      fwr := fun _ => h.fwr (by simp [hm]) }
  · exact { h with
      mode := by simp [startCollect, ModeOK]
      coll := fun _ b => Or.inl (by simp [startCollect])
      fwr := fun _ => h.fwr (by simp [hm]) }

/-- A step of the client. -/
lemma step {l' : Loc B V} {a : Act B (ℕ × V) V} (h : CI Rc f l P o) (hs : ActSpec δ f Rc l a l')
    (n : ℕ) :
    CI Rc f l' (match a with | .trig b op => P ++ [⟨n, b, op⟩] | _ => P)
      (match a with | .ret _ => none | _ => o) := by
  cases hs with
  | trigW b hb =>
    have hbpw : b ∉ l.pw := fun h' => disjoint_left.1 h.dpq h' hb
    refine ⟨h.mode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.fwr⟩
    · rw [← h.part]; ext x; simp only [mem_union, mem_insert, mem_erase]
      by_cases hx : x = b <;> simp [hx, hb]
    · simp only [disjoint_insert_left, mem_erase, ne_eq, not_true_eq_false, false_and,
        not_false_eq_true, true_and]
      exact disjoint_of_subset_right (erase_subset _ _) h.dpq
    · simp only [disjoint_insert_left]
      exact ⟨fun h' => disjoint_left.1 h.dqw hb h', h.dpw⟩
    · exact disjoint_of_subset_left (erase_subset _ _) h.dqw
    · exact h.cov.trans (subset_insert _ _)
    · intro x
      simp only [mem_insert, h.pw, List.mem_append, List.mem_singleton]
      constructor
      · rintro (rfl | ⟨p, hp, h1, h2⟩)
        · exact ⟨_, Or.inr rfl, rfl, trivial⟩
        · exact ⟨p, Or.inl hp, h1, h2⟩
      · rintro ⟨p, hp | rfl, h1, h2⟩
        · exact Or.inr ⟨p, hp, h1, h2⟩
        · exact Or.inl h1.symm
    · intro p hp p' hp' hw hw' hr
      simp only [List.mem_append, List.mem_singleton] at hp hp'
      rcases hp with hp | rfl <;> rcases hp' with hp' | rfl
      · exact h.uniq p hp p' hp' hw hw' hr
      · exact absurd (by simpa [hr] using h.mem_pw_of hp hw) hbpw
      · exact absurd (by simpa [← hr] using h.mem_pw_of hp' hw') hbpw
      · rfl
    · intro hc x
      rcases h.coll hc x with h1 | h1 | ⟨p, hp, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨p, List.mem_append_left _ hp, h2, h3⟩)
  | trigR b hq hc hb =>
    refine ⟨h.mode, h.part, h.dpq, h.dpw, h.dqw, h.cov, ?_, ?_, ?_, h.fwr⟩
    · intro x
      simp only [h.pw, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, Or.inl hp, h1, h2⟩
      · rintro ⟨p, hp | rfl, h1, h2⟩
        · exact ⟨p, hp, h1, h2⟩
        · exact absurd h2 (by simp)
    · intro p hp p' hp' hw hw' hr
      simp only [List.mem_append, List.mem_singleton] at hp hp'
      rcases hp with hp | rfl
      · rcases hp' with hp' | rfl
        · exact h.uniq p hp p' hp' hw hw' hr
        · exact absurd hw' (by simp)
      · exact absurd hw (by simp)
    · intro _ x
      by_cases hx : x = b
      · subst hx; exact Or.inr (Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩)
      · rcases h.coll hc x with h1 | h1 | ⟨p, hp, h2, h3⟩
        · exact Or.inl (mem_erase.2 ⟨hx, h1⟩)
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr ⟨p, List.mem_append_left _ hp, h2, h3⟩)
  | retR hq hm hr hd =>
    refine { h with mode := ?_, coll := by simp, fwr := fun _ => h.fwr (by rw [hm]; simp) }
    simp [ModeOK]
  | toWp v hq hm hr hd =>
    have hpw := h.pw_sub
    refine ⟨?_, ?_, disjoint_sdiff, disjoint_empty_right _, disjoint_empty_right _, subset_rfl, h.pw,
      h.uniq, by simp, by simp⟩
    · have := h.mode; rw [hm] at this
      rcases o with _ | _ | _ <;> simp_all [ModeOK]
    · simp [union_sdiff_of_subset hpw]
  | retW hq hm hc =>
    refine { h with mode := ?_, coll := by simp, fwr := fun _ => hc }
    simp [ModeOK]
  | skip _ _ _ => exact h

/-- Response to a pending read `p`. -/
lemma respRead {P' : List (POp B (ℕ × V))} {p : POp B (ℕ × V)} (h : CI Rc f l P o)
    (hp : p ∈ P) (hpr : p.op = .read) (hP' : ∀ x, x ∈ P' ↔ x ∈ P ∧ x ≠ p) (w : ℕ × V) :
    CI Rc f (recvRead l p.reg w) P' o := by
  have hpw : ∀ b, b ∈ l.pw ↔ ∃ x ∈ P', x.reg = b ∧ x.op.IsWrite := by
    intro b; rw [h.pw]
    constructor
    · rintro ⟨x, hx, h1, h2⟩
      exact ⟨x, (hP' x).2 ⟨hx, by rintro rfl; simp [hpr] at h2⟩, h1, h2⟩
    · rintro ⟨x, hx, h1, h2⟩; exact ⟨x, ((hP' x).1 hx).1, h1, h2⟩
  have huniq : ∀ x ∈ P', ∀ x' ∈ P', x.op.IsWrite → x'.op.IsWrite → x.reg = x'.reg → x = x' :=
    fun x hx x' hx' => h.uniq x ((hP' x).1 hx).1 x' ((hP' x').1 hx').1
  by_cases hc : l.mode.isColl
  · simp only [recvRead, hc, ite_true]
    refine ⟨h.mode, h.part, h.dpq, h.dpw, h.dqw, h.cov, hpw, huniq, ?_, h.fwr⟩
    intro _ b
    rcases h.coll hc b with h1 | h1 | ⟨x, hx, h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl (mem_insert_of_mem h1))
    · by_cases hxp : x = p
      · subst hxp; exact Or.inr (Or.inl (h2 ▸ mem_insert_self _ _))
      · exact Or.inr (Or.inr ⟨x, (hP' x).2 ⟨hx, hxp⟩, h2, h3⟩)
  · simp only [recvRead, hc]
    exact ⟨h.mode, h.part, h.dpq, h.dpw, h.dqw, h.cov, hpw, huniq, fun h' => absurd h' hc, h.fwr⟩

/-- Response to a pending write `p`. -/
lemma respWrite {P' : List (POp B (ℕ × V))} {p : POp B (ℕ × V)} (h : CI Rc f l P o)
    (hp : p ∈ P) (hpw : p.op.IsWrite) (hP' : ∀ x, x ∈ P' ↔ x ∈ P ∧ x ≠ p) :
    CI Rc f (recvWrite l p.reg) P' o := by
  have hb := h.mem_pw_of hp hpw
  have hbq : p.reg ∉ l.q := fun h' => disjoint_left.1 h.dpq hb h'
  have hbw : p.reg ∉ l.wr := fun h' => disjoint_left.1 h.dpw hb h'
  have hpw' : ∀ b, b ∈ l.pw.erase p.reg ↔ ∃ x ∈ P', x.reg = b ∧ x.op.IsWrite := by
    intro b; rw [mem_erase, h.pw]
    constructor
    · rintro ⟨hne, x, hx, h1, h2⟩
      exact ⟨x, (hP' x).2 ⟨hx, by rintro rfl; exact hne h1.symm⟩, h1, h2⟩
    · rintro ⟨x, hx, h1, h2⟩
      obtain ⟨hx, hxp⟩ := (hP' x).1 hx
      refine ⟨?_, x, hx, h1, h2⟩
      rintro rfl
      exact hxp (h.uniq x hx p hp h2 hpw h1)
  have huniq : ∀ x ∈ P', ∀ x' ∈ P', x.op.IsWrite → x'.op.IsWrite → x.reg = x'.reg → x = x' :=
    fun x hx x' hx' => h.uniq x ((hP' x).1 hx).1 x' ((hP' x').1 hx').1
  have hcoll : l.mode.isColl → ∀ b, b ∈ l.rq ∨ b ∈ l.got ∨ ∃ x ∈ P', x.reg = b ∧ x.op = .read := by
    intro hc b
    rcases h.coll hc b with h1 | h1 | ⟨x, hx, h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨x, (hP' x).2 ⟨hx, by rintro rfl; simp [h3] at hpw⟩, h2, h3⟩)
  unfold recvWrite
  split_ifs with hc
  · refine ⟨h.mode, ?_, ?_, ?_, ?_, ?_, hpw', huniq, hcoll, h.fwr⟩
    · rw [← h.part]; ext x; simp only [mem_union, mem_insert, mem_erase]
      by_cases hx : x = p.reg <;> simp [hx, hb]
    · rw [disjoint_insert_right]
      exact ⟨by simp, disjoint_of_subset_left (erase_subset _ _) h.dpq⟩
    · exact disjoint_of_subset_left (erase_subset _ _) h.dpw
    · rw [disjoint_insert_left]; exact ⟨hbw, h.dqw⟩
    · exact erase_subset_erase _ h.cov
  · refine ⟨h.mode, ?_, ?_, ?_, ?_, ?_, hpw', huniq, hcoll, ?_⟩
    · rw [← h.part]; ext x; simp only [mem_union, mem_insert, mem_erase]
      by_cases hx : x = p.reg <;> simp [hx, hb]
    · exact disjoint_of_subset_left (erase_subset _ _) h.dpq
    · rw [disjoint_insert_right]
      exact ⟨by simp, disjoint_of_subset_left (erase_subset _ _) h.dpw⟩
    · rw [disjoint_insert_right]; exact ⟨hbq, h.dqw⟩
    · intro x hx; exact mem_erase.2 ⟨fun h' => hc (h' ▸ hx), h.cov hx⟩
    · intro hm; exact (h.fwr hm).trans (by have := card_le_card (subset_insert p.reg l.wr); simp only at this ⊢; omega)

end CI

/-- The generic invariant of all reachable configurations. -/
def GI (X : Cfg C B V (ℕ × V) (Loc B V)) : Prop :=
  WF X ∧ ∀ c, CI (R c) f (X.loc c) (X.pend c) (X.cur c)

/-- The step of client `d` as a function of its action `a` and new local state `l'`. -/
lemma doStep_eq (X : Cfg C B V (ℕ × V) (Loc B V)) (d : C) :
    (alg δ f R v₀).doStep X d =
      match ((alg δ f R v₀).act d (X.loc d)).1 with
      | .trig b o => { X with loc := update X.loc d ((alg δ f R v₀).act d (X.loc d)).2,
                              pend := update X.pend d (X.pend d ++ [⟨X.cnt d, b, o⟩]),
                              cnt := update X.cnt d (X.cnt d + 1) }
      | .ret x =>
        match X.cur d with
        | some _ => { X with loc := update X.loc d ((alg δ f R v₀).act d (X.loc d)).2,
                             cur := update X.cur d none, hist := X.hist ++ [.ret d x] }
        | none => { X with loc := update X.loc d ((alg δ f R v₀).act d (X.loc d)).2 }
      | .skip => { X with loc := update X.loc d ((alg δ f R v₀).act d (X.loc d)).2 } := by
  unfold Alg.doStep
  rcases ((alg δ f R v₀).act d (X.loc d)).1 with ⟨b, o⟩ | x | _
  · rfl
  · rcases X.cur d <;> rfl
  · rfl

lemma gi_init : GI f R (alg δ f R v₀).initCfg := by
  refine ⟨(alg δ f R v₀).wf_init, fun c => ?_⟩
  refine ⟨by simp [Alg.initCfg, alg, ModeOK], by simp [Alg.initCfg, alg], by simp [Alg.initCfg, alg],
    by simp [Alg.initCfg, alg], by simp [Alg.initCfg, alg], by simp [Alg.initCfg, alg],
    by simp [Alg.initCfg, alg], by simp [Alg.initCfg], by simp [Alg.initCfg, alg],
    by simp [Alg.initCfg, alg]⟩

lemma gi_step {X : Cfg C B V (ℕ × V) (Loc B V)} (h : GI f R X) (e : Ev C V) :
    GI f R ((alg δ f R v₀).step X e) := by
  refine ⟨(alg δ f R v₀).wf_step h.1 e, fun c => ?_⟩
  cases e with
  | inv d o =>
    by_cases hcd : c = d
    · subst hcd
      simp only [Alg.step_inv, Alg.doInv]
      split_ifs with hcur
      · simp only [update_self]
        exact (hcur ▸ h.2 c).invoke δ R v₀ o
      · exact h.2 c
    · obtain ⟨h1, h2, h3, -⟩ := (alg δ f R v₀).doInv_other X o hcd
      simp only [Alg.step_inv, h1, h2, h3]; exact h.2 c
  | step d =>
    by_cases hcd : c = d
    · subst hcd
      have hs := act_spec δ f R v₀ c (X.loc c)
      have hci := (h.2 c).step δ hs (X.cnt c)
      simp only [Alg.step_step, doStep_eq]
      generalize ((alg δ f R v₀).act c (X.loc c)).1 = a at hs hci ⊢
      generalize ((alg δ f R v₀).act c (X.loc c)).2 = l' at hs hci ⊢
      rcases a with ⟨b, o⟩ | x | _
      · simpa using hci
      · rcases hcur : X.cur c with _ | o
        · simpa [hcur] using hci
        · simpa using hci
      · simpa using hci
    · obtain ⟨h1, h2, h3, -⟩ := (alg δ f R v₀).step_other X (e := .step d) rfl hcd
      rw [h1, h2, h3]; exact h.2 c
  | resp d n =>
    by_cases hcd : c = d
    · subst hcd
      simp only [Alg.step_resp, Alg.doResp]
      split
      · exact h.2 c
      · rename_i p hp
        have hpm := List.mem_of_find?_eq_some hp
        have hP' := fun x => Alg.mem_filter_ne (q := x) h.1 hpm
        unfold Alg.apply
        rcases hop : p.op with _ | w
        · simpa [alg, hop] using (h.2 c).respRead hpm hop hP' _
        · simpa [alg, hop] using (h.2 c).respWrite hpm (by simp [hop]) hP'
    · obtain ⟨h1, h2, h3, -⟩ := (alg δ f R v₀).step_other X (e := .resp d n) rfl hcd
      rw [h1, h2, h3]; exact h.2 c

lemma gi_exec {X : Cfg C B V (ℕ × V) (Loc B V)} (h : GI f R X) (E : List (Ev C V)) :
    GI f R ((alg δ f R v₀).exec X E) := by
  induction E generalizing X with
  | nil => exact h
  | cons e E ih => exact ih (gi_step δ f R v₀ h e)

lemma gi_run (E : List (Ev C V)) : GI f R ((alg δ f R v₀).run E) :=
  gi_exec δ f R v₀ (gi_init δ f R v₀) E

lemma gi_traj (ev : ℕ → Ev C V) (t : ℕ) : GI f R ((alg δ f R v₀).traj ev t) := by
  induction t with
  | zero => exact gi_init δ f R v₀
  | succ t ih => exact gi_step δ f R v₀ ih (ev t)

end Podc.RegisterEmulationSpace.Alg2
