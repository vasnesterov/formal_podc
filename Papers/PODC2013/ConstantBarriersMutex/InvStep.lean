import Papers.PODC2013.ConstantBarriersMutex.InvLocal

/-!
# Preservation of the invariant
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

theorem inv_init : Inv (Cfg.init : Cfg h) where
  loc q := by simp [LI, Cfg.init, Mem.init]
  hc q := by simp [HC, Cfg.init]
  lockRole g hg := by simp [Cfg.init, Mem.init] at hg
  uniq g₁ g₂ h₁ := by simp [Cfg.InCSX, Cfg.init, PC.Exit] at h₁
  sig q hq := by simp [Cfg.init, Mem.init] at hq
  nodup := by simp [lv, Cfg.init, Mem.init]
  pq q hq := by simp [lv, Cfg.init, Mem.init] at hq
  inpq q := by simp [lv, Cfg.init, Mem.init]
  q4 _ := rfl
  ex1 g hg := by simp [Cfg.init] at hg
  ex2 g v hv := by simp [Cfg.init] at hv
  ex3 _ := rfl
  ex4 g := by simp [Cfg.init]

/-! ### Helper lemmas -/

/-- Issuing the next doorway write. -/
lemma DoorLI_issue {s : Cfg h} {g : Proc h} {k : ℕ} {w : W h} {c' : PC h}
    (hD : DoorLI s g k) (hk : (doorList g)[k]? = some w) :
    DoorLI (s.loc g [w] c') g (k + 1) := by
  obtain ⟨i, hi, hb, h1, h2⟩ := hD
  refine ⟨i, by omega, ?_, h1, h2⟩
  rw [loc_buf_self, hb, take_succ_doorList g hk, List.drop_append_of_le_length]
  have : ((doorList g).take k).length = k := by
    rw [List.length_take]; have := (List.getElem?_eq_some_iff.1 hk).1; omega
  omega

lemma lv_loc_holder {s : Cfg h} (hI : Inv s) {g : Proc h} {ws : List (W h)} {c' : PC h}
    (hg : Holds s g) (hws : ∀ w ∈ ws, w.isPromQ = false ∧ ∀ r, w.isInPromQ r = false) :
    (lv (s.loc g ws c')).promQ = (lv s).promQ ∧
      ∀ r, (lv (s.loc g ws c')).inPromQ r = (lv s).inPromQ r := by
  unfold lv
  simp only [loc_mem, hI.holds_lock hg]
  rw [loc_buf_self, Mem.view_append]
  exact ⟨view_promQ_of (fun w hw => (hws w hw).1),
    fun r => view_inPromQ_of (fun w hw => (hws w hw).2 r)⟩

lemma lv_loc_holder_eq {s : Cfg h} (hI : Inv s) {g : Proc h} {ws : List (W h)} {c' : PC h}
    (hg : Holds s g) : lv (s.loc g ws c') = (s.view g).view ws := by
  unfold lv
  simp only [loc_mem, hI.holds_lock hg]
  rw [loc_buf_self, Mem.view_append]; rfl

lemma cas_fail {s : Cfg h} {g : Proc h} {c : PC h} (hb : s.buf g = []) (hl : s.mem.lock ≠ none) :
    s.cas g c = s.loc g [] c := by
  unfold Cfg.cas
  simp only [hb, Mem.view_nil, hl, if_false]
  simp [Cfg.loc, ← hb]

lemma view_of_nil {s : Cfg h} {g : Proc h} (hb : s.buf g = []) : s.view g = s.mem := by
  simp [Cfg.view, hb]

/-! ### Steps outside the critical and exit sections -/

/-- Discharges the routine side conditions of `inv_local_nh`. -/
macro "nh_tac" : tactic => `(tactic| first
  | done
  | (simp_all [Holds, Hands, Cfg.InCSX, PC.Exit, PC.Entry, NHW, loc_pc_self, loc_buf_self]; done)
  | skip)

lemma step_rem {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .rem) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have : s.stepProc g = s.loc g [.signal g false] .e18 := by
    simp [Cfg.stepProc, hp, issue_eq_loc]
  rw [this]
  apply inv_local_nh hI
  · unfold LI; rw [loc_pc_self]
    refine ⟨0, by omega, ?_, ?_, ?_⟩
    · rw [loc_buf_self, hL.1]; rfl
    · simp [hL.2]
    · intro h; omega
  all_goals nh_tac

lemma step_e18 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .e18) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have : s.stepProc g = s.loc g [.apply g true] (.e19 h) := by
    simp [Cfg.stepProc, hp, issue_eq_loc]
  rw [this]
  have hng : ¬ Holds s g := Inv.not_holds_of_entry (by simp [hp, PC.Entry])
  apply inv_local_nh hI
  · unfold LI; rw [loc_pc_self]
    refine ⟨le_rfl, ?_⟩
    have := DoorLI_issue (c' := .e19 h) hL (doorList_get1 g)
    simpa using this
  all_goals nh_tac

lemma step_e19 {s : Cfg h} (hI : Inv s) {g : Proc h} {l : ℕ} (hp : s.pc g = .e19 l) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hng : ¬ Holds s g := Inv.not_holds_of_entry (by simp [hp, PC.Entry])
  by_cases hl0 : l = 0
  · subst hl0
    have : s.stepProc g = s.loc g [.node (anc g 0) g] .e22 := by
      simp [Cfg.stepProc, hp, issue_eq_loc]
    rw [this]
    have hD := DoorLI_issue (c' := .e22) hL.2 (doorList_getNode g hL.1)
    apply inv_local_nh hI
    · unfold LI; rw [loc_pc_self]
      have : 2 + (h - 0) + 1 = h + 3 := by omega
      rw [this] at hD; exact hD
    all_goals nh_tac
  · have : s.stepProc g = s.loc g [.node (anc g l) g] (.e19 (l - 1)) := by
      simp [Cfg.stepProc, hp, issue_eq_loc, hl0]
    rw [this]
    have hD := DoorLI_issue (c' := .e19 (l - 1)) hL.2 (doorList_getNode g hL.1)
    apply inv_local_nh hI
    · unfold LI; rw [loc_pc_self]
      refine ⟨by omega, ?_⟩
      have : 2 + (h - (l - 1)) = 2 + (h - l) + 1 := by omega
      rw [this]; exact hD
    all_goals nh_tac

lemma barrier_flush {s : Cfg h} {g : Proc h} {c : PC h} (hb : s.buf g ≠ []) :
    s.barrier g c = s.flush g := by simp [Cfg.barrier, hb]

lemma barrier_goto {s : Cfg h} {g : Proc h} {c : PC h} (hb : s.buf g = []) :
    s.barrier g c = s.loc g [] c := by simp [Cfg.barrier, hb, goto_eq_loc]

/-- A step between two program counters of the waiting section (buffer empty). -/
lemma step_wait {s : Cfg h} (hI : Inv s) {g : Proc h} {c' : PC h}
    (hw : (s.pc g).Waiting ∨ s.pc g = .e23) (hc : c'.Waiting) :
    Inv (s.loc g [] c') := by
  have hL := hI.loc g
  have hE : (s.pc g).Entry := by
    rcases hw with hw | hw
    · revert hw; cases s.pc g <;> simp [PC.Waiting, PC.Entry]
    · rw [hw]; simp [PC.Entry]
  have hb : s.buf g = [] ∧ s.mem.apply g = true := by
    unfold LI at hL
    rcases hw with hw | hw
    · revert hw hL; cases s.pc g <;> simp [PC.Waiting]
    · rw [hw] at hL; exact hL
  have hcE : c'.Entry := by revert hc; cases c' <;> simp [PC.Waiting, PC.Entry]
  apply inv_local_nh hI
  · unfold LI; rw [loc_pc_self, loc_buf_self, hb.1]
    revert hc; cases c' <;> simp [PC.Waiting, hb.2]
  all_goals first
    | exact fun _ => hcE
    | exact fun _ => Or.inl hE
    | exact Inv.not_holds_of_entry hE
    | exact Inv.not_holds_of_entry (by rw [loc_pc_self]; exact hcE)
    | exact Inv.not_incsx_of_entry hE
    | exact Inv.not_incsx_of_entry (by rw [loc_pc_self]; exact hcE)
    | (intro nx hh; unfold Hands at hh; rcases hh with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
        first | (rw [h1] at hE; simp [PC.Entry] at hE) |
          (rw [loc_pc_self] at h1; rw [h1] at hcE; simp [PC.Entry] at hcE))
    | (refine ⟨?_, ?_, ?_⟩ <;> (revert hc; cases c' <;> simp [PC.Waiting, PC.Exit]))
    | (refine ⟨?_, ?_⟩ <;> (revert hE; cases s.pc g <;> simp [PC.Entry, PC.Exit]))
    | (simp; done)

lemma step_e22 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .e22) :
    Inv (s.stepProc g) := by
  have hst : s.stepProc g = s.barrier g .e23 := by simp [Cfg.stepProc, hp]
  rw [hst]
  by_cases hb : s.buf g = []
  · rw [barrier_goto hb]
    have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
    obtain ⟨i, hi, hbi, hap, -⟩ := hL
    have hi' : h + 3 ≤ i := by
      rw [hb] at hbi
      have := congrArg List.length hbi
      simp [doorList_length] at this; omega
    have hE : (s.pc g).Entry := by rw [hp]; simp [PC.Entry]
    apply inv_local_nh hI
    · unfold LI; rw [loc_pc_self, loc_buf_self, hb]; simp [hap.2 (by omega)]
    all_goals first
      | exact Inv.not_holds_of_entry hE
      | exact Inv.not_holds_of_entry (by rw [loc_pc_self]; simp [PC.Entry])
      | exact Inv.not_incsx_of_entry hE
      | exact Inv.not_incsx_of_entry (by rw [loc_pc_self]; simp [PC.Entry])
      | nh_tac
  · rw [barrier_flush hb]; exact inv_flush hI g

lemma step_cas_fail {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .e23 ∨ s.pc g = .e26)
    (hl : s.mem.lock ≠ none) : Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL
  have hb : s.buf g = [] := by rcases hp with hp | hp <;> rw [hp] at hL <;> exact hL.1
  rcases hp with hp | hp
  · have : s.stepProc g = s.loc g [] .e24 := by
      simp only [Cfg.stepProc, hp]; exact cas_fail hb hl
    rw [this]; exact step_wait hI (Or.inr hp) (by simp [PC.Waiting])
  · have : s.stepProc g = s.loc g [] .e27 := by
      simp only [Cfg.stepProc, hp]; exact cas_fail hb hl
    rw [this]; exact step_wait hI (Or.inl (by rw [hp]; simp [PC.Waiting])) (by simp [PC.Waiting])

lemma step_e24 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .e24) :
    Inv (s.stepProc g) := by
  have : s.stepProc g = s.loc g [] (.e25a (s.view g).exits) := by
    simp [Cfg.stepProc, hp, goto_eq_loc]
  rw [this]; exact step_wait hI (Or.inl (by rw [hp]; simp [PC.Waiting])) (by simp [PC.Waiting])

lemma step_e25a {s : Cfg h} (hI : Inv s) {g : Proc h} {e : ℕ} (hp : s.pc g = .e25a e) :
    Inv (s.stepProc g) := by
  have : s.stepProc g = s.loc g []
      (if e + 2 ≤ (s.view g).exits then .e26 else .e25b e) := by
    simp [Cfg.stepProc, hp, goto_eq_loc]
  rw [this]
  exact step_wait hI (Or.inl (by rw [hp]; simp [PC.Waiting])) (by split_ifs <;> simp [PC.Waiting])

lemma step_e25b {s : Cfg h} (hI : Inv s) {g : Proc h} {e : ℕ} (hp : s.pc g = .e25b e) :
    Inv (s.stepProc g) := by
  have : s.stepProc g = s.loc g []
      (if (s.view g).lock = some g ∨ (s.view g).lock = none then .e26 else .e25a e) := by
    simp [Cfg.stepProc, hp, goto_eq_loc]
  rw [this]
  exact step_wait hI (Or.inl (by rw [hp]; simp [PC.Waiting])) (by split_ifs <;> simp [PC.Waiting])

lemma step_x50_empty {s : Cfg h} (hI : Inv s) {g : Proc h} {o : Option (Proc h)}
    (hp : s.pc g = .x50 o) (hb : s.buf g = []) : Inv (s.stepProc g) := by
  have : s.stepProc g = s.loc g [] .rem := by
    simp only [Cfg.stepProc, hp]; exact barrier_goto hb
  rw [this]
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hap : s.mem.apply g = false := by
    rcases o with _ | nx
    · rcases hL with ⟨B, hB, -⟩ | ⟨-, h2⟩
      · rw [hb] at hB; simp at hB
      · exact h2
    · rcases hL.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩ | ⟨-, h2⟩
      · rw [hb] at hB; simp at hB
      · rw [hb] at hB; simp at hB
      · exact h2
  apply inv_local_nh hI
  · unfold LI; rw [loc_pc_self, loc_buf_self, hb]; simp [hap]
  all_goals first
    | (unfold Holds; rw [hp, hb]; simp)
    | (intro nx hh; unfold Hands at hh; rw [hp, hb] at hh; simp at hh)
    | (unfold Cfg.InCSX; rw [hp, hb]; simp [PC.Exit])
    | nh_tac

/-! ### Entering the critical section -/

lemma HC_of_not_incsx {s : Cfg h} {q : Proc h} (hq : ¬ s.InCSX q) : HC s q := by
  unfold HC; unfold Cfg.InCSX at hq
  cases hp : s.pc q <;> simp only [hp, PC.Exit, not_or] at hq ⊢ <;> try trivial
  all_goals first | exact absurd trivial hq.2.1 | skip
  rename_i o
  rcases o with _ | nx <;> intro hne <;> exact absurd ⟨⟨_, rfl⟩, hne⟩ hq.2.2

/-- Entering the critical section with memory `m`. -/
def Cfg.enter (s : Cfg h) (g : Proc h) (m : Mem h) : Cfg h :=
  { mem := m, buf := s.buf, pc := Function.update s.pc g .cs, ent := s.ent + 1 }

/-- Entering the critical section: `g` (buffer empty, in the entry section, `apply` performed)
moves to `cs`, the memory's `lock` becomes `g` (it was `−1`, or `g` with the signal performed). -/
lemma inv_enter {s : Cfg h} (hI : Inv s) {g : Proc h} (hE : (s.pc g).Entry)
    (hb : s.buf g = []) (hap : s.mem.apply g = true)
    (hl : s.mem.lock = none ∨ (s.mem.lock = some g ∧ ∀ g', ¬ Hands s g' g)) :
    Inv (s.enter g { s.mem with lock := some g }) := by
  have hpq : ∀ q, q ≠ g → (s.enter g { s.mem with lock := some g }).pc q = s.pc q := by
    intro q hq; simp [Cfg.enter, Function.update_of_ne hq]
  have hpg : (s.enter g { s.mem with lock := some g }).pc g = .cs := by simp [Cfg.enter]
  -- nobody is in the critical or exit section
  have hnone : ∀ q, ¬ s.InCSX q := by
    intro q hq
    rcases hI.incsx_iff.1 hq with hh | ⟨nx, hh⟩
    · have := hI.holds_lock hh
      rcases hl with hl | ⟨hl, -⟩ <;> rw [hl] at this
      · cases this
      · cases this; exact Inv.not_holds_of_entry hE hh
    · obtain ⟨h1, h2, -, -⟩ := hI.hands_lock hh
      rcases hl with hl | ⟨hl, hnh⟩ <;> rw [hl] at h1
      · cases h1
      · cases h1; exact hnh q hh
  have hnh : ∀ q, ¬ Holds s q := fun q hh => hnone q (hI.incsx_of_holds hh)
  have hlv : (lv (s.enter g { s.mem with lock := some g })).promQ = (lv s).promQ ∧
      ∀ r, (lv (s.enter g { s.mem with lock := some g })).inPromQ r = (lv s).inPromQ r := by
    unfold lv; simp only [Cfg.enter, hb, Mem.view_nil]
    rcases hl with hl | ⟨hl, -⟩ <;> rw [hl] <;> simp [hb]
  have hgq : g ∉ (lv s).promQ := by
    intro hg
    rcases hl with hl | ⟨hl, -⟩
    · unfold lv at hg; rw [hl] at hg; simp [hI.q4 hl] at hg
    · exact (hI.pq g hg).2.2 hl
  have hent : s.ent = s.mem.exits := by
    apply hI.ex3; intro g'
    have hX := hnone g'
    refine ⟨fun h1 => hX (Or.inl h1), fun h1 => hX (Or.inr (Or.inl (by rw [h1]; simp [PC.Exit]))),
      fun h1 => hX (Or.inr (Or.inl (by rw [h1]; simp [PC.Exit]))), fun v hv => ?_⟩
    exact hnh g' (hI.holds_of_exits_mem hv)
  refine
    { loc := ?_, hc := ?_, lockRole := ?_, uniq := ?_, sig := ?_, nodup := ?_, pq := ?_,
      inpq := ?_, q4 := ?_, ex1 := ?_, ex2 := ?_, ex3 := ?_, ex4 := ?_ }
  · intro q
    by_cases hq : q = g
    · subst hq; unfold LI; rw [hpg]; exact ⟨hb, hap, rfl⟩
    · exact LI_mono_out hI (hnone q) rfl (hpq q hq) rfl id
  · intro q
    by_cases hq : q = g
    · subst hq; unfold HC; rw [hpg]; trivial
    · apply HC_of_not_incsx
      unfold Cfg.InCSX; rw [hpq q hq]; exact hnone q
  · intro g' hg'
    simp only [Cfg.enter] at hg'; cases hg'
    left; unfold Holds; rw [hpg]; trivial
  · intro g₁ g₂ h₁ h₂
    have key : ∀ q, (s.enter g { s.mem with lock := some g }).InCSX q → q = g := by
      intro q hq
      by_contra hqg
      unfold Cfg.InCSX at hq; rw [hpq q hqg] at hq; exact hnone q hq
    rw [key _ h₁, key _ h₂]
  · intro q hs hEq ha
    by_cases hq : q = g
    · subst hq; rw [hpg] at hEq; simp [PC.Entry] at hEq
    · rw [hpq q hq] at hEq
      have := (hI.sig q hs hEq ha).1
      rcases hl with hl | ⟨hl, -⟩ <;> rw [hl] at this
      · cases this
      · cases this; exact absurd rfl hq
  · rw [hlv.1]; exact hI.nodup
  · intro q hq
    rw [hlv.1] at hq
    have hqg : q ≠ g := fun h' => hgq (h' ▸ hq)
    obtain ⟨h1, h2, -⟩ := hI.pq q hq
    refine ⟨by rw [hpq q hqg]; exact h1, h2, ?_⟩
    simp only [Cfg.enter, ne_eq, Option.some.injEq]; exact Ne.symm hqg
  · intro q
    rw [hlv.1, hlv.2, hI.inpq q]
    have h38 : ∀ g'' l rest, (s.enter g { s.mem with lock := some g }).pc g'' = .x38 l q rest ↔
        s.pc g'' = .x38 l q rest := by
      intro g'' l rest; by_cases hq : g'' = g
      · subst hq; rw [hpg]; revert hE; cases s.pc g'' <;> simp [PC.Entry]
      · rw [hpq g'' hq]
    have h46 : ∀ g'', (s.enter g { s.mem with lock := some g }).pc g'' = .x46 q ↔
        s.pc g'' = .x46 q := by
      intro g''; by_cases hq : g'' = g
      · subst hq; rw [hpg]; revert hE; cases s.pc g'' <;> simp [PC.Entry]
      · rw [hpq g'' hq]
    simp only [ne_eq, h38, h46]
  · intro hn; simp [Cfg.enter] at hn
  · intro g' _; simp only [Cfg.enter]; omega
  · intro g' v hv
    exact absurd (hI.holds_of_exits_mem (s := s) (g := g') hv) (hnh g')
  · intro hpre; exact absurd hpg (hpre g).1
  · intro g'; exact hI.ex4 g'

lemma cas_success {s : Cfg h} {g : Proc h} {c : PC h} (hb : s.buf g = []) (hl : s.mem.lock = none) :
    s.cas g c = s.enter g { s.mem with lock := some g } := by
  unfold Cfg.cas Cfg.enter
  simp only [hb, Mem.view_nil, hl, if_true]
  congr 1
  funext q; by_cases hq : q = g
  · subst hq; simp [hb]
  · simp [Function.update_of_ne hq]

lemma step_cas {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .e23 ∨ s.pc g = .e26) :
    Inv (s.stepProc g) := by
  by_cases hl : s.mem.lock = none
  · have hL := hI.loc g; unfold LI at hL
    have hb : s.buf g = [] ∧ s.mem.apply g = true := by
      rcases hp with hp | hp <;> rw [hp] at hL <;> exact hL
    have hE : (s.pc g).Entry := by rcases hp with hp | hp <;> rw [hp] <;> simp [PC.Entry]
    have : s.stepProc g = s.enter g { s.mem with lock := some g } := by
      rcases hp with hp | hp <;> simp only [Cfg.stepProc, hp] <;> exact cas_success hb.1 hl
    rw [this]; exact inv_enter hI hE hb.1 hb.2 (Or.inl hl)
  · exact step_cas_fail hI hp hl

lemma step_e27 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .e27) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  by_cases hs : s.mem.signal g = true
  · have hE : (s.pc g).Entry := by rw [hp]; simp [PC.Entry]
    obtain ⟨hl, hnh⟩ := hI.sig g hs hE hL.2
    have hm : { s.mem with lock := some g } = s.mem := by rw [← hl]
    have : s.stepProc g = s.enter g { s.mem with lock := some g } := by
      rw [hm]
      simp [Cfg.stepProc, hp, Cfg.view, hL.1, hs, Cfg.enter, Cfg.goto]
    rw [this]; exact inv_enter hI hE hL.1 hL.2 (Or.inr ⟨hl, hnh⟩)
  · have : s.stepProc g = s := by simp [Cfg.stepProc, hp, Cfg.view, hL.1, hs]
    rw [this]; exact hI

/-! ### Steps of the lock holder -/

lemma incsx_of_holds' {s : Cfg h} {g : Proc h} (hg : Holds s g) : s.InCSX g := by
  unfold Holds at hg; unfold Cfg.InCSX
  revert hg; cases hp : s.pc g <;> simp [PC.Exit]
  intro hm hb; rw [hb] at hm; simp at hm

lemma not_hands_of_holds' {s : Cfg h} {g nx : Proc h} (hg : Holds s g) : ¬ Hands s g nx := by
  unfold Holds at hg
  rintro (⟨hp, hb⟩ | ⟨hp, hb⟩) <;> rw [hp, hb] at hg <;> simp at hg

lemma not_entry_of_holds {s : Cfg h} {g : Proc h} (hg : Holds s g) : ¬ (s.pc g).Entry :=
  fun hE => Inv.not_holds_of_entry hE hg

theorem inv_local_holder {s : Cfg h} (hI : Inv s) {g : Proc h} {ws : List (W h)} {c' : PC h}
    (hg : Holds s g) (hg' : Holds (s.loc g ws c') g)
    (hLI : LI (s.loc g ws c') g) (hHC : HC (s.loc g ws c') g)
    (hws : ∀ w ∈ ws, w.isPromQ = false ∧ ∀ r, w.isInPromQ r = false)
    (hx38 : ∀ l q rest, c' = .x38 l q rest ↔ s.pc g = .x38 l q rest)
    (hx46 : ∀ q, c' = .x46 q ↔ s.pc g = .x46 q)
    (hex1 : c' = .cs ∨ c' = .x31 ∨ c' = .x32 → s.pc g = .cs ∨ s.pc g = .x31 ∨ s.pc g = .x32)
    (hex2 : ∀ v, .exits v ∈ ws → v = s.mem.exits + 1 ∧ s.ent = v)
    (hex3 : (c' ≠ .cs ∧ c' ≠ .x31 ∧ c' ≠ .x32 ∧ ∀ v, .exits v ∉ s.buf g ++ ws) →
      (s.pc g ≠ .cs ∧ s.pc g ≠ .x31 ∧ s.pc g ≠ .x32 ∧ ∀ v, .exits v ∉ s.buf g))
    (hex4 : (s.buf g ++ ws).countP (fun w => w.isExits) ≤ 1) :
    Inv (s.loc g ws c') := by
  have hcE : ¬ c'.Entry := by
    have := not_entry_of_holds hg'; rwa [loc_pc_self] at this
  exact inv_local hI hLI hHC (fun h' => absurd h' (not_entry_of_holds hg))
    (fun h' => absurd h' hcE) (fun h' => absurd hg h') ⟨fun _ => hg, fun _ => hg'⟩
    (fun nx => ⟨fun h' => absurd h' (not_hands_of_holds' hg'),
      fun h' => absurd h' (not_hands_of_holds' hg)⟩)
    ⟨fun _ => incsx_of_holds' hg, fun _ => incsx_of_holds' hg'⟩
    (lv_loc_holder hI hg hws) hx38 hx46 hex1 hex2 hex3 hex4

/-- Discharges routine side conditions for holder steps. -/
macro "hold_tac" : tactic => `(tactic| first
  | done
  | (simp_all [Holds, HC, loc_pc_self, loc_buf_self, W.isPromQ, W.isInPromQ, W.isExits]; done)
  | skip)

lemma XB_append {s : Cfg h} {g : Proc h} {B : List (W h)} {w : W h} (hX : XB s g B)
    (hw : ExitType g w) (hwa : w ≠ .apply g false) : XB s g (B ++ [w]) := by
  obtain ⟨h1, h2, h3⟩ := hX
  refine ⟨fun w' hw' => ?_, ?_, ?_⟩
  · rw [List.mem_append] at hw'; rcases hw' with hw' | hw'
    · exact h1 w' hw'
    · simp at hw'; subst hw'; exact hw
  · rw [h2]; simp [Ne.symm hwa]
  · rcases B with _ | ⟨x, B⟩
    · simp
    · simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_singleton, not_or]
      exact ⟨h3, Ne.symm hwa⟩

lemma addCand_not_mem {g : Proc h} {acc : List (Proc h)} (hg : g ∉ acc) (v : Option (Proc h)) :
    g ∉ addCand g acc v := by
  unfold addCand; rcases v with _ | q
  · exact hg
  · simp only; split_ifs with hq
    · simp [hg]; exact fun h' => hq.1 h'.symm
    · exact hg

lemma Inv.entry_of_apply {s : Cfg h} (hI : Inv s) {g c : Proc h} (hg : Holds s g) (hcg : c ≠ g)
    (ha : s.mem.apply c = true) : (s.pc c).Entry := by
  by_contra hE
  have hX : ¬ s.InCSX c := fun hc => hcg (hI.uniq _ _ hc (hI.incsx_of_holds hg))
  have hL := hI.loc c
  unfold LI at hL; unfold Cfg.InCSX at hX
  revert hL hE hX
  cases s.pc c <;> simp [PC.Entry, PC.Exit, ha]
  rename_i o
  rcases o with _ | nx <;> simp <;> intro h1 h2 <;> simp_all

lemma ws_exitType_ok {w : W h} (hw : w.isPromQ = false ∧ ∀ r, w.isInPromQ r = false) :
    ∀ w' ∈ [w], w'.isPromQ = false ∧ ∀ r, w'.isInPromQ r = false := by
  intro w' hw'; simp at hw'; subst hw'; exact hw

lemma step_cs {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .cs) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have : s.stepProc g = s.loc g [] .x31 := by simp [Cfg.stepProc, hp, goto_eq_loc]
  rw [this]
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  apply inv_local_holder hI hg
  · unfold Holds; rw [loc_pc_self]; trivial
  · unfold LI; rw [loc_pc_self, loc_buf_self]; simpa using hL
  all_goals simp [HC, hp, hI.ex4 g]

lemma step_x31 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .x31) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have : s.stepProc g = s.loc g [.apply g false] .x32 := by simp [Cfg.stepProc, hp, issue_eq_loc]
  rw [this]
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  apply inv_local_holder hI hg
  · unfold Holds; rw [loc_pc_self]; trivial
  · unfold LI; rw [loc_pc_self, loc_buf_self, hL.1]; exact ⟨hL.2.2, Or.inl ⟨rfl, hL.2.1⟩⟩
  all_goals simp [HC, hp, hL.1, W.isPromQ, W.isInPromQ, W.isExits]

lemma step_x32 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .x32) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hbx : (s.view g).exits = s.mem.exits := by
    unfold Cfg.view; rcases hL.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> rfl
  have : s.stepProc g = s.loc g [.exits (s.mem.exits + 1)] (if 0 < h then .x34 0 0 [] else .x42) := by
    simp [Cfg.stepProc, hp, issue_eq_loc, hbx]
  rw [this]
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have hXB : XB (s.loc g [.exits (s.mem.exits + 1)] (if 0 < h then .x34 0 0 [] else .x42)) g
      (s.buf g ++ [.exits (s.mem.exits + 1)]) := by
    simp only [XB, loc_mem]
    rcases hL.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> simp [h2, ExitType, W.isExits]
  have hent := hI.ex1 g (Or.inr (Or.inr hp))
  apply inv_local_holder hI hg
  · unfold Holds; rw [loc_pc_self]; split_ifs <;> trivial
  · unfold LI; rw [loc_pc_self, loc_buf_self]
    split_ifs
    · exact ⟨hL.1, hXB, by simp⟩
    · exact ⟨hL.1, hXB⟩
  · unfold HC; rw [loc_pc_self]; split_ifs <;> trivial
  · simp [W.isPromQ, W.isInPromQ]
  · intro l q rest; rw [hp]; split_ifs <;> simp
  · intro q; rw [hp]; split_ifs <;> simp
  · intro h'; split_ifs at h' <;> simp at h'
  · intro v hv; simp at hv; subst hv; exact ⟨rfl, hent⟩
  · intro h'; exact absurd (h'.2.2.2 (s.mem.exits + 1)) (by simp)
  · rcases hL.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [W.isExits]

lemma step_x34 {s : Cfg h} (hI : Inv s) {g : Proc h} {l j : ℕ} {acc : List (Proc h)}
    (hp : s.pc g = .x34 l j acc) : Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  set acc' := addCand g acc ((s.view g).node (target (anc g l) j))
  have : s.stepProc g = s.loc g [] (if j < 2 then .x34 l (j + 1) acc' else .x35 l acc') := by
    simp [Cfg.stepProc, hp, goto_eq_loc, acc']
  rw [this]
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have hacc : g ∉ acc' := addCand_not_mem hL.2.2 _
  apply inv_local_holder hI hg
  · unfold Holds; rw [loc_pc_self]; split_ifs <;> trivial
  · unfold LI; rw [loc_pc_self, loc_buf_self, List.append_nil]
    split_ifs
    · exact ⟨hL.1, hL.2.1, hacc⟩
    · exact ⟨hL.1, hL.2.1, hacc⟩
  · unfold HC; rw [loc_pc_self]; split_ifs <;> trivial
  all_goals first
    | (intro l q rest; rw [hp]; split_ifs <;> simp)
    | (intro q; rw [hp]; split_ifs <;> simp)
    | (intro h'; split_ifs at h' <;> (simp at h'; done))
    | (simp [hp, hI.ex4 g]; done)
    | skip

/-- Routine side conditions of `inv_local_holder` for goto steps. -/
macro "hgoto_tac" hp:ident : tactic => `(tactic| first
    | (intro l q rest; rw [$hp:ident]; split_ifs <;> simp; done)
    | (intro q; rw [$hp:ident]; split_ifs <;> simp; done)
    | (intro l q rest; rw [$hp:ident]; simp; done)
    | (intro q; rw [$hp:ident]; simp; done)
    | (intro h'; split_ifs at h' <;> (simp at h'; done))
    | (intro h'; (simp at h'; done))
    | (intro h'; refine ⟨by simp [$hp:ident], by simp [$hp:ident], by simp [$hp:ident], ?_⟩;
       simpa using h'.2.2.2)
    | (simp [$hp:ident]; done)
    | (unfold Holds; rw [loc_pc_self]; split_ifs <;> trivial)
    | (unfold Holds; rw [loc_pc_self]; trivial)
    | (unfold HC; rw [loc_pc_self]; split_ifs <;> trivial)
    | (unfold HC; rw [loc_pc_self]; trivial)
    | skip)

lemma step_x35 {s : Cfg h} (hI : Inv s) {g : Proc h} {l : ℕ} {cands : List (Proc h)}
    (hp : s.pc g = .x35 l cands) : Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  rcases cands with _ | ⟨c, rest⟩
  · have : s.stepProc g = s.loc g [] (if l + 1 < h then .x34 (l + 1) 0 [] else .x42) := by
      simp [Cfg.stepProc, hp, goto_eq_loc]
    rw [this]
    apply inv_local_holder hI hg
    · hgoto_tac hp
    · unfold LI; rw [loc_pc_self, loc_buf_self, List.append_nil]
      split_ifs
      · exact ⟨hL.1, hL.2.1, by simp⟩
      · exact ⟨hL.1, hL.2.1⟩
    all_goals first | (simp [hI.ex4 g]; done) | (rw [List.countP_append]; simpa [W.isExits] using hI.ex4 g) | hgoto_tac hp
  · have hcg : c ≠ g := fun h' => hL.2.2 (by simp [h'])
    have hrest : g ∉ rest := fun h' => hL.2.2 (by simp [h'])
    have hva : (s.view g).apply c = s.mem.apply c := by
      unfold Cfg.view; apply view_apply_of
      intro w hw
      rcases hL.2.1.1 w hw with rfl | h1 | h1 | ⟨r, b, rfl⟩
      · simp [W.isApply, Ne.symm hcg]
      all_goals first | rfl | (cases w <;> simp_all [W.isExits, W.isPromQ, W.isApply])
    have : s.stepProc g = s.loc g [] (if s.mem.apply c then .x36 l c rest else .x35 l rest) := by
      simp [Cfg.stepProc, hp, goto_eq_loc, hva]
    rw [this]
    apply inv_local_holder hI hg
    · hgoto_tac hp
    · unfold LI; rw [loc_pc_self, loc_buf_self, List.append_nil]
      split_ifs
      · exact ⟨hL.1, hL.2.1, hrest, hcg⟩
      · exact ⟨hL.1, hL.2.1, hrest⟩
    · unfold HC; rw [loc_pc_self]
      split_ifs with ha
      · simp only [loc_mem]
        refine ⟨?_, ha⟩
        rw [loc_pc_ne s g [] _ hcg]; exact hI.entry_of_apply hg hcg ha
      · trivial
    all_goals first | (simp [hI.ex4 g]; done) | (rw [List.countP_append]; simpa [W.isExits] using hI.ex4 g) | hgoto_tac hp

lemma step_x36 {s : Cfg h} (hI : Inv s) {g : Proc h} {l : ℕ} {c : Proc h} {rest : List (Proc h)}
    (hp : s.pc g = .x36 l c rest) : Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hHC := hI.hc g; unfold HC at hHC; rw [hp] at hHC
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have hlv := hI.lv_of_holds hg
  have : s.stepProc g = s.loc g [] (if (lv s).inPromQ c then .x35 l rest else .x37 l c rest) := by
    simp [Cfg.stepProc, hp, goto_eq_loc, hlv]
  rw [this]
  apply inv_local_holder hI hg
  · hgoto_tac hp
  · unfold LI; rw [loc_pc_self, loc_buf_self, List.append_nil]
    split_ifs
    · exact ⟨hL.1, hL.2.1, hL.2.2.1⟩
    · exact hL
  · unfold HC; rw [loc_pc_self]
    split_ifs with hin
    · trivial
    · have hlv' : lv (s.loc g [] (.x37 l c rest)) = lv s := by
        rw [lv_loc_holder_eq hI hg, hlv]; rfl
      simp only [loc_mem, hlv']
      refine ⟨by rw [loc_pc_ne s g [] _ hL.2.2.2]; exact hHC.1, hHC.2, ?_, by simpa using hin⟩
      intro hcq
      have := (hI.inpq c).2 (Or.inl ⟨hcq, fun g'' l' rest' h38 => ?_⟩)
      · simp [this] at hin
      · have := hI.uniq _ _ (Or.inr (Or.inl (by rw [h38]; simp [PC.Exit]))) (incsx_of_holds' hg)
        subst this; rw [hp] at h38; cases h38
  all_goals first | (simp [hI.ex4 g]; done) | (rw [List.countP_append]; simpa [W.isExits] using hI.ex4 g) | hgoto_tac hp

lemma step_x42 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .x42) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have hlv := hI.lv_of_holds hg
  have : s.stepProc g = s.loc g [] (if (lv s).promQ = [] then .x43 else .x45) := by
    simp [Cfg.stepProc, hp, goto_eq_loc, hlv]
  rw [this]
  apply inv_local_holder hI hg
  · hgoto_tac hp
  · unfold LI; rw [loc_pc_self, loc_buf_self, List.append_nil]
    split_ifs <;> exact hL
  · unfold HC; rw [loc_pc_self]
    split_ifs with hq
    · have hlv' : lv (s.loc g [] .x43) = lv s := by rw [lv_loc_holder_eq hI hg, hlv]; rfl
      rw [hlv']; exact hq
    · have hlv' : lv (s.loc g [] .x45) = lv s := by rw [lv_loc_holder_eq hI hg, hlv]; rfl
      rw [hlv']; exact hq
  all_goals first | (simp [hI.ex4 g]; done) | (rw [List.countP_append]; simpa [W.isExits] using hI.ex4 g) | hgoto_tac hp

lemma step_x43 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .x43) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hHC := hI.hc g; unfold HC at hHC; rw [hp] at hHC
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have : s.stepProc g = s.loc g [.lock none] (.x50 none) := by
    simp [Cfg.stepProc, hp, issue_eq_loc]
  rw [this]
  apply inv_local_holder hI hg
  · unfold Holds; rw [loc_pc_self, loc_buf_self]; simp
  · unfold LI; rw [loc_pc_self, loc_buf_self]; exact Or.inl ⟨_, rfl, hL.2, hL.1⟩
  · unfold HC; rw [loc_pc_self]; intro _
    rw [lv_loc_holder_eq hI hg, ← hI.lv_of_holds hg]; simpa using hHC
  all_goals first | (simp [hp, W.isPromQ, W.isInPromQ, W.isExits, hI.ex4 g]; done) | (rw [List.countP_append]; simpa [W.isExits] using hI.ex4 g) | hgoto_tac hp

lemma step_x47 {s : Cfg h} (hI : Inv s) {g nx : Proc h} (hp : s.pc g = .x47 nx) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hHC := hI.hc g; unfold HC at hHC; rw [hp] at hHC
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have : s.stepProc g = s.loc g [.lock (some nx)] (.x48 nx) := by
    simp [Cfg.stepProc, hp, issue_eq_loc]
  rw [this]
  have hlv : lv (s.loc g [.lock (some nx)] (.x48 nx)) = (lv s).write (.lock (some nx)) := by
    rw [lv_loc_holder_eq hI hg, ← hI.lv_of_holds hg]; rfl
  apply inv_local_holder hI hg
  · unfold Holds; rw [loc_pc_self, loc_buf_self]; simp
  · unfold LI; rw [loc_pc_self, loc_buf_self]; exact ⟨hL.2.2, Or.inl ⟨_, rfl, hL.2.1, hL.1⟩⟩
  · unfold HC NxOK; rw [loc_pc_self, hlv]
    simp only [loc_mem, write_promQ, write_inPromQ]
    rw [loc_pc_ne s g _ _ hL.2.2]; exact hHC
  all_goals first | (simp [hp, W.isPromQ, W.isInPromQ, W.isExits, hI.ex4 g]; done) | (rw [List.countP_append]; simpa [W.isExits] using hI.ex4 g) | hgoto_tac hp

lemma step_x48 {s : Cfg h} (hI : Inv s) {g nx : Proc h} (hp : s.pc g = .x48 nx) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hHC := hI.hc g; unfold HC at hHC; rw [hp] at hHC
  have : s.stepProc g = s.loc g [.signal nx true] (.x50 (some nx)) := by
    simp [Cfg.stepProc, hp, issue_eq_loc]
  rw [this]
  rcases hL.2 with ⟨B, hB, hXB, hlk⟩ | ⟨hb, hlk, hap, hsg⟩
  · -- the holder (its lock write is still buffered)
    have hg : Holds s g := by unfold Holds; rw [hp, hB]; simp
    have hlv : lv (s.loc g [.signal nx true] (.x50 (some nx))) =
        (lv s).write (.signal nx true) := by
      rw [lv_loc_holder_eq hI hg, ← hI.lv_of_holds hg]; rfl
    apply inv_local_holder hI hg
    · unfold Holds; rw [loc_pc_self, loc_buf_self, hB]; simp
    · unfold LI; rw [loc_pc_self, loc_buf_self, hB]
      exact ⟨hL.1, Or.inl ⟨B, by simp, hXB, hlk⟩⟩
    · unfold HC NxOK; rw [loc_pc_self, hlv]; intro _
      simp only [loc_mem, write_promQ, write_inPromQ]
      rw [loc_pc_ne s g _ _ hL.1]; exact hHC
    all_goals first
      | (simp [hp, W.isPromQ, W.isInPromQ, W.isExits]; done)
      | (rw [List.countP_append]; simpa [W.isExits] using hI.ex4 g)
      | hgoto_tac hp
  · -- the hander (its lock write was performed)
    have hlv := lv_loc_nh (s := s) (c' := .x50 (some nx))
      (show ∀ w ∈ [W.signal nx true], NHW g w by intro w hw; simp at hw; subst hw; simp [NHW])
    apply inv_local hI
    · unfold LI; rw [loc_pc_self, loc_buf_self, hb]
      exact ⟨hL.1, Or.inr (Or.inl ⟨by simp, hlk, hap, hsg⟩)⟩
    · unfold HC NxOK; rw [loc_pc_self]; intro _
      simp only [loc_mem, hlv.1, hlv.2]
      rw [loc_pc_ne s g _ _ hL.1]; exact hHC
    · intro hE; rw [hp] at hE; simp [PC.Entry] at hE
    · intro hE; simp [PC.Entry] at hE
    · intro _ w hw; simp at hw; subst hw; simp [NHW]
    · unfold Holds; rw [loc_pc_self, loc_buf_self, hp, hb]; simp
    · intro nx'; unfold Hands; rw [loc_pc_self, loc_buf_self, hp, hb]; simp [eq_comm]
    · unfold Cfg.InCSX; rw [loc_pc_self, loc_buf_self, hp, hb]; simp [PC.Exit]
    · exact hlv
    · intro l q rest; rw [hp]; simp
    · intro q; rw [hp]; simp
    · intro h'; simp at h'
    · intro v hv; simp at hv
    · intro _; refine ⟨by simp [hp], by simp [hp], by simp [hp], by simp [hb]⟩
    · rw [hb]; simp [W.isExits]

lemma step_x50 {s : Cfg h} (hI : Inv s) {g : Proc h} {o : Option (Proc h)}
    (hp : s.pc g = .x50 o) : Inv (s.stepProc g) := by
  by_cases hb : s.buf g = []
  · exact step_x50_empty hI hp hb
  · have : s.stepProc g = s.flush g := by
      simp only [Cfg.stepProc, hp]; exact barrier_flush hb
    rw [this]; exact inv_flush hI g

/-- Holder steps that change the queue fields of the logical memory. -/
theorem inv_local_holder_q {s : Cfg h} (hI : Inv s) {g : Proc h} {w : W h} {c' : PC h}
    (hg : Holds s g) (hg' : Holds (s.loc g [w] c') g)
    (hLI : LI (s.loc g [w] c') g) (hHC : HC (s.loc g [w] c') g)
    (hwe : w.isExits = false) (hset : c' ≠ .cs ∧ c' ≠ .x31 ∧ c' ≠ .x32)
    (hpset : s.pc g ≠ .cs ∧ s.pc g ≠ .x31 ∧ s.pc g ≠ .x32)
    (hnodup : (lv (s.loc g [w] c')).promQ.Nodup)
    (hpq : ∀ q ∈ (lv (s.loc g [w] c')).promQ, q ≠ g ∧ (s.pc q).Entry ∧ s.mem.apply q = true)
    (hinpq : ∀ q, (lv (s.loc g [w] c')).inPromQ q = true ↔
      ((q ∈ (lv (s.loc g [w] c')).promQ ∧ ∀ l rest, c' ≠ .x38 l q rest) ∨ c' = .x46 q)) :
    Inv (s.loc g [w] c') := by
  have hgX := incsx_of_holds' hg
  have hlk := hI.holds_lock hg
  have hpq' : ∀ q, q ≠ g → (s.loc g [w] c').pc q = s.pc q := fun q hq => loc_pc_ne s g _ _ hq
  have hbq : ∀ q, q ≠ g → (s.loc g [w] c').buf q = s.buf q := fun q hq => loc_buf_ne s g _ _ hq
  have hnot : ∀ q, q ≠ g → ¬ s.InCSX q := fun q hq hc => hq (hI.uniq _ _ hc hgX)
  have hnot' : ∀ q, q ≠ g → ¬ (s.loc g [w] c').InCSX q := by
    intro q hq hc; unfold Cfg.InCSX at hc; rw [hpq' q hq, hbq q hq] at hc; exact hnot q hq hc
  refine
    { loc := ?_, hc := ?_, lockRole := ?_, uniq := ?_, sig := ?_, nodup := hnodup, pq := ?_,
      inpq := ?_, q4 := ?_, ex1 := ?_, ex2 := ?_, ex3 := ?_, ex4 := ?_ }
  · intro q
    by_cases hq : q = g
    · subst hq; exact hLI
    · exact (LI_congr (s' := s.loc g [w] c') (s := s) rfl (hbq q hq) (hpq' q hq)).2 (hI.loc q)
  · intro q
    by_cases hq : q = g
    · subst hq; exact hHC
    · exact HC_of_not_incsx (hnot' q hq)
  · intro g' hg''
    simp only [loc_mem] at hg''; rw [hlk] at hg''; cases hg''; exact Or.inl hg'
  · intro g₁ g₂ h₁ h₂
    have key : ∀ q, (s.loc g [w] c').InCSX q → q = g := fun q hq => by
      by_contra hqg; exact hnot' q hqg hq
    rw [key _ h₁, key _ h₂]
  · intro q hs hE ha
    by_cases hq : q = g
    · subst hq; rw [loc_pc_self] at hE
      exact absurd hE (by have := not_entry_of_holds hg'; rwa [loc_pc_self] at this)
    · rw [hpq' q hq] at hE
      have := (hI.sig q hs hE ha).1
      rw [hlk] at this; cases this; exact absurd rfl hq
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hpq q hq
    refine ⟨by rw [hpq' q h1]; exact h2, h3, ?_⟩
    simp only [loc_mem, hlk, ne_eq, Option.some.injEq]; exact Ne.symm h1
  · intro q
    rw [hinpq q]
    have h38 : (∀ g'' l rest, (s.loc g [w] c').pc g'' ≠ .x38 l q rest) ↔
        (∀ l rest, c' ≠ .x38 l q rest) := by
      constructor
      · intro H l rest h'; exact H g l rest (by rw [loc_pc_self, h'])
      · intro H g'' l rest h'
        by_cases hq : g'' = g
        · subst hq; rw [loc_pc_self] at h'; exact H l rest h'
        · exact hnot' g'' hq (Or.inr (Or.inl (by rw [h']; simp [PC.Exit])))
    have h46 : (∃ g'', (s.loc g [w] c').pc g'' = .x46 q) ↔ c' = .x46 q := by
      constructor
      · rintro ⟨g'', h'⟩
        by_cases hq : g'' = g
        · subst hq; rwa [loc_pc_self] at h'
        · exact absurd (Or.inr (Or.inl (by rw [h']; simp [PC.Exit]))) (hnot' g'' hq)
      · intro h'; exact ⟨g, by rw [loc_pc_self, h']⟩
    rw [h38, h46]
  · intro hn; simp only [loc_mem] at hn; rw [hlk] at hn; cases hn
  · intro g' hg''
    by_cases hq : g' = g
    · subst hq; rw [loc_pc_self] at hg''
      rcases hg'' with h' | h' | h' <;> exact absurd h' (by simp [hset])
    · rw [hpq' g' hq] at hg''; exact hI.ex1 g' hg''
  · intro g' v hv
    by_cases hq : g' = g
    · subst hq; rw [loc_buf_self, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hI.ex2 g' v hv
      · simp at hv; subst hv; simp [W.isExits] at hwe
    · rw [hbq g' hq] at hv; exact hI.ex2 g' v hv
  · intro hpre
    apply hI.ex3
    intro g'
    by_cases hq : g' = g
    · subst hq
      have := hpre g'
      rw [loc_pc_self, loc_buf_self] at this
      exact ⟨hpset.1, hpset.2.1, hpset.2.2, fun v hv => this.2.2.2 v (by simp [hv])⟩
    · have := hpre g'
      rwa [hpq' g' hq, hbq g' hq] at this
  · intro g'
    by_cases hq : g' = g
    · subst hq; rw [loc_buf_self, List.countP_append]; simpa [hwe] using hI.ex4 g'
    · rw [hbq g' hq]; exact hI.ex4 g'

lemma Inv.inpq_holder {s : Cfg h} (hI : Inv s) {g : Proc h} (hg : Holds s g) (q : Proc h) :
    (lv s).inPromQ q = true ↔
      ((q ∈ (lv s).promQ ∧ ∀ l rest, s.pc g ≠ .x38 l q rest) ∨ s.pc g = .x46 q) := by
  rw [hI.inpq q]
  have hgX := incsx_of_holds' hg
  have key : ∀ g'', (s.pc g'').Exit → g'' = g := fun g'' hx =>
    hI.uniq _ _ (Or.inr (Or.inl hx)) hgX
  constructor
  · rintro (⟨h1, h2⟩ | ⟨g'', h1⟩)
    · exact Or.inl ⟨h1, fun l rest => h2 g l rest⟩
    · have := key g'' (by rw [h1]; simp [PC.Exit]); subst this; exact Or.inr h1
  · rintro (⟨h1, h2⟩ | h1)
    · refine Or.inl ⟨h1, fun g'' l rest h' => ?_⟩
      have := key g'' (by rw [h']; simp [PC.Exit]); subst this; exact h2 l rest h'
    · exact Or.inr ⟨g, h1⟩

lemma lv_issue {s : Cfg h} (hI : Inv s) {g : Proc h} (hg : Holds s g) (w : W h) (c' : PC h) :
    lv (s.loc g [w] c') = (lv s).write w := by
  rw [lv_loc_holder_eq hI hg, ← hI.lv_of_holds hg]; rfl

lemma step_x37 {s : Cfg h} (hI : Inv s) {g c : Proc h} {l : ℕ} {rest : List (Proc h)}
    (hp : s.pc g = .x37 l c rest) : Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hHC := hI.hc g; unfold HC at hHC; rw [hp] at hHC
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have : s.stepProc g = s.loc g [.promQ ((lv s).promQ ++ [c])] (.x38 l c rest) := by
    simp [Cfg.stepProc, hp, issue_eq_loc, hI.lv_of_holds hg]
  rw [this]
  have hlv := lv_issue hI hg (.promQ ((lv s).promQ ++ [c])) (.x38 l c rest)
  apply inv_local_holder_q hI hg
  · unfold Holds; rw [loc_pc_self]; trivial
  · unfold LI; rw [loc_pc_self, loc_buf_self]
    exact ⟨hL.1, XB_append hL.2.1 (Or.inr (Or.inr (Or.inl rfl))) (by simp), hL.2.2⟩
  · unfold HC; rw [loc_pc_self, hlv]; simp
  · rfl
  · simp
  · simp [hp]
  · rw [hlv]; simp only [write_promQ]
    exact List.nodup_append.2 ⟨hI.nodup, List.nodup_singleton _, by
      intro a ha b hb; simp at hb; subst hb; exact fun h' => hHC.2.2.1 (h' ▸ ha)⟩
  · rw [hlv]; simp only [write_promQ, List.mem_append, List.mem_singleton]
    rintro q (hq | rfl)
    · obtain ⟨h1, h2, h3⟩ := hI.pq q hq
      exact ⟨fun h' => h3 (by rw [hI.holds_lock hg, h']), h1, h2⟩
    · exact ⟨hL.2.2.2, hHC.1, hHC.2.1⟩
  · intro q
    rw [hlv]; simp only [write_promQ, write_inPromQ]
    rw [hI.inpq_holder hg q, hp]
    by_cases hq : q = c
    · subst hq; simp [hHC.2.2.2, hHC.2.2.1]
    · simp [hq, Ne.symm hq]

lemma step_x38 {s : Cfg h} (hI : Inv s) {g c : Proc h} {l : ℕ} {rest : List (Proc h)}
    (hp : s.pc g = .x38 l c rest) : Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hHC := hI.hc g; unfold HC at hHC; rw [hp] at hHC
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have : s.stepProc g = s.loc g [.inPromQ c true] (.x35 l rest) := by
    simp [Cfg.stepProc, hp, issue_eq_loc]
  rw [this]
  have hlv := lv_issue hI hg (.inPromQ c true) (.x35 l rest)
  apply inv_local_holder_q hI hg
  · unfold Holds; rw [loc_pc_self]; trivial
  · unfold LI; rw [loc_pc_self, loc_buf_self]
    exact ⟨hL.1, XB_append hL.2.1 (Or.inr (Or.inr (Or.inr ⟨c, true, rfl⟩))) (by simp), hL.2.2.1⟩
  · unfold HC; rw [loc_pc_self]; trivial
  · rfl
  · simp
  · simp [hp]
  · rw [hlv]; exact hI.nodup
  · rw [hlv]; intro q hq
    obtain ⟨h1, h2, h3⟩ := hI.pq q hq
    exact ⟨fun h' => h3 (by rw [hI.holds_lock hg, h']), h1, h2⟩
  · intro q
    rw [hlv]; simp only [write_promQ, write_inPromQ]
    by_cases hq : q = c
    · subst hq; simp [hHC]
    · rw [if_neg (Ne.symm hq)]
      rw [hI.inpq_holder hg q, hp]
      simp [Ne.symm hq]

lemma step_x45 {s : Cfg h} (hI : Inv s) {g : Proc h} (hp : s.pc g = .x45) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have hv := hI.lv_of_holds hg
  rcases hq : (lv s).promQ with _ | ⟨nx, rest⟩
  · have : s.stepProc g = s.loc g [] .x42 := by
      simp [Cfg.stepProc, hp, goto_eq_loc, ← hv, hq]
    rw [this]
    apply inv_local_holder hI hg
    · hgoto_tac hp
    · unfold LI; rw [loc_pc_self, loc_buf_self, List.append_nil]; exact hL
    all_goals first | (simp [hI.ex4 g]; done) | hgoto_tac hp
  · have : s.stepProc g = s.loc g [.promQ rest] (.x46 nx) := by
      simp [Cfg.stepProc, hp, issue_eq_loc, ← hv, hq]
    rw [this]
    have hlv := lv_issue hI hg (.promQ rest) (.x46 nx)
    have hnx := hI.pq nx (by rw [hq]; simp)
    have hnxg : nx ≠ g := fun h' => hnx.2.2 (by rw [hI.holds_lock hg, h'])
    have hnd := hI.nodup; rw [hq] at hnd
    apply inv_local_holder_q hI hg
    · unfold Holds; rw [loc_pc_self]; trivial
    · unfold LI; rw [loc_pc_self, loc_buf_self]
      exact ⟨hL.1, XB_append hL.2 (Or.inr (Or.inr (Or.inl rfl))) (by simp), hnxg⟩
    · unfold HC; rw [loc_pc_self, hlv]; simp only [write_promQ, loc_mem]
      rw [loc_pc_ne s g _ _ hnxg]
      exact ⟨hnx.1, hnx.2.1, (List.nodup_cons.1 hnd).1⟩
    · rfl
    · simp
    · simp [hp]
    · rw [hlv]; exact (List.nodup_cons.1 hnd).2
    · rw [hlv]; intro q hq'
      obtain ⟨h1, h2, h3⟩ := hI.pq q (by rw [hq]; exact List.mem_cons_of_mem _ hq')
      exact ⟨fun h' => h3 (by rw [hI.holds_lock hg, h']), h1, h2⟩
    · intro q
      rw [hlv]; simp only [write_promQ, write_inPromQ]
      rw [hI.inpq_holder hg q, hp, hq]
      by_cases hqn : q = nx
      · subst hqn; simp
      · simp [hqn, Ne.symm hqn]

lemma step_x46 {s : Cfg h} (hI : Inv s) {g nx : Proc h} (hp : s.pc g = .x46 nx) :
    Inv (s.stepProc g) := by
  have hL := hI.loc g; unfold LI at hL; rw [hp] at hL
  have hHC := hI.hc g; unfold HC at hHC; rw [hp] at hHC
  have hg : Holds s g := by unfold Holds; rw [hp]; trivial
  have : s.stepProc g = s.loc g [.inPromQ nx false] (.x47 nx) := by
    simp [Cfg.stepProc, hp, issue_eq_loc]
  rw [this]
  have hlv := lv_issue hI hg (.inPromQ nx false) (.x47 nx)
  apply inv_local_holder_q hI hg
  · unfold Holds; rw [loc_pc_self]; trivial
  · unfold LI; rw [loc_pc_self, loc_buf_self]
    exact ⟨hL.1, XB_append hL.2.1 (Or.inr (Or.inr (Or.inr ⟨nx, false, rfl⟩))) (by simp), hL.2.2⟩
  · unfold HC NxOK; rw [loc_pc_self, hlv]; simp only [write_promQ, write_inPromQ, loc_mem]
    rw [loc_pc_ne s g _ _ hL.2.2]
    exact ⟨hHC.1, hHC.2.1, hHC.2.2, by simp⟩
  · rfl
  · simp
  · simp [hp]
  · rw [hlv]; exact hI.nodup
  · rw [hlv]; intro q hq
    obtain ⟨h1, h2, h3⟩ := hI.pq q hq
    exact ⟨fun h' => h3 (by rw [hI.holds_lock hg, h']), h1, h2⟩
  · intro q
    rw [hlv]; simp only [write_promQ, write_inPromQ]
    by_cases hq : q = nx
    · subst hq; simp [hHC.2.2]
    · rw [if_neg (Ne.symm hq)]
      rw [hI.inpq_holder hg q, hp]
      simp [Ne.symm hq]

/-- **Steps preserve the invariant.** -/
theorem inv_step {s : Cfg h} (hI : Inv s) (g : Proc h) : Inv (s.stepProc g) := by
  cases hp : s.pc g with
  | rem => exact step_rem hI hp
  | e18 => exact step_e18 hI hp
  | e19 l => exact step_e19 hI hp
  | e22 => exact step_e22 hI hp
  | e23 => exact step_cas hI (Or.inl hp)
  | e24 => exact step_e24 hI hp
  | e25a e => exact step_e25a hI hp
  | e25b e => exact step_e25b hI hp
  | e26 => exact step_cas hI (Or.inr hp)
  | e27 => exact step_e27 hI hp
  | cs => exact step_cs hI hp
  | x31 => exact step_x31 hI hp
  | x32 => exact step_x32 hI hp
  | x34 l j acc => exact step_x34 hI hp
  | x35 l cands => exact step_x35 hI hp
  | x36 l c rest => exact step_x36 hI hp
  | x37 l c rest => exact step_x37 hI hp
  | x38 l c rest => exact step_x38 hI hp
  | x42 => exact step_x42 hI hp
  | x43 => exact step_x43 hI hp
  | x45 => exact step_x45 hI hp
  | x46 nx => exact step_x46 hI hp
  | x47 nx => exact step_x47 hI hp
  | x48 nx => exact step_x48 hI hp
  | x50 o => exact step_x50 hI hp

theorem inv_next {s : Cfg h} (hI : Inv s) (e : Ev h) : Inv (s.next e) := by
  cases e with
  | step g => exact inv_step hI g
  | flush g => exact inv_flush hI g

end Podc.ConstantBarriersMutex
