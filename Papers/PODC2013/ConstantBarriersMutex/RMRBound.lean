import Papers.PODC2013.ConstantBarriersMutex.RMRInv

/-!
# Lemma 10 of the paper: RMR bound by an amortized potential

`pot c s p` bounds the number of RMRs `p` may still incur in its current passage, given the
cache `c` and the configuration `s`. Every event satisfies
`cost + pot' ≤ pot + [p is in the remainder section] · (19·h + 23)` (`pot_step`); summing over a
passage gives Lemma 10 (`RMRMain.lean`).

Outside the busy-waiting statements `pot` only depends on the program counter of `p` (a
budget for the remaining program-order steps: every step costs at most one RMR for a read plus
one for an issued write). For the two busy-waiting statements:

* statement 25 (`phi25`): with `x = exits` in memory, while `x ≤ e + 1` the budget is
  `miss(exits) + (e + 2 − x) + F + 1 + [lock ≠ −1 ∧ miss(lock)]`, where
  `F = ⌊(2e + 4 − mu)/2⌋` counts the lock acquisitions (successful CAS or hand-over) that can
  still happen before `exits` reaches `e + 2` (`mu` = `2·exits + [Pend]`, `RMRInv.lean`). Once
  `x ≥ e + 2` the loop ends after at most one more read of `lock` and one of `exits`.
  At entry (`x = e`) this is at most `6` (`phi25_entry`).
* statement 27 (`phi27`): `miss(signal[p]) + [signal[p] = false]` (at most `2`); only one write
  of another process (`signal[p] ← true`) can happen while `p` waits.
-/

-- The case analyses below use generic tactic combinators; some branches do not need every
-- simp lemma or tactic.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Podc.ConstantBarriersMutex

variable {h : ℕ} {s : Cfg h}

/-- `1` if `p` has no valid copy of `v`. -/
def miss (c : Cache h) (p : Proc h) (v : Var h) : ℕ := if c p v = true then 0 else 1

lemma miss_le (c : Cache h) (p : Proc h) (v : Var h) : miss c p v ≤ 1 := by
  unfold miss; split <;> omega

/-- Budget of the exit section (from the critical section on). -/
def exB (h : ℕ) : ℕ := 18 * h + 9

/-- Budget of the exit section from the start of level `l` of the tree traversal. -/
def lvB (h l : ℕ) : ℕ := 18 * (h - l) + 6

/-- The RMR bound of Lemma 10: `19·h + 23 = 19 log n + 23`. -/
def rmrBound (h : ℕ) : ℕ := 19 * h + 23

/-- Potential at statement 25 (`atB`: about to read `lock`, else about to read `exits`). -/
noncomputable def phi25 (c : Cache h) (s : Cfg h) (p : Proc h) (e : ℕ) (atB : Bool) : ℕ :=
  if s.mem.exits ≤ e + 1 then
    miss c p .exits + (e + 2 - s.mem.exits) + (2 * e + 4 - mu s) / 2 + 1 +
      (if s.mem.lock ≠ none ∧ c p .lock = false then 1 else 0)
  else if atB then 2 else 1

/-- Potential at statement 27. -/
def phi27 (c : Cache h) (s : Cfg h) (p : Proc h) : ℕ :=
  miss c p (.signal p) + (if s.mem.signal p = false then 1 else 0)

/-- The potential: an upper bound on the RMRs `p` still incurs in its current passage. -/
noncomputable def pot (c : Cache h) (s : Cfg h) (p : Proc h) : ℕ :=
  match s.pc p with
  | .rem => 0
  | .e18 => h + 13 + exB h
  | .e19 l => l + 12 + exB h
  | .e22 | .e23 => 11 + exB h
  | .e24 => 10 + exB h
  | .e25a e => phi25 c s p e false + 3 + exB h
  | .e25b e => phi25 c s p e true + 3 + exB h
  | .e26 => 3 + exB h
  | .e27 => phi27 c s p + exB h
  | .cs | .x31 => exB h
  | .x32 => 2 + lvB h 0
  | .x34 l j acc => 6 * (3 - min j 2) + 5 * acc.length + lvB h (l + 1)
  | .x35 l cands => 5 * cands.length + lvB h (l + 1)
  | .x36 l _ rest => 4 + 5 * rest.length + lvB h (l + 1)
  | .x37 l _ rest => 3 + 5 * rest.length + lvB h (l + 1)
  | .x38 l _ rest => 1 + 5 * rest.length + lvB h (l + 1)
  | .x42 => 6
  | .x43 => 1
  | .x45 => 5
  | .x46 _ => 3
  | .x47 _ => 2
  | .x48 _ => 1
  | .x50 _ => 0

/-! ### The cache under events -/

lemma upd_other (c : Cache h) (s : Cfg h) (e : Ev h) {p : Proc h} (ha : e.actor ≠ p) (v : Var h) :
    c.upd s e p v = if ∃ w ∈ s.perf e, w.var = v then false else c p v := by
  have hne : e ≠ .step p := by rintro rfl; exact ha rfl
  simp only [Cache.upd, hne, false_and, ite_false, ha, ne_eq, not_false_eq_true, true_and]

lemma upd_self_step (c : Cache h) (s : Cfg h) (p : Proc h) (v : Var h) :
    c.upd s (.step p) p v = if s.rdVar p = some v ∧ ¬ s.fromBuf p v then true else c p v := by
  simp [Cache.upd, Ev.actor]

lemma upd_self_flush (c : Cache h) (s : Cfg h) (p : Proc h) (v : Var h) :
    c.upd s (.flush p) p v = c p v := by
  simp [Cache.upd, Ev.actor]

/-- An event performs writes to at most one variable. -/
lemma Inv.perf_var_unique (hI : Inv s) (e : Ev h) {v v' : Var h}
    (h1 : ∃ w ∈ s.perf e, w.var = v) (h2 : ∃ w ∈ s.perf e, w.var = v') : v = v' := by
  obtain ⟨w, hw, rfl⟩ := h1
  obtain ⟨w', hw', rfl⟩ := h2
  rcases hI.perf_cases e with h0 | ⟨_, _, -, hp, -⟩ | hc
  · simp [h0] at hw
  · rw [hp, List.mem_singleton] at hw hw'; rw [hw, hw']
  · rw [hc.2.2.2.2.1, List.mem_singleton] at hw hw'; rw [hw, hw']

/-! ### Waiting potentials do not increase under events of other processes -/

lemma Inv.phi25_other (hI : Inv s) (c : Cache h) (e : Ev h) {p : Proc h} (ha : e.actor ≠ p)
    (eN : ℕ) (atB : Bool) : phi25 (c.upd s e) (s.next e) p eN atB ≤ phi25 c s p eN atB := by
  have hmu := hI.mu_mono e
  have hmuL := mu_le s
  have hx' := le_mu s
  by_cases hX : ∃ w ∈ s.perf e, w.var = .exits
  · have hx := hI.exits_written e hX
    have hL : ¬ ∃ w ∈ s.perf e, w.var = .lock := fun hL =>
      absurd (hI.perf_var_unique e hX hL) (by simp)
    have hl := (s.next_not_written e hL).1 rfl
    have hcx : c.upd s e p .exits = false := by simp [upd_other c s e ha, hX]
    have hcl : c.upd s e p .lock = c p .lock := by simp [upd_other c s e ha, hL]
    unfold phi25
    rw [hx, hl, hcl]
    simp only [miss, hcx]
    have := miss_le c p .exits
    unfold miss at this
    split_ifs <;> omega
  · have hx := (s.next_not_written e hX).2.1 rfl
    have hcx : c.upd s e p .exits = c p .exits := by simp [upd_other c s e ha, hX]
    by_cases hL : ∃ w ∈ s.perf e, w.var = .lock
    · have hcl : c.upd s e p .lock = false := by simp [upd_other c s e ha, hL]
      unfold phi25
      rw [hx, hcl]
      simp only [miss, hcx]
      rcases hI.lock_written e hL with ⟨⟨k, hk⟩, hmu', hl'⟩ | hl'
      · simp only [hl', ne_eq, not_false_eq_true, and_self, ite_true]
        split_ifs <;> omega
      · simp only [hl', ne_eq, not_true_eq_false, false_and, ite_false]
        split_ifs <;> omega
    · have hl := (s.next_not_written e hL).1 rfl
      have hcl : c.upd s e p .lock = c p .lock := by simp [upd_other c s e ha, hL]
      unfold phi25
      rw [hx, hl, hcl]
      simp only [miss, hcx]
      split_ifs <;> omega

lemma Inv.phi27_other (hI : Inv s) (c : Cache h) (e : Ev h) {p : Proc h} (ha : e.actor ≠ p) :
    phi27 (c.upd s e) (s.next e) p ≤ phi27 c s p := by
  unfold phi27 miss
  by_cases hS : ∃ w ∈ s.perf e, w.var = .signal p
  · obtain ⟨h1, h2⟩ := hI.signal_written e ha hS
    rw [upd_other c s e ha, h1, h2]
    split_ifs <;> simp_all
  · simp only [upd_other c s e ha, hS, (s.next_not_written e hS).2.2.2 p rfl]; rfl

/-! ### Steps of `p` itself -/

lemma Cfg.rcost_le (s : Cfg h) (c : Cache h) (p : Proc h) : s.rcost c p ≤ 1 := by
  unfold Cfg.rcost; split <;> (try split_ifs) <;> omega

lemma Cfg.rcost_eq_miss (s : Cfg h) (c : Cache h) {p : Proc h} {v : Var h}
    (hb : s.buf p = []) (hv : s.rdVar p = some v) : s.rcost c p = miss c p v := by
  simp only [Cfg.rcost, hv, Cfg.fromBuf, hb, miss]
  cases c p v <;> simp

lemma upd_self_read (c : Cache h) (s : Cfg h) {p : Proc h} {v : Var h}
    (hb : s.buf p = []) (hv : s.rdVar p = some v) (v' : Var h) :
    c.upd s (.step p) p v' = if v' = v then true else c p v' := by
  rw [upd_self_step]
  by_cases h' : v' = v
  · subst h'; simp [hv, Cfg.fromBuf, hb]
  · simp [hv, h', Ne.symm h']

lemma upd_self_noread (c : Cache h) (s : Cfg h) {p : Proc h} (hv : s.rdVar p = none)
    (v' : Var h) : c.upd s (.step p) p v' = c p v' := by
  rw [upd_self_step]; simp [hv]

lemma mu_goto (s : Cfg h) (p : Proc h) (c : PC h) (hE : (s.pc p).Entry ↔ c.Entry) :
    mu (s.goto p c) = mu s := by
  have : Pend (s.goto p c) ↔ Pend s := by
    unfold Pend
    simp only [goto_mem, goto_ent]
    apply or_congr Iff.rfl
    apply exists_congr; intro g
    by_cases hg : g = p
    · subst hg; simp [hE]
    · simp [Function.update_of_ne hg]
  unfold mu; simp only [goto_mem]; split_ifs <;> simp_all

/-- At the entry of statement 25 the waiting budget is at most `6`. -/
lemma phi25_entry (c : Cache h) (s : Cfg h) (p : Proc h) (hc : c p .exits = true) :
    phi25 c s p s.mem.exits false ≤ 6 := by
  have := le_mu s
  unfold phi25 miss
  simp only [show s.mem.exits ≤ s.mem.exits + 1 by omega, hc, ite_true]
  split_ifs <;> omega

lemma length_addCand_le (p : Proc h) (acc : List (Proc h)) (o : Option (Proc h)) :
    (addCand p acc o).length ≤ acc.length + 1 := by
  unfold addCand; split
  · omega
  · split_ifs <;> simp

lemma Cfg.cas_pc_self (s : Cfg h) (p : Proc h) (c : PC h) :
    (s.cas p c).pc p = if (s.view p).lock = none then .cs else c := by
  simp only [Cfg.cas, Cfg.view]; split_ifs <;> simp_all

lemma phi27_le (c : Cache h) (s : Cfg h) (p : Proc h) : phi27 c s p ≤ 2 := by
  have := miss_le c p (.signal p); unfold phi27; split_ifs <;> omega

lemma phi25_pos (c : Cache h) (s : Cfg h) (p : Proc h) (e : ℕ) (atB : Bool) :
    1 ≤ phi25 c s p e atB := by
  unfold phi25; split_ifs <;> omega

/-- A step of `p` costs at most the decrease of the potential (plus the passage budget when the
step starts a passage). -/
lemma Inv.pot_own (hI : Inv s) (hX : X45 s) (c : Cache h) (p : Proc h) :
    s.wcost p + s.rcost c p + pot (c.upd s (.step p)) (s.stepProc p) p ≤
      pot c s p + (if s.pc p = .rem then rmrBound h else 0) := by
  have hr := s.rcost_le c p
  have hL := hI.loc p
  rcases hpc : s.pc p with _ | _ | l | _ | _ | _ | e | e | _ | _ | _ | _ | _ | ⟨l, j, acc⟩ |
    ⟨l, (_ | ⟨q, cands⟩)⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | _ | _ | _ | nx | nx | nx | o <;>
    simp only [LI, hpc] at hL
  all_goals first
    | (simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, issue_pc, goto_pc, Function.update_self,
        Cfg.rcost, Cfg.rdVar, Cfg.barrier, reduceCtorEq, ↓reduceIte, rmrBound, exB, lvB]
       (try split_ifs) <;>
         (try simp only [flush_pc, goto_pc, hpc, Function.update_self, rmrBound, exB, lvB,
           Nat.min_def, List.length_nil, List.length_cons]) <;>
         (try split_ifs) <;> omega)
    | skip
  case x34 =>
    have h1 := length_addCand_le p acc ((s.view p).node (target (anc p l) j))
    simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, goto_pc, Function.update_self, lvB]
    split_ifs <;> simp only [Nat.min_def] <;> split_ifs <;> omega
  case x45 =>
    have hne := hX p hpc
    obtain ⟨nx, rest, hq⟩ : ∃ nx rest, (s.view p).promQ = nx :: rest := by
      cases h' : (s.view p).promQ with
      | nil => exact absurd h' hne
      | cons a b => exact ⟨a, b, rfl⟩
    simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, hq, issue_pc, Function.update_self,
      reduceCtorEq, ↓reduceIte]
    omega
  case e23 =>
    simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, Cfg.rcost, Cfg.rdVar, Cfg.cas_pc_self,
      reduceCtorEq, ↓reduceIte]
    split_ifs <;> simp only [exB] <;> omega
  case e26 =>
    have := phi27_le (c.upd s (.step p)) (s.cas p .e27) p
    simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, Cfg.rcost, Cfg.rdVar, Cfg.cas_pc_self,
      reduceCtorEq, ↓reduceIte]
    split_ifs <;> simp only [exB] <;> omega
  case e24 =>
    obtain ⟨hb, -⟩ := hL
    have hv : s.view p = s.mem := by simp [Cfg.view, hb]
    have hrd : s.rdVar p = some .exits := by simp [Cfg.rdVar, hpc]
    have hcx : c.upd s (.step p) p .exits = true := by rw [upd_self_read c s hb hrd]; simp
    have h6 := phi25_entry (c.upd s (.step p)) (s.goto p (.e25a s.mem.exits)) p hcx
    have := miss_le c p .exits
    rw [s.rcost_eq_miss c hb hrd]
    simp only [goto_mem] at h6
    simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, hv, goto_pc, Function.update_self]
    omega
  case e25a =>
    obtain ⟨hb, -⟩ := hL
    have hv : s.view p = s.mem := by simp [Cfg.view, hb]
    have hrd : s.rdVar p = some .exits := by simp [Cfg.rdVar, hpc]
    have hcx : c.upd s (.step p) p .exits = true := by rw [upd_self_read c s hb hrd]; simp
    have hcl : c.upd s (.step p) p .lock = c p .lock := by rw [upd_self_read c s hb hrd]; simp
    have := miss_le c p .exits
    have := phi25_pos c s p e false
    rw [s.rcost_eq_miss c hb hrd]
    simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, hv, goto_pc, Function.update_self,
      reduceCtorEq, ↓reduceIte, add_zero]
    split_ifs with hx
    · simp only; omega
    · have hmu := mu_goto s p (.e25b e) (by simp [hpc, PC.Entry])
      simp only
      unfold phi25
      simp only [goto_mem, hmu, hcx, hcl, miss]
      split_ifs <;> omega
  case e25b =>
    obtain ⟨hb, -⟩ := hL
    have hv : s.view p = s.mem := by simp [Cfg.view, hb]
    have hrd : s.rdVar p = some .lock := by simp [Cfg.rdVar, hpc]
    have hcl : c.upd s (.step p) p .lock = true := by rw [upd_self_read c s hb hrd]; simp
    have hcx : c.upd s (.step p) p .exits = c p .exits := by rw [upd_self_read c s hb hrd]; simp
    have := miss_le c p .lock
    have := phi25_pos c s p e true
    rw [s.rcost_eq_miss c hb hrd]
    simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, hv, goto_pc, Function.update_self,
      reduceCtorEq, ↓reduceIte, add_zero]
    split_ifs with hl
    · simp only; omega
    · have hmu := mu_goto s p (.e25a e) (by simp [hpc, PC.Entry])
      have hln : s.mem.lock ≠ none := fun h' => hl (Or.inr h')
      simp only
      unfold phi25
      simp only [goto_mem, hmu, hcx, hcl, miss, hln, ne_eq, not_false_eq_true, true_and]
      split_ifs <;> simp_all <;> omega
  case e27 =>
    obtain ⟨hb, -⟩ := hL
    have hv : s.view p = s.mem := by simp [Cfg.view, hb]
    have hrd : s.rdVar p = some (.signal p) := by simp [Cfg.rdVar, hpc]
    have hcs : c.upd s (.step p) p (.signal p) = true := by rw [upd_self_read c s hb hrd]; simp
    have := miss_le c p (.signal p)
    rw [s.rcost_eq_miss c hb hrd]
    simp only [pot, Cfg.stepProc, Cfg.wcost, hpc, hv, reduceCtorEq, ↓reduceIte, add_zero]
    split_ifs with hs
    · simp only [goto_pc, Function.update_self, phi27, hs]
      simp
    · simp only [hpc, phi27, hcs, miss, hs]
      simp; omega

/-! ### All events -/

lemma Inv.pot_other (hI : Inv s) (c : Cache h) (e : Ev h) {p : Proc h} (ha : e.actor ≠ p) :
    pot (c.upd s e) (s.next e) p ≤ pot c s p := by
  have hpc' := s.pc_next_of_ne_actor e ha
  unfold pot
  rw [hpc']
  split
  · exact le_rfl
  all_goals first
    | exact le_rfl
    | (have := hI.phi25_other c e ha ‹_› false; omega)
    | (have := hI.phi25_other c e ha ‹_› true; omega)
    | (have := hI.phi27_other c e ha; omega)

lemma pot_congr_cache {c c' : Cache h} {p : Proc h} (hc : ∀ v, c' p v = c p v) (s : Cfg h) :
    pot c' s p = pot c s p := by
  unfold pot phi25 phi27 miss
  simp only [hc]

lemma Inv.pot_flush_self (hI : Inv s) (c : Cache h) (p : Proc h) :
    pot (c.upd s (.flush p)) (s.flush p) p ≤ pot c s p := by
  rw [pot_congr_cache (upd_self_flush c s p)]
  have hL := hI.loc p
  rcases hpc : s.pc p with _ | _ | l | _ | _ | _ | e | e | _ | _ | _ | _ | _ | ⟨l, j, acc⟩ |
    ⟨l, c⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | _ | _ | _ | nx | nx | nx | o <;>
    simp only [LI, hpc] at hL
  all_goals first
    | (rw [flush_of_nil _ _ hL.1])
    | (simp only [pot, flush_pc, hpc]; exact le_rfl)

/-- **Per-event inequality**: the RMRs incurred by `p` in an event are bounded by the decrease
of the potential, plus `19·h + 23` for the step that starts a passage. -/
theorem Inv.pot_step (hI : Inv s) (hX : X45 s) (c : Cache h) (e : Ev h) (p : Proc h) :
    evCost c s e p + pot (c.upd s e) (s.next e) p ≤
      pot c s p + (if s.pc p = .rem then rmrBound h else 0) := by
  by_cases he : e = .step p
  · subst he
    simp only [evCost, ite_true, Cfg.next]
    exact hI.pot_own hX c p
  · simp only [evCost, he, ite_false, zero_add]
    by_cases ha : e.actor = p
    · cases e with
      | step q => simp [Ev.actor] at ha; exact absurd (congrArg Ev.step ha) he
      | flush q =>
        simp only [Ev.actor] at ha; subst ha
        exact (hI.pot_flush_self c q).trans (Nat.le_add_right _ _)
    · exact (hI.pot_other c e ha).trans (Nat.le_add_right _ _)

end Podc.ConstantBarriersMutex
