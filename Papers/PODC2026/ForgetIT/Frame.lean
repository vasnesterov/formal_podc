import Papers.PODC2026.ForgetIT.Spec

/-!
# Frame lemmas: how each rule changes each field of the local state
-/

set_option linter.unusedSectionVars false

namespace Podc.ForgetIT

variable {P Val : Type} [Fintype P] [DecidableEq P] [DecidableEq Val]
variable {prm : Params P} {p : P}

section helpers

variable (V : ℕ) (g : Option (GV Val)) (s : LS P Val)

@[simp] lemma ensureVC_vote1 : (ensureVC V g s).1.vote1 = s.vote1 := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_view : (ensureVC V g s).1.view = s.view := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_guard : (ensureVC V g s).1.guard = s.guard := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_lock : (ensureVC V g s).1.lock = s.lock := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_vtp : (ensureVC V g s).1.vtp = s.vtp := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_pot : (ensureVC V g s).1.pot = s.pot := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_alert : (ensureVC V g s).1.alert = s.alert := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_echo : (ensureVC V g s).1.echo = s.echo := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_echoS : (ensureVC V g s).1.echoS = s.echoS := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_rcv : (ensureVC V g s).1.rcv = s.rcv := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_acc : (ensureVC V g s).1.acc = s.acc := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_prop : (ensureVC V g s).1.prop = s.prop := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_entered : (ensureVC V g s).1.entered = s.entered := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_clk : (ensureVC V g s).1.clk = s.clk := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_active : (ensureVC V g s).1.active = s.active := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_out : (ensureVC V g s).1.out = s.out := by
  unfold ensureVC; split <;> rfl
@[simp] lemma ensureVC_decided : (ensureVC V g s).1.decided = s.decided := by
  unfold ensureVC; split <;> rfl

lemma ensureVC_vote2 (W : ℕ) :
    (ensureVC V g s).1.vote2 W = if W = V ∧ s.vote2 V = none then some (none, g) else s.vote2 W := by
  unfold ensureVC; split <;> rename_i h <;> by_cases hW : W = V <;> simp_all

lemma ensureVC_vote2' (W : ℕ) :
    (ensureVC V g s).1.vote2 W = s.vote2 W ∨
      (s.vote2 W = none ∧ W = V ∧ (ensureVC V g s).1.vote2 W = some (none, g)) := by
  rw [ensureVC_vote2]
  by_cases h : W = V
  · subst h; by_cases h' : s.vote2 W = none <;> simp [h']
  · simp [h]

lemma ensureVC_vote2_self (h : s.vote2 V = none) :
    (ensureVC V g s).1.vote2 V = some (none, g) := by
  rw [ensureVC_vote2]; simp [h]

lemma ensureVC_vote2_some {W : ℕ} {x} (h : s.vote2 W = some x) :
    (ensureVC V g s).1.vote2 W = some x := by
  rcases ensureVC_vote2' V g s W with h' | ⟨h1, -, -⟩
  · rw [h', h]
  · simp_all

lemma ensureVC_vote2_none {W : ℕ} (h : (ensureVC V g s).1.vote2 W = none) : s.vote2 W = none := by
  rcases ensureVC_vote2' V g s W with h' | ⟨h1, -, -⟩
  · rw [← h', h]
  · exact h1

lemma ensureVC_vc (W : ℕ) : (ensureVC V g s).1.vc W = true ↔ W = V ∨ s.vc W = true := by
  unfold ensureVC; split <;> by_cases hW : W = V <;> simp_all

lemma mem_ensureVC {m : Msg Val} (h : m ∈ (ensureVC V g s).2) :
    m = .vote2 V none g ∧ s.vote2 V = none := by
  unfold ensureVC at h; split at h <;> simp_all

variable (k : Fin 3) (x : GV Val)

@[simp] lemma sendEcho_vote1 : (sendEcho k V x s).1.vote1 = s.vote1 := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_vote2 : (sendEcho k V x s).1.vote2 = s.vote2 := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_view : (sendEcho k V x s).1.view = s.view := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_guard : (sendEcho k V x s).1.guard = s.guard := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_lock : (sendEcho k V x s).1.lock = s.lock := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_vtp : (sendEcho k V x s).1.vtp = s.vtp := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_pot : (sendEcho k V x s).1.pot = s.pot := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_alert : (sendEcho k V x s).1.alert = s.alert := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_vc : (sendEcho k V x s).1.vc = s.vc := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_rcv : (sendEcho k V x s).1.rcv = s.rcv := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_acc : (sendEcho k V x s).1.acc = s.acc := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_prop : (sendEcho k V x s).1.prop = s.prop := by
  unfold sendEcho; split <;> (try split) <;> rfl
@[simp] lemma sendEcho_decided : (sendEcho k V x s).1.decided = s.decided := by
  unfold sendEcho; split <;> (try split) <;> rfl

/-- How `sendEcho` changes the echo slots. -/
lemma sendEcho_echo (k' : Fin 3) (W : ℕ) :
    (sendEcho k V x s).1.echo k' W =
      if k' = k ∧ W = V ∧ s.echo k V = none then some x else s.echo k' W := by
  unfold sendEcho
  split <;> rename_i h
  · by_cases hk : k' = k <;> by_cases hW : W = V <;> simp_all
  · split <;> simp_all

lemma sendEcho_echoS (k' : Fin 3) (W : ℕ) :
    (sendEcho k V x s).1.echoS k' W = true ↔ s.echoS k' W = true ∨
      (k' = k ∧ W = V ∧ ∃ y, s.echo k V = some y ∧ s.echoS k V = false ∧ y ≠ .safe ∧
        (x = .safe ∨ x ≠ y)) := by
  unfold sendEcho
  split <;> rename_i h
  · simp_all
  · split <;> rename_i h'
    · by_cases hk : k' = k <;> by_cases hW : W = V <;> simp_all
    · constructor
      · intro h1; exact Or.inl h1
      · rintro (h1 | ⟨rfl, rfl, y, hy, h2, h3, h4⟩)
        · exact h1
        · simp_all

lemma mem_sendEcho {m : Msg Val} (h : m ∈ (sendEcho k V x s).2) :
    (m = .echo k V x ∧ s.echo k V = none) ∨
    (m = .echo k V .safe ∧ ∃ y, s.echo k V = some y ∧ s.echoS k V = false ∧ y ≠ .safe ∧
        (x = .safe ∨ x ≠ y)) := by
  unfold sendEcho at h
  split at h <;> rename_i h1
  · simp_all
  · split at h <;> simp_all

end helpers

section enter

variable (prm : Params P) (p : P) (V : ℕ) (s : LS P Val)

@[simp] lemma enterV_view : (enterV prm p V s).1.view = V := by simp [enterV]
@[simp] lemma enterV_vote1 : (enterV prm p V s).1.vote1 = s.vote1 := by simp [enterV]
@[simp] lemma enterV_guard : (enterV prm p V s).1.guard = s.guard := by simp [enterV]
@[simp] lemma enterV_lock : (enterV prm p V s).1.lock = s.lock := by simp [enterV]
@[simp] lemma enterV_vtp : (enterV prm p V s).1.vtp = s.vtp := by simp [enterV]
@[simp] lemma enterV_pot : (enterV prm p V s).1.pot = s.pot := by simp [enterV]
@[simp] lemma enterV_alert : (enterV prm p V s).1.alert = s.alert := by simp [enterV]
@[simp] lemma enterV_echo : (enterV prm p V s).1.echo = s.echo := by simp [enterV]
@[simp] lemma enterV_echoS : (enterV prm p V s).1.echoS = s.echoS := by simp [enterV]
@[simp] lemma enterV_rcv : (enterV prm p V s).1.rcv = s.rcv := by simp [enterV]
@[simp] lemma enterV_acc : (enterV prm p V s).1.acc = s.acc := by simp [enterV]
@[simp] lemma enterV_prop : (enterV prm p V s).1.prop = s.prop := by simp [enterV]
@[simp] lemma enterV_decided : (enterV prm p V s).1.decided = s.decided := by simp [enterV]

lemma enterV_vote2 (W : ℕ) :
    (enterV prm p V s).1.vote2 W = s.vote2 W ∨
      (s.vote2 W = none ∧ (W = V - 2 ∨ W = V - 1) ∧
        (enterV prm p V s).1.vote2 W = some (none, s.guard V)) := by
  simp only [enterV]
  set s0 : LS P Val := { s with view := V, entered := s.clk, active := true }
  have e0 : s0.vote2 = s.vote2 := rfl
  set r1 := ensureVC (V - 2) (s.guard V) s0
  rcases ensureVC_vote2' (V - 1) (s.guard V) r1.1 W with h | ⟨h1, h2, h3⟩
  · rw [h]
    rcases ensureVC_vote2' (V - 2) (s.guard V) s0 W with h' | ⟨h1', h2', h3'⟩
    · left; rw [h', e0]
    · right; exact ⟨h1', Or.inl h2', h3'⟩
  · right; exact ⟨e0 ▸ ensureVC_vote2_none _ _ _ h1, Or.inr h2, h3⟩

lemma enterV_vc (W : ℕ) :
    (enterV prm p V s).1.vc W = true ↔ W = V - 2 ∨ W = V - 1 ∨ s.vc W = true := by
  simp only [enterV, ensureVC_vc]; tauto

lemma mem_enterV {m : Msg Val} (h : m ∈ (enterV prm p V s).2) :
    (∃ W, m = .vote2 W none (s.guard V) ∧ s.vote2 W = none ∧ (W = V - 2 ∨ W = V - 1) ∧
      (enterV prm p V s).1.vote2 W = some (none, s.guard V)) ∨ ∃ w, m = .prepare V w := by
  simp only [enterV, List.mem_append] at h ⊢
  set s0 : LS P Val := { s with view := V, entered := s.clk, active := true }
  have e0 : s0.vote2 = s.vote2 := rfl
  set r1 := ensureVC (V - 2) (s.guard V) s0
  rcases h with (h | h) | h
  · obtain ⟨rfl, h2⟩ := mem_ensureVC _ _ _ h
    refine Or.inl ⟨_, rfl, e0 ▸ h2, Or.inl rfl, ensureVC_vote2_some _ _ _ ?_⟩
    exact ensureVC_vote2_self _ _ _ h2
  · obtain ⟨rfl, h2⟩ := mem_ensureVC _ _ _ h
    refine Or.inl ⟨_, rfl, e0 ▸ ensureVC_vote2_none _ _ _ h2, Or.inr rfl, ?_⟩
    exact ensureVC_vote2_self _ _ _ h2
  · split_ifs at h
    · split at h <;> simp_all
    · simp at h

@[simp] lemma passiveV_view : (passiveV V s).1.view = V := by simp [passiveV]
@[simp] lemma passiveV_vote1 : (passiveV V s).1.vote1 = s.vote1 := by simp [passiveV]
@[simp] lemma passiveV_guard : (passiveV V s).1.guard = s.guard := by simp [passiveV]
@[simp] lemma passiveV_lock : (passiveV V s).1.lock = s.lock := by simp [passiveV]
@[simp] lemma passiveV_vtp : (passiveV V s).1.vtp = s.vtp := by simp [passiveV]
@[simp] lemma passiveV_pot : (passiveV V s).1.pot = s.pot := by simp [passiveV]
@[simp] lemma passiveV_alert : (passiveV V s).1.alert = s.alert := by simp [passiveV]
@[simp] lemma passiveV_echo : (passiveV V s).1.echo = s.echo := by simp [passiveV]
@[simp] lemma passiveV_echoS : (passiveV V s).1.echoS = s.echoS := by simp [passiveV]
@[simp] lemma passiveV_rcv : (passiveV V s).1.rcv = s.rcv := by simp [passiveV]
@[simp] lemma passiveV_acc : (passiveV V s).1.acc = s.acc := by simp [passiveV]
@[simp] lemma passiveV_prop : (passiveV V s).1.prop = s.prop := by simp [passiveV]
@[simp] lemma passiveV_decided : (passiveV V s).1.decided = s.decided := by simp [passiveV]

lemma passiveV_vote2 (W : ℕ) :
    (passiveV V s).1.vote2 W = s.vote2 W ∨
      (s.vote2 W = none ∧ (W = V - 2 ∨ W = V - 1 ∨ W = V) ∧
        (passiveV V s).1.vote2 W = some (none, s.guard V)) := by
  simp only [passiveV]
  set s0 : LS P Val := { s with view := V, entered := s.clk, active := false }
  have e0 : s0.vote2 = s.vote2 := rfl
  set r1 := ensureVC (V - 2) (s.guard V) s0
  set r2 := ensureVC (V - 1) (s.guard V) r1.1
  rcases ensureVC_vote2' V (s.guard V) r2.1 W with h | ⟨h1, h2, h3⟩
  · rw [h]
    rcases ensureVC_vote2' (V - 1) (s.guard V) r1.1 W with h | ⟨h1, h2, h3⟩
    · rw [h]
      rcases ensureVC_vote2' (V - 2) (s.guard V) s0 W with h' | ⟨h1', h2', h3'⟩
      · left; rw [h', e0]
      · right; exact ⟨h1', Or.inl h2', h3'⟩
    · right; exact ⟨e0 ▸ ensureVC_vote2_none _ _ _ h1, Or.inr (Or.inl h2), h3⟩
  · right
    exact ⟨e0 ▸ ensureVC_vote2_none _ _ _ (ensureVC_vote2_none _ _ _ h1), Or.inr (Or.inr h2), h3⟩

lemma passiveV_vc (W : ℕ) :
    (passiveV V s).1.vc W = true ↔ W = V - 2 ∨ W = V - 1 ∨ W = V ∨ s.vc W = true := by
  simp only [passiveV, ensureVC_vc]; tauto

lemma mem_passiveV {m : Msg Val} (h : m ∈ (passiveV V s).2) :
    ∃ W, m = .vote2 W none (s.guard V) ∧ s.vote2 W = none ∧ (W = V - 2 ∨ W = V - 1 ∨ W = V) ∧
      (passiveV V s).1.vote2 W = some (none, s.guard V) := by
  simp only [passiveV, List.mem_append] at h ⊢
  set s0 : LS P Val := { s with view := V, entered := s.clk, active := false }
  have e0 : s0.vote2 = s.vote2 := rfl
  set r1 := ensureVC (V - 2) (s.guard V) s0
  set r2 := ensureVC (V - 1) (s.guard V) r1.1
  rcases h with (h | h) | h
  · obtain ⟨rfl, h2⟩ := mem_ensureVC _ _ _ h
    refine ⟨_, rfl, e0 ▸ h2, Or.inl rfl, ensureVC_vote2_some _ _ _ (ensureVC_vote2_some _ _ _ ?_)⟩
    exact ensureVC_vote2_self _ _ _ h2
  · obtain ⟨rfl, h2⟩ := mem_ensureVC _ _ _ h
    refine ⟨_, rfl, e0 ▸ ensureVC_vote2_none _ _ _ h2, Or.inr (Or.inl rfl),
      ensureVC_vote2_some _ _ _ ?_⟩
    exact ensureVC_vote2_self _ _ _ h2
  · obtain ⟨rfl, h2⟩ := mem_ensureVC _ _ _ h
    refine ⟨_, rfl, e0 ▸ ensureVC_vote2_none _ _ _ (ensureVC_vote2_none _ _ _ h2),
      Or.inr (Or.inr rfl), ?_⟩
    exact ensureVC_vote2_self _ _ _ h2

end enter

section execLemmas

variable (prm : Params P) (p : P) (s : LS P Val)

@[simp] lemma setGuard_vote2 (V x) : (setGuard V x s).vote2 = s.vote2 := rfl
@[simp] lemma setVtp_vote2 (V w) : (setVtp V w s).vote2 = s.vote2 := rfl
@[simp] lemma setGuard_guard (V x) : (setGuard V x s).guard = Function.update s.guard V (some x) :=
  rfl
@[simp] lemma setVtp_guard (V w) : (setVtp V w s).guard = s.guard := rfl

/-- The (messages-of-a-process) state reflects a broadcast message. -/
def Refl (s : LS P Val) : Msg Val → Prop
  | .vote1 W v => s.vote1 W = some v
  | .vote2 W l g => s.vote2 W = some (l, g)
  | .echo k W x => s.echo k W = some x ∨ (x = .safe ∧ s.echoS k W = true)
  | .prepare _ _ => True

/-- Which rule may set an echo slot `(k, W)` to `x`. -/
def EchoSrc : Act P Val → Fin 3 → ℕ → GV Val → Prop
  | .echoLock V _ x, k, W, y => k = 0 ∧ W = V ∧ y = .val x
  | .echoGuard V G, k, W, y => k = 0 ∧ W = V ∧ y = G
  | .echoDiv V, k, W, y => k = 0 ∧ W = V ∧ y = .safe
  | .echo2 V x, k, W, y => k = 1 ∧ W = V ∧ y = x
  | .echo3 V x, k, W, y => k = 2 ∧ W = V ∧ y = x
  | _, _, _, _ => False

lemma exec_rcv (a : Act P Val) : (exec prm p a s).1.rcv = s.rcv := by
  cases a <;> simp [exec, setGuard, setVtp] <;> split <;> simp

lemma exec_prop (a : Act P Val) : (exec prm p a s).1.prop = s.prop := by
  cases a <;> simp [exec, setGuard, setVtp] <;> split <;> simp

lemma exec_vote1 (a : Act P Val) (W : ℕ) :
    (exec prm p a s).1.vote1 W = s.vote1 W ∨
      ∃ w, a = .vote1 w ∧ W = s.view ∧ (exec prm p a s).1.vote1 W = some w := by
  cases a <;> simp [exec, setGuard, setVtp]
  case vote1 w => by_cases h : W = s.view <;> simp [h]
  all_goals split <;> simp

lemma exec_lock (a : Act P Val) (W : ℕ) :
    (exec prm p a s).1.lock W = s.lock W ∨
      ∃ v, a = .lock v ∧ W = s.view ∧ (exec prm p a s).1.lock W = some v := by
  cases a <;> simp [exec, setGuard, setVtp]
  case lock w => by_cases h : W = s.view <;> simp [h]
  all_goals split <;> simp

lemma exec_pot (a : Act P Val) (W : ℕ) :
    (exec prm p a s).1.pot W = s.pot W ∨
      ∃ ℓ, a = .alertSet W (some ℓ) ∧ (exec prm p a s).1.pot W = some ℓ := by
  cases a <;> simp [exec, setGuard, setVtp]
  case alertSet V ol =>
    cases ol <;> simp
    by_cases h : W = V <;> simp [h]
  all_goals split <;> simp

lemma exec_alert (a : Act P Val) (W : ℕ) :
    (exec prm p a s).1.alert W = s.alert W ∨
      (∃ ol, a = .alertSet W ol ∧ (exec prm p a s).1.alert W = some ol.isSome) ∨
      ((a = .alertClear1 W ∨ a = .alertClear2 W) ∧ (exec prm p a s).1.alert W = some false) := by
  cases a <;> simp [exec, setGuard, setVtp]
  case alertSet V ol =>
    cases ol <;> simp <;> by_cases h : W = V <;> simp [h]
  case alertClear1 V => by_cases h : W = V <;> simp [h]
  case alertClear2 V => by_cases h : W = V <;> simp [h]
  all_goals split <;> simp

lemma exec_acc (a : Act P Val) (V : ℕ) (q : P) :
    (exec prm p a s).1.acc V q = s.acc V q ∨
      ∃ l g, a = .accept V q l g ∧ (exec prm p a s).1.acc V q = some (l, g) := by
  cases a <;> simp [exec, setGuard, setVtp]
  case accept V' q' l g =>
    by_cases h : V = V' <;> by_cases h' : q = q' <;> simp [h, h']
  all_goals split <;> simp

lemma exec_vc (a : Act P Val) {W : ℕ} (h : s.vc W = true) : (exec prm p a s).1.vc W = true := by
  cases a <;> simp [exec, setGuard, setVtp]
  case vcTimer => by_cases h' : W = s.view <;> simp [h, h']
  case enter3 => rw [enterV_vc]; simp [h]
  case enter3L => rw [enterV_vc]; simp [h]
  case enterPrep => rw [enterV_vc]; simp [h]
  case passive V x =>
    split
    · rw [passiveV_vc]; simp [h]
    · rw [ensureVC_vc]; simp [h]
  case recover => split <;> simp [h]
  all_goals first | exact h | (split <;> simp [h])

lemma exec_echo (a : Act P Val) (k : Fin 3) (W : ℕ) :
    (exec prm p a s).1.echo k W = s.echo k W ∨
      (s.echo k W = none ∧ ∃ x, (exec prm p a s).1.echo k W = some x ∧ EchoSrc a k W x) := by
  cases a <;> simp [exec, setGuard, setVtp, EchoSrc]
  all_goals first
    | (split <;> simp)
    | (rw [sendEcho_echo]; split_ifs with h <;> simp_all)

lemma exec_echoS (a : Act P Val) (k : Fin 3) (W : ℕ) (h : (exec prm p a s).1.echoS k W = true) :
    s.echoS k W = true ∨ ∃ x y, EchoSrc a k W x ∧ s.echo k W = some y ∧ s.echoS k W = false ∧
      y ≠ .safe ∧ (x = .safe ∨ x ≠ y) := by
  cases a <;> simp [exec, setGuard, setVtp, EchoSrc] at h ⊢
  all_goals first
    | exact h
    | (split at h <;> simp_all)
    | (rw [sendEcho_echoS] at h; rcases h with h | ⟨rfl, rfl, y, hy⟩
       · exact Or.inl h
       · right; refine ⟨⟨rfl, rfl⟩, y, ?_⟩; simp_all)

/-- Where a new `vote-2` entry `(l, g)` for view `W` comes from. -/
def V2Src (prm : Params P) (p : P) (a : Act P Val) (s : LS P Val) (W : ℕ) : Prop :=
  ∃ l g, (exec prm p a s).1.vote2 W = some (l, g) ∧
    (∀ x, l = some x → (a = .lock x ∧ W = s.view) ∨ s.lock W = some x) ∧
    ((W = s.view ∧ g = s.guard s.view) ∨
      (W ≤ (exec prm p a s).1.view ∧ g = (exec prm p a s).1.guard (exec prm p a s).1.view) ∨
      ∃ y, g = some y ∧ cert s 0 (prm.f + 1) W y)

lemma exec_vote2 (a : Act P Val) (hen : En prm p a s) (W : ℕ) :
    (exec prm p a s).1.vote2 W = s.vote2 W ∨ (s.vote2 W = none ∧ V2Src prm p a s W) := by
  unfold V2Src
  cases a
  case lock v =>
    obtain ⟨-, -, h3⟩ := hen
    by_cases h : W = s.view
    · subst h; right; refine ⟨h3, some v, s.guard s.view, by simp [exec], by simp, Or.inl ⟨rfl, rfl⟩⟩
    · left; simp [exec, h]
  case timeout2 =>
    by_cases h : W = s.view
    · subst h; right
      refine ⟨hen, s.lock s.view, s.guard s.view, by simp [exec], by simp, Or.inl ⟨rfl, rfl⟩⟩
    · left; simp [exec, h]
  case recover =>
    simp only [exec]
    split <;> rename_i h0
    · by_cases h : W = s.view
      · subst h; right
        refine ⟨h0, s.lock s.view, s.guard s.view, by simp, by simp, Or.inl ⟨rfl, rfl⟩⟩
      · left; simp [h]
    · left; rfl
  case enter3 V x =>
    simp only [exec]
    rcases enterV_vote2 prm p (V + 1) (setGuard (V + 1) x s) W with h | ⟨h1, h2, h3⟩
    · left; simpa using h
    · right; refine ⟨by simpa using h1, _, _, h3, by simp, Or.inr (Or.inl ⟨?_, by simp⟩)⟩
      simp only [enterV_view]; omega
  case enter3L V x =>
    simp only [exec]
    rcases enterV_vote2 prm p (V + 1) (setVtp (V + 1) (gvOr x s.prop) (setGuard (V + 1) x s)) W
      with h | ⟨h1, h2, h3⟩
    · left; simpa using h
    · right; refine ⟨by simpa using h1, _, _, h3, by simp, Or.inr (Or.inl ⟨?_, by simp⟩)⟩
      simp only [enterV_view]; omega
  case enterPrep V w x =>
    simp only [exec]
    rcases enterV_vote2 prm p V (setGuard V x s) W with h | ⟨h1, h2, h3⟩
    · left; simpa using h
    · right; refine ⟨by simpa using h1, _, _, h3, by simp, Or.inr (Or.inl ⟨?_, by simp⟩)⟩
      simp only [enterV_view]; omega
  case passive V x =>
    obtain ⟨hc, hv⟩ := hen
    simp only [exec]
    split <;> rename_i hlt
    · rcases passiveV_vote2 V (setGuard V x s) W with h | ⟨h1, h2, h3⟩
      · left; simpa using h
      · right; refine ⟨by simpa using h1, _, _, h3, by simp, Or.inr (Or.inl ⟨?_, by simp⟩)⟩
        simp only [passiveV_view]; omega
    · have hV : V = s.view := by omega
      subst hV
      rcases ensureVC_vote2' s.view (some x) s W with h | ⟨h1, h2, h3⟩
      · left; exact h
      · right; subst h2; exact ⟨h1, _, _, h3, by simp, Or.inr (Or.inr ⟨x, rfl, hc⟩)⟩
  case alertSet V ol => left; simp only [exec]; split <;> rfl
  all_goals left; simp [exec, setGuard]

lemma cert_mono {s : LS P Val} {k : Fin 3} {th th' V : ℕ} {x : GV Val} (h : cert s k th V x)
    (h' : th' ≤ th) : cert s k th' V x := le_trans h' h

lemma exec_guard (a : Act P Val) (hen : En prm p a s) (W : ℕ) :
    (exec prm p a s).1.guard W = s.guard W ∨
      (∃ x, a = .clearGuard x ∧ W = s.view ∧ (exec prm p a s).1.guard W = some .safe) ∨
      (W = (exec prm p a s).1.view ∧ s.view < W ∧ ∃ k W' y, (exec prm p a s).1.guard W = some y ∧
        cert s k (prm.f + 1) W' y ∧ W ≤ W' + 1) := by
  cases a
  case clearGuard x =>
    by_cases h : W = s.view
    · subst h; right; left; exact ⟨x, rfl, rfl, by simp [exec]⟩
    · left; simp [exec, h]
  case enter3 V x =>
    obtain ⟨hc, hv, -⟩ := hen
    by_cases h : W = V + 1
    · subst h; right; right
      exact ⟨by simp [exec], by omega, 2, V, x, by simp [exec], cert_mono hc (by omega), le_refl _⟩
    · left; simp [exec, h]
  case enter3L V x =>
    obtain ⟨hc, hv, -⟩ := hen
    by_cases h : W = V + 1
    · subst h; right; right
      exact ⟨by simp [exec], by omega, 2, V, x, by simp [exec], hc, le_refl _⟩
    · left; simp [exec, h]
  case enterPrep V w x =>
    obtain ⟨-, hv, hc⟩ := hen
    by_cases h : W = V
    · subst h; right; right
      exact ⟨by simp [exec], hv, 1, W - 1, x, by simp [exec], hc, by omega⟩
    · left; simp [exec, h]
  case passive V x =>
    obtain ⟨hc, hv⟩ := hen
    simp only [exec]
    split <;> rename_i hlt
    · by_cases h : W = V
      · subst h; right; right; exact ⟨by simp, hlt, 0, W, x, by simp, hc, by omega⟩
      · left; simp [h]
    · left; simp
  case recover => left; simp only [exec]; split <;> rfl
  case alertSet V ol => left; simp only [exec]; split <;> rfl
  all_goals left; simp [exec]

lemma exec_view (a : Act P Val) (hen : En prm p a s) :
    (exec prm p a s).1.view = s.view ∨
      (s.view < (exec prm p a s).1.view ∧ (exec prm p a s).1.guard (exec prm p a s).1.view ≠ none) := by
  cases a
  case enter3 V x => right; obtain ⟨-, hv, -⟩ := hen; simp [exec]; omega
  case enter3L V x => right; obtain ⟨-, hv, -⟩ := hen; simp [exec]; omega
  case enterPrep V w x => right; obtain ⟨-, hv, -⟩ := hen; simp [exec]; omega
  case passive V x =>
    simp only [exec]; split <;> rename_i h
    · right; simp [h]
    · left; simp
  case recover => left; simp only [exec]; split <;> rfl
  case alertSet V ol => left; simp only [exec]; split <;> rfl
  all_goals left; simp [exec, setGuard]

lemma exec_vtp (a : Act P Val) (W : ℕ) :
    (exec prm p a s).1.vtp W = s.vtp W ∨
      ∃ V x, a = .enter3L V x ∧ W = V + 1 ∧ (exec prm p a s).1.vtp W = some (gvOr x s.prop) := by
  cases a
  case enter3L V x =>
    by_cases h : W = V + 1
    · subst h; right; exact ⟨V, x, rfl, rfl, by simp [exec, setVtp]⟩
    · left; simp [exec, setVtp, setGuard, h]
  case passive V x => left; simp only [exec]; split <;> simp [setGuard]
  case recover => left; simp only [exec]; split <;> rfl
  case alertSet V ol => left; simp only [exec]; split <;> rfl
  all_goals left; simp [exec, setGuard]

lemma exec_echoS_mono (a : Act P Val) (k : Fin 3) (W : ℕ) (h : s.echoS k W = true) :
    (exec prm p a s).1.echoS k W = true := by
  cases a <;> simp [exec, setGuard, setVtp]
  all_goals first
    | exact h
    | (rw [sendEcho_echoS]; exact Or.inl h)
    | (split <;> simp [h])

lemma exec_decided (a : Act P Val) :
    (exec prm p a s).1.decided = s.decided ∨
      ∃ v, a = .decide v ∧ s.decided = none ∧ (exec prm p a s).1.decided = some (s.view, v) := by
  cases a
  case decide v =>
    rcases h : s.decided with _ | d
    · right; exact ⟨v, rfl, rfl, by simp [exec, h]⟩
    · left; simp [exec, h]
  case passive V x => left; simp only [exec]; split <;> simp [setGuard]
  case recover => left; simp only [exec]; split <;> rfl
  case alertSet V ol => left; simp only [exec]; split <;> rfl
  all_goals left; simp [exec, setGuard, setVtp]

/-- A newly set echo slot is broadcast. -/
lemma exec_echo_msg (a : Act P Val) (k : Fin 3) (W : ℕ) {x : GV Val} (h0 : s.echo k W = none)
    (h : (exec prm p a s).1.echo k W = some x) : .echo k W x ∈ (exec prm p a s).2 := by
  cases a <;> simp [exec, setGuard, setVtp] at h ⊢
  all_goals first
    | simp_all
    | (split at h <;> simp_all)
    | (rw [sendEcho_echo] at h; split_ifs at h with h1
       · obtain ⟨rfl, rfl, h2⟩ := h1; cases h; simp [sendEcho, h2]
       · simp_all)

/-- Every broadcast message is reflected in the new state. -/
lemma mem_exec_refl (a : Act P Val) {m : Msg Val} (hm : m ∈ (exec prm p a s).2) :
    Refl (exec prm p a s).1 m := by
  cases a
  case vote1 w => simp [exec] at hm; subst hm; simp [Refl, exec]
  case lock v => simp [exec] at hm; subst hm; simp [Refl, exec]
  case timeout2 => simp [exec] at hm; subst hm; simp [Refl, exec]
  case recover =>
    simp only [exec] at hm ⊢; split at hm <;> simp at hm; subst hm; simp [Refl]
  case echoLock V q x =>
    simp only [exec] at hm ⊢
    rcases mem_sendEcho _ _ _ _ hm with ⟨rfl, h⟩ | ⟨rfl, y, hy⟩
    · simp [Refl, sendEcho_echo, h]
    · exact Or.inr ⟨rfl, by rw [sendEcho_echoS]; exact Or.inr ⟨rfl, rfl, y, hy⟩⟩
  case echoGuard V G =>
    simp only [exec] at hm ⊢
    rcases mem_sendEcho _ _ _ _ hm with ⟨rfl, h⟩ | ⟨rfl, y, hy⟩
    · simp [Refl, sendEcho_echo, h]
    · exact Or.inr ⟨rfl, by rw [sendEcho_echoS]; exact Or.inr ⟨rfl, rfl, y, hy⟩⟩
  case echoDiv V =>
    simp only [exec] at hm ⊢
    rcases mem_sendEcho _ _ _ _ hm with ⟨rfl, h⟩ | ⟨rfl, y, hy⟩
    · simp [Refl, sendEcho_echo, h]
    · exact Or.inr ⟨rfl, by rw [sendEcho_echoS]; exact Or.inr ⟨rfl, rfl, y, hy⟩⟩
  case echo2 V x =>
    simp only [exec] at hm ⊢
    rcases mem_sendEcho _ _ _ _ hm with ⟨rfl, h⟩ | ⟨rfl, y, hy⟩
    · simp [Refl, sendEcho_echo, h]
    · exact Or.inr ⟨rfl, by rw [sendEcho_echoS]; exact Or.inr ⟨rfl, rfl, y, hy⟩⟩
  case echo3 V x =>
    simp only [exec] at hm ⊢
    rcases mem_sendEcho _ _ _ _ hm with ⟨rfl, h⟩ | ⟨rfl, y, hy⟩
    · simp [Refl, sendEcho_echo, h]
    · exact Or.inr ⟨rfl, by rw [sendEcho_echoS]; exact Or.inr ⟨rfl, rfl, y, hy⟩⟩
  case enter3 V x =>
    simp only [exec] at hm ⊢
    rcases mem_enterV _ _ _ _ hm with ⟨W, rfl, -, -, h⟩ | ⟨w, rfl⟩
    · exact h
    · trivial
  case enter3L V x =>
    simp only [exec] at hm ⊢
    rcases mem_enterV _ _ _ _ hm with ⟨W, rfl, -, -, h⟩ | ⟨w, rfl⟩
    · exact h
    · trivial
  case enterPrep V w x =>
    simp only [exec] at hm ⊢
    rcases mem_enterV _ _ _ _ hm with ⟨W, rfl, -, -, h⟩ | ⟨w, rfl⟩
    · exact h
    · trivial
  case passive V x =>
    simp only [exec] at hm ⊢
    split at hm
    · rename_i hlt; simp only [hlt, ↓reduceIte]
      obtain ⟨W, rfl, -, -, h⟩ := mem_passiveV _ _ hm
      exact h
    · rename_i hlt; simp only [hlt, ↓reduceIte]
      obtain ⟨rfl, h⟩ := mem_ensureVC _ _ _ hm
      exact ensureVC_vote2_self _ _ _ h
  case alertSet V ol => simp only [exec] at hm; split at hm <;> simp at hm
  all_goals simp [exec] at hm

/-- Reflected messages stay reflected. -/
lemma refl_exec (a : Act P Val) (hen : En prm p a s) {m : Msg Val} (hm : Refl s m) :
    Refl (exec prm p a s).1 m := by
  cases m with
  | prepare => trivial
  | vote1 W v =>
    simp only [Refl] at hm ⊢
    rcases exec_vote1 prm p s a W with h | ⟨w, rfl, rfl, h⟩
    · rw [h, hm]
    · simp_all [En]
  | vote2 W l g =>
    simp only [Refl] at hm ⊢
    rcases exec_vote2 prm p s a hen W with h | ⟨h1, -⟩
    · rw [h, hm]
    · simp_all
  | echo k W x =>
    simp only [Refl] at hm ⊢
    rcases hm with hm | ⟨rfl, hm⟩
    · left
      rcases exec_echo prm p s a k W with h | ⟨h1, -⟩
      · rw [h, hm]
      · simp_all
    · right
      exact ⟨rfl, exec_echoS_mono prm p s a k W hm⟩

end execLemmas

end Podc.ForgetIT
