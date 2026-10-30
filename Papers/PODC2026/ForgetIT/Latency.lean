import Papers.PODC2026.ForgetIT.Refinement

/-!
# Good-case latency of Forget-IT (Theorem 1 / Theorem 3, non-robust good-case latency)

The paper's good-case family `F_gc`: the leader of the first view is correct and GST = 0. We
prove that in every such run of `forgetIT prm K` (with `n = 3f + 1`, at most `f` Byzantine
processes, any delivery times allowed by `Run.Valid f δ`, `Δ ≥ δ + 1` ticks, and `K ≥ 1` rule
passes per tick) every correct process decides the leader's proposal by time `3(δ + 1)`
(`good_case_latency`).

In CSLib's model a message produced in the step at time `τ` is sent at `τ + 1` and delivered by
`τ + 1 + δ`, where it is processed; so one message delay ("round") is `δ + 1` ticks and the
bound `3(δ + 1)` is the paper's `3δ`: prepare → vote-1 → vote-2 → decide.

The proof: up to time `3δ + 3` nothing disturbs view 1 (`LGood`, `good_run`): no timer has
expired, no correct process sends an echo message for a view `≥ 1` (so no view change or view
entry can happen), all correct `vote-1`s are for the leader's value `w`, all correct locks are on
`w`. Then the leader's `prepare` is delivered by time `δ`, all correct processes `vote-1` by time
`δ + 1`, lock by `2δ + 2` and decide by `3δ + 3` (`progress`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ForgetIT

open Finset Cslib.Byzantine.PartialSync

variable {Val : Type} [DecidableEq Val] {n : ℕ}

section basic

variable {prm : Params (Fin n)} {K : ℕ} {R : Run (Fin n) (Msg Val) Val}

lemma LExec.rcv {p : Fin n} {st st' : LS (Fin n) Val × List (Msg Val)} (h : LExec prm p st st') :
    st'.1.rcv = st.1.rcv := by
  induction h with
  | refl => rfl
  | step a _ _ ih => rw [ih, exec_rcv]

lemma LExec.msgs {p : Fin n} {st st' : LS (Fin n) Val × List (Msg Val)} (h : LExec prm p st st') :
    ∃ l, st'.2 = st.2 ++ l := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @step st _ a _ _ ih => obtain ⟨l, hl⟩ := ih; exact ⟨(exec prm p a st.1).2 ++ l, by rw [hl]; simp⟩

/-- The state after a step. -/
lemma rst_succ (τ : ℕ) (p : Fin n) :
    rst prm K R (τ + 1) p =
      { ((pass prm p)^[K] ({ rst prm K R τ p with
          rcv := (rst prm K R τ p).rcv ++ inboxList (R.inbox (forgetIT prm K) p τ) }, [])).1 with
        clk := (rst prm K R τ p).clk + 1,
        out := ((pass prm p)^[K] ({ rst prm K R τ p with
          rcv := (rst prm K R τ p).rcv ++ inboxList (R.inbox (forgetIT prm K) p τ) }, [])).2 } := by
  simp only [rst, Run.st_succ]; rfl

lemma rst_clk (τ : ℕ) (p : Fin n) : (rst prm K R τ p).clk = τ := by
  induction τ with
  | zero => simp [rst, forgetIT, initLS, initR, enterV, ensureVC]; split <;> split <;> rfl
  | succ τ ih => rw [rst_succ]; simp [ih]

lemma rst_rcv_succ (τ : ℕ) (p : Fin n) :
    (rst prm K R (τ + 1) p).rcv =
      (rst prm K R τ p).rcv ++ inboxList (R.inbox (forgetIT prm K) p τ) := by
  rw [rst_succ]; simp only
  rw [(LExec.iter (prm := prm) p K _).rcv]

lemma rst_rcv_mono {τ τ' : ℕ} (h : τ ≤ τ') (p : Fin n) {e : Fin n × Msg Val}
    (he : e ∈ (rst prm K R τ p).rcv) : e ∈ (rst prm K R τ' p).rcv := by
  induction h with
  | refl => exact he
  | step _ ih => rw [rst_rcv_succ]; exact List.mem_append_left _ ih

/-- A message of a correct process is received by the step at its delivery time. -/
lemma rst_deliver {q p : Fin n} (hq : q ∉ R.faulty) {τ : ℕ} {m : Msg Val}
    (hm : m ∈ (rst prm K R τ q).out) (hle : τ ≤ R.dl q τ p) :
    (q, m) ∈ (rst prm K R (R.dl q τ p + 1) p).rcv := by
  rw [rst_rcv_succ]
  apply List.mem_append_right
  simp only [inboxList, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  refine ⟨q, m, ?_, rfl⟩
  rw [Run.inbox_eq_flatMap]
  simp only [List.mem_flatMap, List.mem_range, Run.dlv]
  refine ⟨τ, by omega, ?_⟩
  rw [if_pos rfl, Run.out_of_correct _ _ hq]
  exact hm

end basic

section good

variable (prm : Params (Fin n)) (F : Finset (Fin n)) (w : Val)

/-- Messages correct processes may send during the good phase of view 1. -/
def GoodMsg (q : Fin n) : Msg Val → Prop
  | .prepare V x => q = prm.leader 1 ∧ V = 1 ∧ x = w
  | .vote1 V x => V = 1 ∧ x = w
  | .vote2 V l g => (V = 0 ∧ l = none) ∨ (V = 1 ∧ l = some w ∧ g = some .safe)
  | .echo _ V _ => V = 0

/-- Local state of a correct process during the good phase (at time `τ`). -/
structure LGood (τ : ℕ) (s : LS (Fin n) Val) : Prop where
  view : s.view = 1
  vc1 : s.vc 1 = false
  guard1 : s.guard 1 = some .safe
  entered : s.entered = 0
  clk : s.clk = τ
  vote1 : s.vote1 1 = none ∨ s.vote1 1 = some w
  vote2 : s.vote2 1 = none ∨ s.vote2 1 = some (some w, some .safe)
  decided : s.decided = none ∨ s.decided = some (1, w)
  rcv : ∀ q m, (q, m) ∈ s.rcv → q ∉ F → GoodMsg prm w q m

variable {prm F w}

/-- A certificate with threshold `≥ f + 1` during the good phase is for view `0`. -/
lemma good_cert (hF : F.card ≤ prm.f) {τ : ℕ} {s : LS (Fin n) Val} (hs : LGood prm F w τ s)
    {k : Fin 3} {th V : ℕ} {x : GV Val} (hth : prm.f + 1 ≤ th) (h : cert s k th V x) : V = 0 := by
  obtain ⟨r, hr, m, hm, hb⟩ := exists_correct_of_snd hF hth h
  obtain ⟨y, rfl, -⟩ := isEcho_eq hb
  exact hs.rcv r _ hm hr

lemma sendEcho_good {τ : ℕ} {s : LS (Fin n) Val} (hs : LGood prm F w τ s) {p : Fin n} {k : Fin 3}
    {x : GV Val} :
    LGood prm F w τ (sendEcho k 0 x s).1 ∧ ∀ m ∈ (sendEcho k 0 x s).2, GoodMsg prm w p m := by
  refine ⟨⟨by simp [hs.view], by simp [hs.vc1], by simp [hs.guard1], ?_, ?_, by simp [hs.vote1],
    by simp [hs.vote2], by simp [hs.decided], by simpa using hs.rcv⟩, fun m hm => ?_⟩
  · unfold sendEcho; split <;> (try split) <;> exact hs.entered
  · unfold sendEcho; split <;> (try split) <;> exact hs.clk
  · rcases mem_sendEcho _ _ _ _ hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl

/-- **One rule during the good phase.** -/
lemma good_act (hF : F.card ≤ prm.f) (hℓ : prm.leader 1 ∉ F) {τ : ℕ} (hτ : τ < 3 * prm.Δ)
    {p : Fin n} {s : LS (Fin n) Val} (hs : LGood prm F w τ s) {a : Act (Fin n) Val}
    (ha : Allowed prm p s a) :
    LGood prm F w τ (exec prm p a s).1 ∧ (∀ m ∈ (exec prm p a s).2, GoodMsg prm w p m) ∧
      ((exec prm p a s).1.vote1 1 = some w → s.vote1 1 = some w ∨ .vote1 1 w ∈ (exec prm p a s).2) ∧
      ((exec prm p a s).1.vote2 1 = some (some w, some .safe) →
        s.vote2 1 = some (some w, some .safe) ∨ .vote2 1 (some w) (some .safe) ∈ (exec prm p a s).2)
    := by
  obtain ⟨hen, htm⟩ := ha
  have hv := hs.view
  have frame : ∀ s' : LS (Fin n) Val, s'.view = s.view → s'.vc = s.vc → s'.guard = s.guard →
      s'.entered = s.entered → s'.clk = s.clk → s'.vote1 = s.vote1 → s'.vote2 = s.vote2 →
      s'.decided = s.decided → s'.rcv = s.rcv → LGood prm F w τ s' := by
    intro s' h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1 ▸ hs.view, h2 ▸ hs.vc1, h3 ▸ hs.guard1, h4 ▸ hs.entered, h5 ▸ hs.clk,
      h6 ▸ hs.vote1, h7 ▸ hs.vote2, h8 ▸ hs.decided, h9 ▸ hs.rcv⟩
  have win : ∀ V, inW s V → V = 0 ∨ V = 1 := fun V h => by simp only [inW, hv] at h; omega
  -- rules that leave the relevant fields and send nothing
  have quiet : ∀ s' : LS (Fin n) Val, (exec prm p a s) = (s', []) → s'.view = s.view →
      s'.vc = s.vc → s'.guard = s.guard → s'.entered = s.entered → s'.clk = s.clk →
      s'.vote1 = s.vote1 → s'.vote2 = s.vote2 → s'.decided = s.decided → s'.rcv = s.rcv →
      LGood prm F w τ (exec prm p a s).1 ∧ (∀ m ∈ (exec prm p a s).2, GoodMsg prm w p m) ∧
      ((exec prm p a s).1.vote1 1 = some w → s.vote1 1 = some w ∨ .vote1 1 w ∈ (exec prm p a s).2) ∧
      ((exec prm p a s).1.vote2 1 = some (some w, some .safe) →
        s.vote2 1 = some (some w, some .safe) ∨ .vote2 1 (some w) (some .safe) ∈ (exec prm p a s).2)
      := by
    intro s' he h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [he]
    exact ⟨frame s' h1 h2 h3 h4 h5 h6 h7 h8 h9, by simp, fun h => Or.inl (h6 ▸ h),
      fun h => Or.inl (h7 ▸ h)⟩
  -- echo rules for view 0
  have echo0 : ∀ k x, (exec prm p a s) = sendEcho k 0 x s →
      LGood prm F w τ (exec prm p a s).1 ∧ (∀ m ∈ (exec prm p a s).2, GoodMsg prm w p m) ∧
      ((exec prm p a s).1.vote1 1 = some w → s.vote1 1 = some w ∨ .vote1 1 w ∈ (exec prm p a s).2) ∧
      ((exec prm p a s).1.vote2 1 = some (some w, some .safe) →
        s.vote2 1 = some (some w, some .safe) ∨ .vote2 1 (some w) (some .safe) ∈ (exec prm p a s).2)
      := by
    intro k x he
    rw [he]
    obtain ⟨h1, h2⟩ := sendEcho_good (p := p) (k := k) (x := x) hs
    exact ⟨h1, h2, fun h => Or.inl (by simpa using h), fun h => Or.inl (by simpa using h)⟩
  cases a with
  | vote1 x =>
    obtain ⟨hprep, hg, h0, -⟩ := hen
    rw [hv] at hprep
    obtain ⟨-, -, rfl⟩ := hs.rcv _ _ hprep hℓ
    refine ⟨⟨by simp [exec, hv], by simp [exec, hs.vc1], by simp [exec, hs.guard1],
      by simp [exec, hs.entered], by simp [exec, hs.clk], by simp [exec, hv], by simp [exec, hs.vote2],
      by simp [exec, hs.decided], by simpa [exec] using hs.rcv⟩, ?_, ?_, ?_⟩
    · intro m hm; simp only [exec, hv, List.mem_singleton] at hm; subst hm; exact ⟨rfl, rfl⟩
    · intro _; right; simp [exec, hv]
    · intro h; left; simpa [exec] using h
  | lock v =>
    obtain ⟨hc, -, h0⟩ := hen
    obtain ⟨r, hr, m, hm, hb⟩ := exists_correct_of_snd hF (by omega) hc
    rw [isVote1_eq hb] at hm
    have hgm := hs.rcv r _ hm hr
    simp only [GoodMsg, hv] at hgm
    obtain ⟨-, rfl⟩ := hgm
    refine ⟨⟨by simp [exec, hv], by simp [exec, hs.vc1], by simp [exec, hs.guard1],
      by simp [exec, hs.entered], by simp [exec, hs.clk], by simp [exec, hs.vote1],
      by simp [exec, hv, hs.guard1], by simp [exec, hs.decided], by simpa [exec] using hs.rcv⟩,
      ?_, ?_, ?_⟩
    · intro m hm; simp only [exec, hv, List.mem_singleton, hs.guard1] at hm; subst hm
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · intro h; left; simpa [exec] using h
    · intro _; right; simp [exec, hv, hs.guard1]
  | decide v =>
    obtain ⟨r, hr, m, hm, hb⟩ := exists_correct_of_snd hF (by omega) hen
    obtain ⟨gd, rfl⟩ := isVote2L_eq hb
    have hgm := hs.rcv r _ hm hr
    simp only [GoodMsg, hv] at hgm
    rcases hgm with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by simp)
    · cases h
      refine ⟨⟨by simp [exec, hv], by simp [exec, hs.vc1], by simp [exec, hs.guard1],
        by simp [exec, hs.entered], by simp [exec, hs.clk], by simp [exec, hs.vote1],
        by simp [exec, hs.vote2], ?_, by simpa [exec] using hs.rcv⟩, by simp [exec],
        fun h => Or.inl (by simpa [exec] using h), fun h => Or.inl (by simpa [exec] using h)⟩
      rcases hs.decided with h | h <;> simp [exec, h, hv]
  | timeout2 =>
    have := htm.2; rw [hs.clk, hs.entered] at this; omega
  | clearGuard x => exact absurd hs.guard1 (by rw [← hv]; exact hen.2.1)
  | accept V q l g => exact quiet _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | alertSet V ol =>
    cases ol with
    | none => exact quiet _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    | some ℓ => exact quiet _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | alertClear1 V => exact quiet _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | alertClear2 V => exact quiet _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | vcTimer =>
    have : 4 * prm.Δ ≤ s.clk - s.entered := htm
    rw [hs.clk, hs.entered] at this; omega
  | echoLock V q x =>
    obtain ⟨hw, -, -, hvc⟩ := hen
    rcases win V hw with rfl | rfl
    · exact echo0 0 _ rfl
    · rw [hs.vc1] at hvc; exact absurd hvc (by simp)
  | echoGuard V G =>
    obtain ⟨hw, -, -, hvc⟩ := hen
    rcases win V hw with rfl | rfl
    · exact echo0 0 _ rfl
    · rw [hs.vc1] at hvc; exact absurd hvc (by simp)
  | echoDiv V =>
    obtain ⟨hw, -, -, hvc⟩ := hen
    rcases win V hw with rfl | rfl
    · exact echo0 0 _ rfl
    · rw [hs.vc1] at hvc; exact absurd hvc (by simp)
  | echo2 V x =>
    obtain rfl := good_cert hF hs (by omega) hen.2
    exact echo0 1 _ rfl
  | echo3 V x =>
    obtain rfl := good_cert hF hs (by omega) hen.2
    exact echo0 2 _ rfl
  | enter3 V x =>
    obtain rfl := good_cert hF hs (by omega) hen.1
    have := hen.2.1; omega
  | enter3L V x =>
    obtain rfl := good_cert hF hs le_rfl hen.1
    have := hen.2.1; omega
  | enterPrep V x y =>
    have h1 := good_cert hF hs le_rfl hen.2.2
    have := hen.2.1; omega
  | passive V x =>
    obtain rfl := good_cert hF hs le_rfl hen.1
    have := hen.2; omega
  | recover => exact absurd htm id

/-- A sequence of rules during the good phase. -/
lemma good_lexec (hF : F.card ≤ prm.f) (hℓ : prm.leader 1 ∉ F) {τ : ℕ} (hτ : τ < 3 * prm.Δ)
    {p : Fin n} {st st' : LS (Fin n) Val × List (Msg Val)} (h : LExec prm p st st')
    (hs : LGood prm F w τ st.1) (hm : ∀ m ∈ st.2, GoodMsg prm w p m) :
    LGood prm F w τ st'.1 ∧ (∀ m ∈ st'.2, GoodMsg prm w p m) ∧
      (st'.1.vote1 1 = some w → st.1.vote1 1 = some w ∨ .vote1 1 w ∈ st'.2) ∧
      (st'.1.vote2 1 = some (some w, some .safe) →
        st.1.vote2 1 = some (some w, some .safe) ∨ .vote2 1 (some w) (some .safe) ∈ st'.2) := by
  induction h with
  | refl => exact ⟨hs, hm, fun h => Or.inl h, fun h => Or.inl h⟩
  | @step st st' a ha _ ih =>
    obtain ⟨g1, g2, g3, g4⟩ := good_act hF hℓ hτ hs ha
    obtain ⟨h1, h2, h3, h4⟩ := ih g1 (by
      intro m hm'; simp only [List.mem_append] at hm'
      rcases hm' with h | h
      · exact hm m h
      · exact g2 m h)
    obtain ⟨l, hl⟩ := (LExec.msgs (by assumption : LExec prm p _ st'))
    refine ⟨h1, h2, fun h => ?_, fun h => ?_⟩
    · rcases h3 h with h | h
      · rcases g3 h with h' | h'
        · exact Or.inl h'
        · right; rw [hl]; simp [h']
      · exact Or.inr h
    · rcases h4 h with h | h
      · rcases g4 h with h' | h'
        · exact Or.inl h'
        · right; rw [hl]; simp [h']
      · exact Or.inr h

end good

section run

variable {prm : Params (Fin n)} {K : ℕ} {R : Run (Fin n) (Msg Val) Val}

/-- The global good-phase invariant at time `τ`. -/
def GI (prm : Params (Fin n)) (K : ℕ) (R : Run (Fin n) (Msg Val) Val) (w : Val) (τ : ℕ) : Prop :=
  ∀ p ∉ R.faulty, LGood prm R.faulty w τ (rst prm K R τ p) ∧
    (∀ τ' ≤ τ, ∀ m ∈ (rst prm K R τ' p).out, GoodMsg prm w p m) ∧
    ((rst prm K R τ p).vote1 1 = some w → ∃ τ' ≤ τ, .vote1 1 w ∈ (rst prm K R τ' p).out) ∧
    ((rst prm K R τ p).vote2 1 = some (some w, some .safe) →
      ∃ τ' ≤ τ, .vote2 1 (some w) (some .safe) ∈ (rst prm K R τ' p).out)

lemma gi_zero : GI prm K R (R.inp (prm.leader 1)) 0 := by
  intro p _
  have hv2 : ((initR prm p (R.inp p)).1).vote2 1 = none := by
    simp only [initR]
    rcases enterV_vote2 prm p 1 (startLS (R.inp p)) 1 with h | ⟨-, h, -⟩
    · rw [h]; rfl
    · omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [rst, forgetIT, initLS, initR]
  · show (enterV prm p 1 (startLS (R.inp p))).1.vc 1 = false
    rcases hb : (enterV prm p 1 (startLS (R.inp p))).1.vc 1 with _ | _
    · rfl
    · exfalso
      rcases (enterV_vc prm p 1 (startLS (R.inp p)) 1).1 hb with h | h | h <;> simp [startLS] at h
  · simp [rst, forgetIT, initLS, initR, startLS]
  · show (enterV prm p 1 (startLS (R.inp p))).1.entered = 0
    simp [enterV, startLS]
  · exact rst_clk 0 p
  · left; simp [rst, forgetIT, initLS, initR, startLS]
  · left; simpa [rst, forgetIT, initLS] using hv2
  · left; simp [rst, forgetIT, initLS, initR, startLS]
  · intro q m h; simp [rst, forgetIT, initLS, initR, startLS] at h
  · intro τ' hτ' m hm
    obtain rfl : τ' = 0 := by omega
    have hm' : m ∈ (enterV prm p 1 (startLS (R.inp p))).2 := by
      simpa [rst, forgetIT, initLS, initR] using hm
    rcases mem_enterV _ _ _ _ hm' with ⟨W, rfl, -, hW, -⟩ | ⟨x, rfl⟩
    · exact Or.inl ⟨by omega, rfl⟩
    · simp only [enterV, List.mem_append] at hm'
      rcases hm' with (h | h) | h
      · exact absurd (mem_ensureVC _ _ _ h).1 (by simp)
      · exact absurd (mem_ensureVC _ _ _ h).1 (by simp)
      · split_ifs at h with hp
        · subst hp
          simp only [ensureVC_vtp] at h
          split at h <;> simp_all [startLS, GoodMsg]
        · simp at h
  · intro h; simp [rst, forgetIT, initLS, initR, startLS] at h
  · intro h; simp [rst, forgetIT, initLS] at h; rw [hv2] at h; simp at h

/-- The good-phase invariant propagates while no timer can expire. -/
lemma gi_succ (hF : R.faulty.card ≤ prm.f) (hℓ : prm.leader 1 ∉ R.faulty) {τ : ℕ}
    (hτ : τ < 3 * prm.Δ) (h : GI prm K R (R.inp (prm.leader 1)) τ) :
    GI prm K R (R.inp (prm.leader 1)) (τ + 1) := by
  intro p hp
  obtain ⟨hl, ho, h1, h2⟩ := h p hp
  set w := R.inp (prm.leader 1)
  set s := rst prm K R τ p
  set s1 : LS (Fin n) Val := { s with rcv := s.rcv ++ inboxList (R.inbox (forgetIT prm K) p τ) }
  have hs1 : LGood prm R.faulty w τ s1 := by
    refine ⟨hl.view, hl.vc1, hl.guard1, hl.entered, hl.clk, hl.vote1, hl.vote2, hl.decided, ?_⟩
    intro q m hm hq
    simp only [s1, List.mem_append] at hm
    rcases hm with hm | hm
    · exact hl.rcv q m hm hq
    · simp only [inboxList, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hm
      obtain ⟨q', m', hm', he⟩ := hm
      cases he
      rw [Run.inbox_eq_flatMap] at hm'
      simp only [List.mem_flatMap, List.mem_range, Run.dlv] at hm'
      obtain ⟨τ', hτ', hm'⟩ := hm'
      split_ifs at hm' with hdl
      · rw [Run.out_of_correct _ _ hq] at hm'
        exact ((h q hq).2.1 τ' (by omega) m hm')
      · simp at hm'
  obtain ⟨g1, g2, g3, g4⟩ :=
    good_lexec (prm := prm) hF hℓ hτ (LExec.iter p K (s1, [])) hs1 (by simp)
  have hst := rst_succ (prm := prm) (K := K) (R := R) τ p
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact ⟨g1.view, g1.vc1, g1.guard1, g1.entered, by simp [rst_clk], g1.vote1, g1.vote2, g1.decided,
      g1.rcv⟩
  · intro τ' hτ' m hm
    rcases Nat.lt_or_ge τ' (τ + 1) with h' | h'
    · exact ho τ' (by omega) m hm
    · obtain rfl : τ' = τ + 1 := by omega
      rw [hst] at hm; exact g2 m hm
  · intro hv
    rw [hst] at hv
    rcases g3 hv with h' | h'
    · obtain ⟨τ', hτ', hm⟩ := h1 h'; exact ⟨τ', by omega, hm⟩
    · exact ⟨τ + 1, le_rfl, by rw [hst]; exact h'⟩
  · intro hv
    rw [hst] at hv
    rcases g4 hv with h' | h'
    · obtain ⟨τ', hτ', hm⟩ := h2 h'; exact ⟨τ', by omega, hm⟩
    · exact ⟨τ + 1, le_rfl, by rw [hst]; exact h'⟩

lemma gi_le (hF : R.faulty.card ≤ prm.f) (hℓ : prm.leader 1 ∉ R.faulty) {τ : ℕ}
    (hτ : τ ≤ 3 * prm.Δ) : GI prm K R (R.inp (prm.leader 1)) τ := by
  induction τ with
  | zero => exact gi_zero
  | succ τ ih => exact gi_succ hF hℓ (by omega) (ih (by omega))

lemma foldl_pres {σ α : Type} (f : σ → α → σ) (I : σ → Prop) (hI : ∀ x b, I x → I (f x b))
    (cs : List α) : ∀ x, I x → I (cs.foldl f x) := by
  induction cs with
  | nil => exact fun x h => h
  | cons b cs ih => exact fun x h => ih _ (hI x b h)

-- CSLib candidate (generic `List.foldl` invariant/progress lemma)
lemma foldl_progress {σ α : Type} (f : σ → α → σ) (I Q : σ → Prop) (a : α)
    (hI : ∀ x b, I x → I (f x b)) (hQ : ∀ x b, I x → Q x → Q (f x b))
    (hA : ∀ x, I x → Q (f x a)) (cs : List α) (ha : a ∈ cs) :
    ∀ x, I x → Q (cs.foldl f x) := by
  induction cs with
  | nil => simp at ha
  | cons b cs ih =>
    intro x hx
    rcases List.mem_cons.1 ha with rfl | ha
    · exact foldl_pres f (fun y => I y ∧ Q y) (fun y c h => ⟨hI y c h.1, hQ y c h.1 h.2⟩) cs _
        ⟨hI x _ hx, hA x hx⟩ |>.2
    · exact ih ha _ (hI x b hx)

/-- **Progress within one step.** If, in the step at time `τ` of the good phase, rule `a` is a
candidate of the first pass, and every allowed rule preserves `Q` while `a` establishes `Q` (or is
allowed when `Q` fails), then `Q` holds after the step. -/
lemma step_progress (hF : R.faulty.card ≤ prm.f) (hℓ : prm.leader 1 ∉ R.faulty) {τ : ℕ}
    (hτ : τ < 3 * prm.Δ) (hK : 1 ≤ K) (hgi : GI prm K R (R.inp (prm.leader 1)) τ) {p : Fin n}
    (hp : p ∉ R.faulty) {a : Act (Fin n) Val} {Q : LS (Fin n) Val → Prop}
    (hmem : a ∈ cands prm { rst prm K R τ p with
      rcv := (rst prm K R τ p).rcv ++ inboxList (R.inbox (forgetIT prm K) p τ) })
    (hQ : ∀ s b, LGood prm R.faulty (R.inp (prm.leader 1)) τ s → Allowed prm p s b → Q s →
      Q (exec prm p b s).1)
    (hA : ∀ s, LGood prm R.faulty (R.inp (prm.leader 1)) τ s →
      s.rcv = (rst prm K R (τ + 1) p).rcv → ¬ Q s → Allowed prm p s a)
    (hQa : ∀ s, LGood prm R.faulty (R.inp (prm.leader 1)) τ s → Allowed prm p s a →
      Q (exec prm p a s).1)
    (hQco : ∀ s (c : ℕ) o, Q s → Q { s with clk := c, out := o }) :
    Q (rst prm K R (τ + 1) p) := by
  set w := R.inp (prm.leader 1)
  set s1 : LS (Fin n) Val := { rst prm K R τ p with
      rcv := (rst prm K R τ p).rcv ++ inboxList (R.inbox (forgetIT prm K) p τ) }
  have hr1 : s1.rcv = (rst prm K R (τ + 1) p).rcv := (rst_rcv_succ τ p).symm
  have hs1 : LGood prm R.faulty w τ s1 := by
    obtain ⟨hl, -⟩ := hgi p hp
    refine ⟨hl.view, hl.vc1, hl.guard1, hl.entered, hl.clk, hl.vote1, hl.vote2, hl.decided, ?_⟩
    have := (gi_succ (K := K) hF hℓ hτ hgi p hp).1.rcv
    rwa [← hr1] at this
  let I : LS (Fin n) Val × List (Msg Val) → Prop := fun st =>
    LGood prm R.faulty w τ st.1 ∧ st.1.rcv = s1.rcv
  have hI : ∀ st b, I st → I (tryAct prm p st b) := by
    intro st b ⟨h1, h2⟩
    unfold tryAct; split
    · exact ⟨(good_act hF hℓ hτ h1 (by assumption)).1, by rw [exec_rcv, h2]⟩
    · exact ⟨h1, h2⟩
  have hQ' : ∀ st b, I st → Q st.1 → Q (tryAct prm p st b).1 := by
    intro st b ⟨h1, _⟩ hq
    unfold tryAct; split
    · exact hQ _ _ h1 (by assumption) hq
    · exact hq
  have hA' : ∀ st, I st → Q (tryAct prm p st a).1 := by
    intro st ⟨h1, h2⟩
    unfold tryAct; split
    · exact hQa _ h1 (by assumption)
    · rename_i hna
      by_contra hq
      exact hna (hA _ h1 (by rw [h2, hr1]) hq)
  have hpass : ∀ st, I st → I (pass prm p st) := fun st h => foldl_pres _ I hI _ st h
  have hpassQ : ∀ st, I st → Q st.1 → Q (pass prm p st).1 := fun st h hq =>
    (foldl_pres _ (fun y => I y ∧ Q y.1) (fun y c h => ⟨hI y c h.1, hQ' y c h.1 h.2⟩) _ st
      ⟨h, hq⟩).2
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have h1 : I (pass prm p (s1, [])) ∧ Q (pass prm p (s1, [])).1 :=
    ⟨hpass _ ⟨hs1, rfl⟩, foldl_progress _ I (fun y => Q y.1) a hI hQ' hA' _ hmem _ ⟨hs1, rfl⟩⟩
  have h2 : ∀ k st, I st → Q st.1 → Q ((pass prm p)^[k] st).1 := by
    intro k
    induction k with
    | zero => exact fun st _ hq => hq
    | succ k ih =>
      intro st hi hq
      rw [Function.iterate_succ_apply]
      exact ih _ (hpass st hi) (hpassQ st hi hq)
  rw [rst_succ]
  apply hQco
  rw [Function.iterate_succ_apply]
  exact h2 K' _ h1.1 h1.2

lemma mem_cands_vote1 {prm : Params (Fin n)} {s : LS (Fin n) Val} {x : Val}
    (h : (prm.leader s.view, .prepare s.view x) ∈ s.rcv) : .vote1 x ∈ cands prm s := by
  have hx : x ∈ prepVals s s.view (prm.leader s.view) := by
    simp only [prepVals, List.mem_filterMap]; exact ⟨_, h, by simp⟩
  unfold cands
  iterate 8 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨x, hx, rfl⟩

lemma mem_cands_lock {prm : Params (Fin n)} {s : LS (Fin n) Val} {x : Val} {q : Fin n}
    (h : (q, .vote1 s.view x) ∈ s.rcv) : .lock x ∈ cands prm s := by
  have hx : x ∈ vote1Vals s s.view := by
    simp only [vote1Vals, List.mem_dedup, List.mem_filterMap]; exact ⟨_, h, by simp⟩
  unfold cands
  iterate 7 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨x, hx, rfl⟩

lemma mem_cands_decide {prm : Params (Fin n)} {s : LS (Fin n) Val} {x : Val} {q : Fin n}
    {g : Option (GV Val)} (h : (q, .vote2 s.view (some x) g) ∈ s.rcv) :
    .decide x ∈ cands prm s := by
  have hx : x ∈ vote2Locks s s.view := by
    simp only [vote2Locks, List.mem_dedup, List.mem_filterMap]; exact ⟨_, h, by simp⟩
  unfold cands
  iterate 9 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨x, hx, rfl⟩

-- CSLib candidate (quorum of all correct senders, `Quorum.lean`)
/-- If every correct process has a matching message in `rcv`, the senders form a quorum. -/
lemma quorum_of_all {F : Finset (Fin n)} {f : ℕ} (hn : n = 3 * f + 1) (hF : F.card ≤ f)
    {rcv : List (Fin n × Msg Val)} {b : Msg Val → Bool}
    (h : ∀ r ∉ F, ∃ m, (r, m) ∈ rcv ∧ b m = true) : 2 * f + 1 ≤ (snd rcv b).card := by
  have hsub : Finset.univ \ F ⊆ snd rcv b := by
    intro r hr
    obtain ⟨m, hm, hb⟩ := h r (Finset.mem_sdiff.1 hr).2
    simp only [snd, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(r, m), hm, rfl, hb⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- The leader of view 1 broadcasts its proposal at time 0. -/
lemma init_prepare {prm : Params (Fin n)} {K : ℕ} {R : Run (Fin n) (Msg Val) Val} :
    .prepare 1 (R.inp (prm.leader 1)) ∈ (rst prm K R 0 (prm.leader 1)).out := by
  show _ ∈ (enterV prm (prm.leader 1) 1 (startLS (R.inp (prm.leader 1)))).2
  simp [enterV, startLS]

end run

/-- **Good-case latency** (Theorem 1 and Theorem 3 of the paper, good-case latency `3δ`): in
every run with GST = 0 whose first leader is correct, every correct process decides the first
leader's proposal by time `3(δ + 1)`, i.e. within three message delays (one message delay is
`δ + 1` ticks in this model). Assumptions: `n = 3f + 1`, at most `f` Byzantine processes, the
time unit `Δ ≥ δ + 1` (one message delay), at least one rule pass per tick. -/
theorem good_case_latency {prm : Params (Fin n)} (hn : n = 3 * prm.f + 1) {K : ℕ} (hK : 1 ≤ K)
    {R : Run (Fin n) (Msg Val) Val} {δ : ℕ} (hR : R.Valid prm.f δ) (hgst : R.gst = 0)
    (hℓ : prm.leader 1 ∉ R.faulty) (hΔ : δ + 1 ≤ prm.Δ) {p : Fin n} (hp : p ∉ R.faulty) :
    (R.st (forgetIT prm K) (3 * (δ + 1)) p).decided = some (1, R.inp (prm.leader 1)) := by
  set w := R.inp (prm.leader 1)
  set ℓ := prm.leader 1
  have hF := hR.card_faulty
  have gi : ∀ τ ≤ 3 * prm.Δ, GI prm K R w τ := fun τ hτ => gi_le hF hℓ hτ
  have hdl : ∀ q τ r, q ∉ R.faulty → r ∉ R.faulty → τ ≤ R.dl q τ r ∧ R.dl q τ r ≤ τ + δ :=
    fun q τ r hq hr => ⟨hR.dl_ge q τ r hq hr, by
      have := hR.dl_le q τ r hq hr; rw [hgst, Nat.max_zero] at this; exact this⟩
  -- vote-1
  have hA : ∀ q ∉ R.faulty, ∃ τq ≤ δ + 1, .vote1 1 w ∈ (rst prm K R τq q).out := by
    intro q hq
    set τ1 := R.dl ℓ 0 q
    have h1 := hdl ℓ 0 q hℓ hq
    have hrcv := rst_deliver (prm := prm) (K := K) hℓ init_prepare h1.1
    have hgi := gi τ1 (by omega)
    have hv : (rst prm K R (τ1 + 1) q).vote1 1 = some w := by
      refine step_progress (Q := fun s => s.vote1 1 = some w) (a := .vote1 w) hF hℓ (by omega) hK
        hgi hq ?_ ?_ ?_ ?_ ?_
      · apply mem_cands_vote1
        have hview := (hgi q hq).1.view
        simp only [hview]
        rw [rst_rcv_succ] at hrcv; exact hrcv
      · intro s b _ hb hq'
        exact refl_exec prm q s b hb.1 (m := .vote1 1 w) hq'
      · intro s hs hr hq'
        have h0 : s.vote1 1 = none := by rcases hs.vote1 with h | h; exact h; exact absurd h hq'
        refine ⟨⟨?_, ?_, ?_, ?_⟩, trivial⟩
        · rw [hs.view, hr]; exact hrcv
        · rw [hs.view, hs.guard1]; simp
        · rw [hs.view, h0]
        · rw [hs.view, hs.vc1]
      · intro s hs _; simp [exec, hs.view]
      · intro s c o h; exact h
    obtain ⟨τ', hτ', hm⟩ := (gi (τ1 + 1) (by omega) q hq).2.2.1 hv
    exact ⟨τ', by omega, hm⟩
  -- lock
  have hB : ∀ q ∉ R.faulty, ∃ τq ≤ 2 * δ + 2,
      .vote2 1 (some w) (some .safe) ∈ (rst prm K R τq q).out := by
    intro q hq
    have hgi := gi (2 * δ + 1) (by omega)
    have hall : ∀ r ∉ R.faulty, ∃ m, (r, m) ∈ (rst prm K R (2 * δ + 2) q).rcv ∧
        isVote1 1 w m = true := by
      intro r hr
      obtain ⟨τr, hτr, hm⟩ := hA r hr
      have h1 := hdl r τr q hr hq
      exact ⟨_, rst_rcv_mono (by omega) q (rst_deliver hr hm h1.1), by simp [isVote1]⟩
    have hcard := quorum_of_all hn hF hall
    have hv : (rst prm K R (2 * δ + 2) q).vote2 1 = some (some w, some .safe) := by
      refine step_progress (Q := fun s => s.vote2 1 = some (some w, some .safe)) (a := .lock w)
        hF hℓ (by omega) hK hgi hq ?_ ?_ ?_ ?_ ?_
      · obtain ⟨r, hr⟩ : ∃ r, r ∉ R.faulty := by
          by_contra h; push Not at h
          have : Finset.univ ⊆ R.faulty := fun r _ => h r
          have := Finset.card_le_card this
          rw [Finset.card_univ, Fintype.card_fin] at this; omega
        obtain ⟨m, hm, hb⟩ := hall r hr
        rw [isVote1_eq hb] at hm
        apply mem_cands_lock (q := r)
        have hview := (hgi q hq).1.view
        simp only [hview]
        rw [rst_rcv_succ] at hm; exact hm
      · intro s b _ hb hq'
        exact refl_exec prm q s b hb.1 (m := .vote2 1 (some w) (some .safe)) hq'
      · intro s hs hr hq'
        have h0 : s.vote2 1 = none := by rcases hs.vote2 with h | h; exact h; exact absurd h hq'
        refine ⟨⟨?_, ?_, ?_⟩, trivial⟩
        · rw [hs.view, hr]; exact hcard
        · rw [hs.view, hs.vc1]
        · rw [hs.view, h0]
      · intro s hs _; simp [exec, hs.view, hs.guard1]
      · intro s c o h; exact h
    obtain ⟨τ', hτ', hm⟩ := (gi (2 * δ + 2) (by omega) q hq).2.2.2 hv
    exact ⟨τ', by omega, hm⟩
  -- decide
  have hgi := gi (3 * δ + 2) (by omega)
  have hall : ∀ r ∉ R.faulty, ∃ m, (r, m) ∈ (rst prm K R (3 * δ + 3) p).rcv ∧
      isVote2L 1 w m = true := by
    intro r hr
    obtain ⟨τr, hτr, hm⟩ := hB r hr
    have h1 := hdl r τr p hr hp
    exact ⟨_, rst_rcv_mono (by omega) p (rst_deliver hr hm h1.1), by simp [isVote2L]⟩
  have hcard := quorum_of_all hn hF hall
  have hd : (rst prm K R (3 * δ + 3) p).decided ≠ none := by
    refine step_progress (Q := fun s => s.decided ≠ none) (a := .decide w)
      hF hℓ (by omega) hK hgi hp ?_ ?_ ?_ ?_ ?_
    · obtain ⟨m, hm, hb⟩ := hall p hp
      obtain ⟨gd, rfl⟩ := isVote2L_eq hb
      apply mem_cands_decide (q := p) (g := gd)
      have hview := (hgi p hp).1.view
      simp only [hview]
      rw [rst_rcv_succ] at hm; exact hm
    · intro s b _ _ hq'
      rcases exec_decided prm p s b with h | ⟨v, -, h0, -⟩
      · rw [h]; exact hq'
      · exact absurd h0 hq'
    · intro s hs hr _
      refine ⟨?_, trivial⟩
      show 2 * prm.f + 1 ≤ (snd s.rcv (isVote2L s.view w)).card
      rw [hs.view, hr]; exact hcard
    · intro s _ _; simp only [exec]; cases s.decided <;> simp
    · intro s c o h; exact h
  have hl := (gi (3 * δ + 3) (by omega) p hp).1
  rcases hl.decided with h | h
  · exact absurd h hd
  · show (rst prm K R (3 * (δ + 1)) p).decided = _
    rw [show 3 * (δ + 1) = 3 * δ + 3 by ring]; exact h

end Podc.ForgetIT

namespace Podc.ForgetIT

open Cslib.Byzantine.PartialSync

variable {Val : Type} [DecidableEq Val] {n : ℕ}

/-- Good-case latency in terms of the algorithm's decision map. -/
theorem good_case_decides {prm : Params (Fin n)} (hn : n = 3 * prm.f + 1) {K : ℕ} (hK : 1 ≤ K)
    {R : Run (Fin n) (Msg Val) Val} {δ : ℕ} (hR : R.Valid prm.f δ) (hgst : R.gst = 0)
    (hℓ : prm.leader 1 ∉ R.faulty) (hΔ : δ + 1 ≤ prm.Δ) {p : Fin n} (hp : p ∉ R.faulty) :
    (forgetIT prm K).decide p (R.st (forgetIT prm K) (3 * (δ + 1)) p) =
      some (R.inp (prm.leader 1)) := by
  show Option.map Prod.snd (R.st (forgetIT prm K) (3 * (δ + 1)) p).decided = _
  rw [good_case_latency hn hK hR hgst hℓ hΔ hp]; rfl

/-- **Non-triviality** (Section 3): if all processes are correct, all propose `v` and GST = 0,
then no process decides a value different from `v` (here: `δ + 1 ≤ Δ`, the paper's `δ ≤ Δ`). -/
theorem non_triviality {prm : Params (Fin n)} (hn : n = 3 * prm.f + 1) {K : ℕ} (hK : 1 ≤ K)
    {R : Run (Fin n) (Msg Val) Val} {δ : ℕ} (hR : R.Valid prm.f δ) (hgst : R.gst = 0)
    (hall : R.faulty = ∅) {v : Val} (hinp : ∀ q, R.inp q = v) (hΔ : δ + 1 ≤ prm.Δ) {p : Fin n}
    {τ : ℕ} {v' : Val} (hd : (forgetIT prm K).decide p (R.st (forgetIT prm K) τ p) = some v') :
    v' = v := by
  have hℓ : prm.leader 1 ∉ R.faulty := by simp [hall]
  have hp : p ∉ R.faulty := by simp [hall]
  have h := good_case_decides hn hK hR hgst hℓ hΔ hp
  rw [hinp] at h
  exact run_agreement hn K R hR.card_faulty hp hp hd h

end Podc.ForgetIT
