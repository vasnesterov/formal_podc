import Papers.PODC2025.TwoStepConsensusLB.Fig1Protocol

/-!
# The object version of Fig. 1 is not wait-free

A consensus *object* must be wait-free: every correct process that invokes `propose(v)` eventually
returns (decides) as long as at most `f` processes crash. We show that the object version of Fig. 1
(red lines included) violates this whenever `n − f − e ≥ 2` (e.g. `n = 7`, `f = 3`, `e = 2`, which
satisfies the paper's bound `n ≥ max(2e + f − 1, 2f + 1)` with equality), **independently of the
leader election and of timing**.

Scenario (`stuck_config`): process `p` invokes `propose(v)` and broadcasts `Propose(v)`; only `r`
accepts it (`val_r = v`, `proposer_r = p`); then `p` crashes. Some process starts a ballot `b₀ ≥ 1`
and all processes other than `p` join it (`bal ≥ 1`), so no one accepts `p`'s `Propose` any more.

Claim (`stuck_forever`): from this configuration, in **every** execution in which `p` takes no
step and no process other than `r` invokes `propose` — `r` may invoke `propose(w)` at any time,
every process may start any number of its own ballots and every message may be delivered — no
process ever decides. Indeed `r`'s invocation comes after its vote (`val_r ≠ ⊥`), so line 2 does
nothing and `initial_val_r` stays `⊥`; every `1B` quorum `Q` (of processes `≠ p`) reports a single
vote (`r`'s), `b_max = 0` and no decision, so lines 33 and 35 (which need `n − f − e ≥ 2` votes)
fail, and line 37 fails since every leader has `initial_val = ⊥`: no `2A` is ever sent, and the fast
path is closed (all ballots are `≥ 1`, and `p` is crashed). Hence `r`, a correct process that
invoked `propose`, never returns although only one process crashed.

This scenario is about Fig. 1 as published (`cfg.fallbackVal = false`): with the fixed lines 37–38
(`fallbackVal = true`) `r` itself could start a ballot and propose its own `val`. The second
scenario below (leader election of §C.1) works for both variants.

The restricted relation `QStep` over-approximates the steps of such executions (it does not impose
fairness, but every fair continuation is among its executions), so the result covers all of them.
-/

namespace TwoStepConsensus.Fig1

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- Steps of executions in which `p` has crashed (takes no steps) and only `r` may invoke
`propose`. Any process may start ballots. -/
def QStep (cfg : Config P V) (p r : P) (s s' : State P V) : Prop :=
  ∃ x k, x ≠ p ∧ (k = .invoke → x = r) ∧ Step cfg x k s s'

/-- The invariant of the stuck executions (without the ballot condition). -/
structure Quiet (p r : P) (s : State P V) : Prop where
  decided : ∀ q, q ≠ p → (s.loc q).decided = none
  initVal : ∀ q, q ≠ p → (s.loc q).initVal = none
  vbal : ∀ q, q ≠ p → (s.loc q).vbal = 0
  val : ∀ q, q ≠ p → q ≠ r → (s.loc q).val = none
  val_r : (s.loc r).val ≠ none
  no2A : ∀ b w, .twoA b w ∉ s.msgs
  noDecide : ∀ x b w, .decide x b w ∉ s.msgs
  twoB : ∀ q z b w, .twoB q z b w ∈ s.msgs → z = p
  oneB : ∀ y c d, .oneB y c d ∈ s.msgs → d.decided = none ∧ d.vbal = 0 ∧ (d.val = none ∨ y = r)

/-- The full invariant: additionally every process other than `p` is in a slow ballot. -/
def Stuck (p r : P) (s : State P V) : Prop :=
  Quiet p r s ∧ ∀ q, q ≠ p → 0 < (s.loc q).bal

omit [DecidableEq P] in
/-- Lines 26–38 select nothing on a `Quiet` quorum when `n − f − e ≥ 2` and the leader has
`initial_val = ⊥`. -/
theorem no_select {cfg : Config P V} {r : P} {Q : Finset P} {rep : P → Snap P V} {w : V}
    (hgap : 2 ≤ Fintype.card P - cfg.f - cfg.e)
    (hQ : ∀ q ∈ Q, (rep q).decided = none ∧ (rep q).vbal = 0 ∧ ((rep q).val = none ∨ q = r))
    (h : Select cfg Q rep none w) : False := by
  have hS : ∀ S : Finset P, VotersIn Q rep w S → S.card ≤ 1 := by
    rintro S ⟨hSQ, hS⟩
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    have h1 := (hQ a (hSQ ha)).2.2
    have h2 := (hQ b (hSQ hb)).2.2
    rw [(hS a ha).2] at h1
    rw [(hS b hb).2] at h2
    simp only [reduceCtorEq, false_or] at h1 h2
    rw [h1, h2]
  cases h with
  | l30 hq hd => rw [(hQ _ hq).1] at hd; cases hd
  | l32 _ hq _ hpos _ => rw [(hQ _ hq).2.1] at hpos; exact lt_irrefl 0 hpos
  | l34 _ _ h33 =>
    obtain ⟨S, hS', hc⟩ := h33
    have := hS S hS'
    omega
  | l36 _ _ _ h35 _ =>
    obtain ⟨S, hS', hc⟩ := h35
    have := hS S hS'
    omega
  | l38 _ _ _ _ hi => cases hi

set_option linter.unusedSimpArgs false in
theorem quiet_step {cfg : Config P V} (hfb : cfg.fallbackVal = false) {p r : P}
    (hgap : 2 ≤ Fintype.card P - cfg.f - cfg.e)
    {s s' : State P V} (hQ : Quiet p r s) (hbal : ∀ q, q ≠ p → 0 < (s.loc q).bal)
    (h : QStep cfg p r s s') : Quiet p r s' := by
  obtain ⟨x, k, hxp, hinv, h⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hQ
  cases h
  case send2A Q rep _ _ _ hQ hsel =>
    exfalso
    simp only [leaderIv, hfb, Bool.false_eq_true, ↓reduceIte, h2 x hxp] at hsel
    exact no_select hgap (fun q hq => h9 _ _ _ (hQ q hq)) hsel
  case fastDecide P' hne _ hP' _ _ =>
    exfalso
    obtain ⟨q, hq⟩ := hne
    exact hxp (h8 _ _ _ _ (hP' q hq))
  case slowDecide P' hne _ hP' _ =>
    exfalso
    obtain ⟨q, hq⟩ := hne
    exact hxp (h8 _ _ _ _ (hP' q hq))
  case recvPropose =>
    exfalso
    have := hbal x hxp
    omega
  all_goals constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs,
    Loc.snap] at *
  all_goals grind

theorem Step.bal_le {cfg : Config P V} {s s' : State P V} {x : P} {k : Kind}
    (h : Step cfg x k s s') (q : P) : (s.loc q).bal ≤ (s'.loc q).bal := by
  cases h <;> simp only [State.set_loc, State.send_loc] <;> (try split_ifs) <;> simp_all; omega

theorem stuck_step {cfg : Config P V} (hfb : cfg.fallbackVal = false) {p r : P}
    (hgap : 2 ≤ Fintype.card P - cfg.f - cfg.e)
    {s s' : State P V} (hS : Stuck p r s) (h : QStep cfg p r s s') : Stuck p r s' := by
  refine ⟨quiet_step hfb hgap hS.1 hS.2 h, fun q hq => ?_⟩
  obtain ⟨x, k, -, -, h⟩ := h
  exact lt_of_lt_of_le (hS.2 q hq) (h.bal_le q)

/-- **Wait-freedom fails for the object version** of the paper (`fallbackVal = false`,
`n − f − e ≥ 2`): no process ever decides in any execution from a `Stuck` configuration in which `p`
is crashed and only `r` invokes `propose`. -/
theorem stuck_forever {cfg : Config P V} (hfb : cfg.fallbackVal = false) {p r : P}
    (hgap : 2 ≤ Fintype.card P - cfg.f - cfg.e)
    {s₀ s : State P V} (h₀ : Stuck p r s₀) (h : Relation.ReflTransGen (QStep cfg p r) s₀ s)
    {q : P} (hq : q ≠ p) : (s.loc q).decided = none := by
  have : Stuck p r s := by
    induction h with
    | refl => exact h₀
    | tail _ hst ih => exact stuck_step hfb hgap ih hst
  exact this.1.decided q hq

set_option linter.unusedSimpArgs false in
omit [Fintype P] [LinearOrder V] in
theorem quiet_recv1A {p r x : P} {b : ℕ} {s : State P V} (hQ : Quiet p r s)
    (hxp : x ≠ p) :
    Quiet p r ((s.set x { s.loc x with bal := b }).send (.oneB x b (s.loc x).snap)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hQ
  constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs,
    Loc.snap] at *
  all_goals grind

set_option linter.unusedSimpArgs false in
/-- The stuck configuration is reachable from the initial state (object version): `p` invokes
`propose(v)` and broadcasts it, `r` accepts it, the owner of a ballot `b₀ ≥ 1` starts it, and
every process other than `p` joins `b₀`. `r` has not invoked `propose` yet. -/
theorem stuck_reachable {cfg : Config P V} (hver : cfg.ver = .object) {p r : P} (hpr : p ≠ r)
    {b₀ : ℕ} (hb₀ : 0 < b₀) (v : V) :
    ∃ s₀, Reachable cfg s₀ ∧ Stuck p r s₀ ∧ (s₀.loc p).inv = some v ∧ (s₀.loc r).inv = none := by
  -- the first four steps
  have hinit : ∀ q, (init cfg).loc q = ⟨0, 0, none, none, none, none, none⟩ := by
    intro q; simp [init, hver]
  have st1 := Step.invoke (cfg := cfg) (s := init cfg) (p := p) v hver (by simp [hinit])
  set s1 := (init cfg).set p _ with hs1
  have st2 := Step.sendPropose (cfg := cfg) (s := s1) (p := p) (v := v) (by simp [hs1, hinit])
  set s2 := s1.send (.propose p v) with hs2
  have st3 := Step.recvPropose (cfg := cfg) (s := s2) (p := r) (q := p) (v := v)
    (by simp [hs2]) hpr (by simp [hs2, hs1, hinit, hpr.symm])
    (by simp [hs2, hs1, hinit, hpr.symm])
    (by simp [hs2, hs1, hinit, hpr.symm, Accepts])
  set s3 := (s2.set r _).send (.twoB r p 0 v) with hs3
  have st4 := Step.start1A (cfg := cfg) (s := s3) (p := cfg.owner b₀) (b := b₀) rfl
    (by simp only [hs3, hs2, hs1, State.set_loc, State.send_loc]; split_ifs <;> simp [hinit, hb₀])
  set s4 := s3.send (.oneA b₀) with hs4
  have hr4 : Reachable cfg s4 :=
    .tail (.tail (.tail (.tail .refl ⟨_, _, st1⟩) ⟨_, _, st2⟩) ⟨_, _, st3⟩) ⟨_, _, st4⟩
  have hq4 : Quiet p r s4 := by
    constructor
    all_goals intros
    all_goals simp only [hs4, hs3, hs2, hs1, State.set_loc, State.set_msgs, State.send_loc,
      State.mem_send_msgs, Loc.snap, hinit] at *
    all_goals grind [init]
  -- every process other than `p` joins ballot `b₀`
  have key : ∀ T : Finset P, p ∉ T → ∃ s, Reachable cfg s ∧ Quiet p r s ∧ .oneA b₀ ∈ s.msgs ∧
      (s.loc p).inv = some v ∧ (s.loc r).inv = none ∧
      ∀ q, q ≠ p → (q ∈ T → 0 < (s.loc q).bal) ∧ (q ∉ T → (s.loc q).bal = 0) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨s4, hr4, hq4, by simp [hs4], ?_, ?_, fun q hq => ⟨by simp, ?_⟩⟩
      all_goals simp only [hs4, hs3, hs2, hs1, State.set_loc, State.send_loc]
      all_goals split_ifs <;> simp [hinit] at * <;> grind
    | insert a T ha ih =>
      intro hp
      have hap : a ≠ p := fun h => hp (h ▸ Finset.mem_insert_self a T)
      obtain ⟨s, hr, hq, h1A, hip, hir, hbal⟩ := ih (fun h => hp (Finset.mem_insert_of_mem h))
      have st := Step.recv1A (cfg := cfg) (s := s) (p := a) (b := b₀) h1A
        (by rw [(hbal a hap).2 ha]; exact hb₀)
      refine ⟨_, hr.tail ⟨_, _, st⟩, quiet_recv1A hq hap, Or.inr h1A, ?_, ?_, fun q hqp => ?_⟩
      · simp only [State.send_loc, State.set_loc]; split_ifs <;> simp_all
      · simp only [State.send_loc, State.set_loc]; split_ifs <;> simp_all
      · simp only [State.send_loc, State.set_loc, Finset.mem_insert]
        by_cases hqa : q = a
        · subst hqa; simp [hb₀]
        · simp only [hqa, ↓reduceIte, false_or]
          exact hbal q hqp
  obtain ⟨s, hr, hq, -, hip, hir, hbal⟩ := key (Finset.univ.erase p) (Finset.notMem_erase p _)
  exact ⟨s, hr, ⟨hq, fun q hqp => (hbal q hqp).1 (Finset.mem_erase.2 ⟨hqp, Finset.mem_univ _⟩)⟩,
    hip, hir⟩

/-- **The object version of Fig. 1 (as in the paper, `fallbackVal = false`) is not wait-free**
(whenever `n − f − e ≥ 2`, e.g. `n = 7`, `f = 3`, `e = 2`). There is a reachable configuration `s₀`
in which `p` has invoked `propose(v)`
and `r` has not invoked `propose` yet such that, if `p` crashes (one crash, `≤ f`) and no process
other than `r` invokes `propose`, then no process other than `p` ever decides: in particular `r`
never returns from its `propose` invocation, whatever the leader election, the timing and the
message deliveries. -/
theorem object_not_wait_free {cfg : Config P V} (hver : cfg.ver = .object)
    (hfb : cfg.fallbackVal = false)
    (hgap : 2 ≤ Fintype.card P - cfg.f - cfg.e) {p r : P} (hpr : p ≠ r) {b₀ : ℕ} (hb₀ : 0 < b₀)
    (v : V) :
    ∃ s₀, Reachable cfg s₀ ∧ (s₀.loc p).inv = some v ∧ (s₀.loc r).inv = none ∧
      ∀ s, Relation.ReflTransGen (QStep cfg p r) s₀ s → ∀ q, q ≠ p → (s.loc q).decided = none := by
  obtain ⟨s₀, hr, hS, hip, hir⟩ := stuck_reachable hver hpr hb₀ v
  exact ⟨s₀, hr, hip, hir, fun s hs q hq => stuck_forever hfb hgap hS hs hq⟩

/-- In the stuck executions `r` can indeed invoke `propose(w)` (the invocation is enabled). -/
theorem stuck_invoke_enabled {cfg : Config P V} (hver : cfg.ver = .object) {p r : P}
    {s : State P V} (hpr : p ≠ r) (hir : (s.loc r).inv = none) (w : V) :
    ∃ s', QStep cfg p r s s' ∧ (s'.loc r).inv = some w :=
  ⟨_, ⟨r, .invoke, hpr.symm, fun _ => rfl, Step.invoke w hver hir⟩, by simp⟩

/-- A concrete instance meeting the paper's bound for consensus objects with equality:
`n = 7 = max(2e + f − 1, 2f + 1)` for `f = 3`, `e = 2`, so `n − f − e = 2`. -/
example : 2 ≤ Fintype.card (Fin 7) - 3 - 2 ∧ 2 * 3 + 1 ≤ Fintype.card (Fin 7) ∧
    2 * 2 + 3 - 1 ≤ Fintype.card (Fin 7) := by decide

/-! ## Second scenario: no crash, leader election as in §C.1 (any `n`, `f`, `e`)

With the leader election of §C.1 (only the process `l` output by `Ω` starts ballots), a correct
process `r ≠ l` that invokes `propose` only after all processes moved to a slow ballot never
returns, if no other process invokes `propose`: its `Propose` is ignored (`bal ≠ 0`), `1B` messages
do not carry `initial_val`, so `l` computes `val = ⊥` at lines 26–38 (no decision, `b_max = 0`, no
votes, `initial_val_l = ⊥`) and never sends `2A`. No process crashes; `Ω` may output `l` forever.
This works for all parameters with `f < n` and `n − f − e ≥ 1` (in particular for all parameters
allowed by Theorem 2), and **also for the fixed lines 37–38** (`fallbackVal = true`): nobody has
voted, so the leader's own `val` is `⊥` as well. -/

/-- Steps of executions in which only `r` invokes `propose` and only `l` starts ballots. -/
def OStep (cfg : Config P V) (l r : P) (s s' : State P V) : Prop :=
  ∃ x k, (k = .invoke → x = r) ∧ (k = .start1A → x = l) ∧ Step cfg x k s s'

/-- Invariant of these executions (without the ballot condition): no vote, no decision. -/
structure Idle (cfg : Config P V) (l r : P) (s : State P V) : Prop where
  decided : ∀ q, (s.loc q).decided = none
  vbal : ∀ q, (s.loc q).vbal = 0
  val : ∀ q, (s.loc q).val = none
  initVal : ∀ q, q ≠ r → (s.loc q).initVal = none
  no2A : ∀ b w, .twoA b w ∉ s.msgs
  noDecide : ∀ x b w, .decide x b w ∉ s.msgs
  no2B : ∀ q z b w, .twoB q z b w ∉ s.msgs
  oneA : ∀ b, .oneA b ∈ s.msgs → cfg.owner b = l
  oneB : ∀ y c d, .oneB y c d ∈ s.msgs →
    .oneA c ∈ s.msgs ∧ d.decided = none ∧ d.vbal = 0 ∧ d.val = none

set_option linter.unusedSimpArgs false in
theorem idle_step {cfg : Config P V} {l r : P} (hlr : l ≠ r) (hf : cfg.f < Fintype.card P)
    (hgap : 1 ≤ Fintype.card P - cfg.f - cfg.e) {s s' : State P V} (hI : Idle cfg l r s)
    (hbal : ∀ q, 0 < (s.loc q).bal) (h : OStep cfg l r s s') : Idle cfg l r s' := by
  obtain ⟨x, k, hinv, hst, h⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hI
  cases h
  case send2A Q rep hQc how _ hQ hsel =>
    exfalso
    obtain ⟨q, hq⟩ : Q.Nonempty := by
      rw [← Finset.card_pos]
      omega
    have hxl : x = l := how.symm.trans (h8 _ (h9 _ _ _ (hQ q hq)).1)
    subst hxl
    have hiv : leaderIv cfg (s.loc x) = none := by
      unfold leaderIv
      split_ifs <;> simp [h4 _ hlr, h3]
    rw [hiv] at hsel
    have hv : ∀ q ∈ Q, (rep q).val = none := fun q hq => (h9 _ _ _ (hQ q hq)).2.2.2
    cases hsel with
    | l30 hq hd => rw [(h9 _ _ _ (hQ _ hq)).2.1] at hd; cases hd
    | l32 _ hq _ hpos _ => rw [(h9 _ _ _ (hQ _ hq)).2.2.1] at hpos; exact lt_irrefl 0 hpos
    | l34 _ _ h33 =>
      obtain ⟨S, ⟨hSQ, hS⟩, hc⟩ := h33
      obtain ⟨q, hq⟩ : S.Nonempty := by
        rw [← Finset.card_pos]
        omega
      have := (hS q hq).2
      rw [hv q (hSQ hq)] at this
      cases this
    | l36 _ _ _ h35 _ =>
      obtain ⟨S, ⟨hSQ, hS⟩, hc⟩ := h35
      obtain ⟨q, hq⟩ : S.Nonempty := by
        rw [← Finset.card_pos]
        omega
      have := (hS q hq).2
      rw [hv q (hSQ hq)] at this
      cases this
    | l38 _ _ _ _ hi => cases hi
  case fastDecide P' hne _ hP' _ _ =>
    exfalso
    obtain ⟨q, hq⟩ := hne
    exact h7 _ _ _ _ (hP' q hq)
  case slowDecide P' hne _ hP' _ =>
    exfalso
    obtain ⟨q, hq⟩ := hne
    exact h7 _ _ _ _ (hP' q hq)
  case recvPropose =>
    exfalso
    have := hbal x
    omega
  all_goals constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs,
    Loc.snap] at *
  all_goals grind

/-- **The object version of Fig. 1 is not wait-free under the leader election of §C.1**, with or
without the fallback fix of lines 37–38, for all parameters with `f < n` and `n − f − e ≥ 1`. Let `l
≠ r` and let `b₀ ≥ 1` be a ballot of `l`. There
is a reachable configuration (`l` started `b₀`, all processes joined it, nobody invoked `propose`)
from which, in every execution where only `r` invokes `propose` and only `l` starts ballots (`Ω`
outputs `l`), no process ever decides; `r` can invoke `propose` there, and never returns. -/
theorem object_not_wait_free_omega {cfg : Config P V} (hver : cfg.ver = .object)
    (hf : cfg.f < Fintype.card P) (hgap : 1 ≤ Fintype.card P - cfg.f - cfg.e) {l r : P}
    (hlr : l ≠ r) {b₀ : ℕ} (hb₀ : 0 < b₀) (hown : cfg.owner b₀ = l) :
    ∃ s₀, Reachable cfg s₀ ∧ (s₀.loc r).inv = none ∧
      ∀ s, Relation.ReflTransGen (OStep cfg l r) s₀ s → ∀ q, (s.loc q).decided = none := by
  have hinit : ∀ q, (init cfg).loc q = ⟨0, 0, none, none, none, none, none⟩ := by
    intro q; simp [init, hver]
  have st1 := Step.start1A (cfg := cfg) (s := init cfg) (p := l) (b := b₀) hown
    (by simp [hinit, hb₀])
  set s1 := (init cfg).send (.oneA b₀) with hs1
  have hr1 : Reachable cfg s1 := .tail .refl ⟨_, _, st1⟩
  have hq1 : Idle cfg l r s1 := by
    constructor
    all_goals intros
    all_goals simp only [hs1, State.send_loc, State.mem_send_msgs, hinit] at *
    all_goals grind [init]
  have key : ∀ T : Finset P, ∃ s, Reachable cfg s ∧ Idle cfg l r s ∧ .oneA b₀ ∈ s.msgs ∧
      (s.loc r).inv = none ∧ ∀ q, (q ∈ T → 0 < (s.loc q).bal) ∧ (q ∉ T → (s.loc q).bal = 0) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨s1, hr1, hq1, by simp [hs1], by simp [hs1, hinit], fun q => ⟨by simp, ?_⟩⟩
      simp [hs1, hinit]
    | insert a T ha ih =>
      obtain ⟨s, hr, hq, h1A, hir, hbal⟩ := ih
      have st := Step.recv1A (cfg := cfg) (s := s) (p := a) (b := b₀) h1A
        (by rw [(hbal a).2 ha]; exact hb₀)
      refine ⟨_, hr.tail ⟨_, _, st⟩, ?_, Or.inr h1A, ?_, fun q => ?_⟩
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hq
        constructor
        all_goals intros
        all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs,
          Loc.snap] at *
        all_goals grind
      · simp only [State.send_loc, State.set_loc]; split_ifs <;> simp_all
      · simp only [State.send_loc, State.set_loc, Finset.mem_insert]
        by_cases hqa : q = a
        · subst hqa; simp [hb₀]
        · simp only [hqa, ↓reduceIte, false_or]
          exact hbal q
  obtain ⟨s₀, hr, hq, -, hir, hbal⟩ := key Finset.univ
  refine ⟨s₀, hr, hir, fun s hs q => ?_⟩
  have : Idle cfg l r s ∧ ∀ q, 0 < (s.loc q).bal := by
    induction hs with
    | refl => exact ⟨hq, fun q => (hbal q).1 (Finset.mem_univ _)⟩
    | tail _ hst ih =>
      refine ⟨idle_step hlr hf hgap ih.1 ih.2 hst, fun q => ?_⟩
      obtain ⟨x, k, -, -, hst⟩ := hst
      exact lt_of_lt_of_le (ih.2 q) (hst.bal_le q)
  exact this.1.decided q

end TwoStepConsensus.Fig1
