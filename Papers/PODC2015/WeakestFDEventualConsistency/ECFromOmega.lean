import Papers.PODC2015.WeakestFDEventualConsistency.Specs

/-!
# Lemma 2: eventual consensus from `Ω` in every environment (Algorithm 4)

Algorithm 4 of [DGKPS15]: on invocation of `proposeEC_ℓ(v)` a process broadcasts `promote(v, ℓ)`;
it stores every received promotion in `received[q][ℓ]`; on a local time-out, if
`received[Ω][count] ≠ ⊥` it returns that value to the current instance `count`.

The application is folded into the algorithm: `inp p j` is the value `p` proposes to instance
`j`; `p` invokes instance `0` at its first step and instance `j + 1` in the very step in which it
returns its response to `j` (the paper's usage assumption). The application could choose its
proposals adaptively; since the algorithm is deterministic, every run with an adaptive application
is a run for the function of the proposals it actually made, so fixing `inp` loses nothing.
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

namespace Alg4

variable {P V : Type*} [DecidableEq P]

/-- Outputs: invocations and responses of EC. -/
inductive Out (V : Type*) where
  /-- `proposeEC_j(v)` is invoked. -/
  | inv (j : ℕ) (v : V)
  /-- `v` is returned to `proposeEC_j`. -/
  | resp (j : ℕ) (v : V)

/-- Local state. -/
structure State (P V : Type*) where
  /-- Instance `0` has been invoked. -/
  started : Bool
  /-- The current instance. -/
  count : ℕ
  /-- `received q j`: the value promoted by `q` for instance `j`. -/
  received : P → ℕ → Option V

/-- Record a promotion `(v, j)` received from `q`. -/
def record (s : State P V) : Event P (V × ℕ) Empty → State P V
  | .recv q (v, j) =>
    { s with received := Function.update s.received q (Function.update (s.received q) j (some v)) }
  | _ => s

/-- **Algorithm 4** of [DGKPS15] (the failure-detector value `d` is the output of `Ω`). Messages
`(v, j)` stand for `promote(v, j)`. -/
def alg (inp : P → ℕ → V) : Algorithm P P (V × ℕ) Empty (Out V) (State P V) where
  init _ := ⟨false, 0, fun _ _ => none⟩
  step p d s e :=
    let s₁ := record s e
    if s₁.started = false then
      (⟨true, 0, s₁.received⟩, some (inp p 0, 0), [.inv 0 (inp p 0)])
    else
      match e with
      | .tick =>
        match s₁.received d s₁.count with
        | some v => (⟨true, s₁.count + 1, s₁.received⟩, some (inp p (s₁.count + 1), s₁.count + 1),
            [.resp s₁.count v, .inv (s₁.count + 1) (inp p (s₁.count + 1))])
        | none => (s₁, none, [])
      | _ => (s₁, none, [])

/-- The EC history of a run of Algorithm 4. -/
def hist (inp : P → ℕ → V) (r : Run P P Empty) : ECHist P V where
  inv p j v t := (alg inp).Out r p (.inv j v) t
  resp p j v t := (alg inp).Out r p (.resp j v) t

variable (inp : P → ℕ → V)

/-! ### Facts about one step -/

lemma record_started (s : State P V) (e) : (record s e).started = s.started := by
  unfold record; split <;> rfl

lemma record_count (s : State P V) (e) : (record s e).count = s.count := by
  unfold record; split <;> rfl

lemma step_started (p d s e) : ((alg inp).step p d s e).1.started = true := by
  simp only [alg]
  split_ifs with h
  · rfl
  · rw [Bool.not_eq_false] at h
    split
    · split
      · rfl
      · rw [record_started] at h ⊢; exact h
    · rw [record_started] at h ⊢; exact h

/-- Shape of a step: either the start step, or a decision step, or a silent step. -/
lemma step_cases (p : P) (d : P) (s : State P V) (e) :
    (s.started = false ∧ ((alg inp).step p d s e) =
        (⟨true, 0, (record s e).received⟩, some (inp p 0, 0), [.inv 0 (inp p 0)])) ∨
    (s.started = true ∧ e = .tick ∧ ∃ v, s.received d s.count = some v ∧
      ((alg inp).step p d s e) = (⟨true, s.count + 1, s.received⟩,
        some (inp p (s.count + 1), s.count + 1),
        [.resp s.count v, .inv (s.count + 1) (inp p (s.count + 1))])) ∨
    (s.started = true ∧ ((alg inp).step p d s e) = (record s e, none, [])) := by
  by_cases hs : s.started = false
  · left
    refine ⟨hs, ?_⟩
    simp [alg, record_started, hs]
  · have hs' : s.started = true := by simpa using hs
    right
    cases e with
    | tick =>
      rcases hv : s.received d s.count with _ | v
      · right; refine ⟨hs', ?_⟩; simp [alg, record, hs', hv]
      · left; exact ⟨hs', rfl, v, rfl, by simp only [alg, record, hs', hv]; rfl⟩
    | recv q m => right; exact ⟨hs', by simp [alg, record_started, hs']⟩
    | input i => exact i.elim

/-- Broadcast messages are promotions of the sender's own proposal, together with the
corresponding invocation output. -/
lemma step_bcast {p d s e} {v : V} {j : ℕ} (h : ((alg inp).step p d s e).2.1 = some (v, j)) :
    v = inp p j ∧ Out.inv j v ∈ ((alg inp).step p d s e).2.2 := by
  rcases step_cases inp p d s e with ⟨-, hst⟩ | ⟨-, -, w, -, hst⟩ | ⟨-, hst⟩ <;> rw [hst] at h ⊢
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  · simp at h

lemma step_out_inv {p d s e} {v : V} {j : ℕ} (h : Out.inv j v ∈ ((alg inp).step p d s e).2.2) :
    v = inp p j := by
  rcases step_cases inp p d s e with ⟨-, hst⟩ | ⟨-, -, w, -, hst⟩ | ⟨-, hst⟩ <;> rw [hst] at h <;>
    simp at h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · obtain ⟨rfl, rfl⟩ := h; rfl

lemma step_out_resp {p d s e} {v : V} {j : ℕ} (h : Out.resp j v ∈ ((alg inp).step p d s e).2.2) :
    s.started = true ∧ e = .tick ∧ s.count = j ∧ s.received d j = some v ∧
      ((alg inp).step p d s e).1.count = j + 1 := by
  rcases step_cases inp p d s e with ⟨-, hst⟩ | ⟨h1, h2, w, hw, hst⟩ | ⟨-, hst⟩ <;> rw [hst] at h <;>
    simp at h
  obtain ⟨rfl, rfl⟩ := h
  rw [hst]; exact ⟨h1, h2, rfl, hw, rfl⟩

lemma step_count (p d s e) (hs : s.started = false → s.count = 0) :
    ((alg inp).step p d s e).1.count = s.count ∨
      (((alg inp).step p d s e).1.count = s.count + 1 ∧ s.started = true ∧ e = .tick ∧
        ∃ v, s.received d s.count = some v ∧
          Out.resp s.count v ∈ ((alg inp).step p d s e).2.2) := by
  rcases step_cases inp p d s e with ⟨h1, hst⟩ | ⟨h1, h2, w, hw, hst⟩ | ⟨-, hst⟩ <;> rw [hst]
  · left; exact (hs h1).symm
  · right; exact ⟨rfl, h1, h2, w, hw, by simp⟩
  · left; exact record_count s e

lemma step_received (p d s e) :
    ((alg inp).step p d s e).1.received = (record s e).received := by
  rcases step_cases inp p d s e with ⟨-, hst⟩ | ⟨-, rfl, w, -, hst⟩ | ⟨-, hst⟩ <;> rw [hst]
  rfl

lemma record_received {s : State P V} {e} {q : P} {j : ℕ} {v : V}
    (h : (record s e).received q j = some v) :
    s.received q j = some v ∨ e = .recv q (v, j) := by
  unfold record at h
  split at h
  · rename_i q' v' j'
    by_cases h1 : q = q'
    · subst h1
      by_cases h2 : j = j'
      · subst h2; simp at h; subst h; right; rfl
      · left; simpa [Function.update_of_ne h2] using h
    · left; simpa [Function.update_of_ne h1] using h
  · left; exact h

lemma record_received_keep {s : State P V} {e} {q : P} {j : ℕ} {v : V}
    (h : s.received q j = some v) (he : ∀ v', e = .recv q (v', j) → v' = v) :
    (record s e).received q j = some v := by
  unfold record
  split
  · rename_i q' v' j'
    by_cases h1 : q = q'
    · subst h1
      by_cases h2 : j = j'
      · subst h2; simp [he v' rfl]
      · simpa [Function.update_of_ne h2] using h
    · simpa [Function.update_of_ne h1] using h
  · exact h

lemma step_tick_decide (p d : P) {s : State P V} {w : V} (hs : s.started = true)
    (hw : s.received d s.count = some w) :
    ((alg inp).step p d s .tick).1.count = s.count + 1 := by
  simp [alg, record, hs, hw]

/-! ### Invariants of runs -/

variable {inp} {r : Run P P Empty}

@[simp] lemma st_zero (p : P) : (alg inp).st r p 0 = ⟨false, 0, fun _ _ => none⟩ := rfl

/-- Messages are promotions of the sender's proposal, sent with the invocation. -/
lemma msg_inv {t s : ℕ} {q : P} {v : V} {j : ℕ}
    (h : ((alg inp).cfg r t).msg s = some (q, (v, j))) :
    s < t ∧ v = inp q j ∧ (alg inp).Out r q (.inv j v) s := by
  obtain ⟨c, e, hσ, he, hb⟩ := Algorithm.msg_spec r h
  obtain ⟨h1, h2⟩ := step_bcast inp hb
  refine ⟨?_, h1, (Algorithm.out_iff r).2 ⟨c, e, hσ, he, h2⟩⟩
  by_contra hc
  rw [Algorithm.msg_eq_none_of_le r t s (by omega)] at h
  simp at h

/-- The state invariant. -/
def Inv (inp : P → ℕ → V) (r : Run P P Empty) (t : ℕ) (s : State P V) : Prop :=
  (s.started = false → s.count = 0) ∧
    ∀ q j v, s.received q j = some v → v = inp q j ∧ ∃ s' < t, (alg inp).Out r q (.inv j v) s'

lemma inv_all : ∀ t p, Inv inp r t ((alg inp).st r p t) := by
  refine Algorithm.st_induction_time r _ ?_ ?_ ?_
  · intro p; exact ⟨fun _ => rfl, fun q j v h => by simp [alg] at h⟩
  · rintro t p s ⟨h1, h2⟩
    exact ⟨h1, fun q j v h => by
      obtain ⟨h3, s', hs', h4⟩ := h2 q j v h; exact ⟨h3, s', by omega, h4⟩⟩
  · rintro t p c e hσ he ⟨-, h2⟩
    refine ⟨fun h => by rw [step_started] at h; simp at h, fun q j v h => ?_⟩
    rw [step_received] at h
    rcases record_received h with h | rfl
    · obtain ⟨h3, s', hs', h4⟩ := h2 q j v h; exact ⟨h3, s', by omega, h4⟩
    · obtain ⟨s₀, rfl, hm⟩ := Algorithm.event_eq_recv he
      obtain ⟨hs, h3, h4⟩ := msg_inv hm
      exact ⟨h3, s₀, by omega, h4⟩

lemma received_eq {t : ℕ} {p q : P} {j : ℕ} {v : V}
    (h : ((alg inp).st r p t).received q j = some v) : v = inp q j :=
  ((inv_all t p).2 q j v h).1

lemma count_le_step (t : ℕ) (p : P) (c) (e) (_ : r.σ t = some (p, c))
    (_ : ((alg inp).cfg r t).event c = some e) :
    ((alg inp).st r p t).count ≤ ((alg inp).step p (r.H p t) ((alg inp).st r p t) e).1.count := by
  rcases step_count inp p (r.H p t) _ e (inv_all (inp := inp) (r := r) t p).1 with h | ⟨h, -⟩ <;> omega

lemma count_mono {p : P} {t t' : ℕ} (h : t ≤ t') :
    ((alg inp).st r p t).count ≤ ((alg inp).st r p t').count :=
  Algorithm.st_rel_of_step r (fun _ (a b : State P V) => a.count ≤ b.count) (fun _ _ => le_rfl)
    (fun _ _ _ _ h1 h2 => h1.trans h2) (fun t p c e hσ he => count_le_step t p c e hσ he) p t t' h

lemma started_mono {p : P} {t t' : ℕ} (h : t ≤ t') (hs : ((alg inp).st r p t).started = true) :
    ((alg inp).st r p t').started = true :=
  Algorithm.st_rel_of_step r (fun _ (a b : State P V) => a.started = true → b.started = true) (fun _ _ h => h)
    (fun _ _ _ _ h1 h2 h => h2 (h1 h)) (fun _ _ _ _ _ _ _ => step_started inp _ _ _ _) p t t' h hs

lemma received_mono {p q : P} {j : ℕ} {v : V} {t t' : ℕ} (h : t ≤ t')
    (hv : ((alg inp).st r p t).received q j = some v) :
    ((alg inp).st r p t').received q j = some v := by
  induction t', h using Nat.le_induction with
  | base => exact hv
  | succ t' ht ih =>
    rcases hσ : r.σ t' with _ | ⟨p', c⟩
    · rw [Algorithm.loc_succ_of_ne r t' p (by simp [hσ])]; exact ih
    · by_cases hp : p = p'
      · subst hp
        rcases he : ((alg inp).cfg r t').event c with _ | e
        · rw [Algorithm.st, (Algorithm.cfg_succ_of_event_none r t' p c hσ he).1]; exact ih
        · rw [(Algorithm.cfg_succ_of_event r t' p c e hσ he).1, step_received]
          refine record_received_keep ih ?_
          intro v' hv'; subst hv'
          obtain ⟨s₀, -, hm⟩ := Algorithm.event_eq_recv he
          rw [(msg_inv hm).2.1, ← received_eq ih]
      · rw [Algorithm.loc_succ_of_ne r t' p (by
          intro c' h; rw [hσ] at h; simp at h; exact hp h.1.symm)]
        exact ih

/-- A response of `p` to `j` at time `t`: what the step looks like. -/
lemma resp_spec {p : P} {j : ℕ} {v : V} {t : ℕ} (h : (alg inp).Out r p (.resp j v) t) :
    r.σ t = some (p, .tick) ∧ ((alg inp).st r p t).started = true ∧
      ((alg inp).st r p t).count = j ∧ ((alg inp).st r p t).received (r.H p t) j = some v ∧
      ((alg inp).st r p (t + 1)).count = j + 1 := by
  obtain ⟨c, e, hσ, he, ho⟩ := (Algorithm.out_iff r).1 h
  obtain ⟨h1, rfl, h2, h3, h4⟩ := step_out_resp inp ho
  have hc := Algorithm.event_eq_tick he
  subst hc
  exact ⟨hσ, h1, h2, h3, by rw [(Algorithm.cfg_succ_of_event r t p _ _ hσ he).1, h4]⟩

/-- Count changes only through responses. -/
lemma count_succ_cases (p : P) (t : ℕ) :
    ((alg inp).st r p (t + 1)).count = ((alg inp).st r p t).count ∨
      (((alg inp).st r p (t + 1)).count = ((alg inp).st r p t).count + 1 ∧
        ∃ v, (alg inp).Out r p (.resp ((alg inp).st r p t).count v) t) := by
  rcases hσ : r.σ t with _ | ⟨p', c⟩
  · left; rw [Algorithm.loc_succ_of_ne r t p (by simp [hσ])]
  · by_cases hp : p = p'
    · subst hp
      rcases he : ((alg inp).cfg r t).event c with _ | e
      · left; rw [Algorithm.st, (Algorithm.cfg_succ_of_event_none r t p c hσ he).1]
      · rw [(Algorithm.cfg_succ_of_event r t p c e hσ he).1]
        rcases step_count inp p (r.H p t) _ e (inv_all (inp := inp) (r := r) t p).1 with h | ⟨h, -, -, v, -, ho⟩
        · left; exact h
        · right; exact ⟨h, v, (Algorithm.out_iff r).2 ⟨c, e, hσ, he, ho⟩⟩
    · left; rw [Algorithm.loc_succ_of_ne r t p (by
        intro c' h; rw [hσ] at h; simp at h; exact hp h.1.symm)]

lemma exists_resp_of_count {p : P} {j t : ℕ} (h : j < ((alg inp).st r p t).count) :
    ∃ v t', t' < t ∧ (alg inp).Out r p (.resp j v) t' := by
  induction t with
  | zero => simp at h
  | succ t ih =>
    by_cases h' : j < ((alg inp).st r p t).count
    · obtain ⟨v, t', ht', ho⟩ := ih h'; exact ⟨v, t', by omega, ho⟩
    · rcases count_succ_cases (inp := inp) (r := r) p t with h1 | ⟨h1, v, ho⟩
      · omega
      · have : ((alg inp).st r p t).count = j := by omega
        rw [this] at ho; exact ⟨v, t, by omega, ho⟩

/-- Every invoked instance has been promoted by the invoker. -/
lemma exists_bcast {p : P} {j t : ℕ} (hs : ((alg inp).st r p t).started = true)
    (hj : j ≤ ((alg inp).st r p t).count) :
    ∃ s < t, ((alg inp).cfg r (s + 1)).msg s = some (p, (inp p j, j)) := by
  induction t with
  | zero => simp at hs
  | succ t ih =>
    by_cases h' : ((alg inp).st r p t).started = true ∧ j ≤ ((alg inp).st r p t).count
    · obtain ⟨s, hs', hm⟩ := ih h'.1 h'.2; exact ⟨s, by omega, hm⟩
    · rcases hσ : r.σ t with _ | ⟨p', c⟩
      · rw [Algorithm.loc_succ_of_ne r t p (by simp [hσ])] at hs hj; exact absurd ⟨hs, hj⟩ h'
      · by_cases hp : p = p'
        · subst hp
          rcases he : ((alg inp).cfg r t).event c with _ | e
          · rw [Algorithm.st, (Algorithm.cfg_succ_of_event_none r t p c hσ he).1] at hs hj
            exact absurd ⟨hs, hj⟩ h'
          · obtain ⟨hst, hmsg, -⟩ := Algorithm.cfg_succ_of_event r t p c e hσ he
            rw [hst] at hs hj
            refine ⟨t, by omega, ?_⟩
            rw [hmsg]
            rcases step_cases inp p (r.H p t) ((alg inp).st r p t) e with
              ⟨h1, hstep⟩ | ⟨h1, -, w, -, hstep⟩ | ⟨h1, hstep⟩ <;> rw [hstep] at hj ⊢
            · simp only at hj
              have : j = 0 := by omega
              subst this; rfl
            · simp only at hj
              have hle := (not_and.1 h') h1
              have : j = ((alg inp).st r p t).count + 1 := by omega
              subst this; rfl
            · rw [record_count] at hj; exact absurd ⟨h1, hj⟩ h'
        · rw [Algorithm.loc_succ_of_ne r t p (by
            intro c' h; rw [hσ] at h; simp at h; exact hp h.1.symm)] at hs hj
          exact absurd ⟨hs, hj⟩ h'

/-- Receiving a promotion records it. -/
lemma received_of_recv {t s : ℕ} {p q : P} {v : V} {j : ℕ}
    (hσ : r.σ t = some (p, .recv q s)) (hm : ((alg inp).cfg r t).msg s = some (q, (v, j))) :
    ((alg inp).st r p (t + 1)).received q j = some v := by
  have he := Algorithm.event_recv (I := Empty) hm
  rw [(Algorithm.cfg_succ_of_event r t p _ _ hσ he).1, step_received]
  simp [record]

/-! ### The EC properties -/

/-- EC-Integrity. -/
theorem integrity : ECIntegrity (hist inp r) := by
  intro p j v v' t t' h h'
  obtain ⟨-, -, hc, hv, hc1⟩ := resp_spec h
  obtain ⟨-, -, hc', hv', hc1'⟩ := resp_spec h'
  rcases lt_trichotomy t t' with hlt | rfl | hlt
  · have := count_mono (inp := inp) (r := r) (p := p) (show t + 1 ≤ t' by omega); omega
  · rw [hv] at hv'; exact ⟨rfl, Option.some.inj hv'⟩
  · have := count_mono (inp := inp) (r := r) (p := p) (show t' + 1 ≤ t by omega); omega

/-- EC-Validity (the returned value was proposed, by the trusted leader, strictly earlier). -/
theorem validity : ECValidity (hist inp r) := by
  intro p j v t h
  obtain ⟨-, -, -, hv, -⟩ := resp_spec h
  obtain ⟨-, s', hs', ho⟩ := (inv_all t p).2 _ _ _ hv
  exact ⟨_, s', hs'.le, ho⟩

/-- Every correct process invokes every instance. -/
lemma invoked (hA : (alg inp).Admissible r) (hΩ : r.H ∈ Omega P r.F) :
    ∀ j p, r.F.Correct p → ∃ t, ((alg inp).st r p t).started = true ∧
      j ≤ ((alg inp).st r p t).count := by
  intro j
  induction j with
  | zero =>
    intro p hp
    obtain ⟨t, -, hσ⟩ := hA.ticks p hp 0
    refine ⟨t + 1, ?_, Nat.zero_le _⟩
    rw [(Algorithm.cfg_succ_of_event r t p .tick .tick hσ rfl).1]
    exact step_started inp _ _ _ _
  | succ j ih =>
    intro p hp
    obtain ⟨ℓ, hℓ, T, hT⟩ := hΩ ⟨p, hp⟩
    obtain ⟨tℓ, hs, hj⟩ := ih ℓ hℓ
    obtain ⟨s, -, hm⟩ := exists_bcast hs hj
    obtain ⟨t₁, hσ₁⟩ := hA.delivery p hp (s + 1) s ℓ _ hm
    obtain ⟨hst₁, -⟩ := hA.recv_valid t₁ p ℓ s hσ₁
    have hm₁ : ((alg inp).cfg r t₁).msg s = some (ℓ, (inp ℓ j, j)) := by
      rw [Algorithm.msg_eq_succ r hst₁]; exact hm
    have hrec := received_of_recv hσ₁ hm₁
    obtain ⟨tp, hsp, hjp⟩ := ih p hp
    obtain ⟨t, ht, hσ⟩ := hA.ticks p hp (max (max T (t₁ + 1)) tp)
    have hs_t := started_mono (show tp ≤ t by omega) hsp
    have hj_t := hjp.trans (count_mono (inp := inp) (r := r) (p := p) (show tp ≤ t by omega))
    have hrec_t := received_mono (show t₁ + 1 ≤ t by omega) hrec
    by_cases hlt : j < ((alg inp).st r p t).count
    · exact ⟨t, hs_t, hlt⟩
    · have hc : ((alg inp).st r p t).count = j := by omega
      refine ⟨t + 1, ?_, ?_⟩
      · rw [(Algorithm.cfg_succ_of_event r t p .tick .tick hσ rfl).1]
        exact step_started inp _ _ _ _
      · rw [(Algorithm.cfg_succ_of_event r t p .tick .tick hσ rfl).1,
          step_tick_decide inp p (r.H p t) hs_t (w := inp ℓ j)
            (by rw [hT t (by omega) p hp, hc]; exact hrec_t)]
        omega

/-- EC-Termination. -/
theorem termination (hA : (alg inp).Admissible r) (hΩ : r.H ∈ Omega P r.F) :
    ECTermination r.F (hist inp r) := by
  intro p hp j
  obtain ⟨t, -, hj⟩ := invoked hA hΩ (j + 1) p hp
  obtain ⟨v, t', -, ho⟩ := exists_resp_of_count (show j < ((alg inp).st r p t).count by omega)
  exact ⟨v, t', ho⟩

/-- EC-Agreement holds from some instance on. The instance is chosen after the time `T` at which
`Ω` has stabilized at the correct processes **and every faulty process has crashed** (the paper
only uses the first condition, but faulty processes may trust other leaders while they are
alive, and EC-Agreement constrains all processes). -/
theorem agreement [Finite P] (hA : (alg inp).Admissible r) (hΩ : r.H ∈ Omega P r.F) :
    ∃ k, ECAgreementFrom (hist inp r) k := by
  classical
  have := Fintype.ofFinite P
  obtain ⟨T₀, hT₀⟩ := r.F.exists_crash_bound
  -- responses to late instances are given by correct processes after `T`
  have late : ∀ T, T₀ ≤ T → ∀ j, Finset.univ.sup (fun p => ((alg inp).st r p T).count) < j →
      ∀ p v t, (hist inp r).resp p j v t → T < t ∧ r.F.Correct p ∧
        ((alg inp).st r p t).received (r.H p t) j = some v := by
    intro T hT j hj p v t h
    obtain ⟨hσ, -, hcnt, hv, -⟩ := resp_spec h
    have hTt : T < t := by
      by_contra hle
      have h1 := count_mono (inp := inp) (r := r) (p := p) (show t ≤ T by omega)
      have h2 : ((alg inp).st r p T).count ≤ Finset.univ.sup
          (fun p => ((alg inp).st r p T).count) :=
        Finset.le_sup (f := fun p => ((alg inp).st r p T).count) (Finset.mem_univ p)
      omega
    refine ⟨hTt, ?_, hv⟩
    by_contra hpc
    exact hA.alive t p _ hσ (r.F.mono (show T₀ ≤ t by omega) (hT₀ p hpc))
  by_cases hc : ∃ c, r.F.Correct c
  · obtain ⟨ℓ, -, TΩ, hTΩ⟩ := hΩ hc
    refine ⟨Finset.univ.sup (fun p => ((alg inp).st r p (max T₀ TΩ)).count) + 1, ?_⟩
    intro j hj p q v v' t t' h h'
    have key : ∀ p v t, (hist inp r).resp p j v t → v = inp ℓ j := by
      intro p v t h
      obtain ⟨hTt, hpc, hv⟩ := late (max T₀ TΩ) (le_max_left _ _) j (by omega) p v t h
      rw [hTΩ t (by omega) p hpc] at hv
      exact received_eq hv
    rw [key p v t h, key q v' t' h']
  · refine ⟨Finset.univ.sup (fun p => ((alg inp).st r p T₀).count) + 1, ?_⟩
    intro j hj p q v v' t t' h h'
    exact absurd ⟨p, (late T₀ le_rfl j (by omega) p v t h).2.1⟩ hc

/-! ### The folded application uses EC properly -/

lemma inv_spec {p : P} {j : ℕ} {v : V} {t : ℕ} (h : (alg inp).Out r p (.inv j v) t) :
    v = inp p j ∧ ((alg inp).st r p (t + 1)).started = true ∧
      ((alg inp).st r p (t + 1)).count = j ∧
      (((alg inp).st r p t).started = false ∨
        (((alg inp).st r p t).started = true ∧ ((alg inp).st r p t).count + 1 = j ∧
          ∃ w, (alg inp).Out r p (.resp ((alg inp).st r p t).count w) t)) := by
  obtain ⟨c, e, hσ, he, ho⟩ := (Algorithm.out_iff r).1 h
  have hst := (Algorithm.cfg_succ_of_event r t p c e hσ he).1
  refine ⟨step_out_inv inp ho, by rw [hst]; exact step_started inp _ _ _ _, ?_⟩
  rcases step_cases inp p (r.H p t) ((alg inp).st r p t) e with
    ⟨h1, hstep⟩ | ⟨h1, -, w, -, hstep⟩ | ⟨h1, hstep⟩
  · rw [hstep] at ho; simp at ho
    rw [hst, hstep, ho.1]; exact ⟨rfl, Or.inl h1⟩
  · have ho' := ho
    rw [hstep] at ho; simp at ho
    rw [hst, hstep, ← ho.1]
    refine ⟨rfl, Or.inr ⟨h1, rfl, w, (Algorithm.out_iff r).2 ⟨c, e, hσ, he, ?_⟩⟩⟩
    rw [hstep]; simp
  · rw [hstep] at ho; simp at ho

/-- The application folded into Algorithm 4 respects the usage assumption of EC. -/
theorem properUse : (hist inp r).ProperUse where
  inv_once p j v v' t t' h h' := by
    obtain ⟨hv, hs1, hc1, -⟩ := inv_spec h
    obtain ⟨hv', hs1', hc1', hcase'⟩ := inv_spec h'
    refine ⟨?_, hv.trans hv'.symm⟩
    by_contra hne
    -- w.l.o.g. compare the two invocation times
    have key : ∀ t t', t < t' → (alg inp).Out r p (.inv j v) t → (alg inp).Out r p (.inv j v') t' →
        False := by
      intro t t' hlt h h'
      obtain ⟨-, hs1, hc1, -⟩ := inv_spec h
      obtain ⟨-, -, -, hcase'⟩ := inv_spec h'
      rcases hcase' with hs | ⟨-, hc, -⟩
      · rw [started_mono (show t + 1 ≤ t' by omega) hs1] at hs; simp at hs
      · have := count_mono (inp := inp) (r := r) (p := p) (show t + 1 ≤ t' by omega); omega
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key t t' hlt h h'
    · obtain ⟨-, -, -, hcase⟩ := inv_spec h
      rcases hcase with hs | ⟨-, hc, -⟩
      · rw [started_mono (show t' + 1 ≤ t by omega) hs1'] at hs; simp at hs
      · have := count_mono (inp := inp) (r := r) (p := p) (show t' + 1 ≤ t by omega); omega
  inv_succ p j v t h := by
    obtain ⟨-, -, -, hcase⟩ := inv_spec h
    rcases hcase with hs | ⟨-, hc, w, hw⟩
    · -- a start step invokes instance `0` only
      obtain ⟨c, e, hσ, he, ho⟩ := (Algorithm.out_iff r).1 h
      rcases step_cases inp p (r.H p t) ((alg inp).st r p t) e with
        ⟨-, hstep⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [hstep] at ho; simp at ho
      · rw [hs] at h1; simp at h1
      · rw [hs] at h1; simp at h1
    · have : ((alg inp).st r p t).count = j := by omega
      rw [this] at hw; exact ⟨w, hw⟩
  resp_inv p j v t h := by
    obtain ⟨c, e, hσ, he, ho⟩ := (Algorithm.out_iff r).1 h
    obtain ⟨-, -, hc, -, -⟩ := step_out_resp inp ho
    rcases step_cases inp p (r.H p t) ((alg inp).st r p t) e with
      ⟨-, hstep⟩ | ⟨-, -, w, -, hstep⟩ | ⟨-, hstep⟩ <;> rw [hstep] at ho <;> simp at ho
    refine ⟨inp p (j + 1), (Algorithm.out_iff r).2 ⟨c, e, hσ, he, ?_⟩⟩
    rw [hstep, hc]; simp

/-- **Lemma 2** of [DGKPS15]: in every environment (every failure pattern), Algorithm 4 implements
eventual consensus using `Ω`: every admissible run satisfies EC. (`P` finite.) -/
theorem lemma_2 [Finite P] (inp : P → ℕ → V) (r : Run P P Empty) (hΩ : r.H ∈ Omega P r.F)
    (hA : (alg inp).Admissible r) : EC r.F (hist inp r) :=
  ⟨termination hA hΩ, integrity, validity, agreement hA hΩ⟩

end Alg4

end Podc.WeakestFDEventualConsistency
