import Papers.PODC2021.GoodCaseLatencyBB.Basic

/-!
# Degenerate cases and non-vacuity: the "echo" protocol

The broadcaster `s` keeps sending its input; every other process commits the first value it
receives from `s`; `s` commits its own input at time `0`.

* `n = 2`: the echo protocol solves Byzantine reliable broadcast for every `f` (one honest
  non-broadcaster has nobody to disagree with) and commits after **one** message delay. Hence
  Theorems 4 and 8 (and Theorem 9) of the paper are false for `n = 2`; our versions assume `n ≥ 3`
  (`theorem_4_false_two`, `theorem_8_false_two`; the latter commits by time `δ ≤ 2δ − 1 ≤ Δ + δ − 1`,
  so it refutes Theorems 8 and 9 for `n = 2`).
* `n = 1`: the echo protocol solves partially synchronous BB for every `f` with good-case latency
  `0` rounds, so the literal statements of Theorems 6 and 7 (`f ≥ (n+2)/5`) fail for `n = 1`; this
  forces `f ≥ n`, outside the paper's implicit `f < n` (out of range, not an error)
  (`theorem_7_false_one`).
* Non-vacuity: for `f = 0` the echo protocol solves partially synchronous BB for every `n`
  (`echo_psyncBB_zero`), so `IsPsyncBB` is satisfiable.
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

variable {P V : Type*} [DecidableEq P]

/-- The echo protocol with broadcaster `s` (messages are values; no signatures needed). -/
def echo (s : P) : Algorithm P V (Option V) V V where
  init p v := if p = s then some v else none
  step _ st ib := st.or (ib s).head?
  send p st _ := if p = s then st.toList else []
  decide _ st := st

namespace echo

variable {s : P} {R : Run P V V}

theorem st_succ (τ : ℕ) (p : P) :
    R.st (echo s) (τ + 1) p = (R.st (echo s) τ p).or ((R.inbox (echo s) p τ s).head?) :=
  R.st_succ (echo s) τ p

theorem st_mono {p : P} {τ : ℕ} {v : V} (h : R.st (echo s) τ p = some v) :
    ∀ τ', τ ≤ τ' → R.st (echo s) τ' p = some v := by
  intro τ' hτ'
  induction τ', hτ' using Nat.le_induction with
  | base => exact h
  | succ τ' _ ih => rw [st_succ, ih]; rfl

theorem decides_unique {p : P} {v w : V} (hv : R.Decides (echo s) p v)
    (hw : R.Decides (echo s) p w) : v = w := by
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨τ', hτ'⟩ := hw
  have h1 := st_mono hτ (max τ τ') (le_max_left _ _)
  have h2 := st_mono hτ' (max τ τ') (le_max_right _ _)
  change R.st (echo s) _ p = _ at h1 h2
  rw [h1] at h2; exact Option.some.inj h2

theorem st_s (_hs : s ∉ R.faulty) : ∀ τ, R.st (echo s) τ s = some (R.inp s) := by
  intro τ
  exact st_mono (τ := 0) (by simp [echo]) τ (Nat.zero_le _)

theorem out_s (hs : s ∉ R.faulty) (τ : ℕ) (p : P) :
    R.out (echo s) s τ p = [R.inp s] := by
  rw [Run.out_of_correct _ _ hs, st_s hs]; simp [echo]

/-- With an honest broadcaster, every process only ever holds the broadcaster's input. -/
theorem st_eq (hs : s ∉ R.faulty) (p : P) :
    ∀ τ, R.st (echo s) τ p = none ∨ R.st (echo s) τ p = some (R.inp s) := by
  intro τ
  induction τ with
  | zero =>
    by_cases hp : p = s
    · subst hp; right; simp [echo]
    · left; simp [echo, hp]
  | succ τ ih =>
    rw [st_succ]
    rcases ih with h | h
    · rw [h]
      have : ∀ m ∈ R.inbox (echo s) p τ s, m = R.inp s := by
        intro m hm
        obtain ⟨σ, -, -, hm'⟩ := Run.mem_inbox.mp hm
        rw [out_s hs] at hm'; simpa using hm'
      cases hl : R.inbox (echo s) p τ s with
      | nil => left; rfl
      | cons m l => right; simp [this m (by rw [hl]; simp)]
    · rw [h]; right; rfl

theorem decides_eq (hs : s ∉ R.faulty) {p : P} {v : V} (hv : R.Decides (echo s) p v) :
    v = R.inp s := by
  obtain ⟨τ, hτ⟩ := hv
  rcases st_eq hs p τ with h | h <;> change R.st (echo s) τ p = _ at hτ <;> rw [h] at hτ
  · simp at hτ
  · exact (Option.some.inj hτ).symm

/-- After the batch sent by an honest `s` at time `0` is delivered, `p` has committed. -/
theorem commits_after (hs : s ∉ R.faulty) (p : P) :
    R.st (echo s) (R.dl s 0 p + 1) p = some (R.inp s) := by
  have hm : R.inp s ∈ R.inbox (echo s) p (R.dl s 0 p) s :=
    Run.mem_inbox.mpr ⟨0, Nat.zero_le _, rfl, by rw [out_s hs]; simp⟩
  rw [st_succ]
  rcases st_eq hs p (R.dl s 0 p) with h | h
  · rw [h]
    cases hl : R.inbox (echo s) p (R.dl s 0 p) s with
    | nil => rw [hl] at hm; simp at hm
    | cons m l =>
      have := decides_eq (R := R) (p := p) (v := m) hs ⟨R.dl s 0 p + 1, by
        change R.st (echo s) _ p = _; rw [st_succ, h, hl]; rfl⟩
      simp [this]
  · rw [h]; rfl

theorem decides_of_valid {f D : ℕ} (hR : R.Valid f D) (hs : s ∉ R.faulty) {p : P}
    (hp : p ∉ R.faulty) : R.Decides (echo s) p (R.inp s) ∧
      R.dl s 0 p ≤ max 0 R.gst + D :=
  ⟨⟨R.dl s 0 p + 1, commits_after hs p⟩, hR.dl_le s 0 p hs hp⟩

end echo

open echo

variable [Fintype P] {s : P}

theorem two_cases (h2 : Fintype.card P = 2) {p q : P} (hp : p ≠ s) (hq : q ≠ s) : p = q := by
  by_contra hpq
  have : ({p, q, s} : Finset P).card ≤ 2 := h2 ▸ card_le_univ _
  rw [card_insert_of_notMem (by simp [hpq, hp]), card_insert_of_notMem (by simp [hq])] at this
  simp at this

/-- For `n = 2` the echo protocol solves Byzantine reliable broadcast in every run (any `f`,
asynchronous), without signatures. -/
theorem echo_brb_two (h2 : Fintype.card P = 2) (f : ℕ) :
    IsBRB (Auth.none P V) (echo (V := V) s) s (asyncRuns f) where
  agreement R _ _ p hp q hq v w hv hw := by
    by_cases hs : s ∈ R.faulty
    · obtain rfl := two_cases h2 (p := p) (q := q) (fun e => hp (by rw [e]; exact hs)) (fun e => hq (by rw [e]; exact hs))
      exact decides_unique hv hw
    · rw [decides_eq hs hv, decides_eq hs hw]
  validity R hR _ hs p hp := by
    obtain ⟨D, hD⟩ := hR
    exact (decides_of_valid hD hs hp).1
  termination R hR _ := by
    rintro ⟨p, hp, v, hv⟩ q hq
    by_cases hs : s ∈ R.faulty
    · obtain rfl := two_cases h2 (p := p) (q := q) (fun e => hp (by rw [e]; exact hs)) (fun e => hq (by rw [e]; exact hs))
      exact ⟨v, hv⟩
    · obtain ⟨D, hD⟩ := hR
      exact ⟨_, (decides_of_valid hD hs hq).1⟩

/-- The echo protocol commits after one message delay (synchronous runs, effective delays
`≤ δ`). -/
theorem echo_latency_sync {f δ : ℕ} :
    LatencyWithin (Auth.none P V) (echo (V := V) s) s (syncRuns f δ) δ := by
  intro R hR _ hs p hp
  by_cases hps : p = s
  · subst hps; exact ⟨_, 0, Nat.zero_le _, st_s hs 0⟩
  · have := hR.dl_lt s 0 p hs hp
    exact ⟨R.inp s, R.dl s 0 p + 1, by omega, commits_after hs p⟩

/-- The echo protocol commits within one round in partially synchronous good-case runs. -/
theorem echo_latency_psync {f D : ℕ} :
    PsyncGoodCaseRounds (Auth.none P V) (echo (V := V) s) s f D 1 := by
  intro R hR _ hs p hp
  have := hR.1.dl_le s 0 p hs hp
  rw [hR.2] at this
  exact ⟨R.inp s, R.dl s 0 p + 1, by simp at this; omega, commits_after hs p⟩

/-- **Theorem 4 is false for `n = 2`**: a BRB protocol for asynchronous runs, resilient to any
number of faults, that commits within one round in the lock-step good case. -/
theorem theorem_4_false_two (h2 : Fintype.card P = 2) (f D : ℕ) :
    ∃ (A : Algorithm P V (Option V) V V), A.Unforging (Auth.none P V) ∧
      IsBRB (Auth.none P V) A s (asyncRuns f) ∧
      PsyncGoodCaseRounds (Auth.none P V) A s f D 1 :=
  ⟨echo s, Algorithm.unforging_none _, echo_brb_two h2 f, echo_latency_psync⟩

/-- **Theorems 8 and 9 are false for `n = 2`**: a BRB protocol for synchronous runs with any
delay bound and any number of faults, with good-case latency `δ` (`< 2δ`, `< Δ + δ`). -/
theorem theorem_8_false_two (h2 : Fintype.card P = 2) (f Δ δ : ℕ) :
    ∃ (A : Algorithm P V (Option V) V V), A.Unforging (Auth.none P V) ∧
      IsBRB (Auth.none P V) A s (syncRuns f Δ) ∧
      LatencyWithin (Auth.none P V) A s (syncRuns f δ) δ := by
  refine ⟨echo s, Algorithm.unforging_none _, ?_, echo_latency_sync⟩
  have h := echo_brb_two (V := V) (s := s) h2 f
  have sub : ∀ R ∈ syncRuns (P := P) (M := V) (V := V) f Δ, R ∈ asyncRuns f :=
    fun R hR => ⟨_, SyncValid.valid hR⟩
  exact ⟨fun R hR => h.agreement R (sub R hR), fun R hR => h.validity R (sub R hR),
    fun R hR => h.termination R (sub R hR)⟩

/-- For `n = 1` the echo protocol solves partially synchronous Byzantine broadcast for every `f`
and commits at time `0`: the literal Theorems 6 and 7 fail for `n = 1` (out of range: `f ≥ n`). -/
theorem theorem_7_false_one (h1 : Fintype.card P = 1) (f D r : ℕ) :
    IsPsyncBB (Auth.none P V) (echo (V := V) s) s f D ∧
      PsyncGoodCaseRounds (Auth.none P V) (echo (V := V) s) s f D r := by
  have hall : ∀ p : P, p = s := fun p => Fintype.card_le_one_iff.mp h1.le p s
  refine ⟨⟨fun R _ _ p hp q hq v w hv hw => ?_, fun R _ _ _ hs p _ => ?_,
    fun R _ _ p hp => ?_⟩, fun R _ _ hs p _ => ?_⟩
  · obtain rfl := hall p; obtain rfl := hall q
    exact decides_unique hv hw
  · obtain rfl := hall p; exact ⟨0, st_s hs 0⟩
  · obtain rfl := hall p; exact ⟨_, 0, st_s hp 0⟩
  · obtain rfl := hall p; exact ⟨_, 0, Nat.zero_le _, st_s hs 0⟩

/-- **Non-vacuity.** Without faults, the echo protocol solves partially synchronous Byzantine
broadcast (every `n`, every `D`). -/
theorem echo_psyncBB_zero (D : ℕ) : IsPsyncBB (Auth.none P V) (echo (V := V) s) s 0 D where
  agreement R hR _ p _ q _ v w hv hw := by
    have hs : s ∉ R.faulty := by
      have := hR.card_faulty; simp [card_eq_zero.mp (Nat.le_zero.mp this)]
    rw [decides_eq hs hv, decides_eq hs hw]
  validity R hR _ _ hs p hp := (decides_of_valid hR hs hp).1
  termination R hR _ p hp := by
    have hs : s ∉ R.faulty := by
      have := hR.card_faulty; simp [card_eq_zero.mp (Nat.le_zero.mp this)]
    exact ⟨_, (decides_of_valid hR hs hp).1⟩

end GoodCaseLatencyBB
