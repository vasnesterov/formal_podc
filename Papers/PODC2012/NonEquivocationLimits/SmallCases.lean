import Papers.PODC2012.NonEquivocationLimits.Claim32

/-!
# Claims 3.1 and 3.2 fail for `n ≤ 2`

Both claims are stated for every `n < 3f + 1`, and both proofs start with "without loss of
generality, `n = 3f`" and split the processes into three groups. For `n ≤ 2` this is impossible,
and indeed r-broadcast is then solvable for every `f`, without signatures and against equivocating
faulty processes: the sender keeps sending its message and delivers it at once; every other
process delivers the first message it receives from the sender (`echo`). With `n ≤ 2`, two
distinct correct processes include the sender, so Agreement reduces to Validity.

The claims hold for `n ≥ 3` (`claim_3_1`, `claim_3_2`).
-/

set_option linter.unusedSectionVars false

namespace Podc.NonEquivocationLimits

open Cslib.Byzantine.PartialSync Finset

variable {P V κ : Type*} [DecidableEq P]

/-- The echo protocol with sender `s` (messages are values). -/
def echo (s : P) : Algorithm P V (Option V) V V where
  init p v := if p = s then some v else none
  step _ st ib := st.or (ib s).head?
  send p st _ := if p = s then st.toList else []
  decide _ st := st

namespace echo

variable {s : P} {R : Run P V V}

theorem send_eq (p : P) (st : Option V) (q : P) :
    (echo s).send p st q = if p = s then st.toList else [] := rfl

theorem st_succ (τ : ℕ) (p : P) :
    R.st (echo s) (τ + 1) p = (R.st (echo s) τ p).or ((R.inbox (echo s) p τ s).head?) :=
  R.st_succ (echo s) τ p

theorem st_mono {p : P} {τ : ℕ} {v : V} (h : R.st (echo s) τ p = some v) :
    ∀ τ', τ ≤ τ' → R.st (echo s) τ' p = some v := by
  intro τ' hτ'
  induction τ', hτ' using Nat.le_induction with
  | base => exact h
  | succ τ' _ ih => rw [st_succ, ih]; rfl

theorem decides_iff {p : P} {v : V} : R.Decides (echo s) p v ↔ ∃ τ, R.st (echo s) τ p = some v :=
  Iff.rfl

theorem decides_unique {p : P} {v w : V} (hv : R.Decides (echo s) p v)
    (hw : R.Decides (echo s) p w) : v = w := by
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨τ', hτ'⟩ := hw
  have h1 := st_mono hτ (max τ τ') (le_max_left _ _)
  have h2 := st_mono hτ' (max τ τ') (le_max_right _ _)
  rw [h1] at h2; exact Option.some.inj h2

theorem st_sender (τ : ℕ) : R.st (echo s) τ s = some (R.inp s) :=
  st_mono (τ := 0) (by simp [echo]) τ (Nat.zero_le _)

/-- A non-sender only adopts values received from the sender. -/
theorem st_eq_some {p : P} (hp : p ≠ s) {v : V} :
    ∀ τ, R.st (echo s) τ p = some v → ∃ τ', v ∈ R.inbox (echo s) p τ' s := by
  intro τ
  induction τ with
  | zero => simp [echo, hp]
  | succ τ ih =>
    intro h
    rw [st_succ] at h
    cases hτ : R.st (echo s) τ p with
    | some w => rw [hτ] at h; exact ih (by rw [hτ]; simpa using h)
    | none =>
      rw [hτ] at h
      simp only [Option.none_or] at h
      exact ⟨τ, List.mem_of_mem_head? h⟩

/-- A correct sender only sends its input. -/
theorem mem_inbox_sender {p : P} (hs : s ∉ R.faulty) {τ : ℕ} {v : V}
    (h : v ∈ R.inbox (echo s) p τ s) : v = R.inp s := by
  obtain ⟨σ, -, -, hm⟩ := Run.mem_inbox.mp h
  rw [Run.out_of_correct _ _ hs, send_eq, st_sender] at hm
  simpa using hm

theorem validity (hs : s ∉ R.faulty) {p : P} {v : V} (h : R.Decides (echo s) p v) :
    v = R.inp s := by
  obtain ⟨τ, hτ⟩ := h
  by_cases hp : p = s
  · subst hp; rw [st_sender] at hτ; exact (Option.some.inj hτ).symm
  · obtain ⟨τ', h'⟩ := st_eq_some hp τ hτ
    exact mem_inbox_sender hs h'

/-- With `n ≤ 2`, the echo protocol solves r-broadcast in every asynchronous run, with any number
of Byzantine (possibly equivocating) faults. -/
theorem isRBroadcast [Fintype P] (hP : Fintype.card P ≤ 2) (f : ℕ) :
    IsRBroadcast (echo (V := V) s) s {R | R.AsyncValid f} where
  senderTermination R _ _ := ⟨0, st_sender 0⟩
  completeness R hR := by
    rintro ⟨p, hp, v, hv⟩ q hq
    by_cases hqs : q = s
    · subst hqs; exact ⟨_, 0, st_sender 0⟩
    by_cases hs : s ∈ R.faulty
    · -- the only correct processes are `p` and `q`, both different from `s`
      have hps : p ≠ s := by rintro rfl; exact hp hs
      by_cases hpq : p = q
      · subst hpq; exact ⟨v, hv⟩
      · have : ({p, q, s} : Finset P).card ≤ 2 := (card_le_univ _).trans hP
        rw [card_insert_of_notMem (by simp [hpq, hps]),
          card_insert_of_notMem (by simp [hqs])] at this
        simp at this
    · -- the sender's first batch reaches `q`
      set d := R.dl s 0 q
      have hmem : R.inp s ∈ R.inbox (echo s) q d s :=
        Run.mem_inbox.mpr ⟨0, Nat.zero_le _, rfl, by
          rw [Run.out_of_correct _ _ hs, send_eq, st_sender]; simp⟩
      obtain ⟨w, hw⟩ : ∃ w, R.st (echo s) (d + 1) q = some w := by
        rw [st_succ]
        cases h : R.st (echo s) d q with
        | some w => exact ⟨w, rfl⟩
        | none =>
          obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
          exact ⟨a, by simp [hl]⟩
      exact ⟨w, d + 1, hw⟩
  validity R _ hs p _ v h := validity hs h
  agreement R _ p hp q hq v w hv hw := by
    by_cases hpq : p = q
    · subst hpq; exact decides_unique hv hw
    have hs : s ∉ R.faulty := by
      intro hs
      have hps : p ≠ s := by rintro rfl; exact hp hs
      have hqs : q ≠ s := by rintro rfl; exact hq hs
      have : ({p, q, s} : Finset P).card ≤ 2 := (card_le_univ _).trans hP
      rw [card_insert_of_notMem (by simp [hpq, hps]),
        card_insert_of_notMem (by simp [hqs])] at this
      simp at this
    rw [validity hs hv, validity hs hw]
  integrity R _ p _ v w hv hw := decides_unique hv hw

/-- The echo protocol never equivocates (a correct process only ever sends its fixed input). -/
theorem respectsNE (key : V → κ) : RespectsNE (echo (V := V) s) key := by
  intro R q _ τ τ' p p' m hm m' hm' _
  rw [Run.out_of_correct _ _ ‹_›, send_eq] at hm hm'
  by_cases hq : q = s
  · subst hq; rw [st_sender] at hm hm'; simp_all
  · simp [hq] at hm

end echo

/-- **Claim 3.1 is false for `n ≤ 2`** (for every `f`, in particular for `n < 3f + 1`): the echo
protocol uses non-equivocation as intended (for any key map) and solves r-broadcast against
non-equivocating Byzantine processes in the asynchronous model. -/
theorem claim_3_1_false_small [Fintype P] (hP : Fintype.card P ≤ 2) (f : ℕ) (s : P)
    (key : V → κ) :
    RespectsNE (echo (V := V) s) key ∧
      IsRBroadcast (echo s) s {R | R.AsyncValid f ∧ NonEquivocating key R} :=
  ⟨echo.respectsNE key, (echo.isRBroadcast hP f).mono fun _ hR => hR.1⟩

/-- **Claim 3.2 is false for `n ≤ 2`**: the echo protocol is (trivially) unforging and solves
r-broadcast against equivocating Byzantine processes in the asynchronous model. -/
theorem claim_3_2_false_small [Fintype P] (hP : Fintype.card P ≤ 2) (f : ℕ) (s : P) :
    (echo (V := V) s).Unforging (Auth.none P V) ∧
      IsRBroadcast (echo s) s {R | R.AsyncValid f ∧ R.AuthValid (Auth.none P V) (echo s)} :=
  ⟨Algorithm.unforging_none _, (echo.isRBroadcast hP f).mono fun _ hR => hR.1⟩

end Podc.NonEquivocationLimits
