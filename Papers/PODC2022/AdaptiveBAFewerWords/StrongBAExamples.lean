import Papers.PODC2022.AdaptiveBAFewerWords.StrongBA

/-!
# Algorithm 5 of [CKS22]: non-vacuity and the printed hand-off code

* `failureFree_decides`: in a concrete failure-free run (`n = 3`) all processes decide at line 14.
* `fallback_exists`: for every valid run some behaviour of `A_fallback` satisfies the black-box
  specification, so the hypothesis of `theorem7` is never vacuous.
* `printed_noProof_disagreement`: with the printed line 26 (a decided process echoes
  `bu_proof = ⊥`), agreement fails: `n = 3`, Byzantine leader, `p_2` (input `0`) decides `0` at
  line 14, `p_3` (input `1`) never learns a certificate and `A_fallback` may output `1`.
* `strictWindow_disagreement`: with the printed loop condition `fallback_start > now` and delays of
  exactly `δ`, the decided process's certified echo arrives exactly at `fallback_start` and is
  dropped; same outcome.
* `intended_adopts`: in the same run, the intended code makes `p_3` adopt `0`.
-/

namespace Podc.AdaptiveBAFewerWords.StrongBA

/-! ### A failure-free run -/

/-- No Byzantine process; all delays `1`. -/
def ffAdv : Adversary 1 :=
  { F := ∅, r1 := fun _ => ∅, r2 := fun _ => none, r3 := fun _ => ∅, r4 := fun _ => none,
    d := fun _ _ => 1, fb := ∅ }

/-- Inputs `0, 1, 1`. -/
def ffInp : Proc 1 → Bool := ![false, true, true]

lemma ffAdv_valid : AdvValid ffInp ffAdv 1 where
  card_F := by simp [ffAdv]
  r2 := by simp [ffAdv, leader]
  r4 := by simp [ffAdv, leader]
  delay := by simp [ffAdv]
  fb := by simp [ffAdv]

/-- Non-vacuity: a failure-free run in which every process decides `1` at line 14, whatever
`A_fallback` would do. -/
theorem failureFree_decides (out : Proc 1 → Option Bool) (p : Proc 1) :
    decision ffInp ffAdv out p = some true := by
  apply decision_decided
  revert p
  decide

/-! ### The black-box hypothesis is satisfiable -/

open Classical in
/-- For every valid run, `A_fallback` can behave according to its specification: all output `1`
unless all correct inputs are `0`. -/
theorem fallback_exists {t δ : ℕ} {inp : Proc t → Bool} {A : Adversary t}
    (hA : AdvValid inp A δ) (fin : Proc t → Bool) :
    ∃ out, FallbackSpec δ (correct A) (fbStart inp A δ) fin out := by
  obtain ⟨c, hc⟩ := exists_correct hA
  let b : Bool := if ∀ p ∈ correct A, fin p = false then false else true
  refine ⟨fun _ => some b, fun _ _ => ⟨?_, ?_, ?_⟩⟩
  · intro p _ q _ x y hx hy; simp_all
  · intro p _; exact ⟨b, rfl⟩
  · intro v hv p _ x hx
    simp only [Option.some.injEq] at hx
    subst hx
    cases v
    · simp only [b]; rw [ite_eq_left_iff.mpr (fun h => absurd hv h)]
    · have : ¬ ∀ p ∈ correct A, fin p = false := fun h => by
        simpa [hv c hc] using h c hc
      simp [b, this]

/-! ### The printed hand-off code violates agreement -/

/-- `n = 3`, `t = 1`; the leader `p_1` is Byzantine. It proposes `0` (with `QC_propose(0)` from its
own and `p_2`'s signatures), both correct processes sign `⟨decide, 0⟩`, and it sends `QC_decide(0)`
to `p_2` only. No Byzantine fallback messages; all fallback delays are `δ = 1`. -/
def cxAdv : Adversary 1 :=
  { F := {0}, r1 := fun _ => ∅, r2 := fun _ => some false, r3 := fun _ => ∅,
    r4 := fun p => if p = 1 then some false else none, d := fun _ _ => 1, fb := ∅ }

/-- Inputs: `p_2` has `0`, `p_3` has `1`. -/
def cxInp : Proc 1 → Bool := ![false, false, true]

lemma cxAdv_valid : AdvValid cxInp cxAdv 1 where
  card_F := by simp [cxAdv]
  r2 := by
    intro _ p v h
    simp only [cxAdv, Option.some.injEq] at h
    subst h
    unfold QCproposeAvail sigAvail
    decide
  r4 := by
    intro _ p v h
    simp only [cxAdv] at h
    split_ifs at h
    cases h
    intro q hq
    simp [rprop, cxAdv, leader]
  delay := by simp [cxAdv]
  fb := by simp [cxAdv]

lemma cx_dec5_1 : dec5 cxInp cxAdv 1 = some false := by decide
lemma cx_dec5_2 : dec5 cxInp cxAdv 2 = none := by decide

/-- In the counterexample run, `p_2` sends its echo at time `1` (when `p_3`'s line-17 message
arrives). -/
lemma cx_fbTime_1 : fbTime cxInp cxAdv 1 = some 1 := by
  have h1 : Hears cxInp cxAdv 1 1 :=
    Hears.relay (p := 2) (τ' := 0) (by decide) (Hears.start (by decide) cx_dec5_2) le_rfl
  obtain ⟨τ₀, h, hle⟩ := fbTime_le h1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with rfl | rfl
  · exfalso
    cases fbTime_some h with
    | start _ h2 => simp [cx_dec5_1] at h2
    | byz hm _ => simp [cxAdv] at hm
    | relay _ _ h3 => simp [cxAdv] at h3
  · exact h

/-- The fallback outputs `1` everywhere. -/
def cxOut : Proc 1 → Option Bool := fun _ => some true

/-- If `p_3` does not adopt a value, the run violates agreement for an `A_fallback` behaviour
allowed by its specification. -/
lemma cx_disagreement (R : Reading) (hno : ∀ v, ¬ RecvProof cxInp cxAdv R 1 2 v) :
    FallbackSpec 1 (correct cxAdv) (fbStart cxInp cxAdv 1) (bu cxInp cxAdv R 1) cxOut ∧
      ¬ Agreement (correct cxAdv) (decision cxInp cxAdv cxOut) := by
  have hb1 : bu cxInp cxAdv R 1 1 = false := by simp [bu, cx_dec5_1]
  have hb2 : bu cxInp cxAdv R 1 2 = true := by simp [bu, cx_dec5_2, hno]; rfl
  have hC1 : (1 : Proc 1) ∈ correct cxAdv := by simp [correct, cxAdv]
  have hC2 : (2 : Proc 1) ∈ correct cxAdv := by simp [correct, cxAdv]
  refine ⟨fun _ _ => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p _ q _ x y hx hy; simp_all [cxOut]
  · intro p _; exact ⟨true, rfl⟩
  · intro v hv
    have := (hv 1 hC1).trans (hv 2 hC2).symm
    rw [hb1, hb2] at this
    cases this
  · intro h
    have := h 1 hC1 2 hC2 false true (decision_decided cx_dec5_1)
      (by rw [decision_undecided (by simpa [correct] using hC2) cx_dec5_2]; rfl)
    cases this

/-- **Slip in line 26** (printed reading: a decided process echoes `bu_proof = ⊥`): agreement is
violated for a valid adversary and a fallback behaviour satisfying its strong BA specification. -/
theorem printed_noProof_disagreement :
    let R : Reading := ⟨false, true⟩
    AdvValid cxInp cxAdv 1 ∧
      FallbackSpec 1 (correct cxAdv) (fbStart cxInp cxAdv 1) (bu cxInp cxAdv R 1) cxOut ∧
      ¬ Agreement (correct cxAdv) (decision cxInp cxAdv cxOut) := by
  refine ⟨cxAdv_valid, cx_disagreement _ ?_⟩
  rintro v (⟨s, τ, hm, -⟩ | ⟨h, -⟩)
  · simp [cxAdv] at hm
  · cases h

/-- **Boundary slip in line 20** (printed `while fallback_start > now` drops a message arriving
exactly at `fallback_start`): with all delays equal to `δ`, `p_2`'s certified echo reaches `p_3`
exactly at `2δ` and agreement is violated. -/
theorem strictWindow_disagreement :
    let R : Reading := ⟨true, false⟩
    AdvValid cxInp cxAdv 1 ∧
      FallbackSpec 1 (correct cxAdv) (fbStart cxInp cxAdv 1) (bu cxInp cxAdv R 1) cxOut ∧
      ¬ Agreement (correct cxAdv) (decision cxInp cxAdv cxOut) := by
  refine ⟨cxAdv_valid, cx_disagreement _ ?_⟩
  rintro v (⟨s, τ, hm, -⟩ | ⟨-, p, hp, hpv, τ, hτ, hw⟩)
  · simp [cxAdv] at hm
  · have hp1 : p = 1 := by
      fin_cases p
      · simp [cxAdv] at hp
      · rfl
      · simp [cx_dec5_2] at hpv
    subst hp1
    rw [cx_fbTime_1] at hτ
    cases hτ
    simp [InWindow, cxAdv] at hw

/-- With the intended code, in the same run `p_3` adopts `0` and enters `A_fallback` with `0`
(so by strong unanimity every correct process decides `0`). -/
theorem intended_adopts : bu cxInp cxAdv .intended 1 2 = false :=
  bu_eq_of_decided cxAdv_valid (p := 1) (by simp [cxAdv]) cx_dec5_1 (by simp [cxAdv])

end Podc.AdaptiveBAFewerWords.StrongBA
