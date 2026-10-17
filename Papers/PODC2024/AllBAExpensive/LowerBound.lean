import Papers.PODC2024.AllBAExpensive.WeakLowerBound
import Papers.PODC2024.AllBAExpensive.Containment
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# All Byzantine Agreement Problems Are Expensive — main lower bounds

* `exists_params`: the choice of `β = |B| = |C|` and `σ` giving `t² / 32` (the paper: `t/4`, `t/2`).
* `omission_lower_bound_sq`: `t² ≤ 32 · #messages` for every `t < n` (also `t ≤ 7`, where the
  paper's argument needs `t ≥ 8`; `t = 1` is a separate zero-message argument).
* `weak_consensus_lower_bound_om`: **Lemma 1** (omission model).
* `weak_consensus_lower_bound(_auth)`: **Theorem 2** (Byzantine, synchronous).
* `ff_mem_val`: Lemma 7 for fault-free executions, omission model.
* `message_lower_bound_om`: **Theorem 3** in the omission model.
* `message_lower_bound(_auth)`: **Theorems 1 and 3** (Byzantine, synchronous, with or without
  signatures), and `message_complexity_lower_bound(_auth)` (message-complexity form).
* `external_validity_lower_bound(_auth)`: **Corollary 1**.
-/

namespace AllBAExpensive

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO} {Au : Auth P M K}

omit [DecidableEq P] in
/-- Choice of parameters: for `2 ≤ t < n` there are `β, σ` (`β ≈ t/4`, `σ = t + 1 - 2β`) with
`t² ≤ 32 ⌈β/2⌉ σ`. -/
theorem exists_params (ht : 2 ≤ t) (htn : t < Fintype.card P) :
    ∃ β σ, Params P t β σ ∧ 1 ≤ σ ∧ t ^ 2 ≤ 32 * ((β + 1) / 2 * σ) := by
  by_cases h8 : 8 ≤ t
  · refine ⟨2 * (t / 8), t + 1 - 4 * (t / 8), ⟨by omega, by omega, by omega⟩, by omega, ?_⟩
    have h1 : (2 * (t / 8) + 1) / 2 = t / 8 := by omega
    rw [h1]
    obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < 8 ∧ t = 8 * a + r :=
      ⟨t / 8, t % 8, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod t 8).symm⟩
    have ha : (8 * a + r) / 8 = a := by omega
    rw [ha]
    have ha1 : 1 ≤ a := by omega
    have h2 : 8 * a + r + 1 - 4 * a = 4 * a + r + 1 := by omega
    rw [h2]
    nlinarith
  · refine ⟨1, t - 1, ⟨by omega, by omega, by omega⟩, by omega, ?_⟩
    interval_cases t <;> norm_num

/-- A process sends at most `msgsUpTo (τ + 1)` messages to another process at time `τ`. -/
theorem send_length_le_msgsUpTo (E : OmExec P VI) {F : Finset P} {q p : P} (hq : q ∉ F)
    (hpq : p ≠ q) (τ : ℕ) : (A.send q (E.st A τ q) p).length ≤ E.msgsUpTo A F (τ + 1) := by
  unfold OmExec.msgsUpTo
  refine le_trans ?_ (single_le_sum (f := fun τ' => ∑ q ∈ univ.filter (· ∉ F),
    ∑ p ∈ univ.filter (· ≠ q), (A.send q (E.st A τ' q) p).length) (fun _ _ => Nat.zero_le _)
    (mem_range.mpr (Nat.lt_succ_self τ)))
  refine le_trans ?_ (single_le_sum (f := fun q => ∑ p ∈ univ.filter (· ≠ q),
    (A.send q (E.st A τ q) p).length) (fun _ _ => Nat.zero_le _) (by simpa using hq))
  exact single_le_sum (f := fun p => (A.send q (E.st A τ q) p).length)
    (fun _ _ => Nat.zero_le _) (by simpa using hpq)

omit [Fintype P] in
/-- In a fault-free execution all processes decide the same value. -/
theorem ff_decides (hS : OmSolves t A val) {x : P → VI} {p : P} {v : VO}
    (hv : (ffExec x).Decides A p v) (q : P) : (ffExec x).Decides A q v := by
  have h0 : (ffExec x).Admits A ∅ := OmExec.ff_admits ∅
  obtain ⟨w, hw⟩ := hS.termination (ffExec x) ∅ h0 (by simp) q (by simp)
  rwa [hS.agreement (ffExec x) ∅ h0 (by simp) q (by simp) p (by simp) w v hw hv] at hw

/-- With at least two processes, some fault-free execution has a message (if two fault-free
executions decide differently): otherwise each process decides as in isolation. -/
theorem one_message (hS : OmSolves t A val) (hn : 2 ≤ Fintype.card P)
    {x₀ x₁ : P → VI} {p₀ p₁ : P} {v₀ v₁ : VO} (hne : v₀ ≠ v₁)
    (h₀ : (ffExec x₀).Decides A p₀ v₀) (h₁ : (ffExec x₁).Decides A p₁ v₁) :
    ∃ (E : OmExec P VI) (F : Finset P), E.Admits A F ∧ F.card ≤ t ∧
      ∃ N, 1 ≤ E.msgsUpTo A F N := by
  by_contra hK
  push Not at hK
  have hsil : ∀ x : P → VI, ∀ τ q p, p ≠ q → A.send q ((ffExec x).st A τ q) p = [] := by
    intro x τ q p hpq
    have := send_length_le_msgsUpTo (A := A) (ffExec x) (F := ∅) (by simp) hpq τ
    have := hK (ffExec x) ∅ (OmExec.ff_admits ∅) (by simp) (τ + 1)
    exact List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := P) (by omega)
  set z : P → VI := fun p => if p = a then x₀ p else x₁ p
  -- a process with input `x c` behaves as in the fault-free execution with inputs `x`
  have iso : ∀ (x : P → VI) (c : P), z c = x c → ∀ τ,
      (ffExec z).st A τ c = (ffExec x).st A τ c := by
    intro x c hc τ
    refine OmExec.st_eq_of_inbox_eq (E := ffExec z) (E' := ffExec x) (X := fun _ => {c})
      (fun _ => le_rfl) (fun p hp => by rw [Set.mem_singleton_iff.mp hp]; exact hc)
      (fun τ ih p hp => ?_) τ c rfl
    rw [Set.mem_singleton_iff.mp hp]
    funext q
    by_cases hq : q = c
    · subst hq; rw [OmExec.inbox, OmExec.inbox, ih q rfl]; rfl
    · simp only [OmExec.ff_inbox]
      rw [hsil z τ q c (Ne.symm hq), hsil x τ q c (Ne.symm hq)]
  have da : (ffExec z).Decides A a v₀ := by
    obtain ⟨τ, h⟩ := ff_decides hS h₀ a
    exact ⟨τ, by rw [iso x₀ a (by simp [z]) τ]; exact h⟩
  have db : (ffExec z).Decides A b v₁ := by
    obtain ⟨τ, h⟩ := ff_decides hS h₁ b
    exact ⟨τ, by rw [iso x₁ b (by simp [z, Ne.symm hab]) τ]; exact h⟩
  exact hne (hS.agreement (ffExec z) ∅ (OmExec.ff_admits ∅)
    (by simp) a (by simp) b (by simp) v₀ v₁ da db)

/-- **Lemma 1, all `t`.** Under the hypotheses of `omission_lower_bound`, some execution has at
least `t² / 32` messages (`t² ≤ 32 · #messages`), for every `t < n`. -/
theorem omission_lower_bound_sq (hS : OmSolves t A val) (htn : t < Fintype.card P)
    {x₀ x₁ : P → VI} {p₀ p₁ : P} {v₀ v₁ : VO} (hne : v₀ ≠ v₁)
    (h₀ : (ffExec x₀).Decides A p₀ v₀) (h₁ : (ffExec x₁).Decides A p₁ v₁) :
    ∃ (E : OmExec P VI) (F : Finset P), E.Admits A F ∧ F.card ≤ t ∧
      ∃ N, t ^ 2 ≤ 32 * E.msgsUpTo A F N := by
  rcases Nat.lt_or_ge t 2 with ht | ht
  · rcases Nat.lt_or_ge t 1 with ht1 | ht1
    · exact ⟨ffExec x₀, ∅, OmExec.ff_admits ∅, by simp, 0,
        by simp [show t = 0 by omega]⟩
    · obtain ⟨E, F, h1, h2, N, hN⟩ := one_message hS (by omega) hne h₀ h₁
      exact ⟨E, F, h1, h2, N, by rw [show t = 1 by omega]; omega⟩
  · obtain ⟨β, σ, hp, hσ, hb⟩ := exists_params ht htn
    obtain ⟨E, F, h1, h2, N, hN⟩ := omission_lower_bound hS hp hσ hne h₀ h₁
    exact ⟨E, F, h1, h2, N, le_trans hb (by omega)⟩

/-- **Lemma 1** of [AllBAExpensive]: any (binary) weak consensus algorithm tolerating `t < n`
omission failures has an execution in which correct processes send at least `t² / 32`
messages. -/
theorem weak_consensus_lower_bound_om {A : Algorithm P M S Bool Bool}
    (hS : OmSolves t A (weakValidity P Bool)) (htn : t < Fintype.card P) :
    ∃ (E : OmExec P Bool) (F : Finset P), E.Admits A F ∧ F.card ≤ t ∧
      ∃ N, t ^ 2 ≤ 32 * E.msgsUpTo A F N := by
  have hP : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p⟩ := hP
  have h0 : ∀ b : Bool, (ffExec (fun _ : P => b)).Decides A p b := by
    intro b
    have hadm : (ffExec (fun _ : P => b)).Admits A ∅ := OmExec.ff_admits ∅
    obtain ⟨w, hw⟩ := hS.termination _ ∅ hadm (by simp) p (by simp)
    have := hS.validity _ ∅ hadm (by simp) p (by simp) w hw
    rwa [this b (fun q => by simp [OmExec.conf])] at hw
  exact omission_lower_bound_sq hS htn Bool.false_ne_true (h0 false) (h0 true)

/-- Lemma 7 for fault-free executions in the omission model: a decision of the fault-free
execution with inputs `x` is admissible for every input configuration contained in `x`. -/
theorem ff_mem_val (hS : OmSolves t A val) (htn : t < Fintype.card P) {x : P → VI} {p : P}
    {v : VO} (hv : (ffExec x).Decides A p v) {c' : Config P VI} (hc' : IsInputConfig t c')
    (hcont : Contains (fun q => some (x q)) c') : v ∈ val c' := by
  have h0 : (ffExec x).Admits A ∅ := OmExec.ff_admits ∅
  have hF : (ffExec x).Admits A c'.procsᶜ := h0.mono (empty_subset _)
  have hFc : c'.procsᶜ.card ≤ t := by
    rw [card_compl]; unfold IsInputConfig at hc'; have := c'.procs.card_le_univ; omega
  obtain ⟨p', hp'⟩ : c'.procs.Nonempty := by
    rw [← card_pos]; unfold IsInputConfig at hc'; omega
  have hp'F : p' ∉ c'.procsᶜ := by rw [mem_compl, not_not]; exact hp'
  obtain ⟨w, hw⟩ := hS.termination _ _ hF hFc p' hp'F
  obtain rfl : w = v := hS.agreement _ ∅ h0 (by simp) p' (by simp) p (by simp) w v hw hv
  have := hS.validity _ _ hF hFc p' hp'F w hw
  convert this using 2
  funext q
  simp only [OmExec.conf, mem_compl, Config.mem_procs_iff_ne_none, not_not]
  split_ifs with hq
  · exact hq
  · exact (hcont q hq).symm

/-- **Theorem 3** of [AllBAExpensive], omission model: any algorithm solving a non-trivial
agreement problem in the synchronous omission model with `t < n` has an execution in which
correct processes send at least `t² / 32` messages. -/
theorem message_lower_bound_om [Nonempty VI] (hS : OmSolves t A val) (hnt : ¬ val.Trivial t)
    (htn : t < Fintype.card P) :
    ∃ (E : OmExec P VI) (F : Finset P), E.Admits A F ∧ F.card ≤ t ∧
      ∃ N, t ^ 2 ≤ 32 * E.msgsUpTo A F N := by
  classical
  obtain ⟨p⟩ : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  set d : VI := Classical.arbitrary VI
  have hadm : ∀ x : P → VI, (ffExec x).Admits A ∅ := fun _ => OmExec.ff_admits ∅
  obtain ⟨v₀, h₀⟩ := hS.termination (ffExec fun _ => d) ∅ (hadm _) (by simp) p (by simp)
  obtain ⟨c, hc, hv₀⟩ : ∃ c, IsInputConfig t c ∧ v₀ ∉ val c := by
    by_contra h; push Not at h; exact hnt ⟨v₀, h⟩
  set x₁ : P → VI := fun q => (c q).getD d
  obtain ⟨v₁, h₁⟩ := hS.termination (ffExec x₁) ∅ (hadm _) (by simp) p (by simp)
  have hv₁ : v₁ ∈ val c := ff_mem_val hS htn h₁ hc fun q hq => by
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hq
    simp [x₁, hw]
  exact omission_lower_bound_sq hS htn (fun h => hv₀ (by rw [h]; exact hv₁)) h₀ h₁

/-- **Theorems 1 and 3** of [AllBAExpensive] (authenticated model, which contains the
unauthenticated one): any algorithm solving a non-trivial Byzantine agreement problem in
synchrony with `t < n` has a synchronous execution in which correct processes send at least
`t² / 32` messages (within a finite time `N`). -/
theorem message_lower_bound_auth [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A val) (hnt : ¬ val.Trivial t)
    (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      ∃ N, t ^ 2 ≤ 32 * R.msgsUpTo A N := by
  obtain ⟨E, F, h1, h2, N, hN⟩ := message_lower_bound_om (hA.omSolves hU) hnt htn
  exact ⟨E.toRun A F, OmExec.toRun_valid h2 δ, OmExec.toRun_authValid hU h1, rfl, N,
    by rwa [OmExec.toRun_msgsUpTo h1]⟩

/-- **Theorems 1 and 3** of [AllBAExpensive], unauthenticated model. -/
theorem message_lower_bound [Nonempty VI] (hA : SolvesConsensusSync t δ A val)
    (hnt : ¬ val.Trivial t) (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.gst = 0 ∧ ∃ N, t ^ 2 ≤ 32 * R.msgsUpTo A N := by
  obtain ⟨R, h1, -, h2⟩ := message_lower_bound_auth A.unforging_none hA hnt htn
  exact ⟨R, h1, h2⟩

/-- **Theorem 3**, message-complexity form: some synchronous execution has message complexity
(messages sent by correct processes during the whole execution, as a supremum in `ℕ∞`) at least
`t² / 32`. -/
theorem message_complexity_lower_bound_auth [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A val) (hnt : ¬ val.Trivial t)
    (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      ((t ^ 2 : ℕ) : ℕ∞) ≤ 32 * R.msgComplexity A := by
  obtain ⟨R, h1, h2, h3, N, hN⟩ := message_lower_bound_auth hU hA hnt htn
  refine ⟨R, h1, h2, h3, le_trans
    (by exact_mod_cast hN : ((t ^ 2 : ℕ) : ℕ∞) ≤ 32 * (R.msgsUpTo A N : ℕ∞)) ?_⟩
  exact mul_le_mul_right (le_iSup (fun N => (R.msgsUpTo A N : ℕ∞)) N) _

/-- **Theorem 2** of [AllBAExpensive]: any (binary) weak consensus algorithm (synchronous,
Byzantine, with or without signatures) has an execution with at least `t² / 32` messages. -/
theorem weak_consensus_lower_bound_auth {A : Algorithm P M S Bool Bool} (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A (weakValidity P Bool)) (htn : t < Fintype.card P) :
    ∃ R : Run P M Bool, R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      ∃ N, t ^ 2 ≤ 32 * R.msgsUpTo A N := by
  obtain ⟨E, F, h1, h2, N, hN⟩ := weak_consensus_lower_bound_om (hA.omSolves hU) htn
  exact ⟨E.toRun A F, OmExec.toRun_valid h2 δ, OmExec.toRun_authValid hU h1, rfl, N,
    by rwa [OmExec.toRun_msgsUpTo h1]⟩

/-- **Theorem 2**, unauthenticated model. -/
theorem weak_consensus_lower_bound {A : Algorithm P M S Bool Bool}
    (hA : SolvesConsensusSync t δ A (weakValidity P Bool)) (htn : t < Fintype.card P) :
    ∃ R : Run P M Bool, R.Valid t δ ∧ R.gst = 0 ∧ ∃ N, t ^ 2 ≤ 32 * R.msgsUpTo A N := by
  obtain ⟨R, h1, -, h2⟩ := weak_consensus_lower_bound_auth A.unforging_none hA htn
  exact ⟨R, h1, h2⟩

/-! ### Corollary 1 (External Validity) -/

/-- The lock-step fault-free synchronous run with inputs `x`. -/
abbrev ffRun (M : Type*) (x : P → VI) : Run P M VI := Run.quiet ∅ x

omit [Fintype P] [DecidableEq P] in
theorem ffRun_valid (M : Type*) (x : P → VI) : (ffRun M x).Valid t δ :=
  Run.quiet_valid (by simp) δ

/-- **Corollary 1** of [AllBAExpensive] (External Validity, or any validity property): if an
algorithm solving Byzantine agreement in synchrony has two fault-free (lock-step) executions
deciding different values, then it has an execution with at least `t² / 32` messages. -/
theorem external_validity_lower_bound_auth (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A val) (htn : t < Fintype.card P)
    {x₀ x₁ : P → VI} {p₀ p₁ : P} {v₀ v₁ : VO} (hne : v₀ ≠ v₁)
    (h₀ : (ffRun M x₀).Decides A p₀ v₀) (h₁ : (ffRun M x₁).Decides A p₁ v₁) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      ∃ N, t ^ 2 ≤ 32 * R.msgsUpTo A N := by
  obtain ⟨E, F, h1, h2, N, hN⟩ := omission_lower_bound_sq (hA.omSolves hU) htn hne
    (Run.quiet_empty_decides_iff.mp h₀) (Run.quiet_empty_decides_iff.mp h₁)
  exact ⟨E.toRun A F, OmExec.toRun_valid h2 δ, OmExec.toRun_authValid hU h1, rfl, N,
    by rwa [OmExec.toRun_msgsUpTo h1]⟩

/-- **Corollary 1**, unauthenticated model. -/
theorem external_validity_lower_bound (hA : SolvesConsensusSync t δ A val)
    (htn : t < Fintype.card P) {x₀ x₁ : P → VI} {p₀ p₁ : P} {v₀ v₁ : VO} (hne : v₀ ≠ v₁)
    (h₀ : (ffRun M x₀).Decides A p₀ v₀) (h₁ : (ffRun M x₁).Decides A p₁ v₁) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.gst = 0 ∧ ∃ N, t ^ 2 ≤ 32 * R.msgsUpTo A N := by
  obtain ⟨R, h1, -, h2⟩ := external_validity_lower_bound_auth A.unforging_none hA htn hne h₀ h₁
  exact ⟨R, h1, h2⟩

end AllBAExpensive
