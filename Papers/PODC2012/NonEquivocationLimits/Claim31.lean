import Papers.PODC2012.NonEquivocationLimits.Basic

/-!
# Claim 3.1: non-equivocation without transferable authentication does not help

**Claim 3.1.** In an asynchronous system with `n < 3f + 1` processes, at most `f` Byzantine, where
processes have no transferable authentication and faulty processes cannot equivocate, there is
no r-broadcast protocol.

We prove it (for `n ≥ 3`, see `SmallCases.lean` for `n ≤ 2`) against the weakest adversary we
could think of: every faulty process *imitates* a correct process of another run
(`Imitating`), so it never equivocates if the protocol does not (`claim_3_1`), and it never
needs anybody else's authentication: links are authenticated point to point, and nothing in the
model lets a receiver check a relayed statement (no transferable authentication). The admissible
runs are even partially synchronous (`Run.Valid f δ` for any `δ`), which only strengthens the
result; the asynchronous versions follow (`claim_3_1_async`).

## The four runs (groups `A = g⁻¹ 0 ∋ s`, `B = g⁻¹ 1`, `C = g⁻¹ 2`, each of size `≤ f`)

1. `run1`: `C` silent (crashed), sender input `m'`, synchronous: `A ∪ B` deliver `m'`; all of `B`
   by time `T₁`.
2. `run2 T₁`: `A` faulty, sends to `B` exactly what it sent in run 1 up to `T₁`, then nothing;
   `B ↔ C` messages sent before `T₁ + 1` arrive at `T₁ + 1`. `B` cannot distinguish it from run 1
   up to `T₁ + 1`, delivers `m'`, so `C` delivers `m'` (L2, S2), by time `T₂`.
3. `run3 T₁ H` (`H > T₁, T₂`): no faults, input `m'`; `B ↔ C` as in run 2, `A ↔ C` messages and
   `A → B` messages sent after `T₁` arrive at time `H`. `A ∪ B` see run 1 up to `T₁ + 1`, hence
   `B ∪ C` see run 2 up to `H`: `C` delivers `m'` by `T₂`.
4. `run4 T₁ H`: sender input `m`, `B` faulty and imitates run 3 *exactly*, same delays as run 3.
   `C` sees run 3 up to `H` and delivers `m'`; the correct sender delivers `m` (L1):
   Agreement fails.

**Repair of the paper's proof.** In the paper's Run 3, messages between `A` and `B` are "delivered
in a timely fashion" throughout; then `B` hears from the (now correct, not crashed) processes of
`A` after time `t`, and need not behave as in Run 2, so `C` need not deliver `m'`. We delay the
messages `A → B` sent after `T₁` (as the paper does for the other slow links).
-/

set_option linter.unusedSectionVars false

namespace Podc.NonEquivocationLimits

open Cslib.Byzantine.PartialSync Finset

variable {P M S V κ : Type*} [DecidableEq P]

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i; decide

namespace Claim31

section runs

variable [Fintype P] (A : Algorithm P M S V V) (g : P → Fin 3) (m m' : V)

/-- Run 1: group `C` is silent from the start, the sender broadcasts `m'`, all links are
immediate. -/
def run1 : Run P M V where
  faulty := univ.filter (g · = 2)
  inp _ := m'
  gst := 0
  byz _ _ _ := []
  dl _ τ _ := τ

/-- Run 2: `A` is faulty, imitates run 1 towards `B` up to `T₁` and is silent otherwise;
`B ↔ C` batches sent before `T₁ + 1` are delivered at `T₁ + 1`. -/
def run2 (T₁ : ℕ) : Run P M V where
  faulty := univ.filter (g · = 0)
  inp _ := m'
  gst := T₁ + 1
  byz q τ p := if g p = 1 ∧ τ ≤ T₁ then (run1 g m').out A q τ p else []
  dl q τ p := if (g q = 1 ∧ g p = 2) ∨ (g q = 2 ∧ g p = 1) then max τ (T₁ + 1) else τ

/-- Delays of runs 3 and 4: `B ↔ C` as in run 2; `A ↔ C` and `A → B` after `T₁` delayed until
`H`; everything else immediate. -/
def dl34 (T₁ H : ℕ) (q : P) (τ : ℕ) (p : P) : ℕ :=
  if (g q = 1 ∧ g p = 2) ∨ (g q = 2 ∧ g p = 1) then max τ (T₁ + 1)
  else if (g q = 0 ∧ g p = 2) ∨ (g q = 2 ∧ g p = 0) ∨ (g q = 0 ∧ g p = 1 ∧ T₁ < τ) then max τ H
  else τ

/-- Run 3: no faults, sender input `m'`, delays `dl34`. -/
def run3 (T₁ H : ℕ) : Run P M V where
  faulty := ∅
  inp _ := m'
  gst := H
  byz _ _ _ := []
  dl := dl34 g T₁ H

/-- Run 4: sender input `m`, `B` faulty and replaying run 3 exactly, delays `dl34`. -/
def run4 (s : P) (T₁ H : ℕ) : Run P M V where
  faulty := univ.filter (g · = 1)
  inp p := if p = s then m else m'
  gst := H
  byz := (run3 g m' T₁ H).out A
  dl := dl34 g T₁ H

end runs

section fields

variable [Fintype P] {A : Algorithm P M S V V} {g : P → Fin 3} {m m' : V} {s : P} {T₁ H : ℕ}
  {q p : P} {τ : ℕ}

@[simp] theorem mem_run1_faulty : q ∈ (run1 (M := M) g m').faulty ↔ g q = 2 := by simp [run1]
@[simp] theorem run1_inp : (run1 (M := M) g m').inp p = m' := rfl
@[simp] theorem run1_byz : (run1 (M := M) g m').byz q τ p = [] := rfl
@[simp] theorem run1_dl : (run1 (M := M) g m').dl q τ p = τ := rfl
@[simp] theorem mem_run2_faulty : q ∈ (run2 A g m' T₁).faulty ↔ g q = 0 := by simp [run2]
@[simp] theorem run2_inp : (run2 A g m' T₁).inp p = m' := rfl
theorem run2_byz : (run2 A g m' T₁).byz q τ p =
    if g p = 1 ∧ τ ≤ T₁ then (run1 g m').out A q τ p else [] := rfl
theorem run2_dl : (run2 A g m' T₁).dl q τ p =
    if (g q = 1 ∧ g p = 2) ∨ (g q = 2 ∧ g p = 1) then max τ (T₁ + 1) else τ := rfl
@[simp] theorem not_mem_run3_faulty : q ∉ (run3 (M := M) g m' T₁ H).faulty := by simp [run3]
@[simp] theorem run3_inp : (run3 (M := M) g m' T₁ H).inp p = m' := rfl
@[simp] theorem run3_dl : (run3 (M := M) g m' T₁ H).dl = dl34 g T₁ H := rfl
@[simp] theorem mem_run4_faulty : q ∈ (run4 A g m m' s T₁ H).faulty ↔ g q = 1 := by simp [run4]
@[simp] theorem run4_inp : (run4 A g m m' s T₁ H).inp p = if p = s then m else m' := rfl
@[simp] theorem run4_byz : (run4 A g m m' s T₁ H).byz = (run3 g m' T₁ H).out A := rfl
@[simp] theorem run4_dl : (run4 A g m m' s T₁ H).dl = dl34 g T₁ H := rfl

end fields

variable [Fintype P] {A : Algorithm P M S V V} {g : P → Fin 3} {m m' : V}

/-! ### Validity of the runs -/

theorem run1_valid {f δ : ℕ} (hC : #{p | g p = 2} ≤ f) : (run1 (M := M) g m').Valid f δ :=
  ⟨hC, fun _ _ _ _ _ => le_rfl, fun _ τ _ _ _ => by simp [run1]⟩

theorem run2_valid {f δ : ℕ} (hA : #{p | g p = 0} ≤ f) (T₁ : ℕ) :
    (run2 A g m' T₁).Valid f δ := by
  refine ⟨hA, fun q τ p _ _ => ?_, fun q τ p _ _ => ?_⟩ <;> simp only [run2] <;> split_ifs <;>
    omega

theorem dl34_ge (T₁ H : ℕ) (q : P) (τ : ℕ) (p : P) : τ ≤ dl34 g T₁ H q τ p := by
  unfold dl34; split_ifs <;> omega

theorem dl34_le {T₁ H : ℕ} (hH : T₁ < H) (q : P) (τ : ℕ) (p : P) :
    dl34 g T₁ H q τ p ≤ max τ H := by
  unfold dl34; split_ifs <;> omega

theorem run3_valid {f δ : ℕ} {T₁ H : ℕ} (hH : T₁ < H) : (run3 (M := M) g m' T₁ H).Valid f δ :=
  ⟨by simp [run3], fun q τ p _ _ => dl34_ge T₁ H q τ p,
    fun q τ p _ _ => (dl34_le hH q τ p).trans (by simp [run3])⟩

theorem run4_valid {f δ : ℕ} (hB : #{p | g p = 1} ≤ f) (s : P) {T₁ H : ℕ} (hH : T₁ < H) :
    (run4 A g m m' s T₁ H).Valid f δ :=
  ⟨hB, fun q τ p _ _ => dl34_ge T₁ H q τ p,
    fun q τ p _ _ => (dl34_le hH q τ p).trans (by simp [run4])⟩

/-! ### The adversaries imitate correct processes -/

/-- A failure-free reference run (any data). -/
def refRun (m' : V) : Run P M V := ⟨∅, fun _ => m', 0, fun _ _ _ => [], fun _ τ _ => τ⟩

theorem run1_imitating : Imitating A (run1 (M := M) g m') :=
  fun _ _ => ⟨refRun m', by simp [refRun], fun _ _ => Or.inl rfl⟩

theorem run2_imitating (T₁ : ℕ) : Imitating A (run2 A g m' T₁) := by
  intro q hq
  refine ⟨run1 g m', by simp_all [run1, run2], fun τ p => ?_⟩
  simp only [run2]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem run4_imitating (s : P) (T₁ H : ℕ) : Imitating A (run4 A g m m' s T₁ H) :=
  fun _ _ => ⟨run3 g m' T₁ H, by simp [run3], fun _ _ => Or.inr rfl⟩

/-! ### Indistinguishability -/

/-- `B` cannot distinguish run 2 from run 1 up to time `T₁ + 1`. -/
theorem run2_st (T₁ : ℕ) :
    ∀ τ ≤ T₁ + 1, ∀ p, g p = 1 → (run2 A g m' T₁).st A τ p = (run1 g m').st A τ p := by
  intro τ hτ p hp
  refine Run.st_eq_of_inbox_eq (R := run2 A g m' T₁) A (ref := fun _ => run1 g m')
    (X := {p | g p = 1}) (T := T₁ + 1) (fun _ _ => rfl) ?_ τ hτ p hp
  intro τ hτ hst p hp
  apply Run.inbox_eq_of_dlv_eq
  intro q σ hσ
  simp only [Set.mem_ofPred_eq] at hp hst
  rcases fin3_cases (g q) with hq | hq | hq
  · -- `q ∈ A`: faulty in run 2, replays run 1
    have h2 : q ∈ (run2 A g m' T₁).faulty := by simp [hq]
    simp only [Run.dlv, Run.out_of_faulty A _ h2, run2_byz, run2_dl, run1_dl]
    simp only [hq, hp, show σ ≤ T₁ by omega, and_self, ite_true]
    rfl
  · -- `q ∈ B`: correct in both
    have h2 : q ∉ (run2 A g m' T₁).faulty := by simp [hq]
    have h1 : q ∉ (run1 (M := M) g m').faulty := by simp [hq]
    simp only [Run.dlv, Run.out_of_correct A _ h2, Run.out_of_correct A _ h1,
      hst q hq σ (by omega), run2_dl, run1_dl]
    simp [hq, hp]
  · -- `q ∈ C`: silent in run 1, delayed in run 2
    have h1 : q ∈ (run1 (M := M) g m').faulty := by simp [hq]
    rw [Run.dlv_eq_nil_of_ne _ _ (by simp [run2_dl, hq, hp]; omega)]
    simp [Run.dlv, Run.out_of_faulty A _ h1]

/-- `A ∪ B` cannot distinguish run 3 from run 1 up to time `T₁ + 1`. -/
theorem run3_st_run1 {T₁ H : ℕ} (hH : T₁ < H) :
    ∀ τ ≤ T₁ + 1, ∀ p, g p ≠ 2 → (run3 g m' T₁ H).st A τ p = (run1 g m').st A τ p := by
  intro τ hτ p hp
  refine Run.st_eq_of_inbox_eq (R := run3 g m' T₁ H) A (ref := fun _ => run1 g m')
    (X := {p | g p ≠ 2}) (T := T₁ + 1) (fun _ _ => rfl) ?_ τ hτ p hp
  intro τ hτ hst p hp
  apply Run.inbox_eq_of_dlv_eq
  intro q σ hσ
  simp only [Set.mem_ofPred_eq] at hp hst
  by_cases hq : g q = 2
  · have h1 : q ∈ (run1 (M := M) g m').faulty := by simp [hq]
    rw [Run.dlv_eq_nil_of_ne _ _ ?_]
    · simp [Run.dlv, Run.out_of_faulty A _ h1]
    · rcases fin3_cases (g p) with hp' | hp' | hp' <;>
        simp [dl34, hq, hp'] <;> omega
  · have h1 : q ∉ (run1 (M := M) g m').faulty := by simp [hq]
    simp only [Run.dlv, Run.out_of_correct A _ not_mem_run3_faulty,
      Run.out_of_correct A _ h1, hst q hq σ (by omega), run1_dl]
    have : (run3 (M := M) g m' T₁ H).dl q σ p = σ := by
      simp only [run3_dl, dl34]
      rcases fin3_cases (g q) with hq' | hq' | hq' <;>
        rcases fin3_cases (g p) with hp' | hp' | hp' <;> (simp_all; try omega)
    rw [this]

/-- `B ∪ C` cannot distinguish run 3 from run 2 up to time `H`. -/
theorem run3_st_run2 {T₁ H : ℕ} (hH : T₁ < H) :
    ∀ τ ≤ H, ∀ p, g p ≠ 0 → (run3 g m' T₁ H).st A τ p = (run2 A g m' T₁).st A τ p := by
  intro τ hτ p hp
  refine Run.st_eq_of_inbox_eq (R := run3 g m' T₁ H) A (ref := fun _ => run2 A g m' T₁)
    (X := {p | g p ≠ 0}) (T := H) (fun _ _ => rfl) ?_ τ hτ p hp
  intro τ hτ hst p hp
  apply Run.inbox_eq_of_dlv_eq
  intro q σ hσ
  simp only [Set.mem_ofPred_eq] at hp hst
  by_cases hq : g q = 0
  · have h2 : q ∈ (run2 A g m' T₁).faulty := by simp [hq]
    have h1 : q ∉ (run1 (M := M) g m').faulty := by simp [hq]
    by_cases hpb : g p = 1 ∧ σ ≤ T₁
    · -- replayed batch, delivered immediately in both runs
      simp only [Run.dlv, Run.out_of_correct A _ not_mem_run3_faulty, Run.out_of_faulty A _ h2,
        run3_st_run1 (A := A) (g := g) hH σ (by omega) q (by simp [hq]), run2_byz, run2_dl, run3_dl,
        Run.out_of_correct A _ h1]
      simp [dl34, hq, hpb.1, hpb.2, not_lt.mpr hpb.2]
    · -- not delivered before `H` in run 3, nothing sent in run 2
      rw [Run.dlv_eq_nil_of_ne _ _ ?_]
      · simp [Run.dlv, Run.out_of_faulty A _ h2, run2_byz, hpb]
      · rcases fin3_cases (g p) with hp' | hp' | hp'
        · exact absurd hp' hp
        · have : T₁ < σ := by simp [hp'] at hpb; omega
          simp [dl34, hq, hp', this]; omega
        · simp [dl34, hq, hp']; omega
  · have h2 : q ∉ (run2 A g m' T₁).faulty := by simp [hq]
    simp only [Run.dlv, Run.out_of_correct A _ not_mem_run3_faulty, Run.out_of_correct A _ h2,
      hst q hq σ (by omega)]
    have : (run3 (M := M) g m' T₁ H).dl q σ p = (run2 A g m' T₁).dl q σ p := by
      simp only [run3_dl, run2_dl, dl34]
      rcases fin3_cases (g q) with hq' | hq' | hq' <;>
        rcases fin3_cases (g p) with hp' | hp' | hp' <;> simp_all
    rw [this]

/-- `C` cannot distinguish run 4 from run 3 up to time `H`. -/
theorem run4_st {s : P} (hs : g s = 0) {T₁ H : ℕ} :
    ∀ τ ≤ H, ∀ p, g p = 2 → (run4 A g m m' s T₁ H).st A τ p = (run3 g m' T₁ H).st A τ p := by
  intro τ hτ p hp
  refine Run.st_eq_of_inbox_eq (R := run4 A g m m' s T₁ H) A (ref := fun _ => run3 g m' T₁ H)
    (X := {p | g p = 2}) (T := H) (fun p hp => ?_) ?_ τ hτ p hp
  · have : p ≠ s := by rintro rfl; simp_all
    simp [this]
  intro τ hτ hst p hp
  apply Run.inbox_eq_of_dlv_eq
  intro q σ hσ
  simp only [Set.mem_ofPred_eq] at hp hst
  rcases fin3_cases (g q) with hq | hq | hq
  · -- `A → C` is delayed until `H` in both runs
    rw [Run.dlv_eq_nil_of_ne _ _ (by simp [dl34, hq, hp]; omega),
      Run.dlv_eq_nil_of_ne _ _ (by simp [dl34, hq, hp]; omega)]
  · have h4 : q ∈ (run4 A g m m' s T₁ H).faulty := by simp [hq]
    simp only [Run.dlv, Run.out_of_faulty A _ h4, run4_byz, run4_dl, run3_dl]
    rfl
  · have h4 : q ∉ (run4 A g m m' s T₁ H).faulty := by simp [hq]
    simp only [Run.dlv, Run.out_of_correct A _ not_mem_run3_faulty, Run.out_of_correct A _ h4,
      hst q hq σ (by omega), run4_dl, run3_dl]

/-! ### The contradiction -/

/-- The four-run argument, for any class of admissible runs containing the four runs. -/
theorem not_isRBroadcast_of_mem {s : P} (hs : g s = 0) (hne : ∀ i, ∃ p, g p = i)
    (hmm : m ≠ m') {Adm : Set (Run P M V)} (h1 : run1 g m' ∈ Adm)
    (h2 : ∀ T₁, run2 A g m' T₁ ∈ Adm)
    (h4 : ∀ T₁ H, T₁ < H → run4 A g m m' s T₁ H ∈ Adm) : ¬ IsRBroadcast A s Adm := by
  intro hRB
  -- Run 1: `B` delivers `m'` by `T₁`
  have hs1 : s ∉ (run1 (M := M) g m').faulty := by simp [run1, hs]
  obtain ⟨T₁, hT₁⟩ := exists_deadline (A := A) (R := run1 g m') (fun p => g p = 1)
    (v := m') fun p hp => hRB.all_decide_inp h1 hs1 p (by simp [run1, hp])
  -- Run 2: `B` delivers `m'`, hence `C` delivers `m'` by `T₂`
  obtain ⟨b, hb⟩ := hne 1
  have hb2 : (run2 A g m' T₁).Decides A b m' := by
    obtain ⟨τ, hτ, h⟩ := hT₁ b hb
    exact ⟨τ, by rw [run2_st T₁ τ (by omega) b hb]; exact h⟩
  obtain ⟨T₂, hT₂⟩ := exists_deadline (A := A) (R := run2 A g m' T₁) (fun p => g p = 2)
    (v := m') fun p hp =>
      hRB.all_decide (h2 T₁) (by simp [run2, hb]) hb2 p (by simp [run2, hp])
  -- Run 3 and run 4: `C` delivers `m'`
  set H := T₁ + T₂ + 1
  obtain ⟨c, hc⟩ := hne 2
  have hc4 : (run4 A g m m' s T₁ H).Decides A c m' := by
    obtain ⟨τ, hτ, h⟩ := hT₂ c hc
    refine ⟨τ, ?_⟩
    rw [run4_st hs τ (by omega) c hc, run3_st_run2 (by omega) τ (by omega) c (by simp [hc])]
    exact h
  -- the correct sender delivers `m` in run 4
  have hs4 : s ∉ (run4 A g m m' s T₁ H).faulty := by simp [run4, hs]
  have hsd := hRB.senderTermination _ (h4 T₁ H (by omega)) hs4
  have := hRB.agreement _ (h4 T₁ H (by omega)) s hs4 c (by simp [run4, hc]) _ _ hsd hc4
  simp [run4] at this
  exact hmm this

/-- **Claim 3.1** (imitating adversary): if `3 ≤ n ≤ 3f`, no algorithm solves r-broadcast in the
(partially synchronous, hence also the asynchronous) model in which every faulty process imitates
a correct process of another run. -/
theorem claim_3_1_imitating [Nontrivial V] {f : ℕ} (h3 : 3 ≤ Fintype.card P)
    (hf : Fintype.card P ≤ 3 * f) (δ : ℕ) (A : Algorithm P M S V V) (s : P) :
    ¬ IsRBroadcast A s {R | R.Valid f δ ∧ Imitating A R} := by
  obtain ⟨g, hs, hne, hc⟩ := exists_three_groups (f := f) s h3 hf
  obtain ⟨m, m', hmm⟩ := exists_pair_ne V
  exact not_isRBroadcast_of_mem (A := A) (m := m) hs hne hmm ⟨run1_valid (hc 2), run1_imitating⟩
    (fun T₁ => ⟨run2_valid (hc 0) T₁, run2_imitating T₁⟩)
    (fun T₁ H hH => ⟨run4_valid (hc 1) s hH, run4_imitating s T₁ H⟩)

/-- **Claim 3.1.** Let `3 ≤ n ≤ 3f` and let `key : M → κ` be any key map of the
non-equivocation primitive. No algorithm that uses the primitive as intended (correct processes
never equivocate) solves r-broadcast when at most `f` processes are Byzantine but cannot
equivocate (and there is no transferable authentication). Stated for partially synchronous runs
with any delay bound `δ`; see `claim_3_1_async` for the asynchronous model of the paper. -/
theorem claim_3_1 [Nontrivial V] {f : ℕ} (h3 : 3 ≤ Fintype.card P) (hf : Fintype.card P ≤ 3 * f)
    (δ : ℕ) (key : M → κ) (A : Algorithm P M S V V) (hA : RespectsNE A key) (s : P) :
    ¬ IsRBroadcast A s {R | R.Valid f δ ∧ NonEquivocating key R} := fun h =>
  claim_3_1_imitating h3 hf δ A s
    (h.mono fun _ hR => ⟨hR.1, Imitating.nonEquivocating hA hR.2⟩)

/-- **Claim 3.1**, asynchronous version (the model of the paper: any finite delays). -/
theorem claim_3_1_async [Nontrivial V] {f : ℕ} (h3 : 3 ≤ Fintype.card P)
    (hf : Fintype.card P ≤ 3 * f) (key : M → κ) (A : Algorithm P M S V V)
    (hA : RespectsNE A key) (s : P) :
    ¬ IsRBroadcast A s {R | R.AsyncValid f ∧ NonEquivocating key R} := fun h =>
  claim_3_1 h3 hf 0 key A hA s (h.mono fun _ hR => ⟨hR.1.asyncValid, hR.2⟩)

end Claim31

end Podc.NonEquivocationLimits
