import Papers.PODC2012.NonEquivocationLimits.Claim31

/-!
# Claim 3.2: transferable authentication without non-equivocation does not help

**Claim 3.2.** In an asynchronous system with `n < 3f + 1` processes, at most `f` Byzantine,
where processes have transferable authentication (signatures) but faulty processes can
equivocate, there is no r-broadcast protocol.

Signatures are CSLib's abstract unforgeable tokens (`Cslib.Byzantine.Auth`): the algorithm is
`Unforging` (correct processes only emit their own or received tokens) and the adversary is
`AuthValid` (Byzantine messages only carry Byzantine-signed tokens or tokens already emitted by
correct processes). Proof for `n ≥ 3` (for `n ≤ 2` see `SmallCases.lean`), groups
`A = g⁻¹ 0 ∋ s`, `B = g⁻¹ 1`, `C = g⁻¹ 2`:

1. `run1`: `B` silent, sender input `m`: `C` delivers `m` by `T₁`.
2. `run2`: `C` silent, sender input `m'`: `B` delivers `m'` by `T₂`.
3. `run3 H` (`H > T₁, T₂`): `A` faulty, plays run 1 towards `C` and run 2 towards `B` before `H`;
   `B ↔ C` delayed until `H`. `C` sees run 1 and delivers `m`, `B` sees run 2 and delivers `m'`.

This is the paper's proof; it goes through as written.
-/

set_option linter.unusedSectionVars false

namespace Podc.NonEquivocationLimits

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P]

namespace Claim32

section runs

variable [Fintype P] (A : Algorithm P M S V V) (g : P → Fin 3) (m m' : V)

/-- Run 1 (and run 2): group `j` silent from the start, every process has input `v`,
synchronous. -/
def silentRun (j : Fin 3) (v : V) : Run P M V where
  faulty := univ.filter (g · = j)
  inp _ := v
  gst := 0
  byz _ _ _ := []
  dl _ τ _ := τ

/-- Run 3: `A` faulty and playing `silentRun 1 m` towards `C`, `silentRun 2 m'` towards `B`
before `H`; `B ↔ C` delayed until `H`. -/
def run3 (H : ℕ) : Run P M V where
  faulty := univ.filter (g · = 0)
  inp p := if g p = 1 then m' else m
  gst := H
  byz q τ p := if τ < H then
      (if g p = 2 then (silentRun g 1 m).out A q τ p
       else if g p = 1 then (silentRun g 2 m').out A q τ p else [])
    else []
  dl q τ p := if (g q = 1 ∧ g p = 2) ∨ (g q = 2 ∧ g p = 1) then max τ H else τ

end runs

variable [Fintype P] {A : Algorithm P M S V V} {g : P → Fin 3} {m m' : V} {H : ℕ} {q p : P}
  {τ : ℕ} {j : Fin 3} {v : V}

@[simp] theorem mem_silentRun_faulty : q ∈ (silentRun (M := M) g j v).faulty ↔ g q = j := by
  simp [silentRun]
@[simp] theorem silentRun_inp : (silentRun (M := M) g j v).inp p = v := rfl
@[simp] theorem silentRun_byz : (silentRun (M := M) g j v).byz q τ p = [] := rfl
@[simp] theorem silentRun_dl : (silentRun (M := M) g j v).dl q τ p = τ := rfl
@[simp] theorem mem_run3_faulty : q ∈ (run3 A g m m' H).faulty ↔ g q = 0 := by simp [run3]
@[simp] theorem run3_inp : (run3 A g m m' H).inp p = if g p = 1 then m' else m := rfl
theorem run3_byz : (run3 A g m m' H).byz q τ p = if τ < H then
      (if g p = 2 then (silentRun g 1 m).out A q τ p
       else if g p = 1 then (silentRun g 2 m').out A q τ p else [])
    else [] := rfl
theorem run3_dl : (run3 A g m m' H).dl q τ p =
    if (g q = 1 ∧ g p = 2) ∨ (g q = 2 ∧ g p = 1) then max τ H else τ := rfl

theorem silentRun_valid {f δ : ℕ} (hj : #{p | g p = j} ≤ f) :
    (silentRun (M := M) g j v).Valid f δ :=
  ⟨hj, fun _ _ _ _ _ => le_rfl, fun _ τ _ _ _ => by simp [silentRun]⟩

theorem run3_valid {f δ : ℕ} (hA : #{p | g p = 0} ≤ f) :
    (run3 A g m m' H).Valid f δ := by
  refine ⟨hA, fun q τ p _ _ => ?_, fun q τ p _ _ => ?_⟩ <;> simp only [run3] <;> split_ifs <;>
    omega

/-- In run 3, the processes of group `j ∈ {1, 2}` cannot distinguish run 3 from the run in which
the *other* group `k` is silent (with the input `v` of group `j`), up to time `H`. -/
theorem run3_st {j k : Fin 3} {v : V} (hjk : (j = 2 ∧ k = 1 ∧ v = m) ∨ (j = 1 ∧ k = 2 ∧ v = m')) :
    ∀ τ ≤ H, ∀ p, g p = j → (run3 A g m m' H).st A τ p = (silentRun g k v).st A τ p := by
  intro τ hτ p hp
  refine Run.st_eq_of_inbox_eq (R := run3 A g m m' H) A (ref := fun _ => silentRun g k v)
    (X := {p | g p = j}) (T := H) (fun p hp => ?_) ?_ τ hτ p hp
  · simp only [Set.mem_ofPred_eq] at hp
    rcases hjk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [hp]
  intro τ hτ hst p hp
  apply Run.inbox_eq_of_dlv_eq
  intro q σ hσ
  simp only [Set.mem_ofPred_eq] at hp hst
  rcases fin3_cases (g q) with hq | hq | hq
  · have h3 : q ∈ (run3 A g m m' H).faulty := by simp [hq]
    simp only [Run.dlv, Run.out_of_faulty A _ h3, run3_byz, run3_dl, silentRun_dl,
      show σ < H by omega, ite_true]
    rcases hjk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> (simp [hp, hq]; rfl)
  all_goals
    by_cases hk : g q = k
    · have h1 : q ∈ (silentRun (M := M) g k v).faulty := by simp [hk]
      rw [Run.dlv_eq_nil_of_ne _ _ ?_]
      · simp [Run.dlv, Run.out_of_faulty A _ h1]
      · rcases hjk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> (simp_all [run3_dl]; try omega)
    · have hj : g q = j := by
        rcases hjk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp_all
      have h3 : q ∉ (run3 A g m m' H).faulty := by simp [hq]
      have h1 : q ∉ (silentRun (M := M) g k v).faulty := by simp [hk]
      simp only [Run.dlv, Run.out_of_correct A _ h3, Run.out_of_correct A _ h1,
        hst q hj σ (by omega), silentRun_dl, run3_dl]
      rcases hjk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [hj, hp]

/-- Run 3 respects unforgeability: `A` only replays messages of runs in which it was correct,
and the correct processes behave as in those runs before `H`. -/
theorem run3_authValid {Au : Auth P M K} (hU : A.Unforging Au) :
    (run3 A g m m' H).AuthValid Au A := by
  intro b hb τ r hr x hx y hy
  simp only [mem_run3_faulty] at hb hr
  simp only [run3_byz] at hx
  split_ifs at hx with hτ hr2 hr1
  · refine Run.tokens_replay hU (Ri := silentRun g 1 m) (T := τ) (fun q σ r' hσ => ?_) τ le_rfl
      b r x hx y hy
    rcases fin3_cases (g q) with hq | hq | hq
    · exact Or.inr (Or.inl ⟨by simp [hq], by simp [hq]⟩)
    · exact Or.inr (Or.inr fun z hz => by
        simp [Run.out_of_faulty A _ (show q ∈ (silentRun (M := M) g 1 m).faulty by simp [hq])]
          at hz)
    · refine Or.inl ⟨by simp [hq], ?_⟩
      rw [Run.out_of_correct A _ (by simp [hq]), Run.out_of_correct A _ (by simp [hq]),
        run3_st (Or.inl ⟨rfl, rfl, rfl⟩) σ (by omega) q hq]
  · refine Run.tokens_replay hU (Ri := silentRun g 2 m') (T := τ) (fun q σ r' hσ => ?_) τ le_rfl
      b r x hx y hy
    rcases fin3_cases (g q) with hq | hq | hq
    · exact Or.inr (Or.inl ⟨by simp [hq], by simp [hq]⟩)
    · refine Or.inl ⟨by simp [hq], ?_⟩
      rw [Run.out_of_correct A _ (by simp [hq]), Run.out_of_correct A _ (by simp [hq]),
        run3_st (Or.inr ⟨rfl, rfl, rfl⟩) σ (by omega) q hq]
    · exact Or.inr (Or.inr fun z hz => by
        simp [Run.out_of_faulty A _ (show q ∈ (silentRun (M := M) g 2 m').faulty by simp [hq])]
          at hz)
  · rcases fin3_cases (g r) with h | h | h <;> simp_all
  · simp at hx

/-- **Claim 3.2.** Let `3 ≤ n ≤ 3f`. No unforging algorithm (signatures = transferable
authentication) solves r-broadcast when at most `f` processes are Byzantine and may equivocate.
Stated for partially synchronous runs with any delay bound `δ`; see `claim_3_2_async`. -/
theorem claim_3_2 [Nontrivial V] {f : ℕ} (h3 : 3 ≤ Fintype.card P) (hf : Fintype.card P ≤ 3 * f)
    (δ : ℕ) (Au : Auth P M K) (A : Algorithm P M S V V) (hU : A.Unforging Au) (s : P) :
    ¬ IsRBroadcast A s {R | R.Valid f δ ∧ R.AuthValid Au A} := by
  intro hRB
  obtain ⟨g, hs, hne, hc⟩ := exists_three_groups (f := f) s h3 hf
  obtain ⟨m, m', hmm⟩ := exists_pair_ne V
  have hmem : ∀ j (v : V), silentRun g j v ∈ {R | R.Valid f δ ∧ R.AuthValid Au A} :=
    fun j v => ⟨silentRun_valid (hc j), Run.authValid_of_canonical fun _ _ _ _ => rfl⟩
  -- Run 1: `C` delivers `m` by `T₁`; run 2: `B` delivers `m'` by `T₂`.
  obtain ⟨T₁, hT₁⟩ := exists_deadline (A := A) (R := silentRun g 1 m) (fun p => g p = 2) (v := m)
    fun p hp => hRB.all_decide_inp (hmem 1 m) (by simp [hs]) p (by simp [hp])
  obtain ⟨T₂, hT₂⟩ := exists_deadline (A := A) (R := silentRun g 2 m') (fun p => g p = 1)
    (v := m') fun p hp => hRB.all_decide_inp (hmem 2 m') (by simp [hs]) p (by simp [hp])
  -- Run 3
  set H := T₁ + T₂ + 1
  have h3m : run3 A g m m' H ∈ {R | R.Valid f δ ∧ R.AuthValid Au A} :=
    ⟨run3_valid (hc 0), run3_authValid hU⟩
  obtain ⟨c, hc2⟩ := hne 2
  obtain ⟨b, hb1⟩ := hne 1
  have hcd : (run3 A g m m' H).Decides A c m := by
    obtain ⟨τ, hτ, h⟩ := hT₁ c hc2
    exact ⟨τ, by rw [run3_st (Or.inl ⟨rfl, rfl, rfl⟩) τ (by omega) c hc2]; exact h⟩
  have hbd : (run3 A g m m' H).Decides A b m' := by
    obtain ⟨τ, hτ, h⟩ := hT₂ b hb1
    exact ⟨τ, by rw [run3_st (Or.inr ⟨rfl, rfl, rfl⟩) τ (by omega) b hb1]; exact h⟩
  exact hmm (hRB.agreement _ h3m c (by simp [hc2]) b (by simp [hb1]) m m' hcd hbd)

/-- **Claim 3.2**, asynchronous version (the model of the paper). -/
theorem claim_3_2_async [Nontrivial V] {f : ℕ} (h3 : 3 ≤ Fintype.card P)
    (hf : Fintype.card P ≤ 3 * f) (Au : Auth P M K) (A : Algorithm P M S V V)
    (hU : A.Unforging Au) (s : P) :
    ¬ IsRBroadcast A s {R | R.AsyncValid f ∧ R.AuthValid Au A} := fun h =>
  claim_3_2 h3 hf 0 Au A hU s (h.mono fun _ hR => ⟨hR.1.asyncValid, hR.2⟩)

end Claim32

end Podc.NonEquivocationLimits
