import Papers.PODC2022.HybridApproxAgreement.Spec
import Cslib.Foundations.Combinatorics.Labelling
import Cslib.Computability.Distributed.Byzantine.PartialSync.Merge

/-!
# Theorem 5.1: no hybrid AA when `2 tₛ + tₐ ≥ n`

The paper's split-brain argument. Partition the parties into `S₋`, `S₊` (non-empty, at most
`max tₛ tₐ` each) and `Sₐ` (at most `tₐ`).

* `R₁` (synchronous): `S₋` is Byzantine and silent, everybody else has input `x₁`. By termination and
  validity some `p ∈ S₊` outputs `x₁`, say by time `τ₁`.
* `R₂` (synchronous): `S₊` is Byzantine and silent, everybody else has input `x₀`. Some `q ∈ S₋`
  outputs `x₀` by time `τ₂`.
* `R₃` (asynchronous, `gst = T + 1`, `T = max τ₁ τ₂`; the library run `Run.merge` of `R₁` and `R₂`):
  `Sₐ` is Byzantine; towards `S₊` it replays its
  messages of `R₁`, towards `S₋` those of `R₂` (until `T`); messages between `S₊` and `S₋` are delayed
  past `T`. Then `S₊` cannot distinguish `R₃` from `R₁` and `S₋` cannot distinguish it from `R₂` up to
  `T`, so `p` outputs `x₁` and `q` outputs `x₀` in `R₃`, contradicting `ε`-agreement as
  `|x₁ - x₀| > ε`.

The replayed messages respect unforgeability (`Run.tokens_replay`): `Sₐ` is honest in `R₁`/`R₂`, `S₊`
behaves identically, and the silent parties emit nothing. So the impossibility holds **with
signatures (any PKI)**, as claimed.

If `tₐ > tₛ` the groups `S₋`, `S₊` may be larger than `tₛ`; then `R₁`, `R₂` are used as
asynchronous runs (a synchronous run is in particular asynchronous). The proof needs **`n ≥ 2`**: for
`n = 1` (where `2 tₛ + tₐ ≥ n` can hold) hybrid AA is trivially solvable (`hybridAASolvable_of_card_le_one`).

The requirement used in the asynchronous network is weaker than the paper's: security is only required
on *partially synchronous* runs (`psyncRuns`, with any delay bound `δₐ`), and in the synchronous
network only on runs with the given delay bound `δₛ` (the constructed synchronous runs have zero delay).
-/

open Cslib.Byzantine.PartialSync Finset

namespace HybridApproxAgreement

set_option linter.unusedSectionVars false

variable {P M S K : Type*} [Fintype P] [DecidableEq P]

/-- Partition of `n ≥ 2` parties with `n ≤ 2 u + tₐ` (`u ≥ 1` if needed) into two non-empty groups
of size `≤ max tₛ tₐ` and a remainder of size `≤ tₐ`. -/
theorem exists_split (ts ta : ℕ) (hn2 : 2 ≤ Fintype.card P) (hn : Fintype.card P ≤ 2 * ts + ta) :
    ∃ Sm Sp : Finset P, Sm.Nonempty ∧ Sp.Nonempty ∧ Disjoint Sm Sp ∧
      Sm.card ≤ max ts ta ∧ Sp.card ≤ max ts ta ∧ (Sm ∪ Sp)ᶜ.card ≤ ta := by
  obtain ⟨g, hg, hc⟩ := Fintype.exists_labelling 3 (fun i => if i = 2 then 0 else 1)
    (fun i => if i = 2 then ta else max ts ta) (fun i _ => by split_ifs <;> omega)
    (by simp [sum_range_succ]; omega) (by simp [sum_range_succ]; omega)
  have hrest : (univ.filter (g · = 0) ∪ univ.filter (g · = 1))ᶜ = univ.filter (g · = 2) := by
    ext p; have := hg p; simp; omega
  refine ⟨univ.filter (g · = 0), univ.filter (g · = 1),
    card_pos.1 (by simpa using (hc 0 (by omega)).1),
    card_pos.1 (by simpa using (hc 1 (by omega)).1), disjoint_filter.2 fun _ _ h => by omega,
    by simpa using (hc 0 (by omega)).2, by simpa using (hc 1 (by omega)).2, ?_⟩
  rw [hrest]; simpa using (hc 2 (by omega)).2

/-- In the quiet run in which `F` is Byzantine and silent and all other parties have input `x`, every
honest party outputs `x` (by termination and validity), provided the run belongs to a class on which
`A` is secure. -/
theorem quiet_outputs {Au : Auth P M K} {A : Algorithm P M S ℝ ℝ} {ε : ℝ} {D : Set ℝ}
    {C : Run P M ℝ → Prop} (hA : SecureAA Au A ε D C) {F : Finset P} {x : ℝ} (hx : x ∈ D)
    (hC : C (Run.quiet F fun _ => x)) {p : P} (hp : p ∉ F) :
    Outputs A (Run.quiet F fun _ => x) p x := by
  have hav := Run.quiet_authValid (M := M) (F := F) (I := fun _ => x) (Au := Au) (A := A)
  obtain ⟨v, hv⟩ := hA.termination _ hC hav (fun _ => hx) p hp
  have := InHonestRange.eq_of_const (hA.validity _ hC hav (fun _ => hx) p hp v hv) (x := x)
    (fun _ _ => rfl)
  exact this ▸ hv

/-- **Theorem 5.1** (strong form). Let `n ≥ 2` and `2 tₛ + tₐ ≥ n`, and let the input domain `D`
contain two values at distance `> ε`. Then no unforging protocol is simultaneously a secure AA
protocol on the synchronous runs with at most `tₛ` corruptions (any delay bound `δₛ`) and on the
partially synchronous runs with at most `tₐ` corruptions (any delay bound `δₐ`). -/
theorem not_secure_sync_and_psync {Au : Auth P M K} {A : Algorithm P M S ℝ ℝ}
    (hU : A.Unforging Au) {ts ta δs δa : ℕ} {ε : ℝ} {D : Set ℝ} {x0 x1 : ℝ} (hx0 : x0 ∈ D)
    (hx1 : x1 ∈ D) (hgap : ε < |x1 - x0|) (hn2 : 2 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 2 * ts + ta) :
    ¬ (SecureAA Au A ε D (syncRuns ts δs) ∧ SecureAA Au A ε D (psyncRuns ta δa)) := by
  rintro ⟨hS, hA⟩
  obtain ⟨Sm, Sp, ⟨pm, hpm⟩, ⟨pp, hpp⟩, hd, hcm, hcp, hca⟩ := exists_split ts ta hn2 hn
  -- Run `R₁`: `Sm` silent, inputs `x1`. Some `pp ∈ Sp` outputs `x1`.
  have out1 : ∀ {F : Finset P} {x : ℝ}, x ∈ D → F.card ≤ max ts ta → ∀ p ∉ F,
      Outputs A (Run.quiet F (fun _ => x)) p x := by
    intro F x hx hF p hp
    rcases le_max_iff.mp hF with h | h
    · exact quiet_outputs hS hx (Run.quiet_syncValid h δs) hp
    · exact quiet_outputs hA hx (Run.quiet_valid h δa) hp
  have hpp' : pp ∉ Sm := fun h => disjoint_left.mp hd h hpp
  have hpm' : pm ∉ Sp := disjoint_left.mp hd hpm
  have h1 := out1 hx1 hcm pp hpp'
  have h2 := out1 (F := Sp) hx0 hcp pm hpm'
  obtain ⟨τ1, hτ1⟩ := h1.exists_time
  obtain ⟨τ2, hτ2⟩ := h2.exists_time
  -- the split-brain run `R₃`: `Sₐ` (correct in both) is Byzantine, `S₊` sees `R₁`, `S₋` sees `R₂`
  set T := max τ1 τ2
  set R3 := (Run.quiet (M := M) Sm fun _ => x1).merge A (Run.quiet Sp fun _ => x0) T
  have o1 : Outputs A R3 pp x1 :=
    h1.of_st_eq ⟨τ1, le_max_left _ _, hτ1⟩
      (Run.merge_st_left Run.quiet_canonical · · pp hpp' hpp)
  have o2 : Outputs A R3 pm x0 :=
    h2.of_st_eq ⟨τ2, le_max_right _ _, hτ2⟩
      (Run.merge_st_right Run.quiet_canonical · · pm hpm hpm')
  have hinp : ∀ p, R3.inp p ∈ D := by
    intro p
    by_cases h : p ∈ (Run.quiet (M := M) Sm fun _ => x1).faulty
    · rw [Run.merge_inp_of_mem h]; exact hx0
    · rw [Run.merge_inp_of_notMem h]; exact hx1
  have hR3 : psyncRuns ta δa R3 :=
    Run.merge_valid (by simpa [Run.quiet, ← compl_union] using hca) (fun _ _ _ _ _ => le_rfl)
      fun _ _ _ _ _ => le_rfl
  have := hA.agreement R3 hR3 (Run.merge_authValid hU Run.quiet_canonical Run.quiet_canonical)
    hinp pp (by simp [R3, Run.quiet, hpp]) pm (by simp [R3, Run.quiet, hpm]) x1 x0 o1 o2
  linarith

/-- **Theorem 5.1.** For `n ≥ 2` parties, `ε > 0` and `2 tₛ + tₐ ≥ n`, approximate agreement that is
`tₛ`-secure in a synchronous network and `tₐ`-secure in an asynchronous network is impossible, even
with signatures; already for inputs in any domain `D` containing two points at distance `> ε`
(e.g. `D = Set.univ`, or the bounded input space of a protocol that knows `δmax > ε`). -/
theorem theorem_5_1 {ts ta δ : ℕ} {ε : ℝ} {D : Set ℝ} {x0 x1 : ℝ} (hx0 : x0 ∈ D) (hx1 : x1 ∈ D)
    (hgap : ε < |x1 - x0|) (hn2 : 2 ≤ Fintype.card P) (hn : Fintype.card P ≤ 2 * ts + ta) :
    ¬ HybridAASolvable P ε D ts ta δ := by
  rintro ⟨M, S, K, Au, A, hU, hS, hA⟩
  exact not_secure_sync_and_psync (δa := 0) hU hx0 hx1 hgap hn2 hn
    ⟨hS, hA.mono fun R hR => psyncRuns_le_asyncRuns hR⟩

/-- The paper's form: inputs `±ε`, any `ε > 0`, unrestricted inputs. -/
theorem theorem_5_1' {ts ta δ : ℕ} {ε : ℝ} (hε : 0 < ε) (hn2 : 2 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 2 * ts + ta) : ¬ HybridAASolvable P ε Set.univ ts ta δ :=
  theorem_5_1 (x0 := -ε) (x1 := ε) trivial trivial
    (by rw [show ε - -ε = 2 * ε by ring, abs_of_pos (by linarith)]; linarith) hn2 hn

/-! ### The degenerate case `n ≤ 1` -/

/-- Output the own input immediately. -/
def outputInput (P : Type*) : Algorithm P Unit ℝ ℝ ℝ where
  init _ v := v
  step _ s _ := s
  send _ _ _ := []
  decide _ s := some s

theorem outputInput_st (R : Run P Unit ℝ) : ∀ τ p, R.st (outputInput P) τ p = R.inp p := by
  intro τ p
  induction τ with
  | zero => rfl
  | succ τ ih => rw [Run.st_succ, ← ih]; rfl

theorem outputInput_outputs {R : Run P Unit ℝ} {p : P} {v : ℝ} :
    Outputs (outputInput P) R p v ↔ v = R.inp p := by
  constructor
  · rintro ⟨τ, h, -⟩
    rw [outputInput_st] at h
    exact (Option.some.inj h).symm
  · rintro rfl
    exact ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- For `n ≤ 1` the trivial protocol is a secure AA protocol on *every* class of runs, so
Theorem 5.1 needs `n ≥ 2` (for `n = 1`, `tₛ = 0`, `tₐ = 1` satisfies `2 tₛ + tₐ ≥ n`). -/
theorem outputInput_secure (hP : Fintype.card P ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) (D : Set ℝ)
    (C : Run P Unit ℝ → Prop) : SecureAA (Auth.none P Unit) (outputInput P) ε D C := by
  have hsub : ∀ p q : P, p = q := fun p q => Fintype.card_le_one_iff.mp hP p q
  refine ⟨fun R _ _ _ p _ => ⟨_, outputInput_outputs.mpr rfl⟩, ?_, ?_⟩
  · intro R _ _ _ p hp v hv
    rw [outputInput_outputs.mp hv]
    exact ⟨⟨p, hp, le_rfl⟩, ⟨p, hp, le_rfl⟩⟩
  · intro R _ _ _ p _ q _ v w hv hw
    rw [outputInput_outputs.mp hv, outputInput_outputs.mp hw, hsub p q]
    simpa using hε

theorem hybridAASolvable_of_card_le_one (hP : Fintype.card P ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (D : Set ℝ) (ts ta δ : ℕ) : HybridAASolvable P ε D ts ta δ :=
  ⟨Unit, ℝ, Empty, Auth.none P Unit, outputInput P, (outputInput P).unforging_none,
    outputInput_secure hP hε D _, outputInput_secure hP hε D _⟩

/-- Theorem 5.1 is false as literally stated for `n = 1`: with one party, `tₛ = 0`, `tₐ = 1`
(`2 tₛ + tₐ ≥ n`) hybrid AA is solvable. -/
theorem theorem_5_1_false_n_eq_one {ε : ℝ} (hε : 0 ≤ ε) (δ : ℕ) :
    2 * 0 + 1 ≥ Fintype.card (Fin 1) ∧ HybridAASolvable (Fin 1) ε Set.univ 0 1 δ :=
  ⟨by simp, hybridAASolvable_of_card_le_one (by simp) hε _ _ _ _⟩

end HybridApproxAgreement
