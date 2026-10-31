import Papers.PODC2019.FastReadsRegisterSim.Section4

/-!
# Theorem 4.1 and the gap in the proof of Lemma 4.2

* `theorem_4_1` — no wait-free atomic simulation of a `k`-valued register (`k = 2^m > 2`) from
  binary registers has two readers whose reads take at most `log₂ k` steps.
* `setting_false` — the core: the hypotheses (`Sec4.Setting`) are contradictory;
* `lemma_4_2` — Lemma 4.2 (same root register), true only vacuously;
* `lemma_4_2_core` — the argument of the paper's proof of Lemma 4.2, as it actually works: if some
  root-to-leaf path of `T₂` avoids the root register of `T₁`, contradiction.
* `lemma_4_2_gap` — the step "a value `z` whose path in `T₂` does not include `r₁` exists since
  `r₁` is not the root of `T₂`" is false for complete decision trees: in the tree of depth 2 with
  root register `1` whose two children both read register `0`, every root-to-leaf path reads
  register `0`.
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι P L : Type} [DecidableEq P] [DecidableEq ι]

open Sec3 Sec4

/-- From the hypotheses of the paper (wait-free, atomic, reads of `r` take at most
`m = log₂ |V|` steps) the first read of `r` is a complete decision tree of depth `m` whose
leaves are labelled bijectively by the values (Lemmas 3.3 and 3.4, read is invisible). -/
theorem readerHyp_of_fast [Fintype V] (I : Sim V v₀ ι P L) {w r : P} (hwr : w ≠ r)
    (hw : ∀ v, I.allowed w (.write v)) (hr : I.allowed r .read) (hwf : I.WaitFree)
    (hsafe : I.Safe w) {m : ℕ} (hk : Fintype.card V = 2 ^ m) (hstep : I.ReadStepsLE r m) :
    ReaderHyp I r m := by
  have hof := hwf.obstructionFree
  have h := seqReads hwr hw hr hof hsafe
  have hR : ∀ v, h.R v ≤ m := by
    intro v
    have := hstep _ _ _ (run_wlab hw hof v) (valid_read hwr hw hr hof v)
      (fun u => not_ret_replicate _ _ u)
    rw [accesses_read hwr hw hr hof v, numSteps_run _ _ (read_spec hwr hw hr hof v).1] at this
    rw [R_eq hwr hw hr hof hsafe v]; exact this
  refine ⟨⟨fun u hu => node_read h hk hR hu, fun u hu => ?_⟩, fun u u' hu hu' he =>
    val_injective h hk hR hu hu' he, fun v => ⟨h.str v, ?_, val_str h hk hR v⟩⟩
  · obtain ⟨l, hl, -⟩ := node_ret h hk hR hu; exact ⟨l, hl⟩
  · exact (h.complete hk (str_length_le h hk hR)).1 v

/-- **Lemma 4.2, the argument of its proof.** In the setting of Theorem 4.1, if some root-to-leaf
path of the decision tree `T₂` of the second reader does not read the root register `ρ` of the
tree `T₁` of the first reader, we get a contradiction. -/
theorem lemma_4_2_core {I : Sim V v₀ ι P L} {w r₁ r₂ : P} {m : ℕ} (S : Setting I w r₁ r₂ m)
    {ρ : ι} (hρ : RdN (I.act r₁) (nd I r₁ []) ρ) {u₂ : List Bool} (hu₂ : u₂.length = m)
    (havoid : ∀ j < m, ∀ i, RdN (I.act r₂) (nd I r₂ (u₂.take j)) i → i ≠ ρ) : False :=
  caseA S hρ hu₂ havoid

/-- **Core of Theorem 4.1**: the setting is contradictory (repaired proof: `caseA` if some path
of `T₂` avoids the root register `ρ` of `T₁`, `caseB` otherwise). -/
theorem setting_false {I : Sim V v₀ ι P L} {w r₁ r₂ : P} {m : ℕ} (S : Setting I w r₁ r₂ m) :
    False := by
  obtain ⟨ρ, k, hk', -⟩ := S.R₁.tree.inner [] (by have := S.hm; simp; omega)
  have hρ : RdN (I.act r₁) (nd I r₁ []) ρ := ⟨k, hk'⟩
  by_cases hA : ∃ u₂ : List Bool, u₂.length = m ∧
      ∀ j < m, ∀ i, RdN (I.act r₂) (nd I r₂ (u₂.take j)) i → i ≠ ρ
  · obtain ⟨u₂, hu₂, hav⟩ := hA
    exact caseA S hρ hu₂ hav
  · push Not at hA
    refine caseB S hρ (fun U hU => ?_)
    obtain ⟨j, hj, i, hi, rfl⟩ := hA U hU
    exact ⟨j, hj, hi⟩

/-- **Lemma 4.2** of the paper: in the setting of Theorem 4.1, the decision trees `T₁` and `T₂`
have the same root register. True, but only vacuously: the setting is contradictory
(`setting_false`); the paper's own proof has a gap (`lemma_4_2_gap`). -/
theorem lemma_4_2 {I : Sim V v₀ ι P L} {w r₁ r₂ : P} {m : ℕ} (S : Setting I w r₁ r₂ m)
    {ρ₁ ρ₂ : ι} (_ : RdN (I.act r₁) (nd I r₁ []) ρ₁) (_ : RdN (I.act r₂) (nd I r₂ []) ρ₂) :
    ρ₁ = ρ₂ :=
  (setting_false S).elim

/-- **Theorem 4.1** of the paper. No wait-free simulation of an atomic `k`-valued register
(`k = 2 ^ m > 2`) using atomic binary registers can have reads that take at most `log₂ k` steps,
assuming there are at least two readers: if `r₁ ≠ r₂` are readers, the reads of `r₁` and of `r₂`
cannot both take at most `m` steps. -/
theorem theorem_4_1 [Fintype V] (I : Sim V v₀ ι P L) {w r₁ r₂ : P} (h1w : r₁ ≠ w)
    (h2w : r₂ ≠ w) (h12 : r₁ ≠ r₂) (hw : ∀ v, I.allowed w (.write v))
    (hr₁ : I.allowed r₁ .read) (hr₂ : I.allowed r₂ .read) (hwf : I.WaitFree)
    (hatom : I.Atomic w) {m : ℕ} (hk : Fintype.card V = 2 ^ m) (hk2 : 2 < Fintype.card V) :
    ¬ (I.ReadStepsLE r₁ m ∧ I.ReadStepsLE r₂ m) := by
  rintro ⟨hs₁, hs₂⟩
  have hsafe := hatom.regular.safe
  have hm : 2 ≤ m := by
    by_contra hlt
    interval_cases m <;> simp_all
  exact setting_false
    { h1w, h2w, h12, hw, hr₁, hr₂, hof := hwf.obstructionFree, hatom, hm,
      R₁ := readerHyp_of_fast I (Ne.symm h1w) hw hr₁ hwf hsafe hk hs₁
      R₂ := readerHyp_of_fast I (Ne.symm h2w) hw hr₂ hwf hsafe hk hs₂ }

/-! ## The gap in the proof of Lemma 4.2 -/

/-- A reader program whose first read is the complete decision tree of depth 2 with root register
`1` and register `0` at both children (local state = bits read so far, leaves return the bits). -/
def gapAct (u : List Bool) : Action (register (List Bool) []) (BinRegs (Fin 2)) (List Bool) :=
  match u with
  | [] => .access 1 .read (fun b => [b])
  | [c] => .access 0 .read (fun b => [c, b])
  | _ => .ret u u

/-- **The gap in the proof of Lemma 4.2.** The tree `gapAct` is complete of depth 2 (every leaf
is at depth 2 and the four leaves carry distinct values), its root register `1` differs from the
register `0`, and still every root-to-leaf path reads register `0`. So "`r₁` is not the root of
`T₂`" does not imply that some path of `T₂` avoids `r₁`. -/
theorem lemma_4_2_gap :
    -- the root reads register `1`, not `0`
    RdN gapAct (node gapAct [] []) (1 : Fin 2) ∧ ¬ RdN gapAct (node gapAct [] []) (0 : Fin 2) ∧
    -- complete tree of depth 2 with distinct leaf values
    (∀ u : List Bool, u.length < 2 → ∃ i k, gapAct (node gapAct [] u) = .access i .read k) ∧
    (∀ u : List Bool, u.length = 2 → ∃ l, gapAct (node gapAct [] u) = .ret u l) ∧
    -- every root-to-leaf path reads register `0`
    ∀ u : List Bool, u.length = 2 → ∃ j < 2, RdN gapAct (node gapAct [] (u.take j)) (0 : Fin 2) := by
  refine ⟨⟨_, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    simp only [node, List.foldl_nil, gapAct, Action.access.injEq] at hk
    exact absurd hk.1 (by decide)
  · intro u hu
    match u, hu with
    | [], _ => exact ⟨_, _, rfl⟩
    | [c], _ => exact ⟨_, _, rfl⟩
  · intro u hu
    match u, hu with
    | [c, d], _ => exact ⟨_, rfl⟩
  · intro u hu
    match u, hu with
    | [c, d], _ => exact ⟨1, by omega, _, rfl⟩

end Podc.FastReadsRegisterSim
