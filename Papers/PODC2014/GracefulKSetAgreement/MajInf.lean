import Papers.PODC2014.GracefulKSetAgreement.Model

/-!
# The message adversary `MAJINF(k)` (Definitions 17–21)

A vertex-stable root component is represented together with its *maximal* interval of stability
`[a, b]` (round indices, `b = ⊤` for a root component that stays stable forever):
`IsMaxVSRC ρ R a b`. `Vd ρ d` (the paper's `V_d`) is the set of maximal VSRCs of length `≥ d`.

* Definition 17 (influence) `Influences`: a causal chain from `p` starting right after the
  interval of `R_cur` that ends at the latest in the first round of `R_suc`
  (`cd_{s_cur+1}(p, q) ≤ r_suc − s_cur`); it presupposes that `R_cur` ends before `R_suc` starts.
* Definition 18 (influence sets) `IS`.
* Definition 19 (majority influence), two readings:
  - `MajInfLit`, the literal one: `R` ranges over all of `V_{D+1}`. Since `IS(R_cur, R_cur) = ∅`,
    taking `R = R_cur` requires `|IS(R_cur, R_suc)| > |IS(R_cur, R_suc)|`, so it never holds
    (`majInfLit_false`), and with it `MAJINF(k)` just says `|V_{2D+1}| ≤ k`
    (`mem_MAJINFLit_iff`).
  - `MajInf`, the charitable one used by `MAJINF`: `R ≠ R_cur`, and `R_cur` ends before `R_suc`
    starts ("majority-influenced by some *earlier* VSRC", p. 29; without this, Def. 19 lets a
    later VSRC majority-influence an earlier one).
* Definition 21 `MAJINF D k`: all but at most `k` VSRCs of `V_{2D+1}` are majority-influenced by
  some VSRC of `V_{2D+1}`. (Definition 20, strong influence, is not needed.)

Interpretation choices (continuing I1–I9 of `Alg4.lean`):
* **I10** `V_d` consists of maximal VSRCs (with `[a, ∞)` for eventually stable root components).
* **I11** `IS(R₁, R₂) = ∅` unless `R₁`'s interval ends before `R₂`'s starts.
* **I12** Definition 15 (iii) is used in the strong reading `VSRCkAll` of `Model.lean`.
* **I13–I14** Definition 19 as `MajInf` (and `MajInfLit`) above.
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

variable {P : Type}

/-- A VSRC with its interval: vertex set, first round, last round (`⊤` = forever). -/
abbrev VSRCI (P : Type) := Set P × ℕ × ℕ∞

/-- `R` is a vertex-stable root component in exactly the rounds `a..b` (`b = ⊤`: forever): it is a
root component in each of these rounds but neither in round `a − 1` nor in round `b + 1`. -/
def IsMaxVSRC (ρ : ℕ → Graph P) (R : Set P) (a : ℕ) (b : ℕ∞) : Prop :=
  (a : ℕ∞) ≤ b ∧
  (∀ t : ℕ, a ≤ t → (t : ℕ∞) ≤ b → IsRootComp (ρ t) R) ∧
  (∀ t, t + 1 = a → ¬ IsRootComp (ρ t) R) ∧
  (∀ t : ℕ, b = t → ¬ IsRootComp (ρ (t + 1)) R)

/-- `V_d`: the (maximal) vertex-stable root components that are stable for at least `d`
consecutive rounds. -/
def Vd (ρ : ℕ → Graph P) (d : ℕ) : Set (VSRCI P) :=
  {X | IsMaxVSRC ρ X.1 X.2.1 X.2.2 ∧ ((X.2.1 + d : ℕ) : ℕ∞) ≤ X.2.2 + 1}

theorem Vd_mono {ρ : ℕ → Graph P} {d d' : ℕ} (h : d ≤ d') : Vd ρ d' ⊆ Vd ρ d := by
  rintro X ⟨hX, hlen⟩
  refine ⟨hX, le_trans ?_ hlen⟩
  exact_mod_cast Nat.add_le_add_left h _

/-- `X` ends before `Y` starts. -/
def Precedes (X Y : VSRCI P) : Prop := ∃ b : ℕ, X.2.2 = b ∧ b < Y.2.1

/-- **Definition 17** (influence): `p ∈ R_cur` influences `q ∈ R_suc` if `R_cur` ends (round
`s_cur`) before `R_suc` starts (round `r_suc`) and there is a causal chain from `p` starting in
round `s_cur + 1` and ending at the latest in round `r_suc`. -/
def Influences (ρ : ℕ → Graph P) (X Y : VSRCI P) (p q : P) : Prop :=
  ∃ b : ℕ, X.2.2 = b ∧ b < Y.2.1 ∧ Journey ρ (b + 1) p (Y.2.1 + 1) q

/-- **Definition 18** (influence sets): `IS(R_cur, R_suc) = {q ∈ R_suc | ∃ p ∈ R_cur, p ↪ q}`. -/
def IS (ρ : ℕ → Graph P) (X Y : VSRCI P) : Set P :=
  {q | q ∈ Y.1 ∧ ∃ p ∈ X.1, Influences ρ X Y p q}

theorem IS_eq_empty_of_not_precedes {ρ : ℕ → Graph P} {X Y : VSRCI P} (h : ¬ Precedes X Y) :
    IS ρ X Y = ∅ := by
  ext q
  simp only [IS, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro - ⟨p, -, b, hb, hlt, -⟩
  exact h ⟨b, hb, hlt⟩

/-- **Definition 19, literal reading**: `R_cur ↪m R_suc` iff for all `R ∈ V_{D+1}` with
`IS(R, R_cur) = ∅`, `|IS(R_cur, R_suc)| > |IS(R, R_suc)|`, and for all `R ∈ V_{D+1}` with
`IS(R, R_cur) ≠ ∅`, `|IS(R_cur, R_suc)| ≥ |IS(R, R_suc)|`. -/
def MajInfLit (ρ : ℕ → Graph P) (D : ℕ) (X Y : VSRCI P) : Prop :=
  X ∈ Vd ρ (2 * D + 1) ∧ Y ∈ Vd ρ (2 * D + 1) ∧
  ∀ R ∈ Vd ρ (D + 1),
    (IS ρ R X = ∅ → (IS ρ R Y).ncard < (IS ρ X Y).ncard) ∧
    (IS ρ R X ≠ ∅ → (IS ρ R Y).ncard ≤ (IS ρ X Y).ncard)

/-- **Definition 19, charitable reading**: as `MajInfLit`, but `R` ranges over `V_{D+1} \ {R_cur}`
and `R_cur` must end before `R_suc` starts. -/
def MajInf (ρ : ℕ → Graph P) (D : ℕ) (X Y : VSRCI P) : Prop :=
  X ∈ Vd ρ (2 * D + 1) ∧ Y ∈ Vd ρ (2 * D + 1) ∧ Precedes X Y ∧
  ∀ R ∈ Vd ρ (D + 1), R ≠ X →
    (IS ρ R X = ∅ → (IS ρ R Y).ncard < (IS ρ X Y).ncard) ∧
    (IS ρ R X ≠ ∅ → (IS ρ R Y).ncard ≤ (IS ρ X Y).ncard)

/-- **The literal Definition 19 is unsatisfiable**: take `R = R_cur`; `IS(R_cur, R_cur) = ∅`. -/
theorem majInfLit_false {ρ : ℕ → Graph P} {D : ℕ} {X Y : VSRCI P} : ¬ MajInfLit ρ D X Y := by
  rintro ⟨hX, -, h⟩
  have hX' : X ∈ Vd ρ (D + 1) := Vd_mono (by omega) hX
  have hXX : IS ρ X X = ∅ := by
    refine IS_eq_empty_of_not_precedes ?_
    rintro ⟨b, hb, hlt⟩
    have := hX.1.1
    rw [hb] at this
    exact absurd (by exact_mod_cast this) (Nat.not_le.mpr hlt)
  exact lt_irrefl _ ((h X hX').1 hXX)

/-- **Definition 21** (`MAJINF(k)`, with the charitable Definition 19): some `K ⊆ V_{2D+1}` with
`|K| ≤ k` such that every `R ∈ V_{2D+1} \ K` is majority-influenced by some `R' ∈ V_{2D+1}`. -/
def MAJINF (D k : ℕ) : Set (ℕ → Graph P) := {ρ |
  ∃ K ⊆ Vd ρ (2 * D + 1), K.encard ≤ k ∧
    ∀ Y ∈ Vd ρ (2 * D + 1) \ K, ∃ X ∈ Vd ρ (2 * D + 1), MajInf ρ D X Y}

/-- **Definition 21 with the literal Definition 19.** -/
def MAJINFLit (D k : ℕ) : Set (ℕ → Graph P) := {ρ |
  ∃ K ⊆ Vd ρ (2 * D + 1), K.encard ≤ k ∧
    ∀ Y ∈ Vd ρ (2 * D + 1) \ K, ∃ X ∈ Vd ρ (2 * D + 1), MajInfLit ρ D X Y}

/-- With the literal Definition 19, `MAJINF(k)` only says that at most `k` VSRCs are stable for
`2D + 1` rounds. -/
theorem mem_MAJINFLit_iff {ρ : ℕ → Graph P} {D k : ℕ} :
    ρ ∈ MAJINFLit D k ↔ (Vd ρ (2 * D + 1)).encard ≤ k := by
  constructor
  · rintro ⟨K, hK, hcard, h⟩
    have : Vd ρ (2 * D + 1) ⊆ K := fun Y hY => by
      by_contra hYK
      obtain ⟨X, -, hXY⟩ := h Y ⟨hY, hYK⟩
      exact majInfLit_false hXY
    exact (Set.encard_le_encard this).trans hcard
  · intro h
    exact ⟨_, subset_rfl, h, fun Y hY => absurd hY.1 hY.2⟩

end Podc.GracefulKSetAgreement
