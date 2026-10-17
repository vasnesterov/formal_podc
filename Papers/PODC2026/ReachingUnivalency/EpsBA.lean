import Mathlib
import Podc.Foundations.Count

/-!
# Reaching Univalency — §2.3–2.5: ε-Byzantine Agreement and the reductions

* `EpsBAOn C ε F inp out` : the outputs `out` of the correct members of the committee `C` satisfy
  ε-Agreement and ε-Validity w.r.t. the inputs `inp` (the paper's ε-BA with `Π := C`, `n := |C|`);
  `EpsBA` is the case `C = Π`.
* `prop3` : **Proposition 3** — after ε-BA, one all-to-all exchange of outputs and a majority vote
  solve BA when `f < n(1/2 - ε)`.
* `majorityOracle` : the "ideal" committee outcome (every member outputs the majority of the
  correct members' inputs) is a valid ε-BA outcome for every committee with fewer than
  `|C|(1/3 - ε)` faults (`majorityOracle_epsBA`); used as the committee black box in the
  counterexample to Lemma 6.
* `prop5_committee`, `prop5_extract` : **Proposition 5** — the committee size
  `m = ⌊f/(1/3-ε)⌋ + 1` and the extraction function (majority of signed committee outputs once
  `m - f` members have signed) satisfy Consistency (in the stronger monotone form), Termination and
  Validity.
* `consistency_not_monotone` : the inference stated after the definition of Extractable BA
  ("Consistency implies `F(M) = F(M_c)` for `M_c ⊆ M ⊆ M_a`") does not follow from Consistency.
-/

namespace ReachingUnivalency

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- **ε-BA on a committee `C`** (§2.3 with `Π := C`): there is a set `X` of correct members with
`|X| < |C| ε` and a value `v` such that every correct member outside `X` outputs `v`
(ε-Agreement), and `v = x` whenever fewer than `|C| ε` correct members have an input other than
`x` (ε-Validity). Faulty processors are those in `F`. -/
def EpsBAOn (C : Finset P) (ε : ℚ) (F : Finset P) (inp out : P → Bool) : Prop :=
  ∃ (X : Finset P) (v : Bool), X ⊆ C \ F ∧ (X.card : ℚ) < C.card * ε ∧
    (∀ p ∈ C \ F, p ∉ X → out p = v) ∧
    ∀ x, ((((C \ F).filter fun p => inp p ≠ x).card : ℚ) < C.card * ε → v = x)

/-- **ε-BA** (§2.3): `EpsBAOn` for the whole system. -/
def EpsBA (ε : ℚ) (F : Finset P) (inp out : P → Bool) : Prop := EpsBAOn univ ε F inp out

/-- Number of received values equal to `b`. -/
abbrev recvCount (recv : P → Option Bool) (b : Bool) : ℕ := univ.countEq recv (some b)

/-- Majority of the received values (ties broken by `tie`). -/
def majority (recv : P → Option Bool) (tie : Bool) : Bool :=
  if recvCount recv false < recvCount recv true then true
  else if recvCount recv true < recvCount recv false then false else tie

/-- **Proposition 3.** Let `ε ∈ (0, 1/2)` and `f < n (1/2 - ε)`. After an ε-BA protocol, let every
processor send its output to all; `recv p q` is what `p` receives from `q` (the true output if
`q` is correct, anything if `q` is faulty). Then the majority vote gives Agreement and Validity of
BA. -/
theorem prop3 {ε : ℚ} (hε : 0 < ε) {F : Finset P} (hf : (F.card : ℚ) < Fintype.card P * (1/2 - ε))
    {inp out : P → Bool} (h : EpsBA ε F inp out) (recv : P → P → Option Bool)
    (hrecv : ∀ p q, q ∉ F → recv p q = some (out q)) (tie : P → Bool) :
    (∃ v, ∀ p ∉ F, majority (recv p) (tie p) = v) ∧
    ∀ x, (∀ p ∉ F, inp p = x) → ∀ p ∉ F, majority (recv p) (tie p) = x := by
  obtain ⟨X, v, hX, hXc, hagr, hval⟩ := h
  -- every correct processor sees `v` from more than `n/2` processors
  have key : ∀ p, majority (recv p) (tie p) = v := by
    intro p
    set G := (univ \ F) \ X
    have hG : (G.card : ℚ) > Fintype.card P / 2 := by
      have h1 : G.card = (univ \ F).card - X.card := by
        rw [card_sdiff_of_subset (by simpa using hX)]
      have h2 : (univ \ F).card = Fintype.card P - F.card := by
        rw [card_sdiff_of_subset (subset_univ _), card_univ]
      have h3 : X.card ≤ (univ \ F).card := card_le_card (by simpa using hX)
      have h4 : F.card ≤ Fintype.card P := card_le_univ F
      have : (G.card : ℚ) = Fintype.card P - F.card - X.card := by
        rw [h1, Nat.cast_sub h3, h2, Nat.cast_sub h4]
      rw [this]
      simp only [card_univ] at hXc
      linarith
    have hsub : G ⊆ univ.filter fun q => recv p q = some v := by
      intro q hq
      simp only [G, mem_sdiff, mem_univ, true_and] at hq
      simp [hrecv p q hq.1, hagr q (by simp [hq.1]) hq.2]
    have hv : (recvCount (recv p) v : ℚ) > Fintype.card P / 2 :=
      lt_of_lt_of_le hG (by exact_mod_cast card_le_card hsub)
    have hsum : recvCount (recv p) v + recvCount (recv p) (!v) ≤ Fintype.card P :=
      countEq_add_countEq_le (by cases v <;> simp)
    have hlt : recvCount (recv p) (!v) < recvCount (recv p) v := by
      have : (recvCount (recv p) (!v) : ℚ) < recvCount (recv p) v := by
        have : (recvCount (recv p) v : ℚ) + recvCount (recv p) (!v) ≤ Fintype.card P := by
          exact_mod_cast hsum
        linarith
      exact_mod_cast this
    unfold majority
    cases v
    · simp only [Bool.not_false] at hlt
      simp [hlt, not_lt.mpr hlt.le]
    · simp only [Bool.not_true] at hlt
      simp [hlt]
  refine ⟨⟨v, fun p _ => key p⟩, fun x hx p _ => ?_⟩
  rw [key p]
  apply hval
  have : ((univ \ F).filter fun p => inp p ≠ x) = ∅ := by
    ext q
    simp only [mem_filter, mem_sdiff, mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_and, not_not]
    exact hx q
  rw [this, card_empty, Nat.cast_zero]
  have : (0 : ℚ) < (univ : Finset P).card := by
    have : (0 : ℚ) ≤ F.card := by positivity
    simp only [card_univ]; nlinarith
  positivity

/-! ### The ideal committee outcome -/

/-- Majority of the inputs of the correct members of `C` (ties: `false`). -/
def majVal (C F : Finset P) (vals : P → Bool) : Bool :=
  decide (((C \ F).filter fun p => vals p = false).card < ((C \ F).filter fun p => vals p = true).card)

/-- The ideal committee outcome: every member outputs the majority of the inputs of the correct
members of `C`. -/
def majorityOracle (C F : Finset P) (vals : P → Bool) : P → Bool := fun _ => majVal C F vals

omit [Fintype P] in
lemma card_filter_ne_add (s : Finset P) (vals : P → Bool) (x : Bool) :
    (s.filter fun p => vals p ≠ x).card + (s.filter fun p => vals p = x).card = s.card := by
  rw [add_comm, ← card_union_of_disjoint (disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1; ext p; simp only [mem_union, mem_filter]; tauto

omit [Fintype P] in
/-- The ideal outcome is a valid ε-BA outcome on every committee with fewer than `|C|(1/3 - ε)`
faulty members. -/
theorem majorityOracle_epsBA {ε : ℚ} (hε : 0 < ε) {C F : Finset P}
    (hF : ((C ∩ F).card : ℚ) < C.card * (1/3 - ε)) (vals : P → Bool) :
    EpsBAOn C ε F vals (majorityOracle C F vals) := by
  have hC : (0 : ℚ) < C.card := by
    by_contra h
    push Not at h
    have : (0 : ℚ) ≤ (C ∩ F).card := by positivity
    have h0 : (C.card : ℚ) = 0 := le_antisymm h (by positivity)
    rw [h0, zero_mul] at hF
    linarith
  refine ⟨∅, majVal C F vals, empty_subset _, by simp; positivity, fun p _ _ => rfl,
    fun x hx => ?_⟩
  have h1 := card_filter_ne_add (C \ F) vals x
  have h2 := card_sdiff_add_card_inter C F
  have h1' : ((((C \ F).filter fun p => vals p ≠ x).card : ℕ) : ℚ) +
      (((C \ F).filter fun p => vals p = x).card : ℚ) = ((C \ F).card : ℚ) := by exact_mod_cast h1
  have h2' : ((C \ F).card : ℚ) + (C ∩ F).card = C.card := by exact_mod_cast h2
  have hlt : ((C \ F).filter fun p => vals p ≠ x).card <
      ((C \ F).filter fun p => vals p = x).card := by
    have : ((((C \ F).filter fun p => vals p ≠ x).card : ℕ) : ℚ) <
        (((C \ F).filter fun p => vals p = x).card : ℚ) := by nlinarith
    exact_mod_cast this
  unfold majVal
  cases x
  · have : ((C \ F).filter fun p => vals p ≠ false) = ((C \ F).filter fun p => vals p = true) := by
      ext p; simp
    rw [this] at hlt
    simp [not_lt.mpr hlt.le]
  · have : ((C \ F).filter fun p => vals p ≠ true) = ((C \ F).filter fun p => vals p = false) := by
      ext p; simp
    rw [this] at hlt
    simp [hlt]

/-! ### Proposition 5: Extractable BA from ε-BA on a committee -/

/-- **Proposition 5, committee size.** For `ε ∈ (0, 1/3)` and `f < n(1/3 - ε)`, the committee size
`m = ⌊f/(1/3 - ε)⌋ + 1` satisfies `f < m(1/3 - ε)` and `m ≤ n`. -/
theorem prop5_committee {ε : ℚ} (hε : ε < 1/3) {f n : ℕ} (hf : (f : ℚ) < n * (1/3 - ε)) :
    (f : ℚ) < (⌊(f : ℚ) / (1/3 - ε)⌋₊ + 1 : ℕ) * (1/3 - ε) ∧ ⌊(f : ℚ) / (1/3 - ε)⌋₊ + 1 ≤ n := by
  have hpos : (0 : ℚ) < 1/3 - ε := by linarith
  constructor
  · have := Nat.lt_floor_add_one ((f : ℚ) / (1/3 - ε))
    push_cast
    rwa [div_lt_iff₀ hpos] at this
  · have h1 : (f : ℚ) / (1/3 - ε) < n := by rwa [div_lt_iff₀ hpos]
    have := (Nat.floor_lt (by positivity)).mpr h1
    omega

/-- Signed committee outputs are pairs `(signer, bit)`. The extraction function of Proposition 5:
if the set contains signed outputs of at least `|C| - f` committee members, return the majority
signed bit (ties: `false`), otherwise nothing (the empty string). -/
def extract (C : Finset P) (f : ℕ) (M : Finset (P × Bool)) : Option Bool :=
  let M' := M.filter fun x => x.1 ∈ C
  if C.card - f ≤ (M'.image Prod.fst).card then
    some (decide ((M'.filter fun x => x.2 = false).card < (M'.filter fun x => x.2 = true).card))
  else none

omit [Fintype P] in
/-- **Proposition 5, extraction.** Run ε-BA on a committee `C` of size `m` with `f < m(1/3 - ε)`
faulty members (at most `f`), and let each member sign its output. For every set `Mₐ` of signed
outputs respecting unforgeability (a correct member only signs its own output), the extraction
function returns, on every subset of `Mₐ`, either nothing or the ε-BA value `v`, and returns `v`
on every subset containing the correct members' signed outputs. This is Consistency (even in the
monotone form `M ⊆ M' ⊆ Mₐ → F(M) ⪯ F(M')`), Termination and, via ε-Validity, Validity. -/
theorem prop5_extract {ε : ℚ} {C F : Finset P} {f : ℕ} (hfC : (C ∩ F).card ≤ f)
    (hf : (f : ℚ) < C.card * (1/3 - ε)) {inp out : P → Bool} (hBA : EpsBAOn C ε F inp out) :
    ∃ v : Bool,
      (∀ Ma : Finset (P × Bool), (∀ c b, (c, b) ∈ Ma → c ∈ C → c ∉ F → b = out c) →
        (∀ M ⊆ Ma, extract C f M = none ∨ extract C f M = some v) ∧
        (∀ M ⊆ Ma, (∀ c ∈ C \ F, (c, out c) ∈ M) → extract C f M = some v)) ∧
      ∀ x, (∀ c ∈ C \ F, inp c = x) → v = x := by
  obtain ⟨X, v, hX, hXc, hagr, hval⟩ := hBA
  refine ⟨v, fun Ma hMa => ?_, fun x hx => hval x ?_⟩
  swap
  · have : ((C \ F).filter fun p => inp p ≠ x) = ∅ := by
      ext q
      simp only [mem_filter, Finset.notMem_empty, iff_false, not_and, not_not]
      exact hx q
    rw [this, card_empty, Nat.cast_zero]
    have : (0 : ℚ) ≤ f := by positivity
    nlinarith
  -- on subsets of `Mₐ` with enough signers the majority is `v`
  have maj : ∀ M ⊆ Ma, C.card - f ≤ ((M.filter fun x => x.1 ∈ C).image Prod.fst).card →
      extract C f M = some v := by
    intro M hM hcard
    set M' := M.filter fun x => x.1 ∈ C
    simp only [extract, M'] at hcard ⊢
    simp only [hcard, ↓reduceIte]
    congr 1
    -- pairs with the wrong bit come from faulty members or from `X`
    have hbad : ((M'.filter fun x => x.2 = !v).image Prod.fst) ⊆ (C ∩ F) ∪ X := by
      intro c hc
      simp only [mem_image, mem_filter, M'] at hc
      obtain ⟨⟨c', b⟩, ⟨⟨hm, hcC⟩, hb⟩, rfl⟩ := hc
      simp only at hb hcC ⊢
      by_cases hcF : c' ∈ F
      · exact mem_union_left _ (mem_inter.mpr ⟨hcC, hcF⟩)
      · refine mem_union_right _ ?_
        by_contra hcX
        have h1 := hMa c' b (hM hm) hcC hcF
        have h2 := hagr c' (mem_sdiff.mpr ⟨hcC, hcF⟩) hcX
        rw [hb] at h1
        rw [h2] at h1
        cases v <;> simp at h1
    have hinj : ∀ b : Bool, ((M'.filter fun x => x.2 = b).image Prod.fst).card =
        (M'.filter fun x => x.2 = b).card := by
      intro b
      refine card_image_of_injOn fun x hx y hy hxy => ?_
      simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
      exact Prod.ext hxy (hx.2.trans hy.2.symm)
    have hbad' : (M'.filter fun x => x.2 = !v).card ≤ f + X.card := by
      rw [← hinj]
      calc _ ≤ ((C ∩ F) ∪ X).card := card_le_card hbad
        _ ≤ (C ∩ F).card + X.card := card_union_le _ _
        _ ≤ f + X.card := by omega
    have hsplit : (M'.image Prod.fst) ⊆ ((M'.filter fun x => x.2 = v).image Prod.fst) ∪
        ((M'.filter fun x => x.2 = !v).image Prod.fst) := by
      intro c hc
      simp only [mem_image] at hc
      obtain ⟨⟨c', b⟩, hm, rfl⟩ := hc
      by_cases hb : b = v
      · exact mem_union_left _ (mem_image.mpr ⟨(c', b), mem_filter.mpr ⟨hm, hb⟩, rfl⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨(c', b), mem_filter.mpr ⟨hm, by
          cases b <;> cases v <;> simp_all⟩, rfl⟩)
    have hgood : C.card - f ≤ (M'.filter fun x => x.2 = v).card + (M'.filter fun x => x.2 = !v).card := by
      rw [← hinj v, ← hinj (!v)]
      exact hcard.trans ((card_le_card hsplit).trans (card_union_le _ _))
    have hlt : (M'.filter fun x => x.2 = !v).card < (M'.filter fun x => x.2 = v).card := by
      have hCf : f ≤ C.card := by
        have : (f : ℚ) < C.card := by nlinarith
        exact_mod_cast this.le
      have e1 : ((C.card - f : ℕ) : ℚ) = C.card - f := by rw [Nat.cast_sub hCf]
      have hg : ((C.card - f : ℕ) : ℚ) ≤ ((M'.filter fun x => x.2 = v).card : ℚ) +
          (M'.filter fun x => x.2 = !v).card := by exact_mod_cast hgood
      have hb : ((M'.filter fun x => x.2 = !v).card : ℚ) ≤ f + X.card := by exact_mod_cast hbad'
      have : ((M'.filter fun x => x.2 = !v).card : ℚ) < (M'.filter fun x => x.2 = v).card := by
        rw [e1] at hg
        nlinarith
      exact_mod_cast this
    cases v
    · simp only [Bool.not_false, M'] at hlt
      simp [not_lt.mpr hlt.le]
    · simp only [Bool.not_true, M'] at hlt
      simp [hlt]
  refine ⟨fun M hM => ?_, fun M hM hcont => maj M hM ?_⟩
  · by_cases h : C.card - f ≤ ((M.filter fun x => x.1 ∈ C).image Prod.fst).card
    · exact Or.inr (maj M hM h)
    · left
      simp only [extract]
      simp [h]
  · -- the correct members are signers
    have hsub : C \ F ⊆ ((M.filter fun x => x.1 ∈ C).image Prod.fst) := by
      intro c hc
      exact mem_image.mpr ⟨(c, out c), mem_filter.mpr ⟨hcont c hc, (mem_sdiff.mp hc).1⟩, rfl⟩
    have := card_sdiff_add_card_inter C F
    have := card_le_card hsub
    omega

/-- The remark after the definition of Extractable BA (§2.4) claims that Consistency
(`F(M) ⪯ F(Mₐ)` for all `M ⊆ Mₐ`) together with `F(M_c) ∈ {0,1}` implies `F(M) = F(M_c)` for
`M_c ⊆ M ⊆ Mₐ`. This does not follow: `F(M)` may be the empty string. Strings of length `≤ 1` are
modelled as `Option Bool` (`none` = empty string), so `σ ⪯ τ` is `σ = none ∨ σ = τ`. -/
theorem consistency_not_monotone :
    ∃ (Fn : Finset ℕ → Option Bool) (Mc M Ma : Finset ℕ), Mc ⊆ M ∧ M ⊆ Ma ∧
      (∀ M' ⊆ Ma, Fn M' = none ∨ Fn M' = Fn Ma) ∧ Fn Mc = some true ∧ Fn M = none := by
  refine ⟨fun S => if S.card = 1 then none else some true, ∅, {0}, {0, 1}, by simp, by simp,
    fun M' _ => ?_, by simp, by simp⟩
  by_cases h : M'.card = 1 <;> simp [h]

end ReachingUnivalency
