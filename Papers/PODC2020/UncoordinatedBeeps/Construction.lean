import Papers.PODC2020.UncoordinatedBeeps.USICode
import Podc.Foundations.Combinatorics.SidonSet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# USI-codes from Sidon sets (Section 3.2 of the paper)

Dufoulon, Burman, Beauquier. *Can Uncoordinated Beeps tell Stories?* PODC 2020.

* `IsSidonSet l K D` — Definition 4 (`(l, K)` Sidon set).
* `theorem_3` — the Erdős–Turán construction (proved in `Podc/Foundations/Combinatorics/SidonSet`).
* `lemma_4` — Sidon sets are Golomb rulers (integer differences); `lemma_4_mod_false` — the paper's
  literal statement with differences `mod l` is false.
* `lemma_6`, `theorem_5`, `theorem_7`, `corollary_8` — the codes built from Sidon sets.

The paper's codeword for a set `S = {d + 1 : d ∈ D}` of 1-based positions is `indWord l D` (0-based
positions `D`).
-/

namespace Podc.UncoordinatedBeeps

open Word Cslib

/-- The binary word of length `l` whose `1`-positions are exactly the (0-based) positions in `P`.
For `P = D` this is the paper's codeword `c` with `c[p] = 1 ⟺ p ∈ S = {d + 1 : d ∈ D}`. -/
def indWord (l : ℕ) (P : Finset ℕ) : Word l := fun i => decide ((i : ℕ) ∈ P)

/-- **Definition 4.** An `(l, K)` Sidon set: a `K`-element subset of `{0, …, l - 1}` all of whose
pairwise sums are different (sums `d + d` included). -/
def IsSidonSet (l K : ℕ) (D : Finset ℕ) : Prop :=
  (∀ d ∈ D, d < l) ∧ D.card = K ∧ IsSidon (↑D : Set ℕ)

/-- **Theorem 3** (Erdős–Turán). For an odd prime `p` with `K ≤ p ≤ 2K`, the set
`{2 i p + (i² mod p) : i < K}` is an `(l, K)` Sidon set with `l = 2p² ≤ 8K²`. -/
theorem theorem_3 {p K : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : K ≤ p) (hpK : p ≤ 2 * K) :
    IsSidonSet (2 * p ^ 2) K (SidonSet.erdosTuran p K) ∧ 2 * p ^ 2 ≤ 8 * K ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := SidonSet.erdosTuran_spec hp hp2 hK hpK
  exact ⟨⟨h3, h2, h1⟩, h4⟩

/-- **Lemma 4** (distinct pairwise differences), integer version: in an `(l, K)` Sidon set, every
non-zero difference `d₁ - d₂` is realised by only one pair. -/
theorem lemma_4 {l K : ℕ} {D : Finset ℕ} (hD : IsSidonSet l K D) {d₁ d₂ d₃ d₄ : ℕ}
    (h₁ : d₁ ∈ D) (h₂ : d₂ ∈ D) (h₃ : d₃ ∈ D) (h₄ : d₄ ∈ D) (hne : d₁ ≠ d₂)
    (h : (d₁ : ℤ) - d₂ = d₃ - d₄) : d₁ = d₃ ∧ d₂ = d₄ :=
  hD.2.2.golomb h₁ h₂ h₃ h₄ (by omega) hne

/-- **Lemma 4 as literally stated is false**: differences are taken `mod l` there, and a Sidon set
need not be a Golomb ruler modulo `l`. The Erdős–Turán set of `theorem_3` for `p = K = 3` is
`D = {0, 7, 13}`, a `(14, 3)` Sidon set (`14 ≤ 2p² = 18`), and `7 - 0 ≡ 0 - 7 (mod 14)`. -/
theorem lemma_4_mod_false :
    IsSidonSet 14 3 (SidonSet.erdosTuran 3 3) ∧ SidonSet.erdosTuran 3 3 = {0, 7, 13} ∧
      ((7 : ℤ) - 0) % 14 = ((0 : ℤ) - 7) % 14 ∧ (7, 0) ≠ (0, 7) := by
  have hET : SidonSet.erdosTuran 3 3 = {0, 7, 13} := by decide
  refine ⟨⟨by rw [hET]; decide, SidonSet.card_erdosTuran (by norm_num) 3,
    SidonSet.erdosTuran_isSidon Nat.prime_three (by norm_num) le_rfl⟩, hET, by norm_num,
    by decide⟩

/-- **Lemma 4 as literally stated is false**, even when a difference `d₁ - d₂` and its negative
`d₂ - d₁` are not told apart (i.e. pairs counted as unordered): `D = {0, 1, 3}` is a `(4, 3)` Sidon
set, and `1 ≡ 1 - 0 ≡ 0 - 3 (mod 4)` is realised by the two different pairs `{0, 1}` and `{0, 3}`. -/
theorem lemma_4_mod_false' :
    IsSidonSet 4 3 {0, 1, 3} ∧ ((1 : ℤ) - 0) % 4 = 1 ∧ ((0 : ℤ) - 3) % 4 = 1 ∧
      ({1, 0} : Finset ℕ) ≠ {0, 3} := by
  refine ⟨⟨by decide, by decide, ?_⟩, by norm_num, by norm_num, by decide⟩
  intro a ha b hb c hc d hd h
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb hc hd
  omega

theorem indWord_getZ {l : ℕ} {P : Finset ℕ} (hP : ∀ s ∈ P, s < l) {m : ℤ} :
    (indWord l P).getZ m = true ↔ ∃ s ∈ P, m = s := by
  rw [getZ_eq_true]
  constructor
  · rintro ⟨hb, hm⟩
    simp only [indWord, decide_eq_true_eq] at hm
    exact ⟨_, hm, by omega⟩
  · rintro ⟨s, hs, rfl⟩
    have := hP s hs
    exact ⟨by omega, by simpa [indWord] using hs⟩

theorem extShift_indWord {l : ℕ} {P : Finset ℕ} (hP : ∀ s ∈ P, s < l) {t : ℤ}
    {j : Fin (3 * l - 2)} :
    extShift (indWord l P) t j = true ↔ ∃ s ∈ P, ((j : ℕ) : ℤ) = s + ((l : ℤ) - 1 + t) := by
  simp only [extShift, indWord_getZ hP]
  constructor <;> rintro ⟨s, hs, h⟩ <;> exact ⟨s, hs, by omega⟩

/-- The heart of Lemma 6 / Theorem 7: two extended shifted words built from subsets `P, Q` of a Sidon
set share at most one `1`-position, unless they are the same shift of overlapping sets. -/
theorem card_common_le_one {l : ℕ} {D P Q : Finset ℕ} (hD : IsSidon (↑D : Set ℕ))
    (hDl : ∀ d ∈ D, d < l) (hPD : P ⊆ D) (hQD : Q ⊆ D) {t t' : ℤ}
    (htt : t = t' → Disjoint P Q) :
    (Finset.univ.filter fun j : Fin (3 * l - 2) =>
      extShift (indWord l P) t j = true ∧ extShift (indWord l Q) t' j = true).card ≤ 1 := by
  have hP : ∀ s ∈ P, s < l := fun s hs => hDl s (hPD hs)
  have hQ : ∀ s ∈ Q, s < l := fun s hs => hDl s (hQD hs)
  rw [Finset.card_le_one]
  intro j₁ hj₁ j₂ hj₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, extShift_indWord hP,
    extShift_indWord hQ] at hj₁ hj₂
  obtain ⟨⟨s₁, hs₁, e₁⟩, ⟨s₁', hs₁', e₁'⟩⟩ := hj₁
  obtain ⟨⟨s₂, hs₂, e₂⟩, ⟨s₂', hs₂', e₂'⟩⟩ := hj₂
  by_contra hne
  have hs : s₁ ≠ s₂ := by
    rintro rfl; apply hne; ext; omega
  rcases hD (hPD hs₁) (hQD hs₂') (hPD hs₂) (hQD hs₁') (by omega) with ⟨h, -⟩ | ⟨h, -⟩
  · exact hs h
  · subst h
    have htt' : t = t' := by omega
    exact Finset.disjoint_left.1 (htt htt') hs₁ hs₁'

/-- **Lemma 6.** For an `(l, K)` Sidon set `D` and its codeword `c`, two extended shifted words
`σ̄(c, t)`, `σ̄(c, t')` with `t ≠ t'` have at most one common `1`-position. (The paper omits the
hypothesis `t ≠ t'`, which is clearly intended.) -/
theorem lemma_6 {l K : ℕ} {D : Finset ℕ} (hD : IsSidonSet l K D) {t t' : ℤ} (htt : t ≠ t') :
    (Finset.univ.filter fun j : Fin (3 * l - 2) =>
      extShift (indWord l D) t j = true ∧ extShift (indWord l D) t' j = true).card ≤ 1 :=
  card_common_le_one hD.2.2 hD.1 subset_rfl subset_rfl fun h => absurd h htt

/-- Definition 4 must count the sums `d + d`: under the weaker reading "sums of two *distinct*
elements are different", `D = {0, 1, 2}` would be a `(3, 3)` Sidon set (`0+1, 0+2, 1+2` differ), but
its codeword `111` has `σ̄(111, 0)` and `σ̄(111, 1)` sharing two `1`-positions, so Lemma 4 and
Lemma 6 fail. (The Erdős–Turán sets of Theorem 3 satisfy the strong reading, `theorem_3`.) -/
theorem lemma_6_needs_strong_sidon :
    (∀ a ∈ ({0, 1, 2} : Finset ℕ), ∀ b ∈ ({0, 1, 2} : Finset ℕ), ∀ c ∈ ({0, 1, 2} : Finset ℕ),
      ∀ d ∈ ({0, 1, 2} : Finset ℕ), a ≠ b → c ≠ d → a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
    (Finset.univ.filter fun j : Fin (3 * 3 - 2) =>
      extShift (indWord 3 {0, 1, 2}) 0 j = true ∧
        extShift (indWord 3 {0, 1, 2}) 1 j = true).card = 2 := by
  constructor
  · decide
  · decide

/-- An extended shifted codeword `σ̄(c, t)` with `t` in the shift range has at least `|P|` ones. -/
theorem card_le_ones {l : ℕ} {P : Finset ℕ} (hP : ∀ s ∈ P, s < l) {t : ℤ}
    (ht : InShiftRange l t) :
    P.card ≤ (Finset.univ.filter fun j : Fin (3 * l - 2) =>
      extShift (indWord l P) t j = true).card := by
  obtain ⟨ht1, ht2⟩ := ht
  let f : ℕ → Fin (3 * l - 2) := fun s =>
    if hs : s < l then ⟨s + ((l : ℤ) - 1 + t).toNat, by omega⟩ else ⟨0, by omega⟩
  have hf : ∀ s ∈ P, ((f s : ℕ) : ℤ) = s + ((l : ℤ) - 1 + t) := by
    intro s hs; simp only [f, hP s hs, ↓reduceDIte]; omega
  calc P.card = (P.image f).card := by
        refine (Finset.card_image_of_injOn ?_).symm
        intro a ha b hb hab
        have := hf a ha; have := hf b hb
        have : ((f a : ℕ) : ℤ) = f b := by rw [hab]
        omega
    _ ≤ _ := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_image] at hj
        obtain ⟨s, hs, rfl⟩ := hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, extShift_indWord hP]
        exact ⟨s, hs, hf s hs⟩

/-- The general form of **Theorem 7**: codewords given by pairwise disjoint `(k+1)`-element subsets
`P a` (`a : Fin h`) of a Sidon set `D ⊆ {0, …, l - 1}` form a `USI(h, k)`-code of length `l`. -/
theorem isUSICode_of_sidon {l h k : ℕ} {D : Finset ℕ} (hD : IsSidon (↑D : Set ℕ))
    (hDl : ∀ d ∈ D, d < l) (P : Fin h → Finset ℕ) (hPD : ∀ a, P a ⊆ D)
    (hdisj : Pairwise fun a b => Disjoint (P a) (P b)) (hcard : ∀ a, (P a).card = k + 1) :
    IsUSICode (Finset.univ.image fun a => indWord l (P a)) h k := by
  classical
  have hPl : ∀ a, ∀ s ∈ P a, s < l := fun a s hs => hDl s (hPD a hs)
  constructor
  · -- the `h` codewords are distinct
    rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
    intro a b hab
    by_contra hne
    obtain ⟨s, hs⟩ := Finset.card_pos.1 (by rw [hcard a]; omega : 0 < (P a).card)
    have h1 : (indWord l (P a)).getZ s = true := (indWord_getZ (hPl a)).2 ⟨s, hs, rfl⟩
    simp only at hab
    rw [hab, indWord_getZ (hPl b)] at h1
    obtain ⟨s', hs', e⟩ := h1
    have : s = s' := by exact_mod_cast e
    subst this
    exact Finset.disjoint_left.1 (hdisj hne) hs hs'
  · intro X hX hXC c hc t ht hcX hcont
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨b, rfl⟩ := hc
    set O := Finset.univ.filter fun j : Fin (3 * l - 2) => extShift (indWord l (P b)) t j = true
    have hO : k + 1 ≤ O.card := hcard b ▸ card_le_ones (hPl b) ht
    -- every one of `σ̄(c, t)` is a one of some `σ̄(x)`, `x ∈ X`, and each `x` covers at most one
    have hsub : O ⊆ X.biUnion fun x => O.filter fun j => extShift x.1 x.2 j = true := by
      intro j hj
      have hj' := hj
      simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      obtain ⟨x, hx, hxj⟩ := superpose_eq_true.1 (hcont j hj')
      exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨hj, hxj⟩⟩
    have hle : ∀ x ∈ X, (O.filter fun j => extShift x.1 x.2 j = true).card ≤ 1 := by
      intro x hx
      obtain ⟨hxC, -⟩ := hXC x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxC
      obtain ⟨a, ha⟩ := hxC
      have := card_common_le_one (l := l) hD hDl (hPD b) (hPD a) (t := t) (t' := x.2) ?_
      · refine le_trans (Finset.card_le_card ?_) this
        intro j hj
        simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨hj.1, ha ▸ hj.2⟩
      · intro htt
        by_cases hab : b = a
        · subst hab
          exact absurd (show (indWord l (P b), t) ∈ X by rw [htt, ha]; exact hx) hcX
        · exact hdisj hab
    have := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_card_nsmul _ _ 1 hle))
    simp only [smul_eq_mul, mul_one] at this
    omega

/-- **Theorem 7.** Let `D` be an `(l, h·K)` Sidon set partitioned into `h` sets `S₁, …, S_h` of size
`K ≥ 1`, and let `cᵢ` have its ones exactly at `Sᵢ`. Then `{c₁, …, c_h}` is a `USI(h, K - 1)`-code of
length `l`. -/
theorem theorem_7 {l h K : ℕ} {D : Finset ℕ} (hD : IsSidonSet l (h * K) D) (hK : 1 ≤ K)
    (S : Fin h → Finset ℕ) (hpart : (Finset.univ.biUnion S) = D)
    (hdisj : Pairwise fun a b => Disjoint (S a) (S b)) (hcard : ∀ a, (S a).card = K) :
    IsUSICode (Finset.univ.image fun a => indWord l (S a)) h (K - 1) :=
  isUSICode_of_sidon hD.2.2 hD.1 S
    (fun a => hpart ▸ Finset.subset_biUnion_of_mem S (Finset.mem_univ a)) hdisj
    (fun a => by rw [hcard a]; omega)

/-- **Theorem 5.** For an `(l, K)` Sidon set `D` (`K ≥ 1`), the single codeword with ones at `D`
forms a `USI(1, K - 1)`-code of length `l`. -/
theorem theorem_5 {l K : ℕ} {D : Finset ℕ} (hD : IsSidonSet l K D) (hK : 1 ≤ K) :
    IsUSICode ({indWord l D} : Finset (Word l)) 1 (K - 1) := by
  have := theorem_7 (h := 1) (by rwa [one_mul]) hK (fun _ => D) (by simp)
    (fun a b hab => absurd (Subsingleton.elim a b) hab) (fun _ => hD.2.1)
  simpa using this

/-- **Corollary 8.** For all `h, k` there is a `USI(h, k)`-code of length `l ≤ 8 h² (k + 1)²`. -/
theorem corollary_8 (h k : ℕ) :
    ∃ l ≤ 8 * h ^ 2 * (k + 1) ^ 2, ∃ C : Finset (Word l), IsUSICode C h k := by
  obtain ⟨e, he, hS, hlt⟩ := SidonSet.exists_sidon_enum (h * (k + 1))
  refine ⟨8 * (h * (k + 1)) ^ 2, by ring_nf; rfl, _, isUSICode_of_sidon hS ?_
    (fun a => (Finset.Ico (a * (k + 1)) ((a + 1) * (k + 1))).image e) ?_ ?_ ?_⟩
  · intro d hd
    simp only [Finset.mem_image, Finset.mem_range] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    exact hlt i hi
  · intro a
    apply Finset.image_subset_image
    intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
    have := a.isLt
    calc i < (a + 1) * (k + 1) := hi.2
      _ ≤ h * (k + 1) := Nat.mul_le_mul_right _ (by omega)
  · intro a b hab
    rw [Finset.disjoint_image he]
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [Finset.mem_Ico] at hia hib
    apply hab
    ext
    rcases Nat.lt_or_ge (a : ℕ) b with h1 | h1
    · have : ((a : ℕ) + 1) * (k + 1) ≤ b * (k + 1) := Nat.mul_le_mul_right _ h1
      omega
    · rcases Nat.lt_or_ge (b : ℕ) a with h2 | h2
      · have : ((b : ℕ) + 1) * (k + 1) ≤ a * (k + 1) := Nat.mul_le_mul_right _ h2
        omega
      · omega
  · intro a
    rw [Finset.card_image_of_injective _ he, Nat.card_Ico]
    ring_nf; omega

/-- **Corollary 8**, second part: a `USI(2, k)`-code of length `l ≤ 32 (k + 1)²`. -/
theorem corollary_8_two (k : ℕ) :
    ∃ l ≤ 32 * (k + 1) ^ 2, ∃ C : Finset (Word l), IsUSICode C 2 k := by
  obtain ⟨l, hl, C, hC⟩ := corollary_8 2 k
  exact ⟨l, by linarith, C, hC⟩

end Podc.UncoordinatedBeeps
