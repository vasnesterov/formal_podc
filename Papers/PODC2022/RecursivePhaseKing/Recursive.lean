import Papers.PODC2022.RecursivePhaseKing.Subroutines

/-!
# Algorithm 8: spec-level pieces of Section 4

* Lemma 4.3 (`lemma_4_3`): if node `1` is faulty, one of the two halves `V₀ = {2, …, ⌈n/2⌉}`,
  `V₁ = {⌈n/2⌉ + 1, …, n}` has fewer than a third faulty nodes (nodes are `Fin n`, node `i` is the
  paper's `i + 1`).
* The time recurrence of Lemma 4.5 (`lemma_4_5_time`): if a running-time function satisfies the
  three case bounds of the paper's proof (node `1` correct; node `1` faulty and `V₀` good; node `1`
  faulty and `V₀` bad, in which case the call on `V₀` times out after the known bound plus `3`
  rounds and the call on `V₁` is good), then it is at most `C (f + 1)` with the explicit constant
  `C = c₀ + 3 + 2 c₁`. This is the arithmetic of the induction; the case bounds themselves
  (Theorem 4.1, Lemma 4.2, the compiled constant-round subroutines) are hypotheses.
* `alg2_split_term`: in the termination check (Algorithm 2) with `n = 7`, `t = 2`, the faulty nodes
  can make some correct nodes terminate and others not. In Algorithm 8 these terminated nodes do
  not take part in the later calls of Algorithm 7; see `README.md` for why this breaks the proof
  of Lemma 4.5 / Corollary 4.4 (formal counterexample at the level of Algorithm 7 in
  `VotingBarrier.lean`).
-/

namespace RecursivePhaseKing

open Finset

/-- `|V₀| = ⌈n/2⌉ - 1`. -/
def v0 (n : ℕ) : ℕ := (n + 1) / 2 - 1

/-- `|V₁| = ⌊n/2⌋`. -/
def v1 (n : ℕ) : ℕ := n / 2

/-- `V₀ = {2, …, ⌈n/2⌉}` (0-based: `1 ≤ i ≤ ⌈n/2⌉ - 1`). -/
def V0 (n : ℕ) : Finset (Fin n) := univ.filter fun i => 1 ≤ i.val ∧ i.val + 1 ≤ (n + 1) / 2

/-- `V₁ = {⌈n/2⌉ + 1, …, n}` (0-based: `⌈n/2⌉ ≤ i`). -/
def V1 (n : ℕ) : Finset (Fin n) := univ.filter fun i => (n + 1) / 2 ≤ i.val

/-- Lemma 4.3 of [LS22]: if node `1` is faulty (and fewer than a third of all nodes are), one of
`V₀`, `V₁` has fewer than a third faulty nodes. -/
theorem lemma_4_3 {n : ℕ} (F : Finset (Fin n)) (h3 : 3 * F.card < n) (h0 : ∀ i : Fin n,
    i.val = 0 → i ∈ F) :
    3 * (V0 n ∩ F).card < (V0 n).card ∨ 3 * (V1 n ∩ F).card < (V1 n).card := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0', h1'⟩ := hcon
  have hn : 0 < n := by omega
  set z : Fin n := ⟨0, hn⟩
  have hz : z ∈ F := h0 z rfl
  -- `{0}`, `V₀`, `V₁` partition the nodes
  have hpart : (univ : Finset (Fin n)) = insert z (V0 n ∪ V1 n) := by
    ext i
    simp only [mem_univ, mem_insert, mem_union, V0, V1, mem_filter, true_and, true_iff]
    by_cases h : i.val = 0
    · left; exact Fin.ext h
    · right; omega
  have hdisj : Disjoint (V0 n) (V1 n) := by
    rw [disjoint_left]; intro i h h'
    simp only [V0, V1, mem_filter, mem_univ, true_and] at h h'; omega
  have hz' : z ∉ V0 n ∪ V1 n := by simp [V0, V1, z]; omega
  have hcardn : n = 1 + (V0 n).card + (V1 n).card := by
    have := congrArg card hpart
    rw [card_univ, Fintype.card_fin, card_insert_of_notMem hz', card_union_of_disjoint hdisj]
      at this
    omega
  have hcardF : 1 + (V0 n ∩ F).card + (V1 n ∩ F).card ≤ F.card := by
    have hsub : insert z ((V0 n ∩ F) ∪ (V1 n ∩ F)) ⊆ F := by
      intro i hi
      simp only [mem_insert, mem_union, mem_inter] at hi
      rcases hi with rfl | ⟨-, h⟩ | ⟨-, h⟩
      · exact hz
      · exact h
      · exact h
    have hz'' : z ∉ (V0 n ∩ F) ∪ (V1 n ∩ F) := by
      intro h; apply hz'
      simp only [mem_union, mem_inter] at h ⊢; tauto
    have := card_le_card hsub
    rw [card_insert_of_notMem hz'', card_union_of_disjoint
      (Disjoint.mono inter_subset_left inter_subset_left hdisj)] at this
    omega
  omega

theorem card_V0 (n : ℕ) : (V0 n).card = v0 n := by
  have : (V0 n).map Fin.valEmbedding = Icc 1 ((n + 1) / 2 - 1) := by
    ext x
    simp only [mem_map, V0, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hx; exact ⟨⟨x, by omega⟩, by simp only; omega, rfl⟩
  rw [← card_map, this, Nat.card_Icc, v0]; omega

theorem card_V1 (n : ℕ) : (V1 n).card = v1 n := by
  have : (V1 n).map Fin.valEmbedding = Ico ((n + 1) / 2) n := by
    ext x
    simp only [mem_map, V1, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i.isLt⟩
    · intro hx; exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  rw [← card_map, this, Nat.card_Ico, v1]; omega

/-- The time recurrence of Lemma 4.5 of [LS22]. `time n f` is a worst-case running time of
Algorithm 8 on `n` nodes with `f < n/3` faults. Its three case bounds are hypotheses:
* node 1 correct: at most `c₀` rounds (constant-round compiled code);
* node 1 faulty, `f = f₀ + f₁ + 1` with `f_j` faults in `V_j`:
  - `V₀` good (`3 f₀ < |V₀|`): `c₀ + (time |V₀| f₀ + c₁)` (the first call of Algorithm 7 succeeds
    after the recursive call plus `c₁` rounds, Lemma 4.2);
  - `V₀` bad: the first call of Algorithm 7 times out after `C ⌈|V₀|/3⌉ + 3 + c₁` rounds (its loop
    length, using the known bound `C ⌈k/3⌉` for consensus on `k` nodes), and `V₁` is good
    (Lemma 4.3): `c₀ + (C ⌈|V₀|/3⌉ + 3 + c₁) + (time |V₁| f₁ + c₁)`.
Then `time n f ≤ C (f + 1)` for `C = c₀ + 3 + 2 c₁` (or larger). -/
theorem lemma_4_5_time (c₀ c₁ C : ℕ) (hC : c₀ + 3 + 2 * c₁ ≤ C) (time : ℕ → ℕ → ℕ)
    (h : ∀ n f, 3 * f < n →
      time n f ≤ c₀ ∨
      ∃ f₀ f₁, f = f₀ + f₁ + 1 ∧ f₀ ≤ v0 n ∧ f₁ ≤ v1 n ∧
        ((3 * f₀ < v0 n ∧ time n f ≤ c₀ + (time (v0 n) f₀ + c₁)) ∨
         (v0 n ≤ 3 * f₀ ∧ 3 * f₁ < v1 n ∧
          time n f ≤ c₀ + (C * ((v0 n + 2) / 3) + 3 + c₁) + (time (v1 n) f₁ + c₁)))) :
    ∀ n f, 3 * f < n → time n f ≤ C * (f + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf
    rcases h n f hf with h1 | ⟨f₀, f₁, rfl, hf₀, hf₁, ⟨hg, ht⟩ | ⟨hb, hg, ht⟩⟩
    · nlinarith
    · have hv : v0 n < n := by unfold v0; omega
      have := ih (v0 n) hv f₀ hg
      nlinarith
    · have hv : v1 n < n := by unfold v1; omega
      have h1 := ih (v1 n) hv f₁ hg
      have h2 : C * ((v0 n + 2) / 3) ≤ C * f₀ := Nat.mul_le_mul_left _ (by omega)
      nlinarith

/-! ### Termination checks can split -/

/-- First-round receptions of an instance of Algorithm 2 (as termination check) on `n = 7` nodes, `t = 2`, faulty nodes
`0, 1`: correct inputs `1,1,1,1,0` (nodes `2–6`); the faulty nodes send `1` in the first round only
to nodes `2, 3, 4`, and in the second round only to nodes `2, 3`. -/
def splitR1 (i q : Fin 7) : Option Bool :=
  if q.val ≤ 1 then (if i.val ≤ 4 then some true else none) else some (decide (q.val ≤ 5))

/-- See `splitR1`. -/
def splitInst : Alg2Inst ({0, 1} : Finset (Fin 7)) 2 where
  x i := decide (i.val ≤ 5)
  pick _ := true
  r1 := splitR1
  r2 i q := if q.val ≤ 1 then (if i.val ≤ 3 then some true else none) else vote 5 (splitR1 q)
  h1 i _ q hq := by
    have : ¬ q.val ≤ 1 := by
      intro h; apply hq; fin_cases q <;> simp_all
    simp [splitR1, this]
  h2 i _ q hq := by
    have : ¬ q.val ≤ 1 := by
      intro h; apply hq; fin_cases q <;> simp_all
    simp [this]

/-- In `splitInst`, the correct nodes `2, 3` terminate (`term = 1`), the correct nodes `4, 5, 6`
do not, and all correct nodes output `1` (termination agreement). -/
theorem alg2_split_term :
    splitInst.s 2 = true ∧ splitInst.s 3 = true ∧ splitInst.s 4 = false ∧
      splitInst.s 5 = false ∧ splitInst.s 6 = false ∧ ∀ i : Fin 7, 2 ≤ i.val → splitInst.o i = true := by
  decide

end RecursivePhaseKing
