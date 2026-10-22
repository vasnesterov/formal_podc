import Mathlib
import Cslib.Foundations.Combinatorics.Labelling

/-!
# Generalized symmetry breaking (GSB) tasks: definitions and feasibility

Imbs, Rajsbaum, Raynal, *The universe of symmetry breaking tasks*, PODC 2011 (full version:
IRISA PI 1965, January 2011). Numbering follows the full version.

A GSB task `⟨n, m, ℓ⃗, u⃗⟩` is *inputless*: its set of legal output vectors does not depend on the
input vector (the identities). An output vector is a map `O : Fin n → Fin m` (process ↦ decided
value; the paper's values `1..m` are `0..m-1` here), and it is legal iff every value `v` is decided
by at least `ℓ v` and at most `u v` processes (Definition 2).

## Main definitions
* `cnt O v` — `#_v(O)`, the number of processes deciding `v`;
* `gsb n ℓ u` — the output vectors of the asymmetric `⟨n, m, ℓ⃗, u⃗⟩`-GSB task;
* `sgsb n m ℓ u` — the symmetric `⟨n, m, ℓ, u⟩`-GSB task;
* instances: renaming `⟨n,m,0,1⟩`, perfect renaming `⟨n,n,1,1⟩`, `k`-WSB, `k`-slot, election.

## Main statements
* `lemma_1` — corrected Lemma 1: feasible iff `ℓ v ≤ u v` for all `v` and `∑ ℓ ≤ n ≤ ∑ u`;
* `lemma_1_false` — Lemma 1 as stated (without `ℓ v ≤ u v`) is false;
* `lemma_2` — symmetric feasibility `m ℓ ≤ n ≤ m u`;
* `lemma_4`, `lemma_5` — monotonicity in the bounds.
-/

namespace Podc.SymmetryBreakingTasks

open Finset

variable {n m : ℕ}

/-- `#_v(O)`: the number of entries of the output vector `O` equal to `v`. -/
def cnt (O : Fin n → Fin m) (v : Fin m) : ℕ := #{i | O i = v}

/-- Definition 2: the output vectors of the asymmetric `⟨n, m, ℓ⃗, u⃗⟩`-GSB task
(values `Fin m`). -/
def gsb (n : ℕ) (ℓ u : Fin m → ℕ) : Set (Fin n → Fin m) :=
  {O | ∀ v, ℓ v ≤ cnt O v ∧ cnt O v ≤ u v}

/-- The output vectors of the symmetric `⟨n, m, ℓ, u⟩`-GSB task. -/
def sgsb (n m ℓ u : ℕ) : Set (Fin n → Fin m) := gsb n (fun _ => ℓ) (fun _ => u)

@[simp] lemma mem_gsb {ℓ u : Fin m → ℕ} {O : Fin n → Fin m} :
    O ∈ gsb n ℓ u ↔ ∀ v, ℓ v ≤ cnt O v ∧ cnt O v ≤ u v := Iff.rfl

@[simp] lemma mem_sgsb {ℓ u : ℕ} {O : Fin n → Fin m} :
    O ∈ sgsb n m ℓ u ↔ ∀ v, ℓ ≤ cnt O v ∧ cnt O v ≤ u := Iff.rfl

/-- The counts of an output vector add up to the number of processes. -/
lemma sum_cnt (O : Fin n → Fin m) : ∑ v, cnt O v = n := by
  have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ) (f := O)
    (fun _ _ => mem_univ _)
  simpa [cnt] using this.symm

lemma cnt_le (O : Fin n → Fin m) (v : Fin m) : cnt O v ≤ n := by
  simpa [cnt] using card_filter_le (univ : Finset (Fin n)) (fun i => O i = v)

/-- The count of `v` plus the counts of the other `m - 1` values is `n`. -/
lemma cnt_add_sum_erase (O : Fin n → Fin m) (v : Fin m) :
    cnt O v + ∑ w ∈ univ.erase v, cnt O w = n := by
  rw [add_sum_erase _ _ (mem_univ v), sum_cnt]

/-- If every count is at most `u`, every count is at least `n - u (m - 1)`. -/
lemma sub_le_cnt {u : ℕ} {O : Fin n → Fin m} (h : ∀ w, cnt O w ≤ u) (v : Fin m) :
    n - u * (m - 1) ≤ cnt O v := by
  have h1 := cnt_add_sum_erase O v
  have h2 : ∑ w ∈ univ.erase v, cnt O w ≤ (univ.erase v).card * u :=
    sum_le_card_nsmul _ _ _ (fun w _ => h w) |>.trans_eq (by simp)
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
  rw [mul_comm] at h2
  omega

/-- If every count is at least `ℓ`, every count is at most `n - ℓ (m - 1)`. -/
lemma cnt_le_sub {ℓ : ℕ} {O : Fin n → Fin m} (h : ∀ w, ℓ ≤ cnt O w) (v : Fin m) :
    cnt O v ≤ n - ℓ * (m - 1) := by
  have h1 := cnt_add_sum_erase O v
  have h2 : (univ.erase v).card • ℓ ≤ ∑ w ∈ univ.erase v, cnt O w :=
    card_nsmul_le_sum _ _ _ (fun w _ => h w)
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, smul_eq_mul, mul_comm] at h2
  omega

/-- Every vector of counts adding up to `n` (with values in prescribed ranges) is realized. -/
lemma exists_of_bounds (lo hi : Fin m → ℕ) (hle : ∀ v, lo v ≤ hi v) (hlo : ∑ v, lo v ≤ n)
    (hhi : n ≤ ∑ v, hi v) : ∃ O : Fin n → Fin m, ∀ v, lo v ≤ cnt O v ∧ cnt O v ≤ hi v := by
  obtain ⟨g, hg⟩ := Fintype.exists_fin_labelling (α := Fin n) lo hi hle (by simpa using hlo)
    (by simpa using hhi)
  exact ⟨g, hg⟩

/-- Every count vector is realized by an output vector. -/
lemma exists_cnt_eq (c : Fin m → ℕ) (hc : ∑ v, c v = n) : ∃ O : Fin n → Fin m, cnt O = c := by
  obtain ⟨O, hO⟩ := exists_of_bounds c c (fun _ => le_rfl) hc.le hc.ge
  exact ⟨O, funext fun v => le_antisymm (hO v).2 (hO v).1⟩

/-- `∑ v, (if v = v₀ then a else b) = a + (m - 1) b`. -/
lemma sum_ite_eq_single (v₀ : Fin m) (a b : ℕ) :
    ∑ v, (if v = v₀ then a else b) = a + b * (m - 1) := by
  rw [← add_sum_erase _ _ (mem_univ v₀),
    sum_congr rfl (g := fun _ => b) (fun v hv => by simp [ne_of_mem_erase hv])]
  simp [card_erase_of_mem, mul_comm]

/-- An output vector in which `v₀` is decided exactly `a` times and every other value between
`lo` and `hi` times exists as soon as the numbers add up. -/
lemma exists_cnt_single (v₀ : Fin m) {a lo hi : ℕ} (hle : lo ≤ hi) (h1 : a + lo * (m - 1) ≤ n)
    (h2 : n ≤ a + hi * (m - 1)) :
    ∃ O : Fin n → Fin m, cnt O v₀ = a ∧ ∀ v, v ≠ v₀ → lo ≤ cnt O v ∧ cnt O v ≤ hi := by
  obtain ⟨O, hO⟩ := exists_of_bounds (n := n) (fun v => if v = v₀ then a else lo)
    (fun v => if v = v₀ then a else hi) (fun v => by split_ifs <;> omega)
    (by rw [sum_ite_eq_single]; exact h1) (by rw [sum_ite_eq_single]; exact h2)
  refine ⟨O, ?_, fun v hv => ?_⟩
  · have := hO v₀; simp only [ite_true] at this; omega
  · have := hO v; simpa [hv] using this

/-! ### Feasibility (Lemmas 1 and 2) -/

/-- Lemma 1 (corrected): the asymmetric `⟨n, m, ℓ⃗, u⃗⟩`-GSB task is feasible (has an output
vector) iff `ℓ v ≤ u v` for every `v` and `∑ ℓ ≤ n ≤ ∑ u`. The paper omits `ℓ v ≤ u v`. -/
theorem lemma_1 (ℓ u : Fin m → ℕ) :
    (gsb n ℓ u).Nonempty ↔ (∀ v, ℓ v ≤ u v) ∧ ∑ v, ℓ v ≤ n ∧ n ≤ ∑ v, u v := by
  constructor
  · rintro ⟨O, hO⟩
    refine ⟨fun v => (hO v).1.trans (hO v).2, ?_, ?_⟩
    · rw [← sum_cnt O]; exact sum_le_sum fun v _ => (hO v).1
    · rw [← sum_cnt O]; exact sum_le_sum fun v _ => (hO v).2
  · rintro ⟨hle, hlo, hhi⟩
    exact exists_of_bounds ℓ u hle hlo hhi

/-- Lemma 1 as stated in the paper ("feasible iff `∑ ℓ ≤ n ≤ ∑ u`") is false:
`n = 3`, `ℓ⃗ = [2, 0]`, `u⃗ = [1, 5]` satisfies `2 ≤ 3 ≤ 6` but value `1` would have to be decided
at least twice and at most once. -/
theorem lemma_1_false :
    ¬ ∀ (n m : ℕ) (ℓ u : Fin m → ℕ), (gsb n ℓ u).Nonempty ↔ ∑ v, ℓ v ≤ n ∧ n ≤ ∑ v, u v := by
  intro h
  have h1 := (h 3 2 ![2, 0] ![1, 5]).2 (by decide)
  rw [lemma_1] at h1
  exact absurd (h1.1 0) (by decide)

/-- Lemma 2: the symmetric `⟨n, m, ℓ, u⟩`-GSB task is feasible iff `m ℓ ≤ n ≤ m u`. -/
theorem lemma_2 (n m ℓ u : ℕ) : (sgsb n m ℓ u).Nonempty ↔ m * ℓ ≤ n ∧ n ≤ m * u := by
  rw [sgsb, lemma_1]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, h1, h2⟩
    exact Nat.le_of_mul_le_mul_left (h1.trans h2) (Nat.pos_of_ne_zero (fun h => by
      subst h; exact v.elim0))

/-- Feasibility of the symmetric task. -/
def Feasible (n m ℓ u : ℕ) : Prop := m * ℓ ≤ n ∧ n ≤ m * u

lemma Feasible.nonempty {ℓ u : ℕ} (h : Feasible n m ℓ u) : (sgsb n m ℓ u).Nonempty :=
  (lemma_2 n m ℓ u).2 h

lemma feasible_iff {ℓ u : ℕ} : Feasible n m ℓ u ↔ (sgsb n m ℓ u).Nonempty :=
  (lemma_2 n m ℓ u).symm

lemma Feasible.le {ℓ u : ℕ} (h : Feasible n m ℓ u) (hm : 1 ≤ m) : ℓ ≤ u :=
  Nat.le_of_mul_le_mul_left (h.1.trans h.2) hm

/-! ### Monotonicity (Lemmas 4 and 5) -/

/-- Lemma 4: increasing the upper bound can only add output vectors. -/
theorem lemma_4 {ℓ u u' : ℕ} (h : u ≤ u') : sgsb n m ℓ u ⊆ sgsb n m ℓ u' :=
  fun _ hO v => ⟨(hO v).1, (hO v).2.trans h⟩

/-- Lemma 5: decreasing the lower bound can only add output vectors. -/
theorem lemma_5 {ℓ ℓ' u : ℕ} (h : ℓ' ≤ ℓ) : sgsb n m ℓ u ⊆ sgsb n m ℓ' u :=
  fun _ hO v => ⟨h.trans (hO v).1, (hO v).2⟩

/-! ### Instances of GSB tasks (Section 3.2) -/

/-- `m`-renaming is the `⟨n, m, 0, 1⟩`-GSB task: its output vectors are the injective ones. -/
theorem sgsb_zero_one (n m : ℕ) : sgsb n m 0 1 = {O : Fin n → Fin m | Function.Injective O} := by
  ext O
  simp only [mem_sgsb, zero_le, true_and, Set.mem_ofPred_eq, cnt]
  constructor
  · intro h i j hij
    by_contra hne
    have : ({i, j} : Finset (Fin n)) ⊆ ({k | O k = O i} : Finset (Fin n)) := by
      intro k hk; simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [hij]
    have := (card_le_card this).trans (h (O i))
    rw [card_pair hne] at this; omega
  · intro h v
    rw [card_le_one]
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact h (ha.trans hb.symm)

/-- Perfect renaming is the `⟨n, n, 1, 1⟩`-GSB task: its output vectors are the bijections. -/
theorem sgsb_one_one (n : ℕ) : sgsb n n 1 1 = {O : Fin n → Fin n | Function.Bijective O} := by
  ext O
  constructor
  · intro h
    have hinj : Function.Injective O := by
      have : O ∈ sgsb n n 0 1 := lemma_5 (Nat.zero_le 1) h
      rw [sgsb_zero_one] at this; exact this
    exact ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  · intro h v
    have hinj : O ∈ sgsb n n 0 1 := by rw [sgsb_zero_one]; exact h.1
    refine ⟨?_, (hinj v).2⟩
    obtain ⟨i, rfl⟩ := h.2 v
    exact card_pos.2 ⟨i, by simp⟩

/-- The `k`-weak symmetry breaking task `⟨n, 2, k, n - k⟩` (`k = 1`: WSB). -/
def kWSB (n k : ℕ) : Set (Fin n → Fin 2) := sgsb n 2 k (n - k)

/-- The `k`-slot task `⟨n, k, 1, n⟩`: every value is decided at least once. -/
def kSlot (n k : ℕ) : Set (Fin n → Fin k) := sgsb n k 1 n

/-- Section 3.2: `⟨n, k, 1, n⟩` and `⟨n, k, 1, n - k + 1⟩` are synonyms (for `k ≥ 1`). -/
theorem kSlot_eq (hk : 1 ≤ k) : kSlot n k = sgsb n k 1 (n - k + 1) := by
  ext O
  simp only [kSlot, mem_sgsb]
  refine ⟨fun h v => ⟨(h v).1, ?_⟩, fun h v => ⟨(h v).1, cnt_le O v⟩⟩
  have := cnt_le_sub (fun w => (h w).1) v
  omega

/-- WSB is the 2-slot task, and `⟨n,2,1,n-1⟩`, `⟨n,2,0,n-1⟩`, `⟨n,2,1,n⟩` are synonyms
(Sections 3.2 and 4; `n ≥ 1`). -/
theorem wsb_synonyms (hn : 1 ≤ n) :
    kWSB n 1 = kSlot n 2 ∧ kWSB n 1 = sgsb n 2 0 (n - 1) := by
  refine ⟨?_, ?_⟩
  · ext O
    simp only [kWSB, kSlot, mem_sgsb]
    refine ⟨fun h v => ⟨(h v).1, (h v).2.trans (Nat.sub_le n 1)⟩, fun h v => ⟨(h v).1, ?_⟩⟩
    have := cnt_le_sub (fun w => (h w).1) v
    simpa using this
  · ext O
    simp only [kWSB, mem_sgsb, zero_le, true_and]
    refine ⟨fun h v => (h v).2, fun h v => ⟨?_, h v⟩⟩
    have := sub_le_cnt h v
    omega

/-- The election task: exactly one process decides `0`, the other `n - 1` decide `1`
(an asymmetric GSB task). -/
def election (n : ℕ) : Set (Fin n → Fin 2) := gsb n ![1, n - 1] ![1, n - 1]

/-- Election outputs are WSB outputs (`n ≥ 2`), so election solves WSB trivially (Section 5.3). -/
theorem election_subset_wsb (hn : 2 ≤ n) : election n ⊆ kWSB n 1 := by
  intro O hO v
  have h0 := hO 0; have h1 := hO 1
  simp at h0 h1
  fin_cases v <;> simp <;> omega

end Podc.SymmetryBreakingTasks
