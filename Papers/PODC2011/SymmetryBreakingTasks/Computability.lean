import Papers.PODC2011.SymmetryBreakingTasks.Structure
import Podc.Computability.Distributed.IteratedModel.PostProcess

/-!
# Complexity and computability of GSB tasks (Section 5)

* Theorem 8 (perfect renaming is universal): explicit output maps (`theorem_8_asymm`,
  `theorem_8_symm`) and the algorithmic statement in CSLib's iterated model (`theorem_8`): any
  algorithm solving perfect renaming, post-processed by a fixed map, solves any feasible GSB task.
* Theorem 9 (solvability without communication) and Corollaries 2–4. "No communication" means
  that a process decides from its own identity only, with the same decision function `δ` for all
  processes (index independence). `noComm_iff` shows that this is exactly 0-round solvability by an
  index-independent algorithm of CSLib's iterated model (in any model).
* Model sensitivity of Theorem 9: with index-*dependent* algorithms, perfect renaming is solvable
  without communication (`perfectRenaming_indexDependent`); with *comparison-based* algorithms
  (which Section 2.3 imposes on all algorithms), the decision function is constant and
  Theorem 9's "if" direction fails (`noComm_comparisonBased_iff`, `theorem_9_comparisonBased_false`).
* Theorem 10 and Corollary 5 are reductions to cited impossibility results; we prove the
  reductions (`theorem_10`, `corollary_5`) with the cited results as hypotheses.

Identities are `Fin N` (the paper's `1..N`); Theorem 9 uses `N = 2n - 1` as in the paper.
-/

namespace Podc.SymmetryBreakingTasks

open Finset Cslib.Iterated

variable {n m N ℓ u : ℕ}

/-! ### Theorem 8: perfect renaming is universal -/

/-- Counts are invariant under permuting the processes. -/
lemma cnt_comp_bijective {O : Fin n → Fin m} {π : Fin n → Fin n} (hπ : Function.Bijective π)
    (v : Fin m) : cnt (O ∘ π) v = cnt O v :=
  card_equiv (Equiv.ofBijective π hπ) (by simp)

/-- Theorem 8, asymmetric case: given a feasible `⟨n, m, ℓ⃗, u⃗⟩`-GSB task, fix one of its output
vectors `V`; a process that obtained the name `d` in perfect renaming decides `V[d]`. -/
theorem theorem_8_asymm {ℓ u : Fin m → ℕ} (h : (gsb n ℓ u).Nonempty) :
    ∃ V : Fin n → Fin m, ∀ π ∈ sgsb n n 1 1, V ∘ π ∈ gsb n ℓ u := by
  obtain ⟨V, hV⟩ := h
  refine ⟨V, fun π hπ v => ?_⟩
  rw [sgsb_one_one] at hπ
  rw [cnt_comp_bijective hπ]; exact hV v

/-- The map `d ↦ d mod m` of Theorem 8 (`m ≥ 1`). -/
def modMap (hm : 1 ≤ m) (d : Fin n) : Fin m := ⟨d % m, Nat.mod_lt _ hm⟩

/-- Among the names `0, …, n-1`, exactly `⌊n/m⌋ + [v < n mod m]` are `≡ v (mod m)`. -/
lemma card_mod_eq (hm : 1 ≤ m) (v : Fin m) :
    #{d : Fin n | (d : ℕ) % m = v} = balanced n m v := by
  have h := Nat.count_modEq_card n hm v
  rw [Nat.mod_eq_of_lt v.isLt, Nat.count_eq_card_filter_range] at h
  rw [balanced, ← h]
  refine card_bij (fun d _ => (d : ℕ)) ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, mem_univ, true_and, mem_range] at hd ⊢
    exact ⟨d.isLt, by rw [Nat.ModEq, hd, Nat.mod_eq_of_lt v.isLt]⟩
  · intro a _ b _ h; exact Fin.ext h
  · intro x hx
    simp only [mem_filter, mem_range] at hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    have := hx.2; rw [Nat.ModEq, Nat.mod_eq_of_lt v.isLt] at this; exact this

/-- Theorem 8, symmetric case: after perfect renaming, value `v` is decided exactly
`⌊n/m⌋ + [v < n mod m]` times (the balanced kernel vector) by `d ↦ d mod m`. -/
lemma cnt_modMap (hm : 1 ≤ m) {π : Fin n → Fin n} (hπ : π ∈ sgsb n n 1 1) (v : Fin m) :
    cnt (modMap hm ∘ π) v = balanced n m v := by
  rw [sgsb_one_one] at hπ
  rw [cnt_comp_bijective hπ]
  simp only [cnt, modMap, Fin.ext_iff]
  exact card_mod_eq hm v

/-- Theorem 8, symmetric case: for a feasible `⟨n, m, ℓ, u⟩`-GSB task, a process that obtained the
name `d` in perfect renaming decides `d mod m`. -/
theorem theorem_8_symm (hm : 1 ≤ m) (h : Feasible n m ℓ u) :
    ∀ π ∈ sgsb n n 1 1, modMap hm ∘ π ∈ sgsb n m ℓ u := by
  intro π hπ
  rw [mem_sgsb]; intro v
  rw [cnt_modMap hm hπ]
  exact ((mem_kernelSet.1 (balanced_mem_kernelSet hm h)).1.2 v)

/-- A GSB task (given by its output vectors `S`) as a task of CSLib's iterated model: the inputs
are distinct identities in `Fin N`, any set of processes may participate, and the decisions of the
participants must extend to an output vector in `S` (validity of Definition 1). -/
def gsbTask (N : ℕ) (S : Set (Fin n → Fin m)) : Task (Fin n) (Fin N) (Fin m) where
  Inp := {p | Function.Injective p.2}
  Δ _ _ := S

/-- Theorem 8: any algorithm solving perfect renaming `⟨n, n, 1, 1⟩` (in any iterated model, with
any number of rounds), followed by a fixed local map, solves any feasible asymmetric GSB task;
index independence is preserved. -/
theorem theorem_8 {A B : Type} (M : Model (Fin n) A B) {t : ℕ} {ℓ u : Fin m → ℕ}
    (h : (gsb n ℓ u).Nonempty) :
    ∃ g : Fin n → Fin m, ∀ alg : Alg (Fin n) (Fin N) A B (Fin n) t,
      Solves M (gsbTask N (sgsb n n 1 1)) alg →
        Solves M (gsbTask N (gsb n ℓ u)) (alg.mapDec g) ∧
        (alg.IndexIndependent → (alg.mapDec g).IndexIndependent) := by
  obtain ⟨V, hV⟩ := theorem_8_asymm h
  exact ⟨V, fun alg halg => ⟨halg.mapDec V subset_rfl fun _ _ _ y hy => hV y hy,
    fun hI => hI.mapDec V⟩⟩

/-! ### Theorem 9: solvability without communication -/

/-- A GSB task with output vectors `S` is solvable without communication (identities in `Fin N`):
some decision function `δ`, used by every process on its own identity, produces an output vector
in `S` for every assignment of distinct identities. -/
def NoCommSolvable (N : ℕ) (S : Set (Fin n → Fin m)) : Prop :=
  ∃ δ : Fin N → Fin m, ∀ x : Fin n → Fin N, Function.Injective x → δ ∘ x ∈ S

/-- `NoCommSolvable` is 0-round solvability by an index-independent algorithm of CSLib's iterated
model (in any model `M`; after 0 rounds a process knows only its identity). -/
theorem noComm_iff {A B : Type} [Inhabited A] (M : Model (Fin n) A B) (hn : 1 ≤ n)
    (S : Set (Fin n → Fin m)) :
    (∃ alg : Alg (Fin n) (Fin N) A B (Fin m) 0, alg.IndexIndependent ∧
      Solves M (gsbTask N S) alg) ↔ NoCommSolvable N S := by
  constructor
  · rintro ⟨alg, hI, hS⟩
    refine ⟨alg.dec ⟨0, hn⟩, fun x hx => ?_⟩
    obtain ⟨y, hy, hdec⟩ := hS univ x hx x Reach.zero
    have : alg.dec ⟨0, hn⟩ ∘ x = y :=
      funext fun i => by rw [← hdec i (mem_univ i), hI.2 i ⟨0, hn⟩]; rfl
    rw [this]; exact hy
  · rintro ⟨δ, hδ⟩
    refine ⟨⟨fun _ _ _ => default, fun _ v => δ v⟩, ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩, ?_⟩
    intro I x hx V hV
    rw [reach_zero_iff] at hV
    rw [hV]
    exact ⟨δ ∘ x, hδ x hx, fun _ _ => rfl⟩

/-- Index independence matters: with index-dependent decision functions, perfect renaming
`⟨n, n, 1, 1⟩` is solvable with 0 rounds (process `i` decides `i`), although by Theorem 9 it is
not solvable without communication for `n ≥ 2`. -/
theorem perfectRenaming_indexDependent {A B : Type} [Inhabited A] (M : Model (Fin n) A B) :
    Solves M (gsbTask N (sgsb n n 1 1))
      (⟨fun _ _ _ => default, fun i _ => i⟩ : Alg (Fin n) (Fin N) A B (Fin n) 0) := by
  intro I x _ V _
  exact ⟨id, by rw [sgsb_one_one]; exact Function.bijective_id, fun _ _ => rfl⟩

/-- Distinct identities can be chosen inside any set of at least `n` identities. -/
lemma exists_injective_mem (T : Finset (Fin N)) (hT : n ≤ #T) :
    ∃ x : Fin n → Fin N, Function.Injective x ∧ ∀ i, x i ∈ T := by
  obtain ⟨T', hT', hc⟩ := exists_subset_card_eq hT
  exact ⟨T'.orderEmbOfFin hc, (T'.orderEmbOfFin hc).injective,
    fun i => hT' (T'.orderEmbOfFin_mem hc i)⟩

/-- Distinct identities can be chosen so that a given set of at most `n` identities is used. -/
lemma exists_injective_superset (T : Finset (Fin N)) (hT : #T ≤ n) (hn : n ≤ N) :
    ∃ x : Fin n → Fin N, Function.Injective x ∧ ∀ a ∈ T, ∃ i, x i = a := by
  obtain ⟨T', hT', -, hc⟩ := exists_subsuperset_card_eq (subset_univ T) hT (by simpa using hn)
  refine ⟨T'.orderEmbOfFin hc, (T'.orderEmbOfFin hc).injective, fun a ha => ?_⟩
  have : a ∈ Set.range (T'.orderEmbOfFin hc) := by rw [range_orderEmbOfFin]; exact hT' ha
  exact this

/-- The decision function `a ↦ ⌊a / c⌋` (groups of `c` consecutive identities), `N ≤ m c`. -/
def divMap {c : ℕ} (hN : N ≤ m * c) (a : Fin N) : Fin m :=
  ⟨a / c, Nat.div_lt_of_lt_mul (by have := a.isLt; rw [mul_comm] at hN; omega)⟩

/-- `divMap` solves `⟨n, m, 0, c⟩` without communication. -/
lemma div_solves {c : ℕ} (hN : N ≤ m * c) (x : Fin n → Fin N) (hx : Function.Injective x) :
    divMap hN ∘ x ∈ sgsb n m 0 c := by
  rw [mem_sgsb]; intro v
  refine ⟨Nat.zero_le _, ?_⟩
  simp only [cnt, Function.comp_apply, Fin.ext_iff, divMap]
  calc #{i | (x i : ℕ) / c = v} ≤ #((Ico (v * c) (v * c + c)).filter (· < N)) := by
        refine card_le_card_of_injOn (fun i => (x i : ℕ)) (fun i hi => ?_) ?_
        · simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hi
          simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq]
          rcases Nat.eq_zero_or_pos c with hc | hc
          · subst hc; simp at hN; exact absurd (x i).isLt (by omega)
          · refine ⟨⟨?_, ?_⟩, (x i).isLt⟩
            · rw [← hi]; exact Nat.div_mul_le_self _ _
            · rw [← hi]; have := Nat.lt_div_mul_add (a := (x i : ℕ)) hc; linarith
        · intro i _ j _ hij; exact hx (Fin.ext hij)
    _ ≤ #(Ico (v * c) (v * c + c)) := card_filter_le _ _
    _ = c := by simp

/-- Theorem 9: for `m > 1`, the `⟨n, m, ℓ, u⟩`-GSB task (identities `1..2n-1`) is solvable without
communication iff `ℓ = 0` and `⌈(2n-1)/m⌉ ≤ u`. -/
theorem theorem_9 (hm : 2 ≤ m) :
    NoCommSolvable (2 * n - 1) (sgsb n m ℓ u) ↔ ℓ = 0 ∧ (2 * n - 1) ⌈/⌉ m ≤ u := by
  constructor
  · rintro ⟨δ, hδ⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- no process: the only output vector is empty
      have := hδ Fin.elim0 (fun a => a.elim0)
      rw [mem_sgsb] at this
      have h0 := this ⟨0, by omega⟩
      simp [cnt] at h0
      exact ⟨by omega, by simp⟩
    constructor
    · -- some value is the decision of at most `n - 1` identities: avoid them
      by_contra hℓ
      obtain ⟨v, -, hv⟩ := exists_card_fiber_lt_of_card_lt_mul
        (s := (univ : Finset (Fin (2 * n - 1))))
        (t := (univ : Finset (Fin m))) (f := δ) (n := n) (by
          simp only [card_univ, Fintype.card_fin]
          have : 2 * n ≤ m * n := Nat.mul_le_mul_right n hm
          omega)
      obtain ⟨x, hx, hxT⟩ := exists_injective_mem (n := n)
        ({a | δ a ≠ v} : Finset (Fin (2 * n - 1)))
        (by
          have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * n - 1))))
            (fun a => δ a = v)
          simp only [card_univ, Fintype.card_fin] at this
          simp only [ne_eq]
          omega)
      have := (mem_sgsb.1 (hδ x hx) v).1
      have h0 : cnt (δ ∘ x) v = 0 := by
        simp only [cnt, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies,
          Function.comp_apply]
        intro i; simpa using hxT i
      omega
    · -- some value is the decision of more than `u` identities: use `u + 1` of them
      by_contra hu
      rw [ceilDiv_le_iff_le_mul (by omega)] at hu
      obtain ⟨v, -, hv⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s := (univ : Finset (Fin (2 * n - 1)))) (t := (univ : Finset (Fin m))) (f := δ) (n := u)
        (fun _ _ => mem_univ _) (by simp only [card_univ, Fintype.card_fin]; omega)
      have hun : u + 1 ≤ n := by
        have : m * u < 2 * n - 1 := by omega
        by_contra h'
        have : 2 * n ≤ m * u := by
          calc 2 * n ≤ 2 * u := by omega
            _ ≤ m * u := Nat.mul_le_mul_right u hm
        omega
      obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (s := ({a | δ a = v} : Finset _)) (n := u + 1)
        (by omega)
      obtain ⟨x, hx, hxT⟩ := exists_injective_superset (n := n) T (by omega) (by omega)
      have := (mem_sgsb.1 (hδ x hx) v).2
      have : u + 1 ≤ cnt (δ ∘ x) v := by
        rw [← hTc]
        refine card_le_card_of_surjOn x (fun a ha => ?_)
        obtain ⟨i, rfl⟩ := hxT a ha
        refine ⟨i, ?_, rfl⟩
        simpa using hT ha
      omega
  · rintro ⟨rfl, hu⟩
    have hN : 2 * n - 1 ≤ m * ((2 * n - 1) ⌈/⌉ m) :=
      le_smul_ceilDiv (a := m) (b := 2 * n - 1) (by omega)
    exact ⟨_, fun x hx => lemma_4 hu (div_solves hN x hx)⟩

/-- Section 5.2: a feasible GSB task with a single value (`m = 1`) is solvable without
communication. -/
theorem noComm_of_one (h : Feasible n 1 ℓ u) : NoCommSolvable N (sgsb n 1 ℓ u) := by
  refine ⟨fun _ => 0, fun x _ => mem_sgsb.2 fun v => ?_⟩
  have hv : v = 0 := Subsingleton.elim _ _
  have : cnt ((fun _ : Fin N => (0 : Fin 1)) ∘ x) v = n := by simp [cnt, hv]
  rw [this]; exact ⟨by simpa using h.1, by simpa using h.2⟩

/-- Corollary 2: `x`-bounded homonymous renaming `⟨n, ⌈(2n-1)/x⌉, 0, x⟩` is solvable without
communication (process with identity `a` decides `⌊a/x⌋`). -/
theorem corollary_2 {k : ℕ} (hk : 1 ≤ k) :
    NoCommSolvable (2 * n - 1) (sgsb n ((2 * n - 1) ⌈/⌉ k) 0 k) := by
  · have hN : 2 * n - 1 ≤ (2 * n - 1) ⌈/⌉ k * k := by
      have := le_smul_ceilDiv (a := k) (b := 2 * n - 1) hk
      simpa [mul_comm] using this
    exact ⟨_, fun x hx => div_solves hN x hx⟩

/-- Corollary 3: WSB `⟨n, 2, 1, n - 1⟩` is not solvable without communication. -/
theorem corollary_3 : ¬ NoCommSolvable (2 * n - 1) (kWSB n 1) := by
  intro h
  have := (theorem_9 (m := 2) (ℓ := 1) (u := n - 1) le_rfl).1 h
  omega

/-- Corollary 4: `k`-WSB `⟨n, 2, k, n - k⟩` (`k ≤ n`) is solvable without communication from
(non-adaptive) `2(n-k)`-renaming: a process with new name `a` decides `⌊a/(n-k)⌋`. -/
theorem corollary_4 (hk : k ≤ n) :
    ∃ δ : Fin (2 * (n - k)) → Fin 2, ∀ R ∈ sgsb n (2 * (n - k)) 0 1, δ ∘ R ∈ kWSB n k := by
  refine ⟨divMap (m := 2) (c := n - k) le_rfl, fun R hR => ?_⟩
  rw [sgsb_zero_one] at hR
  have h := div_solves (m := 2) (c := n - k) le_rfl R hR
  rw [mem_sgsb] at h
  refine mem_sgsb.2 fun v => ⟨?_, (h v).2⟩
  have := sub_le_cnt (fun w => (h w).2) v
  simp at this; omega

/-! ### Comparison-based algorithms without communication -/

/-- A decision function (no communication) is comparison-based: replacing the identities by others
in the same relative order does not change the decisions (Section 2.2). -/
def ComparisonBased (n : ℕ) (δ : Fin N → Fin m) : Prop :=
  ∀ x x' : Fin n → Fin N, Function.Injective x → Function.Injective x' →
    (∀ i j, x i < x j ↔ x' i < x' j) → ∀ i, δ (x i) = δ (x' i)

/-- Without communication, a comparison-based decision function gives the same decision to
consecutive identities. -/
lemma ComparisonBased.step {k : ℕ} (hN : k + 2 ≤ N) {δ : Fin N → Fin m}
    (h : ComparisonBased (k + 1) δ) (a : ℕ) (ha : a + 1 < N) :
    δ ⟨a, by omega⟩ = δ ⟨a + 1, ha⟩ := by
  obtain ⟨e, he, heT⟩ := exists_injective_mem (n := k)
    ({c | (c : ℕ) ≠ a ∧ (c : ℕ) ≠ a + 1} : Finset (Fin N)) (by
      have : ({c | (c : ℕ) ≠ a ∧ (c : ℕ) ≠ a + 1} : Finset (Fin N)) =
          univ \ {⟨a, by omega⟩, ⟨a + 1, ha⟩} := by
        ext c; simp [Fin.ext_iff]
      rw [this, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
        card_pair (by simp [Fin.ext_iff])]
      omega)
  simp only [mem_filter, mem_univ, true_and] at heT
  have key := h (Fin.cons ⟨a, by omega⟩ e) (Fin.cons ⟨a + 1, ha⟩ e)
    (Fin.cons_injective_iff.2 ⟨fun ⟨i, hi⟩ => (heT i).1 (by rw [hi]), he⟩)
    (Fin.cons_injective_iff.2 ⟨fun ⟨i, hi⟩ => (heT i).2 (by rw [hi]), he⟩) (fun i j => by
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp only [Fin.cons_zero, Fin.cons_succ, Fin.lt_def] <;>
        first | omega | (have := heT j; omega) | (have := heT i; omega))
    0
  simpa using key

/-- Without communication, a comparison-based decision function is constant (`n ≥ 1` processes,
`N ≥ n + 1` identities; e.g. `N = 2n - 1` with `n ≥ 2`). -/
theorem ComparisonBased.const (hn : 1 ≤ n) (hN : n + 1 ≤ N) {δ : Fin N → Fin m}
    (h : ComparisonBased n δ) (a b : Fin N) : δ a = δ b := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hall : ∀ c : ℕ, (hc : c < N) → δ ⟨c, hc⟩ = δ ⟨0, by omega⟩ := by
    intro c
    induction c with
    | zero => intro _; rfl
    | succ c ih => intro hc; rw [← h.step hN c hc, ih]
  rw [hall a a.isLt, hall b b.isLt]

/-- With comparison-based algorithms (as Section 2.3 requires of all algorithms), a GSB task with
`m ≥ 2` and `n ≥ 2` is solvable without communication iff `ℓ = 0` and `u ≥ n` (everybody decides
the same value). -/
theorem noComm_comparisonBased_iff (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∃ δ : Fin (2 * n - 1) → Fin m, ComparisonBased n δ ∧
      ∀ x : Fin n → Fin (2 * n - 1), Function.Injective x → δ ∘ x ∈ sgsb n m ℓ u) ↔
    ℓ = 0 ∧ n ≤ u := by
  constructor
  · rintro ⟨δ, hc, hδ⟩
    let x : Fin n → Fin (2 * n - 1) := Fin.castLE (by omega)
    have hx : Function.Injective x := Fin.castLE_injective _
    have hconst : ∀ i, δ (x i) = δ ⟨0, by omega⟩ := fun i => hc.const (by omega) (by omega) _ _
    have hcnt : ∀ v, cnt (δ ∘ x) v = if v = δ ⟨0, by omega⟩ then n else 0 := by
      intro v
      simp only [cnt, Function.comp_apply, hconst]
      split_ifs with h <;> simp [h, eq_comm]
    obtain ⟨w, hw⟩ : ∃ w : Fin m, w ≠ δ ⟨0, by omega⟩ := by
      by_cases h0 : δ ⟨0, by omega⟩ = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
    have h1 := (mem_sgsb.1 (hδ x hx) w).1
    have h2 := (mem_sgsb.1 (hδ x hx) (δ ⟨0, by omega⟩)).2
    rw [hcnt] at h1 h2
    simp only [hw, ite_false, ite_true] at h1 h2
    exact ⟨by omega, h2⟩
  · rintro ⟨rfl, hu⟩
    refine ⟨fun _ => ⟨0, by omega⟩, fun _ _ _ _ _ _ => rfl, fun x _ => mem_sgsb.2 fun v => ?_⟩
    exact ⟨Nat.zero_le _, (cnt_le _ v).trans hu⟩

/-- Theorem 9 fails for comparison-based algorithms: `⟨2, 3, 0, 1⟩` satisfies `ℓ = 0` and
`⌈3/3⌉ ≤ 1`, but no comparison-based decision function solves it without communication. -/
theorem theorem_9_comparisonBased_false :
    (0 = 0 ∧ (2 * 2 - 1) ⌈/⌉ 3 ≤ 1) ∧
    ¬ ∃ δ : Fin (2 * 2 - 1) → Fin 3, ComparisonBased 2 δ ∧
      ∀ x : Fin 2 → Fin (2 * 2 - 1), Function.Injective x → δ ∘ x ∈ sgsb 2 3 0 1 := by
  refine ⟨⟨rfl, by decide⟩, fun h => ?_⟩
  have := (noComm_comparisonBased_iff le_rfl (by norm_num)).1 h
  omega

/-! ### Theorem 10 and Corollary 5 (reductions to cited impossibility results) -/

/-- The parity map of Theorem 10's proof. -/
def parity (v : Fin m) : Fin 2 := ⟨v % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Theorem 10, the reduction: for `m ≥ 2`, deciding the parity of an output of
`⟨n, m, 1, u⟩` solves WSB `⟨n, 2, 1, n - 1⟩` (for every `u`). -/
theorem parity_mem_wsb (hm : 2 ≤ m) {O : Fin n → Fin m} (hO : O ∈ sgsb n m 1 u) :
    parity ∘ O ∈ kWSB n 1 := by
  have hpos : ∀ w : Fin 2, 1 ≤ cnt (parity ∘ O) w := by
    intro w
    obtain ⟨i, hi⟩ := card_pos.1 (by have := (mem_sgsb.1 hO ⟨w, by omega⟩).1; exact this)
    simp only [mem_filter, mem_univ, true_and] at hi
    refine card_pos.2 ⟨i, ?_⟩
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply, parity, hi, Fin.ext_iff]
    exact Nat.mod_eq_of_lt w.isLt
  have hsum := sum_cnt (parity ∘ O)
  rw [Fin.sum_univ_two] at hsum
  refine mem_sgsb.2 fun w => ⟨hpos w, ?_⟩
  have := hpos 0; have := hpos 1
  fin_cases w <;> simp <;> omega

/-- Theorem 10 (conditional on the cited results): if WSB is not solvable (in some iterated model,
in `t` rounds) — by [Castañeda–Rajsbaum] this is the case in the wait-free read/write model when
`{binom n i : 1 ≤ i ≤ ⌊n/2⌋}` is not prime, via the equivalence of WSB and `(2n-2)`-renaming —
then no `⟨n, m, 1, u⟩`-GSB task with `m ≥ 2` is solvable. -/
theorem theorem_10 {A B : Type} (M : Model (Fin n) A B) {t : ℕ} (hm : 2 ≤ m) (u : ℕ)
    (hWSB : ¬ Solvable M (gsbTask N (kWSB n 1)) t) :
    ¬ Solvable M (gsbTask N (sgsb n m 1 u)) t :=
  Solvable.mapDec_contra hWSB parity subset_rfl fun _ _ _ _ hy => parity_mem_wsb hm hy

/-- Election solves WSB (Section 5.3): election output vectors are WSB output vectors. -/
theorem election_solves_wsb {A B : Type} (M : Model (Fin n) A B) {t : ℕ} (hn : 2 ≤ n)
    (h : Solvable M (gsbTask N (election n)) t) : Solvable M (gsbTask N (kWSB n 1)) t :=
  h.mapDec id subset_rfl fun _ _ _ _ hy => election_subset_wsb hn hy

/-- Corollary 5 (conditional on Theorem 11, whose proof uses topology): if election is not solvable,
then perfect renaming is not solvable (by Theorem 8). -/
theorem corollary_5 {A B : Type} (M : Model (Fin n) A B) {t : ℕ} (hn : 1 ≤ n)
    (hElection : ¬ Solvable M (gsbTask N (election n)) t) :
    ¬ Solvable M (gsbTask N (sgsb n n 1 1)) t := by
  have hfeas : (election n).Nonempty := by
    rw [election, lemma_1]
    refine ⟨fun v => le_rfl, ?_, ?_⟩ <;> simp [Fin.sum_univ_two] <;> omega
  obtain ⟨V, hV⟩ := theorem_8_asymm hfeas
  exact Solvable.mapDec_contra hElection V subset_rfl fun _ _ _ y hy => hV y hy

end Podc.SymmetryBreakingTasks
