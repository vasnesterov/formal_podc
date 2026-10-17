import Papers.PODC2026.TreeAA.TreeGeom
import Cslib.Computability.Distributed.Byzantine.LockStep.Sequential
import Cslib.Computability.Distributed.Byzantine.Specs
import Mathlib

/-!
# Problem specifications and local computations of the protocols

Model: CSLib's synchronous lock-step Byzantine model `Cslib.Byzantine.LockStep` on the complete
network `⊤` with parties `P` (`n = |P|`), a static adversary corrupting at most `t` parties
(`LockStep.atMost t`), deterministic protocols, optionally with ideal signatures (`Auth`).

* `RealAA ε` — Definition 1 (termination, validity, `ε`-agreement), with the precondition
  `Close D` ("the honest inputs are `D`-close") under which the round bound is promised.
* `GraphAA G` — Definition 2 (termination, validity w.r.t. the shortest-path hull, 1-agreement).
* `Gradecast snd` — Definition 4 (termination, integrity, consistency), grades in `Fin 3`.
* `rnd` — the rounding `[j]` of Section 4.1 (nearest integer, ties up) and Remark 1.
* `projIdx G L v` — index of the projection `proj_L(v)` (the first vertex of `L` closest to `v`).
* `lsp k d g` — Definition 5: the longest path prefix supported by at least `k` received paths
  with grade at least `g` (`d s` = what was received from sender `s`).
-/

namespace TreeAA

open Cslib.Byzantine.LockStep SimpleGraph

variable {P V : Type*}

/-! ### Specifications -/

/-- **Definition 1** (AA on `ℝ`): termination, validity (outputs within the range of the honest
inputs) and `ε`-agreement. -/
def RealAA (ε : ℝ) : Spec P ℝ ℝ := fun x H dec =>
  (∀ p ∈ H, ∃ o, dec p o) ∧
  (∀ p ∈ H, ∀ o, dec p o → ∃ a ∈ H, ∃ b ∈ H, x a ≤ o ∧ o ≤ x b) ∧
  (∀ p ∈ H, ∀ q ∈ H, ∀ o o', dec p o → dec q o' → |o - o'| ≤ ε)

/-- The honest inputs are `D`-close. -/
def Close (D : ℝ) : (P → ℝ) → Set P → Prop := fun x H => ∀ p ∈ H, ∀ q ∈ H, |x p - x q| ≤ D

/-- **Definition 2** (AA on a graph `G`): termination, validity (outputs in the shortest-path
convex hull of the honest inputs) and 1-agreement. -/
def GraphAA (G : SimpleGraph V) : Spec P V V := fun x H dec =>
  (∀ p ∈ H, ∃ o, dec p o) ∧
  (∀ p ∈ H, ∀ o, dec p o → o ∈ hull G (x '' H)) ∧
  (∀ p ∈ H, ∀ q ∈ H, ∀ o o', dec p o → dec q o' → G.dist o o' ≤ 1)

/-- **Definition 4** (gradecast with sender `snd`): termination, integrity (an honest sender's
value is output with grade 2), consistency (grades differ by at most one; positive grades
come with the same value). The shared `Problem.Gradecast` with top grade `2`; `gradecast_iff`
unfolds it. -/
abbrev Gradecast {W : Type*} (snd : P) : Spec P W (W × Fin 3) :=
  Cslib.Byzantine.Problem.Gradecast 2
    (fun v (g : Fin 3) w g' => (g : ℕ) ≤ g' + 1 ∧ (0 < g → 0 < g' → v = w)) snd

/-- Definition 4 in its explicit form. -/
lemma gradecast_iff {W : Type*} {snd : P} {x : P → W} {H : Set P} {dec : P → W × Fin 3 → Prop} :
    Gradecast snd x H dec ↔
      (∀ p ∈ H, ∃ o, dec p o) ∧
      (snd ∈ H → ∀ p ∈ H, dec p (x snd, 2)) ∧
      (∀ p ∈ H, ∀ q ∈ H, ∀ v w (g g' : Fin 3), dec p (v, g) → dec q (w, g') →
        (g : ℕ) ≤ g' + 1 ∧ (0 < g → 0 < g' → v = w)) :=
  Iff.rfl

/-! ### Rounding (Remark 1) -/

/-- `[j]`: the nearest integer to `j` (ties rounded up). -/
noncomputable def rnd (j : ℝ) : ℤ := ⌊j + 1 / 2⌋

lemma rnd_intCast (i : ℤ) : rnd i = i := by
  unfold rnd; rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith

lemma rnd_natCast (i : ℕ) : rnd i = i := by exact_mod_cast rnd_intCast i

lemma rnd_mono {j j' : ℝ} (h : j ≤ j') : rnd j ≤ rnd j' := Int.floor_mono (by linarith)

/-- **Remark 1.1**: rounding stays within an integer range. -/
lemma rnd_mem_Icc {a b : ℕ} {j : ℝ} (ha : (a : ℝ) ≤ j) (hb : j ≤ b) :
    (a : ℤ) ≤ rnd j ∧ rnd j ≤ b := by
  constructor
  · have := rnd_mono ha; rwa [rnd_natCast] at this
  · have := rnd_mono hb; rwa [rnd_natCast] at this

lemma rnd_add_one (j : ℝ) : rnd (j + 1) = rnd j + 1 := by
  unfold rnd; rw [show j + 1 + 1 / 2 = (j + 1 / 2) + 1 by ring]; exact Int.floor_add_one _

/-- **Remark 1.2**: rounding preserves 1-closeness. -/
lemma rnd_close {j j' : ℝ} (h : |j - j'| ≤ 1) : |rnd j - rnd j'| ≤ 1 := by
  rw [abs_le] at h ⊢
  have h1 := rnd_mono (show j ≤ j' + 1 by linarith)
  have h2 := rnd_mono (show j' ≤ j + 1 by linarith)
  rw [rnd_add_one] at h1 h2
  constructor <;> linarith

/-! ### Projection onto a path -/

section Proj

variable (G : SimpleGraph V)

open Classical in
/-- The index (in `L`) of the projection of `v` onto the vertex list `L`: the first index at
which the distance to `v` is minimal. -/
noncomputable def projIdx (L : List V) (v : V) : ℕ :=
  if h : ∃ i, i < L.length ∧ ∀ j < L.length, G.dist v (L.getD i v) ≤ G.dist v (L.getD j v)
  then Nat.find h else 0

variable {G}

lemma exists_projIdx {L : List V} (hL : L ≠ []) (v : V) :
    ∃ i, i < L.length ∧ ∀ j < L.length, G.dist v (L.getD i v) ≤ G.dist v (L.getD j v) := by
  obtain ⟨i, hi, hmin⟩ := (Finset.range L.length).exists_min_image
    (fun i => G.dist v (L.getD i v)) (by simpa [List.length_pos_iff] using hL)
  exact ⟨i, by simpa using hi, fun j hj => hmin j (by simpa using hj)⟩

lemma projIdx_eq {L : List V} (hL : L ≠ []) (v : V) [DecidablePred fun i =>
    i < L.length ∧ ∀ j < L.length, G.dist v (L.getD i v) ≤ G.dist v (L.getD j v)] :
    projIdx G L v = Nat.find (exists_projIdx (G := G) hL v) := by
  classical
  unfold projIdx
  simp only [exists_projIdx (G := G) hL v, ↓reduceDIte]
  congr

lemma projIdx_lt {L : List V} (hL : L ≠ []) (v : V) : projIdx G L v < L.length := by
  classical
  rw [projIdx_eq hL v]
  exact (Nat.find_spec (exists_projIdx hL v)).1

lemma projIdx_min {L : List V} (hL : L ≠ []) (v : V) {j : ℕ} (hj : j < L.length) :
    G.dist v (L.getD (projIdx G L v) v) ≤ G.dist v L[j] := by
  classical
  have h := (Nat.find_spec (exists_projIdx (G := G) hL v)).2 j hj
  rw [← projIdx_eq hL v] at h
  rwa [List.getD_eq_getElem _ _ hj] at h

end Proj

/-! ### Longest supported path prefix (Definition 5) -/

section Support

variable [Fintype P] [DecidableEq V]

/-- The senders whose received path has `L` as a prefix and grade at least `g`. -/
noncomputable def supporters (d : P → List V × Fin 3) (g : Fin 3) (L : List V) : Finset P := by
  classical exact Finset.univ.filter (fun s => g ≤ (d s).2 ∧ L <+: (d s).1)

lemma mem_supporters {d : P → List V × Fin 3} {g : Fin 3} {L : List V} {s : P} :
    s ∈ supporters d g L ↔ g ≤ (d s).2 ∧ L <+: (d s).1 := by
  classical
  unfold supporters; simp

open Classical in
/-- **Definition 5**: the longest path prefix supported by at least `k` paths received with grade
at least `g` (`[]` if there is none). -/
noncomputable def lsp (k : ℕ) (d : P → List V × Fin 3) (g : Fin 3) : List V :=
  let C := (Finset.univ.biUnion fun s => (d s).1.inits.toFinset).filter
    (fun L => k ≤ (supporters d g L).card)
  if h : C.Nonempty then (C.exists_max_image List.length h).choose else []

lemma lsp_spec {k : ℕ} (hk : 0 < k) {d : P → List V × Fin 3} {g : Fin 3} {L : List V}
    (hL : k ≤ (supporters d g L).card) :
    k ≤ (supporters d g (lsp k d g)).card ∧ L.length ≤ (lsp k d g).length := by
  classical
  set C := (Finset.univ.biUnion fun s => (d s).1.inits.toFinset).filter
    (fun L => k ≤ (supporters d g L).card) with hC
  have hLC : L ∈ C := by
    rw [hC, Finset.mem_filter]
    refine ⟨?_, hL⟩
    obtain ⟨s, hs⟩ := Finset.card_pos.1 (lt_of_lt_of_le hk hL)
    rw [Finset.mem_biUnion]
    exact ⟨s, Finset.mem_univ _, by
      rw [List.mem_toFinset, List.mem_inits]; exact (mem_supporters.1 hs).2⟩
  have hne : C.Nonempty := ⟨L, hLC⟩
  have hlsp : lsp k d g = (C.exists_max_image List.length hne).choose := by
    unfold lsp; simp only [← hC, hne, ↓reduceDIte]
  have hspec := (C.exists_max_image List.length hne).choose_spec
  rw [hlsp]
  exact ⟨(Finset.mem_filter.1 hspec.1).2, hspec.2 L hLC⟩

/-- Two prefixes, each supported by more than half of the senders (possibly with different
grades), are comparable. -/
lemma prefix_or_prefix_of_supported {k : ℕ} (hk : Fintype.card P < 2 * k)
    {d : P → List V × Fin 3} {g g' : Fin 3} {L L' : List V}
    (hL : k ≤ (supporters d g L).card) (hL' : k ≤ (supporters d g' L').card) :
    L <+: L' ∨ L' <+: L := by
  classical
  have hcard := Finset.card_union_add_card_inter (supporters d g L) (supporters d g' L')
  have hu := Finset.card_le_univ (supporters d g L ∪ supporters d g' L')
  obtain ⟨s, hs⟩ : (supporters d g L ∩ supporters d g' L').Nonempty := by
    rw [← Finset.card_pos]; omega
  rw [Finset.mem_inter, mem_supporters, mem_supporters] at hs
  exact List.prefix_or_prefix_of_prefix hs.1.2 hs.2.2

end Support

end TreeAA
