import Papers.PODC2022.AsyncSpeedup.Speedup
import Cslib.Foundations.Data.Finset.Card

/-!
# Facts about one-round solutions of local tasks

The arguments of Section 3.3, Section 4.3 and Claims 2, 3, 4, 6 all inspect a one-round algorithm
`g` solving a local task `Π_{τ,σ}` on a few executions:

* `local_solo` — a process that sees only itself outputs its value in `τ` (condition (1) of
  Definition 1);
* `local_proj` — the outputs of a round with `≥ 2` participants form a face of a legal output for
  `σ` (condition (2));
* `local_triangle` — the "γ argument" (Corollary 2, Claims 3, 4, 6): two executions in which `i`
  (resp. `j`) runs solo first and `k` has the same view in both;
* `iis_local_path` — the "path of three edges" argument (Corollary 1, Claim 2) in IIS.
-/

set_option linter.unusedSectionVars false

namespace AsyncSpeedup

open Cslib.Iterated

variable {P X Y A B : Type} [DecidableEq P] {M : Model P A B}

lemma step_congr {Y : Type} {r : ℕ} (τ : P → View P Y B r) {p q : Pattern P B} {i : P}
    (hs : p.sees i = q.sees i) (ho : p.out i = q.out i) : step τ p i = step τ q i := by
  unfold step; rw [hs, ho]

/-- Condition (1) of Definition 1, as used in the proofs: in any round of a one-round solution of a
local task, a process that sees only itself outputs its own value. -/
lemma local_solo (hsolo : M.AllowsSolo) {b₀ : P → A → B}
    (hdet : M.SoloDet b₀) {T : Task P X Y} {I : Finset P} {x : P → X} {τ : P → Y}
    {g : Alg P Y A B Y 1} (hg : Solves M (localTask T I x τ) g) {J : Finset P} (hJI : J ⊆ I)
    {p : Pattern P B} (hp : p ∈ M.Pat J (fun k => g.inp 0 k (τ k))) {i : P} (hi : i ∈ J)
    (hs : p.sees i = {i}) : g.dec i (step (r := 0) τ p i) = τ i := by
  obtain ⟨p₀, hp₀, hs₀⟩ := hsolo {i} (fun k => g.inp 0 k (τ k)) i (Finset.mem_singleton_self i)
  obtain ⟨y, ⟨hy1, -⟩, hdec⟩ := hg.one_round (J := {i}) (x := τ)
    ⟨Finset.singleton_nonempty i, Finset.singleton_subset_iff.2 (hJI hi), rfl⟩ p₀ hp₀
  have hstep : step (r := 0) τ p i = step (r := 0) τ p₀ i :=
    step_congr (r := 0) (Y := Y) τ (hs.trans hs₀.symm)
      ((hdet J _ p hp i hi hs).trans (hdet {i} _ p₀ hp₀ i (Finset.mem_singleton_self i) hs₀).symm)
  rw [hstep, hdec i (Finset.mem_singleton_self i)]
  exact hy1 (Finset.card_singleton i) i (Finset.mem_singleton_self i)

/-- Condition (2) of Definition 1, as used in the proofs. -/
lemma local_proj {T : Task P X Y} {I : Finset P} {x : P → X} {τ : P → Y}
    {g : Alg P Y A B Y 1} (hg : Solves M (localTask T I x τ) g) {J : Finset P} (hJI : J ⊆ I)
    (hJ : 1 < J.card) {p : Pattern P B} (hp : p ∈ M.Pat J (fun k => g.inp 0 k (τ k))) :
    ∃ y ∈ T.Δ I x, ∀ j ∈ J, g.dec j (step (r := 0) τ p j) = y j := by
  obtain ⟨y, ⟨-, hy2⟩, hdec⟩ := hg.one_round (J := J) (x := τ)
    ⟨Finset.card_pos.1 (lt_trans zero_lt_one hJ), hJI, rfl⟩ p hp
  obtain ⟨y', hy', hyy'⟩ := hy2 (Nat.ne_of_gt hJ)
  exact ⟨y', hy', fun j hj => (hdec j hj).trans (hyy' j hj)⟩

/-- The "γ argument": if in two rounds of all of `I` process `i` (resp. `j`) sees only itself and
process `k` has the same view, then `τ i` and `τ j` are both "adjacent" in `Δ(σ)` to the common
output `γ` of `k`. -/
lemma local_triangle (hsolo : M.AllowsSolo) {b₀ : P → A → B}
    (hdet : M.SoloDet b₀) {T : Task P X Y} {I : Finset P} {x : P → X} {τ : P → Y}
    {g : Alg P Y A B Y 1} (hg : Solves M (localTask T I x τ) g) {i j k : P} (hi : i ∈ I)
    (hj : j ∈ I) (hk : k ∈ I) (hij : i ≠ j)
    {p q : Pattern P B} (hp : p ∈ M.Pat I (fun l => g.inp 0 l (τ l)))
    (hq : q ∈ M.Pat I (fun l => g.inp 0 l (τ l))) (hpi : p.sees i = {i}) (hqj : q.sees j = {j})
    (hks : p.sees k = q.sees k) (hko : p.out k = q.out k) :
    ∃ γ : Y, (∃ y ∈ T.Δ I x, y i = τ i ∧ y k = γ) ∧ (∃ y ∈ T.Δ I x, y j = τ j ∧ y k = γ) := by
  have hI := Finset.one_lt_card.2 ⟨i, hi, j, hj, hij⟩
  obtain ⟨y₁, hy₁, hd₁⟩ := local_proj hg le_rfl hI hp
  obtain ⟨y₂, hy₂, hd₂⟩ := local_proj hg le_rfl hI hq
  refine ⟨g.dec k (step (r := 0) τ p k), ⟨y₁, hy₁, ?_, (hd₁ k hk).symm⟩, ⟨y₂, hy₂, ?_, ?_⟩⟩
  · rw [← hd₁ i hi]; exact local_solo hsolo hdet hg le_rfl hp hi hpi
  · rw [← hd₂ j hj]; exact local_solo hsolo hdet hg le_rfl hq hj hqj
  · rw [← hd₂ k hk]; exact congrArg (g.dec k) (step_congr (r := 0) (Y := Y) τ hks.symm hko.symm)

/-- In zero rounds a process decides on its input alone; a solo run pins down the decision. -/
lemma zero_round_solo {M : Model P A B} {T : Task P X Y} {alg : Alg P X A B Y 0}
    (h : Solves M T alg) {i : P} {x : P → X} (hx : ({i}, x) ∈ T.Inp) :
    ∃ y ∈ T.Δ {i} x, alg.dec i (x i) = y i := by
  obtain ⟨y, hy, hdec⟩ := h {i} x hx x Reach.zero
  exact ⟨y, hy, hdec i (Finset.mem_singleton_self i)⟩

/-! ### Rank patterns -/

lemma rankSees_congr {I : Finset P} {rk rk' : P → ℕ} {i i' : P}
    (h : ∀ l ∈ I, rk l ≤ rk i ↔ rk' l ≤ rk' i') : rankSees I rk i = rankSees I rk' i' := by
  ext l; simp only [mem_rankSees]
  constructor
  · rintro ⟨hl, h'⟩; exact ⟨hl, (h l hl).1 h'⟩
  · rintro ⟨hl, h'⟩; exact ⟨hl, (h l hl).2 h'⟩

lemma rankSees_eq_singleton {I : Finset P} {rk : P → ℕ} {i : P} (hi : i ∈ I) (h0 : rk i = 0)
    (hpos : ∀ l ∈ I, l ≠ i → 0 < rk l) : rankSees I rk i = {i} := by
  ext l
  simp only [mem_rankSees, Finset.mem_singleton, h0]
  constructor
  · rintro ⟨hl, h'⟩; by_contra hne; have := hpos l hl hne; omega
  · rintro rfl; exact ⟨hi, h0.le⟩

/-- Ranks `i ↦ 0`, `j ↦ 1`, `k ↦ 2`, others `↦ 3` (ordered partition `[i], [j], [k], rest`). -/
def rank3 (i j k : P) : P → ℕ := fun l => if l = i then 0 else if l = j then 1 else if l = k then 2
  else 3

lemma rank3_solo {I : Finset P} {i j k : P} (hi : i ∈ I) :
    rankSees I (rank3 i j k) i = {i} :=
  rankSees_eq_singleton hi (by simp [rank3]) (fun l _ hl => by
    simp [rank3, hl]; split_ifs <;> omega)

lemma rank3_third {I : Finset P} {i j k : P} (hik : i ≠ k) (hjk : j ≠ k) :
    rankSees I (rank3 i j k) k = rankSees I (rank3 j i k) k :=
  rankSees_congr fun l _ => by
    simp only [rank3, ite_false, ite_true, hik.symm, hjk.symm]
    by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [h1, h2] <;> split_ifs <;> omega

lemma rank3_zero {i j k : P} : rank3 i j k i = 0 := by simp [rank3]

/-! ### The path argument in IIS -/

/-- Ranks `[i], [j], rest`. -/
def rank2 (i j : P) : P → ℕ := fun l => if l = i then 0 else if l = j then 1 else 2

/-- Ranks `[i, j], rest`. -/
def rankPair (i j : P) : P → ℕ := fun l => if l = i ∨ l = j then 0 else 1

/-- Pattern of `iis` given by ranks. -/
def iisPat (I : Finset P) (rk : P → ℕ) : Pattern P Unit := ⟨rankSees I rk, fun _ => ()⟩

lemma iisPat_mem {I : Finset P} (rk : P → ℕ) (a : P → Unit) :
    iisPat I rk ∈ (iis : Model P Unit Unit).Pat I a :=
  isIS_rankSees rk

/-- The path argument of Corollary 1 and Claim 2: in IIS, for `i ≠ j` in `I`, the solo vertex of
`i`, the vertices of `j` and `i` seeing both, and the solo vertex of `j` form a path of three edges,
each of which is mapped into a face of a legal output for `σ`. -/
lemma iis_local_path {T : Task P X Y} {I : Finset P} {x : P → X} {τ : P → Y}
    {g : Alg P Y Unit Unit Y 1} (hg : Solves iis (localTask T I x τ) g) {i j : P} (hi : i ∈ I)
    (hj : j ∈ I) (hij : i ≠ j) :
    ∃ b c : Y, (∃ y ∈ T.Δ I x, y i = τ i ∧ y j = b) ∧ (∃ y ∈ T.Δ I x, y j = b ∧ y i = c) ∧
      (∃ y ∈ T.Δ I x, y i = c ∧ y j = τ j) := by
  have hI := Finset.one_lt_card.2 ⟨i, hi, j, hj, hij⟩
  have hsolo := iis_allowsSolo (P := P)
  have hdet := iis_soloDet (P := P)
  obtain ⟨y₁, hy₁, hd₁⟩ := local_proj hg le_rfl hI (iisPat_mem (rank2 i j) _)
  obtain ⟨y₂, hy₂, hd₂⟩ := local_proj hg le_rfl hI (iisPat_mem (rankPair i j) _)
  obtain ⟨y₃, hy₃, hd₃⟩ := local_proj hg le_rfl hI (iisPat_mem (rank2 j i) _)
  have hs₁ : rankSees I (rank2 i j) i = {i} :=
    rankSees_eq_singleton hi (by simp [rank2]) (fun l _ hl => by
      simp [rank2, hl]; split_ifs <;> omega)
  have hs₃ : rankSees I (rank2 j i) j = {j} :=
    rankSees_eq_singleton hj (by simp [rank2]) (fun l _ hl => by
      simp [rank2, hl]; split_ifs <;> omega)
  have hjb : rankSees I (rank2 i j) j = rankSees I (rankPair i j) j :=
    rankSees_congr fun l _ => by
      simp only [rank2, rankPair, hij.symm, ite_false, ite_true, or_true]
      by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [h1, h2, hij, hij.symm]
  have hic : rankSees I (rankPair i j) i = rankSees I (rank2 j i) i :=
    rankSees_congr fun l _ => by
      simp only [rank2, rankPair, hij, ite_false, ite_true, true_or]
      by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [h1, h2, hij, hij.symm]
  refine ⟨g.dec j (step (r := 0) τ (iisPat I (rankPair i j)) j),
    g.dec i (step (r := 0) τ (iisPat I (rankPair i j)) i), ⟨y₁, hy₁, ?_, ?_⟩,
    ⟨y₂, hy₂, (hd₂ j hj).symm, (hd₂ i hi).symm⟩, ⟨y₃, hy₃, ?_, ?_⟩⟩
  · rw [← hd₁ i hi]
    exact local_solo hsolo hdet hg le_rfl (iisPat_mem _ _) hi hs₁
  · rw [← hd₁ j hj]
    exact congrArg (g.dec j) (step_congr (r := 0) (Y := Y) τ (p := iisPat I (rank2 i j))
      (q := iisPat I (rankPair i j)) hjb rfl)
  · rw [← hd₃ i hi]
    exact congrArg (g.dec i) (step_congr (r := 0) (Y := Y) τ (p := iisPat I (rankPair i j))
      (q := iisPat I (rank2 j i)) hic rfl).symm
  · rw [← hd₃ j hj]
    exact local_solo hsolo hdet hg le_rfl (iisPat_mem _ _) hj hs₃

/-! ### Patterns of the augmented models given by ranks and a first-class process -/

/-- `iisTS` pattern: ordered partition by `rk`, test&set won by `w`. -/
def tsPat (I : Finset P) (rk : P → ℕ) (w : P) : Pattern P Bool :=
  ⟨rankSees I rk, fun l => decide (l = w)⟩

lemma tsPat_mem {I : Finset P} {rk : P → ℕ} {w : P} (hw : w ∈ I) (h0 : rk w = 0)
    (a : P → Unit) : tsPat I rk w ∈ (iisTS : Model P Unit Bool).Pat I a :=
  ⟨isIS_rankSees rk, w, hw, fun l _ => by simp [tsPat, hw, h0], fun _ _ => rfl⟩

/-- `iisBC` pattern: ordered partition by `rk`, consensus decided by the proposal of `w`. -/
def bcPat (I : Finset P) (rk : P → ℕ) (w : P) (a : P → Bool) : Pattern P Bool :=
  ⟨rankSees I rk, fun _ => a w⟩

lemma bcPat_mem {I : Finset P} {rk : P → ℕ} {w : P} (hw : w ∈ I) (h0 : rk w = 0)
    (a : P → Bool) : bcPat I rk w a ∈ (iisBC : Model P Bool Bool).Pat I a :=
  ⟨isIS_rankSees rk, w, hw, fun l _ => by simp [bcPat, hw, h0], fun _ _ => rfl⟩

end AsyncSpeedup
