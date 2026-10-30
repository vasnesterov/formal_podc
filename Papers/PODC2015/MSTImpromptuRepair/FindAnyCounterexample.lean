import Papers.PODC2015.MSTImpromptuRepair.FindAny
import Papers.PODC2015.MSTImpromptuRepair.PairwiseExtend

/-!
# Lemma 5 fails with the paper's hash range `r > ∑ deg`

`FindAny` step 3a draws a pairwise independent `h : [1, maxEdgeNum(T)] → [r]` with `r` "a power of
2 `>` the sum of degrees of nodes in `T`", and step 3b uses the indices `i = 1, …, lg r`. Lemma 4,
however, needs `|W| < 2^(ℓ-1) = r/2` (`W` = the leaving edges), and its index `j` may be `0`.

Instance: the star `K_{1,3}` (center `0`, leaves `1, 2, 3`, IDs `1, …, 4`), `T = {0}`: the sum of
degrees is `3`, so `r = 4` (`ℓ = 2`, indices `{1, 2}`) is allowed. The three edges are all leaving,
with the paper's edge numbers `10, 11, 12` (ID concatenation, smallest first, 3-bit fields).
We give a pairwise independent family on `[0, 12] ⊇ [1, maxEdgeNum(T)] = [1, 12]` (`hfam`,
`hfam_pairwiseIndep`) for which, for **every** seed, the number of leaving edges hashing into
`[2] = {0, 1}` is `0` or `2` (the high bits of the three hash values are `s₁, s₂, ¬(s₁ ⊕ s₂)`),
so `min = 2`, `w(T) = 10 ⊕ 11 ⊕ 12 = 13`, which is the number of no edge: `Sum = 0` and the round
fails (`step_eq_none`). Hence `FindAny-C` returns `∅` with probability 1 and `FindAny` never
finds the leaving edges, whatever `HP-TestOut` does (`findAnyC_eq_none`, `findAny_eq_none`,
`lemma5_findAnyC_false`).
-/

namespace Podc.MSTImpromptuRepair.FindAnyCex

open Finset Cslib.Probability

/-- The star `K_{1,3}` with center `0`. -/
def star : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0)
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

instance : DecidableRel star.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u = 0 ∨ v = 0)))

/-- Node IDs `1, …, 4`. -/
def ident (v : Fin 4) : ℕ := v.val + 1

/-- The paper's edge number: the concatenation of the endpoint IDs, smallest first (3-bit
fields). -/
def edgeNumber : Sym2 (Fin 4) → ℕ :=
  Sym2.lift ⟨fun u v => 8 * min (ident u) (ident v) + max (ident u) (ident v), fun u v => by
    simp only [min_comm, max_comm]⟩

/-- Edge numbers as keys in `[0, 12]` (the edges of the star get `10, 11, 12`). -/
def num (e : Sym2 (Fin 4)) : Fin 13 := ⟨edgeNumber e % 13, Nat.mod_lt _ (by norm_num)⟩

/-- XOR of edge numbers: their 4-bit binary representations in `(ZMod 2)^4`. -/
def enc (x : Fin 13) : Fin 4 → ZMod 2 := fun i => if x.val.testBit i then 1 else 0

theorem enc_add_self (x : Fin 4 → ZMod 2) : x + x = 0 := by
  funext i; exact zmod2_add_self (x i)

/-- The three edges of the star. -/
def C : Finset (Sym2 (Fin 4)) := {s(0, 1), s(0, 2), s(0, 3)}

theorem cut_eq : cut star {0} = C := by decide

theorem edgeFinset_eq : star.edgeFinset = C := by decide

/-- The sum of the degrees of the nodes of `T = {0}` is `3`, so `r = 4` is a power of `2` larger
than it, as the paper requires. -/
theorem sum_deg : #(Eup star (fun _ => True) {0}) = 3 := by decide

theorem enc_num_injOn : Set.InjOn (fun e => enc (num e)) star.edgeSet := by
  intro a ha b hb h
  have ha' : a ∈ C := by rw [← edgeFinset_eq]; simpa using ha
  have hb' : b ∈ C := by rw [← edgeFinset_eq]; simpa using hb
  revert h; revert ha' hb'; revert a b; decide

/-- The base seeds `(s₁, s₂, l₁, l₂, l₃)`. -/
abbrev Ω₀ := Bool × Bool × Bool × Bool × Bool

/-- The keys on which the base family is prescribed: the three edge numbers. -/
def W₀ : Finset (Fin 13) := {10, 11, 12}

/-- The base family on the keys `10, 11, 12`: `h(10) = 2 s₁ + l₁`, `h(11) = 2 s₂ + l₂`,
`h(12) = 2 ¬(s₁ ⊕ s₂) + l₃` (values in `[4]`). -/
def h₀ : Ω₀ → Fin 13 → ℕ
  | (s₁, s₂, l₁, l₂, l₃), x =>
    if x = 10 then 2 * s₁.toNat + l₁.toNat
    else if x = 11 then 2 * s₂.toNat + l₂.toNat
    else if x = 12 then 2 * (!(xor s₁ s₂)).toNat + l₃.toNat
    else 0

theorem h₀_pairwiseIndep : IsPairwiseIndep 4 W₀ h₀ := by
  unfold IsPairwiseIndep; decide

/-- The counterexample family on all keys `[0, 12]`: `h₀` on `10, 11, 12`, independent uniform
values elsewhere. -/
def hfam : Ω₀ × (Fin 13 → Fin 4) → Fin 13 → ℕ := extendHash (r := 4) W₀ h₀

/-- `hfam` is a pairwise independent family `[0, 12] → [2^2]`. -/
theorem hfam_pairwiseIndep : IsPairwiseIndep (2 ^ 2) univ hfam :=
  IsPairwiseIndep.extend (by norm_num) h₀_pairwiseIndep

theorem hfam_num (ω : Ω₀ × (Fin 13 → Fin 4)) {e : Sym2 (Fin 4)} (he : e ∈ C) :
    hfam ω (num e) = h₀ ω.1 (num e) := by
  have : num e ∈ W₀ := by revert he; revert e; decide
  simp [hfam, extendHash, this]

/-- A round fails whenever, for every index `i ∈ I` with `h_i(T) = 1`, `w(T)` is not the number
of an edge. -/
theorem step_eq_none_of {V U N : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {T : Finset V} [AddCommGroup N] [DecidableEq N] {num : Sym2 V → U}
    {enc : U → N} {hv : U → ℕ} {I : Finset ℕ}
    (h : ∀ i ∈ I, hT G T num hv i = 1 → ∀ e ∈ G.edgeFinset, enc (num e) ≠ wT G T num enc hv i) :
    step G T num enc hv I = none := by
  unfold step minIdx
  split_ifs with hne
  · dsimp only
    have hmem := min'_mem _ hne
    rw [mem_filter] at hmem
    rw [dif_neg]
    rintro ⟨e, he, heq, -⟩
    exact h _ hmem.1 hmem.2 e he heq
  · rfl

/-- The decidable core: for every base seed and `i ∈ {1, 2}`, if an odd number of the three
edges hash into `[2^i]`, the XOR of their numbers is not the number of an edge. -/
theorem core : ∀ ω₀ : Ω₀, ∀ i ∈ Icc 1 2,
    ((#(C.filter fun e => h₀ ω₀ (num e) < 2 ^ i) : ℕ) : ZMod 2) = 1 →
      ∀ e ∈ C, enc (num e) ≠ ∑ f ∈ C.filter (fun e => h₀ ω₀ (num e) < 2 ^ i), enc (num f) := by
  decide

/-- **The round of `FindAny` fails for every seed** of the pairwise independent family `hfam`. -/
theorem step_eq_none (ω : Ω₀ × (Fin 13 → Fin 4)) :
    step star {0} num enc (hfam ω) (Icc 1 2) = none := by
  apply step_eq_none_of
  intro i hi h1 e he
  rw [hT_eq_card_cut, cut_eq] at h1
  rw [wT_eq_sum_cut enc_add_self, cut_eq]
  rw [edgeFinset_eq] at he
  have hf : C.filter (fun e => hfam ω (num e) < 2 ^ i) = C.filter (fun e => h₀ ω.1 (num e) < 2 ^ i) :=
    filter_congr fun e he => by rw [hfam_num ω he]
  rw [hf] at h1 ⊢
  exact core ω.1 i hi h1 e he

/-- Hence `FindAny-C` (with the paper's index range `{1, …, lg r}`, `r = 4`) returns `∅` for every
choice of the random point `α` of `HP-TestOut` and every hash seed, although all three edges at
the center leave `T = {0}`. -/
theorem findAnyC_eq_none {p : ℕ} (dnum : Fin 4 × Fin 4 → ℕ) (α : ZMod p)
    (ω : Ω₀ × (Fin 13 → Fin 4)) :
    findAnyC star {0} num enc dnum α (hfam ω) (Icc 1 2) = none := by
  unfold findAnyC; split_ifs <;> simp [step_eq_none]

/-- …and `FindAny` returns `∅` for any number of repetitions. -/
theorem findAny_eq_none {p K : ℕ} (dnum : Fin 4 × Fin 4 → ℕ) (α : ZMod p)
    (ωs : Fin K → Ω₀ × (Fin 13 → Fin 4)) :
    findAny star {0} num enc dnum α (fun k => hfam (ωs k)) (Icc 1 2) = none := by
  unfold findAny; split_ifs
  · rw [List.findSome?_eq_none_iff]
    intro o ho
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ho
    simp [step_eq_none]
  · rfl

theorem cut_nonempty : (cut star {0}).Nonempty := by rw [cut_eq]; decide

/-- **Lemma 5 is false with the paper's parameters**: here some edge leaves `T`, the hash family is
pairwise independent on `[1, maxEdgeNum(T)]` into `[r]` with `r = 4 > 3 = ∑ deg`, but `FindAny-C`
returns a leaving edge with probability `0 < 1/16`. -/
theorem lemma5_findAnyC_false {p : ℕ} [NeZero p] (dnum : Fin 4 × Fin 4 → ℕ) :
    (cut star {0}).Nonempty ∧ #(Eup star (fun _ => True) {0}) < 2 ^ 2 ∧
    IsPairwiseIndep (2 ^ 2) univ hfam ∧
    uprob (fun x : ZMod p × (Ω₀ × (Fin 13 → Fin 4)) => ∃ e ∈ cut star {0},
      findAnyC star {0} num enc dnum x.1 (hfam x.2) (Icc 1 2) = some e) = 0 := by
  refine ⟨cut_nonempty, by rw [sum_deg]; norm_num, hfam_pairwiseIndep, ?_⟩
  have : (fun x : ZMod p × (Ω₀ × (Fin 13 → Fin 4)) => ∃ e ∈ cut star {0},
      findAnyC star {0} num enc dnum x.1 (hfam x.2) (Icc 1 2) = some e) = fun _ => False := by
    funext x; simp [findAnyC_eq_none]
  rw [this, uprob_false]

end Podc.MSTImpromptuRepair.FindAnyCex
