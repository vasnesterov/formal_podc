import Cslib.Computability.Distributed.Byzantine.CanonicalRounds.Schedule
import Papers.PODC2026.CanonicalRoundByzantine.Problems

/-!
# The executions `α₀`, `α₁`, `α₂` of Theorem 1 of [AFW26]

The processes are split into five groups `A, B, C, D, E` (`Groups`): `|B| = |D| = f` and
`|A|, |C|, |E| ≤ f` (this handles every `2f ≤ n ≤ 5f`; the paper assumes `n = 5f` "for simplicity").

* `α₂` (configuration `C₂`): `E` Byzantine; `B, C` have input `x₀` and hear `A B C E`;
  `A, D` have input `x₁` and hear `A C D E`; `E` pretends to `B C` to be correct in `α₀` and to
  `A D` to be correct in `α₁` (two-faced).
* `α₀` (configuration `C₀`): `A` Byzantine, behaving towards everybody as in `α₂`; `B C D E`
  correct with input `x₀`, all hearing `A B C E` (the messages of `D` are late).
* `α₁` (configuration `C₁`): `C` Byzantine, behaving as in `α₂`; `A B D E` correct with input
  `x₁`, all hearing `A C D E` (the messages of `B` are late).

All three are described by one *cover*: a round-level system with two copies of `E`
(`cov τ r b p`: history after round `r` of process `p` in copy `b`; copy `false` hosts `B, C, E₀`,
copy `true` hosts `A, D, E₁`). Lemmas `clean₂_eq`, `clean₀_eq`, `clean₁_eq` are the paper's
Lemmas 3 and 4 (and their analogue for `α₂`): the round-level histories of the correct processes
coincide with the cover histories.

The random numbers of the simulated copies of `E` are a fixed `r₀ : R`: the adversary of `α₂`
cannot know the tape entries of Byzantine processes; `α₀` and `α₁` therefore run with the tape
`ρE ρ` in which the row of every `E`-process is constant (`ρ` itself is arbitrary).
-/

namespace Podc2026.CanonicalRound

open Cslib.Byzantine.CanonicalRounds Finset

variable {n : ℕ} {V R M O : Type*}

/-- A partition of the processes into the groups `A = 0, B = 1, C = 2, D = 3, E = 4`. -/
structure Groups (n f : ℕ) where
  grp : Fin n → Fin 5
  cardB : (univ.filter fun p => grp p = 1).card = f
  cardD : (univ.filter fun p => grp p = 3).card = f
  cardA : (univ.filter fun p => grp p = 0).card ≤ f
  cardC : (univ.filter fun p => grp p = 2).card ≤ f
  cardE : (univ.filter fun p => grp p = 4).card ≤ f

namespace Groups

variable {f : ℕ} (G : Groups n f)

/-- Group `i` as a finset. -/
def set (i : Fin 5) : Finset (Fin n) := univ.filter fun p => G.grp p = i

@[simp] theorem mem_set {i : Fin 5} {p : Fin n} : p ∈ G.set i ↔ G.grp p = i := by simp [set]

/-- The copy of the cover hosting `p` (`false`: `B, C`; `true`: `A, D, E`). -/
def side (p : Fin n) : Bool := !(G.grp p = 1 ∨ G.grp p = 2)

/-- The processes heard in copy `b`: all but `D` (copy `false`) or all but `B` (copy `true`). -/
def hb (b : Bool) : Finset (Fin n) := univ.filter fun q => G.grp q ≠ if b then 1 else 3

/-- The copy whose node `q` is heard by nodes of copy `b`. -/
def nb (b : Bool) (q : Fin n) : Bool := if G.grp q = 4 then b else G.side q

theorem card_hb (b : Bool) : (G.hb b).card = n - f := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun q => G.grp q = if b then 1 else 3)
  cases b
  · simp only [hb, Bool.false_eq_true, if_false] at h ⊢
    rw [card_univ, Fintype.card_fin, G.cardD] at h
    simp only [ne_eq]; omega
  · simp only [hb, if_true] at h ⊢
    rw [card_univ, Fintype.card_fin, G.cardB] at h
    simp only [ne_eq]; omega

end Groups

/-- Existence of a partition for `2f ≤ n ≤ 5f`. -/
theorem Groups.exists (f : ℕ) (h2 : 2 * f ≤ n) (h5 : n ≤ 5 * f) : Nonempty (Groups n f) := by
  -- B = [0, f), D = [f, 2f), A = [2f, 3f), C = [3f, 4f), E = [4f, n)
  let g : Fin n → Fin 5 := fun p =>
    if p.val < f then 1 else if p.val < 2 * f then 3 else if p.val < 3 * f then 0
    else if p.val < 4 * f then 2 else 4
  have key : ∀ a b, (univ.filter fun p : Fin n => a ≤ p.val ∧ p.val < b).map Fin.valEmbedding ⊆
      Finset.Ico a b := by
    intro a b x; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    rintro ⟨p, hp, rfl⟩; exact hp
  have key_le : ∀ a b, (univ.filter fun p : Fin n => a ≤ p.val ∧ p.val < b).card ≤ b - a := by
    intro a b
    rw [← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico]
    exact Finset.card_le_card (key a b)
  have key_eq : ∀ a b, a ≤ b → b ≤ n →
      (univ.filter fun p : Fin n => a ≤ p.val ∧ p.val < b).card = b - a := by
    intro a b hab hbn
    rw [← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico]
    congr 1
    refine Finset.Subset.antisymm (key a b) (fun x hx => ?_)
    simp only [Finset.mem_Ico] at hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply]
    exact ⟨⟨x, by omega⟩, hx, rfl⟩
  have hB : (univ.filter fun p => g p = 1) = univ.filter fun p : Fin n => 0 ≤ p.val ∧ p.val < f := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]; split_ifs <;> simp <;> omega
  have hD : (univ.filter fun p => g p = 3) =
      univ.filter fun p : Fin n => f ≤ p.val ∧ p.val < 2 * f := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]; split_ifs <;> simp <;> omega
  have hA : (univ.filter fun p => g p = 0) =
      univ.filter fun p : Fin n => 2 * f ≤ p.val ∧ p.val < 3 * f := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]; split_ifs <;> simp <;> omega
  have hC : (univ.filter fun p => g p = 2) =
      univ.filter fun p : Fin n => 3 * f ≤ p.val ∧ p.val < 4 * f := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]; split_ifs <;> simp <;> omega
  have hE : (univ.filter fun p => g p = 4) =
      univ.filter fun p : Fin n => 4 * f ≤ p.val ∧ p.val < n := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]
    have := p.isLt; split_ifs <;> simp <;> omega
  refine ⟨⟨g, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hB, key_eq 0 f (by omega) (by omega)]; omega
  · rw [hD, key_eq f (2 * f) (by omega) (by omega)]; omega
  · rw [hA]; have := key_le (2 * f) (3 * f); omega
  · rw [hC]; have := key_le (3 * f) (4 * f); omega
  · rw [hE]; have := key_le (4 * f) n; omega

/-! ### The cover -/

section Cover

variable (alg : CanonAlg n V R M O) {f : ℕ} (G : Groups n f) (x₀ x₁ : V) (r₀ : R)

/-- Input of the nodes of copy `b`. -/
def xs (b : Bool) : V := if b then x₁ else x₀

/-- The tape `ρ` with constant rows `r₀` for the processes of `E`. -/
def ρE (ρ : Tape n R) : Tape n R := fun p j => if G.grp p = 4 then r₀ else ρ p j

/-- The cover: history after round `r` of node `p` of copy `b` (tape `τ`, with constant rows for
the two copies of `E`). Node `(b, p)` hears the processes of `G.hb b`; the sender `q` is the node
`(G.nb b q, q)`. -/
noncomputable def cov (τ : Tape n R) : ℕ → Bool → Fin n → Log n R M
  | 0 => fun _ p => [.draw (ρE G r₀ τ p 1)]
  | r + 1 => fun b p => cov τ r b p ++ (hearList (fun _ => G.hb b) p).map (fun q => .recv q (r + 1)
      (alg.msg q (xs x₀ x₁ (G.nb b q)) (cov τ r (G.nb b q) q))) ++ [.draw (ρE G r₀ τ p (r + 2))]

/-- The cover only depends on the tape rows of `A B C D` up to round `r + 1`. -/
theorem cov_congr {τ τ' : Tape n R} (r : ℕ)
    (h : ∀ X, G.grp X ≠ 4 → ∀ j, 1 ≤ j → j ≤ r + 1 → τ X j = τ' X j) :
    cov alg G x₀ x₁ r₀ τ r = cov alg G x₀ x₁ r₀ τ' r := by
  induction r with
  | zero =>
    funext b p; simp only [cov, ρE]
    split_ifs with hp
    · rfl
    · rw [h p hp 1 le_rfl le_rfl]
  | succ r ih =>
    have ih := ih (fun X hX j h1 h2 => h X hX j h1 (by omega))
    funext b p; simp only [cov, ih, ρE]
    split_ifs with hp
    · rfl
    · rw [h p hp (r + 2) (by omega) le_rfl]

/-! #### `α₂` -/

/-- Byzantine messages of `E` in `α₂`: towards `p`, the message of the copy hosting `p`. -/
noncomputable def byz₂ (ρ : Tape n R) (s : ℕ) (q p : Fin n) : M :=
  alg.msg q (xs x₀ x₁ (G.side p)) (cov alg G x₀ x₁ r₀ ρ (s - 1) (G.side p) q)

/-- Inputs of `C₂`. -/
def I₂ (p : Fin n) : V := xs x₀ x₁ (G.side p)

theorem clean₂_eq (ρ : Tape n R) (r : ℕ) (p : Fin n) (hp : G.grp p ≠ 4) :
    clean alg (I₂ G x₀ x₁) (G.set 4) (fun p => G.hb (G.side p)) (byz₂ alg G x₀ x₁ r₀ ρ) ρ r p =
      cov alg G x₀ x₁ r₀ ρ r (G.side p) p := by
  induction r generalizing p with
  | zero => simp [clean, cov, ρE, hp]
  | succ r ih =>
    rw [clean_succ]; simp only [cov, ih p hp, ρE, hp, if_false]
    congr 2
    apply List.map_congr_left
    intro q _
    simp only [cmsg, Groups.mem_set, byz₂, Nat.add_sub_cancel, Groups.nb]
    split_ifs with hq
    · rfl
    · rw [ih q hq]; rfl

/-! #### `α₀` -/

/-- Byzantine messages of `A` in `α₀`: the messages of `A` in `α₂` (cover copy `true`). -/
noncomputable def byz₀ (ρ : Tape n R) (s : ℕ) (q _p : Fin n) : M :=
  alg.msg q x₁ (cov alg G x₀ x₁ r₀ ρ (s - 1) true q)

theorem clean₀_eq (ρ : Tape n R) (r : ℕ) (p : Fin n) (hp : G.grp p = 1 ∨ G.grp p = 2 ∨ G.grp p = 4) :
    clean alg (fun _ => x₀) (G.set 0) (fun _ => G.hb false) (byz₀ alg G x₀ x₁ r₀ ρ)
      (ρE G r₀ ρ) r p = cov alg G x₀ x₁ r₀ ρ r false p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [clean_succ]; simp only [cov, ih p hp]
    congr 2
    · apply List.map_congr_left
      intro q hq
      rw [mem_hearList] at hq
      simp only [Groups.hb, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true,
        if_false] at hq
      simp only [cmsg, Groups.mem_set, byz₀, Nat.add_sub_cancel, Groups.nb, Groups.side]
      have := (G.grp q).isLt
      by_cases h0 : G.grp q = 0
      · simp [h0, xs]
      · have hq' : G.grp q = 1 ∨ G.grp q = 2 ∨ G.grp q = 4 := by omega
        rw [if_neg h0, ih q hq']
        rcases hq' with h | h | h <;> simp [h, xs]

/-! #### `α₁` -/

/-- Byzantine messages of `C` in `α₁`: the messages of `C` in `α₂` (cover copy `false`). -/
noncomputable def byz₁ (ρ : Tape n R) (s : ℕ) (q _p : Fin n) : M :=
  alg.msg q x₀ (cov alg G x₀ x₁ r₀ ρ (s - 1) false q)

theorem clean₁_eq (ρ : Tape n R) (r : ℕ) (p : Fin n) (hp : G.grp p = 0 ∨ G.grp p = 3 ∨ G.grp p = 4) :
    clean alg (fun _ => x₁) (G.set 2) (fun _ => G.hb true) (byz₁ alg G x₀ x₁ r₀ ρ)
      (ρE G r₀ ρ) r p = cov alg G x₀ x₁ r₀ ρ r true p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [clean_succ]; simp only [cov, ih p hp]
    congr 2
    · apply List.map_congr_left
      intro q hq
      rw [mem_hearList] at hq
      simp only [Groups.hb, Finset.mem_filter, Finset.mem_univ, true_and, if_true] at hq
      simp only [cmsg, Groups.mem_set, byz₁, Nat.add_sub_cancel, Groups.nb, Groups.side]
      have := (G.grp q).isLt
      by_cases h2 : G.grp q = 2
      · simp [h2, xs]
      · have hq' : G.grp q = 0 ∨ G.grp q = 3 ∨ G.grp q = 4 := by omega
        rw [if_neg h2, ih q hq']
        rcases hq' with h | h | h <;> simp [h, xs]

end Cover

end Podc2026.CanonicalRound
