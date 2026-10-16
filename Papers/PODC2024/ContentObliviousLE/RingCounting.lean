import Mathlib

/-!
# Counting lemmas for one instance of Algorithm 1 on a ring

Abstract versions of Lemmas 5–10 and 16 of Frei–Gelles–Ghazy–Nolin, *Content-Oblivious Leader
Election on Rings* (arXiv 2405.03646). Nodes are `ZMod n`; pulses travel from `v` to `v + 1`.
For node `v`, `ρ v` is the number of pulses received, `σ v` the number sent and `I v` its ID.

* `Profile ρ σ I`: the invariant of Lemma 5 (`σ = ρ + 1` while `ρ < I`, `σ = ρ` afterwards);
* `Edge ρ σ`: channels do not create pulses, `ρ (v + 1) ≤ σ v`.

All lemmas are *static*: they hold for any counters satisfying these invariants, in particular for
every reachable configuration of the algorithms using Algorithm 1 as a sub-routine.
IDs need not be unique (Lemma 15/16).
-/

namespace Podc.ContentOblivious.Ring

open Finset

variable {n : ℕ} [NeZero n]

/-- Induction around the ring. -/
lemma induction (P : ZMod n → Prop) (a : ZMod n) (h0 : P a) (hs : ∀ v, P v → P (v + 1)) :
    ∀ v, P v := by
  intro v
  have key : ∀ k : ℕ, P (a + k) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih => push_cast; rw [← add_assoc]; exact hs _ ih
  have := key (v - a).val
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this

/-- Induction around the ring, backwards. -/
lemma induction_down (P : ZMod n → Prop) (a : ZMod n) (h0 : P a) (hs : ∀ v, P (v + 1) → P v) :
    ∀ v, P v := by
  intro v
  have := induction (fun w => P (-w)) (-a) (by simpa using h0)
    (fun w hw => hs _ (by rwa [neg_add, neg_add_cancel_right])) (-v)
  simpa using this

lemma sum_shift (f : ZMod n → ℕ) (k : ZMod n) : ∑ v, f (v + k) = ∑ v, f v :=
  Equiv.sum_comp (Equiv.addRight k) f

/-- The invariant of Lemma 5. -/
def Profile (ρ σ I : ZMod n → ℕ) : Prop := ∀ v, σ v = ρ v + if ρ v < I v then 1 else 0

/-- Pulses sent by `v` towards `v + 1` bound the pulses received by `v + 1`. -/
def Edge (ρ σ : ZMod n → ℕ) : Prop := ∀ v, ρ (v + 1) ≤ σ v

variable {ρ σ I : ZMod n → ℕ}

lemma Profile.le (h : Profile ρ σ I) (v : ZMod n) : ρ v ≤ σ v := by rw [h v]; omega

/-- A node never sends more than `max ρ I` pulses (used for the bound of Corollary 13). -/
lemma Profile.sigma_le (h : Profile ρ σ I) {M : ℕ} {v : ZMod n} (hρ : ρ v ≤ M) (hI : I v ≤ M) :
    σ v ≤ M := by
  rw [h v]; split_ifs <;> omega

/-- Lemma 8: a configuration where every link is tight (no pulse in transit) has every node past
its ID. -/
lemma Profile.good_of_tight (h : Profile ρ σ I) (ht : ∀ v, ρ (v + 1) = σ v) :
    ∀ v, I v ≤ ρ v := by
  have hsum : ∑ v, σ v = ∑ v, ρ v + ∑ v, (if ρ v < I v then 1 else 0) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => h v
  have h2 : ∑ v, σ v = ∑ v, ρ v := by
    rw [← sum_shift ρ 1]; exact sum_congr rfl fun v _ => (ht v).symm
  have h3 : ∑ v, (if ρ v < I v then 1 else 0 : ℕ) = 0 := by omega
  intro v
  have := (sum_eq_zero_iff.1 h3) v (mem_univ v)
  by_contra hc
  simp [not_le.1 hc] at this

/-- Lemma 7 / Lemma 10: once every node is past its ID, all counters are equal and links are
tight. -/
lemma Profile.tight_of_good (h : Profile ρ σ I) (he : Edge ρ σ) (hg : ∀ v, I v ≤ ρ v) :
    (∀ v, ρ (v + 1) = σ v) ∧ (∀ v, σ v = ρ v) ∧ ∀ v w, ρ v = ρ w := by
  have hσ : ∀ v, σ v = ρ v := fun v => by rw [h v, if_neg (not_lt.2 (hg v))]; simp
  have hle : ∀ v ∈ (univ : Finset (ZMod n)), ρ (v + 1) ≤ ρ v := fun v _ => (hσ v) ▸ he v
  have heq := (sum_eq_sum_iff_of_le hle).1 (sum_shift ρ 1)
  have hstep : ∀ v, ρ (v + 1) = ρ v := fun v => heq v (mem_univ v)
  refine ⟨fun v => by rw [hσ, hstep], hσ, fun v w => ?_⟩
  have := induction (fun x => ρ x = ρ v) v rfl (fun x hx => by rw [hstep, hx]) w
  exact this.symm

/-- Lemma 10 (3): once every node is past its ID, everybody has received and sent exactly
`max I` pulses (given the bound `ρ ≤ max I` of Corollary 13). -/
lemma Profile.eq_max_of_good (h : Profile ρ σ I) (he : Edge ρ σ) (hg : ∀ v, I v ≤ ρ v) {M : ℕ}
    (hb : ∀ v, ρ v ≤ M) {ℓ : ZMod n} (hℓ : I ℓ = M) : ∀ v, ρ v = M ∧ σ v = M := by
  obtain ⟨-, hσ, hc⟩ := h.tight_of_good he hg
  intro v
  have h1 := hc v ℓ
  have := hg ℓ; have := hb v
  refine ⟨by omega, by rw [hσ]; omega⟩

/-- Lemma 16 (generalising Lemma 6 to non-unique IDs): if all nodes of maximal ID `M` have received
at least `M` pulses, then every node is past its ID. -/
lemma Profile.good_of_max_good (h : Profile ρ σ I) (he : Edge ρ σ) {M : ℕ} (hM : ∀ v, I v ≤ M)
    (hmax : ∀ v, I v = M → M ≤ ρ v) {ℓ : ZMod n} (hℓ : I ℓ = M) : ∀ v, I v ≤ ρ v := by
  -- walking backwards from a node of maximal ID
  have back : ∀ x, M ≤ ρ (x + 1) → I x < M → M ≤ ρ x := by
    intro x hx hI
    have := he x; rw [h x] at this; split_ifs at this <;> omega
  have key : ∀ k : ℕ, ∀ y : ZMod n, I (y + k) = M → M ≤ ρ y := by
    intro k
    induction k with
    | zero => intro y hy; exact hmax y (by simpa using hy)
    | succ k ih =>
      intro y hy
      have h1 : M ≤ ρ (y + 1) := ih (y + 1) (by rw [← hy]; push_cast; ring_nf)
      rcases (hM y).lt_or_eq with hlt | heq
      · exact back y h1 hlt
      · exact hmax y heq
  intro v
  have := key (ℓ - v).val v (by rw [ZMod.natCast_zmod_val, add_sub_cancel]; exact hℓ)
  exact (hM v).trans this

/-- Corollary 13 as an inductive step: if all counters are at most `M ≥ max I`, a node that can
still receive a pulse stays at most `M` after receiving it. -/
lemma Profile.succ_le_of_lt (h : Profile ρ σ I) {M : ℕ} (hb : ∀ v, ρ v ≤ M) (hM : ∀ v, I v ≤ M)
    {v : ZMod n} (hlt : ρ (v + 1) < σ v) : ρ (v + 1) + 1 ≤ M := by
  have := h.sigma_le (hb v) (hM v); omega

/-- Reversing the ring turns a counter profile for pulses travelling to `v - 1` into one for pulses
travelling to `v + 1`. -/
lemma Profile.neg (h : Profile ρ σ I) : Profile (fun v => ρ (-v)) (fun v => σ (-v)) (fun v => I (-v)) :=
  fun v => h (-v)

lemma edge_neg (h : ∀ v, ρ (v - 1) ≤ σ v) : Edge (fun v => ρ (-v)) (fun v => σ (-v)) := by
  intro v; have := h (-v); simp only; rwa [neg_add, ← sub_eq_add_neg]

/-- Pigeonhole: `k` distinct positive natural numbers have maximum at least `k`. -/
lemma exists_ge_of_injective {k : ℕ} (f : Fin k → ℕ) (hf : Function.Injective f)
    (hpos : ∀ i, 0 < f i) (hk : 0 < k) : ∃ i, k ≤ f i := by
  by_contra hc
  push_neg at hc
  have hsub : univ.image f ⊆ Finset.Ioo 0 k := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    exact mem_Ioo.2 ⟨hpos i, hc i⟩
  have := card_le_card hsub
  rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin, Nat.card_Ioo] at this
  omega

/-- Distinct steps around the ring give distinct nodes. -/
lemma add_natCast_injective (v : ZMod n) {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : v + (i : ZMod n) = v + j) : i = j := by
  have := add_left_cancel h
  rw [ZMod.natCast_eq_natCast_iff'] at this
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

end Podc.ContentOblivious.Ring
