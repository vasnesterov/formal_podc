import Mathlib

/-!
# Information-theoretic lemmas (Section 4, Lemmas 1–2 and Theorem 1)

Spiegelman, Cassuto, Chockler, Keidar. *Space Bounds for Reliable Storage: Fundamental Limits of Coding.*
PODC 2016 (arXiv 1507.05169v1).

An `ℓ`-bit string is modelled as `Fin ℓ → Bool` (Lemma 1, Lemma 2) or as an element of `Fin (2 ^ ℓ)`
(the incremental storage of Theorem 1). `log₂` is `Nat.clog 2` (the paper writes `⌈log₂ ·⌉` in Lemma 1).

* `lemma1` — Lemma 1 (pigeonhole).
* `lemma2` — Lemma 2: an encoder that adaptively chooses among several fixed encoders is itself one fixed
  function, so Lemma 1 applies to it. `lemma2_no_extra_bits` shows that the proof's claim that
  `log₂ m` *additional* bits are needed is false (the conclusion of the lemma is still fine).
* `theorem1_false` — Theorem 1 ("any write with value `u_s ∈ U_s` adds at least `log₂ |U_s|` bits") is
  false, even when the object stores the minimum number of bits after every write.
* `theorem1_cumulative` — what is true: after `s` writes the object stores at least
  `⌈log₂ (|U₁| ⋯ |U_s|)⌉` bits.
* `exists_ne_of_bits_lt`, `restore` — the information-theoretic fact used by the storage lower bound:
  a reader that must output the value of one of finitely many writes, from blocks each of which is a
  function of a single written value, holds at least `D = ⌈log₂ |V|⌉` bits of blocks of one of them.
-/

namespace Podc.ReliableStorageSpace

open Finset

/-- Lemma 1 of [Spiegelman et al.]: if `u₁, …, u_s` can all be recovered from an `ℓ`-bit string
`E(u₁, …, u_s)`, then `ℓ ≥ ⌈log₂ (|U₁| ⋯ |U_s|)⌉`. -/
theorem lemma1 {s ℓ : ℕ} {U : Fin s → Type*} [∀ i, Fintype (U i)]
    (E : (∀ i, U i) → (Fin ℓ → Bool)) (D : ∀ i, (Fin ℓ → Bool) → U i)
    (hD : ∀ u i, D i (E u) = u i) :
    Nat.clog 2 (∏ i, Fintype.card (U i)) ≤ ℓ := by
  have hinj : Function.Injective E := fun u v h => funext fun i => by
    rw [← hD u i, ← hD v i, h]
  have := Fintype.card_le_of_injective E hinj
  simp only [Fintype.card_pi, Fintype.card_bool] at this
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 this

/-- Lemma 2 of [Spiegelman et al.], formalized: a base object that chooses, depending on the values
`u₁, …, u_s`, one of `m` fixed encoders `E j` implements the single fixed function
`u ↦ E (σ u) u`, so Lemma 1 bounds its output length. (The proof in the paper instead claims that
`log₂ m` extra bits must be stored to identify `j`; see `lemma2_no_extra_bits`.) -/
theorem lemma2 {s ℓ m : ℕ} {U : Fin s → Type*} [∀ i, Fintype (U i)]
    (E : Fin m → (∀ i, U i) → (Fin ℓ → Bool)) (σ : (∀ i, U i) → Fin m)
    (D : ∀ i, (Fin ℓ → Bool) → U i) (hD : ∀ u i, D i (E (σ u) u) = u i) :
    Nat.clog 2 (∏ i, Fintype.card (U i)) ≤ ℓ :=
  lemma1 (fun u => E (σ u) u) D hD

/-- The proof of Lemma 2 claims that choosing among `m` encoders costs `log₂ m` additional bits. This is
false: two encoders of `U = Fin 4` into `2` bits, chosen adaptively, are decodable without any extra bit
(`2 = ⌈log₂ 4⌉`). Here `E 0` is used for `u ∈ {0, 1}` and `E 1` (which swaps `2` and `3`) for
`u ∈ {2, 3}`. -/
theorem lemma2_no_extra_bits :
    ∃ (E : Fin 2 → Fin 4 → Fin 4) (σ : Fin 4 → Fin 2) (Dec : Fin 4 → Fin 4),
      E 0 ≠ E 1 ∧ (∀ u, Dec (E (σ u) u) = u) ∧ Nat.clog 2 4 = 2 := by
  refine ⟨![id, ![0, 1, 3, 2]], fun u => if u.val < 2 then 0 else 1, ![0, 1, 3, 2], ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 2
    simp at this
  · decide
  · decide

/-! ### Theorem 1 -/

/-- Incremental storage of a base object that receives two writes `u₁ ∈ U₁`, `u₂ ∈ U₂`, both of which
must stay recoverable from the stored bits: after the first write it stores `ℓ₁` bits `E₁ u₁`, after the
second `ℓ₂` bits `E₂ (E₁ u₁) u₂` (a function of the stored bits and the new value). -/
structure TwoWrites (U₁ U₂ : Type*) where
  ℓ₁ : ℕ
  ℓ₂ : ℕ
  E₁ : U₁ → Fin (2 ^ ℓ₁)
  E₂ : Fin (2 ^ ℓ₁) → U₂ → Fin (2 ^ ℓ₂)
  D₁ : Fin (2 ^ ℓ₁) → U₁
  D₂₁ : Fin (2 ^ ℓ₂) → U₁
  D₂₂ : Fin (2 ^ ℓ₂) → U₂
  hD₁ : ∀ u, D₁ (E₁ u) = u
  hD₂₁ : ∀ u v, D₂₁ (E₂ (E₁ u) v) = u
  hD₂₂ : ∀ u v, D₂₂ (E₂ (E₁ u) v) = v

/-- **Theorem 1 of [Spiegelman et al.] is false.** It claims that a write of `u_s ∈ U_s` adds at least
`log₂ |U_s|` bits to a base object that keeps all written values recoverable. Counterexample: `|U₁| = 5`,
`|U₂| = 3`. The object stores `3 = ⌈log₂ 5⌉` bits after the first write and `4 = ⌈log₂ 15⌉` bits after
the second (both the minimum possible), so the second write adds `1 < log₂ 3` bits. The proof's
"simple subtraction" of two lower bounds is invalid. -/
theorem theorem1_false :
    ∃ T : TwoWrites (Fin 5) (Fin 3),
      T.ℓ₁ = Nat.clog 2 5 ∧ T.ℓ₂ = Nat.clog 2 (5 * 3) ∧
      ((T.ℓ₂ - T.ℓ₁ : ℕ) : ℝ) < Real.logb 2 3 := by
  refine ⟨{ ℓ₁ := 3, ℓ₂ := 4
            E₁ := fun u => ⟨u.val, by omega⟩
            E₂ := fun x v => ⟨(x.val % 5) * 3 + v.val, by omega⟩
            D₁ := fun x => ⟨x.val % 5, by omega⟩
            D₂₁ := fun y => ⟨y.val / 3 % 5, by omega⟩
            D₂₂ := fun y => ⟨y.val % 3, by omega⟩
            hD₁ := by decide
            hD₂₁ := by decide
            hD₂₂ := by decide }, by decide, by decide, ?_⟩
  simp only [Nat.reduceSub, Nat.cast_one]
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  norm_num

/-- What is true instead of Theorem 1 (cumulative form): if all of `u₁, …, u_s` can be recovered from the
`ℓ` bits a base object stores after `s` writes, then `ℓ ≥ ⌈log₂ (|U₁| ⋯ |U_s|)⌉`. This is Lemma 1
applied to the composite encoding, whatever the intermediate states were. -/
theorem theorem1_cumulative {s ℓ : ℕ} {U : Fin s → Type*} [∀ i, Fintype (U i)]
    (E : (∀ i, U i) → Fin (2 ^ ℓ)) (D : ∀ i, Fin (2 ^ ℓ) → U i) (hD : ∀ u i, D i (E u) = u i) :
    Nat.clog 2 (∏ i, Fintype.card (U i)) ≤ ℓ := by
  have hinj : Function.Injective E := fun u v h => funext fun i => by
    rw [← hD u i, ← hD v i, h]
  have := Fintype.card_le_of_injective E hinj
  simp only [Fintype.card_pi, Fintype.card_fin] at this
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 this

/-! ### Black-box restoration -/

section Restore

variable {W J V : Type*} [Fintype V] [DecidableEq W] (sz : J → ℕ) (enc : (j : J) → V → Fin (2 ^ sz j))

/-- If a finite set `t` of code blocks (block `j` is the `sz j`-bit string `enc j v`) has fewer than
`⌈log₂ |V|⌉` bits in total, two different values have the same blocks. -/
theorem exists_ne_of_bits_lt (t : Finset J) (ht : ∑ j ∈ t, sz j < Nat.clog 2 (Fintype.card V)) :
    ∃ v v' : V, v ≠ v' ∧ ∀ j ∈ t, enc j v = enc j v' := by
  classical
  have hcard : Fintype.card ((j : t) → Fin (2 ^ sz j.1)) < Fintype.card V := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_coe_sort t (fun j => 2 ^ sz j), Finset.prod_pow_eq_pow_sum]
    by_contra h
    push Not at h
    exact absurd ((Nat.clog_le_iff_le_pow (by norm_num)).2 h) (not_le.2 ht)
  obtain ⟨v, v', hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun v (j : t) => enc j.1 v) hcard
  exact ⟨v, v', hne, fun j hj => congrFun heq ⟨j, hj⟩⟩

/-- **Restoration needs `D` bits of one write.** Blocks are pairs `(w, j)` (block `j` of the value of
write `w`), with contents `enc j (val w)` for a value assignment `val`. A reader holds the blocks `s`,
and its output `out` depends only on their contents. If for *every* value assignment the output is the
value of one of the writes in the finite set `W`, then for some `w ∈ W` the blocks of `w` in `s` have
at least `⌈log₂ |V|⌉` bits. -/
theorem restore [Nonempty V] (s : Finset (W × J)) (Wr : Finset W)
    (out : ((b : W × J) → Fin (2 ^ sz b.2)) → V)
    (hout : ∀ g g' : (b : W × J) → Fin (2 ^ sz b.2), (∀ b ∈ s, g b = g' b) → out g = out g')
    (hreg : ∀ val : W → V, ∃ w ∈ Wr, out (fun b => enc b.2 (val b.1)) = val w) :
    ∃ w ∈ Wr, Nat.clog 2 (Fintype.card V) ≤ ∑ b ∈ s with b.1 = w, sz b.2 := by
  classical
  by_contra hcon
  push Not at hcon
  -- for each write in `Wr`, two values with the same held blocks
  have hpair : ∀ w ∈ Wr, ∃ v v' : V, v ≠ v' ∧ ∀ b ∈ s, b.1 = w → enc b.2 v = enc b.2 v' := by
    intro w hw
    have h1 := hcon w hw
    rw [← Finset.sum_image (f := sz) (g := Prod.snd) (s := s.filter (·.1 = w))
      (fun x hx y hy hxy => by
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
        exact Prod.ext (hx.2.trans hy.2.symm) hxy)] at h1
    obtain ⟨v, v', hne, h⟩ := exists_ne_of_bits_lt sz enc _ h1
    exact ⟨v, v', hne, fun b hb hbw => h b.2 (Finset.mem_image.2 ⟨b, by simp [hb, hbw], rfl⟩)⟩
  choose! a a' hne hsame using hpair
  let v₀ : V := Classical.arbitrary V
  let val₁ : W → V := fun w => if w ∈ Wr then a w else v₀
  set o := out (fun b => enc b.2 (val₁ b.1)) with ho
  let val₂ : W → V := fun w => if w ∈ Wr then (if a w = o then a' w else a w) else v₀
  have hagree : out (fun b => enc b.2 (val₂ b.1)) = o := by
    rw [ho]
    apply hout
    intro b hb
    simp only [val₁, val₂]
    split_ifs with h1 h2
    · exact (hsame b.1 h1 b hb rfl).symm
    · rfl
    · rfl
  obtain ⟨w, hw, hw'⟩ := hreg val₂
  rw [hagree] at hw'
  simp only [val₂, hw, ite_true] at hw'
  split_ifs at hw' with h
  · exact hne w hw (h.trans hw')
  · exact h hw'.symm

end Restore

end Podc.ReliableStorageSpace
