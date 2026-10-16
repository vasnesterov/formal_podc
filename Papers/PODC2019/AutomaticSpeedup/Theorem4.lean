import Papers.PODC2019.AutomaticSpeedup.WeakColoring
import Papers.PODC2019.AutomaticSpeedup.Lemmas123
import Cslib.Computability.Distributed.Local.Linial

/-!
# Lemma 4 and Theorem 4 of Brandt (PODC 2019, §5.1–5.2), port-numbering version

* `lemma_4`: the speedup lemma for superweak colouring, for deterministic port-numbering
  algorithms without identifiers (the paper states it for order-invariant algorithms with IDs and
  remarks that "an analogous speedup lemma can be achieved for general algorithms in a setting
  without unique IDs"). Chain: Theorem 1's forward half steps, the maximality simplification
  (Theorem 2; edge symmetry is broken by the orientation), the trit description
  (`ViewSystem.solvesE_toTrit`), and Lemma 3.
* `theorem_4`: weak 2-colouring is not solvable in `T` rounds on a class of `Δ`-regular oriented
  graphs that is `t`-independent for `1 ≤ t ≤ T + 1` and rich (`RichFor`), whenever
  `5 T + 7 ≤ log* Δ`.

Tower bounds use CSLib's `Nat.tower` (`tower 0 = 1`, `tower (m+1) = 2 ^ tower m`) and
`Nat.logStar`, and are proved by induction.
-/

namespace AutomaticSpeedup

open Cslib.PortNumbering Problem

/-- **Lemma 4** (port-numbering version, no IDs). Let `k ≥ 2` and `Δ ≥ 2^(4^k + 1)`, and let `𝒢` be
a class of `Δ`-regular graphs whose inputs contain an orientation of every edge, `t`-independent
for some `t ≥ 1`. If superweak `k`-colouring is solvable on `𝒢` in `t` rounds, then superweak
`k'`-colouring, `k' = 2^(2^(5^k))`, is solvable in `t - 1` rounds. -/
theorem lemma_4 {k : ℕ} (hk : 2 ≤ k) {I : Type} {n Δ t : ℕ} {𝒢 : Set (LGraph I n)}
    (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) {o : I → Bool}
    (hor : HasOrientation 𝒢 o) (ht : 1 ≤ t) (hind : IsIndependent 𝒢 t)
    (h : SolvableIn 𝒢 (superweak k) Δ t) :
    SolvableIn 𝒢 (superweak (2 ^ 2 ^ 5 ^ k)) Δ (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply lemma_3 hk hΔ hreg hor
  obtain ⟨A, hA⟩ := (solvableIn_iff_view _ _ _ _).1 h
  rw [solvableIn_iff_view]
  have hdeg : ∀ G v, (viewSystem 𝒢 s).deg G v ≤ Δ := fun G v => (hreg G.1 G.2 v).le
  -- `Π_{1/2}` on edge views (Theorem 1, first half step)
  have h1 := ViewSystem.solvesE_toEdge (ind1_of hind.1) hdeg (solvesN_iff.2 hA)
  -- `Π'_{1/2}` (Theorem 2, edge symmetry from the orientation)
  have h2 := ViewSystem.solvesE_max (edgeAsym_of (hor.edgeAsym (by omega))) h1
  -- the trit description of `Π'_{1/2}`
  have h3 := ViewSystem.solvesE_toTrit h2
  -- `(tritHalf k)_1` in `t - 1` rounds (Theorem 1, second half step)
  have h4 := ViewSystem.solvesP_toPrev (ind2_of hind.2) hdeg h3
  -- `(tritHalf k)'_1 = tritOne k` (Theorem 2)
  have h5 := ViewSystem.solvesP_max h4
  exact ⟨_, solvesP_iff.1 h5⟩

/-! ### Tower bounds -/

theorem tower_le_succ (m : ℕ) : Nat.tower m ≤ Nat.tower (m + 1) :=
  (Nat.lt_two_pow_self).le

theorem tower_mono {m m' : ℕ} (h : m ≤ m') : Nat.tower m ≤ Nat.tower m' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (tower_le_succ _)

/-- `tower (log* n) ≤ n` for `n ≥ 1`. -/
theorem tower_logStar_le : ∀ n : ℕ, 1 ≤ n → Nat.tower (Nat.logStar n) ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [Nat.logStar]
    split_ifs with h
    · simpa [Nat.tower] using hn
    · have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
      have hlt : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
      calc Nat.tower (Nat.logStar (Nat.log 2 n) + 1)
          = 2 ^ Nat.tower (Nat.logStar (Nat.log 2 n)) := rfl
        _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) (ih _ hlt hlog)
        _ ≤ n := Nat.pow_log_le_self 2 (by omega)

theorem tower_le_of_le_logStar {m n : ℕ} (hn : 1 ≤ n) (h : m ≤ Nat.logStar n) :
    Nat.tower m ≤ n :=
  (tower_mono h).trans (tower_logStar_le n hn)

theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self

/-- `2^(4^k + 1) ≤ 2^2^2^2^k`: the degree condition of Lemma 4 holds once `k ≤ log⁽⁴⁾ Δ`. -/
theorem two_pow_four_pow_le (k : ℕ) : 2 ^ (4 ^ k + 1) ≤ 2 ^ 2 ^ 2 ^ 2 ^ k := by
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 : 4 ^ k + 1 ≤ 2 ^ (2 * k + 1) := by
    rw [pow_succ, pow_mul]; norm_num
  have h2 : 2 * k + 1 ≤ 2 ^ 2 ^ k := by
    have a := succ_le_two_pow k
    have b : 2 ^ (k + 1) ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) a
    rw [pow_succ] at b
    omega
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)

theorem add_two_le_two_pow {k : ℕ} (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k _ ih => rw [pow_succ]; omega

/-- `2^2^5^k ≤ F^5(k)` with `F x = 2^x` (for `k ≥ 2`): Lemma 4's `k'` is at most `F^5(k)`. -/
theorem lemma4_bound {k : ℕ} (hk : 2 ≤ k) : 2 ^ 2 ^ 5 ^ k ≤ 2 ^ 2 ^ 2 ^ 2 ^ 2 ^ k := by
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 : 5 ^ k ≤ 2 ^ (3 * k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) k
  have h2 : 3 * k ≤ 2 ^ 2 ^ k := by
    have a := add_two_le_two_pow hk
    have b : 2 ^ (k + 2) ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) a
    have c := succ_le_two_pow k
    rw [pow_add] at b
    nlinarith
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)

theorem two_mul_add_three_le {k : ℕ} (hk : 4 ≤ k) : 2 * k + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k _ ih => rw [pow_succ]; omega

/-- The sequence `k_i` of the proof of Theorem 4: `k_0 = 2`, `k_{i+1} = F^5(k_i)`, `F x = 2^x`;
i.e. `k_i = tower (5 i + 1)`. -/
def kSeq (i : ℕ) : ℕ := Nat.tower (5 * i + 1)

theorem kSeq_zero : kSeq 0 = 2 := rfl

theorem kSeq_succ (i : ℕ) : kSeq (i + 1) = 2 ^ 2 ^ 2 ^ 2 ^ 2 ^ kSeq i := by
  simp only [kSeq, show 5 * (i + 1) + 1 = 5 * i + 1 + 1 + 1 + 1 + 1 + 1 by ring]; rfl

theorem two_le_kSeq (i : ℕ) : 2 ≤ kSeq i := tower_mono (show 1 ≤ 5 * i + 1 by omega)

/-! ### Theorem 4 -/

/-- **Theorem 4** (port-numbering version). Let `𝒢` be a class of `Δ`-regular graphs (on `n`
nodes) whose inputs contain an orientation `o` of every edge, that is `t`-independent for all
`1 ≤ t ≤ T + 1`, and that is rich (`RichFor`) for an input list `ι` of length `Δ` with at least
`(Δ - 1) / 2` ports of each orientation. If `5 T + 7 ≤ log* Δ`, then weak 2-colouring is not
solvable on `𝒢` in `T` rounds.

Proof (as in the paper): weak 2-colouring in `T` rounds gives its pointer version, hence superweak
2-colouring, in `T + 1` rounds; `T + 1` applications of Lemma 4 (with monotonicity in `k`) give
superweak `k_{T+1}`-colouring in `0` rounds, `k_i = F^5(k_{i-1})`, `k_0 = 2`; this is impossible
since `k_{T+1} + 1 ≤ (Δ - 1)/2`. -/
theorem theorem_4 {I : Type} {n Δ T : ℕ} {𝒢 : Set (LGraph I n)}
    (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) {o : I → Bool} (hor : HasOrientation 𝒢 o)
    (hind : ∀ t, 1 ≤ t → t ≤ T + 1 → IsIndependent 𝒢 t)
    (ι : List I) (hlen : ι.length = Δ) (hrich : RichFor 𝒢 o ι)
    (hcount : ∀ b, (Δ - 1) / 2 ≤ (Finset.univ.filter fun p : Fin ι.length => o ι[p] = b).card)
    (hT : 5 * T + 7 ≤ Nat.logStar Δ) :
    ¬ Weak2ColSolvableIn 𝒢 T := by
  intro hw
  have hΔ1 : 1 ≤ Δ := by
    rcases Nat.eq_zero_or_pos Δ with h | h
    · subst h; simp [Nat.logStar] at hT
    · exact h
  have htow : Nat.tower (5 * T + 7) ≤ Δ := tower_le_of_le_logStar hΔ1 hT
  -- superweak 2-colouring in `T + 1` rounds
  have h0 : SolvableIn 𝒢 (superweak (kSeq 0)) Δ (T + 1 - 0) :=
    (solvableIn_weakPtr hΔ1 hreg hw).of_labelHom (weakPtrToSuperweak Δ)
  -- `j` applications of Lemma 4
  have key : ∀ j ≤ T + 1, SolvableIn 𝒢 (superweak (kSeq j)) Δ (T + 1 - j) := by
    intro j
    induction j with
    | zero => intro _; exact h0
    | succ j ih =>
      intro hj
      have hk := two_le_kSeq j
      have hΔk : 2 ^ (4 ^ kSeq j + 1) ≤ Δ := by
        refine (two_pow_four_pow_le _).trans (le_trans ?_ htow)
        exact tower_mono (show 5 * j + 1 + 4 ≤ 5 * T + 7 by omega)
      have := lemma_4 hk hΔk hreg hor (by omega) (hind _ (by omega) (by omega)) (ih (by omega))
      rw [show T + 1 - j - 1 = T + 1 - (j + 1) by omega] at this
      exact this.superweak_mono (by rw [kSeq_succ]; exact lemma4_bound hk)
  have hfin := key (T + 1) le_rfl
  rw [Nat.sub_self] at hfin
  refine not_solvableIn_superweak_zero ι hlen hrich (fun b => le_trans ?_ (hcount b)) hfin
  -- `k_{T+1} + 1 ≤ (Δ - 1) / 2`
  have h3 : 4 ≤ kSeq (T + 1) := tower_mono (show 2 ≤ 5 * (T + 1) + 1 by omega)
  have h4 := two_mul_add_three_le h3
  have h5 : 2 ^ kSeq (T + 1) ≤ Δ := by
    refine le_trans ?_ htow
    show Nat.tower (5 * (T + 1) + 1 + 1) ≤ _
    exact tower_mono (by omega)
  omega

/-- **Theorem 4** with the paper's runtime condition `1 ≤ T ≤ (log* Δ - 8) / 5` (§5.2). -/
theorem theorem_4_paper {I : Type} {n Δ T : ℕ} {𝒢 : Set (LGraph I n)}
    (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) {o : I → Bool} (hor : HasOrientation 𝒢 o)
    (hind : ∀ t, 1 ≤ t → t ≤ T + 1 → IsIndependent 𝒢 t)
    (ι : List I) (hlen : ι.length = Δ) (hrich : RichFor 𝒢 o ι)
    (hcount : ∀ b, (Δ - 1) / 2 ≤ (Finset.univ.filter fun p : Fin ι.length => o ι[p] = b).card)
    (hT1 : 1 ≤ T) (hT : T ≤ (Nat.logStar Δ - 8) / 5) :
    ¬ Weak2ColSolvableIn 𝒢 T :=
  theorem_4 hreg hor hind ι hlen hrich hcount (by omega)

end AutomaticSpeedup
