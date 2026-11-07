import Papers.PODC2016.UniformDeploymentRings.Defs

/-!
# Uniform deployment in asynchronous rings — combinatorics on words (Lemmas 2–4)

Lemmas 2, 3 and 4 of Section 4.2 of
[M. Shibata, T. Mega, F. Ooshita, H. Kakugawa, T. Masuzawa, *Uniform deployment of mobile agents
in asynchronous rings*, PODC 2016; JPDC 119 (2018)], about the estimation rule of Algorithm 4
(`est`, see `Defs.lean`): an agent walking around the ring records the distances between
consecutive token nodes and stops at the first `4m` such that the recorded sequence is `S⁴` with
`|S| = m`; it estimates `k' = m` tokens and `n' = ΣS` nodes.

* `HasPeriodOn f p L`, `HasPeriodOn.gcd` : a weak form of the Fine–Wilf periodicity lemma
  (two periods `p, q` on a segment of length `≥ p + q` give the period `gcd p q`).
* `lemma_2` (Lemma 2, cited by the paper from Kawai et al., SIROCCO 2012), for lists, and its
  functional form `lemma_2_fun`.
* `ringWord A i` : the infinite distance sequence observed by the agent starting at the `i`-th
  token of a ring with distance sequence `A` (`A` read cyclically from index `i`).
* `est_ringWord_pos`, `est_ringWord_le`, `fourRep_est_ringWord` : the estimation terminates
  within one round.
* `lemma_3` (Lemma 3): a wrong estimate of `n` is at most `n / 2`; `lemma_3_card`: a wrong
  estimate `k'` of `k` satisfies `2k' ≤ k`.
* `lemma_4` (Lemma 4): in an aperiodic ring some agent estimates `k` correctly; `lemma_4_sum`:
  it estimates `n` correctly. `sum_est_ringWord_eq_iff`: with positive distances, estimating `n`
  correctly is the same as estimating `k` correctly.
* An `example` checks the ring of Fig. 9 (`k' = 2`, `n' = 4` for one agent, `k' = 9` for another).

Proof of Lemma 4: we follow the paper (an agent `a_m` with maximal estimate `ℓ`; the agent
`a_{m+ℓ}` has the same estimate, by Lemma 2), but we choose `a_m` maximizing the estimated number
of tokens rather than of nodes, and conclude directly: the word read from `a_m` then has the
periods `ℓ` and `k`, hence the period `gcd ℓ k < k` (`HasPeriodOn.gcd`), so the ring is periodic.

The statements for general `k`-periodic words `w : ℕ → ℕ` (`lemma_3_word`, `lemma_4_word`) need
no positivity of the distances.
-/

namespace Podc.UniformDeploymentRings

/-! ### Periods on an initial segment -/

/-- `f` has period `p` on the initial segment `[0, L)` of `ℕ`. -/
def HasPeriodOn {α : Type*} (f : ℕ → α) (p L : ℕ) : Prop := ∀ x, x + p < L → f (x + p) = f x

theorem HasPeriodOn.mono {α : Type*} {f : ℕ → α} {p L L' : ℕ} (h : HasPeriodOn f p L)
    (hL : L' ≤ L) : HasPeriodOn f p L' :=
  fun x hx => h x (by omega)

/-- Weak Fine–Wilf lemma: if `f` has periods `p` and `q` on `[0, L)` with `p + q ≤ L`, then it
has period `gcd p q` there. -/
-- CSLib candidate
theorem HasPeriodOn.gcd {α : Type*} {f : ℕ → α} {p q L : ℕ} (hp : HasPeriodOn f p L)
    (hq : HasPeriodOn f q L) (hL : p + q ≤ L) : HasPeriodOn f (Nat.gcd p q) L := by
  induction h : p + q using Nat.strong_induction_on generalizing p q L with
  | _ n ih =>
  wlog hqp : q ≤ p generalizing p q
  · rw [Nat.gcd_comm]; exact this hq hp (by omega) (by omega) (by omega)
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simpa using hp
  rcases eq_or_lt_of_le hqp with rfl | hqp'
  · simpa using hp
  have hr : HasPeriodOn f (p - q) (L - q) := by
    intro x hx
    have h1 := hq (x + (p - q)) (by omega)
    have h2 := hp x (by omega)
    rw [show x + (p - q) + q = x + p by omega] at h1
    rw [← h1, h2]
  have hg := ih (p - q + q) (by omega) hr (hq.mono (by omega)) (by omega) rfl
  rw [Nat.gcd_sub_self_left hqp] at hg
  have hgpos : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_right _ hq0
  have hgle : Nat.gcd p q ≤ p - q :=
    Nat.le_of_dvd (by omega) (Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
  intro x hx
  by_cases hx' : x + Nat.gcd p q < L - q
  · exact hg x hx'
  · have h1 := hq (x - q + Nat.gcd p q) (by omega)
    have h2 := hq (x - q) (by omega)
    have h3 := hg (x - q) (by omega)
    rw [show x - q + Nat.gcd p q + q = x + Nat.gcd p q by omega] at h1
    rw [show x - q + q = x by omega] at h2
    rw [h1, h3, h2]

/-- Functional form of Lemma 2: if `f` has periods `p` and `q < p` on `[0, 3q)`, then
`2q ≤ p`, or `f` has a period `g` on `[0, 3q)` that is a proper divisor of `q`. -/
theorem lemma_2_fun {α : Type*} {f : ℕ → α} {p q : ℕ} (hp : HasPeriodOn f p (3 * q))
    (hq : HasPeriodOn f q (3 * q)) (hlt : q < p) :
    2 * q ≤ p ∨ ∃ g, 0 < g ∧ g < q ∧ g ∣ q ∧ HasPeriodOn f g (3 * q) := by
  by_cases h2 : 2 * q ≤ p
  · exact Or.inl h2
  right
  have hq0 : 0 < q := by omega
  have hg := hp.gcd hq (by omega)
  refine ⟨Nat.gcd p q, Nat.gcd_pos_of_pos_right _ hq0, ?_, Nat.gcd_dvd_right _ _, hg⟩
  rcases (Nat.le_of_dvd hq0 (Nat.gcd_dvd_right p q)).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨c, hc⟩ := h ▸ Nat.gcd_dvd_left p q
    rcases c with _ | _ | c
    · omega
    · omega
    · rw [hc] at h2; apply h2; nlinarith

theorem getElem?_append3 {α : Type*} (A : List α) (j : ℕ) (hj : j < 3 * A.length) :
    (A ++ A ++ A)[j]? = A[j % A.length]? := by
  rw [List.append_assoc]
  by_cases h1 : j < A.length
  · rw [List.getElem?_append_left h1, Nat.mod_eq_of_lt h1]
  rw [List.getElem?_append_right (by omega)]
  by_cases h2 : j - A.length < A.length
  · rw [List.getElem?_append_left h2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h2]
  · rw [List.getElem?_append_right (by omega), Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.sub_sub]

/-- Lemma 2 of the paper (cited from Kawai et al., SIROCCO 2012): if `|B| < |A|` and `B³` is a
prefix of `A³`, then `|B| ≤ |A| / 2` or `B` is periodic (a nontrivial rotation of `B` fixes `B`). -/
theorem lemma_2 {α : Type*} (A B : List α) (hlt : B.length < A.length)
    (hpre : B ++ B ++ B <+: A ++ A ++ A) :
    2 * B.length ≤ A.length ∨ ∃ x, 0 < x ∧ x < B.length ∧ B.rotate x = B := by
  set p := A.length
  set q := B.length
  let f : ℕ → Option α := fun j => (A ++ A ++ A)[j]?
  have hfB : ∀ j < 3 * q, f j = B[j % q]? := by
    intro j hj
    obtain ⟨t, ht⟩ := hpre
    simp only [f, ← ht]
    rw [List.getElem?_append_left (by simp; omega), getElem?_append3 B j hj]
  have hp : HasPeriodOn f p (3 * q) := by
    intro x hx
    simp only [f]
    rw [getElem?_append3 A _ (by omega), getElem?_append3 A _ (by omega), Nat.add_mod_right]
  have hq : HasPeriodOn f q (3 * q) := by
    intro x hx
    rw [hfB _ hx, hfB _ (by omega), Nat.add_mod_right]
  rcases lemma_2_fun hp hq hlt with h | ⟨g, hg0, hgq, -, hg⟩
  · exact Or.inl h
  refine Or.inr ⟨g, hg0, hgq, List.ext_getElem (by simp) fun j h1 h2 => ?_⟩
  rw [List.getElem_rotate]
  have hjq : j < q := h2
  have e1 := hfB j (by omega)
  have e2 := hfB (j + g) (by omega)
  rw [hg j (by omega), e1, Nat.mod_eq_of_lt hjq] at e2
  rw [List.getElem?_eq_getElem hjq] at e2
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))] at e2
  exact (Option.some.inj e2).symm

/-! ### The estimation rule on periodic words -/

theorem two_mul_le_of_dvd_of_lt {g m : ℕ} (hd : g ∣ m) (hlt : g < m) : 2 * g ≤ m := by
  obtain ⟨c, rfl⟩ := hd
  rcases c with _ | _ | c
  · omega
  · omega
  · nlinarith

theorem est_spec {w : ℕ → ℕ} (h : ∃ m, 0 < m ∧ FourRep w m) :
    0 < est w ∧ FourRep w (est w) ∧ ∀ m, 0 < m → FourRep w m → est w ≤ m := by
  classical
  unfold est
  rw [dite_eq_left h]
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun m hm hf => Nat.find_min' h ⟨hm, hf⟩⟩

/-- The infinite word `w` read from position `i` on. -/
def shiftWord (w : ℕ → ℕ) (i : ℕ) : ℕ → ℕ := fun j => w (i + j)

section Periodic

variable {w : ℕ → ℕ} {k : ℕ}

/-- On a `k`-periodic word the estimation stops within one round: `0 < est w ≤ k`, the observed
prefix of length `4 · est w` is a fourth power, and no shorter fourth power was seen before. -/
theorem est_props (hk : 0 < k) (hw : ∀ j, w (j + k) = w j) :
    0 < est w ∧ est w ≤ k ∧ FourRep w (est w) ∧ ∀ m, 0 < m → m < est w → ¬ FourRep w m := by
  obtain ⟨h1, h2, h3⟩ := est_spec ⟨k, hk, fun x _ => hw x⟩
  exact ⟨h1, h3 k hk (fun x _ => hw x), h2, fun m hm hlt hf => by have := h3 m hm hf; omega⟩

theorem periodic_shiftWord (hw : ∀ j, w (j + k) = w j) (i : ℕ) :
    ∀ j, shiftWord w i (j + k) = shiftWord w i j := fun j => by
  simp only [shiftWord]; rw [← Nat.add_assoc, hw]

theorem periodic_add_mul (hw : ∀ j, w (j + k) = w j) (j t : ℕ) : w (j + t * k) = w j := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.succ_mul, ← Nat.add_assoc, hw, ih]

theorem shiftWord_mod (hw : ∀ j, w (j + k) = w j) (i : ℕ) :
    shiftWord w (i % k) = shiftWord w i := by
  funext j
  simp only [shiftWord]
  conv_rhs => rw [← Nat.mod_add_div i k]
  rw [show i % k + k * (i / k) + j = i % k + j + i / k * k by ring, periodic_add_mul hw]

theorem sum_shiftWord (hw : ∀ j, w (j + k) = w j) (i : ℕ) :
    ∑ j ∈ Finset.range k, shiftWord w i j = ∑ j ∈ Finset.range k, w j := by
  induction i with
  | zero => simp [shiftWord]
  | succ i ih =>
    have h1 := Finset.sum_range_succ (shiftWord w i) k
    have h2 := Finset.sum_range_succ' (shiftWord w i) k
    have h3 : shiftWord w i k = shiftWord w i 0 := by
      simpa using periodic_shiftWord hw i 0
    have h4 : ∀ j, shiftWord w i (j + 1) = shiftWord w (i + 1) j := fun j => by
      simp only [shiftWord]; ring_nf
    simp only [h4] at h2
    omega

/-- Lemma 3 (number of tokens) for an arbitrary `k`-periodic word: a wrong estimate `k' ≠ k`
satisfies `k' ≤ k / 2`. -/
theorem lemma_3_word (hk : 0 < k) (hw : ∀ j, w (j + k) = w j) (hne : est w ≠ k) :
    2 * est w ≤ k := by
  obtain ⟨h0, hle, hf, hmin⟩ := est_props hk hw
  have hp : HasPeriodOn w k (3 * est w) := fun x _ => hw x
  have hq : HasPeriodOn w (est w) (3 * est w) := fun x hx => hf x (by omega)
  rcases lemma_2_fun hp hq (by omega) with h | ⟨g, hg0, hgm, hgd, hg⟩
  · exact h
  · exfalso
    have := two_mul_le_of_dvd_of_lt hgd hgm
    exact hmin g hg0 hgm fun x hx => hg x (by omega)

/-- If the estimate `k'` of `k` is wrong, the first `2k'` letters are `S S` with `|S| = k'`, so
`2 · Σ S ≤ Σ_{j < k} w j`. -/
theorem two_mul_sum_est_le (hk : 0 < k) (hw : ∀ j, w (j + k) = w j) (hne' : est w ≠ k) :
    2 * ∑ j ∈ Finset.range (est w), w j ≤ ∑ j ∈ Finset.range k, w j := by
  have h2 := lemma_3_word hk hw hne'
  obtain ⟨-, -, hf, -⟩ := est_props hk hw
  calc 2 * ∑ j ∈ Finset.range (est w), w j
      = ∑ j ∈ Finset.range (est w + est w), w j := by
        rw [Finset.sum_range_add, two_mul]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [add_comm]
        exact (hf j (by omega)).symm
    _ ≤ ∑ j ∈ Finset.range k, w j := Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- Lemma 3 (number of nodes) for an arbitrary `k`-periodic word: if the estimated length
`n' = Σ_{j < k'} w j` of the ring differs from `n = Σ_{j < k} w j`, then `n' ≤ n / 2`. -/
theorem lemma_3_word_sum (hk : 0 < k) (hw : ∀ j, w (j + k) = w j)
    (hne : ∑ j ∈ Finset.range (est w), w j ≠ ∑ j ∈ Finset.range k, w j) :
    2 * ∑ j ∈ Finset.range (est w), w j ≤ ∑ j ∈ Finset.range k, w j :=
  two_mul_sum_est_le hk hw fun h => hne (by rw [h])

/-- Lemma 4 for an arbitrary `k`-periodic word `w` with minimal period `k`: some agent
(starting position `i < k`) estimates the number `k` of tokens correctly. -/
theorem lemma_4_word (hk : 0 < k) (hw : ∀ j, w (j + k) = w j)
    (hprim : ∀ x, 0 < x → x < k → ¬ ∀ j, w (j + x) = w j) :
    ∃ i < k, est (shiftWord w i) = k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm, hmax⟩ := (Finset.range k).exists_max_image (fun i => est (shiftWord w i))
    ⟨0, by simp [hk]⟩
  set ℓ := est (shiftWord w m) with hℓ
  have hmax' : ∀ i, est (shiftWord w i) ≤ ℓ := fun i => by
    rw [← shiftWord_mod hw]; exact hmax _ (by simp [Nat.mod_lt _ hk])
  have hℓk : ℓ < k := lt_of_le_of_ne (est_props hk (periodic_shiftWord hw m)).2.1
    (hcon m (by simpa using hm))
  -- Key step: an agent with maximal estimate `ℓ` is followed, `ℓ` tokens later, by another one.
  have step : ∀ i, est (shiftWord w i) = ℓ → est (shiftWord w (i + ℓ)) = ℓ := by
    intro i hi
    obtain ⟨u0, -, uf, umin⟩ := est_props hk (periodic_shiftWord hw i)
    rw [hi] at u0 uf umin
    obtain ⟨v0, -, vf, vmin⟩ := est_props hk (periodic_shiftWord hw (i + ℓ))
    have hle := hmax' (i + ℓ)
    by_contra hne
    have hlt' := lt_of_le_of_ne hle hne
    have huv : ∀ x, shiftWord w (i + ℓ) x = shiftWord w i (x + ℓ) := fun x => by
      simp only [shiftWord]; ring_nf
    by_cases h2 : 2 * est (shiftWord w (i + ℓ)) ≤ ℓ
    · apply umin _ v0 hlt'
      intro x hx
      rw [← uf (x + est (shiftWord w (i + ℓ))) (by omega), ← huv, vf x hx, huv,
        uf x (by omega)]
    · have hp : HasPeriodOn (shiftWord w (i + ℓ)) ℓ (3 * est (shiftWord w (i + ℓ))) := by
        intro x hx
        rw [huv, huv, uf (x + ℓ) (by omega)]
      have hq : HasPeriodOn (shiftWord w (i + ℓ)) (est (shiftWord w (i + ℓ)))
          (3 * est (shiftWord w (i + ℓ))) := fun x hx => vf x (by omega)
      rcases lemma_2_fun hp hq hlt' with h | ⟨g, hg0, hgl, hgd, hg⟩
      · exact h2 h
      · have := two_mul_le_of_dvd_of_lt hgd hgl
        exact vmin g hg0 hgl fun x hx => hg x (by omega)
  have iter : ∀ t, est (shiftWord w (m + t * ℓ)) = ℓ := by
    intro t
    induction t with
    | zero => simp [hℓ]
    | succ t ih => rw [Nat.succ_mul, ← Nat.add_assoc]; exact step _ ih
  have hℓ0 : 0 < ℓ := (est_props hk (periodic_shiftWord hw m)).1
  -- Hence the word read from `m` has period `ℓ` everywhere.
  have hper : ∀ j, shiftWord w m (j + ℓ) = shiftWord w m j := by
    intro j
    have hf := (est_props hk (periodic_shiftWord hw (m + j / ℓ * ℓ))).2.2.1
    rw [iter] at hf
    have := hf (j % ℓ) (by have := Nat.mod_lt j hℓ0; omega)
    have hj := Nat.div_add_mod' j ℓ
    simp only [shiftWord] at this ⊢
    rw [show m + (j + ℓ) = m + j / ℓ * ℓ + (j % ℓ + ℓ) by omega,
      show m + j = m + j / ℓ * ℓ + j % ℓ by omega]
    exact this
  -- Combined with the period `k`, it has period `gcd ℓ k < k`: the ring is periodic.
  have hgcd : ∀ x, shiftWord w m (x + Nat.gcd ℓ k) = shiftWord w m x := by
    intro x
    have h1 : HasPeriodOn (shiftWord w m) ℓ (x + Nat.gcd ℓ k + ℓ + k + 1) := fun y _ => hper y
    have h2 : HasPeriodOn (shiftWord w m) k (x + Nat.gcd ℓ k + ℓ + k + 1) :=
      fun y _ => periodic_shiftWord hw m y
    exact (h1.gcd h2 (by omega)) x (by omega)
  have hg0 : 0 < Nat.gcd ℓ k := Nat.gcd_pos_of_pos_left _ hℓ0
  have hgk : Nat.gcd ℓ k < k := lt_of_le_of_lt (Nat.le_of_dvd hℓ0 (Nat.gcd_dvd_left _ _)) hℓk
  apply hprim _ hg0 hgk
  intro j
  have e := hgcd (j + (k - m))
  simp only [shiftWord] at e
  rw [show m + (j + (k - m) + Nat.gcd ℓ k) = j + Nat.gcd ℓ k + k by
      have : m < k := by simpa using hm
      omega,
    show m + (j + (k - m)) = j + k by
      have : m < k := by simpa using hm
      omega, hw, hw] at e
  exact e

end Periodic

/-! ### Rings given by their distance sequence -/

/-- The distance sequence of a ring, read cyclically: `cycWord A j = A[j mod |A|]`. -/
def cycWord (A : List ℕ) : ℕ → ℕ := fun j => A.getD (j % A.length) 0

/-- The distance sequence `(d₀, d₁, …)` observed by the agent starting at the `i`-th token of a
ring whose distance sequence (from token `0`) is `A`: `dⱼ = A[(i + j) mod |A|]`. -/
def ringWord (A : List ℕ) (i : ℕ) : ℕ → ℕ := shiftWord (cycWord A) i

theorem ringWord_apply (A : List ℕ) (i j : ℕ) :
    ringWord A i j = A.getD ((i + j) % A.length) 0 := rfl

theorem periodic_cycWord (A : List ℕ) : ∀ j, cycWord A (j + A.length) = cycWord A j := by
  intro j; simp only [cycWord, Nat.add_mod_right]

theorem periodic_ringWord (A : List ℕ) (i : ℕ) :
    ∀ j, ringWord A i (j + A.length) = ringWord A i j :=
  periodic_shiftWord (periodic_cycWord A) i

theorem sum_range_getD (A : List ℕ) : ∑ j ∈ Finset.range A.length, A.getD j 0 = A.sum := by
  induction A with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.sum_cons, add_comm]

theorem sum_ringWord (A : List ℕ) (i : ℕ) :
    ∑ j ∈ Finset.range A.length, ringWord A i j = A.sum := by
  rw [ringWord, sum_shiftWord (periodic_cycWord A), ← sum_range_getD]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [cycWord, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]

/-- The estimation of Algorithm 4 terminates within one round: `0 < k' ≤ k`, and the first `4k'`
observed distances form a fourth power `S⁴` with `|S| = k'`. -/
theorem est_ringWord_spec (A : List ℕ) (hA : A ≠ []) (i : ℕ) :
    0 < est (ringWord A i) ∧ est (ringWord A i) ≤ A.length ∧
      FourRep (ringWord A i) (est (ringWord A i)) := by
  have hk : 0 < A.length := List.length_pos_iff.mpr hA
  obtain ⟨h1, h2, h3, -⟩ :=
    est_props hk (periodic_ringWord A i)
  exact ⟨h1, h2, h3⟩

/-- Lemma 3 (number of tokens): if the agent starting at token `i` estimates a wrong number
`k' ≠ k` of agents, then `k' ≤ k / 2`. -/
theorem lemma_3_card (A : List ℕ) (hA : A ≠ []) (i : ℕ) (hne : est (ringWord A i) ≠ A.length) :
    2 * est (ringWord A i) ≤ A.length :=
  lemma_3_word (List.length_pos_iff.mpr hA) (periodic_ringWord A i) hne

/-- Lemma 3 of the paper: if an agent estimates a wrong number of nodes `n' ≠ n` (where `n` is
the sum of the distance sequence `A` of the ring and `n'` the sum of the first `k'` distances it
observed), then `n' ≤ n / 2`. -/
theorem lemma_3 (A : List ℕ) (i : ℕ)
    (hne : ∑ j ∈ Finset.range (est (ringWord A i)), ringWord A i j ≠ A.sum) :
    2 * ∑ j ∈ Finset.range (est (ringWord A i)), ringWord A i j ≤ A.sum := by
  rcases eq_or_ne A [] with rfl | hA
  · exfalso; apply hne; simp [ringWord, shiftWord, cycWord]
  have h := lemma_3_word_sum (List.length_pos_iff.mpr hA)
    (periodic_ringWord A i)
  rw [sum_ringWord] at h
  exact h hne

/-- With positive distances, an agent estimates `n` correctly iff it estimates `k` correctly. -/
theorem sum_est_ringWord_eq_iff (A : List ℕ) (hA : A ≠ []) (hpos : ∀ a ∈ A, 0 < a) (i : ℕ) :
    ∑ j ∈ Finset.range (est (ringWord A i)), ringWord A i j = A.sum ↔
      est (ringWord A i) = A.length := by
  constructor
  · intro h
    by_contra hne
    have h2 := two_mul_sum_est_le (List.length_pos_iff.mpr hA) (periodic_ringWord A i) hne
    rw [sum_ringWord, h] at h2
    have : 0 < A.sum := by
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hA
      have := hpos a (by simp)
      simp only [List.sum_cons]; omega
    omega
  · intro h
    rw [h, sum_ringWord]

/-- Lemma 4 of the paper: if the ring is aperiodic (no nontrivial rotation of its distance
sequence `A` fixes `A`), then at least one agent estimates the number `k` of agents (and hence,
by `sum_ringWord`, the number `n` of nodes) correctly. -/
theorem lemma_4 (A : List ℕ) (hA : A ≠ [])
    (hprim : ∀ x, 0 < x → x < A.length → A.rotate x ≠ A) :
    ∃ i < A.length, est (ringWord A i) = A.length := by
  have hk : 0 < A.length := List.length_pos_iff.mpr hA
  apply lemma_4_word hk (periodic_cycWord A)
  intro x hx0 hxk hx
  apply hprim x hx0 hxk
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  have := hx j
  simp only [cycWord, Nat.mod_eq_of_lt h2] at this
  rw [List.getElem_rotate]
  have e1 : A.getD ((j + x) % A.length) 0 = A[(j + x) % A.length]'(Nat.mod_lt _ hk) :=
    by rw [List.getD_eq_getElem]
  rw [List.getD_eq_getElem _ _ h2, e1] at this
  exact this

/-- Lemma 4, in terms of the number of nodes: in an aperiodic ring at least one agent estimates
the number `n` of nodes correctly. -/
theorem lemma_4_sum (A : List ℕ) (hA : A ≠ [])
    (hprim : ∀ x, 0 < x → x < A.length → A.rotate x ≠ A) :
    ∃ i < A.length, ∑ j ∈ Finset.range (est (ringWord A i)), ringWord A i j = A.sum := by
  obtain ⟨i, hi, h⟩ := lemma_4 A hA hprim
  exact ⟨i, hi, by rw [h, sum_ringWord]⟩

/-- `est w = m` as soon as `S⁴` with `|S| = m` is the first fourth power observed. -/
theorem est_eq_of {w : ℕ → ℕ} {m : ℕ} (hm : 0 < m) (hf : FourRep w m)
    (hmin : ∀ m', 0 < m' → m' < m → ¬ FourRep w m') : est w = m := by
  obtain ⟨h0, h1, h2⟩ := est_spec ⟨m, hm, hf⟩
  have := h2 m hm hf
  by_contra hne
  exact hmin _ h0 (by omega) h1

/-- The example of Fig. 9 (an aperiodic ring with `k = 9`, `n = 27`): the agent starting at the
second token observes `(1, 3)⁴` and estimates `k' = 2`, `n' = 4`, while the agent starting at the
first token estimates correctly. -/
example : est (ringWord [11, 1, 3, 1, 3, 1, 3, 1, 3] 1) = 2 ∧
    est (ringWord [11, 1, 3, 1, 3, 1, 3, 1, 3] 0) = 9 := by
  constructor
  · refine est_eq_of (by norm_num) (by decide) ?_
    intro m' h0 h1; obtain rfl : m' = 1 := by omega
    decide
  · refine est_eq_of (by norm_num) (by decide) ?_
    intro m' h0 h1
    interval_cases m' <;> decide

end Podc.UniformDeploymentRings
