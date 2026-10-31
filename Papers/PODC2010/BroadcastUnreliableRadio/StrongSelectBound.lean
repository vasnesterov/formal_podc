import Papers.PODC2010.BroadcastUnreliableRadio.StrongSelect

/-!
# Strong select broadcasts in `O(n^{3/2} √log n)` rounds (Lemmas 8, 9 and Theorem 10)

Kuhn, Lynch, Newport, Oshman, Richa. *Broadcasting in Unreliable Radio Networks.* PODC 2010.

The model is described in `StrongSelect.lean`. Densities are handled by cross-multiplication:
with `ρ = 1 / D`, `D = 12 f 2 ^ smax` (an integer), `den(1, t) < ρ` becomes `#inf t * D < t`.

**Repair of the density argument.** The paper lets `T` be the least round with `den(1, T) < ρ`,
where `den` counts nodes receiving the message *for the first time* in an interval. If the source
is not counted, then `T = 1` whenever nobody receives the message in round 1 (e.g. the source's id
is not in `F_1[1]`), and the first claim of the proof of Theorem 10 ("every node receives the
message by the end of round `T`") is false; the last step of the proof (the node `u` must have got
the message in `[T - 1/ρ + 1, T]`, contradicting Lemma 9) fails exactly when `u` is the source.
We count the source as a first-time receiver of round 1, i.e. `den(1, t) = #inf t / t` where
`inf t` (which contains the source) is the set of nodes holding the message after round `t`.
Then `T > 1/ρ = D` (`D_lt_T`), Lemma 9 holds (`lemma9`), Lemma 8 holds (`lemma8`; the bound
`P ≤ R` there needs the source to be counted when `T' = 1`), and Theorem 10 follows
(`informed_by_T`, `theorem10`).
-/

namespace Podc.BroadcastUnreliableRadio.StrongSelect

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {N : DualGraph V} {A : Params V}

namespace Params

/-- `D = 1 / ρ = 12 f 2 ^ smax`, the inverse of the density threshold `ρ` of the paper. -/
def D (A : Params V) : ℕ := 12 * A.f * 2 ^ A.smax

omit [Fintype V] [DecidableEq V] in
lemma two_ℓ'_one_le_D (A : Params V) : 2 * A.ℓ' 1 ≤ A.D := by
  have hL : A.L ≤ 2 ^ A.smax := Nat.sub_le _ _
  unfold ℓ' D
  calc 2 * (2 ^ (1 + 1) * A.f * A.L) = 8 * A.f * A.L := by ring
    _ ≤ 8 * A.f * 2 ^ A.smax := Nat.mul_le_mul_left _ hL
    _ ≤ 12 * A.f * 2 ^ A.smax := by gcongr; norm_num

omit [Fintype V] [DecidableEq V] in
lemma six_ℓ'_le (A : Params V) (s : ℕ) : 6 * A.ℓ' s ≤ 2 ^ s * A.D := by
  have hL : A.L ≤ 2 ^ A.smax := Nat.sub_le _ _
  unfold ℓ' D
  calc 6 * (2 ^ (s + 1) * A.f * A.L) = 2 ^ s * (12 * A.f * A.L) := by ring
    _ ≤ 2 ^ s * (12 * A.f * 2 ^ A.smax) := by gcongr

omit [Fintype V] [DecidableEq V] in
lemma D_pos (A : Params V) (hf : 1 ≤ A.f) : 0 < A.D := by unfold D; positivity

end Params

omit [Fintype V] in
lemma exists_edge_out {E : V → V → Prop} {S : Finset V} {a b : V}
    (h : Relation.ReflTransGen E a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ u v, E u v ∧ u ∈ S ∧ v ∉ S := by
  induction h with
  | refl => exact absurd ha hb
  | @tail b c _ hbc ih =>
    by_cases hb' : b ∈ S
    · exact ⟨b, c, hbc, hb', hb⟩
    · exact ih hb'

namespace Execution

variable (ex : Execution N A)

open Classical in
/-- The participants of iteration `m` of `F s`. -/
noncomputable def participants (s m : ℕ) : Finset V :=
  univ.filter fun v => A.Participates ex.inf v s m

lemma mem_participants {s m : ℕ} {v : V} :
    v ∈ ex.participants s m ↔ A.Participates ex.inf v s m := by
  classical
  simp [participants]

/-- If the participants of iteration `m` of `F s` are few enough for `F s` to be strongly
selective for them, each of them sends alone in some round of that iteration. -/
lemma isolated {s m k : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ A.smax)
    (hF : StronglySelective (A.F s) (A.ℓ s) k) (hZ : (ex.participants s m).card ≤ k) {v : V}
    (hv : A.Participates ex.inf v s m) :
    ∃ r, m * A.ℓ' s < r ∧ r ≤ (m + 1) * A.ℓ' s ∧ ∀ w, A.Sends ex.inf r w ↔ w = v := by
  obtain ⟨j, hj, hZj⟩ := hF _ hZ v ((ex.mem_participants).2 hv)
  obtain ⟨r, h1, h2, hfam, hiter, hidx⟩ := A.exists_round hs1 hs m hj
  refine ⟨r, h1, h2, fun w => ?_⟩
  have := congrArg (w ∈ ·) hZj
  simp only [mem_inter, mem_singleton, ex.mem_participants] at this
  simp only [Params.Sends, hfam, hiter, hidx]
  exact Iff.of_eq this

omit [Fintype V] in
/-- A node informed by round `t` participates in an iteration of `F s` ending by round
`t + 2 ℓ'_s`. -/
lemma exists_participates (hs : 1 ≤ A.smax) (hf : 1 ≤ A.f) (s : ℕ) {t : ℕ} {u : V}
    (hu : u ∈ ex.inf t) :
    ∃ m, A.Participates ex.inf u s m ∧ (m + 1) * A.ℓ' s ≤ t + 2 * A.ℓ' s := by
  classical
  have hP := A.ℓ'_pos hs hf s
  have hm0 : u ∈ ex.inf ((t / A.ℓ' s + 1) * A.ℓ' s) := by
    rw [add_mul, one_mul]; exact ex.mono' (Nat.lt_div_mul_add hP).le hu
  have hex : ∃ m, u ∈ ex.inf (m * A.ℓ' s) := ⟨_, hm0⟩
  refine ⟨Nat.find hex, ⟨Nat.find_spec hex, fun m' hm' => Nat.find_min hex hm'⟩, ?_⟩
  have h1 : Nat.find hex ≤ t / A.ℓ' s + 1 := Nat.find_min' hex hm0
  have h2 : t / A.ℓ' s * A.ℓ' s ≤ t := Nat.div_mul_le_self t _
  calc (Nat.find hex + 1) * A.ℓ' s ≤ (t / A.ℓ' s + 1 + 1) * A.ℓ' s :=
        Nat.mul_le_mul_right _ (by omega)
    _ = t / A.ℓ' s * A.ℓ' s + 2 * A.ℓ' s := by ring
    _ ≤ t + 2 * A.ℓ' s := by omega

/-! ## The round `T` -/

lemma exists_sparse : ∃ T, (ex.inf T).card * A.D < T :=
  ⟨Fintype.card V * A.D + 1, Nat.lt_succ_of_le (Nat.mul_le_mul_right _ (card_le_univ _))⟩

open Classical in
/-- `T`: the first round `t` with `den(1, t) < ρ`, i.e. `#inf t * D < t` (the source counts as
a first-time receiver of round 1, see the module docstring). -/
noncomputable def T : ℕ := Nat.find ex.exists_sparse

lemma T_spec : (ex.inf ex.T).card * A.D < ex.T := by
  classical exact Nat.find_spec ex.exists_sparse

/-- Minimality of `T`: `den(1, t) ≥ ρ` for `t < T`. -/
lemma le_of_lt_T {t : ℕ} (ht : t < ex.T) : t ≤ (ex.inf t).card * A.D := by
  classical
  have := Nat.find_min ex.exists_sparse ht
  omega

lemma D_lt_T : A.D < ex.T := by
  have h1 : 1 ≤ (ex.inf ex.T).card := card_pos.2 ⟨_, ex.src_mem _⟩
  have := ex.T_spec
  nlinarith

/-- **Lemma 9** (repaired). No node receives the message for the first time in
`[T - 1/ρ + 1, T]`: every node holding the message after round `T` already held it after round
`T - 1/ρ` (`T > 1/ρ` by `D_lt_T`). -/
theorem lemma9 {v : V} (hv : v ∈ ex.inf ex.T) : v ∈ ex.inf (ex.T - A.D) := by
  by_contra hv'
  rcases Nat.eq_zero_or_pos A.D with h0 | hD
  · exact hv' (by rw [h0, Nat.sub_zero]; exact hv)
  have hlt : (ex.inf (ex.T - A.D)).card < (ex.inf ex.T).card :=
    card_lt_card ⟨ex.mono' (Nat.sub_le _ _), fun h => hv' (h hv)⟩
  have hmin := ex.le_of_lt_T (t := ex.T - A.D) (by have := ex.D_lt_T; omega)
  have hT := ex.T_spec
  have hDT := ex.D_lt_T
  have : ((ex.inf (ex.T - A.D)).card + 1) * A.D ≤ (ex.inf ex.T).card * A.D :=
    Nat.mul_le_mul_right _ hlt
  rw [add_mul, one_mul] at this
  omega

/-- The density estimate of Lemma 8: the participants `P` of an iteration `m` of `F s` among the
last iterations ending by round `T` satisfy `P < ρ ⋅ 6 ℓ'_s`. -/
lemma participants_card_mul_D_lt {s m : ℕ} (hm1 : (m + 1) * A.ℓ' s ≤ ex.T)
    (hm2 : ex.T < (m + 5) * A.ℓ' s) :
    (ex.participants s m).card * A.D < 6 * A.ℓ' s := by
  have hT := ex.T_spec
  have e1 : (m + 5) * A.ℓ' s = m * A.ℓ' s + 5 * A.ℓ' s := by ring
  have e2 : (m + 1) * A.ℓ' s = m * A.ℓ' s + A.ℓ' s := by ring
  by_cases h6 : ex.T ≤ 6 * A.ℓ' s
  · -- `T' = 1`: here the source may be a participant (this needs the repaired density).
    have hsub : ex.participants s m ⊆ ex.inf ex.T := fun w hw =>
      ex.mono' (by omega) ((ex.mem_participants).1 hw).1
    have := Nat.mul_le_mul_right A.D (card_le_card hsub)
    omega
  · push Not at h6
    have hm : m ≠ 0 := by rintro rfl; rw [zero_mul] at e1; omega
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
    have e3 : (m' + 1) * A.ℓ' s = m' * A.ℓ' s + A.ℓ' s := by ring
    have hma : ex.T - 6 * A.ℓ' s ≤ m' * A.ℓ' s := by omega
    have hsub : ex.participants s (m' + 1) ⊆ ex.inf ex.T \ ex.inf (ex.T - 6 * A.ℓ' s) := by
      intro w hw
      have hw := (ex.mem_participants).1 hw
      refine mem_sdiff.2 ⟨ex.mono' (by omega) hw.1, fun hwa => ?_⟩
      exact hw.2 m' (by omega) (ex.mono' hma hwa)
    have hc := card_le_card hsub
    rw [card_sdiff_of_subset (ex.mono' (Nat.sub_le _ _))] at hc
    have hmin := ex.le_of_lt_T (t := ex.T - 6 * A.ℓ' s) (by omega)
    have hca : (ex.inf (ex.T - 6 * A.ℓ' s)).card ≤ (ex.inf ex.T).card :=
      card_le_card (ex.mono' (Nat.sub_le _ _))
    have : (ex.participants s (m' + 1)).card * A.D + (ex.inf (ex.T - 6 * A.ℓ' s)).card * A.D
        ≤ (ex.inf ex.T).card * A.D := by
      rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- **Lemma 8.** Let `m` be one of the last (at most) four iterations of `F s` that end by
round `T` (i.e. `(m + 1) ℓ'_s ≤ T < (m + 5) ℓ'_s`). Every node participating in iteration `m`
sends alone in some round of that iteration. -/
theorem lemma8
    (hssf : ∀ s, 1 ≤ s → s < A.smax → StronglySelective (A.F s) (A.ℓ s) (2 ^ s))
    (hrr : StronglySelective (A.F A.smax) (A.ℓ A.smax) (Fintype.card V))
    {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ A.smax) {m : ℕ} (hm1 : (m + 1) * A.ℓ' s ≤ ex.T)
    (hm2 : ex.T < (m + 5) * A.ℓ' s) {v : V} (hv : A.Participates ex.inf v s m) :
    ∃ r, m * A.ℓ' s < r ∧ r ≤ (m + 1) * A.ℓ' s ∧ ∀ w, A.Sends ex.inf r w ↔ w = v := by
  rcases hs.lt_or_eq with hs' | rfl
  · refine ex.isolated hs1 hs (hssf s hs1 hs') ?_ hv
    have h1 := ex.participants_card_mul_D_lt hm1 hm2
    have h2 := A.six_ℓ'_le s
    exact (Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le h1 h2)).le
  · exact ex.isolated hs1 le_rfl hrr (card_le_univ _) hv

/-- **Theorem 10, first part.** Every node holds the message at the end of round `T`. -/
theorem informed_by_T (hs : 1 ≤ A.smax) (hf : 1 ≤ A.f)
    (hssf : ∀ s, 1 ≤ s → s < A.smax → StronglySelective (A.F s) (A.ℓ s) (2 ^ s))
    (hrr : StronglySelective (A.F A.smax) (A.ℓ A.smax) (Fintype.card V)) (v : V) :
    v ∈ ex.inf ex.T := by
  by_contra hw
  obtain ⟨u, v, huv, hu, hv⟩ := exists_edge_out (N.reachable v) (ex.src_mem ex.T) hw
  -- `u` never sends alone in rounds `1, …, T`.
  have never : ∀ r, 1 ≤ r → r ≤ ex.T → ¬ ∀ w, A.Sends ex.inf r w ↔ w = u :=
    fun r h1 h2 hiso => hv (ex.mono' h2 (ex.progress r h1 u hiso v huv))
  -- Backwards induction on `s`: `u` did not have the message by round `T - 2 ℓ'_s`.
  have claim : ∀ k s, s + k = A.smax → 1 ≤ s →
      ∀ t, t + 2 * A.ℓ' s ≤ ex.T → u ∉ ex.inf t := by
    intro k
    induction k with
    | zero =>
      intro s hsk hs1 t ht hut
      obtain ⟨m, hp, hb⟩ := ex.exists_participates hs hf s hut
      obtain ⟨r, h1, h2, hiso⟩ :=
        ex.isolated hs1 (by omega) (by rw [show s = A.smax by omega] at *; exact hrr)
          (card_le_univ _) hp
      exact never r (by omega) (by omega) hiso
    | succ k ih =>
      intro s hsk hs1 t ht hut
      have ih' := ih (s + 1) (by omega) (by omega)
      rw [A.ℓ'_succ] at ih'
      obtain ⟨m, hp, hb⟩ := ex.exists_participates hs hf s hut
      have hm2 : ex.T < (m + 5) * A.ℓ' s := by
        by_contra h
        exact ih' (m * A.ℓ' s) (by nlinarith) hp.1
      obtain ⟨r, h1, h2, hiso⟩ :=
        ex.lemma8 hssf hrr hs1 (by omega) (by omega) hm2 hp
      exact never r (by omega) (by omega) hiso
  have := ex.D_lt_T
  exact claim (A.smax - 1) 1 (by omega) le_rfl (ex.T - A.D)
    (by have := A.two_ℓ'_one_le_D; omega) (ex.lemma9 hu)

/-- **Theorem 10.** In any directed dual graph network, under collision rule CR4 with
asynchronous start, every execution of strong select informs all `n` nodes by round
`X = n / ρ = 12 n f 2 ^ smax`. Here the families `F s` (`1 ≤ s < smax`) are
`(n, 2 ^ s)`-strongly selective of size `4 ^ s f`, and `F smax` is `(n, n)`-strongly selective
(e.g. round robin, padded to size `4 ^ smax f ≥ n`). With `4 ^ smax ≈ n / log n` and
`f = O(log n)` (Theorem 7) this is `O(n ^ {3/2} √(log n))`, see `theorem10_asymptotic`. -/
theorem theorem10 (hs : 1 ≤ A.smax) (hf : 1 ≤ A.f)
    (hssf : ∀ s, 1 ≤ s → s < A.smax → StronglySelective (A.F s) (A.ℓ s) (2 ^ s))
    (hrr : StronglySelective (A.F A.smax) (A.ℓ A.smax) (Fintype.card V)) (v : V) :
    v ∈ ex.inf (Fintype.card V * A.D) := by
  by_cases hT : ex.T ≤ Fintype.card V * A.D
  · exact ex.mono' hT (ex.informed_by_T hs hf hssf hrr v)
  · push Not at hT
    have h1 := ex.le_of_lt_T hT
    have h2 : Fintype.card V ≤ (ex.inf (Fintype.card V * A.D)).card :=
      Nat.le_of_mul_le_mul_right h1 (A.D_pos hf)
    have : ex.inf (Fintype.card V * A.D) = univ :=
      eq_univ_of_card _ (le_antisymm (card_le_univ _) h2)
    rw [this]; exact mem_univ v

end Execution

omit [DecidableEq V] in
/-- The round bound of Theorem 10 is `O(n ^ {3/2} √(log n))`: if `4 ^ smax f ≤ c₁ n` and
`f ≤ c₂ log₂ n`, then `X ^ 2 ≤ 144 c₁ c₂ n ^ 3 log₂ n` for `X = 12 n f 2 ^ smax`. -/
theorem theorem10_asymptotic (A : Params V) {c₁ c₂ : ℕ}
    (h₁ : 4 ^ A.smax * A.f ≤ c₁ * Fintype.card V) (h₂ : A.f ≤ c₂ * Nat.log 2 (Fintype.card V)) :
    (Fintype.card V * A.D) ^ 2 ≤ 144 * c₁ * c₂ * Fintype.card V ^ 3 * Nat.log 2 (Fintype.card V) := by
  set n := Fintype.card V
  have e : (n * A.D) ^ 2 = 144 * n ^ 2 * (4 ^ A.smax * A.f) * A.f := by
    unfold Params.D
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
  rw [e]
  calc 144 * n ^ 2 * (4 ^ A.smax * A.f) * A.f
      ≤ 144 * n ^ 2 * (c₁ * n) * (c₂ * Nat.log 2 n) := by gcongr
    _ = 144 * c₁ * c₂ * n ^ 3 * Nat.log 2 n := by ring

end Podc.BroadcastUnreliableRadio.StrongSelect
