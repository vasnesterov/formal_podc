import Papers.PODC2021.StabilizingLEDynamic.LE.Propagation

/-!
# Algorithm `LE`: fake identifiers, timely sources, suspicion values (Lemmas 8–16)

Times are 0-indexed (`X G γ t` is the paper's `γ_{t+1}`); bounds are translated accordingly and
are sometimes slightly sharper than the paper's.
-/

namespace StabilizingLEDynamic.LE

open Classical Cslib.HeardOf

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ} {G : DG ι} {γ : ι → St ι Δ} {V : Finset ι}

variable (G V) in
/-- `r` is a timely source of `G` (Definition 6). -/
def TSource (r : ι) : Prop := r ∈ V ∧ ∀ q ∈ V, ∀ t, tdist G t r q ≤ Δ

section
variable (hΔ : 1 ≤ Δ) (hG : IsDG V G)
include hΔ hG

/-! ### Lemma 8: fake identifiers -/

omit hΔ in
/-- Records received in rounds `j ≥ Δ` are genuine (Lemma 2 / Corollary 4). -/
theorem recv_prov {j : ℕ} (hj : Δ ≤ j) {q : ι} {r : Rcd ι Δ} (hr : Recv G γ j q r) :
    r.id ∈ V ∧ r.lsps = (X G γ (j - (Δ - r.ttl.val)) r.id).L ∧
      j + 1 ≤ j - (Δ - r.ttl.val) + Δ := by
  obtain ⟨k, hk, -, hmem, hpos, -⟩ := hr.mem hG
  obtain ⟨h1, h2⟩ := provenance hG j k hk r hmem (by omega) (by omega)
  exact ⟨h1, h2, by have := r.ttl.isLt; omega⟩

/-- **Lemma 8(b)**: a fake identifier is not in any `Lstable` from time `2Δ` on. -/
theorem fake_L {f : ι} (hf : f ∉ V) {q : ι} (hq : q ∈ V) {t : ℕ} (ht : 2 * Δ ≤ t) :
    (X G γ t q).L.f f = none := by
  by_contra h
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp h
  obtain ⟨j, hj1, hj2, r, hr, hid, -⟩ :=
    lemma_4 hΔ hG (fun h => hf (by rw [h]; exact hq)) (by omega) he
  exact hf (hid ▸ (recv_prov hG (by omega) hr).1)

/-- **Lemma 8(c)**: records received in rounds `j ≥ 3Δ - 1` do not mention fake identifiers. -/
theorem fake_lsps {f : ι} (hf : f ∉ V) {j : ℕ} (hj : 3 * Δ ≤ j + 1) {q : ι} {r : Rcd ι Δ}
    (hr : Recv G γ j q r) : r.lsps.f f = none := by
  obtain ⟨h1, h2, h3⟩ := recv_prov hG (by omega) hr
  rw [h2]
  exact fake_L hΔ hG hf h1 (by omega)

/-- **Lemma 8(d)**: a fake identifier is not in any `Gstable` from time `4Δ - 1` on. -/
theorem fake_G {f : ι} (hf : f ∉ V) {q : ι} (hq : q ∈ V) {t : ℕ} (ht : 4 * Δ ≤ t + 1) :
    (X G γ t q).G.f f = none := by
  by_contra h
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp h
  obtain ⟨j, hj1, hj2, r, hr, -, hfr, -⟩ :=
    lemma_5 hΔ hG (fun h => hf (by rw [h]; exact hq)) (by omega) he
  exact hfr (fake_lsps hΔ hG hf (by omega) hr)

omit hG in
/-- **Lemma 8(a) is slightly misstated.** The paper claims that from configuration `γ_{Δ+1}` on
(0-indexed time `Δ`), no `msgs` set contains a record tagged with a fake identifier. But a
well-formed record `⟨f, L, Δ⟩` in an initial `msgs(p)` is only decremented once per round and is
still in `msgs(p)` at time `Δ` (with timer `0`; it is removed during the next round). Such records
are never sent, so the rest of the proof is unaffected (`fake_L`, `fake_G` give the paper's
conclusions (b)–(d)). -/
theorem lemma_8a_imprecise {p f : ι} {L : MapT ι Δ} (hL : L.f f ≠ none)
    (h : (⟨f, L, Fin.last Δ⟩ : Rcd ι Δ) ∈ (γ p).msgs) :
    (⟨f, L, 0⟩ : Rcd ι Δ) ∈ (X G γ Δ p).msgs := by
  have key : ∀ c ≤ Δ, (⟨f, L, ⟨Δ - c, by omega⟩⟩ : Rcd ι Δ) ∈ (X G γ c p).msgs := by
    intro c hc
    induction c with
    | zero => exact h
    | succ c ih =>
      rw [X_succ, roundLE_msgs]
      right
      refine ⟨_, subset_foldl_bodyM _ _ _ (ih (by omega)), by simp only; omega, hL, ?_⟩
      simp only [dec]; congr 2
  have := key Δ le_rfl
  simpa using this

/-! ### Timely sources (Lemmas 9–12) -/

/-- **Lemma 9**: a timely source is in every `Lstable` from time `Δ + 1` on. -/
theorem lemma_9 {r : ι} (hr : TSource G V (Δ := Δ) r) {q : ι} (hq : q ∈ V) {t : ℕ}
    (ht : Δ + 1 ≤ t) : (X G γ t q).L.f r ≠ none := by
  by_cases hqr : q = r
  · subst hqr; rw [L_self hΔ (by omega)]; simp
  have hreach : Reach G r (t - Δ) (t - Δ + Δ) q := tdist_le_iff.mp (hr.2 q hq (t - Δ))
  obtain ⟨-, -, -, h4⟩ := lemma_3 hΔ hG (γ := γ) hr.1 (by omega) le_rfl hreach
  obtain ⟨j, hj1, hj2, hj3⟩ := h4 hqr
  have := lemma_6 hΔ hG hj3 (Ne.symm hqr) (u := t) (by omega) (by simp only [rcd]; omega)
  simpa [rcd] using this

/-- **Lemma 10**: the suspicion value of a timely source is constant from time `2Δ` on. -/
theorem lemma_10 {r : ι} (hr : TSource G V (Δ := Δ) r) {t : ℕ} (ht : 2 * Δ ≤ t) :
    susp G γ t r = susp G γ (2 * Δ) r := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [susp_succ hΔ (by omega), ih, nIncr, List.countP_eq_zero.mpr, Nat.add_zero]
    intro r' hr' hc
    simp only [decide_eq_true_eq] at hc
    obtain ⟨h1, h2, h3⟩ := recv_prov hG (by omega) ((mem_mbx hG).mp hr')
    rw [h2] at hc
    exact lemma_9 hΔ hG hr h1 (by omega) hc.2

/-- `p`'s suspicion value is constant from time `T ≥ 1` on (membership in `♢Const`). -/
def ConstFrom (G : DG ι) (γ : ι → St ι Δ) (p : ι) (T : ℕ) : Prop :=
  1 ≤ T ∧ ∀ t ≥ T, susp G γ t p = susp G γ T p

/-- **Lemma 11**: a process whose suspicion value is constant from time `T` on is in the
`Lstable` map of every timely source from time `T` on. -/
theorem lemma_11 {p : ι} (hp : p ∈ V) {T : ℕ} (hT : ConstFrom G γ p T) {r : ι}
    (hr : TSource G V (Δ := Δ) r) {t : ℕ} (ht : T ≤ t) : (X G γ t r).L.f p ≠ none := by
  by_cases hpr : p = r
  · subst hpr; rw [L_self hΔ (by have := hT.1; omega)]; simp
  intro hnone
  have hreach : Reach G r t (t + Δ) p := tdist_le_iff.mp (hr.2 p hp t)
  obtain ⟨-, -, -, h4⟩ := lemma_3 hΔ hG (γ := γ) hr.1 (by have := hT.1; omega) le_rfl hreach
  obtain ⟨j, hj1, hj2, hj3⟩ := h4 hpr
  have hinc : 0 < nIncr p (mbx G γ j p) := by
    rw [nIncr, List.countP_pos_iff]
    exact ⟨_, (mem_mbx hG).mpr hj3, by simp [rcd, Ne.symm hpr, hnone]⟩
  have h1 := susp_succ hΔ (G := G) (γ := γ) (t := j) (by have := hT.1; omega) p
  have h2 := hT.2 j (by omega)
  have h3 := hT.2 (j + 1) (by omega)
  omega

/-- **Lemma 12**: a process whose suspicion value is constant from time `T` on is in every
`Gstable` map from time `T + Δ` on. -/
theorem lemma_12 {p : ι} (hp : p ∈ V) {T : ℕ} (hT : ConstFrom G γ p T) {r : ι}
    (hr : TSource G V (Δ := Δ) r) {q : ι} (hq : q ∈ V) {t : ℕ} (ht : T + Δ ≤ t) :
    (X G γ t q).G.f p ≠ none := by
  have hT1 := hT.1
  by_cases hqp : q = p
  · subst hqp; rw [G_self hΔ (by omega)]; simp
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (lemma_11 hΔ hG hp hT hr (t := t) (by omega))
    obtain ⟨j, hj1, hj2, r', hr', hid, -⟩ := lemma_4 hΔ hG (Ne.symm hqp) (by omega) he
    obtain ⟨-, -, -, -, -, hlsps⟩ := hr'.mem hG
    rw [hid] at hlsps
    exact lemma_7 hΔ hG (Ne.symm hqp) hr' (by rw [hid]; exact Ne.symm hqp) hlsps
      (by omega) (by omega)
  · have hreach : Reach G r (t - Δ) (t - Δ + Δ) q := tdist_le_iff.mp (hr.2 q hq (t - Δ))
    obtain ⟨-, -, -, h4⟩ := lemma_3 hΔ hG (γ := γ) hr.1 (by omega) le_rfl hreach
    obtain ⟨j, hj1, hj2, hj3⟩ := h4 hqr
    have hpL := lemma_11 hΔ hG hp hT hr (t := t - Δ) (by omega)
    exact lemma_7 hΔ hG (Ne.symm hqp) hj3 (by simp [rcd, Ne.symm hqr]) (by simpa [rcd] using hpL)
      (by omega) (by omega)

/-! ### Accuracy of the memorized suspicion values (Lemmas 13–16) -/

omit hΔ in
/-- **Lemma 13.** -/
theorem lemma_13 {j : ℕ} (hj : Δ ≤ j) {q : ι} {r : Rcd ι Δ} (hr : Recv G γ j q r) :
    ∃ u, j + 1 ≤ u + Δ ∧ u ≤ j ∧ suspOf r.lsps r.id = susp G γ u r.id := by
  obtain ⟨-, h2, h3⟩ := recv_prov hG hj hr
  exact ⟨_, h3, by omega, by rw [h2]; rfl⟩

/-- **Lemma 14.** -/
theorem lemma_14 {p q : ι} (hpq : p ≠ q) {t : ℕ} (ht : 2 * Δ ≤ t) {e : Entry Δ}
    (h : (X G γ t q).L.f p = some e) :
    ∃ u, t + 1 ≤ u + 2 * Δ ∧ u + 1 ≤ t ∧ e.1 = susp G γ u p := by
  obtain ⟨j, hj1, hj2, r, hr, hid, hval⟩ := lemma_4 hΔ hG hpq (by omega) h
  obtain ⟨u, hu1, hu2, hu3⟩ := lemma_13 hG (by omega) hr
  rw [hid] at hu3
  exact ⟨u, by omega, by omega, hval.trans hu3⟩

/-- **Lemma 15.** -/
theorem lemma_15 {j : ℕ} (hj : 3 * Δ ≤ j + 1) {q : ι} {r : Rcd ι Δ} (hr : Recv G γ j q r)
    {p : ι} (hp : r.lsps.f p ≠ none) :
    ∃ u, j + 2 ≤ u + 3 * Δ ∧ u ≤ j ∧ suspOf r.lsps p = susp G γ u p := by
  obtain ⟨h1, h2, h3⟩ := recv_prov hG (by omega) hr
  by_cases hpx : p = r.id
  · subst hpx
    exact ⟨j - (Δ - r.ttl.val), by omega, by omega, by rw [h2]; rfl⟩
  · rw [h2] at hp ⊢
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hp
    obtain ⟨u, hu1, hu2, hu3⟩ := lemma_14 hΔ hG hpx (by omega) he
    exact ⟨u, by omega, by omega, by rw [suspOf, he]; exact hu3⟩

/-- **Lemma 16** (for `t ≥ 4Δ - 1`, i.e. the paper's `i ≥ 4Δ`). -/
theorem lemma_16 {p q : ι} (hpq : p ≠ q) {t : ℕ} (ht : 4 * Δ ≤ t + 1) {e : Entry Δ}
    (h : (X G γ t q).G.f p = some e) :
    ∃ u, t + 2 ≤ u + 4 * Δ ∧ u ≤ t ∧ e.1 = susp G γ u p := by
  obtain ⟨j, hj1, hj2, r, hr, -, hp, hval⟩ := lemma_5 hΔ hG hpq (by omega) h
  obtain ⟨u, hu1, hu2, hu3⟩ := lemma_15 hΔ hG (by omega) hr hp
  exact ⟨u, by omega, by omega, hval.trans hu3⟩

/-! ### Theorem 6 -/

/-- The core of **Theorem 6**: if from time `T ≥ 1` on, the processes of `C ⊆ V` have constant
suspicion values `fin`, with minimum `m`, and all other processes have suspicion values `> m`,
then from time `T + 4Δ` on every process elects
`ℓ = min {p ∈ C | fin p = m}`. -/
theorem theorem_6_core {r : ι} (hr : TSource G V (Δ := Δ) r) {T : ℕ} (hT : 1 ≤ T)
    {C : Finset ι} (hCV : C ⊆ V) (fin : ι → ℕ) (hC : ∀ p ∈ C, ∀ t ≥ T, susp G γ t p = fin p)
    {m : ℕ} (hm : ∀ p ∈ C, m ≤ fin p) (hnC : ∀ p ∈ V, p ∉ C → m < susp G γ T p)
    {ℓ : ι} (hℓC : ℓ ∈ C) (hℓm : fin ℓ = m) (hℓmin : ∀ p ∈ C, fin p = m → ℓ ≤ p)
    {t : ℕ} (ht : T + 4 * Δ ≤ t) {q : ι} (hq : q ∈ V) :
    (algLE Δ).lid q (X G γ t q) = ℓ := by
  rw [lid_eq hΔ (by omega)]
  -- the value attached to `k ∈ Gstable(q)_t` is a suspicion value of `k` at a time `≥ T`
  have hval : ∀ k e, (X G γ t q).G.f k = some e → ∃ u, T ≤ u ∧ e.1 = susp G γ u k := by
    intro k e he
    by_cases hkq : k = q
    · subst hkq; rw [G_self hΔ (by omega)] at he; cases he; exact ⟨t, by omega, rfl⟩
    · obtain ⟨u, hu1, -, hu3⟩ := lemma_16 hΔ hG hkq (by omega) he
      exact ⟨u, by omega, hu3⟩
  have hconst : ConstFrom G γ ℓ T :=
    ⟨hT, fun t ht => (hC ℓ hℓC t ht).trans (hC ℓ hℓC T le_rfl).symm⟩
  apply leaderOf_eq (m := m)
  · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp
      (lemma_12 hΔ hG (hCV hℓC) hconst hr hq (t := t) (by omega))
    obtain ⟨u, hu, hu'⟩ := hval ℓ e he
    refine ⟨e.2, ?_⟩
    rw [he]
    exact congrArg some (Prod.ext (by rw [hu', hC ℓ hℓC u hu, hℓm]) rfl)
  · intro k e he
    have hkV : k ∈ V := by
      by_contra hkV
      rw [fake_G hΔ hG hkV hq (by omega)] at he; cases he
    obtain ⟨u, hu, hu'⟩ := hval k e he
    by_cases hkC : k ∈ C
    · rw [hu', hC k hkC u hu]
      exact ⟨hm k hkC, hℓmin k hkC⟩
    · have := hnC k hkV hkC
      have := susp_mono hΔ (G := G) (γ := γ) hT hu k
      rw [hu']
      exact ⟨by omega, fun h => by omega⟩

end

end StabilizingLEDynamic.LE
