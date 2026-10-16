import Papers.PODC2021.StabilizingLEDynamic.LE.Exec

/-!
# Algorithm `LE`: communication (Lemma 3) and timers (Lemmas 4–7)
-/

namespace StabilizingLEDynamic.LE

open Classical Cslib.HeardOf

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ} {G : DG ι} {γ : ι → St ι Δ} {V : Finset ι}

/-- The record initiated by `p` with map `M`, of age `c` (timer `Δ - c`). -/
def rcd (p : ι) (M : MapT ι Δ) (c : ℕ) : Rcd ι Δ := ⟨p, M, ⟨Δ - c, by omega⟩⟩

variable (G γ) in
/-- The record initiated by `p` at the end of round `t₀ - 1` is held by `q` at time `s` (with the
right age), and if `q ≠ p`, `q` received it in some round of `[t₀, s)`. -/
def Good (p : ι) (t₀ : ℕ) (q : ι) (s : ℕ) : Prop :=
  t₀ ≤ s ∧ s ≤ t₀ + Δ ∧ rcd p (X G γ t₀ p).L (s - t₀) ∈ (X G γ s q).msgs ∧
    (q ≠ p → ∃ j, t₀ ≤ j ∧ j < s ∧ Recv G γ j q (rcd p (X G γ t₀ p).L (j - t₀)))

section
variable (hΔ : 1 ≤ Δ) (hG : IsDG V G)
include hΔ hG

theorem good_stay {p q : ι} {t₀ s : ℕ} (ht₀ : 1 ≤ t₀) (h : Good G γ p t₀ q s)
    (hs : s < t₀ + Δ) : Good G γ p t₀ q (s + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, ?_, fun hq => ?_⟩
  · rw [X_succ, roundLE_msgs]
    right
    refine ⟨_, subset_foldl_bodyM _ _ _ h3, ?_, ?_, ?_⟩
    · simp only [rcd]; omega
    · simp [rcd, L_self hΔ ht₀ p]
    · simp only [rcd, dec]; congr 2; omega
  · obtain ⟨j, hj1, hj2, hj3⟩ := h4 hq
    exact ⟨j, hj1, by omega, hj3⟩

theorem good_self {p : ι} {t₀ : ℕ} (ht₀ : 1 ≤ t₀) :
    ∀ c ≤ Δ, Good G γ p t₀ p (t₀ + c) := by
  intro c hc
  induction c with
  | zero =>
    refine ⟨le_rfl, by omega, ?_, fun h => absurd rfl h⟩
    obtain ⟨t, rfl⟩ : ∃ t', t₀ = t' + 1 := ⟨t₀ - 1, by omega⟩
    rw [Nat.add_zero, X_succ, roundLE_msgs]
    left
    simp only [rcd, Nat.sub_self, Nat.sub_zero]
    rfl
  | succ c ih => exact good_stay hΔ hG ht₀ (ih (by omega)) (by show t₀ + c < t₀ + Δ; omega)

theorem good_forward {p q q' : ι} {t₀ s : ℕ} (ht₀ : 1 ≤ t₀) (hq : q ∈ V)
    (h : Good G γ p t₀ q s) (hs : s < t₀ + Δ) (hedge : G s q q') :
    Good G γ p t₀ q' (s + 1) := by
  by_cases hq'p : q' = p
  · subst hq'p
    have := good_self hΔ hG (γ := γ) (p := q') ht₀ (s + 1 - t₀) (by have := h.1; omega)
    rwa [show t₀ + (s + 1 - t₀) = s + 1 by have := h.1; omega] at this
  obtain ⟨h1, h2, h3, -⟩ := h
  set r0 := rcd p (X G γ t₀ p).L (s - t₀)
  have hsent : r0 ∈ sent (X G γ s q) := by
    rw [mem_sent]
    refine ⟨h3, ?_, ?_⟩
    · simp only [r0, rcd]; omega
    · simp [r0, rcd, L_self hΔ ht₀ p]
  have hrecv : Recv G γ s q' r0 := ⟨q, hedge, hsent⟩
  refine ⟨by omega, by omega, ?_, fun _ => ⟨s, h1, by omega, hrecv⟩⟩
  obtain ⟨r', hr', hid, httl⟩ :=
    exists_foldl_bodyM (M := (X G γ s q').msgs) ((mem_mbx hG).mpr hrecv) (Ne.symm hq'p)
  -- `r'` has the same initiator and age, hence is `r0` (Lemma 2)
  have hq'V : q' ∈ V := (hG s q q' hedge).2.1
  have hr'eq : r' = r0 := by
    have hk : ∃ k ∈ V, r' ∈ (X G γ s k).msgs := by
      rcases mem_foldl_bodyM hr' with h | ⟨h, -⟩
      · exact ⟨q', hq'V, h⟩
      · obtain ⟨k, hk, -, h, -⟩ := ((mem_mbx hG).mp h).mem hG
        exact ⟨k, hk, h⟩
    obtain ⟨k, hk, hr'k⟩ := hk
    have hval : r'.ttl.val = Δ - (s - t₀) := by rw [httl]; rfl
    obtain ⟨-, h6⟩ := provenance hG s k hk r' hr'k (by omega) (by omega)
    rw [hval, hid, show s - (Δ - (Δ - (s - t₀))) = t₀ by omega] at h6
    exact Rcd.ext hid h6 httl
  subst hr'eq
  rw [X_succ, roundLE_msgs]
  right
  refine ⟨_, hr', ?_, ?_, ?_⟩
  · simp only [r0, rcd]; omega
  · simp [r0, rcd, L_self hΔ ht₀ p]
  · simp only [r0, rcd, dec]; congr 2; omega

theorem good_stay_iter {p q : ι} {t₀ s s' : ℕ} (ht₀ : 1 ≤ t₀) (h : Good G γ p t₀ q s)
    (hss' : s ≤ s') (hs' : s' ≤ t₀ + Δ) : Good G γ p t₀ q s' := by
  induction s', hss' using Nat.le_induction with
  | base => exact h
  | succ b hb' ih => exact good_stay hΔ hG ht₀ (ih (by omega)) (by omega)

theorem good_reach {p : ι} {t₀ : ℕ} (ht₀ : 1 ≤ t₀) {r q : ι} {s b : ℕ}
    (h : Reach G r s b q) (hr : r ∈ V) (hgood : Good G γ p t₀ r s) (hsb : s ≤ b)
    (hb : b ≤ t₀ + Δ) : Good G γ p t₀ q b := by
  induction h with
  | refl r s b => exact good_stay_iter hΔ hG ht₀ hgood hsb hb
  | @step r r' q s b t hst htb hedge _ ih =>
    have hgt : Good G γ p t₀ r t := good_stay_iter hΔ hG ht₀ hgood hst (by omega)
    exact ih (hG t r r' hedge).2.1 (good_forward hΔ hG ht₀ hr hgt (by omega) hedge)
      (by omega) hb

/-- **Lemma 3.** If `d̂_{t₀}(p, q) ≤ d ≤ Δ` (`t₀ ≥ 1`), then `q` holds the record initiated by
`p` at the end of round `t₀ - 1` at time `t₀ + d`, and if `q ≠ p` it received it in some round
`j ∈ [t₀, t₀ + d)` with timer `Δ - (j - t₀)`. -/
theorem lemma_3 {p q : ι} (hp : p ∈ V) {t₀ d : ℕ} (ht₀ : 1 ≤ t₀) (hd : d ≤ Δ)
    (h : Reach G p t₀ (t₀ + d) q) : Good G γ p t₀ q (t₀ + d) :=
  good_reach hΔ hG ht₀ h hp (good_self hΔ hG ht₀ 0 (by omega)) (by omega) (by omega)

/-! ### Timers -/

theorem L_persist {q k : ι} (hk : k ≠ q) {u : ℕ} {e : Entry Δ}
    (h : (X G γ u q).L.f k = some e) :
    ∀ i, i + 1 ≤ e.2.val → ∃ e', (X G γ (u + i) q).L.f k = some e' ∧ e.2.val ≤ e'.2.val + i := by
  intro i
  induction i with
  | zero => intro _; exact ⟨e, h, by omega⟩
  | succ i ih =>
    intro hi
    obtain ⟨e', h1, h2⟩ := ih (by omega)
    obtain ⟨e'', h3, h4⟩ := roundLE_L_keep q (X G γ (u + i) q) (mbx G γ (u + i) q) hk h1
      (by omega)
    exact ⟨e'', by rw [← Nat.add_assoc, X_succ]; exact h3, by omega⟩

theorem G_persist {q k : ι} (hk : k ≠ q) {u : ℕ} {e : Entry Δ}
    (h : (X G γ u q).G.f k = some e) :
    ∀ i, i + 1 ≤ e.2.val → ∃ e', (X G γ (u + i) q).G.f k = some e' ∧ e.2.val ≤ e'.2.val + i := by
  intro i
  induction i with
  | zero => intro _; exact ⟨e, h, by omega⟩
  | succ i ih =>
    intro hi
    obtain ⟨e', h1, h2⟩ := ih (by omega)
    obtain ⟨e'', h3, h4⟩ := roundLE_G_keep q (X G γ (u + i) q) (mbx G γ (u + i) q) hk h1
      (by omega)
    exact ⟨e'', by rw [← Nat.add_assoc, X_succ]; exact h3, by omega⟩

/-- **Lemma 6.** If `q` receives a record `⟨id, −, τ⟩` (`id ≠ q`) in round `j`, then
`id ∈ Lstable(q)` at times `j + 1, …, j + τ`. -/
theorem lemma_6 {q : ι} {j : ℕ} {r : Rcd ι Δ} (hr : Recv G γ j q r) (hid : r.id ≠ q) {u : ℕ}
    (hu1 : j + 1 ≤ u) (hu2 : u ≤ j + r.ttl.val) : (X G γ u q).L.f r.id ≠ none := by
  obtain ⟨e, h1, h2⟩ := roundLE_L_recv q (X G γ j q) (mbx G γ j q) ((mem_mbx hG).mpr hr) hid
    (by obtain ⟨_, _, _, _, h, _⟩ := hr.mem hG; omega)
  rw [← X_succ] at h1
  rw [Fin.le_def] at h2
  obtain ⟨e', h3, -⟩ := L_persist hΔ hG hid h1 (u - (j + 1)) (by omega)
  rw [show j + 1 + (u - (j + 1)) = u by omega] at h3
  simp [h3]

/-- **Lemma 7** (corrected). If `q` receives a record `⟨id, LSPs, −⟩` with `id ≠ q` and
`k ∈ LSPs`, `k ≠ q`, in round `j`, then `k ∈ Gstable(q)` at times `j + 1, …, j + Δ`. The paper
omits `id ≠ q`; without it the lemma is false, since line 12 skips `q`'s own relayed records (see
differencies.md). All uses satisfy `id ≠ q`. -/
theorem lemma_7 {q k : ι} (hk : k ≠ q) {j : ℕ} {r : Rcd ι Δ} (hr : Recv G γ j q r)
    (hid : r.id ≠ q) (hkr : r.lsps.f k ≠ none) {u : ℕ} (hu1 : j + 1 ≤ u) (hu2 : u ≤ j + Δ) :
    (X G γ u q).G.f k ≠ none := by
  obtain ⟨σ, h1⟩ := roundLE_G_recv q (X G γ j q) (mbx G γ j q) hΔ hk ((mem_mbx hG).mpr hr) hid hkr
  rw [← X_succ] at h1
  obtain ⟨e', h3, -⟩ := G_persist hΔ hG hk h1 (u - (j + 1)) (by simp; omega)
  rw [show j + 1 + (u - (j + 1)) = u by omega] at h3
  simp [h3]

/-! ### History of the entries (Lemmas 4 and 5) -/

theorem L_pos {q k : ι} (hk : k ≠ q) {t : ℕ} (ht : 1 ≤ t) {e : Entry Δ}
    (h : (X G γ t q).L.f k = some e) : 1 ≤ e.2.val := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [X_succ] at h
  exact (roundLE_L_ne q _ _ hk h).1

theorem G_pos {q k : ι} (hk : k ≠ q) {t : ℕ} (ht : 1 ≤ t) {e : Entry Δ}
    (h : (X G γ t q).G.f k = some e) : 1 ≤ e.2.val := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [X_succ] at h
  exact (roundLE_G_ne q _ _ hk h).1

omit hΔ in
/-- Every entry `k ≠ q` of `Lstable(q)` either comes from the initial configuration (and then
its timer is small), or was set by a record `⟨k, LSPs, −⟩` received recently. -/
theorem L_hist (t : ℕ) : ∀ q k, k ≠ q → ∀ e : Entry Δ, (X G γ t q).L.f k = some e →
    e.2.val + t ≤ Δ ∨ ∃ j < t, t + e.2.val ≤ j + 1 + Δ ∧
      ∃ r, Recv G γ j q r ∧ r.id = k ∧ e.1 = suspOf r.lsps k := by
  induction t with
  | zero => intro q k _ e _; left; have := e.2.isLt; omega
  | succ t ih =>
    intro q k hk e h
    rw [X_succ] at h
    obtain ⟨-, h1 | ⟨e0, he0, h2, h3⟩⟩ := roundLE_L_ne q _ _ hk h
    · obtain ⟨r, hr, hid, rfl⟩ := h1
      right
      exact ⟨t, by omega, by have := r.ttl.isLt; simp; omega, r, (mem_mbx hG).mp hr, hid, rfl⟩
    · rcases ih q k hk e0 he0 with h4 | ⟨j, hj, h5, r, hr, hid, h6⟩
      · left; omega
      · right; exact ⟨j, by omega, by omega, r, hr, hid, by rw [← h2]; exact h6⟩

omit hΔ in
theorem G_hist (t : ℕ) : ∀ q k, k ≠ q → ∀ e : Entry Δ, (X G γ t q).G.f k = some e →
    e.2.val + t ≤ Δ ∨ ∃ j < t, t + e.2.val ≤ j + 1 + Δ ∧
      ∃ r, Recv G γ j q r ∧ r.id ≠ q ∧ r.lsps.f k ≠ none ∧ e.1 = suspOf r.lsps k := by
  induction t with
  | zero => intro q k _ e _; left; have := e.2.isLt; omega
  | succ t ih =>
    intro q k hk e h
    rw [X_succ] at h
    obtain ⟨-, h1 | ⟨e0, he0, h2, h3⟩⟩ := roundLE_G_ne q _ _ hk h
    · obtain ⟨r, hr, hid, hkr, rfl⟩ := h1
      right
      exact ⟨t, by omega, by simp only [Fin.val_last]; omega, r, (mem_mbx hG).mp hr, hid, hkr,
        rfl⟩
    · rcases ih q k hk e0 he0 with h4 | ⟨j, hj, h5, r, hr, hid, hkr, h6⟩
      · left; omega
      · right; exact ⟨j, by omega, by omega, r, hr, hid, hkr, by rw [← h2]; exact h6⟩

/-- **Lemma 4 / Corollary 5** (with the value of the entry): for `t ≥ Δ`, an entry `k ≠ q` of
`Lstable(q)` was set by a record `⟨k, LSPs, −⟩` received in some round of `[t - Δ, t)`. -/
theorem lemma_4 {q k : ι} (hk : k ≠ q) {t : ℕ} (ht : Δ ≤ t) {e : Entry Δ}
    (h : (X G γ t q).L.f k = some e) :
    ∃ j, t - Δ ≤ j ∧ j < t ∧ ∃ r, Recv G γ j q r ∧ r.id = k ∧ e.1 = suspOf r.lsps k := by
  have hpos := L_pos hΔ hG hk (by omega) h
  rcases L_hist hG t q k hk e h with h1 | ⟨j, hj, h2, h3⟩
  · omega
  · exact ⟨j, by omega, hj, h3⟩

/-- **Lemma 5** (with the value of the entry; records with `id = id(q)` are ignored by `q`, which
the paper's proof of Lemma 16 overlooks): for `t ≥ Δ`, an entry `k ≠ q` of `Gstable(q)` was set by
a record `⟨id, LSPs, −⟩` with `id ≠ q`, `k ∈ LSPs`, received in some round of `[t - Δ, t)`. -/
theorem lemma_5 {q k : ι} (hk : k ≠ q) {t : ℕ} (ht : Δ ≤ t) {e : Entry Δ}
    (h : (X G γ t q).G.f k = some e) :
    ∃ j, t - Δ ≤ j ∧ j < t ∧ ∃ r, Recv G γ j q r ∧ r.id ≠ q ∧ r.lsps.f k ≠ none ∧
      e.1 = suspOf r.lsps k := by
  have hpos := G_pos hΔ hG hk (by omega) h
  rcases G_hist hG t q k hk e h with h1 | ⟨j, hj, h2, h3⟩
  · omega
  · exact ⟨j, by omega, hj, h3⟩

end

end StabilizingLEDynamic.LE
