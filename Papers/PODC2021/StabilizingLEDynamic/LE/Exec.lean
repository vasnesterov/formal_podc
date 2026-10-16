import Papers.PODC2021.StabilizingLEDynamic.LE.Round

/-!
# Algorithm `LE`: executions, Remark 4, and Lemma 2

We fix a dynamic graph `G` with vertex set `V` and an arbitrary initial configuration `γ`.
Times are 0-indexed: `exec … t` is the paper's `γ_{t+1}`, so the paper's "`i > 1`" is `t ≥ 1`.
-/

namespace StabilizingLEDynamic.LE

open Classical Cslib.HeardOf

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ}

theorem mem_sent {s : St ι Δ} {r : Rcd ι Δ} :
    r ∈ sent s ↔ r ∈ s.msgs ∧ 0 < r.ttl.val ∧ r.lsps.f r.id ≠ none := by
  simp [sent]

variable (G : DG ι) (γ : ι → St ι Δ)

/-- The configuration at time `t`. -/
noncomputable abbrev X (G : DG ι) (γ : ι → St ι Δ) : ℕ → ι → St ι Δ := exec (algLE Δ) G γ

/-- The received records of `q` in round `t`, in processing order. -/
noncomputable def mbx (t : ℕ) (q : ι) : List (Rcd ι Δ) :=
  (mailbox q (msgs (G t) (X G γ t) q)).toList

theorem X_succ (t : ℕ) (q : ι) : X G γ (t + 1) q = roundLE q (X G γ t q) (mbx G γ t q) := by
  change next (algLE Δ).step (G t) (X G γ t) q = _
  simp only [next, algLE, mbx]
  congr 1
  simp [msgs, hears_self]

/-- `q` receives the record `r` in round `t`. -/
def Recv (t : ℕ) (q : ι) (r : Rcd ι Δ) : Prop := ∃ k, G t k q ∧ r ∈ sent (X G γ t k)

variable {G γ} {V : Finset ι}

theorem mem_mbx (hG : IsDG V G) {t : ℕ} {q : ι} {r : Rcd ι Δ} :
    r ∈ mbx G γ t q ↔ Recv G γ t q r := by
  have hset : mailboxSet q (msgs (G t) (X G γ t) q) = {r | Recv G γ t q r} := by
    ext r
    simp only [mailboxSet, msgs, Set.mem_setOf_eq, Recv]
    constructor
    · rintro ⟨k, hk, s, hs, hr⟩
      by_cases h : Hears (G t) q k
      · rw [if_pos h] at hs; cases hs
        exact ⟨k, h.resolve_left hk, hr⟩
      · rw [if_neg h] at hs; cases hs
    · rintro ⟨k, hk, hr⟩
      exact ⟨k, (hG t k q hk).2.2, _, by rw [if_pos (show Hears (G t) q k from Or.inr hk)], hr⟩
  have hfin : (mailboxSet q (msgs (G t) (X G γ t) q)).Finite := by
    rw [hset]
    refine (V.finite_toSet.biUnion fun k _ => (sent (X G γ t k)).finite_toSet).subset ?_
    rintro r ⟨k, hk, hr⟩
    exact Set.mem_biUnion (hG t k q hk).1 hr
  simp only [mbx, mailbox, dif_pos hfin, Finset.mem_toList, Set.Finite.mem_toFinset]
  rw [hset]; rfl

theorem Recv.mem (hG : IsDG V G) {t : ℕ} {q : ι} {r : Rcd ι Δ} (h : Recv G γ t q r) :
    ∃ k ∈ V, k ≠ q ∧ r ∈ (X G γ t k).msgs ∧ 0 < r.ttl.val ∧ r.lsps.f r.id ≠ none := by
  obtain ⟨k, hk, hr⟩ := h
  obtain ⟨h1, h2, h3⟩ := mem_sent.mp hr
  exact ⟨k, (hG t k q hk).1, (hG t k q hk).2.2, h1, h2, h3⟩

/-! ### Remark 4 -/

variable (hΔ : 1 ≤ Δ)
include hΔ

/-- The suspicion value `suspicion(p)_t` (Definition 7; defined for `t ≥ 1`). -/
noncomputable def susp (G : DG ι) (γ : ι → St ι Δ) (t : ℕ) (p : ι) : ℕ :=
  suspOf (X G γ t p).L p

omit hΔ in
theorem susp_def (t : ℕ) (p : ι) : susp G γ t p = suspOf (X G γ t p).L p := rfl

/-- Remark 4(a): after the first round, `⟨id(p), susp, Δ⟩ ∈ Lstable(p)`. -/
theorem L_self {t : ℕ} (ht : 1 ≤ t) (p : ι) :
    (X G γ t p).L.f p = some (susp G γ t p, Fin.last Δ) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [susp_def, suspOf, X_succ, roundLE_L_me _ _ _ hΔ]

/-- Remark 4(b): after the first round, `Gstable(p)[id(p)] = Lstable(p)[id(p)]`. -/
theorem G_self {t : ℕ} (ht : 1 ≤ t) (p : ι) :
    (X G γ t p).G.f p = some (susp G γ t p, Fin.last Δ) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [X_succ, roundLE_G_me _ _ _ hΔ, ← X_succ, L_self hΔ (by omega)]

/-- The suspicion value only grows, by the number of received records (from other processes)
not containing `p` (line 18). -/
theorem susp_succ {t : ℕ} (ht : 1 ≤ t) (p : ι) :
    susp G γ (t + 1) p = susp G γ t p + nIncr p (mbx G γ t p) := by
  rw [susp_def, suspOf, X_succ, roundLE_L_me _ _ _ hΔ, baseSusp_eq (L_self hΔ ht p)]

theorem susp_mono {t u : ℕ} (ht : 1 ≤ t) (htu : t ≤ u) (p : ι) :
    susp G γ t p ≤ susp G γ u p := by
  induction u, htu using Nat.le_induction with
  | base => exact le_rfl
  | succ u hu ih => rw [susp_succ hΔ (by omega)]; omega

theorem lid_eq {t : ℕ} (ht : 1 ≤ t) (p : ι) : (algLE Δ).lid p (X G γ t p) =
    leaderOf p (X G γ t p).G := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  change (X G γ (t + 1) p).lid = _
  rw [X_succ]; rfl

/-! ### Lemma 2 (provenance of records) -/

omit hΔ in
/-- **Lemma 2** (and Corollary 4). A record `⟨id, LSPs, ttl⟩` with `ttl ≥ 1` in `msgs(q)` at time
`t ≥ Δ - ttl + 1` was initiated by the process `id ∈ V` at the end of round `t - (Δ - ttl) - 1`,
with `LSPs = Lstable(id)_{t - (Δ - ttl)}`. -/
theorem provenance (hG : IsDG V G) (t : ℕ) :
    ∀ q ∈ V, ∀ r ∈ (X G γ t q).msgs, 1 ≤ r.ttl.val → Δ - r.ttl.val + 1 ≤ t →
      r.id ∈ V ∧ r.lsps = (X G γ (t - (Δ - r.ttl.val)) r.id).L := by
  induction t with
  | zero => intro q _ r _ _ h; omega
  | succ t ih =>
    intro q hq r hr h1 h2
    rw [X_succ, roundLE_msgs] at hr
    rcases hr with rfl | ⟨r0, hr0, h3, h4, rfl⟩
    · simp only [Fin.val_last, Nat.sub_self, Nat.sub_zero]
      exact ⟨hq, by rw [X_succ]⟩
    · have hd : (dec r0.ttl).val = r0.ttl.val - 1 := rfl
      simp only [hd] at h1 h2 ⊢
      have key : ∃ k ∈ V, r0 ∈ (X G γ t k).msgs := by
        rcases mem_foldl_bodyM hr0 with h | ⟨h, -⟩
        · exact ⟨q, hq, h⟩
        · obtain ⟨k, hk, -, h, -⟩ := ((mem_mbx hG).mp h).mem hG
          exact ⟨k, hk, h⟩
      obtain ⟨k, hk, hr0k⟩ := key
      obtain ⟨h5, h6⟩ := ih k hk r0 hr0k (by omega) (by omega)
      refine ⟨h5, ?_⟩
      rw [h6]; congr 2; omega

end StabilizingLEDynamic.LE
