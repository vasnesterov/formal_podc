import Papers.PODC2014.MultiMessageBroadcastMAC.Lemmas
import Cslib.Foundations.Combinatorics.SimpleGraph.Ball

/-!
# Theorem 3.1: BMMB in `O((D + k) F_ack)` time for arbitrary `G'`

The pipeline argument of §3.1: for the source `u` of a message `m` and every node `v` at distance
`d` from `u` in `G`, after `(d + ℓ) F_ack` time `v` has acknowledged `m` or at least `ℓ` messages
(`theorem_3_1_key`). No assumption on `G'` and no progress bound are needed.
-/

namespace Podc.MultiMessageBroadcastMAC

variable {V M : Type*}

namespace Exec

variable [DecidableEq V] [DecidableEq M] {G G' : SimpleGraph V} {α : Exec G G' M}

/-- A message in `R_v(t)` is acknowledged at `v`, or `ℓ` messages are, by time `t + ℓ F_ack`. -/
lemma mem_C_or_le_card {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack) {v : V} {t : ℝ}
    (ht : 0 ≤ t) {m : M} (hm : m ∈ α.R v t) (ℓ : ℕ) :
    m ∈ α.C v (t + ℓ * Fack) ∨ ℓ ≤ (α.C v (t + ℓ * Fack)).card := by
  induction ℓ with
  | zero => right; simp
  | succ ℓ ih =>
    set s := t + ℓ * Fack
    have hs : t + ((ℓ + 1 : ℕ) : ℝ) * Fack = s + Fack := by simp only [s]; push_cast; ring
    rw [hs]
    have hts : t ≤ s := le_add_of_nonneg_right (by positivity)
    have hss : 0 ≤ s := ht.trans hts
    have hmono := (α.lemma_3_5_1 v (show s ≤ s + Fack by linarith)).2
    by_cases hmC : m ∈ α.C v s
    · exact Or.inl (hmono hmC)
    · rcases ih with h | h
      · exact absurd h hmC
      · right
        have hb : (α.at_ s).Busy v :=
          α.busy_of_not_subset fun hsub => hmC (hsub ((α.lemma_3_5_1 v hts).1 hm))
        have := ack_progress hA hss hb
        rw [card_C] at h ⊢
        omega

/-- The key claim in the proof of Theorem 3.1: if `m` arrives at `u` (at time `0`) and `v` is at
distance `d` from `u` in `G`, then after `(d + ℓ) F_ack` time the sent set `C_v` of `v` contains
`m` or at least `ℓ` messages. -/
theorem theorem_3_1_key {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack)
    (h0 : α.ArrivalsAtZero) {u : V} {m : M} (hm : α.Arrives u m) (ℓ d : ℕ) (v : V)
    (hd : G.edist u v = d) :
    m ∈ α.C v ((d + ℓ) * Fack) ∨ ℓ ≤ (α.C v ((d + ℓ) * Fack)).card := by
  induction ℓ generalizing d v with
  | zero => right; simp
  | succ ℓ ihℓ =>
    induction d generalizing v with
    | zero =>
      obtain rfl : u = v := (SimpleGraph.edist_eq_zero_iff (G := G)).1 (by simpa using hd)
      have := mem_C_or_le_card hA hF le_rfl (α.mem_R_zero h0 hm) (ℓ + 1)
      simpa using this
    | succ d ihd =>
      obtain ⟨w, hw, hwv⟩ := SimpleGraph.exists_adj_of_edist_eq_succ hd
      set s := ((d + 1 : ℕ) + ℓ : ℝ) * Fack
      have hs0 : 0 ≤ s := by positivity
      have hs : ((d + 1 : ℕ) + (ℓ + 1 : ℕ) : ℝ) * Fack = s + Fack := by
        simp only [s]; push_cast; ring
      have hs' : ((d : ℕ) + (ℓ + 1 : ℕ) : ℝ) * Fack = s := by simp only [s]; push_cast; ring
      rw [hs]
      have hmono := (α.lemma_3_5_1 v (show s ≤ s + Fack by linarith)).2
      have hv := ihℓ (d + 1) v hd
      change m ∈ α.C v s ∨ ℓ ≤ (α.C v s).card at hv
      have hw' := ihd w hw
      rw [hs'] at hw'
      by_cases hmC : m ∈ α.C v s
      · exact Or.inl (hmono hmC)
      by_cases hcard : ℓ + 1 ≤ (α.C v s).card
      · exact Or.inr (hcard.trans (Finset.card_le_card hmono))
      right
      have hvℓ : (α.C v s).card = ℓ := by
        rcases hv with h | h
        · exact absurd h hmC
        · omega
      -- `v` got a message it has not acknowledged
      have hsub : α.C w s ⊆ α.R v s := α.lemma_3_5_3 hwv.symm le_rfl
      have hb : (α.at_ s).Busy v := by
        refine α.busy_of_not_subset fun hRC => ?_
        rcases hw' with h | h
        · exact hmC (hRC (hsub h))
        · have := Finset.card_le_card (hsub.trans hRC)
          omega
      have := ack_progress hA hs0 hb
      rw [card_C] at hvℓ ⊢
      omega

/-- **Theorem 3.1** (Ghaffari–Kantor–Lynch–Newport): in the standard abstract MAC layer model with
an arbitrary `G'`, BMMB delivers every message `m` that arrives at a node `u` at time `0` to every
node `v` of `u`'s component of `G` (`v` even acknowledges `m`) by time `(d + k) F_ack`, where
`d = d_G(u, v)` and `k` bounds the number of messages. In particular, every message reaches its
whole component within `(D + k) F_ack`, `D` the diameter of `G`: `O((D + k) F_ack)` time. -/
theorem theorem_3_1 {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack) (h0 : α.ArrivalsAtZero)
    {K : Finset M} (hK : ∀ i m, α.Arrives i m → m ∈ K) {k : ℕ} (hk : K.card ≤ k)
    {u v : V} {m : M} (hm : α.Arrives u m) (huv : G.Reachable u v) :
    m ∈ α.C v ((G.dist u v + k) * Fack) ∧ m ∈ α.R v ((G.dist u v + k) * Fack) := by
  have hC : m ∈ α.C v ((G.dist u v + k) * Fack) := by
    rcases theorem_3_1_key hA hF h0 hm k (G.dist u v) v huv.coe_dist_eq_edist.symm with h | h
    · exact h
    · have hsub := (α.C_subset_R v ((G.dist u v + k) * Fack)).trans (α.R_subset hK v _)
      have heq : α.C v ((G.dist u v + k) * Fack) = K :=
        Finset.eq_of_subset_of_card_le hsub (hk.trans h)
      rw [heq]; exact hK u m hm
  exact ⟨hC, α.C_subset_R v _ hC⟩

/-- **Theorem 3.1**, diameter form: if every node of `u`'s component is within distance `D` of
`u`, then by time `(D + k) F_ack` every node of the component got `m`. -/
theorem theorem_3_1_diam {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack)
    (h0 : α.ArrivalsAtZero) {K : Finset M} (hK : ∀ i m, α.Arrives i m → m ∈ K) {k : ℕ}
    (hk : K.card ≤ k) {D : ℕ} {u v : V} {m : M} (hm : α.Arrives u m) (huv : G.Reachable u v)
    (hD : G.dist u v ≤ D) : m ∈ α.R v ((D + k) * Fack) := by
  refine (α.lemma_3_5_1 v ?_).1 (theorem_3_1 hA hF h0 hK hk hm huv).2
  gcongr

end Exec

end Podc.MultiMessageBroadcastMAC
