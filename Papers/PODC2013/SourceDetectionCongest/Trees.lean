import Papers.PODC2013.SourceDetectionCongest.Main

/-!
# Corollary 4.7: BFS trees and the concurrent-flooding schedule

For a source `s` in the output of `v` (`(m + 1, s) ∈ top_σ(L_v^{(h)})`, so `v ≠ s`), the paper
lets `p_s(v)` be "the node from which `v` receives `(hd(s,v) - 1, s)` for the first time". Several
in-neighbours may send this pair in the same round, so `p_s(v)` needs a tie-break; we prove the
statements for *every* in-neighbour that sends the pair in the first round in which `v` receives
it (`IsFirstRecv`), so any tie-break works.
-/

namespace Podc.SourceDetectionCongest

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {E : V → V → Prop} [DecidableRel E] {S : Finset V} {β : ℕ} {cap : ℕ∞}

/-- A stored distance `n + 1` was produced by receiving `(n, s)` in an earlier round. -/
lemma exists_recv_of_est_succ : ∀ (t : ℕ) (v s : V) (n : ℕ),
    (run E S β cap t v).est s = ((n + 1 : ℕ) : ℕ∞) →
    ∃ t' < t, ∃ u, E u v ∧ toLex (n, s) ∈ msg β (run E S β cap t' u)
  | 0, v, s, n, h => by
      simp only [run, init] at h
      split_ifs at h
      · exact absurd h (by norm_cast)
      · exact absurd h.symm (ENat.natCast_ne_top _)
  | t + 1, v, s, n, h => by
      rw [est_succ] at h
      split_ifs at h with hc
      · exact absurd h.symm (ENat.natCast_ne_top _)
      rcases min_choice ((run E S β cap t v).est s) (recv (inboxAt E S β cap t v) s) with he | he
      · rw [he] at h
        obtain ⟨t', ht', hu⟩ := exists_recv_of_est_succ t v s n h
        exact ⟨t', by omega, hu⟩
      · rw [he] at h
        obtain ⟨u, x, hx, hs, heq⟩ := exists_of_recv_ne_top (by rw [h]; simp)
        simp only [inboxAt] at hx
        split_ifs at hx with huv
        · obtain ⟨⟨m, s'⟩, rfl⟩ := toLex.surjective x
          simp only [ofLex_toLex] at hs heq
          subst hs
          rw [h] at heq
          have h2 : n + 1 = m + 1 := by exact_mod_cast heq
          obtain rfl : n = m := by omega
          exact ⟨t, by omega, u, huv, hx⟩
        · simp at hx

omit [Fintype V] [DecidableRel E] in
/-- `top_k(L_u^{(d)})` grows with `d`. -/
lemma topk_Lspec_mono {d d' k : ℕ} {u : V} (h : d ≤ d') {x : ℕ ×ₗ V}
    (hx : x ∈ topk k (Lspec E S d u)) : x ∈ topk k (Lspec E S d' u) := by
  rw [mem_topk] at hx ⊢
  refine ⟨Lspec_mono h hx.1, lt_of_le_of_lt (card_le_card fun y hy0 => ?_) hx.2⟩
  obtain ⟨hy, hyx⟩ := mem_filter.1 hy0
  refine mem_filter.2 ⟨?_, hyx⟩
  obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective y
  obtain ⟨⟨m', s'⟩, rfl⟩ := toLex.surjective x
  obtain ⟨hS, hm, -⟩ := mem_Lspec.1 hy
  have hx' := (mem_Lspec.1 hx.1).2.2
  have : m ≤ m' := by
    rw [Prod.Lex.toLex_lt_toLex] at hyx; rcases hyx with h | ⟨h, -⟩ <;> omega
  exact mem_Lspec.2 ⟨hS, hm, by omega⟩

omit [Fintype V] [DecidableRel E] in
/-- If `σ ≥ |S|`, then `top_σ(L_v^{(h)}) = L_v^{(h)}`. -/
lemma topk_Lspec_of_card_le {h σ : ℕ} {v : V} (hσ : #S ≤ σ) :
    topk σ (Lspec E S h v) = Lspec E S h v := by
  apply subset_antisymm topk_subset
  intro x hx
  have hcard : #(Lspec E S h v) ≤ σ :=
    card_image_le.trans ((card_filter_le S (fun s => hd E s v ≤ h)).trans hσ)
  have hlt : #((Lspec E S h v).filter (· < x)) < #(Lspec E S h v) :=
    card_lt_card ⟨filter_subset _ _, fun h => by simpa using (mem_filter.1 (h hx)).2⟩
  exact mem_topk.2 ⟨hx, lt_of_lt_of_le hlt hcard⟩

/-- `v` receives `(m, s)` in round `t + 1` (from some in-neighbour). -/
def RecvAt (E : V → V → Prop) [DecidableRel E] (S : Finset V) (β : ℕ) (cap : ℕ∞)
    (t : ℕ) (v s : V) (m : ℕ) : Prop :=
  ∃ u, E u v ∧ toLex (m, s) ∈ msg β (run E S β cap t u)

/-- Round `t + 1` is the first round in which `v` receives `(m, s)`. -/
def IsFirstRecv (E : V → V → Prop) [DecidableRel E] (S : Finset V) (β : ℕ) (cap : ℕ∞)
    (t : ℕ) (v s : V) (m : ℕ) : Prop :=
  RecvAt E S β cap t v s m ∧ ∀ t' < t, ¬ RecvAt E S β cap t' v s m

/-- **Corollary 4.7** (with `T = h + ⌈σ/β⌉ - 1`, the running time of Theorem 1.2; `T = h + σ - 1`
for Algorithm 1). Let `(m + 1, s)` be in the output `top_σ(L_v^{(h)})` of `v`.

* (i) `v` receives `(m, s)` from an in-neighbour by round `T` (the paper: `h + σ`);
* (ii) every in-neighbour `u` that sends `(m, s)` to `v` in the first round in which `v`
  receives it (a candidate for `p_s(v)`) satisfies `hd(s, u) = m = hd(s, v) - 1` and has `s` in
  its own output: the parent pointers form a BFS tree of `s` inside the nodes that output `s`;
* (iii) `v` sends `(m + 1, s)` in some round `≤ T + 1` (i.e., within `h + σ` rounds for
  Algorithm 1), and only after the round in which `u` sent `(m, s)`: the sending pattern is a
  schedule for concurrent flooding on all these trees. -/
theorem corollary_4_7 (hβ : 1 ≤ β) {h σ : ℕ} (hcap : (h : ℕ∞) ≤ cap) {v s : V} {m : ℕ}
    (hx : toLex (m + 1, s) ∈ topk σ (Lspec E S h v)) :
    (∃ t, t + 1 ≤ h + σ ⌈/⌉ β - 1 ∧ RecvAt E S β cap t v s m) ∧
    (∀ t u, IsFirstRecv E S β cap t v s m → E u v → toLex (m, s) ∈ msg β (run E S β cap t u) →
      hd E s u = m ∧ toLex (m, s) ∈ topk σ (Lspec E S h u) ∧
      (∃ t' ≤ h + σ ⌈/⌉ β - 1, toLex (m + 1, s) ∈ msg β (run E S β cap t' v)) ∧
      ∀ t', toLex (m + 1, s) ∈ msg β (run E S β cap t' v) → t < t') := by
  obtain ⟨hS, hm, hmh⟩ := mem_Lspec.1 (topk_subset hx)
  have hσ : 1 ≤ σ := by
    rcases Nat.eq_zero_or_pos σ with rfl | h; · simp at hx
    exact h
  have hc : 1 ≤ σ ⌈/⌉ β := by
    rw [Nat.ceilDiv_eq_add_pred_div]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have hcap' : (h' : ℕ∞) ≤ cap := le_trans (by exact_mod_cast Nat.le_succ h') hcap
  refine ⟨?_, fun t u hfirst huv hu => ?_⟩
  · -- (i)
    obtain ⟨w, hw, hws⟩ := exists_pred_of_hd_eq_succ hm
    have hxw := mem_topk_Lspec_pred hx hw hws
    obtain ⟨t, ht, hmsg⟩ :=
      (lemma_4_6 hβ (h' + σ ⌈/⌉ β - 1) w h' σ hcap' (by omega)).2 _ hxw
    exact ⟨t, by omega, w, hw, hmsg⟩
  · -- (ii)
    have hest := State.mem_entries.1 (msg_subset_entries hu)
    have hle := hd_le_est (E := E) (S := S) (β := β) (cap := cap) t u s
    rw [hest] at hle
    have hge := hd_le_succ (s := s) huv
    rw [hm] at hge
    have hum : hd E s u = m := by
      apply le_antisymm hle
      generalize hd E s u = y at hge hle
      induction y using ENat.recTopCoe with
      | top => simp at hle
      | coe y =>
        have : m + 1 ≤ y + 1 := by exact_mod_cast hge
        exact_mod_cast (by omega : m ≤ y)
    refine ⟨hum, topk_Lspec_mono (Nat.le_succ h') (mem_topk_Lspec_pred hx huv hum), ?_, ?_⟩
    · -- (iii) `v` sends its pair by round `T + 1`
      obtain ⟨t', ht', hmsg⟩ := (lemma_4_6 hβ (h' + 1 + σ ⌈/⌉ β - 1) v (h' + 1) σ hcap
        (by omega)).2 _ hx
      exact ⟨t', ht', hmsg⟩
    · -- (iii) and only after its parent
      intro t' ht'
      have hest' := State.mem_entries.1 (msg_subset_entries ht')
      obtain ⟨t'', ht'', u', hu'v, hu'⟩ := exists_recv_of_est_succ t' v s m hest'
      by_contra hle'
      exact hfirst.2 t'' (by omega) ⟨u', hu'v, hu'⟩

omit [Fintype V] [DecidableRel E] in
/-- Corollary 4.7(ii), last sentence: if `σ ≥ |S|`, every node within distance `h` of `s` outputs
`s`, so the tree of `s` comprises all of them. -/
theorem corollary_4_7_all {h σ : ℕ} (hσ : #S ≤ σ) {v s : V} (hs : s ∈ S) (hv : hd E s v ≤ h) :
    toLex ((hd E s v).toNat, s) ∈ topk σ (Lspec E S h v) := by
  rw [topk_Lspec_of_card_le hσ]
  have hfin : hd E s v ≠ ⊤ := ne_top_of_le_ne_top (by simp) hv
  refine mem_Lspec.2 ⟨hs, (ENat.natCast_toNat hfin).symm, ?_⟩
  rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hfin]; exact hv

end Podc.SourceDetectionCongest
