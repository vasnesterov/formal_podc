import Papers.PODC2013.SourceDetectionCongest.Analysis

/-!
# Lemma 4.6 and Theorem 1.2

`lemma_4_6` is the key invariant, for `β ≥ 1` pairs per message (the paper: `β = 1`, condition
`d + k ≤ r + 1`; general `β`: `d + ⌈k/β⌉ ≤ r + 1`). `theorem_1_2` is the main result:
Algorithm 1 solves `(S, h, σ)`-detection in `h + σ - 1` rounds; `theorem_1_2_beta` is the
remark after it (`h + ⌈σ/β⌉ - 1` rounds with `β` pairs per message), and both hold whether
Line 16 is executed after the loop or in every round.
-/

namespace Podc.SourceDetectionCongest

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {E : V → V → Prop} [DecidableRel E] {S : Finset V} {β : ℕ} {cap : ℕ∞}

/-- `⌈(k - β)/β⌉ + 1 = ⌈k/β⌉` for `k, β ≥ 1`. -/
lemma ceilDiv_sub_add_one {k β : ℕ} (hk : 1 ≤ k) (hβ : 1 ≤ β) :
    (k - β) ⌈/⌉ β + 1 = k ⌈/⌉ β := by
  simp only [Nat.ceilDiv_eq_add_pred_div]
  rcases le_or_gt β k with h | h
  · rw [show k + β - 1 = (k - β + β - 1) + 1 * β by omega, Nat.add_mul_div_right _ _ (by omega)]
  · rw [show k - β + β - 1 = β - 1 by omega, Nat.div_eq_of_lt (by omega),
      Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]

/-- Lemma 4.6 for `d = 0` (the base case of the paper's induction): `(0, v)` is in `L_v` from the
start and is sent in round 1. -/
lemma lemma_4_6_zero (hβ : 1 ≤ β) (v : V) (k r : ℕ) :
    topk k (Lspec E S 0 v) ⊆ (run E S β cap r v).entries ∧
      ∀ x ∈ topk k (Lspec E S 0 v), ∃ t ≤ r, x ∈ msg β (run E S β cap t v) := by
  have hL : ∀ x ∈ topk k (Lspec E S 0 v), x = toLex (0, v) ∧ v ∈ S := by
    intro x hx
    obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
    obtain ⟨hS, hm, hm0⟩ := mem_Lspec.1 (topk_subset hx)
    obtain rfl : m = 0 := by omega
    obtain rfl := hd_eq_zero.1 (by simpa using hm)
    exact ⟨rfl, hS⟩
  have h0 : ∀ hv : v ∈ S, toLex (0, v) ∈ (run E S β cap 0 v).entries := fun hv => by
    rw [State.mem_entries]; simp [run, init, hv]
  refine ⟨fun x hx => ?_, fun x hx => ⟨0, Nat.zero_le r, ?_⟩⟩
  · obtain ⟨rfl, hv⟩ := hL x hx
    exact corollary_4_4_persist_init (h0 hv) r
  · obtain ⟨rfl, hv⟩ := hL x hx
    have hun : ∀ y ∈ (run E S β cap 0 v).unsent, y = toLex (0, v) := by
      intro y hy
      obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective y
      have := (State.mem_unsent.1 hy).1
      simp only [run, init] at this
      split_ifs at this with hs
      · obtain ⟨rfl, -⟩ := hs
        have : m = 0 := by exact_mod_cast this.symm
        rw [this]
      · exact absurd this.symm (ENat.natCast_ne_top m)
    refine mem_topk.2 ⟨State.mem_unsent.2 ⟨by simp [run, init, hv], rfl⟩, ?_⟩
    rw [filter_eq_empty_iff.2 fun y hy hlt => by rw [hun y hy] at hlt; exact lt_irrefl _ hlt]
    simpa using (by omega : 0 < β)

/-- **Lemma 4.6**, for `β ≥ 1` pairs per message, in the run that does not terminate. Let
`d, k ∈ ℕ` with `d ≤ cap` and `d + ⌈k/β⌉ ≤ r + 1`. Then (i) `top_k(L_v^{(d)}) ⊆ L_v^r`, and
(ii) every element of `top_k(L_v^{(d)})` is sent by `v` in one of the rounds `1, …, r + 1`
(in round `t + 1` node `v` sends `msg β (run … t v)`).

For `β = 1` and `cap = ⊤` this is the paper's statement (`d + k ≤ r + 1`), where the paper
restricts to `r ≤ h + σ - 1` only because the algorithm stops there ("if not terminated"). -/
theorem lemma_4_6 (hβ : 1 ≤ β) : ∀ (r : ℕ) (v : V) (d k : ℕ), (d : ℕ∞) ≤ cap →
    d + k ⌈/⌉ β ≤ r + 1 →
    topk k (Lspec E S d v) ⊆ (run E S β cap r v).entries ∧
      ∀ x ∈ topk k (Lspec E S d v), ∃ t ≤ r, x ∈ msg β (run E S β cap t v) := by
  intro r
  induction r with
  | zero =>
    intro v d k hdcap hdk
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : 1 ≤ k ⌈/⌉ β := by
        rw [Nat.ceilDiv_eq_add_pred_div]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      obtain rfl : d = 0 := by omega
      exact lemma_4_6_zero hβ v k 0
  | succ r ih =>
    -- Part (i) for `r + 1`, for all `v, d, k`.
    have part_i : ∀ (v : V) (d k : ℕ), (d : ℕ∞) ≤ cap → d + k ⌈/⌉ β ≤ r + 2 →
        topk k (Lspec E S d v) ⊆ (run E S β cap (r + 1) v).entries := by
      intro v d k hdcap hdk x hx
      obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
      obtain ⟨hS, hm, hmd⟩ := mem_Lspec.1 (topk_subset hx)
      rcases m with _ | m
      · obtain rfl := hd_eq_zero.1 (by simpa using hm)
        exact corollary_4_4_persist_init (by rw [State.mem_entries]; simp [run, init, hS]) (r + 1)
      · obtain ⟨w, hw, hws⟩ := exists_pred_of_hd_eq_succ hm
        obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        have hxw := mem_topk_Lspec_pred hx hw hws
        have hdc : (d : ℕ∞) ≤ cap := le_trans (by exact_mod_cast Nat.le_succ d) hdcap
        obtain ⟨t, ht, hmsg⟩ := (ih w d k hdc (by omega)).2 _ hxw
        have hcap' : hd E s v ≤ cap := by
          rw [hm]; exact le_trans (by exact_mod_cast hmd) hdcap
        exact corollary_4_4_persist hw hmsg hm hcap' (by omega)
    intro v d k hdcap hdk
    refine ⟨part_i v d k hdcap hdk, fun x hx => ?_⟩
    by_cases hle : d + k ⌈/⌉ β ≤ r + 1
    · obtain ⟨t, ht, h⟩ := (ih v d k hdcap hle).2 x hx
      exact ⟨t, by omega, h⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hx
      · exact hk
    have hk' : d + (k - β) ⌈/⌉ β ≤ r + 1 := by
      have := ceilDiv_sub_add_one hk hβ; omega
    by_cases hx' : x ∈ topk (k - β) (Lspec E S d v)
    · obtain ⟨t, ht, h⟩ := (ih v d (k - β) hdcap hk').2 x hx'
      exact ⟨t, by omega, h⟩
    by_cases hsent : ∃ t ≤ r, x ∈ msg β (run E S β cap t v)
    · obtain ⟨t, ht, h⟩ := hsent
      exact ⟨t, by omega, h⟩
    push Not at hsent
    refine ⟨r + 1, le_rfl, ?_⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
    have hT := part_i v d k hdcap hdk
    have hest := State.mem_entries.1 (hT hx)
    have hflag : (run E S β cap (r + 1) v).sent s = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      obtain ⟨t, ht, hmsg⟩ := sent_spec (r + 1) v s hc (by rw [hest]; simp)
      rw [hest] at hmsg
      exact hsent t (by omega) (by simpa using hmsg)
    have hun : toLex (m, s) ∈ (run E S β cap (r + 1) v).unsent :=
      State.mem_unsent.2 ⟨hest, hflag⟩
    refine mem_topk.2 ⟨hun, ?_⟩
    have hsub : (run E S β cap (r + 1) v).unsent.filter (· < toLex (m, s)) ⊆
        (topk k (Lspec E S d v) \ topk (k - β) (Lspec E S d v)).erase (toLex (m, s)) := by
      intro y hy
      obtain ⟨hyu, hyx⟩ := mem_filter.1 hy
      have hyT := mem_topk_of_mem_entries (fun s h => lemma_4_3 (r + 1) v s h) hT hx
        (State.unsent_subset hyu) hyx.le
      refine mem_erase.2 ⟨hyx.ne, mem_sdiff.2 ⟨hyT, fun hy' => ?_⟩⟩
      obtain ⟨t, ht, hmsg⟩ := (ih v d (k - β) hdcap hk').2 y hy'
      obtain ⟨⟨m', s'⟩, rfl⟩ := toLex.surjective y
      have hm' := (mem_Lspec.1 (topk_subset hyT)).2.1
      have := (sent_persist hmsg hm' (r := r + 1) (by omega)).1
      rw [(State.mem_unsent.1 hyu).2] at this
      exact Bool.false_ne_true this
    have h1 := card_le_card hsub
    have h2 := card_erase_of_mem (mem_sdiff.2 ⟨hx, hx'⟩)
    have h3 := card_topk_sdiff_le (k := k - β) (k' := k) (F := Lspec E S d v)
    rw [h2] at h1
    omega

/-- The output after `r` rounds is correct as soon as `h + ⌈σ/β⌉ ≤ r + 1`. -/
theorem output_eq (hβ : 1 ≤ β) {h σ r : ℕ} (hcap : (h : ℕ∞) ≤ cap) (hr : h + σ ⌈/⌉ β ≤ r + 1)
    (v : V) : output h σ (run E S β cap r v) = topk σ (Lspec E S h v) :=
  output_eq_of_subset (fun s hs => lemma_4_3 r v s hs) (lemma_4_6 hβ r v h σ hcap hr).1

/-- **Theorem 1.2** (with the remark after its proof). With `β ≥ 1` pairs per message, the
output `top_σ` of the entries with distance `≤ h` after `h + ⌈σ/β⌉ - 1` rounds is
`top_σ(L_v^{(h)})` at every node: unweighted `(S, h, σ)`-detection is solved in
`h + ⌈σ/β⌉ - 1` rounds. Holds for Line 16 after the loop (`cap = ⊤`) and in every round
(`cap = h`). -/
theorem theorem_1_2_beta (hβ : 1 ≤ β) {h σ : ℕ} (hcap : (h : ℕ∞) ≤ cap) (v : V) :
    (output h σ (run E S β cap (h + σ ⌈/⌉ β - 1) v)).sort (· ≤ ·) =
      ((Lspec E S h v).sort (· ≤ ·)).take σ := by
  rw [output_eq hβ hcap (by omega), sort_topk]

/-- **Theorem 1.2.** Unweighted `(S, h, σ)`-detection is solved by Algorithm 1 (one pair per
message) in `σ + h - 1` rounds: after `σ + h - 1` rounds, every node `v` outputs (as a
lexicographically sorted list) `top_σ(L_v^{(h)})`. `E` is arbitrary, so this covers undirected
graphs (`E = G.Adj`, see `theorem_1_2_graph`) and directed graphs (Corollary 4.10). -/
theorem theorem_1_2 (S : Finset V) (h σ : ℕ) (v : V) :
    (output h σ (alg1 E S (σ + h - 1) v)).sort (· ≤ ·) =
      ((Lspec E S h v).sort (· ≤ ·)).take σ := by
  have := theorem_1_2_beta (E := E) (S := S) (cap := ⊤) (le_refl 1) (h := h) (σ := σ) le_top v
  simpa [Nat.ceilDiv_eq_add_pred_div, add_comm] using this

/-- **Theorem 1.2** with Line 16 executed in every round (`cap = h`). -/
theorem theorem_1_2_truncated (S : Finset V) (h σ : ℕ) (v : V) :
    (output h σ (run E S 1 h (σ + h - 1) v)).sort (· ≤ ·) =
      ((Lspec E S h v).sort (· ≤ ·)).take σ := by
  have := theorem_1_2_beta (E := E) (S := S) (cap := h) (le_refl 1) (h := h) (σ := σ) le_rfl v
  simpa [Nat.ceilDiv_eq_add_pred_div, add_comm] using this

/-- **Corollary 4.10** (directed graphs): in a directed graph `G` with arcs `G u v`, messages
sent only to out-neighbours, Algorithm 1 solves directed `(S, h, σ)`-detection
(`L_v^{(h)}` built from `hd(s, v)`, the length of a shortest directed path from `s` to `v`) in
`σ + h - 1` rounds. This is `theorem_1_2` with `E = G`. -/
theorem corollary_4_10 (G : V → V → Prop) [DecidableRel G] (S : Finset V) (h σ : ℕ) (v : V) :
    (output h σ (alg1 G S (σ + h - 1) v)).sort (· ≤ ·) =
      ((Lspec G S h v).sort (· ≤ ·)).take σ :=
  theorem_1_2 S h σ v

end Podc.SourceDetectionCongest
