import Papers.PODC2019.SmallBuffersAQT.Phase
import Podc.Computability.Distributed.AQT.Basic

/-!
# Theorem 4.1: buffer space of HPTS

An execution (`Run`) of HPTS on the path `⟨n⟩`, `n = m^ℓ`, against a *batched* adversary
`b : ℕ → ℕ → ℕ → ℕ` (batch `φ` is accepted at the first round `ℓφ` of phase `φ`, Algorithm 3
lines 3–5): round `r` forwards at level `sched (r mod ℓ)` with an arbitrary valid choice of packets
inside pseudo-buffers, and the next batch is added when a phase is over. For the paper's adversary
`A`, the batches are its `ℓ`-reduction `Cslib.AQT.reduce A ℓ` (Definition 2.4).

* `Run.badness_le`: with levels processed in decreasing order inside each phase (`fixedSched`), if
  the batched adversary is `(ρ', σ)`-bounded with `ρ' ≤ 1` then every badness is at most `σ + 1`.
* `Run.occ_le`: every buffer holds at most `(#pseudo-buffers in use) + σ + 1 ≤ ℓ m + σ + 1`
  packets (`theorem_4_1`).
-/

namespace Podc.SmallBuffersAQT

open Finset Cslib.AQT

variable {m ℓ : ℕ}

variable (m ℓ) in
/-- Accept batch `φ` of the batched adversary `b`. -/
def addBatch (b : ℕ → ℕ → ℕ → ℕ) (φ : ℕ) (c : Config) : Config :=
  fun i w => c i w + if i < w ∧ w < m ^ ℓ then b φ i w else 0

variable (m ℓ) in
/-- Occupancy of the buffer of node `i`. -/
def occ (c : Config) (i : ℕ) : ℕ := ∑ w ∈ range (m ^ ℓ), c i w

variable (m ℓ) in
/-- Well-formed configurations: every stored packet still has to move right inside the path. -/
def WF (c : Config) : Prop := ∀ i w, c i w ≠ 0 → i < w ∧ w < m ^ ℓ

/-- The paper's schedule (Algorithm 3: `λ = t mod ℓ`, increasing levels within a phase). -/
def paperSched (_ℓ p : ℕ) : ℕ := p

/-- The repaired schedule: decreasing levels `ℓ-1, …, 0` within a phase. -/
def fixedSched (ℓ p : ℕ) : ℕ := ℓ - 1 - p

variable (m ℓ) in
/-- An execution of HPTS with schedule `sched` against the batched adversary `b`. The choice of
the forwarded packet inside each pseudo-buffer (`sel r`) is arbitrary. -/
structure Run (sched : ℕ → ℕ → ℕ) (b : ℕ → ℕ → ℕ → ℕ) where
  cfg : ℕ → Config
  sel : ℕ → ℕ → Key → ℕ
  valid : ∀ r, ValidSel m ℓ (cfg r) (sel r)
  init : cfg 0 = addBatch m ℓ b 0 (fun _ _ => 0)
  step : ∀ r, cfg (r + 1) =
    if (r + 1) % ℓ = 0 then
      addBatch m ℓ b ((r + 1) / ℓ) (hptsStep m ℓ (sched ℓ (r % ℓ)) (cfg r) (sel r))
    else hptsStep m ℓ (sched ℓ (r % ℓ)) (cfg r) (sel r)

section Lemmas

lemma pb_addBatch (b : ℕ → ℕ → ℕ → ℕ) (φ : ℕ) (c : Config) (u : ℕ) (q : Key) :
    pb m ℓ (addBatch m ℓ b φ c) u q =
      pb m ℓ c u q + ∑ w ∈ (range (m ^ ℓ)).filter (fun w => u < w ∧ key m ℓ u w = q), b φ u w := by
  unfold pb addBatch
  rw [← sum_add_distrib]
  refine sum_congr rfl fun w hw => ?_
  simp only [mem_filter, mem_range] at hw
  rw [ite_eq_left ⟨hw.2.1, hw.1⟩]

/-- Accepting a batch increases the badness of `i` by at most the number of new packets that have
to cross `i`. -/
lemma badness_addBatch_le (b : ℕ → ℕ → ℕ → ℕ) (φ : ℕ) (c : Config) (i : ℕ) :
    badness m ℓ (addBatch m ℓ b φ c) i ≤ badness m ℓ c i + cross b (m ^ ℓ) i φ (φ + 1) := by
  classical
  set s := (KS m ℓ).filter (fun q => q.1 ∈ range ℓ ∧ i < q.2)
  have h1 : badness m ℓ (addBatch m ℓ b φ c) i ≤ badness m ℓ c i +
      ∑ q ∈ s, ∑ u ∈ range (i + 1),
        ∑ w ∈ (range (m ^ ℓ)).filter (fun w => u < w ∧ key m ℓ u w = q), b φ u w := by
    unfold badness Bad
    rw [← sum_add_distrib]
    refine sum_le_sum fun q _ => ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun u _ => ?_
    rw [pb_addBatch]; omega
  refine h1.trans (Nat.add_le_add_left ?_ _)
  rw [sum_comm]
  unfold cross
  rw [Nat.Ico_succ_singleton, sum_singleton]
  refine sum_le_sum fun u _ => ?_
  have hfib : ∑ q ∈ s, ∑ w ∈ (range (m ^ ℓ)).filter (fun w => u < w ∧ key m ℓ u w = q), b φ u w =
      ∑ w ∈ (range (m ^ ℓ)).filter (fun w => u < w ∧ key m ℓ u w ∈ s), b φ u w := by
    rw [← sum_fiberwise_of_maps_to (s := (range (m ^ ℓ)).filter (fun w => u < w ∧ key m ℓ u w ∈ s))
      (t := s) (g := key m ℓ u) (fun w hw => (mem_filter.1 hw).2.2)]
    refine sum_congr rfl fun q hq => ?_
    rw [filter_filter]
    congr 1
    ext w
    simp only [mem_filter]
    aesop
  rw [hfib]
  refine sum_le_sum_of_subset fun w hw => ?_
  simp only [mem_filter, mem_range, s, KS, mem_product] at hw
  simp only [mem_Ioo]
  exact ⟨hw.2.2.2.2.trans_le (xd_le u w), hw.1⟩

/-- The keys (pseudo-buffers) in use at node `i`. -/
def keysAt (m ℓ : ℕ) (c : Config) (i : ℕ) : Finset Key :=
  ((range (m ^ ℓ)).filter (fun w => i < w ∧ c i w ≠ 0)).image (key m ℓ i)

/-- A buffer holds at most one non-bad packet per pseudo-buffer in use plus its bad packets. -/
lemma occ_le (c : Config) (hc : WF m ℓ c) (i : ℕ) :
    occ m ℓ c i ≤ (keysAt m ℓ c i).card + badness m ℓ c i := by
  classical
  set T := (range (m ^ ℓ)).filter (fun w => i < w ∧ c i w ≠ 0)
  have h1 : occ m ℓ c i = ∑ w ∈ T, c i w := by
    unfold occ
    rw [sum_filter]
    refine sum_congr rfl fun w _ => ?_
    split_ifs with h
    · rfl
    · by_contra hne
      exact h ⟨(hc i w (Ne.symm hne |>.symm)).1, Ne.symm (Ne.symm hne)⟩
  have h2 : ∑ w ∈ T, c i w = ∑ q ∈ keysAt m ℓ c i, ∑ w ∈ T.filter (fun w => key m ℓ i w = q), c i w :=
    (sum_fiberwise_of_maps_to (fun w hw => mem_image_of_mem _ hw) _).symm
  have h3 : ∀ q ∈ keysAt m ℓ c i, ∑ w ∈ T.filter (fun w => key m ℓ i w = q), c i w ≤ pb m ℓ c i q := by
    intro q _
    unfold pb
    refine sum_le_sum_of_subset fun w hw => ?_
    simp only [T, mem_filter] at hw ⊢
    exact ⟨hw.1.1, hw.1.2.1, hw.2⟩
  have hsub : keysAt m ℓ c i ⊆ (KS m ℓ).filter (fun q => q.1 ∈ range ℓ ∧ i < q.2) := by
    intro q hq
    simp only [keysAt, mem_image, mem_filter, mem_range] at hq
    obtain ⟨w, ⟨hw, hiw, -⟩, rfl⟩ := hq
    obtain ⟨hlt, -, -⟩ := lv_spec hiw hw
    simp only [KS, mem_filter, mem_product, mem_range, key]
    exact ⟨⟨hlt, (xd_le i w).trans_lt hw⟩, hlt, lt_xd hiw hw⟩
  have h4 : ∑ q ∈ keysAt m ℓ c i, (pb m ℓ c i q - 1) ≤ badness m ℓ c i := by
    unfold badness Bad
    refine (sum_le_sum_of_subset hsub).trans (sum_le_sum fun q _ => ?_)
    exact single_le_sum (f := fun u => pb m ℓ c u q - 1) (fun _ _ => Nat.zero_le _)
      (mem_range.2 (Nat.lt_succ_self i))
  rw [h1, h2]
  calc ∑ q ∈ keysAt m ℓ c i, ∑ w ∈ T.filter (fun w => key m ℓ i w = q), c i w
      ≤ ∑ q ∈ keysAt m ℓ c i, (1 + (pb m ℓ c i q - 1)) := sum_le_sum fun q hq => by
        have := h3 q hq; omega
    _ = (keysAt m ℓ c i).card + ∑ q ∈ keysAt m ℓ c i, (pb m ℓ c i q - 1) := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
    _ ≤ _ := Nat.add_le_add_left h4 _

/-- At most `ℓ m` pseudo-buffers per node (`ℓ n^{1/ℓ}` in the paper). -/
lemma card_keysAt_le (c : Config) (i : ℕ) : (keysAt m ℓ c i).card ≤ ℓ * m := by
  have hsub : keysAt m ℓ c i ⊆ (range ℓ ×ˢ range m).image
      (fun p : ℕ × ℕ => (p.1, i / m ^ (p.1 + 1) * m ^ (p.1 + 1) + p.2 * m ^ p.1)) := by
    intro q hq
    simp only [keysAt, mem_image, mem_filter, mem_range] at hq
    obtain ⟨w, ⟨hw, hiw, -⟩, rfl⟩ := hq
    exact key_mem_image hiw hw
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp

/-- At most one pseudo-buffer per destination in use. -/
lemma card_keysAt_le_dest (c : Config) (i : ℕ) (D : Finset ℕ) (hD : ∀ w, c i w ≠ 0 → w ∈ D) :
    (keysAt m ℓ c i).card ≤ D.card := by
  refine card_image_le.trans (card_le_card fun w hw => ?_)
  simp only [mem_filter] at hw
  exact hD w hw.2.2

lemma WF_addBatch (b : ℕ → ℕ → ℕ → ℕ) (φ : ℕ) {c : Config} (hc : WF m ℓ c) :
    WF m ℓ (addBatch m ℓ b φ c) := by
  intro i w h
  unfold addBatch at h
  by_cases h' : c i w = 0
  · rw [h', zero_add] at h
    split_ifs at h with hh
    · exact hh
    · exact absurd rfl h
  · exact hc i w h'

lemma WF_hptsStep {c : Config} {sel : ℕ → Key → ℕ} (hsel : ValidSel m ℓ c sel) (hc : WF m ℓ c)
    (lam : ℕ) : WF m ℓ (hptsStep m ℓ lam c sel) := by
  intro i w h
  unfold hptsStep fwd at h
  by_cases h' : c i w = 0
  · rw [h'] at h
    split_ifs at h with h1 h2 h2
    · obtain ⟨-, -, hw, -⟩ := arrival_key hsel h2; exact ⟨(arrival_spec h2).2.2, hw⟩
    · simp at h
    · obtain ⟨-, -, hw, -⟩ := arrival_key hsel h2; exact ⟨(arrival_spec h2).2.2, hw⟩
    · simp at h
  · exact hc i w h'

end Lemmas

namespace Run

variable {sched : ℕ → ℕ → ℕ} {b : ℕ → ℕ → ℕ → ℕ} (R : Run m ℓ sched b)

/-- The configuration of round `r` after forwarding. -/
def post (r : ℕ) : Config := hptsStep m ℓ (sched ℓ (r % ℓ)) (R.cfg r) (R.sel r)

lemma wf (r : ℕ) : WF m ℓ (R.cfg r) := by
  induction r with
  | zero =>
    rw [R.init]
    exact WF_addBatch b 0 (fun i w h => absurd rfl h)
  | succ r ih =>
    rw [R.step r]
    split_ifs
    · exact WF_addBatch b _ (WF_hptsStep (R.valid r) ih _)
    · exact WF_hptsStep (R.valid r) ih _

lemma cfg_succ_of_ne (_hℓ : 1 ≤ ℓ) {φ k : ℕ} (hk : k + 1 < ℓ) :
    R.cfg (ℓ * φ + k + 1) = R.post (ℓ * φ + k) := by
  rw [R.step, ite_eq_right]
  · rfl
  · rw [show ℓ * φ + k + 1 = (k + 1) + ℓ * φ by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hk]
    omega

lemma cfg_phase_start (hℓ : 1 ≤ ℓ) (φ : ℕ) :
    R.cfg (ℓ * (φ + 1)) = addBatch m ℓ b (φ + 1) (R.post (ℓ * φ + (ℓ - 1))) := by
  have h : ℓ * (φ + 1) = ℓ * φ + (ℓ - 1) + 1 := by rw [mul_add]; omega
  rw [h, R.step, ite_eq_left]
  · congr 1
    rw [← h, Nat.mul_div_cancel_left _ (by omega)]
  · rw [← h]; exact Nat.mul_mod_right _ _

lemma mod_phase (_hℓ : 1 ≤ ℓ) {φ k : ℕ} (hk : k < ℓ) : (ℓ * φ + k) % ℓ = k := by
  rw [show ℓ * φ + k = k + ℓ * φ by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

/-- One phase of a run with the repaired schedule satisfies the hypothesis of
`phase_decreasing`. -/
lemma phase_facts (hR : sched = fixedSched) (hℓ : 1 ≤ ℓ) (φ i : ℕ) :
    (∀ k < ℓ, badness m ℓ (R.cfg (ℓ * φ + k)) i ≤ badness m ℓ (R.cfg (ℓ * φ)) i) ∧
      badness m ℓ (R.post (ℓ * φ + (ℓ - 1))) i ≤ badness m ℓ (R.cfg (ℓ * φ)) i - 1 := by
  set d : ℕ → Config := fun k => if k < ℓ then R.cfg (ℓ * φ + k) else R.post (ℓ * φ + (ℓ - 1))
  have hd : ∀ k ≤ ℓ - 1, ∃ sel, ValidSel m ℓ (d k) sel ∧
      d (k + 1) = hptsStep m ℓ (ℓ - 1 - k) (d k) sel := by
    intro k hk
    refine ⟨R.sel (ℓ * φ + k), ?_, ?_⟩
    · simp only [d, ite_eq_left (show k < ℓ by omega)]; exact R.valid _
    · have hdk : d k = R.cfg (ℓ * φ + k) := by simp only [d, ite_eq_left (show k < ℓ by omega)]
      rw [hdk]
      have hpost : R.post (ℓ * φ + k) = hptsStep m ℓ (ℓ - 1 - k) (R.cfg (ℓ * φ + k)) (R.sel (ℓ * φ + k)) := by
        simp only [post, hR, fixedSched, mod_phase hℓ (show k < ℓ by omega)]
      rcases Nat.lt_or_ge (k + 1) ℓ with h | h
      · simp only [d, ite_eq_left h]
        rw [← add_assoc, R.cfg_succ_of_ne hℓ h, hpost]
      · simp only [d, ite_eq_right (show ¬ (k + 1 < ℓ) by omega)]
        rw [show ℓ * φ + (ℓ - 1) = ℓ * φ + k by omega, hpost]
  have hd0 : d 0 = R.cfg (ℓ * φ) := by simp [d, show 0 < ℓ by omega]
  obtain ⟨hle, hlt⟩ := phase_decreasing (m := m) (ℓ := ℓ) i (ℓ - 1) (by omega) d hd
  rw [hd0] at hle hlt
  refine ⟨fun k hk => ?_, ?_⟩
  · have := hle k (by omega)
    simp only [d, ite_eq_left hk] at this
    exact this
  · have hdl : d (ℓ - 1 + 1) = R.post (ℓ * φ + (ℓ - 1)) := by
      simp only [d, ite_eq_right (show ¬ (ℓ - 1 + 1 < ℓ) by omega)]
    rw [show ℓ - 1 + 1 = ℓ by omega] at hlt hle hdl
    by_cases hpos : 0 < badness m ℓ (R.cfg (ℓ * φ)) i
    · have := hlt (by unfold badness at hpos; exact hpos)
      rw [hdl] at this; omega
    · have := hle ℓ le_rfl
      rw [hdl] at this; omega

/-- The badness invariant of the proof of Theorem 4.1: at the beginning of phase `φ` the badness
of `i` is at most `ξ + 1`, where `ξ` is the excess of the batched adversary after batch `φ`. -/
theorem badness_phase_start (hR : sched = fixedSched) (hℓ : 1 ≤ ℓ) {ρ : ℝ} (hρ : ρ ≤ 1) (i φ : ℕ) :
    (badness m ℓ (R.cfg (ℓ * φ)) i : ℝ) ≤ excess b (m ^ ℓ) ρ i (φ + 1) + 1 := by
  induction φ with
  | zero =>
    rw [mul_zero, R.init]
    have h1 := badness_addBatch_le (m := m) (ℓ := ℓ) b 0 (fun _ _ => 0) i
    have h0 : badness m ℓ (fun _ _ => 0) i = 0 := by simp [badness, Bad, pb]
    rw [h0, zero_add] at h1
    have h2 := cross_succ_le b (m ^ ℓ) ρ i 0
    have h3 := excess_nonneg b (m ^ ℓ) ρ i 0
    have : (badness m ℓ (addBatch m ℓ b 0 fun _ _ => 0) i : ℝ) ≤ cross b (m ^ ℓ) i 0 1 := by
      exact_mod_cast h1
    linarith
  | succ φ ih =>
    rw [R.cfg_phase_start hℓ φ]
    have h1 := badness_addBatch_le (m := m) (ℓ := ℓ) b (φ + 1) (R.post (ℓ * φ + (ℓ - 1))) i
    have h2 := cross_succ_le b (m ^ ℓ) ρ i (φ + 1)
    have h3 := (R.phase_facts hR hℓ φ i).2
    have h4 := excess_nonneg b (m ^ ℓ) ρ i (φ + 1)
    have h5 : (badness m ℓ (R.post (ℓ * φ + (ℓ - 1))) i : ℝ) ≤ excess b (m ^ ℓ) ρ i (φ + 1) := by
      rcases Nat.eq_zero_or_pos (badness m ℓ (R.cfg (ℓ * φ)) i) with h0 | h0
      · rw [h0] at h3
        have : badness m ℓ (R.post (ℓ * φ + (ℓ - 1))) i = 0 := by omega
        rw [this]; simpa using h4
      · have : (badness m ℓ (R.post (ℓ * φ + (ℓ - 1))) i : ℝ) ≤
            (badness m ℓ (R.cfg (ℓ * φ)) i : ℝ) - 1 := by
          have : badness m ℓ (R.post (ℓ * φ + (ℓ - 1))) i + 1 ≤ badness m ℓ (R.cfg (ℓ * φ)) i := by
            omega
          have : (badness m ℓ (R.post (ℓ * φ + (ℓ - 1))) i : ℝ) + 1 ≤
              badness m ℓ (R.cfg (ℓ * φ)) i := by exact_mod_cast this
          linarith
        linarith
    have : (badness m ℓ (addBatch m ℓ b (φ + 1) (R.post (ℓ * φ + (ℓ - 1)))) i : ℝ) ≤
        badness m ℓ (R.post (ℓ * φ + (ℓ - 1))) i + cross b (m ^ ℓ) i (φ + 1) (φ + 1 + 1) := by
      exact_mod_cast h1
    linarith

/-- Every badness stays at most `σ + 1` (proof of Theorem 4.1). -/
theorem badness_le (hR : sched = fixedSched) (hℓ : 1 ≤ ℓ) {ρ σ : ℝ}
    (hb : IsBounded b (m ^ ℓ) ρ σ) (hρ : ρ ≤ 1) (r : ℕ) {i : ℕ} (hi : i < m ^ ℓ) :
    (badness m ℓ (R.cfg r) i : ℝ) ≤ σ + 1 := by
  have hr : r = ℓ * (r / ℓ) + r % ℓ := (Nat.div_add_mod r ℓ).symm
  have h1 := (R.phase_facts hR hℓ (r / ℓ) i).1 (r % ℓ) (Nat.mod_lt _ (by omega))
  rw [← hr] at h1
  have h2 := R.badness_phase_start hR hℓ hρ i (r / ℓ)
  have h3 := excess_le hb hi (r / ℓ + 1)
  have : (badness m ℓ (R.cfg r) i : ℝ) ≤ badness m ℓ (R.cfg (ℓ * (r / ℓ))) i := by exact_mod_cast h1
  linarith

/-- Buffer bound: occupancy at most (pseudo-buffers in use) `+ σ + 1`. -/
theorem occ_le_keys (hR : sched = fixedSched) (hℓ : 1 ≤ ℓ) {ρ σ : ℝ}
    (hb : IsBounded b (m ^ ℓ) ρ σ) (hρ : ρ ≤ 1) (r : ℕ) {i : ℕ} (hi : i < m ^ ℓ) :
    (occ m ℓ (R.cfg r) i : ℝ) ≤ (keysAt m ℓ (R.cfg r) i).card + σ + 1 := by
  have h1 := occ_le (R.cfg r) (R.wf r) i
  have h2 := R.badness_le hR hℓ hb hρ r hi
  have : (occ m ℓ (R.cfg r) i : ℝ) ≤ (keysAt m ℓ (R.cfg r) i).card + badness m ℓ (R.cfg r) i := by
    exact_mod_cast h1
  linarith

end Run

/-- **Theorem 4.1** of [MPR19] (with the schedule repaired to decreasing levels within a phase):
for every positive integer `ℓ` and every `(ρ, σ)`-bounded adversary `A` with `ρ ℓ ≤ 1`, every
execution of HPTS on the path with `n = m^ℓ` nodes uses at most `ℓ n^{1/ℓ} + σ + 1 = ℓ m + σ + 1`
buffer space at every node in every round. The adversary's packets are accepted phase by phase
(the `ℓ`-reduction `reduce A ℓ`, Algorithm 3 lines 3–5); packets injected during the current phase
and not yet accepted are not counted (as in the paper). -/
theorem theorem_4_1 (hℓ : 1 ≤ ℓ) {A : ℕ → ℕ → ℕ → ℕ} {ρ σ : ℝ}
    (hA : IsBounded A (m ^ ℓ) ρ σ) (hρ0 : 0 ≤ ρ) (hρℓ : ρ * ℓ ≤ 1)
    (R : Run m ℓ fixedSched (reduce A ℓ)) (r : ℕ) {i : ℕ} (hi : i < m ^ ℓ) :
    (occ m ℓ (R.cfg r) i : ℝ) ≤ ℓ * m + σ + 1 := by
  have hb := reduce_isBounded hA hρ0 ℓ
  have h := R.occ_le_keys rfl hℓ hb (by linarith) r hi
  have hk : ((keysAt m ℓ (R.cfg r) i).card : ℝ) ≤ ℓ * m := by
    exact_mod_cast card_keysAt_le (R.cfg r) i
  linarith

end Podc.SmallBuffersAQT
