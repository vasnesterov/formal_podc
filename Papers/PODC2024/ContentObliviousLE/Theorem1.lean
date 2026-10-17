import Papers.PODC2024.ContentObliviousLE.Alg2
import Cslib.Computability.Distributed.ContentOblivious.Mirror

/-!
# Theorem 1: Algorithm 2 is a quiescently terminating leader election with `n(2·IDmax+1)` pulses

Frei, Gelles, Ghazy, Nolin, *Content-Oblivious Leader Election on Rings*, PODC 2024 (brief
announcement), Theorem 1; full version arXiv 2405.03646, Theorem 1 / Appendix A.

Setting: oriented ring `ZMod n` (`n ≥ 1`, including the self-loop `n = 1` and the double link
`n = 2`), distinct positive IDs, adversarial asynchronous scheduler (`Cslib.ContentOblivious.Step`).
`ℓ` is the node of maximal ID.
-/

namespace Podc.ContentOblivious.Alg2

open Cslib.ContentOblivious Finset

variable {n : ℕ} [NeZero n] {id : ZMod n → ℕ} {ℓ : ZMod n}

/-- Before the termination event the execution cannot stop. -/
lemma Inv1.not_final (hid : Function.Injective id) (hpos : ∀ v, 0 < id v) (hℓ : ∀ v, id v ≤ id ℓ)
    {c : Cfg n} (hr : Reach (oriented n) alg id c) (h : Inv1 id (id ℓ) c) :
    ¬ Final (oriented n) alg c := by
  intro hfin
  have hC := h.counters hr
  -- CW-quiescence
  have hcw : ∀ v, c.recvd (v + 1, false) = c.sent (v, true) := by
    intro v
    by_contra hne
    have hlt : c.recvd (v + 1, false) < c.sent (v, true) := lt_of_le_of_ne ((edges hr).1 v) hne
    obtain ⟨-, hst, -⟩ := h (v + 1)
    apply hfin (v + 1) false
    refine ⟨hst.2.2.2.2.2.2, ?_, by simpa using hlt⟩
    simp [alg, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2]
  have hgood := hC.profile_cw.good_of_tight hcw
  have hmax := hC.profile_cw.eq_max_of_good (fun v => hC.ecw v) hgood
    (fun v => (hC.node v).2.2.2.1) (ℓ := ℓ) rfl
  -- CCW-quiescence
  have hccw : ∀ v, c.recvd (v, true) = c.sent (v + 1, false) := by
    intro v
    by_contra hne
    have hlt : c.recvd (v, true) < c.sent (v + 1, false) := lt_of_le_of_ne ((edges hr).2 v) hne
    obtain ⟨-, hst, -⟩ := h v
    apply hfin v true
    refine ⟨hst.2.2.2.2.2.2, ?_, by simpa using hlt⟩
    simp [alg, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2, hst.1, hst.2.1, hgood v]
  -- then the event `ρcw = ID = ρccw` has happened at `ℓ`, contradicting `Inv1`
  have hprof : Ring.Profile (fun x => c.recvd (-x, true)) (fun x => c.sent (-x, false))
      (fun x => id (-x)) := by
    intro x; simp only; rw [(hC.node (-x)).2.1, if_pos (hgood _)]
  have htight : ∀ x, c.recvd (-(x + 1), true) = c.sent (-x, false) := by
    intro x; rw [hccw]; congr 2; ring
  have hg' := hprof.good_of_tight htight
  have h1 := hg' (-ℓ); simp only [neg_neg] at h1
  have h2 := (hC.node ℓ).2.2.2.2
  exact (h ℓ).2.2 ⟨(hmax ℓ).1, le_antisymm h2 h1⟩

/-- After the termination event: if all CCW links are tight, every node has received `IDmax + 1`
CCW pulses. -/
lemma Inv2.all_of_tight {c : Cfg n} (h : Inv2 id ℓ c)
    (ht : ∀ v, c.recvd (v, true) = c.sent (v + 1, false)) : ∀ v, c.recvd (v, true) = id ℓ + 1 := by
  obtain ⟨-, hB, hC, -⟩ := h
  refine ZMod.chain_ccw_all _ (ℓ - 1) (fun v _ hv => ?_) (by rw [ht, sub_add_cancel, hC])
  rw [ht]
  by_cases hv' : v + 1 = ℓ
  · rw [hv', hC]
  · rw [(hB _ hv').1, hv]

lemma Inv2.sent_le {c : Cfg n} (h : Inv2 id ℓ c) (v : ZMod n) : c.sent (v, false) ≤ id ℓ + 1 := by
  obtain ⟨-, hB, hC, -⟩ := h
  by_cases hv : v = ℓ
  · subst hv; omega
  · obtain ⟨b1, -, b3⟩ := hB v hv
    rcases b3 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

lemma Inv2.done_iff {c : Cfg n} (h : Inv2 id ℓ c) (v : ZMod n) :
    (c.st v).done = true ↔ c.recvd (v, true) = id ℓ + 1 := by
  obtain ⟨-, hB, -, hD⟩ := h
  by_cases hv : v = ℓ
  · subst hv
    rcases hD with ⟨d1, -, d3⟩ | ⟨d1, -, d3⟩ <;> simp [d1, d3]
  · rcases (hB v hv).2.2 with ⟨d1, d3⟩ | ⟨d1, d3⟩ <;> simp [d1, d3]

/-- In a final configuration (after the termination event), all CCW links are tight. -/
lemma Inv2.tight_of_final (hℓ : ∀ v, id v ≤ id ℓ) {c : Cfg n} (hr : Reach (oriented n) alg id c)
    (h : Inv2 id ℓ c) (hfin : Final (oriented n) alg c) : ∀ v, c.recvd (v, true) = c.sent (v + 1, false) := by
  intro v
  by_contra hne
  have hlt : c.recvd (v, true) < c.sent (v + 1, false) := lt_of_le_of_ne ((edges hr).2 v) hne
  have hd : (c.st v).done = false := by
    by_contra hd
    simp only [Bool.not_eq_false] at hd
    have := (h.done_iff v).1 hd
    have := h.sent_le (v + 1)
    omega
  apply hfin v true
  obtain ⟨a1, a2, -, a4, -⟩ := h.1 v
  refine ⟨hd, ?_, by simpa using hlt⟩
  simp [alg, hd, a1, a2, a4, hℓ v]

/-- When `ℓ` has terminated, all CCW links are tight. -/
lemma Inv2.tight_of_done {c : Cfg n} (hr : Reach (oriented n) alg id c) (h : Inv2 id ℓ c)
    (hd : (c.st ℓ).done = true) : ∀ v, c.recvd (v, true) = c.sent (v + 1, false) := by
  have hl := (h.done_iff ℓ).1 hd
  have heq : ∀ v, c.sent (v, false) = c.recvd (v, true) := by
    intro v
    by_cases hv : v = ℓ
    · subst hv; rw [h.2.2.1, hl]
    · exact (h.2.1 v hv).1
  have hle : ∀ v ∈ (univ : Finset (ZMod n)), c.recvd (v, true) ≤ c.sent (v + 1, false) :=
    fun v _ => (edges hr).2 v
  have hsum : ∑ v, c.recvd (v, true) = ∑ v, c.sent (v + 1, false) := by
    rw [Fintype.sum_add_right_eq_self (fun v => c.sent (v, false)) 1]
    exact sum_congr rfl fun v _ => (heq v).symm
  exact fun v => (sum_eq_sum_iff_of_le hle).1 hsum v (mem_univ v)

lemma Inv2.quiescent_of_tight {c : Cfg n} (h : Inv2 id ℓ c)
    (ht : ∀ v, c.recvd (v, true) = c.sent (v + 1, false)) : Quiescent (oriented n) alg c := by
  rintro ⟨v, _ | _⟩
  · simp only [oriented_peer_false]; rw [(h.1 v).2.2.2.1, (h.1 (v - 1)).2.2.2.2.1]
  · simp only [oriented_peer_true]; exact ht v

variable (hid : Function.Injective id) (hpos : ∀ v, 0 < id v) (hℓ : ∀ v, id v ≤ id ℓ)
include hid hpos hℓ

/-- **Theorem 1 (correctness at termination).** Every maximal execution ends in a configuration
where all nodes have terminated, exactly the node `ℓ` of maximal ID outputs `Leader`, no pulse is in
transit (quiescence), and exactly `n(2·IDmax + 1)` pulses have been sent. -/
theorem final_spec {c : Cfg n} (hr : Reach (oriented n) alg id c) (hfin : Final (oriented n) alg c) :
    Quiescent (oriented n) alg c ∧ (∀ v, (c.st v).done = true) ∧
      (∀ v, (c.st v).leader = true ↔ v = ℓ) ∧ totalSent c = n * (2 * id ℓ + 1) := by
  rcases reach_inv hid hpos hℓ hr with h1 | h2
  · exact absurd hfin (h1.not_final hid hpos hℓ hr)
  have ht := h2.tight_of_final hℓ hr hfin
  have hall := h2.all_of_tight ht
  refine ⟨h2.quiescent_of_tight ht, fun v => (h2.done_iff v).2 (hall v), fun v => ?_, ?_⟩
  · rw [(h2.1 v).2.2.2.2.2.2, decide_eq_true_iff]
    exact ⟨fun h => hid h.symm, fun h => h ▸ rfl⟩
  · rw [totalSent, sum_ports]
    have : ∀ v, c.sent (v, false) + c.sent (v, true) = 2 * id ℓ + 1 := by
      intro v
      have := ht (v - 1); rw [sub_add_cancel] at this
      rw [(h2.1 v).2.2.2.2.1, ← this, hall]; ring
    simp [this, ZMod.card]

/-- **Theorem 1 (message complexity).** No execution ever sends more than `n(2·IDmax + 1)` pulses. -/
theorem totalSent_le {c : Cfg n} (hr : Reach (oriented n) alg id c) :
    totalSent c ≤ n * (2 * id ℓ + 1) := by
  rw [totalSent, sum_ports]
  have : ∀ v, c.sent (v, false) + c.sent (v, true) ≤ 2 * id ℓ + 1 := by
    intro v
    rcases reach_inv hid hpos hℓ hr with h1 | h2
    · have := ((h1 v).1.sent_le (hℓ v)); omega
    · have := h2.sent_le v; have := (h2.1 v).2.2.2.2.1; omega
  calc ∑ v, (c.sent (v, false) + c.sent (v, true)) ≤ ∑ _v : ZMod n, (2 * id ℓ + 1) :=
        sum_le_sum fun v _ => this v
    _ = n * (2 * id ℓ + 1) := by simp [ZMod.card]

/-- **Theorem 1 (termination).** There is no infinite execution. -/
theorem no_infinite_execution :
    ¬ ∃ f : ℕ → Cfg n, f 0 = initCfg alg id ∧ ∀ k, Step (oriented n) alg (f k) (f (k + 1)) :=
  Cslib.ContentOblivious.no_infinite_execution (B := n * (2 * id ℓ + 1))
    fun _ hr => totalSent_le hid hpos hℓ hr

/-- Every execution can be completed (non-vacuity of `final_spec`). -/
theorem exists_final {c : Cfg n} (hr : Reach (oriented n) alg id c) :
    ∃ c', Relation.ReflTransGen (Step (oriented n) alg) c c' ∧ Final (oriented n) alg c' :=
  Cslib.ContentOblivious.exists_final (B := n * (2 * id ℓ + 1))
    (fun _ hr => totalSent_le hid hpos hℓ hr) hr

/-- **Quiescent termination** (Section 1.1): at any time, no pulse is in transit towards a
terminated node (hence a terminated node never receives a pulse), and its output is final and
correct. -/
theorem terminated_spec {c : Cfg n} (hr : Reach (oriented n) alg id c) {v : ZMod n}
    (hv : (c.st v).done = true) :
    (∀ k, c.recvd (v, k) = c.sent ((oriented n).peer (v, k))) ∧ ((c.st v).leader = true ↔ v = ℓ) := by
  rcases reach_inv hid hpos hℓ hr with h1 | h2
  · rw [(h1 v).2.1.2.2.2.2.2.2] at hv; cases hv
  refine ⟨fun k => ?_, ?_⟩
  · cases k
    · simp only [oriented_peer_false]; rw [(h2.1 v).2.2.2.1, (h2.1 (v - 1)).2.2.2.2.1]
    · simp only [oriented_peer_true]
      have := (h2.done_iff v).1 hv
      have := h2.sent_le (v + 1)
      have := (edges hr).2 v
      omega
  · rw [(h2.1 v).2.2.2.2.2.2, decide_eq_true_iff]
    exact ⟨fun h => hid h.symm, fun h => h ▸ rfl⟩

/-- **The leader terminates last** (Section 1.1): once `ℓ` has terminated, every node has
terminated and the network is quiescent. -/
theorem leader_last {c : Cfg n} (hr : Reach (oriented n) alg id c) (hd : (c.st ℓ).done = true) :
    (∀ v, (c.st v).done = true) ∧ Quiescent (oriented n) alg c := by
  rcases reach_inv hid hpos hℓ hr with h1 | h2
  · rw [(h1 ℓ).2.1.2.2.2.2.2.2] at hd; cases hd
  have ht := h2.tight_of_done hr hd
  exact ⟨fun v => (h2.done_iff v).2 (h2.all_of_tight ht v), h2.quiescent_of_tight ht⟩

/-- Terminated nodes stay terminated (termination is irrevocable). -/
theorem done_stable {c c' : Cfg n} (hr : Reach (oriented n) alg id c)
    (hs : Step (oriented n) alg c c') {v : ZMod n} (hv : (c.st v).done = true) :
    (c'.st v).done = true := by
  obtain ⟨u, j, hen⟩ := hs
  by_cases hu : v = u
  · subst hu; exact absurd hen.1 (by simp [alg, hv])
  · rw [d_st_ne _ _ _ _ hu]; exact hv

/-- **Theorem 1** of Frei–Gelles–Ghazy–Nolin (PODC 2024): Algorithm 2 is a quiescently terminating
content-oblivious leader election algorithm on oriented rings with unique (positive) IDs, of message
complexity exactly `n(2·IDmax + 1)`. -/
theorem theorem_1 :
    -- every execution is finite
    (¬ ∃ f : ℕ → Cfg n, f 0 = initCfg alg id ∧ ∀ k, Step (oriented n) alg (f k) (f (k + 1))) ∧
    -- at the end: all terminated, unique leader `ℓ`, quiescence, exactly `n(2·IDmax+1)` pulses
    (∀ c, Reach (oriented n) alg id c → Final (oriented n) alg c →
      Quiescent (oriented n) alg c ∧ (∀ v, (c.st v).done = true) ∧
        (∀ v, (c.st v).leader = true ↔ v = ℓ) ∧ totalSent c = n * (2 * id ℓ + 1)) ∧
    -- quiescent termination: nothing is ever in transit towards a terminated node
    (∀ c, Reach (oriented n) alg id c → ∀ v, (c.st v).done = true →
      ∀ k, c.recvd (v, k) = c.sent ((oriented n).peer (v, k))) ∧
    -- the leader is the last node to terminate
    (∀ c, Reach (oriented n) alg id c → (c.st ℓ).done = true →
      (∀ v, (c.st v).done = true) ∧ Quiescent (oriented n) alg c) ∧
    -- worst-case message complexity
    (∀ c, Reach (oriented n) alg id c → totalSent c ≤ n * (2 * id ℓ + 1)) :=
  ⟨no_infinite_execution hid hpos hℓ, fun _ hr hf => final_spec hid hpos hℓ hr hf,
    fun _ hr _ hv => (terminated_spec hid hpos hℓ hr hv).1, fun _ hr hd => leader_last hid hpos hℓ hr hd,
    fun _ hr => totalSent_le hid hpos hℓ hr⟩

end Podc.ContentOblivious.Alg2
