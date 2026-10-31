import Papers.PODC2020.ConsecutiveBallotsPaxos.Invariants

/-!
# Safety of Paxos with Consecutive Quorums (Section 4.1)

Main results, for every reachable state of Classic Paxos (`cp = false`) and of Consecutive Paxos
(`cp = true`, Consecutive Proposals enabled), over any intersecting quorum system:

* `cq_propose_eq` (the core, a strengthened Lemma 4.3'): if the accepts of a Consecutive Quorum for
  `v` cover the ballots `[lo, hi]`, then every proposal in a ballot `≥ lo` has value `v`;
* `theorem_3_2` (Chosen Invariant) and `theorem_3_1` (Safety) with CQ Chosen/CQ Learned;
* Lemmas 4.1, 4.2, 4.3 (literal Definition 6), Lemma 4.1' (literal), and Lemmas 4.2', 4.3' for the
  intended reading of Definition 6 (`CQChosen'`); the literal Lemmas 4.2', 4.3' are false, see
  `Counterexample.lean`;
* Section 4.2: classic chosen/learned implies CQ chosen/learned.
-/

namespace Podc.ConsecutiveBallotsPaxos

open Msg

variable {A V : Type*} [DecidableEq A] {QS : QuorumSystem A} {cp : Bool} {s : State A V}

omit [DecidableEq A] in
lemma QuorumSystem.nonempty (QS : QuorumSystem A) {Q : Finset A} (hQ : QS.IsQuorum Q) :
    ∃ a, a ∈ Q := by
  obtain ⟨a, ha, -⟩ := QS.inter Q Q hQ hQ
  exact ⟨a, ha⟩

/-- Definition 8 of [paper] (Accept Implies Propose), an invariant of the protocol. -/
theorem accept_implies_propose (hs : Reachable QS cp s) {a : A} {i : ℕ} {v : V}
    (h : accept a i v ∈ s.msgs) : propose i v ∈ s.msgs :=
  hs.inv.acc_prop a i v h

/-- Definition 9 of [paper] (Chosen Implies Propose), for CQ Chosen. -/
theorem chosen_implies_propose (hs : Reachable QS cp s) {i : ℕ} {v : V}
    (h : CQChosen QS s.msgs i v) : propose i v ∈ s.msgs := by
  obtain ⟨Q, -, a, -, ha⟩ := h
  exact accept_implies_propose hs ha

omit [DecidableEq A] in
/-- The core argument (Lemma 4.3' in its strong form): let every member `a` of a quorum `Q` have
accepted `v` in ballot `x a ∈ [lo, hi]`, with every ballot of `[lo, hi]` used by some member. Then
every proposal in a ballot `j ≥ lo` has value `v`. Induction on `j`: ballots in `[lo, hi]` carry
`v` by uniqueness of the proposal per ballot; a Normal proposal in `j > hi` sees, through the
member of `Q` in its promise quorum, a reported ballot `≥ lo`; a Consecutive proposal in
`j = c + 1 > hi` copies the proposal of ballot `c ≥ lo`. -/
theorem propose_eq_of_interval (hI : Inv QS cp s) {Q : Finset A} (hQ : QS.IsQuorum Q) {v : V}
    {x : A → ℕ} (hx : ∀ a ∈ Q, accept a (x a) v ∈ s.msgs) {lo hi : ℕ}
    (hbnd : ∀ a ∈ Q, lo ≤ x a ∧ x a ≤ hi) (hcov : ∀ k, lo ≤ k → k ≤ hi → ∃ a ∈ Q, x a = k) :
    ∀ j, lo ≤ j → ∀ w, propose j w ∈ s.msgs → w = v := by
  obtain ⟨a₀, ha₀⟩ := QS.nonempty hQ
  have hlohi : lo ≤ hi := le_trans (hbnd a₀ ha₀).1 (hbnd a₀ ha₀).2
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj w hw
  by_cases hjhi : j ≤ hi
  · obtain ⟨a, ha, rfl⟩ := hcov j hj hjhi
    exact hI.prop_unique _ _ _ hw (hI.acc_prop _ _ _ (hx a ha))
  push Not at hjhi
  rcases hI.prop_ok j w hw with ⟨Qj, hQj, hall, hcase⟩ | ⟨-, c, rfl, a, ha⟩
  · -- Normal proposal: the member `α ∈ Q ∩ Qj` reported a ballot `≥ x α ≥ lo`
    obtain ⟨α, hαQ, hαQj⟩ := QS.inter Q Qj hQ hQj
    obtain ⟨r, hr⟩ := hall α hαQj
    have hxα := hbnd α hαQ
    cases r with
    | none =>
      have := hI.prom_none α j (x α) v hr (hx α hαQ)
      omega
    | some p =>
      obtain ⟨k, u⟩ := p
      have hk := (hI.prom_some α j k u hr).2.2 (x α) v (hx α hαQ) (by omega)
      rcases hcase with hnone | ⟨a₁, ha₁, k₁, hk₁, hmax⟩
      · exact absurd hr (hnone α hαQj k u)
      · have hkk₁ := hmax α hαQj k u hr
        obtain ⟨hk₁j, hacc₁, -⟩ := hI.prom_some a₁ j k₁ w hk₁
        exact ih k₁ hk₁j (by omega) w (hI.acc_prop _ _ _ hacc₁)
  · -- Consecutive proposal in ballot `c + 1`: copies ballot `c`
    have hacc : accept a c w ∈ s.msgs := by
      rcases ha with ha | ha
      · exact (hI.prom_some a (c + 1) c w ha).2.1
      · exact ha
    exact ih c (by omega) (by omega) w (hI.acc_prop _ _ _ hacc)

omit [DecidableEq A] in
/-- A Consecutive Quorum covers an interval of ballots. -/
lemma CQ.interval {M : Set (Msg A V)} {Q : Finset A} {v : V} (h : CQ QS M Q v) :
    ∃ x : A → ℕ, ∃ lo hi : ℕ, (∀ a ∈ Q, accept a (x a) v ∈ M) ∧
      (∀ a ∈ Q, lo ≤ x a ∧ x a ≤ hi) ∧ (∀ k, lo ≤ k → k ≤ hi → ∃ a ∈ Q, x a = k) := by
  classical
  obtain ⟨hQ, x, hx, hcons⟩ := h
  obtain ⟨a₀, ha₀⟩ := QS.nonempty hQ
  have hne : (Q.image x).Nonempty := ⟨x a₀, Finset.mem_image_of_mem x ha₀⟩
  have hS : x '' (Q : Set A) = ↑(Q.image x) := (Finset.coe_image).symm
  refine ⟨x, (Q.image x).min' hne, (Q.image x).max' hne, hx,
    fun a ha => ⟨Finset.min'_le _ _ (Finset.mem_image_of_mem x ha),
      Finset.le_max' _ _ (Finset.mem_image_of_mem x ha)⟩, fun k h1 h2 => ?_⟩
  have hmem : k ∈ x '' (Q : Set A) :=
    hcons.mem_of_le_of_le (Set.toFinite _) (by rw [hS]; exact Finset.min'_mem _ _)
      (by rw [hS]; exact Finset.max'_mem _ _) h1 h2
  obtain ⟨a, ha, rfl⟩ := hmem
  exact ⟨a, ha, rfl⟩

/-- Strong form of Lemma 4.3': if the accepts `accept(x a, v)` (`a ∈ Q`) form a Consecutive
Quorum, every proposal in a ballot `j ≥ x a` (for any member `a`) has value `v`. -/
theorem cq_propose_eq (hs : Reachable QS cp s) {Q : Finset A} {v : V} {x : A → ℕ}
    (hx : ∀ a ∈ Q, accept a (x a) v ∈ s.msgs) (hQ : QS.IsQuorum Q)
    (hcons : ConsecutiveSet (x '' Q)) {a : A} (ha : a ∈ Q) {j : ℕ} (hj : x a ≤ j) {w : V}
    (hw : propose j w ∈ s.msgs) : w = v := by
  classical
  have hne : (Q.image x).Nonempty := ⟨x a, Finset.mem_image_of_mem x ha⟩
  have hS : x '' (Q : Set A) = ↑(Q.image x) := (Finset.coe_image).symm
  refine propose_eq_of_interval hs.inv hQ hx (lo := (Q.image x).min' hne)
    (hi := (Q.image x).max' hne)
    (fun b hb => ⟨Finset.min'_le _ _ (Finset.mem_image_of_mem x hb),
      Finset.le_max' _ _ (Finset.mem_image_of_mem x hb)⟩) (fun k h1 h2 => ?_) j
    (le_trans (Finset.min'_le _ _ (Finset.mem_image_of_mem x ha)) hj) w hw
  have hmem : k ∈ x '' (Q : Set A) :=
    hcons.mem_of_le_of_le (Set.toFinite _) (by rw [hS]; exact Finset.min'_mem _ _)
      (by rw [hS]; exact Finset.max'_mem _ _) h1 h2
  obtain ⟨b, hb, rfl⟩ := hmem
  exact ⟨b, hb, rfl⟩

/-- Any two Consecutive Quorums support the same value. -/
theorem cq_unique (hs : Reachable QS cp s) {Q₁ Q₂ : Finset A} {v w : V}
    (h₁ : CQ QS s.msgs Q₁ v) (h₂ : CQ QS s.msgs Q₂ w) : v = w := by
  obtain ⟨x₁, lo₁, hi₁, hx₁, hb₁, hc₁⟩ := h₁.interval
  obtain ⟨x₂, lo₂, hi₂, hx₂, hb₂, hc₂⟩ := h₂.interval
  obtain ⟨a₁, ha₁⟩ := QS.nonempty h₁.1
  obtain ⟨a₂, ha₂⟩ := QS.nonempty h₂.1
  rcases le_total lo₁ lo₂ with h | h
  · obtain ⟨b, hb, hxb⟩ := hc₂ lo₂ le_rfl (le_trans (hb₂ a₂ ha₂).1 (hb₂ a₂ ha₂).2)
    have hp := hs.inv.acc_prop _ _ _ (hx₂ b hb)
    rw [hxb] at hp
    exact (propose_eq_of_interval hs.inv h₁.1 hx₁ hb₁ hc₁ lo₂ h w hp).symm
  · obtain ⟨b, hb, hxb⟩ := hc₁ lo₁ le_rfl (le_trans (hb₁ a₁ ha₁).1 (hb₁ a₁ ha₁).2)
    have hp := hs.inv.acc_prop _ _ _ (hx₁ b hb)
    rw [hxb] at hp
    exact propose_eq_of_interval hs.inv h₂.1 hx₂ hb₂ hc₂ lo₁ h v hp

/-- **Theorem 3.2 of [paper] (Chosen Invariant)** with CQ Chosen (Definition 6, literal): no two
different values can be chosen, in Classic Paxos (`cp = false`) and in Consecutive Paxos
(`cp = true`). -/
theorem theorem_3_2 (hs : Reachable QS cp s) {i j : ℕ} {v w : V}
    (hv : CQChosen QS s.msgs i v) (hw : CQChosen QS s.msgs j w) : v = w :=
  cq_unique hs hv.choose_spec.1 hw.choose_spec.1

omit [DecidableEq A] in
lemma CQ.mono {M M' : Set (Msg A V)} (hM : M ⊆ M') {Q : Finset A} {v : V}
    (h : CQ QS M Q v) : CQ QS M' Q v := by
  obtain ⟨hQ, x, hx, hc⟩ := h
  exact ⟨hQ, x, fun a ha => hM (hx a ha), hc⟩

omit [DecidableEq A] in
lemma CQChosen.mono {M M' : Set (Msg A V)} (hM : M ⊆ M') {i : ℕ} {v : V}
    (h : CQChosen QS M i v) : CQChosen QS M' i v := by
  obtain ⟨Q, hQ, a, ha, hacc⟩ := h
  exact ⟨Q, hQ.mono hM, a, ha, hM hacc⟩

/-- **Theorem 3.1 of [paper] (Safety)** with CQ learning: two learners, having received the sets
of messages `L₁, L₂` (subsets of the sent messages; the network is asynchronous and may lose,
delay or reorder messages), never learn different values. -/
theorem theorem_3_1 (hs : Reachable QS cp s) {L₁ L₂ : Set (Msg A V)} (h₁ : L₁ ⊆ s.msgs)
    (h₂ : L₂ ⊆ s.msgs) {i j : ℕ} {v w : V}
    (hv : CQLearned QS L₁ i v) (hw : CQLearned QS L₂ j w) : v = w :=
  theorem_3_2 hs (CQChosen.mono h₁ hv) (CQChosen.mono h₂ hw)

/-- Theorem 3.1 across time: learning at a state `s` and at a later state `s'` of the same
execution. -/
theorem theorem_3_1_execution {s' : State A V} (hs : Reachable QS cp s)
    (hss' : Relation.ReflTransGen (Step QS cp) s s') {L₁ L₂ : Set (Msg A V)} (h₁ : L₁ ⊆ s.msgs)
    (h₂ : L₂ ⊆ s'.msgs) {i j : ℕ} {v w : V}
    (hv : CQLearned QS L₁ i v) (hw : CQLearned QS L₂ j w) : v = w :=
  theorem_3_1 (hs.trans hss') (h₁.trans (msgs_subset_of_reflTransGen hss')) h₂ hv hw

/-- Lemma 4.1 of [paper] (Equal CQ). -/
theorem lemma_4_1 (hs : Reachable QS cp s) {i : ℕ} {v w : V}
    (hv : CQChosen QS s.msgs i v) (hw : CQChosen QS s.msgs i w) : w = v :=
  (theorem_3_2 hs hv hw).symm

/-- Lemma 4.2 of [paper] (Less Than CQ). -/
theorem lemma_4_2 (hs : Reachable QS cp s) {i j : ℕ} (_ : j < i) {v w : V}
    (hv : CQChosen QS s.msgs i v) (hw : CQChosen QS s.msgs j w) : w = v :=
  (theorem_3_2 hs hv hw).symm

/-- Lemma 4.3 of [paper] (Greater Than CQ). -/
theorem lemma_4_3 (hs : Reachable QS cp s) {i j : ℕ} (_ : i < j) {v w : V}
    (hv : CQChosen QS s.msgs i v) (hw : CQChosen QS s.msgs j w) : w = v :=
  (theorem_3_2 hs hv hw).symm

/-- Lemma 4.1' of [paper]: if an acceptor accepted `v` in ballot `i`, no other value is chosen
in ballot `i` (literal Definition 6). -/
theorem lemma_4_1' (hs : Reachable QS cp s) {a : A} {i : ℕ} {v w : V}
    (ha : accept a i v ∈ s.msgs) (hw : CQChosen QS s.msgs i w) : w = v :=
  hs.inv.prop_unique i w v (chosen_implies_propose hs hw) (accept_implies_propose hs ha)

omit [DecidableEq A] in
/-- The intended reading of Definition 6 implies the literal one. -/
lemma CQChosen'.cqChosen {M : Set (Msg A V)} {i : ℕ} {v : V} (h : CQChosen' QS M i v) :
    CQChosen QS M i v := by
  obtain ⟨Q, hQ, x, hx, hc, a, ha, rfl⟩ := h
  exact ⟨Q, ⟨hQ, x, hx, hc⟩, a, ha, hx a ha⟩

/-- Lemma 4.3' of [paper], for the intended reading `CQChosen'` of Definition 6: if `v` is chosen
in ballot `i`, no value `w ≠ v` is proposed in any ballot `j > i` (indeed in any `j ≥ i`). With
the literal Definition 6 this is false: `lemma_4_3'_literal_false`. -/
theorem lemma_4_3' (hs : Reachable QS cp s) {i : ℕ} {v : V} (hv : CQChosen' QS s.msgs i v)
    {j : ℕ} (hij : i < j) {w : V} (hw : propose j w ∈ s.msgs) : w = v := by
  obtain ⟨Q, hQ, x, hx, hc, a, ha, rfl⟩ := hv
  exact cq_propose_eq hs hx hQ hc ha hij.le hw

/-- Lemma 4.2' of [paper], for the intended reading `CQChosen'` of Definition 6: if an acceptor
accepted `v` in ballot `i`, no value `w ≠ v` is chosen in a ballot `j < i`. With the literal
Definition 6 this is false: `lemma_4_2'_literal_false`. -/
theorem lemma_4_2' (hs : Reachable QS cp s) {a : A} {i : ℕ} {v : V} (ha : accept a i v ∈ s.msgs)
    {j : ℕ} (hji : j < i) {w : V} (hw : CQChosen' QS s.msgs j w) : w = v :=
  (lemma_4_3' hs hw hji (accept_implies_propose hs ha)).symm

/-! ### Section 4.2: Consecutive Quorums only weaken the learning criterion -/

omit [DecidableEq A] in
/-- A classic quorum (Definition 4) is a Consecutive Quorum: Classic Chosen implies CQ Chosen
(already in the intended sense). -/
theorem classicChosen_cqChosen' {M : Set (Msg A V)} {i : ℕ} {v : V}
    (h : ClassicChosen QS M i v) : CQChosen' QS M i v := by
  obtain ⟨Q, hQ, hacc⟩ := h
  obtain ⟨a, ha⟩ := QS.nonempty hQ
  refine ⟨Q, hQ, fun _ => i, hacc, ?_, a, ha, rfl⟩
  have : (fun _ : A => i) '' (Q : Set A) = {i} :=
    Set.Nonempty.image_const ⟨a, Finset.mem_coe.mpr ha⟩ i
  rw [this]
  exact consecutiveSet_singleton i

omit [DecidableEq A] in
/-- Section 4.2 of [paper] (liveness is preserved): whenever a learner learns `v` in Classic Paxos,
it also learns `v` with Consecutive Quorums. -/
theorem classicLearned_cqLearned {L : Set (Msg A V)} {i : ℕ} {v : V}
    (h : ClassicLearned QS L i v) : CQLearned QS L i v :=
  (classicChosen_cqChosen' h).cqChosen

/-- Corollary: Theorem 3.2 for Classic Chosen (Definition 4). -/
theorem theorem_3_2_classic (hs : Reachable QS cp s) {i j : ℕ} {v w : V}
    (hv : ClassicChosen QS s.msgs i v) (hw : ClassicChosen QS s.msgs j w) : v = w :=
  theorem_3_2 hs (classicChosen_cqChosen' hv).cqChosen (classicChosen_cqChosen' hw).cqChosen

end Podc.ConsecutiveBallotsPaxos
