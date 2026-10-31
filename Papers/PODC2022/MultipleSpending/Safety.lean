import Papers.PODC2022.MultipleSpending.Protocol

/-!
# Safety of Algorithms 1–2: Lemmas 4.3, 4.4 and the safety part of Theorem 4.8

* `lemma_4_3`: histories of correct processes are well formed.
* `lemma_4_4`: the spending number of the correct histories never exceeds the inconsistency
  number `λ(Q, F)` (assuming every process has a quorum and the run's faulty set is in `F`).
* `spend_le_byz`: the sharper bound behind it — a faulty issuer spends an input at most
  `λ(Q, {B})` times, `B` the actual faulty set; `spend_le_one_of_correct`: a correct issuer
  spends it at most once (if correct processes never issue conflicting transactions).
  Hence `spendingNumber_le_refined`: `γ ≤ max 1 λ(Q, {B})`.
* `integrity`, `accuracy`, `accused_byzantine`, `hist_mono`, `acHist_mono`: Integrity,
  Accuracy (in its sound "only if" direction) and Monotonicity of Theorem 4.8.
-/

namespace Podc.MultipleSpending

open Finset

variable {P Tx : Type*} [Fintype P] [DecidableEq P] [DecidableEq Tx]

namespace Setup

variable (A : Setup P Tx)

theorem Reachable.inv {σ : State P Tx} (h : A.Reachable σ) : A.Inv σ := by
  induction h with
  | refl => exact A.inv_init
  | tail _ hs ih => exact A.inv_step ih hs

/-- **Lemma 4.3**: the history of a correct process is well formed. -/
theorem lemma_4_3 {σ : State P Tx} (h : A.Reachable σ) {p : P} (hp : p ∉ A.B) :
    A.X.WellFormed (σ.hist p) :=
  (Reachable.inv A h).wf p hp

/-- Members of `I^r_tx` are accepted by correct processes, after echoes from a quorum. -/
theorem exists_acceptor {σ : State P Tx} (h : A.Reachable σ) {r : P} {tx t : Tx}
    (ht : t ∈ A.X.spendSet (A.Γ σ) r tx) :
    ∃ p, p ∉ A.B ∧ t ∈ σ.hist p ∧ ∃ Q ∈ A.T.Q p, ∀ q ∈ Q, (p, q, Msg.echo t) ∈ σ.rcv := by
  obtain ⟨⟨T, ⟨p, hp, rfl⟩, htT⟩, hin, -⟩ := ht
  have hne : t ≠ A.X.init := fun e => by
    rw [e, A.X.inputs_init] at hin; exact Finset.notMem_empty _ hin
  exact ⟨p, hp, htT, (Reachable.inv A h).quorum p t hp htT hne⟩

/-- **Core of Lemma 4.4.** Any finite set of transactions of `r` spending the same input `tx`,
accepted by correct processes, has at most `λ(Q', F')` elements, for any trust model with the
same quorums whose fault model contains the actual faulty set `B`. -/
theorem card_spend_le {σ : State P Tx} (h : A.Reachable σ) (T' : TrustModel P)
    (hQ : T'.Q = A.T.Q) (hB : A.B ∈ T'.F) (hq : T'.HasQuorums) {r : P} {tx : Tx}
    (D : Finset Tx) (hD : ↑D ⊆ A.X.spendSet (A.Γ σ) r tx) :
    D.card ≤ inconsistencyNumber T' := by
  classical
  have hI := Reachable.inv A h
  have hex : ∀ t : D, ∃ p, p ∉ A.B ∧ (t : Tx) ∈ σ.hist p ∧
      ∃ Q ∈ A.T.Q p, ∀ q ∈ Q, (p, q, Msg.echo (t : Tx)) ∈ σ.rcv :=
    fun t => exists_acceptor A h (hD t.2)
  choose pf hpfB hpfh Qf hQf hQfe using hex
  have hspend : ∀ t : D, tx ∈ A.X.inputs t ∧ A.X.issuer t = some r := fun t => (hD t.2).2
  have hinj : Function.Injective pf := by
    intro t t' he
    by_contra hne
    have hne' : (t : Tx) ≠ t' := fun e => hne (Subtype.ext e)
    have hwf := hI.wf _ (hpfB t)
    refine hwf.noConflict t (hpfh t) t' (he ▸ hpfh t') ⟨hne', ?_, ?_⟩
    · rw [(hspend t).2, (hspend t').2]
    · exact Finset.not_disjoint_iff.mpr ⟨tx, (hspend t).1, (hspend t').1⟩
  let C : Finset P := Finset.univ.image pf
  have hCcard : C.card = D.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  let R : P → Finset P := fun p => if hp : ∃ t, pf t = p then Qf hp.choose else ∅
  have hR : ∀ t, R (pf t) = Qf t := by
    intro t
    have hp : ∃ t', pf t' = pf t := ⟨t, rfl⟩
    simp only [R, hp, ↓reduceDIte]
    rw [hinj hp.choose_spec]
  rw [← hCcard]
  refine T'.card_le_inconsistencyNumber_of_family hq hB ?hCF R ?hR ?hdisj
  case hCF =>
    rw [Finset.disjoint_left]
    intro p hp
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hp
    exact hpfB t
  case hR =>
    intro p hp
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hp
    rw [hR, hQ]; exact hQf t
  case hdisj =>
    intro p hp p' hp' hne x hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.mp hp'
    rw [hR, hR, Finset.mem_inter] at hx
    by_contra hxB
    have h1 := hI.genuine _ _ _ hxB (hQfe t x hx.1)
    have h2 := hI.genuine _ _ _ hxB (hQfe t' x hx.2)
    have hne' : (t : Tx) ≠ t' := fun e => hne (by rw [Subtype.ext e])
    have := hI.echo_excl x t t' hxB h1 h2 hne' (by rw [(hspend t).2, (hspend t').2])
    exact Finset.disjoint_left.mp this (hspend t).1 (hspend t').1

/-- **Lemma 4.4** (`k`-Spending): at any time, the spending number of the histories of the
correct processes is at most the inconsistency number `k_max = λ(Q, F)`. The hypothesis that
every process has a quorum is implicit in the paper (otherwise there is no quorum map and
`k_max` is undefined). -/
theorem lemma_4_4 (hq : A.T.HasQuorums) (hB : A.B ∈ A.T.F) {σ : State P Tx}
    (h : A.Reachable σ) : A.X.spendingNumber (A.Γ σ) ≤ inconsistencyNumber A.T := by
  rw [TxSystem.spendingNumber_le_iff]
  intro r tx _
  exact encard_le_of_finset fun D hD => A.card_spend_le h A.T rfl hB hq D hD

/-- The faulty-issuer case with the actual faulty set: a process spends an input at most
`λ(Q, {B})` times. -/
theorem spend_le_byz (hq : A.T.HasQuorums) {σ : State P Tx} (h : A.Reachable σ) (r : P)
    (tx : Tx) :
    (A.X.spendSet (A.Γ σ) r tx).encard ≤ inconsistencyNumber ⟨A.T.Q, {A.B}⟩ :=
  encard_le_of_finset fun D hD => A.card_spend_le h ⟨A.T.Q, {A.B}⟩ rfl rfl hq D hD

/-- Correct processes never issue conflicting transactions (implicit in the paper, used in the
proofs of Lemma 4.7 and of Accuracy). -/
def HonestIssuers : Prop :=
  ∀ p ∉ A.B, ∀ t ∈ A.issue p, ∀ t' ∈ A.issue p, ¬ A.X.Conflict t t'

/-- **Integrity** (Theorem 4.8): if the issuer `w` of a transaction accepted by a correct
process is correct, then `w` issued it. -/
theorem integrity (hself : A.T.SelfMem) {σ : State P Tx} (h : A.Reachable σ) {p w : P}
    {t : Tx} (hp : p ∉ A.B) (ht : t ∈ σ.hist p) (hw : A.X.issuer t = some w) (hwB : w ∉ A.B) :
    (w, Msg.req t) ∈ σ.sent ∧ t ∈ A.issue w := by
  have hI := Reachable.inv A h
  have hne : t ≠ A.X.init := fun e => by rw [e, A.X.issuer_init] at hw; simp at hw
  obtain ⟨Q, hQ, hQe⟩ := hI.quorum p t hp ht hne
  obtain ⟨w', hw', hs⟩ := hI.echo_signed _ _ _ (hQe p (hself p Q hQ))
  rw [hw] at hw'
  obtain rfl := Option.some_injective _ hw'
  have hreq : (w, Msg.req t) ∈ σ.sent := hs.resolve_left hwB
  exact ⟨hreq, hI.req_issue w t hwB hreq⟩

/-- A correct issuer spends each input at most once. -/
theorem spend_le_one_of_correct (hself : A.T.SelfMem) (hhon : A.HonestIssuers)
    {σ : State P Tx} (h : A.Reachable σ) {r : P} (hr : r ∉ A.B) (tx : Tx) :
    (A.X.spendSet (A.Γ σ) r tx).encard ≤ 1 := by
  rw [Set.encard_le_one_iff]
  intro t t' ht ht'
  by_contra hne
  have i1 : t ∈ A.issue r := by
    obtain ⟨p, hp, hph, -⟩ := exists_acceptor A h ht
    exact (A.integrity hself h hp hph ht.2.2 hr).2
  have i2 : t' ∈ A.issue r := by
    obtain ⟨p, hp, hph, -⟩ := exists_acceptor A h ht'
    exact (A.integrity hself h hp hph ht'.2.2 hr).2
  exact hhon r hr t i1 t' i2
    ⟨hne, by rw [ht.2.2, ht'.2.2], Finset.not_disjoint_iff.mpr ⟨tx, ht.2.1, ht'.2.1⟩⟩

/-- **Refined `k`-spending bound**: `γ(Γ) ≤ max 1 λ(Q, {B})` where `B` is the actual faulty set.
Only a faulty issuer can multiply spend, and only the graphs `G_{B,S}` matter. -/
theorem spendingNumber_le_refined (hq : A.T.HasQuorums) (hself : A.T.SelfMem)
    (hhon : A.HonestIssuers) {σ : State P Tx} (h : A.Reachable σ) :
    A.X.spendingNumber (A.Γ σ) ≤ max 1 (inconsistencyNumber ⟨A.T.Q, {A.B}⟩ : ℕ∞) := by
  rw [TxSystem.spendingNumber_le_iff]
  intro r tx _
  by_cases hr : r ∈ A.B
  · exact (A.spend_le_byz hq h r tx).trans (le_max_right _ _)
  · exact (A.spend_le_one_of_correct hself hhon h hr tx).trans (le_max_left _ _)

/-- **Accuracy** (Theorem 4.8, sound direction): every accusation of a correct process is
verifiable (`verify-acc`): two distinct conflicting transactions validly signed by the
accused. -/
theorem accuracy {σ : State P Tx} (h : A.Reachable σ) {p w : P} {t t' : Tx} (hp : p ∉ A.B)
    (ha : (w, t, t') ∈ acHist σ p) :
    A.VerifyAcc w t t' ∧ A.Signed σ t ∧ A.Signed σ t' :=
  (Reachable.inv A h).acc_sent p w t t' hp ha

/-- **Accuracy**, `AC ⊆ F`: only faulty processes are accused (if correct processes never issue
conflicting transactions). -/
theorem accused_byzantine (hhon : A.HonestIssuers) {σ : State P Tx} (h : A.Reachable σ)
    {p w : P} {t t' : Tx} (hp : p ∉ A.B) (ha : (w, t, t') ∈ acHist σ p) : w ∈ A.B := by
  have hI := Reachable.inv A h
  obtain ⟨⟨hne, hw, hw', hdis⟩, ⟨w1, h1, s1⟩, ⟨w2, h2, s2⟩⟩ := A.accuracy h hp ha
  by_contra hwB
  rw [hw] at h1; obtain rfl := Option.some_injective _ h1
  rw [hw'] at h2; obtain rfl := Option.some_injective _ h2
  have i1 := hI.req_issue _ t hwB (s1.resolve_left hwB)
  have i2 := hI.req_issue _ t' hwB (s2.resolve_left hwB)
  exact hhon _ hwB t i1 t' i2 ⟨hne, hw.trans hw'.symm, hdis⟩

/-- **Monotonicity** (Theorem 4.8) of transaction histories. -/
theorem hist_mono {σ σ' : State P Tx} (h : Relation.ReflTransGen A.Step σ σ') (p : P) :
    σ.hist p ⊆ σ'.hist p := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans (Step.hist_subset A hs p)

/-- **Monotonicity** (Theorem 4.8) of accusation histories. -/
theorem acHist_mono {σ σ' : State P Tx} (h : Relation.ReflTransGen A.Step σ σ') (p : P) :
    acHist σ p ⊆ acHist σ' p := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact fun a ha => Step.sent_subset A hs (ih ha)

omit [Fintype P] [DecidableEq P] in
/-- The Accuracy property of §4.2 literally says "`verify-acc(AC, P)` returns true **if and only
if** `AC ⊆ F`". The "if" direction cannot hold for a run-independent verification function as
soon as some process may or may not be faulty: only the "only if" direction (soundness, proved in
`accused_byzantine`) is meaningful. -/
theorem accuracy_iff_impossible {Pf : Type*} [Nonempty Pf] (Fs : Set (Finset P)) (p : P)
    (h0 : ∅ ∈ Fs) (hp : {p} ∈ Fs) (verify : Finset P → Pf → Prop) :
    ¬ ∀ F ∈ Fs, ∀ AC pf, verify AC pf ↔ AC ⊆ F := by
  intro h
  obtain ⟨pf⟩ := ‹Nonempty Pf›
  have h1 := (h {p} hp {p} pf).mpr le_rfl
  have h2 := (h ∅ h0 {p} pf).mp h1
  exact Finset.notMem_empty p (h2 (Finset.mem_singleton_self p))

end Setup

end Podc.MultipleSpending
