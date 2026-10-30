import Papers.PODC2022.InternetComputerConsensus.Safety

/-!
# Deadlock freeness of ICC0 (Lemma "Deadlock freeness", Property P1)

**Lemma (Deadlock freeness)** of [ICC, Section 4]: "Assume at most `t < n/3` corrupt parties,
secure signatures, and collision resistance. In each round, if all messages up to that round
broadcast by honest parties have been delivered to all honest parties, and all notarization and
proposal delay times have elapsed, then all honest parties will have finished the round with a
notarized block."

We read "will have finished" with the paper's "wait for" semantics: an honest party executes a
clause as soon as its condition holds. So the hypothesis is a reachable state in which
* every message of a round `≤ k` broadcast by an honest party is in every honest pool;
* every honest party in a round `≤ k` that has started its round has its proposal and
  notarization delays elapsed (for all ranks);
* no honest party in a round `≤ k` has an enabled clause of the Tree Building Subprotocol
  (`TBSettled`);
and the conclusion is that every honest party is past round `k`.

The proof: take an honest party in the smallest round `j ≤ k`. If it waits for the beacon, it has
the `n - |F| ≥ t + 1` honest beacon shares. If some honest party already finished round `j`, its
notarization (and the echoed chain below it) has been delivered. Otherwise every honest party is
in round `j`, has proposed, and has cast a notarization share for the valid non-disqualified block
of minimal rank in its pool; since disqualifications are echoed, all honest parties pick the same
minimal rank and the same block, and its `n - |F| ≥ n - t` shares finish the round.
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

/-- No clause of the Tree Building Subprotocol is enabled for `q`: every enabled clause is a
clause of the Finalization Subprotocol (the only clauses that change `kmax`). -/
def TBSettled (π : Params P) (s : GState P V) (q : P) : Prop :=
  ∀ l M, LStep π s.now q (s.loc q) l M → (s.loc q).kmax < l.kmax

/-- A notarization that can exist has an honest signer, whose share was cast on an echoed block. -/
theorem Inv.auth_of_notarCert {s : GState P V} (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {B : Block P V} (hB : NotarCert π F s.sent B) :
    Msg.auth B ∈ s.sent := by
  obtain ⟨q, hqF, hq⟩ := hB.exists_correct_signer hF (by omega)
  exact (hI.share B q (hq.resolve_left hqF)).2.1

/-- If all honest messages of rounds `≤ K` are in `pool`, every echoed block of round `≤ K` is
valid for `pool`. -/
theorem Inv.valid_of_auth {s : GState P V} (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {pool : Set (Msg P V)} {K : ℕ}
    (hdel : ∀ m ∈ s.sent, m.round ≤ K → m ∈ pool) :
    ∀ {B : Block P V}, B.round ≤ K → Msg.auth B ∈ s.sent → Valid pool B
  | .root, _, _ => trivial
  | .mk k α par pl, hK, hB => by
      obtain ⟨k', α', par', pl', he, h1, h2, h3⟩ := hI.sent_auth _ hB
      simp only [Block.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [Block.round_mk] at hK
      refine ⟨h1, hdel _ h2 hK, hdel _ hB hK, ?_, ?_⟩
      · rcases hI.sent_notar _ h3 with h | h
        · rw [h]; trivial
        · exact Inv.valid_of_auth hI hF hn hdel (by omega) (hI.auth_of_notarCert hF hn h)
      · exact Or.inr (hdel _ h3 (by simp [Msg.round]; omega))

/-- A notarization broadcast by an honest party, once delivered with everything below it, makes
the block notarized. -/
theorem Inv.notarized_of_sent {s : GState P V} (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {pool : Set (Msg P V)} {K : ℕ}
    (hdel : ∀ m ∈ s.sent, m.round ≤ K → m ∈ pool) {B : Block P V} (hK : B.round ≤ K)
    (hB : Msg.notar B ∈ s.sent) : Notarized pool B := by
  rcases hI.sent_notar B hB with h | h
  · rw [h]; exact notarized_root _
  · exact ⟨hI.valid_of_auth hF hn hdel hK (hI.auth_of_notarCert hF hn h),
      Or.inr (hdel _ hB (by simpa [Msg.round] using hK))⟩

/-- A disqualified rank is the rank of a corrupt party. -/
theorem Inv.D_corrupt {s : GState P V} (hI : Inv π F s)
    (hinj : ∀ k, Function.Injective (π.rank k)) {q : P} (hq : q ∉ F)
    (hact : (s.loc q).active = true) {r : ℕ} (hr : r ∈ (s.loc q).D) :
    ∃ α ∈ F, π.rank (s.loc q).round α = r := by
  obtain ⟨B₁, B₂, hne, h1, h2, h3, h4, h5, h6⟩ := hI.D_spec q hq hact r hr
  have hpos := hI.round_pos q hq
  cases B₁ with
  | root => simp at h1; omega
  | mk k₁ α₁ par₁ pl₁ =>
  cases B₂ with
  | root => simp at h2; omega
  | mk k₂ α₂ par₂ pl₂ =>
    simp only [Block.round_mk] at h1 h2
    subst h1 h2
    simp only [Block.rk_mk] at h3 h4
    have hα : α₁ = α₂ := hinj _ (h3.trans h4.symm)
    subst hα
    by_contra hcon
    have hα₁ : α₁ ∉ F := fun h => hcon ⟨α₁, h, h3⟩
    obtain ⟨rfl, rfl⟩ := hI.auth_unique _ α₁ par₁ pl₁ par₂ pl₂ hα₁ h5 h6
    exact hne rfl

/-- `t + 1` honest beacon shares: `n - |F| ≥ t + 1`. -/
theorem beaconReady_of_forall {pool : Set (Msg P V)} (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {j : ℕ} (h : ∀ q ∉ F, Msg.beacon j q ∈ pool) :
    BeaconReady π pool j :=
  (certified_of_forall_notMem (signed := fun q k => Msg.beacon k q ∈ pool) hF h).mono
    (fun _ h => h) (by omega)

theorem notarShares_of_forall {pool : Set (Msg P V)} (hF : #F ≤ π.t) {B : Block P V}
    (h : ∀ q ∉ F, Msg.notarShare B q ∈ pool) : NotarShares π pool B :=
  (certified_of_forall_notMem (signed := fun q B => Msg.notarShare B q ∈ pool) hF h).mono
    (fun _ h => h) (by omega)

theorem finalShares_of_forall {pool : Set (Msg P V)} (hF : #F ≤ π.t) {B : Block P V}
    (h : ∀ q ∉ F, Msg.finalShare B q ∈ pool) : FinalShares π pool B :=
  (certified_of_forall_notMem (signed := fun q B => Msg.finalShare B q ∈ pool) hF h).mono
    (fun _ h => h) (by omega)

/-- The hypotheses of the core argument: everybody honest is in round `j` (started), everything of
rounds `≤ j` is delivered, delays elapsed, no Tree Building clause enabled. -/
structure Stuck (π : Params P) (F : Finset P) (s : GState P V) (j : ℕ) : Prop where
  inv : Inv π F s
  inj : ∀ k, Function.Injective (π.rank k)
  hF : #F ≤ π.t
  hn : 3 * π.t < Fintype.card P
  del : ∀ m ∈ s.sent, m.round ≤ j → ∀ q ∉ F, m ∈ (s.loc q).pool
  all : ∀ q ∉ F, (s.loc q).round = j ∧ (s.loc q).active = true
  time : ∀ q ∉ F, (∀ α, (s.loc q).t0 j + π.Δntry (π.rank j α) ≤ s.now) ∧
    (s.loc q).t0 j + π.Δprop (π.rank j q) ≤ s.now
  set : ∀ q ∉ F, TBSettled π s q

/-- A candidate rank of `q` in round `j`: the rank of a valid round-`j` block not
disqualified by `q`. -/
def Cand (s : GState P V) (π : Params P) (j : ℕ) (q : P) (r : ℕ) : Prop :=
  ∃ B : Block P V, Valid (s.loc q).pool B ∧ B.round = j ∧ B.rk π.rank = r ∧ r ∉ (s.loc q).D

section Main

variable [Nonempty V] {s : GState P V} {j : ℕ} (H : Stuck π F s j)
include H

theorem Stuck.cand_exists_of_proposed {q : P} (hq : q ∉ F) (hprop : (s.loc q).proposed = true) :
    ∃ r, Cand s π j q r := by
  have hI := H.inv
  obtain ⟨hr, ha⟩ := H.all q hq
  obtain ⟨par, pl, hauth⟩ := hI.proposed_auth q hq ha hprop
  refine ⟨π.rank j q, .mk j q par pl, ?_, rfl, rfl, fun hD => ?_⟩
  · rw [hr] at hauth
    exact hI.valid_of_auth H.hF H.hn (fun m hm hmr => H.del m hm hmr q hq) (by simp) hauth
  · rw [← hr] at hD
    obtain ⟨α, hα, he⟩ := hI.D_corrupt H.inj hq ha hD
    exact hq (H.inj _ he ▸ hα)

theorem Stuck.proposed {q : P} (hq : q ∉ F) : (s.loc q).proposed = true := by
  have hI := H.inv
  obtain ⟨hr, ha⟩ := H.all q hq
  by_contra hp
  simp only [Bool.not_eq_true] at hp
  obtain ⟨Bp, h1, h2⟩ := hI.parent_ok q hq
  have := H.set q hq _ _ (LStep.propose (s.loc q) Bp (Classical.arbitrary _) ha hp
    (by rw [hr]; exact (H.time q hq).2) h1 h2)
  simp at this

open Classical in
/-- The minimal candidate rank of an honest party. -/
noncomputable def Stuck.rmin (q : P) (hq : q ∉ F) : ℕ :=
  Nat.find (H.cand_exists_of_proposed hq (H.proposed hq))

theorem Stuck.rmin_spec {q : P} (hq : q ∉ F) : Cand s π j q (H.rmin q hq) := by
  classical
  exact Nat.find_spec (H.cand_exists_of_proposed hq (H.proposed hq))

theorem Stuck.rmin_le {q : P} (hq : q ∉ F) {r : ℕ} (hr : Cand s π j q r) : H.rmin q hq ≤ r := by
  classical
  exact Nat.find_min' _ hr

/-- Every valid round-`j` block of minimal candidate rank has received a notarization share. -/
theorem Stuck.mem_N {q : P} (hq : q ∉ F) {B : Block P V} (hBv : Valid (s.loc q).pool B)
    (hBr : B.round = j) (hBk : B.rk π.rank = H.rmin q hq) : B ∈ (s.loc q).N := by
  have hI := H.inv
  obtain ⟨hr, ha⟩ := H.all q hq
  obtain ⟨-, -, -, -, hD⟩ := H.rmin_spec hq
  by_contra hBN
  have hpos := hI.round_pos q hq
  have hBr' : B.round = (s.loc q).round := hBr.trans hr.symm
  have hD' : B.rk π.rank ∉ (s.loc q).D := hBk ▸ hD
  have htime' : (s.loc q).t0 (s.loc q).round + π.Δntry (B.rk π.rank) ≤ s.now := by
    cases B with
    | root => simp at hBr'; omega
    | mk k α par pl =>
      simp only [Block.round_mk] at hBr
      subst hBr
      rw [hr]; exact (H.time q hq).1 α
  have hbetter : ∀ B', Valid (s.loc q).pool B' → B'.round = (s.loc q).round →
      B'.rk π.rank < B.rk π.rank → B'.rk π.rank ∈ (s.loc q).D := by
    intro B' h1 h2 h3
    by_contra h4
    have := H.rmin_le hq ⟨B', h1, h2.trans hr, rfl, h4⟩
    omega
  by_cases hex : ∃ B' ∈ (s.loc q).N, B'.rk π.rank = B.rk π.rank
  · have := H.set q hq _ _ (LStep.echoDisq _ B ha hBr' hBv hBN hD' htime' hbetter hex)
    simp at this
  · have := H.set q hq _ _ (LStep.echoShare _ B ha hBr' hBv hBN hD' htime' hbetter hex)
    simp at this

theorem Stuck.witness {q : P} (hq : q ∉ F) : ∃ B : Block P V, Valid (s.loc q).pool B ∧
    B.round = j ∧ B.rk π.rank = H.rmin q hq ∧ B ∈ (s.loc q).N ∧
    Msg.notarShare B q ∈ s.sent ∧ Msg.auth B ∈ s.sent := by
  obtain ⟨B, h1, h2, h3, -⟩ := H.rmin_spec hq
  have h4 := H.mem_N hq h1 h2 h3
  have h5 := (H.inv.N_share q hq (H.all q hq).2 B h4).1
  exact ⟨B, h1, h2, h3, h4, h5, (H.inv.share B q h5).2.1⟩

theorem Stuck.valid_of_auth {q : P} (hq : q ∉ F) {B : Block P V} (hB : Msg.auth B ∈ s.sent)
    (hBr : B.round = j) : Valid (s.loc q).pool B :=
  H.inv.valid_of_auth H.hF H.hn (fun m hm hmr => H.del m hm hmr q hq) hBr.le hB

theorem Stuck.rmin_notMem_D {p q : P} (hp : p ∉ F) (hq : q ∉ F) :
    H.rmin q hq ∉ (s.loc p).D := by
  intro hD
  obtain ⟨hr, ha⟩ := H.all p hp
  obtain ⟨B₁, B₂, hne, h1, h2, h3, h4, h5, h6⟩ := H.inv.D_spec p hp ha _ hD
  rw [hr] at h1 h2
  have e₁ := H.mem_N hq (H.valid_of_auth hq h5 h1) h1 h3
  have e₂ := H.mem_N hq (H.valid_of_auth hq h6 h2) h2 h4
  exact hne (H.inv.N_unique q hq (H.all q hq).2 B₁ e₁ B₂ e₂ (h3.trans h4.symm))

theorem Stuck.rmin_le_rmin {p q : P} (hp : p ∉ F) (hq : q ∉ F) : H.rmin p hp ≤ H.rmin q hq := by
  obtain ⟨B, -, h2, h3, -, -, h6⟩ := H.witness hq
  exact H.rmin_le hp ⟨B, H.valid_of_auth hp h6 h2, h2, h3, H.rmin_notMem_D hp hq⟩

/-- The core of deadlock freeness: the hypotheses `Stuck` are contradictory. -/
theorem Stuck.false : False := by
  have hI := H.inv
  obtain ⟨q₀, hq₀⟩ : ∃ q, q ∉ F := by
    by_contra h
    push Not at h
    have : (univ : Finset P) ⊆ F := fun q _ => h q
    have := card_le_card this
    have := H.hF; have := H.hn; simp at *; omega
  obtain ⟨B₀, h1, h2, h3, h4, -, -⟩ := H.witness hq₀
  have hall : ∀ q (hq : q ∉ F), Msg.notarShare B₀ q ∈ s.sent := by
    intro q hq
    obtain ⟨B, -, g2, g3, g4, g5, g6⟩ := H.witness hq
    have hrm : H.rmin q hq = H.rmin q₀ hq₀ :=
      le_antisymm (H.rmin_le_rmin hq hq₀) (H.rmin_le_rmin hq₀ hq)
    have e := H.mem_N hq₀ (H.valid_of_auth hq₀ g6 g2) g2 (g3.trans hrm)
    rw [hI.N_unique q₀ hq₀ (H.all q₀ hq₀).2 B e B₀ h4 (by rw [g3, h3, hrm])] at g5
    exact g5
  obtain ⟨hr, ha⟩ := H.all q₀ hq₀
  have := H.set q₀ hq₀ _ _ (LStep.finish (s.loc q₀) B₀ ha (h2.trans hr.symm) h1 (Or.inr
    (notarShares_of_forall H.hF (fun q hq => H.del _ (hall q hq) (by simp [Msg.round, h2]) q₀ hq₀))))
  simp at this

end Main

/-- **Lemma (Deadlock freeness)** of [ICC, Section 4] (Property P1). Assume at most `t < n/3`
corrupt parties (idealized signatures and hashing; ranks given by a permutation in each round).
Consider a reachable state and a round `k` such that
* all messages of rounds `≤ k` broadcast by honest parties have been delivered to all honest
  parties,
* every honest party that has started a round `≤ k` has its proposal and notarization delays
  elapsed (for all ranks), and
* with the "wait for" semantics, no honest party in a round `≤ k` has an enabled clause of the
  Tree Building Subprotocol.

Then all honest parties have finished round `k`. (A round can only be finished by clause (a), with a
notarized round-`k` block; `Inv.finished` records that a notarization of a round-`k` block has been
broadcast.) -/
theorem deadlock_freeness [Nonempty V] (hinj : ∀ k, Function.Injective (π.rank k))
    (hF : #F ≤ π.t) (hn : 3 * π.t < Fintype.card P) {s : GState P V} (hs : Reachable π F s)
    (k : ℕ) (hdel : ∀ m ∈ s.sent, m.round ≤ k → ∀ q ∉ F, m ∈ (s.loc q).pool)
    (htime : ∀ q ∉ F, (s.loc q).round ≤ k → (s.loc q).active = true →
      (∀ α, (s.loc q).t0 (s.loc q).round + π.Δntry (π.rank (s.loc q).round α) ≤ s.now) ∧
        (s.loc q).t0 (s.loc q).round + π.Δprop (π.rank (s.loc q).round q) ≤ s.now)
    (hset : ∀ q ∉ F, (s.loc q).round ≤ k → TBSettled π s q) :
    ∀ q ∉ F, k < (s.loc q).round := by
  have hI := inv_of_reachable hinj hF hn hs
  by_contra hcon
  push Not at hcon
  obtain ⟨q₀, hq₀F, hq₀k⟩ := hcon
  obtain ⟨qm, hqm, hmin⟩ := (univ.filter (· ∉ F)).exists_min_image (fun q => (s.loc q).round)
    ⟨q₀, by simpa using hq₀F⟩
  simp only [mem_filter, mem_univ, true_and] at hqm hmin
  set j := (s.loc qm).round with hj
  have hjk : j ≤ k := (hmin q₀ hq₀F).trans hq₀k
  have hj1 : 1 ≤ j := hI.round_pos qm hqm
  -- Case A: someone in round `j` waits for the beacon
  by_cases hA : ∃ q ∉ F, (s.loc q).round = j ∧ (s.loc q).active = false
  · obtain ⟨q, hq, hqr, hqa⟩ := hA
    have hready : BeaconReady π (s.loc q).pool (s.loc q).round := by
      refine beaconReady_of_forall hF hn (fun q' hq' => ?_)
      refine hdel _ (hI.beacon_sent q' hq' _ (by omega) ?_) (by simp [Msg.round]; omega) q hq
      rw [hqr]; exact hmin q' hq'
    have := hset q hq (by omega) _ _ (LStep.beacon _ hqa hready)
    simp [LState.start] at this
  push Not at hA
  have hact : ∀ q ∉ F, (s.loc q).round = j → (s.loc q).active = true := by
    intro q hq hqr
    have := hA q hq hqr
    simpa using this
  -- Case B1: someone already finished round `j`
  by_cases hB : ∃ q ∉ F, j < (s.loc q).round
  · obtain ⟨q, hq, hqj⟩ := hB
    obtain ⟨B, hBr, hBn⟩ := hI.finished q hq j hj1 hqj
    have hBnot := hI.notarized_of_sent hF hn (fun m hm hmr => hdel m hm hmr qm hqm)
      (by omega) hBn
    have := hset qm hqm hjk _ _ (LStep.finish _ B (hact qm hqm rfl) hBr hBnot.1
      (Or.inl <| hdel _ hBn (by simp [Msg.round]; omega) qm hqm))
    simp at this
  push Not at hB
  have hall : ∀ q ∉ F, (s.loc q).round = j ∧ (s.loc q).active = true := fun q hq =>
    ⟨le_antisymm (hB q hq) (hmin q hq), hact q hq (le_antisymm (hB q hq) (hmin q hq))⟩
  refine Stuck.false (V := V) (j := j) ⟨hI, hinj, hF, hn,
    fun m hm hmr q hq => hdel m hm (hmr.trans hjk) q hq, hall, fun q hq => ?_,
    fun q hq => hset q hq (by rw [(hall q hq).1]; exact hjk)⟩
  have := htime q hq (by rw [(hall q hq).1]; exact hjk) (hall q hq).2
  rw [(hall q hq).1] at this
  exact this

end Podc.InternetComputerConsensus
