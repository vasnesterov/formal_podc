import Papers.PODC2022.InternetComputerConsensus.Basic

/-!
# The global invariant of ICC0

`Inv π F s` collects the facts about reachable states used by all three main properties.
The key ones are:

* `pool_avail`: honest pools only contain available messages (unforgeability);
* `share`: an honest notarization share for a round-`k` block was cast while in round `k`, after
  the block was echoed (its authenticator was broadcast by an honest party);
* `fshare`: an honest party that cast a finalization share for `B` cast no notarization share for
  another block of the same round (this is what makes Property P2 hold);
* `auth_unique`: an honest party authenticates at most one block per round;
* `D_spec`: a disqualified rank has two distinct echoed blocks.
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] (π : Params P) (F : Finset P)

/-- The global invariant. -/
structure Inv (s : GState P V) : Prop where
  round_pos : ∀ q ∉ F, 1 ≤ (s.loc q).round
  pool_avail : ∀ q ∉ F, ∀ m ∈ (s.loc q).pool, Avail π F s.sent m
  sent_notar : ∀ B, Msg.notar B ∈ s.sent → B = .root ∨ NotarCert π F s.sent B
  sent_final : ∀ B, Msg.final B ∈ s.sent → FinalCert π F s.sent B
  sent_auth : ∀ B, Msg.auth B ∈ s.sent → ∃ k α par pl, B = .mk k α par pl ∧ par.round + 1 = k ∧
    Msg.block B ∈ s.sent ∧ Msg.notar par ∈ s.sent
  auth_honest : ∀ k α par pl, α ∉ F → Msg.auth (.mk k α par pl) ∈ s.sent →
    k < (s.loc α).round ∨
      (k = (s.loc α).round ∧ (s.loc α).active = true ∧ (s.loc α).proposed = true)
  auth_unique : ∀ k α par pl par' pl', α ∉ F → Msg.auth (.mk k α par pl) ∈ s.sent →
    Msg.auth (.mk k α par' pl') ∈ s.sent → par = par' ∧ pl = pl'
  proposed_auth : ∀ q ∉ F, (s.loc q).active = true → (s.loc q).proposed = true →
    ∃ par pl, Msg.auth (.mk (s.loc q).round q par pl) ∈ s.sent
  share : ∀ B q, Msg.notarShare B q ∈ s.sent → q ∉ F ∧ Msg.auth B ∈ s.sent ∧ 1 ≤ B.round ∧
    (B.round < (s.loc q).round ∨
      (B.round = (s.loc q).round ∧ (s.loc q).active = true ∧ B ∈ (s.loc q).N)) ∧
    (s.loc q).t0 B.round + π.Δntry (B.rk π.rank) ≤ s.now
  N_share : ∀ q ∉ F, (s.loc q).active = true → ∀ B ∈ (s.loc q).N,
    Msg.notarShare B q ∈ s.sent ∧ B.round = (s.loc q).round
  N_unique : ∀ q ∉ F, (s.loc q).active = true → ∀ B₁ ∈ (s.loc q).N, ∀ B₂ ∈ (s.loc q).N,
    B₁.rk π.rank = B₂.rk π.rank → B₁ = B₂
  D_spec : ∀ q ∉ F, (s.loc q).active = true → ∀ r ∈ (s.loc q).D, ∃ B₁ B₂, B₁ ≠ B₂ ∧
    B₁.round = (s.loc q).round ∧ B₂.round = (s.loc q).round ∧ B₁.rk π.rank = r ∧
    B₂.rk π.rank = r ∧ Msg.auth B₁ ∈ s.sent ∧ Msg.auth B₂ ∈ s.sent
  fshare : ∀ B q, Msg.finalShare B q ∈ s.sent → q ∉ F ∧ B.round < (s.loc q).round ∧
    (∀ B', Msg.notarShare B' q ∈ s.sent → B'.round = B.round → B' = B)
  beacon_sent : ∀ q ∉ F, ∀ j, 1 ≤ j → j ≤ (s.loc q).round → Msg.beacon j q ∈ s.sent
  beacon_active : ∀ q ∉ F, (s.loc q).active = true →
    Msg.beacon ((s.loc q).round + 1) q ∈ s.sent
  finished : ∀ q ∉ F, ∀ i, 1 ≤ i → i < (s.loc q).round →
    ∃ B : Block P V, B.round = i ∧ Msg.notar B ∈ s.sent
  parent_ok : ∀ q ∉ F, ∃ Bp, Bp.round + 1 = (s.loc q).round ∧ Notarized (s.loc q).pool Bp
  out_ok : ∀ q ∉ F, ((s.loc q).kmax = 0 ∧ (s.loc q).out = []) ∨
    ∃ B, B.round = (s.loc q).kmax ∧ Valid (s.loc q).pool B ∧ FinalCert π F s.sent B ∧
      (s.loc q).out = B.chain
  t0_le : ∀ q ∉ F, ∀ j, (j < (s.loc q).round ∨ (j = (s.loc q).round ∧ (s.loc q).active = true)) →
    (s.loc q).t0 j ≤ s.now
  fshare_cert : ∀ B q, Msg.finalShare B q ∈ s.sent → NotarCert π F s.sent B

variable {π F}

/-- The state after party `p` executes a clause leading to `l` and broadcasting `M`. -/
def actState (s : GState P V) (p : P) (l : LState P V) (M : Set (Msg P V)) : GState P V :=
  { s with loc := Function.update s.loc p { l with pool := l.pool ∪ M }, sent := s.sent ∪ M }

@[simp] theorem actState_loc_self (s : GState P V) (p : P) (l : LState P V) (M) :
    (actState s p l M).loc p = { l with pool := l.pool ∪ M } := by
  simp [actState]

@[simp] theorem actState_loc_ne (s : GState P V) {p q : P} (l : LState P V) (M) (h : q ≠ p) :
    (actState s p l M).loc q = s.loc q := by
  simp [actState, Function.update_of_ne h]

@[simp] theorem actState_sent (s : GState P V) (p : P) (l : LState P V) (M) :
    (actState s p l M).sent = s.sent ∪ M := rfl

@[simp] theorem actState_now (s : GState P V) (p : P) (l : LState P V) (M) :
    (actState s p l M).now = s.now := rfl

/-! ### Safety core -/

/-- **Property P2 at the level of signatures.** If a finalization on `B` and a notarization on
`B'` can both exist, and `B`, `B'` have the same round, then `B' = B`. -/
theorem Inv.final_notar_eq {s : GState P V} (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {B B' : Block P V} (hB : FinalCert π F s.sent B)
    (hB' : NotarCert π F s.sent B') (hr : B'.round = B.round) : B' = B := by
  obtain ⟨q, hqF, hq1, hq2⟩ := hB.common_correct_signer hB' hF (by omega)
  have h1 := hq1.resolve_left hqF
  have h2 := hq2.resolve_left hqF
  exact (hI.fshare B q h1).2.2 B' h2 hr

/-- A finalization can only exist for a block that has a notarization. -/
theorem Inv.notarCert_of_finalCert {s : GState P V} (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {B : Block P V} (hB : FinalCert π F s.sent B) :
    NotarCert π F s.sent B := by
  obtain ⟨q, hqF, hq⟩ := hB.exists_correct_signer hF (by omega)
  exact hI.fshare_cert B q (hq.resolve_left hqF)

/-! ### Initial state -/

theorem inv_init : Inv π F (GState.init F : GState P V) := by
  constructor <;> simp [GState.init, LState.init]
  · intro q hq; exact Or.inr ⟨q, hq, rfl⟩
  · intro q hq j h1 h2; exact ⟨hq, by omega⟩
  · intro q _ i h1; omega
  · intro q _; exact ⟨.root, rfl, notarized_root _⟩

/-! ### Delivery and ticks -/

/-- Growing honest pools by available messages preserves the invariant. -/
theorem Inv.of_pools {s s' : GState P V} (hI : Inv π F s) (hnow : s'.now = s.now)
    (hsent : s'.sent = s.sent) (pl : P → Set (Msg P V))
    (hloc : ∀ q, s'.loc q = { s.loc q with pool := pl q }) (hsub : ∀ q, (s.loc q).pool ⊆ pl q)
    (havail : ∀ q ∉ F, ∀ m ∈ pl q, Avail π F s.sent m) : Inv π F s' := by
  constructor <;> simp only [hloc, hsent, hnow]
  · exact hI.round_pos
  · exact havail
  · exact hI.sent_notar
  · exact hI.sent_final
  · exact hI.sent_auth
  · exact hI.auth_honest
  · exact hI.auth_unique
  · exact hI.proposed_auth
  · exact hI.share
  · exact hI.N_share
  · exact hI.N_unique
  · exact hI.D_spec
  · exact hI.fshare
  · exact hI.beacon_sent
  · exact hI.beacon_active
  · exact hI.finished
  · intro q hq
    obtain ⟨Bp, h1, h2⟩ := hI.parent_ok q hq
    exact ⟨Bp, h1, h2.mono (hsub q)⟩
  · intro q hq
    rcases hI.out_ok q hq with h | ⟨B, h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨B, h1, h2.mono (hsub q), h3, h4⟩
  · exact hI.t0_le
  · exact hI.fshare_cert

theorem Inv.deliver {s : GState P V} (hI : Inv π F s) {p : P} {m : Msg P V} (hp : p ∉ F)
    (hm : Avail π F s.sent m) :
    Inv π F { s with loc := (Function.update s.loc p
      { s.loc p with pool := insert m (s.loc p).pool }) } := by
  refine hI.of_pools rfl rfl (fun q => if q = p then insert m (s.loc p).pool else (s.loc q).pool)
    (fun q => ?_) (fun q => ?_) (fun q hq => ?_)
  · by_cases h : q = p
    · subst h; simp
    · simp [h]
  · by_cases h : q = p
    · subst h; simp
    · simp [h]
  · by_cases h : q = p
    · subst h; simp only [ite_true, Set.mem_insert_iff]
      rintro m' (rfl | hm'); exacts [hm, hI.pool_avail q hq m' hm']
    · simp only [h, ite_false]; exact hI.pool_avail q hq

theorem Inv.tick {s : GState P V} (hI : Inv π F s) : Inv π F { s with now := s.now + 1 } := by
  constructor <;> simp only
  all_goals first
    | exact hI.round_pos | exact hI.pool_avail | exact hI.sent_notar | exact hI.sent_final
    | exact hI.sent_auth | exact hI.auth_honest | exact hI.auth_unique | exact hI.proposed_auth
    | exact hI.N_share | exact hI.N_unique | exact hI.D_spec | exact hI.fshare
    | exact hI.beacon_sent | exact hI.beacon_active | exact hI.finished | exact hI.parent_ok
    | exact hI.out_ok | exact hI.fshare_cert | skip
  · intro B q h
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI.share B q h
    exact ⟨h1, h2, h3, h4, by omega⟩
  · intro q hq j hj
    have := hI.t0_le q hq j hj
    omega

end Podc.InternetComputerConsensus
