import Papers.PODC2016.UnbeatableSetConsensus.Unbeatable

/-!
# Arbitrary deterministic protocols are covered (Coan's reduction)

The paper restricts attention to full-information protocols ("Coan showed that it is sufficient to
consider full-information protocols"). Our `Protocol` is a decision rule on full-information views.
Here we check that this covers every deterministic message-passing protocol of CSLib's synchronous
crash model (`Cslib.SyncCrash`, protocols `Cslib.Byzantine.LockStep.Protocol P ℕ M ℕ` with arbitrary
message type `M`): the history of a process is a function of its full-information view
(`hist_eq_of_sameView`), so its decisions form a `Protocol` (`Protocol.ofLockStep`) whose decision
times are those of the original protocol, with "decide" read as "first decision"
(`decidesAt_ofLockStep_iff`). Hence the unbeatability of `Optmin[k]` holds against all of them
(`theorem1_lockStep`).
-/

namespace Podc.UnbeatableSetConsensus

open Cslib

variable {P M : Type*}

-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash/System.lean
/-- **The history of every deterministic protocol is a function of the full-information view.** -/
theorem hist_eq_of_sameView (alg : Byzantine.LockStep.Protocol P ℕ M ℕ) {r r' : Run P} :
    ∀ {m : ℕ} {i : P}, SameView r r' i m → SyncCrash.hist alg r m i = SyncCrash.hist alg r' m i
  | 0, _, _ => rfl
  | m + 1, i, h => by
    rw [SyncCrash.hist_succ, SyncCrash.hist_succ, hist_eq_of_sameView alg h.1]
    congr 2
    funext p
    rw [SyncCrash.msg_eq_deliv, SyncCrash.msg_eq_deliv]
    have hc : (p ≠ i ∧ r.Deliv p i m) ↔ (p ≠ i ∧ r'.Deliv p i m) := h.2.1 p
    by_cases hp : p ≠ i ∧ r.Deliv p i m
    · have hs : SameView r r' p m := h.2.2 p hp
      rw [ite_eq_left hp, ite_eq_left (hc.1 hp), hs.input_eq, hist_eq_of_sameView alg hs]
    · rw [ite_eq_right hp, ite_eq_right (fun h' => hp (hc.2 h'))]

/-- The decision rule of a deterministic protocol, as a full-information decision rule. -/
noncomputable def Protocol.ofLockStep (alg : Byzantine.LockStep.Protocol P ℕ M ℕ) : Protocol P where
  dec r i m := alg.decide i (r.input i) (SyncCrash.hist alg r m i)
  dec_congr r r' i m h := by rw [h.input_eq, hist_eq_of_sameView alg h]

/-- Decisions of `Protocol.ofLockStep alg` are the first decisions of `alg`. -/
theorem decidesAt_ofLockStep_iff (alg : Byzantine.LockStep.Protocol P ℕ M ℕ) {r : Run P} {i : P}
    {m v : ℕ} : DecidesAt (Protocol.ofLockStep alg) r i m v ↔
      SyncCrash.DecidesAt alg r i m v ∧ ∀ m' < m, ∀ d, ¬ SyncCrash.DecidesAt alg r i m' d := by
  simp only [DecidesAt, SyncCrash.decidesAt_iff, Protocol.ofLockStep]
  constructor
  · rintro ⟨ha, hd, hb⟩
    exact ⟨⟨ha, hd⟩, fun m' hm' d ⟨_, hd'⟩ => by rw [hb m' hm'] at hd'; cases hd'⟩
  · rintro ⟨⟨ha, hd⟩, hb⟩
    refine ⟨ha, hd, fun m' hm' => ?_⟩
    by_contra hne
    obtain ⟨d, hd'⟩ := Option.ne_none_iff_exists'.1 hne
    exact hb m' hm' d ⟨ha.mono hm'.le, hd'⟩

/-- **Theorem 1 against arbitrary deterministic protocols**: a deterministic protocol (with
arbitrary messages) that solves nonuniform `k`-set consensus and decides no later than
`Optmin[k]` decides no earlier than `Optmin[k]`. -/
theorem theorem1_lockStep [Fintype P] {k t : ℕ} {D : Set ℕ} (hk : 1 ≤ k)
    (hD : ∀ v ≤ k, v ∈ D) (alg : Byzantine.LockStep.Protocol P ℕ M ℕ)
    (hsolve : SolvesSetConsensus k t D (Protocol.ofLockStep alg))
    (hdom : Dominates t D (Protocol.ofLockStep alg) (optmin k)) :
    Dominates t D (optmin k) (Protocol.ofLockStep alg) :=
  (theorem1 hk hD).2 _ hsolve hdom

end Podc.UnbeatableSetConsensus
