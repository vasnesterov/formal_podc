import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Messages

/-!
# Theorem 3.1: adaptive synchronous Byzantine agreement with `O(n·f)` messages and `O(f)` rounds

`theorem_3_1`: for `t < n/2`, given a quadratic fallback protocol (Momose–Ren; a black box,
`Fallback`, with `O(n)` rounds and `O(n)` messages per party), `SyncBA` is an unforging
deterministic protocol that solves Byzantine agreement against every authenticated static
Byzantine adversary with `f ≤ t` faults, all honest parties deciding within `C₁ (f + 1)` rounds
and sending at most `C₂ n (f + 1)` messages in total, for constants `C₁, C₂` depending only on the
fallback's constants.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {Mf Sf : Type}
  {Afb : Protocol (Fin n) Bool Mf Bool} {Af : Auth (Fin n) Mf Sf}

/-! ### Unforgeability of the protocol -/

lemma histTokens_append (h : History (Fin n) (Msg n)) (ib : Fin n → Option (Msg n)) :
    Auth.histTokens auth h ⊆ Auth.histTokens auth (h ++ [ib]) := by
  rw [Auth.histTokens_append]; exact Set.subset_union_left

lemma stateOf_toks (p : Fin n) (x : Bool) :
    ∀ h : History (Fin n) (Msg n), ∀ τ ∈ (stateOf π p x h).toks,
      τ.1 = p ∨ τ ∈ Auth.histTokens auth h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro τ hτ; simp [init_toks] at hτ
  | append_singleton h ib ih =>
    intro τ hτ
    rw [stateOf_append] at hτ
    rcases trans_toks hτ with h1 | ⟨q, hq⟩
    · exact (ih τ h1).imp_right fun h' => histTokens_append h ib h'
    · by_cases hqp : q = p
      · subst hqp
        simp only [ite_true] at hq
        rcases hm : out π q (stateOf π q x h) h.length q with _ | m
        · simp [hm, omToks] at hq
        · simp only [hm, omToks, Option.map_some, Option.getD_some] at hq
          rcases out_toks hm hq with h1 | h1
          · exact (ih τ h1).imp_right fun h' => histTokens_append h ib h'
          · exact Or.inl (ownToks_fst h1)
      · simp only [hqp, ite_false] at hq
        rcases hm : ib q with _ | m
        · simp [hm, omToks] at hq
        · simp only [hm, omToks, Option.map_some, Option.getD_some] at hq
          right
          rw [Auth.histTokens_append]
          exact Or.inr ⟨ib, List.mem_singleton_self _, q, m, hm, by simpa [auth] using hq⟩

/-- Stage A only emits its own partial signatures and relayed ones. -/
theorem stageA_unforging : (stageA π).Unforging auth := by
  intro p x h q m hm τ hτ
  simp only [stageA] at hm
  split_ifs at hm
  rcases out_toks hm (by simpa [auth] using hτ) with h1 | h1
  · exact stateOf_toks p x h τ h1
  · exact Or.inl (ownToks_fst h1)

lemma stageB_unforging (hU : Afb.Unforging Af) : (stageB Afb).Unforging Af := by
  intro p x h q m hm τ hτ
  cases x with
  | none => simp [stageB] at hm
  | some v => exact hU p v h q m hm τ hτ

/-- `SyncBA` is unforging (honest parties only emit their own and relayed signatures). -/
theorem syncBA_unforging (hU : Afb.Unforging Af) :
    (syncBA π Afb).Unforging (Auth.seq auth Af) :=
  Protocol.Unforging.seq stageA_unforging (stageB_unforging hU)

/-! ### Theorem 3.1 -/

lemma n_le_of_many {f : ℕ} (hres : 2 * π.t < n) (hf : f ≤ π.t) (hfk : ¬ f + π.k ≤ n) :
    n ≤ 4 * f + 1 := by
  unfold Params.k at hfk; omega

/-- **Theorem 3.1** (explicit constants). Let `t < n/2` and let `Afb` be a fallback protocol
(Byzantine agreement for `t` faults, authenticated, unforging) deciding within `cR · n` rounds in
which every honest party sends at most `cM · n` messages. Then `SyncBA` (built on `Afb`) is an
unforging deterministic protocol such that, against every authenticated static Byzantine adversary
corrupting `f ≤ t` parties:
* it solves Byzantine agreement (termination, strong unanimity, agreement);
* every honest party decides within `(47 + 4 cR)(f + 1)` rounds — `O(f)`;
* honest parties send at most `(100 + 4 cM) · n · (f + 1)` messages in total — `O(n f)`. -/
theorem theorem_3_1 {cR cM : ℕ} (hres : 2 * π.t < n) {Rfb mfb : ℕ}
    (hfb : Fallback Afb Af π.t Rfb mfb) (hR : Rfb ≤ cR * n) (hM : mfb ≤ cM * n) :
    (syncBA π Afb).Unforging (Auth.seq auth Af) ∧
    ∀ sc : Scenario (Fin n) Bool (Msg n ⊕ Mf), sc.byz.ncard ≤ π.t → sc.Reliable →
      sc.AuthValid (G n) (syncBA π Afb) (Auth.seq auth Af) →
      BA sc.input sc.honest (Decides (G n) (syncBA π Afb) sc) ∧
      TerminatesBy (G n) (syncBA π Afb) sc ((47 + 4 * cR) * (sc.byz.ncard + 1)) ∧
      ∀ T, honestMsgs (syncBA π Afb) sc T ≤ (100 + 4 * cM) * n * (sc.byz.ncard + 1) := by
  refine ⟨syncBA_unforging hfb.unforging, fun sc hZ hrel hV => ?_⟩
  obtain ⟨hBA, hT⟩ := syncBA_correct hres hfb sc hZ hrel hV
  set f := sc.byz.ncard
  refine ⟨hBA, fun p hp => ?_, fun T => ?_⟩
  · obtain ⟨r, hr, o, ho⟩ := hT p hp
    refine ⟨r, hr.trans ?_, o, ho⟩
    unfold roundBound
    split_ifs with hfk
    · nlinarith
    · have := n_le_of_many hres hZ hfk
      unfold R0
      nlinarith
  · refine (syncBA_msgs hres hfb sc hZ hrel hV T).trans ?_
    unfold msgBound
    split_ifs with hfk
    · nlinarith
    · have := n_le_of_many hres hZ hfk
      have h1 : n * mfb ≤ n * (cM * n) := Nat.mul_le_mul_left _ hM
      nlinarith

end Podc.FewToManyFaultsBA.Sync
