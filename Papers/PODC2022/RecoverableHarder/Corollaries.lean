import Papers.PODC2022.RecoverableHarder.RuppertSuff
import Papers.PODC2022.RecoverableHarder.TypeS

/-!
# Corollaries 17 and 20, Propositions 18, 19 and 21, Theorem 22

* `recSolvable_one`, `wfSolvable_of_recSolvable`: basic facts (`rcons ≤ cons`).
* `corollary17`: a readable type with consensus number `≥ n ≥ 4` solves RC among `n - 2`;
  `corollary17_bounds`: `cons(T) - 2 ≤ rcons(T) ≤ cons(T)`.
* `prop18`: `cons(T) ≥ 3` ⇒ `rcons(T) ≥ 2` (readable).
* `prop19`, `corollary20`: `T_n` is `n`-discerning, not `(n-1)`-recording; `cons(T_n) = n` and
  `rcons(T_n) < n`.
* `prop21`: `cons(S_n) = rcons(S_n) = n`.
* `theorem22`, `theorem22_ovens`: robustness of the recoverable consensus hierarchy for readable
  types.
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

variable {S : ObjSpec}

/-! ## Basic facts -/

/-- A recoverable consensus algorithm is a wait-free consensus algorithm. -/
theorem wfConsensus_of_recConsensus {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ}
    {A : Alg n T} (h : RecConsensus A) : WFConsensus A :=
  ⟨fun x γ _ => h.agree x γ trivial, fun x γ _ => h.valid x γ trivial,
    fun x e p N _ hinf hN => h.prog x e p N (fun _ => trivial) hinf hN⟩

/-- `rcons(T) ≤ cons(T)`: recoverable consensus is at least as hard as consensus. -/
theorem wfSolvable_of_recSolvable {n : ℕ} (h : RecSolvable S n) : WFSolvable S n := by
  obtain ⟨ιR, ιS, h1, h2, R, hR, A, hA⟩ := h
  exact ⟨ιR, ιS, h1, h2, R, hR, A, wfConsensus_of_recConsensus hA⟩

/-- One process solves recoverable consensus with any type. -/
theorem recSolvable_one (S : ObjSpec) : RecSolvable S 1 :=
  ⟨List Bool × Bool, List Bool, inferInstance, inferInstance, fun _ => Reg,
    fun _ => register_rwLike _ _, trivAlg (mem0 S S.init),
    (solves_admB_true_iff _).1 ((trivAlg_safe _ _ _).solves (trivAlg_ranked _))⟩

/-! ## Corollary 17 and Proposition 18 -/

/-- **Corollary 17.** A deterministic readable type that solves consensus among `n ≥ 4`
processes solves recoverable consensus among `n - 2` processes. -/
theorem corollary17 {n : ℕ} (hn : 4 ≤ n) (hread : S.Readable) (h : WFSolvable S n) :
    RecSolvable S (n - 2) :=
  theorem8 hread (theorem16 hn (isDiscerning_of_wfSolvable (by omega) h))

/-- **Proposition 18.** A deterministic readable type that solves consensus among `3` processes
solves recoverable consensus among `2` processes. -/
theorem prop18_full (hread : S.Readable) (h : WFSolvable S 3) : RecSolvable S 2 :=
  theorem8 hread (prop18 (isDiscerning_of_wfSolvable (by omega) h))

/-- **Corollary 17, second part:** `cons(T) - 2 ≤ rcons(T) ≤ cons(T)` for deterministic readable
types (consensus numbers in the sense of `ConsensusNumber`, `RecConsensusNumber`). -/
theorem corollary17_bounds {c r : ℕ} (hread : S.Readable) (hc : ConsensusNumber S c)
    (hr : RecConsensusNumber S r) : c - 2 ≤ r ∧ r ≤ c := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    by_cases hc4 : 4 ≤ c
    · exact hr.2 (c - 2) hlt (corollary17 hc4 hread hc.1)
    · -- `c ≤ 3`: then `r = 0`, contradicting `rcons ≥ 1`
      exact hr.2 1 (by omega) (recSolvable_one S)
  · by_contra hlt
    push Not at hlt
    exact hc.2 r hlt (wfSolvable_of_recSolvable hr.1)

/-! ## Proposition 19 and Corollary 20 -/

lemma tn_sum {n : ℕ} (hn : 2 ≤ n) : n / 2 - 1 + ((n + 1) / 2 - 1) + 2 = n := by omega

/-- **Proposition 19.** For `n ≥ 4`, `T_n` is `n`-discerning but not `(n-1)`-recording (indeed not
`m`-recording for any `m ≥ n - 1`). -/
theorem prop19 {n : ℕ} (hn : 4 ≤ n) :
    IsDiscerning n (Tn n) ∧ ∀ m, n - 1 ≤ m → ¬ IsRecording m (Tn n) := by
  refine ⟨?_, fun m hm => TT.not_isRecording (by omega) (by omega) (by omega)⟩
  have := TT.isDiscerning (n / 2 - 1) ((n + 1) / 2 - 1)
  rwa [tn_sum (by omega)] at this

/-- **Corollary 20.** For `n ≥ 4`, the readable type `T_n` has consensus number exactly `n`, and
recoverable consensus is not solvable with `T_n` among `n` or more processes:
`rcons(T_n) < cons(T_n) = n`. The upper bound `cons(T_n) ≤ n` uses `TT.not_isDiscerning`, which
the paper does not prove. -/
theorem corollary20 {n : ℕ} (hn : 4 ≤ n) :
    ConsensusNumber (Tn n) n ∧ ∀ m, n ≤ m → ¬ RecSolvable (Tn n) m := by
  refine ⟨⟨theorem3_suff (TT.readable _ _) (prop19 hn).1, fun m hm h => ?_⟩, fun m hm h => ?_⟩
  · exact TT.not_isDiscerning (by omega) (isDiscerning_of_wfSolvable (by omega) h)
  · exact (prop19 hn).2 (m - 1) (by omega) (theorem14 (by omega) h)

/-! ## Proposition 21 -/

/-- **Proposition 21.** For `n ≥ 2`, the readable type `S_n` has consensus number and recoverable
consensus number `n`. -/
theorem prop21 {n : ℕ} (hn : 2 ≤ n) :
    RecConsensusNumber (Sn n) n ∧ ConsensusNumber (Sn n) n := by
  have hrec : RecSolvable (Sn n) n := by
    have := theorem8 (SS.readable (n - 1)) (SS.isRecording (k := n - 1) (by omega))
    rwa [show n - 1 + 1 = n by omega] at this
  have hwf : ∀ m, n < m → ¬ WFSolvable (Sn n) m := fun m hm h =>
    SS.not_isDiscerning (k := n - 1) (by omega) (by omega)
      (isDiscerning_of_wfSolvable (by omega) h)
  exact ⟨⟨hrec, fun m hm h => hwf m hm (wfSolvable_of_recSolvable h)⟩,
    ⟨wfSolvable_of_recSolvable hrec, hwf⟩⟩

/-! ## Theorem 22 (robustness) -/

/-- Recoverable consensus among `n` processes is solvable with objects whose types are in the
family `𝒯` (each object is read/write-like or of a type of `𝒯`). -/
def RecSolvableSet {J : Type} (𝒯 : J → ObjSpec) (n : ℕ) : Prop :=
  ∃ (ι : Type) (_ : DecidableEq ι) (T : ι → ObjSpec)
    (_ : ∀ i, (T i).RWLike ∨ ∃ j, T i = 𝒯 j) (A : Alg n T), RecConsensus A

theorem recSolvableSet_of_recSolvable {J : Type} {𝒯 : J → ObjSpec} {n : ℕ} (j : J)
    (h : RecSolvable (𝒯 j) n) : RecSolvableSet 𝒯 n := by
  obtain ⟨ιR, ιS, _, _, R, hR, A, hA⟩ := h
  exact ⟨ιR ⊕ ιS, inferInstance, withRW R (𝒯 j), fun i => by
    rcases i with i | i
    · exact Or.inl (hR i)
    · exact Or.inr ⟨j, rfl⟩, A, hA⟩

/-- **Theorem 22.** Let `𝒯` be a family of deterministic readable types each of which has
recoverable consensus number at most `r` (no type solves RC among `r + 1` processes). Then the
family does not solve RC among `m ≥ r + 2` processes: `max rcons ≤ rcons(𝒯) ≤ max rcons + 1`
(the lower bound is `recSolvableSet_of_recSolvable`). Paper's proof: Theorem 14 + Theorem 8. -/
theorem theorem22 {J : Type} {𝒯 : J → ObjSpec} (hread : ∀ j, (𝒯 j).Readable) {r : ℕ}
    (hr : 1 ≤ r) (hmax : ∀ j, ¬ RecSolvable (𝒯 j) (r + 1)) {m : ℕ} (hm : r + 2 ≤ m) :
    ¬ RecSolvableSet 𝒯 m := by
  rintro ⟨ι, _, T, hT, A, hA⟩
  obtain ⟨i, hi⟩ := theorem14_alg (by omega) hA
  rcases hT i with hrw | ⟨j, hj⟩
  · exact not_recording_of_rwLike hrw _ hi
  · rw [hj] at hi
    exact hmax j (theorem8 (hread j) (IsRecording.mono (by omega) (by omega) hi))

/-- Robustness without the `+ 1` (from Ovens' Theorem 13): the family does not solve RC among
`m ≥ r + 1` processes either, i.e. `rcons(𝒯) = max_T rcons(T)` (Ovens, PODC'24, Theorem 14). -/
theorem theorem22_ovens {J : Type} {𝒯 : J → ObjSpec} (hread : ∀ j, (𝒯 j).Readable) {r : ℕ}
    (hr : 1 ≤ r) (hmax : ∀ j, ¬ RecSolvable (𝒯 j) (r + 1)) {m : ℕ} (hm : r + 1 ≤ m) :
    ¬ RecSolvableSet 𝒯 m := by
  rintro ⟨ι, _, T, hT, A, hA⟩
  obtain ⟨i, hi⟩ := theorem13 (by omega) hA
  rcases hT i with hrw | ⟨j, hj⟩
  · exact not_recording_of_rwLike hrw _ hi
  · rw [hj] at hi
    exact hmax j (theorem8 (hread j) (IsRecording.mono (by omega) hm hi))

/-- The hypothesis `dffr` of Ovens' Theorem 14 (PODC'24) is DFFR's Theorem 8, now proved:
Ovens' robustness theorem holds unconditionally. -/
theorem ovens_theorem14 {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}
    (hread : ∀ i, (T i).Readable) (hn : 2 ≤ n) (hA : RecConsensus A) :
    ∃ i, RecSolvable (T i) n :=
  Ovens.theorem14 (fun _ _ h1 h2 => theorem8 h1 h2) hread hn hA

end Podc.RecoverableHarder
