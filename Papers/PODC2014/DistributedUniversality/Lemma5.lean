import Papers.PODC2014.DistributedUniversality.NonVacuity

/-!
# Lemma 5: in every round, some operations are committed

Lemma 5 of Raynal–Stainer–Taubenfeld (PODC 2014) states, for the construction of Figure 1, that in
every round `r` some process obtains `(commit, op)` from the adopt-commit object of an object `op`
was decided for by `kSC[r]`.  The proofs of Theorem 2 (Figure 2) and Theorem 4(a) (Section 4.3,
`(k, ℓ)`-SC objects) reuse its argument in the generalized form: in every round at least `ℓ`
objects have an operation committed by some process (or, in the contention-aware variant, all `k`
objects, when some process skipped lines 2M–4M).

The proof is by the inductive invariant `NonVacuity.Inv`: the first process `p` to finish its
adopt-commit invocations on its `ℓ` decided objects (ghost `firstL r`) got commit on all of them,
because before that moment every invocation of these adopt-commit objects comes from a process
still in its decided block, which proposes the value agreed by `SC[r]`, so the no-conflict
property applies.
-/

namespace Podc.DistributedUniversality.Lemma5

open Podc.DistributedUniversality NonVacuity

variable {n k : ℕ} {M : Mode}

/-- Process `p` has completed the adopt-commit part (lines N1–4 / N1–4M) of round `r`. -/
def DoneAC (s : St n k) (p : Fin n) (r : ℕ) : Prop :=
  r < (s.loc p).r ∨ (r = (s.loc p).r ∧ ((∃ q, (s.loc p).pc = .collect q) ∨
    (s.loc p).pc = .loc ∨ (∃ m, (s.loc p).pc = .upd m) ∨ (s.loc p).pc = .write))

theorem past_of_doneAC {s : St n k} (hI : Inv M s) {r : ℕ} (hr : 1 ≤ r) {p : Fin n}
    (hd : DoneAC s p r) : Past M s p r := by
  have h := hI.proc p
  rcases hd with hd | ⟨rfl, hd⟩
  · exact h.past _ hr hd
  · have hp := h.pc
    rcases hd with ⟨q, hq⟩ | hq | ⟨m, hq⟩ | hq <;> rw [hq] at hp
    · exact hp.2.2
    · exact hp.2
    · exact hp.2.2
    · exact hp.2

/-- **Lemma 5, generalized form (used in the proofs of Theorem 2 and Theorem 4(a)).**
Assume `1 ≤ ℓ ≤ k`.  In every reachable state, if some process has completed the adopt-commit part
of round `r ≥ 1`, then there is a set `S` of at least `ℓ` objects such that, for each `x ∈ S`, some
process obtained a final pair `(commit, op)` for `x` in round `r` (`fin`: the response of line N1
if the process skipped lines 2M–4M, otherwise the response of line 3/4 (3M/4M)). -/
theorem lemma5_general (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) {s : St n k} (hs : Reachable M s)
    {r : ℕ} (hr : 1 ≤ r) {p : Fin n} (hp : DoneAC s p r) :
    ∃ S : Finset (Fin k), M.ℓ ≤ S.card ∧ ∀ x ∈ S, ∃ j v, fin M s r x j = some (true, v) := by
  have hI := inv_reachable hℓ (by omega) hs
  by_cases hsk : ∃ j, skipped M s r j
  · obtain ⟨j, hj⟩ := hsk
    refine ⟨Finset.univ, by simpa using hℓk, fun x _ => ?_⟩
    obtain ⟨v, hv⟩ := hj.2 x
    exact ⟨j, v, by simp [fin, hj, hv]⟩
  · push Not at hsk
    rcases past_of_doneAC hI hr hp with h | h
    · exact absurd h (hsk p)
    · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
      obtain ⟨d, hd, hc⟩ := hI.l1 r q hq
      refine ⟨Finset.univ.filter (fun x => (d x).isSome), ((hI.sc r).card q d hd).ge,
        fun x hx => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hx
      exact ⟨q, v, by simp [fin, hsk q, hc x v hv]⟩

/-- **Lemma 5** (the construction of Figure 1: `k`-SC objects, `ℓ = 1`, no contention-aware
lines).  If some process has completed lines 1–4 of round `r ≥ 1`, then some process `pᵢ`
obtained from `kSC[r]` a pair `(x, op)` and then `(commit, op)` from `AC[r][x]`. -/
theorem lemma5 (hM : M.ℓ = 1) (hca : M.ca = false) (hk : 0 < k) {s : St n k}
    (hs : Reachable M s) {r : ℕ} (hr : 1 ≤ r) {p : Fin n} (hp : DoneAC s p r) :
    ∃ i d x op, s.scR r i = some d ∧ d x = some op ∧ s.acR r true x i = some (true, op) := by
  have hI := inv_reachable (M := M) (by omega) hk hs
  rcases past_of_doneAC hI hr hp with h | h
  · rw [skipped, hca] at h; simp at h
  · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨d, hd, hc⟩ := hI.l1 r q hq
    have hcard := (hI.sc r).card q d hd
    rw [hM] at hcard
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter
      (fun x => (d x).isSome)).card)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp hx
    exact ⟨q, d, x, op, hd, hop, hc x op hop⟩

end Podc.DistributedUniversality.Lemma5
