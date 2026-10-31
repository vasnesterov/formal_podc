import Papers.PODC2011.SimultaneousAllCaseOptimal.FastProtocols

/-!
# §4: all-case optimality (Lemma 4, Theorems 6 and 8)

* The similarity graph of a protocol at time `k` (`Similar`, `Connected`): runs are adjacent if
  some process survives round `k` in both and has the same local state (input and history) at
  time `k`.
* **Lemma 4** (`lemma4`): in a protocol solving `sim(T)`, if the nonfaulty processes decide at time
  `k` in `r`, they decide at time `k` in every run connected to `r` at time `k`.
* Lemma 5 (Dwork–Moses) and Lemma 7 (Moses–Raynal) are cited, not proved, in the paper; here they
  are hypotheses (`Lemma5Hyp`, `Lemma7Hyp`). Lemma 5 is **false** when `t = n − 1`
  (`lemma5_false`, `Lemma5False.lean`).
* **Theorem 6** (`theorem6`) and **Theorem 8** (`theorem8`): given Lemma 5 (resp. 7) and the
  ConCon properties, `Opt(A, k̂)` is all-case optimal when `k̂` is a worst-case lower bound and `A`
  solves `T` within `k̂` rounds.
* The by-product claimed in the abstract (`beat_lower_bound`): a simultaneous protocol that beats
  the worst-case lower bound in some run decides at a time `k ≥ t + 1 − W(F)` in that run.
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I M O MC : Type} [Fintype P]

/-- Two runs are indistinguishable to some process at time `k`: it survives round `k` in both and
has the same local state (input and history) at time `k` in both. -/
def Similar (A : Protocol P I M O) (k : ℕ) (r r' : Run P I) : Prop :=
  ∃ p, r.Alive p k ∧ r'.Alive p k ∧ r.input p = r'.input p ∧ hist A r k p = hist A r' k p

/-- `r ∼ₖ r'`: `r` and `r'` are in the same connected component of the similarity graph of `A` at
time `k`, whose vertices are the runs of `A` (at most `t` crashes, inputs in `T.inputs`). -/
def Connected (A : Protocol P I M O) (T : Task P I O) (t k : ℕ) (r r' : Run P I) : Prop :=
  Relation.ReflTransGen (fun r₁ r₂ => T.IsRun t r₁ ∧ T.IsRun t r₂ ∧ Similar A k r₁ r₂) r r'

/-- **Lemma 4.** Let `A` solve `sim(T)` (with `t < n`). If the nonfaulty processes decide at time
`k` in a run `r`, they decide at time `k` in every run `r'` with `r' ∼ₖ r`.
The paper's proof says that the process `p` witnessing an edge "has not failed" and hence decides
at time `k`; `p` only survives round `k` (it may crash later). That `p` decides at time `k` anyway is
`SolvesSim.decides_of_alive`. -/
theorem lemma4 {A : Protocol P I M O} {T : Task P I O} {t : ℕ} (ht : t < Fintype.card P)
    (hA : SolvesSim A T t) {k : ℕ} {r r' : Run P I} (hr : T.IsRun t r) (h : DecideAll A r k)
    (hc : Connected A T t k r r') : DecideAll A r' k := by
  induction hc with
  | refl => exact h
  | tail _ hstep ih =>
    obtain ⟨hr₁, hr₂, p, hp₁, hp₂, hin, hh⟩ := hstep
    obtain ⟨q, hq⟩ := hr₁.exists_correct ht
    obtain ⟨d, hd⟩ := ih q hq
    obtain ⟨dp, hdp⟩ := hA.decides_of_alive hr₁ hd hp₁
    have hdp' := decides_congr hin hh hp₂ hdp
    intro q' hq'
    obtain ⟨m, d', hd'⟩ := hA.complete _ hr₂ q' hq'
    have := hA.simultaneous _ hr₂ p q' k m dp d' hdp' hd'
    subst this
    exact ⟨d', hd'⟩

/-- **Lemma 5** of the paper ([DM90, MR08]), as a hypothesis on the task's input vectors and `t`:
for every protocol `A`, if round `k` is premature in two runs of `A`, the runs are connected at
time `k`. (The paper states it for complete sets of input vectors and `t ≤ n − 1`; it is false for
`t = n − 1`, see `lemma5_false`.) -/
def Lemma5Hyp (T : Task P I O) (t : ℕ) : Prop :=
  ∀ (M : Type) (A : Protocol P I M O) (k : ℕ) (r r' : Run P I), T.IsRun t r → T.IsRun t r' →
    Premature r t k → Premature r' t k → Connected A T t k r r'

/-- **Lemma 7** of the paper ([MR08]) for `c`-coverable input sets, as a hypothesis: the
conclusion of Lemma 5 for `k ≤ t + 1 − c`. -/
def Lemma7Hyp (T : Task P I O) (t c : ℕ) : Prop :=
  ∀ (M : Type) (A : Protocol P I M O) (k : ℕ) (r r' : Run P I), T.IsRun t r → T.IsRun t r' →
    k + c ≤ t + 1 → Premature r t k → Premature r' t k → Connected A T t k r r'

/-- `k̂` is a worst-case lower bound for `T`: no protocol solves `T` with every nonfaulty process
deciding by a time `k < k̂` in every run. -/
def WorstCaseLB (T : Task P I O) (t kh : ℕ) : Prop :=
  ∀ (M : Type) (A : Protocol P I M O) (k : ℕ), SolvesWithin A T t k → kh ≤ k

/-- All-case optimality (§4): `X` solves `sim(T)`, and for every input vector and failure
pattern, `X` decides no later than any other protocol solving `sim(T)` does in the run with the
same input vector and failure pattern. -/
def AllCaseOptimal {MX : Type} (X : Protocol P I MX O) (T : Task P I O) (t : ℕ) : Prop :=
  SolvesSim X T t ∧ ∀ (M : Type) (B : Protocol P I M O), SolvesSim B T t →
    ∀ r, T.IsRun t r → ∀ k, DecideAll B r k → ∃ k' ≤ k, DecideAll X r k'

/-- The heart of the proofs of Theorems 6 and 8: given a simultaneous protocol `B` deciding at a
premature time `k₀` in some run `r`, `B̂ = Opt(B, k₀)` solves `T` within `k₀` rounds, provided the
runs of `B̂` in which `k₀` is premature are connected to `r` at time `k₀`. -/
lemma solvesWithin_opt {C : CCProtocol P I MC} {B : Protocol P I M O} {T : Task P I O} {t : ℕ}
    (ht : t < Fintype.card P) (hC : IsConCon C T t) (hB : SolvesSim B T t) {r : Run P I}
    (hr : T.IsRun t r) {k₀ : ℕ} (hdec : DecideAll B r k₀) (hk₀ : Premature r t k₀)
    (hconn : ∀ r', T.IsRun t r' → Premature r' t k₀ → Connected (Opt C B T k₀) T t k₀ r r') :
    SolvesWithin (Opt C B T k₀) T t k₀ := by
  obtain ⟨h2, h2a, -⟩ := theorem2 hC hB.toSolves
  have hsim : SolvesSim (Opt C B T k₀) T t := else_solvesSim (delay_solvesSim hB k₀) h2
  -- `B̂` decides at `k₀` in `r`
  have hr0 : DecideAll (Opt C B T k₀) r k₀ := by
    intro p hp
    obtain ⟨d, hd⟩ := hdec p hp
    refine ⟨d, decides_else_of_left (decides_delay_iff.2 ⟨hd.alive, k₀, hd, by simp⟩)
      fun m' hm' => raw_concon_lt hC hr (hd.alive.mono hm'.le) ?_⟩
    unfold Premature at hk₀; omega
  refine { toSolves := hsim.toSolves, within := fun r' hr' p hp => ?_ }
  by_cases hk1 : t + 1 - r'.waste ≤ k₀
  · obtain ⟨d, hd⟩ := h2a r' hr' p (Run.alive_of_not_faulty hp _)
    obtain ⟨m, hm, d', hd'⟩ := exists_decides_else_le_right (A := Delay B k₀) hd
    exact ⟨m, by omega, d', hd'⟩
  · have hpre : Premature r' t k₀ := by unfold Premature; omega
    obtain ⟨d, hd⟩ := lemma4 ht hsim hr hr0 (hconn r' hr' hpre) p hp
    exact ⟨k₀, le_rfl, d, hd⟩

/-- **Theorem 6 (all-case optimality).** Let `k̂` be a worst-case lower bound for `T` and let `A`
solve `T` within `k̂` rounds. Assume Lemma 5 (stated in the paper for complete input sets) and a
continuous-consensus protocol `C` with the ConCon properties. Then
`Opt(A, k̂) = Delay(A, k̂) else ConCon(A)` is all-case optimal for `sim(T)`. -/
theorem theorem6 {C : CCProtocol P I MC} {A : Protocol P I M O} {T : Task P I O} {t kh : ℕ}
    (ht : t < Fintype.card P) (hC : IsConCon C T t) (h5 : Lemma5Hyp T t)
    (hLB : WorstCaseLB T t kh) (hA : SolvesWithin A T t kh) :
    AllCaseOptimal (Opt C A T kh) T t := by
  obtain ⟨h3, h3a⟩ := theorem3 hC hA
  refine ⟨h3, fun MB B hB r hr k₀ hdec => ?_⟩
  by_cases hle : min kh (t + 1 - r.waste) ≤ k₀
  · exact ⟨_, hle, fun p hp => h3a r hr p (Run.alive_of_not_faulty hp _)⟩
  · exfalso
    have hk₀ : Premature r t k₀ := by unfold Premature; omega
    have := solvesWithin_opt ht hC hB hr hdec hk₀ fun r' hr' hpre =>
      h5 _ _ k₀ r r' hr hr' hk₀ hpre
    have := hLB _ _ _ this
    omega

/-- **Theorem 8 (all-case optimality, `c`-coverable inputs).** As Theorem 6, with Lemma 7 for
`c` instead of Lemma 5, under the extra hypothesis `k̂ ≤ t + 2 − c`. -/
theorem theorem8 {C : CCProtocol P I MC} {A : Protocol P I M O} {T : Task P I O} {t kh c : ℕ}
    (ht : t < Fintype.card P) (hC : IsConCon C T t) (h7 : Lemma7Hyp T t c)
    (hkc : kh + c ≤ t + 2) (hLB : WorstCaseLB T t kh) (hA : SolvesWithin A T t kh) :
    AllCaseOptimal (Opt C A T kh) T t := by
  obtain ⟨h3, h3a⟩ := theorem3 hC hA
  refine ⟨h3, fun MB B hB r hr k₀ hdec => ?_⟩
  by_cases hle : min kh (t + 1 - r.waste) ≤ k₀
  · exact ⟨_, hle, fun p hp => h3a r hr p (Run.alive_of_not_faulty hp _)⟩
  · exfalso
    have hk₀ : Premature r t k₀ := by unfold Premature; omega
    have := solvesWithin_opt ht hC hB hr hdec hk₀ fun r' hr' hpre =>
      h7 _ _ k₀ r r' hr hr' (by omega) hk₀ hpre
    have := hLB _ _ _ this
    omega

/-- **"Beating the worst-case bound is as hard as simultaneous consensus"** (abstract, end of the
proof of Theorem 6): under the hypotheses of Theorem 6, if a protocol solving `sim(T)` decides at
time `k < k̂` in a run with failure pattern `F`, then `k ≥ t + 1 − W(F)`. -/
theorem beat_lower_bound {C : CCProtocol P I MC} {B : Protocol P I M O} {T : Task P I O}
    {t kh : ℕ} (ht : t < Fintype.card P) (hC : IsConCon C T t) (h5 : Lemma5Hyp T t)
    (hLB : WorstCaseLB T t kh) (hB : SolvesSim B T t) {r : Run P I} (hr : T.IsRun t r) {k : ℕ}
    (hdec : DecideAll B r k) (hk : k < kh) : t + 1 - r.waste ≤ k := by
  by_contra hlt
  have hk₀ : Premature r t k := by unfold Premature; omega
  have := solvesWithin_opt ht hC hB hr hdec hk₀ fun r' hr' hpre => h5 _ _ k r r' hr hr' hk₀ hpre
  have := hLB _ _ _ this
  omega

end Podc.SimultaneousAllCaseOptimal
