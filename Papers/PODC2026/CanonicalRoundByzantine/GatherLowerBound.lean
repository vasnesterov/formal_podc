import Papers.PODC2026.CanonicalRoundByzantine.Main
import Papers.PODC2026.CanonicalRoundByzantine.Gather

/-!
# Corollary 15 of [AFW26]: canonical-round gather

Algorithm 4 with `R = 1` (crusader agreement from one call to gather, Lines 1–3) adds no
communication: given a canonical-round gather algorithm `alg`, the crusader agreement algorithm
`caOfGather alg` has the same messages and decides `line2 (S)` as soon as gather returns `S`. Its
executions are those of `alg` (`exec_caOfGather`), so it has the same round complexity, it is
communication-closed if `alg` is, and it is safe for crusader agreement if `alg` is safe for gather
(`safe_caOfGather`, the argument of Theorem 14 at every prefix of an execution). Theorem 1 /
Corollary 6 and Corollary 8 then give Corollary 15.

Gather is specified at every prefix (`gatherSpec`): agreement, validity, and a common core of size
`n - f` contained in the outputs of all correct processes that have returned so far.
-/

namespace Podc2026.CanonicalRound

open Cslib.Byzantine.CanonicalRounds Finset
open Podc2026.CanonicalRound.Gather (cnt lemma11 heavy_unique exists_not_mem_of_cnt
  cnt_ge_of_functional)

variable {n : ℕ} {V R M : Type*} [DecidableEq V]

/-- The gather specification (Section 4.2), required of the outputs returned so far. -/
def gatherSpec (f : ℕ) : Spec n V (Finset (Fin n × V)) := fun I F d =>
  (∀ i ∉ F, ∀ j ∉ F, ∀ Si Sj k a b, d i = some Si → d j = some Sj → (k, a) ∈ Si → (k, b) ∈ Sj →
    a = b) ∧
  (∀ i ∉ F, ∀ j ∉ F, ∀ Si a, d i = some Si → (j, a) ∈ Si → a = I j) ∧
  (∃ SC : Finset (Fin n × V), SC.card = n - f ∧ ∀ i ∉ F, ∀ Si, d i = some Si → SC ⊆ Si)

open Classical in
/-- Line 2 of Algorithm 4 (and the decision of Line 3 for `R = 1`): decide `(v, 1)` if some value
`v` appears `|S| - f` times in `S`, otherwise `(⊥, 0)`. -/
noncomputable def line2 (f : ℕ) (S : Finset (Fin n × V)) : Option V × ℕ :=
  if h : ∃ v, S.card - f ≤ cnt S v then (some h.choose, 1) else (none, 0)

/-- Algorithm 4 for `R = 1` on top of a canonical-round gather algorithm. -/
noncomputable def caOfGather (f : ℕ) (alg : CanonAlg n V R M (Finset (Fin n × V))) :
    CanonAlg n V R M (Option V × ℕ) :=
  ⟨alg.msg, fun p v h => (alg.dec p v h).map (line2 f)⟩

variable (f : ℕ) (alg : CanonAlg n V R M (Finset (Fin n × V)))

theorem exec_caOfGather (I : Fin n → V) (ρ : Tape n R) (A : Adversary n R M) (k : ℕ) :
    (caOfGather f alg).exec f I ρ A k = alg.exec f I ρ A k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [CanonAlg.exec, ih]; rfl

theorem findSome?_map_map {α β γ : Type*} (F : α → Option β) (g : β → γ) :
    ∀ L : List α, L.findSome? (fun x => (F x).map g) = (L.findSome? F).map g
  | [] => rfl
  | x :: L => by
    rw [List.findSome?_cons, List.findSome?_cons]
    rcases F x with _ | b
    · exact findSome?_map_map F g L
    · rfl

theorem decision_caOfGather (p : Fin n) (v : V) (l : Log n R M) :
    (caOfGather f alg).decision p v l = (alg.decision p v l).map (line2 f) :=
  findSome?_map_map _ _ _

theorem decidesBy_caOfGather {p : Fin n} {v : V} {r : ℕ} {l : Log n R M} :
    (caOfGather f alg).DecidesBy p v r l ↔ alg.DecidesBy p v r l := by
  simp [CanonAlg.DecidesBy, caOfGather]

theorem rounds_caOfGather (I : Fin n → V) (ρ : Tape n R) (A : Adversary n R M) :
    (caOfGather f alg).rounds f I ρ A = alg.rounds f I ρ A := by
  simp only [CanonAlg.rounds, CanonAlg.AllDecideBy, exec_caOfGather, decidesBy_caOfGather]

theorem allDecide_caOfGather (I : Fin n → V) (ρ : Tape n R) (A : Adversary n R M) :
    (caOfGather f alg).AllDecide f I ρ A ↔ alg.AllDecide f I ρ A := by
  simp [CanonAlg.AllDecide, exec_caOfGather, decision_caOfGather]

theorem admissible_caOfGather (I : Fin n → V) (A : Adversary n R M) :
    (caOfGather f alg).Admissible f I A ↔ alg.Admissible f I A := by
  simp [CanonAlg.Admissible, CanonAlg.Fair, exec_caOfGather]

theorem commClosed_caOfGather (h : alg.CommClosed) : (caOfGather f alg).CommClosed :=
  fun p v l l' hl => ⟨(h p v l l' hl).1, by simp [caOfGather, (h p v l l' hl).2]⟩

theorem line2_spec (S : Finset (Fin n × V)) :
    (line2 f S = (none, 0) ∧ ¬ ∃ v, S.card - f ≤ cnt S v) ∨
      ∃ v, line2 f S = (some v, 1) ∧ S.card - f ≤ cnt S v := by
  unfold line2
  split_ifs with h
  · exact Or.inr ⟨_, rfl, h.choose_spec⟩
  · exact Or.inl ⟨rfl, h⟩

/-- The crusader agreement properties from the gather properties at one prefix (the argument of
Theorem 14 of [AFW26]). -/
theorem cc_of_gather (h3f : 3 * f < n) (I : Fin n → V) (F : Finset (Fin n)) (hF : F.card ≤ f)
    (d : Fin n → Option (Finset (Fin n × V))) (hg : gatherSpec f I F d) :
    connectedConsensusSpec 1 I F (fun p => (d p).map (line2 f)) := by
  obtain ⟨hag, hval, SC, hSC, hcore⟩ := hg
  -- a heavy value in an output is heavy in the core
  have heavy : ∀ i ∉ F, ∀ Si u, d i = some Si → Si.card - f ≤ cnt Si u → SC.card - f ≤ cnt SC u :=
    fun i hi Si u hd hu => lemma11 (hcore i hi Si hd) hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp a g hd
    obtain ⟨Si, hSi, hpa⟩ := Option.map_eq_some_iff.1 hd
    rcases line2_spec f Si with ⟨h, -⟩ | ⟨v, h, -⟩
    · rw [h] at hpa; simp only [Prod.mk.injEq] at hpa; left; exact ⟨hpa.1.symm, hpa.2.symm⟩
    · rw [h] at hpa; simp only [Prod.mk.injEq] at hpa; right
      exact ⟨by rw [← hpa.1]; simp, by omega, by omega⟩
  · intro p hp q hq a g b h hdp hdq
    obtain ⟨Si, hSi, hpa⟩ := Option.map_eq_some_iff.1 hdp
    obtain ⟨Sj, hSj, hqb⟩ := Option.map_eq_some_iff.1 hdq
    have gr : ∀ S : Finset (Fin n × V), ∀ a g, line2 f S = (a, g) → g ≤ 1 := by
      intro S a g hS
      rcases line2_spec f S with ⟨h, -⟩ | ⟨v, h, -⟩ <;> rw [h] at hS <;> simp at hS <;> omega
    refine ⟨by have := gr _ _ _ hpa; omega, by have := gr _ _ _ hqb; omega, ?_⟩
    rcases line2_spec f Si with ⟨h1, -⟩ | ⟨u, h1, hu⟩
    · left; rw [h1] at hpa; simp at hpa; exact hpa.1.symm
    rcases line2_spec f Sj with ⟨h2, -⟩ | ⟨w, h2, hw⟩
    · right; left; rw [h2] at hqb; simp at hqb; exact hqb.1.symm
    right; right
    rw [h1] at hpa; rw [h2] at hqb
    simp only [Prod.mk.injEq] at hpa hqb
    rw [← hpa.1, ← hqb.1, heavy_unique (by omega) (heavy p hp Si u hSi hu)
      (heavy q hq Sj w hSj hw)]
  · intro p hp v g hd
    obtain ⟨Si, hSi, hpa⟩ := Option.map_eq_some_iff.1 hd
    rcases line2_spec f Si with ⟨h1, -⟩ | ⟨u, h1, hu⟩
    · rw [h1] at hpa; simp at hpa
    rw [h1] at hpa; simp only [Prod.mk.injEq, Option.some.injEq] at hpa
    obtain ⟨rfl, -⟩ := hpa
    have hcard := card_le_card (hcore p hp Si hSi)
    obtain ⟨j, hj, hjS⟩ := exists_not_mem_of_cnt (S := Si) (F := F) (w := u) (by omega)
    exact ⟨j, hj, (hval p hp j hj Si u hSi hjS).symm⟩
  · intro p hp a g hd hall
    obtain ⟨Si, hSi, hpa⟩ := Option.map_eq_some_iff.1 hd
    have hfun : ∀ k a b, (k, a) ∈ Si → (k, b) ∈ Si → a = b :=
      fun k a b ha hb => hag p hp p hp Si Si k a b hSi hSi ha hb
    have hcorr : ∀ j a, j ∉ F → (j, a) ∈ Si → a = I p := fun j a hj ha =>
      (hval p hp j hj Si a hSi ha).trans (hall j hj p hp)
    have hc := cnt_ge_of_functional hfun hcorr
    rcases line2_spec f Si with ⟨-, hno⟩ | ⟨u, h1, -⟩
    · exact absurd ⟨I p, by omega⟩ hno
    · rw [h1] at hpa; simp only [Prod.mk.injEq] at hpa; exact hpa.2.symm

theorem safe_caOfGather (h3f : 3 * f < n) (hsafe : alg.Safe f (gatherSpec f)) :
    (caOfGather f alg).Safe f (connectedConsensusSpec 1) := by
  intro I A hA ρ k
  rw [admissible_caOfGather] at hA
  have := cc_of_gather f h3f I A.F hA.1 _ (hsafe I A hA ρ k)
  simpa [exec_caOfGather, decision_caOfGather] using this

/-- **Corollary 15 of [AFW26].** For `3f < n ≤ 5f` (and at least two input values), any
canonical-round algorithm for gather (deterministic, or for any tape) has, for every `K`, an
admissible execution in which some correct process does not terminate by round `K`. -/
theorem corollary15 [Nonempty R] (h3f : 3 * f < n) (h5f : n ≤ 5 * f) {v v' : V} (hv : v ≠ v')
    (hsafe : alg.Safe f (gatherSpec f)) (K : ℕ) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, (K : ℕ∞) < alg.rounds f I ρ A := by
  obtain ⟨I, A, hA, h⟩ := connectedConsensus_unbounded le_rfl hv (caOfGather f alg) h3f h5f
    (safe_caOfGather f alg h3f hsafe) K
  exact ⟨I, A, (admissible_caOfGather f alg I A).1 hA,
    fun ρ => rounds_caOfGather f alg I ρ A ▸ h ρ⟩

/-- **Corollary 15 of [AFW26]**, second part: no communication-closed canonical-round gather
algorithm for `3f < n ≤ 5f`. -/
theorem corollary15_commClosed [Nonempty R] (h3f : 3 * f < n) (h5f : n ≤ 5 * f) {v v' : V}
    (hv : v ≠ v') (hcc : alg.CommClosed) :
    ¬ (alg.Safe f (gatherSpec f) ∧
      ∀ I (A : Adversary n R M), alg.Admissible f I A → ∀ ρ, alg.AllDecide f I ρ A) := by
  rintro ⟨hs, ht⟩
  exact connectedConsensus_not_commClosed le_rfl hv (caOfGather f alg)
    (commClosed_caOfGather f alg hcc) h3f h5f ⟨safe_caOfGather f alg h3f hs,
      fun I A hA ρ => (allDecide_caOfGather f alg I ρ A).2
        (ht I A ((admissible_caOfGather f alg I A).1 hA) ρ)⟩

end Podc2026.CanonicalRound
