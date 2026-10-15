import Papers.PODC2025.ByzantineStableMatching.Problem
import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel

/-!
# Lemma 1: Byzantine broadcast suffices for bSM

**Lemma 1** of Constantinescu, Dufay, Ghinea, Wattenhofer, *Byzantine Stable Matching* (PODC 2025):
whenever Byzantine broadcast is available, bSM is solvable. Every party distributes its preference list
by Byzantine broadcast (one instance per party, run in parallel = interactive consistency, see
`Cslib.Byzantine.LockStep.IC_of_BB`); then every party runs Gale–Shapley offline on the agreed vector of
lists and outputs its partner.

* `offline`: the offline step (partner index of a party in the Gale–Shapley matching of a vector of
  lists).
* `offlineMatch`: spec-level statement — any decision relation satisfying `IC` yields, after the
  offline step, a decision relation satisfying `bSM`. Reusable for other protocols that end with an
  agreed vector of lists.
* `bSM_of_IC`, `bSM_of_IC_auth`, `lemma1`, `lemma1_auth`.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Cslib.StableMatching Sum

variable {k : ℕ}

/-- The Gale–Shapley matching (`L` proposing) of a vector of preference lists: `inl i` has list
`d (inl i)`, `inr j` has list `d (inr j)`. -/
def gsOfVector (d : Party k → Equiv.Perm (Fin k)) : Fin k ≃ Fin k :=
  galeShapley (Prefs.ofPerms (fun i => d (inl i)) (fun j => d (inr j))) rfl

/-- The offline step: the output of party `p` given the agreed vector of lists `d`. -/
def offline : Party k → (Party k → Equiv.Perm (Fin k)) → Option (Fin k)
  | inl i, d => some (gsOfVector d i)
  | inr j, d => some ((gsOfVector d).symm j)

@[simp] lemma offline_inl (i : Fin k) (d : Party k → Equiv.Perm (Fin k)) :
    offline (inl i) d = some (gsOfVector d i) := rfl

@[simp] lemma offline_inr (j : Fin k) (d : Party k → Equiv.Perm (Fin k)) :
    offline (inr j) d = some ((gsOfVector d).symm j) := rfl

/-- Agreeing on a vector of lists whose honest entries are the honest inputs (interactive
consistency) and then running Gale–Shapley offline solves bSM. -/
theorem offlineMatch (x : Party k → Equiv.Perm (Fin k)) (H : Set (Party k))
    (decV : Party k → (Party k → Equiv.Perm (Fin k)) → Prop) (hIC : IC x H decV) :
    bSM k x H (fun p o => ∃ d, decV p d ∧ offline p d = o) := by
  obtain ⟨hterm, hvalid, hagree⟩ := hIC
  refine ⟨⟨fun p hp => ?_, fun i j hi hj => ?_, ?_⟩, ?_⟩
  · obtain ⟨d, hd⟩ := hterm p hp
    exact ⟨_, d, hd, rfl⟩
  · constructor
    · rintro ⟨d, hd, hdo⟩
      obtain ⟨e, he⟩ := hterm _ hj
      obtain rfl := hagree _ hi _ hj _ _ hd he
      refine ⟨d, he, ?_⟩
      simp only [offline_inl, Option.some.injEq] at hdo
      simp [← hdo]
    · rintro ⟨d, hd, hdo⟩
      obtain ⟨e, he⟩ := hterm _ hi
      obtain rfl := hagree _ hi _ hj _ _ he hd
      refine ⟨_, he, ?_⟩
      simp only [offline_inr, Option.some.injEq] at hdo
      simp [← hdo]
  · rintro p q hp hq hpq z z' ⟨d, hd, hdz⟩ ⟨e, he, hez⟩
    obtain rfl := hagree p hp q hq d e hd he
    rcases p with i | i <;> rcases q with i' | i' <;>
      simp only [offline_inl, offline_inr, Option.some.injEq] at hdz hez <;> subst hdz hez <;>
      simp only [partner, ne_eq, reduceCtorEq, not_false_eq_true, inl.injEq, inr.injEq,
        EmbeddingLike.apply_eq_iff_eq] <;> exact fun h => hpq (by rw [h])
  · rintro i j _ _ hi hj ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩ ⟨h₁, h₂⟩
    obtain rfl := hagree _ hi _ hj _ _ hd he
    have hxi : d (inl i) = x (inl i) := hvalid _ hi d hd _ hi
    have hxj : d (inr j) = x (inr j) := hvalid _ hi d hd _ hj
    apply galeShapley_isStable (Prefs.ofPerms (fun i => d (inl i)) (fun j => d (inr j))) rfl i j
    refine ⟨?_, ?_⟩
    · simp only [Prefs.ofPerms_rankL]
      rw [hxi]
      exact h₁
    · simp only [Prefs.ofPerms_rankR]
      rw [hxj]
      exact h₂

/-- The bSM protocol obtained from an interactive-consistency protocol by the offline step. -/
noncomputable def Protocol.ofIC {M : Type*}
    (alg : Protocol (Party k) (Equiv.Perm (Fin k)) M (Party k → Equiv.Perm (Fin k))) :
    Protocol (Party k) (Equiv.Perm (Fin k)) M (Option (Fin k)) :=
  alg.mapOutput offline

lemma decides_ofIC_eq {M : Type*} (G : SimpleGraph (Party k))
    (alg : Protocol (Party k) (Equiv.Perm (Fin k)) M (Party k → Equiv.Perm (Fin k)))
    (s : Scenario (Party k) (Equiv.Perm (Fin k)) M) :
    Decides G (Protocol.ofIC alg) s = fun p o => ∃ d, Decides G alg s p d ∧ offline p d = o := by
  funext p o
  exact propext (decides_mapOutput G alg offline s p o)

/-- If interactive consistency on preference lists is solvable, so is bSM. -/
theorem bSM_of_IC {G : SimpleGraph (Party k)} {Z : AdvStructure (Party k)}
    (h : Solvable G Z (IC : Spec (Party k) (Equiv.Perm (Fin k)) (Party k → Equiv.Perm (Fin k)))) :
    Solvable G Z (bSM k) := by
  obtain ⟨M, alg, halg⟩ := h
  refine ⟨M, Protocol.ofIC alg, fun s hZ hrel => ?_⟩
  rw [decides_ofIC_eq]
  exact offlineMatch _ _ _ (halg s hZ hrel)

/-- Authenticated version of `bSM_of_IC`. -/
theorem bSM_of_IC_auth {G : SimpleGraph (Party k)} {Z : AdvStructure (Party k)}
    (h : SolvableAuth G Z
      (IC : Spec (Party k) (Equiv.Perm (Fin k)) (Party k → Equiv.Perm (Fin k)))) :
    SolvableAuth G Z (bSM k) := by
  obtain ⟨M, S, A, alg, hU, halg⟩ := h
  refine ⟨M, S, A, Protocol.ofIC alg, Protocol.Unforging.mapOutput alg offline hU, fun s hZ hrel hV => ?_⟩
  rw [decides_ofIC_eq]
  exact offlineMatch _ _ _
    (halg s hZ hrel ((Scenario.authValid_mapOutput G alg offline A s).1 hV))

/-- **Lemma 1** (unauthenticated): whenever Byzantine broadcast (of preference lists, for every
sender) is solvable on `G` against `Z`, bSM is solvable on `G` against `Z`. -/
theorem lemma1 {G : SimpleGraph (Party k)} {Z : AdvStructure (Party k)}
    (h : ∀ s, Solvable G Z (BB s : Spec (Party k) (Equiv.Perm (Fin k)) (Equiv.Perm (Fin k)))) :
    Solvable G Z (bSM k) :=
  bSM_of_IC (IC_of_BB h)

/-- **Lemma 1** (authenticated). -/
theorem lemma1_auth {G : SimpleGraph (Party k)} {Z : AdvStructure (Party k)}
    (h : ∀ s, SolvableAuth G Z (BB s : Spec (Party k) (Equiv.Perm (Fin k)) (Equiv.Perm (Fin k)))) :
    SolvableAuth G Z (bSM k) :=
  bSM_of_IC_auth (IC_of_BB_auth h)

end Papers.PODC2025.ByzantineStableMatching
