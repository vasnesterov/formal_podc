import Papers.PODC2020.SelfStabHighDynamics.Unbounded

/-!
# The implicit assumptions of Theorem 6 are necessary

Theorem 6 (and Corollary 8, Lemma 13, Corollary 9) fails

* if the identifier domain has only `n` elements (`knowsN2`: with `IDSET = Fin 2`, a process
  that knows `n = 2` elects `0`, and a single process elects itself);
* if the algorithm may know the set of processes (`knowsV`: the local state of every process is
  the set `V` itself, and `lid := min V`).

In both cases the pseudo-stabilization phase of every execution has length `0`, and the set of
all configurations is a closed set of legitimate configurations.
-/

namespace Podc.SelfStabHighDynamics

open Cslib.HeardOf
open StabilizingLEDynamic (DG IsDG JssQ DGClass)

/-- With `IDSET = Fin 2`: the input of every process is `n`; if `n = 2` the leader is `0`,
otherwise the process itself. Its local states depend on the system only through `n`. -/
def knowsN2 : SAlg (Fin 2) ℕ where
  step p m := (m p).getD 0
  lid p s := if s = 2 then 0 else p
  S V _ := {k | k = V.card}
  S_nonempty _ _ _ := Set.singleton_nonempty _

theorem knowsN2_sizeOnly : SizeOnly knowsN2 := fun _ _ h _ _ _ => by
  simp only [knowsN2, h]

theorem knowsN2_exec (G : DG (Fin 2)) (γ : Fin 2 → ℕ) (t : ℕ) : knowsN2.exec G γ t = γ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    change ((msgs (G t) (knowsN2.exec G γ t) p) p).getD 0 = γ p
    rw [msgs_self, ih]; rfl

/-- `knowsN2` elects a process of `V` from the start in every execution, for every (nonempty)
`V ⊆ Fin 2`. -/
theorem knowsN2_spLE {V : Finset (Fin 2)} (hV : V.Nonempty) (G : DG (Fin 2))
    {γ : Fin 2 → ℕ} (hγ : γ ∈ knowsN2.Cfg V) (i : ℕ) :
    spLE knowsN2 V (fun t => knowsN2.exec G γ (i + t)) := by
  simp only [knowsN2_exec]
  have hc : V.card ≤ 2 := by simpa using Finset.card_le_univ V
  rcases Nat.lt_or_ge V.card 2 with h | h
  · obtain ⟨a, rfl⟩ := (Finset.card_eq_one (s := V)).mp (by have := hV.card_pos; omega)
    refine ⟨a, Finset.mem_singleton_self a, fun t q hq => ?_⟩
    rw [Finset.mem_singleton] at hq; subst hq
    have : γ q = 1 := hγ q (Finset.mem_singleton_self q)
    simp [knowsN2, this]
  · have hV2 : V = Finset.univ := Finset.eq_univ_of_card V (by rw [Fintype.card_fin]; omega)
    refine ⟨0, hV2 ▸ Finset.mem_univ _, fun t q hq => ?_⟩
    have h2 : γ q = (Finset.univ : Finset (Fin 2)).card := by
      have := hγ q hq; rw [hV2] at this; exact this
    have : γ q = 2 := by simpa using h2
    simp [knowsN2, this]

/-- `knowsN2` is a pseudo-stabilizing leader election algorithm for every class (so it
satisfies the hypotheses of the paper's Theorem 6). -/
theorem knowsN2_pseudoStab (C : DGClass (Fin 2)) : PseudoStab knowsN2 C (spLE knowsN2) :=
  fun _ hV G _ _ hγ => ⟨0, knowsN2_spLE hV G hγ 0⟩

/-- With two identifiers and two processes, every execution of the pseudo-stabilizing,
`SizeOnly` algorithm `knowsN2` satisfies `SP_LE` from the start, so the conclusion of Theorem 6
fails for `f = 0`. -/
theorem theorem_6_needs_large_IDSET (Δ : ℕ) :
    ¬ ∃ V : Finset (Fin 2), V.card = 2 ∧ ∃ G ∈ JssQ Δ V, ∃ γ ∈ knowsN2.Cfg V,
      ∀ i ≤ 0, ¬ spLE knowsN2 V (fun t => knowsN2.exec G γ (i + t)) := by
  rintro ⟨V, hV, G, -, γ, hγ, h⟩
  exact h 0 le_rfl (knowsN2_spLE (Finset.card_pos.mp (by omega)) G hγ 0)

/-- The local state of every process is the set of processes; `lid := min V`. -/
noncomputable def knowsV : SAlg ℕ (Finset ℕ) where
  step p m := (m p).getD ∅
  lid p s := if h : s.Nonempty then s.min' h else p
  S V _ := {V}
  S_nonempty V _ _ := Set.singleton_nonempty V

theorem knowsV_exec (G : DG ℕ) (γ : ℕ → Finset ℕ) (t : ℕ) : knowsV.exec G γ t = γ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    change ((msgs (G t) (knowsV.exec G γ t) p) p).getD ∅ = γ p
    rw [msgs_self, ih]; rfl

/-- `knowsV` elects `min V` from the start in every execution (in particular it is
self-stabilizing for every class, and Theorem 6 fails for it with `f = 0`). -/
theorem knowsV_spLE {V : Finset ℕ} (hV : V.Nonempty) (G : DG ℕ) {γ : ℕ → Finset ℕ}
    (hγ : γ ∈ knowsV.Cfg V) (i : ℕ) : spLE knowsV V (fun t => knowsV.exec G γ (i + t)) := by
  refine ⟨V.min' hV, V.min'_mem hV, fun t q hq => ?_⟩
  simp only [knowsV_exec]
  have : γ q = V := hγ q hq
  simp [knowsV, this, hV]

/-- `knowsV` is a pseudo-stabilizing leader election algorithm for every class. -/
theorem knowsV_pseudoStab (C : DGClass ℕ) : PseudoStab knowsV C (spLE knowsV) :=
  fun _ hV G _ _ hγ => ⟨0, knowsV_spLE hV G hγ 0⟩

/-- Theorem 6 fails for the pseudo-stabilizing algorithm `knowsV`, whose states are not
`SizeOnly`: for every `n` and `f`, every execution satisfies `SP_LE` from the start. -/
theorem theorem_6_needs_sizeOnly (Δ n : ℕ) (f : ℕ → ℕ → ℕ) :
    ¬ ∃ V : Finset ℕ, V.card = n ∧ 2 ≤ n ∧ ∃ G ∈ JssQ Δ V, ∃ γ ∈ knowsV.Cfg V,
      ∀ i ≤ f n Δ, ¬ spLE knowsV V (fun t => knowsV.exec G γ (i + t)) := by
  rintro ⟨V, hV, hn, G, -, γ, hγ, h⟩
  exact h 0 (Nat.zero_le _) (knowsV_spLE (Finset.card_pos.mp (by omega)) G hγ 0)

end Podc.SelfStabHighDynamics
