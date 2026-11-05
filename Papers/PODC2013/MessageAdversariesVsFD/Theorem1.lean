import Papers.PODC2013.MessageAdversariesVsFD.StronglyCorrect

/-!
# Theorem 1, synchronous side: `SMP_n[adv : ∞]` solves exactly the local tasks

Theorem 1 of the paper states that a task is solvable in `SMP_n[adv : ∞]` iff it is solvable in
`AMP_{n,n-1}[fd : ∅]`; its proof shows that both are equivalent to the task being *local* (each
process computes its output from its own input). This file proves the synchronous half, for both
solvability notions:

* `solvable_inf_iff_local`: every process must output (the paper's definition);
* `solvableSC_inf_iff_local`: only strongly correct processes must output.

The asynchronous half is in `AsyncTheorem1.lean` (if present) / discussed in the README.
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.HeardOf (Graph Hears Deaf conf conf_agree_deaf conf_congr)

variable {P X Y : Type}

/-- The pattern in which every message is suppressed. -/
def silent : ℕ → Graph P := fun _ _ _ => False

namespace Alg

variable {σ : Type} (A : Alg P X Y σ)

/-- The trajectory of process `i` with input `v` when it hears nobody. -/
noncomputable def solo (i : P) (v : X) (t : ℕ) : σ :=
  conf A.step (fun _ => A.init i v) silent t i

open Classical in
/-- The first output of process `i` with input `v` when it hears nobody. -/
noncomputable def soloOut (i : P) (v : X) : Option Y :=
  if h : ∃ t, (A.out (A.solo i v t)).isSome then A.out (A.solo i v (Nat.find h)) else none

theorem run_eq_solo {x : P → X} {p : ℕ → Graph P} {i : P} {T : ℕ}
    (hdeaf : ∀ t < T, Deaf (p t) i) {t : ℕ} (ht : t ≤ T) :
    A.run x p t i = A.solo i (x i) t := by
  -- replace `p` by a pattern that agrees with it before `T` and is silent afterwards
  let q : ℕ → Graph P := fun k => if k < T then p k else silent k
  have h1 : A.run x p t i = conf A.step (fun i => A.init i (x i)) q t i := by
    unfold run
    rw [conf_congr _ (fun k hk => (ite_eq_left (by omega : k < T)).symm)]
  rw [h1, solo]
  refine conf_agree_deaf (step := A.step) (p := q) (p' := silent)
    (C := fun i => A.init i (x i)) (C' := fun _ => A.init i (x i)) (i := i)
    (fun k => ?_) (fun k j (hj : False) => hj.elim) rfl t
  intro j hj
  by_cases hk : k < T
  · simp only [q, ite_eq_left hk] at hj; exact hdeaf k hk j hj
  · simp only [q, ite_eq_right hk, silent] at hj

theorem output_eq_of_first {x : P → X} {p : ℕ → Graph P} {i : P} {t : ℕ}
    (ht : (A.out (A.run x p t i)).isSome) (hlt : ∀ s < t, A.out (A.run x p s i) = none) :
    A.output x p i = A.out (A.run x p t i) := by
  classical
  have hd : A.Decided x p i := ⟨t, ht⟩
  unfold output
  rw [dite_eq_left_of_eq_true (eq_true hd)]
  congr 2
  apply le_antisymm (Nat.find_min' hd ht)
  by_contra hc
  have h1 := hlt _ (not_le.1 hc)
  have h2 : (A.out (A.run x p (Nat.find hd) i)).isSome := Nat.find_spec hd
  rw [h1] at h2; exact absurd h2 (by simp)

theorem output_eq_soloOut {x : P → X} {p : ℕ → Graph P} {i : P} {T : ℕ}
    (hdeaf : ∀ t < T, Deaf (p t) i) (hdec : ∃ t ≤ T, (A.out (A.solo i (x i) t)).isSome) :
    A.output x p i = A.soloOut i (x i) := by
  classical
  have hs : ∃ t, (A.out (A.solo i (x i) t)).isSome := hdec.imp fun _ h => h.2
  have hfind : Nat.find hs ≤ T := by
    obtain ⟨t, htT, ht⟩ := hdec; exact le_trans (Nat.find_min' hs ht) htT
  have hd : A.Decided x p i := ⟨Nat.find hs, by
    rw [A.run_eq_solo hdeaf hfind]; exact Nat.find_spec hs⟩
  have heq : Nat.find hd = Nat.find hs := by
    apply le_antisymm
    · exact Nat.find_min' hd (by rw [A.run_eq_solo hdeaf hfind]; exact Nat.find_spec hs)
    · refine Nat.find_min' hs ?_
      have h2 := Nat.find_spec hd
      have hle : Nat.find hd ≤ T := le_trans (Nat.find_min' hd (by
        rw [A.run_eq_solo hdeaf hfind]; exact Nat.find_spec hs)) hfind
      rwa [A.run_eq_solo hdeaf hle] at h2
  unfold output soloOut
  rw [dite_eq_left_of_eq_true (eq_true hd), dite_eq_left_of_eq_true (eq_true hs), heq, A.run_eq_solo hdeaf hfind]

end Alg

/-- The algorithm deciding `f i (x i)` immediately. -/
noncomputable def localAlg (f : P → X → Option Y) : Alg P X Y (Option (P × X)) where
  init i v := some (i, v)
  step i m := (m i).join
  out s := s.bind fun a => f a.1 a.2

theorem localAlg_output (f : P → X → Option Y) (x : P → X) (p : ℕ → Graph P) (i : P)
    (hf : (f i (x i)).isSome) : (localAlg f).output x p i = f i (x i) := by
  rw [Alg.output_eq_of_first (t := 0) _ (by simpa [Alg.run, localAlg] using hf)
    (fun s hs => absurd hs (Nat.not_lt_zero _))]
  simp [Alg.run, localAlg]

theorem localAlg_solves {T : Task P X Y} (hT : T.IsLocal) (Adv : Adversary P) :
    ∃ σ, ∃ A : Alg P X Y σ, A.Solves Adv T := by
  obtain ⟨f, hf⟩ := hT
  refine ⟨_, localAlg f, fun x hx p _ => ?_⟩
  obtain ⟨O, hO, hfO⟩ := hf x hx
  have hs : ∀ i, (f i (x i)).isSome := fun i => by simp [hfO i]
  refine ⟨fun i => ⟨0, by simpa [Alg.run, localAlg] using hs i⟩, O, hO, fun i y hy => ?_⟩
  rw [localAlg_output f x p i (hs i), hfO i] at hy
  exact Option.some_injective _ hy

/-- **Theorem 1 of [Raynal–Stainer], synchronous side.** A task is solvable in `SMP_n[adv : ∞]`
(every process outputs) iff it is local. -/
theorem solvable_inf_iff_local (T : Task P X Y) : Solvable (advInf : Adversary P) T ↔ T.IsLocal := by
  constructor
  · rintro ⟨σ, A, hA⟩
    refine ⟨A.soloOut, fun x hx => ?_⟩
    obtain ⟨hdec, O, hO, hval⟩ := hA x hx silent trivial
    refine ⟨O, hO, fun i => ?_⟩
    have hdeaf : ∀ t, Deaf ((silent : ℕ → Graph P) t) i := fun t j hj => hj.elim
    obtain ⟨t, ht⟩ := hdec i
    have hsolo : (A.out (A.solo i (x i) t)).isSome := by
      rwa [A.run_eq_solo (T := t) (fun k _ => hdeaf k) le_rfl] at ht
    rw [← A.output_eq_soloOut (fun k _ => hdeaf k) ⟨t, le_rfl, hsolo⟩]
    have hd : A.Decided x silent i := hdec i
    have hsome : (A.output x silent i).isSome := by
      classical
      simp only [Alg.output, dite_eq_left_of_eq_true (eq_true hd)]; exact Nat.find_spec hd
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
    rw [hy, hval i y hy]
  · intro h
    obtain ⟨σ, A, hA⟩ := localAlg_solves h advInf
    exact ⟨σ, A, hA⟩

/-- The pattern in which only `i` is heard (by everybody). -/
def onlyFrom (i : P) : ℕ → Graph P := fun _ j _ => j = i

/-- The pattern that is silent during the first `T` rounds and complete afterwards. -/
def silentThenAll (T : ℕ) : ℕ → Graph P := fun t _ _ => T ≤ t

/-- **Theorem 1 of [Raynal–Stainer], synchronous side, weak semantics.** Even if only strongly
correct processes must output, a task is solvable in `SMP_n[adv : ∞]` iff it is local. -/
theorem solvableSC_inf_iff_local [Finite P] (T : Task P X Y) :
    SolvableSC (advInf : Adversary P) T ↔ T.IsLocal := by
  constructor
  · rintro ⟨σ, A, hA⟩
    refine ⟨A.soloOut, fun x hx => ?_⟩
    -- every process decides when running alone: in `onlyFrom i`, process `i` is a source
    have hsolo : ∀ i, ∃ t, (A.out (A.solo i (x i) t)).isSome := by
      intro i
      have hi : i ∈ SC (onlyFrom i) :=
        mem_SC_of_source (r₀ := 0) fun t _ j => by
          by_cases h : i = j
          · exact Or.inl h
          · exact Or.inr rfl
      obtain ⟨t, ht⟩ := (hA x hx (onlyFrom i) trivial).1 i hi
      have hdeaf : ∀ k, Deaf ((onlyFrom i : ℕ → Graph P) k) i := fun k j hj => hj
      exact ⟨t, by rwa [A.run_eq_solo (T := t) (fun k _ => hdeaf k) le_rfl] at ht⟩
    classical
    have : Fintype P := Fintype.ofFinite P
    let T := Finset.univ.sup fun i => Nat.find (hsolo i)
    have hT : ∀ i, Nat.find (hsolo i) ≤ T := fun i => Finset.le_sup (f := fun i => Nat.find (hsolo i))
      (Finset.mem_univ i)
    obtain ⟨-, O, hO, hval⟩ := hA x hx (silentThenAll T) trivial
    refine ⟨O, hO, fun i => ?_⟩
    have hdeaf : ∀ t < T, Deaf ((silentThenAll T : ℕ → Graph P) t) i := fun t ht j hj => by
      simp only [silentThenAll] at hj; omega
    have hout := A.output_eq_soloOut hdeaf ⟨_, hT i, Nat.find_spec (hsolo i)⟩
    have hsome : (A.soloOut i (x i)).isSome := by
      simp only [Alg.soloOut, dite_eq_left_of_eq_true (eq_true (hsolo i))]; exact Nat.find_spec (hsolo i)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
    rw [hy, hval i y (hout.trans hy)]
  · intro h
    obtain ⟨σ, A, hA⟩ := localAlg_solves h advInf
    exact ⟨σ, A, fun x hx p hp => ⟨fun i _ => (hA x hx p hp).1 i, (hA x hx p hp).2⟩⟩

end Podc.MessageAdversariesVsFD
