import Papers.PODC2020.SelfStabHighDynamics.Classes

/-!
# Section 3: knowledge of `n` and closure

* `theorem_1`: in `TC_B(Δ)`, `Δ ≥ 2`, a `(k, V)`-ambiguous self-stabilizing leader election
  algorithm has no closed set of legitimate configurations for `V`; `corollary_1` (its
  contrapositive, as the paper intends it).
* `theorem_2` / `corollary_2`: in `TC_Q(Δ)`, every self-stabilizing algorithm for a recurring
  specification has a closed set of legitimate configurations.
* `theorem_3` / `corollary_3`: no self-stabilizing leader election algorithm for `TC_Q(Δ)`
  (`Δ ≥ 2`), resp. `TC_R`, is size-ambiguous.

The core of Theorem 1 (`no_closed_of_ambiguous`) only needs a set `M` of configurations that
contains a configuration of `A` for `V`, is closed under the first round of every graph of
`TC_B(Δ)`, and from which every execution satisfies `SP_LE`. Theorem 3 applies it directly to
`M = {γ | every execution from γ in TC_Q(Δ) satisfies SP_LE}` (the set of the proof of
Theorem 2), so it does not need the invariance of the configurations of `A` used in Theorem 2.

The proof of Theorem 1 is simpler than the paper's: the TVG `G` (complete in odd rounds, complete
on a `k`-subset `U` not containing the leader in even rounds) does not need a rotating window,
and the configurations `γ^i` of the paper's proof are exactly the execution of `A` in the static
complete graph on `U` started from `γ` (in the first round of `G`, the processes outside `U` are
isolated, so the whole configuration evolves as in the static graph on `U`).
-/

namespace Podc.SelfStabHighDynamics

open Cslib.HeardOf
open StabilizingLEDynamic (DG IsDG DGClass JssB JssQ Jss J_shift)

variable {ι σ : Type*}

/-- The core of Theorem 1. -/
theorem no_closed_of_ambiguous {A : SAlg ι σ} {Δ : ℕ} (hΔ : 2 ≤ Δ) {V : Finset ι} {k : ℕ}
    (hamb : Ambiguous A k V) (hps : PseudoStab A (JssB Δ) (spLE A)) (M : Set (ι → σ))
    {γ : ι → σ} (hγ : γ ∈ M) (hγC : γ ∈ A.Cfg V)
    (hM : ∀ G ∈ JssB Δ V, ∀ γ ∈ M, A.exec G γ 1 ∈ M ∧ spLE A V (A.exec G γ)) : False := by
  classical
  obtain ⟨hk0, hkV, hS⟩ := hamb
  -- the leader `ℓ` elected in `γ`
  obtain ⟨ℓ, hℓV, hℓ⟩ := (hM _ (K_mem_JssB (by omega)) γ hγ).2
  -- a `k`-subset `U` of `V` not containing `ℓ`
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq (s := V.erase ℓ) (n := k)
    (by rw [Finset.card_erase_of_mem hℓV]; omega)
  have hUV : U ⊆ V := hUsub.trans (Finset.erase_subset _ _)
  have hℓU : ℓ ∉ U := fun h => by simpa using hUsub h
  -- the TVG `G`: complete on `U` in even rounds, complete on `V` in odd rounds
  set G : DG ι := fun t => if t % 2 = 0 then K U else K V with hGdef
  have hG : G ∈ JssB Δ V := by
    refine mem_JssB_of_complete (fun t a b h => ?_) (fun i => ?_)
    · simp only [hGdef] at h; split_ifs at h
      · exact ⟨hUV h.1, hUV h.2.1, h.2.2⟩
      · exact h
    · refine ⟨if i % 2 = 0 then i + 1 else i, by split_ifs <;> omega, by split_ifs <;> omega,
        fun p hp q hq hpq => ?_⟩
      simp only [hGdef]
      split_ifs <;> first | omega | exact ⟨hp, hq, hpq⟩
  have hG0 : G 0 = K U := by simp [hGdef]
  -- Claims 2 and 3: the execution in the static graph `K U` stays in `M`, electing `ℓ`
  have key : ∀ j, A.exec (fun _ => K U) γ j ∈ M ∧
      ∀ q ∈ V, A.lid q (A.exec (fun _ => K U) γ j q) = ℓ := by
    intro j
    induction j with
    | zero => exact ⟨hγ, hℓ 0⟩
    | succ j ih =>
      have hstep : A.exec (fun _ => K U) γ (j + 1) = A.exec G (A.exec (fun _ => K U) γ j) 1 := by
        change next _ (K U) _ = next _ (G 0) _
        rw [hG0]; rfl
      obtain ⟨hM1, ℓ', -, hℓ'⟩ := hM G hG _ ih.1
      have hℓℓ' : ℓ' = ℓ := (hℓ' 0 ℓ hℓV).symm.trans (ih.2 ℓ hℓV)
      subst hℓℓ'
      exact ⟨hstep ▸ hM1, fun q hq => hstep ▸ hℓ' 1 q hq⟩
  -- `γ` is a configuration for `U`, and the static complete graph on `U` is in `TC_B(Δ)`
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hγU : γ ∈ A.Cfg U := fun p hp => (hS U hUV hUcard p hp) ▸ hγC p (hUV hp)
  obtain ⟨i, ℓ', hℓ'U, h'⟩ := hps U hUne _ (K_mem_JssB (by omega)) γ hγU
  obtain ⟨q, hq⟩ := hUne
  have := (h' 0 q hq).symm.trans ((key (i + 0)).2 q (hUV hq))
  exact hℓU (this ▸ hℓ'U)

/-- **Theorem 1.** Let `A` be a self-stabilizing leader election algorithm for `TC_B(Δ)` with
`Δ ≥ 2`, and `L` a set of legitimate configurations of `A` for `V`. If `A` is
`(k, V)`-ambiguous, then `L` is not closed in `TC_B(Δ)`. -/
theorem theorem_1 {A : SAlg ι σ} {Δ : ℕ} (hΔ : 2 ≤ Δ) (hA : SelfStab A (JssB Δ) (spLE A))
    {V : Finset ι} {L : Set (ι → σ)} (hL : IsLegit A (JssB Δ) (spLE A) V L) {k : ℕ}
    (hamb : Ambiguous A k V) : ¬ Closed A (JssB Δ) V L := by
  intro hcl
  have hps := hA.pseudoStab fun _ _ hG i => J_shift hG i
  obtain ⟨γ0, hγ0⟩ := A.cfg_nonempty V
  obtain ⟨i, hi⟩ := hL.2.1 _ (K_mem_JssB (by omega)) γ0 hγ0
  exact no_closed_of_ambiguous hΔ hamb hps L hi (hL.1 hi)
    fun G hG γ hγ => ⟨hcl G hG γ hγ 1, hL.2.2 G hG γ hγ⟩

/-- **Corollary 1** (the contrapositive of Theorem 1): if a set of legitimate configurations of
`A` for `V` is closed in `TC_B(Δ)`, then `A` is not `(k, V)`-ambiguous, for any `k`. (The paper
states the conclusion as "`A` is not size-ambiguous", which is stronger and false, see
`corollary_1_as_stated_false`.) -/
theorem corollary_1 {A : SAlg ι σ} {Δ : ℕ} (hΔ : 2 ≤ Δ) (hA : SelfStab A (JssB Δ) (spLE A))
    {V : Finset ι} {L : Set (ι → σ)} (hL : IsLegit A (JssB Δ) (spLE A) V L)
    (hcl : Closed A (JssB Δ) V L) (k : ℕ) : ¬ Ambiguous A k V :=
  fun hamb => theorem_1 hΔ hA hL hamb hcl

/-- The executions of `A` stay in the configurations of `A` for `V` (implicit in the paper:
an execution is a sequence of configurations of `A` for `V`). -/
def Invariant (A : SAlg ι σ) (C : DGClass ι) : Prop :=
  ∀ V, ∀ G ∈ C V, ∀ γ ∈ A.Cfg V, ∀ t, A.exec G γ t ∈ A.Cfg V

/-- If every execution from `γ` in `TC_Q(Δ)` satisfies a recurring specification, so does
every execution from a configuration reachable from `γ` (by Property 1). -/
theorem forall_spec_exec {A : SAlg ι σ} {Δ : ℕ} {SP : Spec ι σ} (hSP : Recurring SP)
    {V : Finset ι} {G : DG ι} (hG : G ∈ JssQ Δ V) {γ : ι → σ}
    (h : ∀ G' ∈ JssQ Δ V, SP V (A.exec G' γ)) (i : ℕ) :
    ∀ G' ∈ JssQ Δ V, SP V (A.exec G' (A.exec G γ i)) := by
  intro G' hG'
  have := hSP V _ (h _ (splice_mem_JssQ hG.1 i hG')) i
  have heq : (fun t => A.exec (splice G i G') γ (i + t)) = A.exec G' (A.exec G γ i) :=
    funext fun t => conf_splice _ _ _ _ _
  rwa [heq] at this

/-- **Theorem 2.** Let `SP` be a recurring specification and `A` a self-stabilizing algorithm for
`SP` on `TC_Q(Δ)`. For every `V`, there is a set of legitimate configurations of `A` for `V` which
is closed in `TC_Q(Δ)`. -/
theorem theorem_2 {A : SAlg ι σ} {Δ : ℕ} {SP : Spec ι σ} (hSP : Recurring SP)
    (hinv : Invariant A (JssQ Δ)) (hA : SelfStab A (JssQ Δ) SP) {V : Finset ι}
    (hV : V.Nonempty) : ∃ L, IsLegit A (JssQ Δ) SP V L ∧ Closed A (JssQ Δ) V L := by
  obtain ⟨L', hL'sub, hconv, hcorr⟩ := hA V hV
  refine ⟨{γ | γ ∈ A.Cfg V ∧ ∀ G ∈ JssQ Δ V, SP V (A.exec G γ)},
    ⟨fun _ h => h.1, fun G hG γ hγ => ?_, fun G hG γ hγ => hγ.2 G hG⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hconv G hG γ hγ
    exact ⟨i, hL'sub hi, fun G' hG' => hcorr G' hG' _ hi⟩
  · intro G hG γ hγ i
    exact ⟨hinv V G hG γ hγ.1 i, forall_spec_exec hSP hG hγ.2 i⟩

/-- **Corollary 2.** Every self-stabilizing leader election algorithm for `TC_Q(Δ)` has, for
every `V`, a set of legitimate configurations closed in `TC_Q(Δ)`. -/
theorem corollary_2 {A : SAlg ι σ} {Δ : ℕ} (hinv : Invariant A (JssQ Δ))
    (hA : SelfStab A (JssQ Δ) (spLE A)) {V : Finset ι} (hV : V.Nonempty) :
    ∃ L, IsLegit A (JssQ Δ) (spLE A) V L ∧ Closed A (JssQ Δ) V L :=
  theorem_2 (recurring_spLE A) hinv hA hV

/-- **Theorem 3.** No self-stabilizing leader election algorithm for `TC_Q(Δ)`, `Δ ≥ 2`, is
size-ambiguous. -/
theorem theorem_3 {A : SAlg ι σ} {Δ : ℕ} (hΔ : 2 ≤ Δ) (hA : SelfStab A (JssQ Δ) (spLE A)) :
    ¬ SizeAmbiguous A := by
  rintro ⟨k, V, hamb⟩
  have hps : PseudoStab A (JssB Δ) (spLE A) :=
    (hA.mono fun V => JssB_subset_JssQ Δ V).pseudoStab fun _ _ hG i => J_shift hG i
  have hV : V.Nonempty := Finset.card_pos.mp (by have := hamb.2.1; omega)
  obtain ⟨L, hLsub, hconv, hcorr⟩ := hA V hV
  obtain ⟨γ0, hγ0⟩ := A.cfg_nonempty V
  obtain ⟨i, hi⟩ := hconv _ (JssB_subset_JssQ _ _ (K_mem_JssB (by omega))) γ0 hγ0
  exact no_closed_of_ambiguous hΔ hamb hps {γ | ∀ G ∈ JssQ Δ V, spLE A V (A.exec G γ)}
    (fun G hG => hcorr G hG _ hi) (hLsub hi) fun G hG γ hγ =>
      ⟨forall_spec_exec (recurring_spLE A) (JssB_subset_JssQ _ _ hG) hγ 1,
        hγ G (JssB_subset_JssQ _ _ hG)⟩

/-- **Corollary 3.** No self-stabilizing leader election algorithm for `TC_R` is
size-ambiguous. -/
theorem corollary_3 {A : SAlg ι σ} (hA : SelfStab A Jss (spLE A)) : ¬ SizeAmbiguous A :=
  theorem_3 (Δ := 2) le_rfl (hA.mono fun V => JssQ_subset_Jss 2 V)

end Podc.SelfStabHighDynamics
