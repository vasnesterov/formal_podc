import Papers.PODC2026.FewToManyFaultsBA.SyncBA.EndGame

/-!
# Stage B: the fallback among the participants

A run of `stageB Afb` (participants have input `some v`, the others are silent) is a run of `Afb`
in the scenario `bScen s₂` where the silent honest parties are declared Byzantine and silent
(`hist_bScen`). When every honest party participates, `bScen s₂` has the same Byzantine set
(`bScen_byz`), so the guarantees of `Afb` apply.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} {Mf Sf : Type} (Afb : Protocol (Fin n) Bool Mf Bool)

-- CSLib candidate (LockStep: running a protocol among a subset of the honest parties)
open Classical in
/-- The `Afb` scenario of a stage-B run: non-participants become silent Byzantine parties. -/
noncomputable def bScen (s₂ : Scenario (Fin n) (Option Bool) Mf) : Scenario (Fin n) Bool Mf where
  byz := s₂.byz ∪ {p | s₂.input p = none}
  input p := (s₂.input p).getD false
  adv r b q := if b ∈ s₂.byz then s₂.adv r b q else none
  drop := s₂.drop

variable {Afb}

lemma mem_bScen_byz {s₂ : Scenario (Fin n) (Option Bool) Mf} {p : Fin n} :
    p ∉ (bScen s₂).byz ↔ p ∉ s₂.byz ∧ ∃ v, s₂.input p = some v := by
  simp only [bScen, Set.mem_union, Set.mem_setOf_eq, not_or]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, Option.ne_none_iff_exists'.1 h2⟩
  · rintro ⟨h1, v, hv⟩; exact ⟨h1, by simp [hv]⟩

lemma stageB_send_none {p : Fin n} {h : History (Fin n) Mf} {q : Fin n} :
    (stageB Afb).send p none h q = none := rfl

/-- **Simulation.** Participants have the same histories in the stage-B run and in the `Afb` run of
`bScen s₂`. -/
theorem hist_bScen (G : SimpleGraph (Fin n)) (s₂ : Scenario (Fin n) (Option Bool) Mf) :
    ∀ r, ∀ p, p ∉ (bScen s₂).byz → hist G (stageB Afb) s₂ r p = hist G Afb (bScen s₂) r p := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro p hp
    rw [hist_succ, hist_succ, ih p hp]
    congr 1
    refine congrArg (fun f => [f]) (funext fun q => ?_)
    unfold deliver
    by_cases hadj : G.Adj q p
    · simp only [hadj, ite_true]
      by_cases hq : q ∈ s₂.byz
      · have : q ∈ (bScen s₂).byz := Or.inl hq
        simp [hq, this, bScen]
      · by_cases hqp : s₂.input q = none
        · have : q ∈ (bScen s₂).byz := Or.inr hqp
          simp [hq, this, bScen, hqp, stageB]
        · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hqp
          have hqb : q ∉ (bScen s₂).byz := mem_bScen_byz.2 ⟨hq, v, hv⟩
          simp only [hq, hqb, ite_false]
          rw [ih q hqb]
          simp only [bScen, stageB, hv, Option.getD_some]
          by_cases hd : s₂.drop r q p <;> simp [hd]
    · simp [hadj]

lemma status_bScen (G : SimpleGraph (Fin n)) (s₂ : Scenario (Fin n) (Option Bool) Mf) {p : Fin n}
    (hp : p ∉ (bScen s₂).byz) (r : ℕ) :
    status G (stageB Afb) s₂ r p = status G Afb (bScen s₂) r p := by
  obtain ⟨-, v, hv⟩ := mem_bScen_byz.1 hp
  unfold status
  rw [hist_bScen G s₂ r p hp]
  simp only [stageB, hv, bScen, Option.getD_some]

lemma decides_bScen (G : SimpleGraph (Fin n)) (s₂ : Scenario (Fin n) (Option Bool) Mf)
    {p : Fin n} (hp : p ∉ (bScen s₂).byz) (o : Bool) :
    Decides G (stageB Afb) s₂ p o ↔ Decides G Afb (bScen s₂) p o := by
  simp only [Decides, status_bScen G s₂ hp]

/-- When every honest party participates, `bScen` has the same Byzantine set. -/
lemma bScen_byz {s₂ : Scenario (Fin n) (Option Bool) Mf}
    (hall : ∀ p, p ∉ s₂.byz → (s₂.input p).isSome) : (bScen s₂).byz = s₂.byz := by
  ext p
  simp only [bScen, Set.mem_union, Set.mem_setOf_eq, or_iff_left_iff_imp]
  intro h
  by_contra hp
  have := hall p hp
  rw [h] at this; simp at this

lemma bScen_reliable {s₂ : Scenario (Fin n) (Option Bool) Mf} (h : s₂.Reliable) :
    (bScen s₂).Reliable := h

/-- Authentication transfers to `bScen`. -/
lemma bScen_authValid (G : SimpleGraph (Fin n)) {Af : Auth (Fin n) Mf Sf}
    {s₂ : Scenario (Fin n) (Option Bool) Mf} (hV : s₂.AuthValid G (stageB Afb) Af) :
    (bScen s₂).AuthValid G Afb Af := by
  intro r b q m hb hq hadj hm τ hτ
  simp only [bScen] at hm
  split_ifs at hm with hb'
  rcases hV r b q m hb' (fun h => hq (Or.inl h)) hadj hm τ hτ with h | h
  · exact Or.inl (Or.inl h)
  · right
    obtain ⟨r', hr', p, hp, q', hadj', m', hm', hτ'⟩ := h
    by_cases hpn : s₂.input p = none
    · simp [stageB, hpn] at hm'
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hpn
      have hpb : p ∉ (bScen s₂).byz := mem_bScen_byz.2 ⟨hp, v, hv⟩
      refine ⟨r', hr', p, hpb, q', hadj', m', ?_, hτ'⟩
      rw [← hist_bScen G s₂ r' p hpb]
      simpa [stageB, hv, bScen] using hm'

end Podc.FewToManyFaultsBA.Sync
