import Papers.PODC2020.SelfStabHighDynamics.Alg3.Exec

/-!
# Algorithm 3: the paper's statements (Section 6)

`A = alg`, `ℓ = min V`. Times are 0-indexed: `A.exec G γ t` is the configuration at the end of the
paper's Round `t`; the paper's `d̂_{p,o_T}(q)` (journeys departing in Round 2 or later) is
`tdist G 1 p q`. Every statement holds for every processing order of the received pairs and
every tie-break in macro `max(p)`.
-/

namespace Podc.SelfStabHighDynamics.Alg3

open Cslib.HeardOf Cslib.DynNet StabilizingLEDynamic

variable {ι : Type*} [LinearOrder ι] {V : Finset ι} {G : DG ι} {γ : ι → MSt ι}

/-- Configurations stay configurations for `V`: `n = |V|`, at most `n` entries, distinct keys. -/
theorem exec_mem_cfg (hγ : γ ∈ alg.Cfg V) (t : ℕ) : alg.exec G γ t ∈ alg.Cfg V := X_cfg hγ t

/-- After every round, each process `p` holds its own pair `⟨id(p), 0⟩` (line 7). -/
theorem self_mem_exec (hγ : γ ∈ alg.Cfg V) (t : ℕ) {p : ι} (hp : p ∈ V) :
    (p, 0) ∈ (alg.exec G γ (t + 1) p).mem := X_self hγ t hp

/-- **Lemma 10.** For a fake identifier `f`, at the beginning of Round `t + 1` (= end of Round `t`),
every timestamp of `f` in some `members(p)` is `≥ t`. (No assumption on the initial
configuration is needed.) -/
theorem lemma_10 (hG : IsDG V G) {f : ι} (hf : f ∉ V) :
    ∀ t, ∀ p ∈ V, ∀ x ∈ (alg.exec G γ t p).mem, x.1 = f → t ≤ x.2 := by
  intro t p hp x hx hxf
  exact X_fakeGe hG t p hp x hx (hxf ▸ hf)

/-- **Lemma 11.** For every `i ≥ 1`, at the end of Round `i`: if `d̂_{p,o_T}(q) ≤ i - 1` then
`id(p) ∈ members(q)` and `members(q)[p] ≤ i - 1`. -/
theorem lemma_11 (hG : IsDG V G) (hγ : γ ∈ alg.Cfg V) :
    ∀ i ≥ 1, ∀ p ∈ V, ∀ q ∈ V, tdist G 1 p q ≤ ((i - 1 : ℕ) : ℕ∞) →
      ∃ x ∈ (alg.exec G γ i q).mem, x.1 = p ∧ x.2 ≤ i - 1 := by
  intro i hi p hp q _ hd
  rw [tdist_le_iff, show 1 + (i - 1) = i by omega] at hd
  obtain ⟨-, x, hx, hx1, hx2⟩ := lemma11_journey hG hγ hp hd
  exact ⟨x, hx, hx1, by omega⟩

/-- **Lemma 12** (and the closure claim before it). From a legitimate configuration, in any
dynamic graph with vertex set `V`, the execution stays legitimate and satisfies `SP_LE`. -/
theorem lemma_12 (hV : V.Nonempty) (hG : IsDG V G) (hγ : γ ∈ alg.Cfg V ∩ {γ | Legit V hV γ}) :
    (∀ t, alg.exec G γ t ∈ alg.Cfg V ∩ {γ | Legit V hV γ}) ∧
      spLE (alg (ι := ι)) V (alg.exec G γ) := by
  have h : ∀ t, alg.exec G γ t ∈ alg.Cfg V ∩ {γ | Legit V hV γ} := fun t =>
    ⟨X_cfg hγ.1 t, legit_X hG hγ.2 t⟩
  exact ⟨h, V.min' hV, V.min'_mem hV, fun i q hq => ((h i).2 q hq).1⟩

/-- Convergence in `TC_R`: some configuration of every execution is legitimate. -/
theorem converge (hV : V.Nonempty) (hG : G ∈ Jss V) (hγ : γ ∈ alg.Cfg V) :
    ∃ i, alg.exec G γ i ∈ alg.Cfg V ∩ {γ | Legit V hV γ} := by
  classical
  have hb : ∀ p q, ∃ b, p ∈ V → q ∈ V → Journey G 1 p b q := by
    intro p q
    by_cases h : p ∈ V ∧ q ∈ V
    · obtain ⟨b, hb⟩ := hG.2 p h.1 q h.2 1
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨0, fun hp hq => absurd ⟨hp, hq⟩ h⟩
  choose b hb using hb
  set T := max 1 ((V ×ˢ V).sup fun x => b x.1 x.2) with hT
  refine ⟨T, X_cfg hγ T, legit_of_cover hγ hV (le_max_left _ _) fun p hp q hq => ?_⟩
  have hle : b p q ≤ T := le_trans (Finset.le_sup (f := fun x : ι × ι => b x.1 x.2) (b := (p, q))
    (Finset.mem_product.mpr ⟨hp, hq⟩)) (le_max_right _ _)
  obtain ⟨-, x, hx, rfl, -⟩ := lemma11_journey hG.1 hγ hp ((hb p q hp hq).mono_right hle)
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

/-- **Theorem 8.** Algorithm 3 is self-stabilizing for leader election in `TC_R`: the legitimate
configurations form a set of legitimate configurations (Definition 1) and are closed
(Definition 2). -/
theorem theorem_8 (hV : V.Nonempty) :
    IsLegit (alg (ι := ι)) Jss (spLE (alg (ι := ι))) V (alg.Cfg V ∩ {γ | Legit V hV γ}) ∧
      Closed (alg (ι := ι)) Jss V (alg.Cfg V ∩ {γ | Legit V hV γ}) :=
  ⟨⟨fun _ h => h.1, fun _ hG _ hγ => converge hV hG hγ,
      fun _ hG _ hγ => (lemma_12 hV hG.1 hγ).2⟩,
    fun _ hG _ hγ i => (lemma_12 hV hG.1 hγ).1 i⟩

/-- **Theorem 8** (Definition 1 form). -/
theorem selfStab : SelfStab (alg (ι := ι)) Jss (spLE (alg (ι := ι))) :=
  fun _ hV => ⟨_, (theorem_8 hV).1⟩

/-- **Theorem 9.** In `TC_B(Δ)`, the configuration at the end of every Round `t ≥ Δ + 1` is
legitimate. -/
theorem theorem_9 (hV : V.Nonempty) {Δ : ℕ} (hG : G ∈ JssB Δ V) (hγ : γ ∈ alg.Cfg V) :
    ∀ t ≥ Δ + 1, alg.exec G γ t ∈ alg.Cfg V ∩ {γ | Legit V hV γ} := by
  intro t ht
  refine ⟨X_cfg hγ t, legit_of_cover hγ hV (by omega) fun p hp q hq => ?_⟩
  have hd := tdist_le_iff.mp (hG.2 p hp q hq 1)
  obtain ⟨-, x, hx, rfl, -⟩ := lemma11_journey hG.1 hγ hp (hd.mono_right (r := t) (by omega))
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

/-- Algorithm 3 is not size-ambiguous (Definition 3): `n` is part of the input. -/
theorem not_sizeAmbiguous : ¬ SizeAmbiguous (alg (ι := ι)) := by
  rintro ⟨k, V, hk0, hkV, h⟩
  obtain ⟨U, hUV, hU⟩ := Finset.exists_subset_card_eq hkV.le
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (hU ▸ hk0)
  have hmem : (⟨k, [], p⟩ : MSt ι) ∈ alg.S U p := by
    simp only [alg, Set.mem_ofPred_eq]; exact ⟨hU.symm, by simp, by simp [keys]⟩
  rw [h U hUV hU p hp] at hmem
  simp only [alg, Set.mem_ofPred_eq] at hmem
  omega

end Podc.SelfStabHighDynamics.Alg3
