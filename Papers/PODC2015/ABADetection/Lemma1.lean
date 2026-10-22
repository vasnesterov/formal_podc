import Papers.PODC2015.ABADetection.Common

/-!
# Lemma 1: covering many registers (Aghazadeh–Woelfel, PODC 2015, Section 2.1)

`lemma1`: let an implementation from *bounded* base objects whose operations are all reads or blind
writes (registers) be obstruction-free and separate clean from dirty configurations
(`Separates`, Observation 1). Then from every reachable quiescent configuration `Q` (reached by a
standard execution) and for every list `ps` of distinct readers, a `(ps ∪ {w0})`-only execution
leads to a configuration in which the writer `w0` is idle and the processes of `ps` cover `|ps|`
distinct registers.

The proof follows the paper: iterate the induction hypothesis, a block write by `ps` and a round
`γᵢ` (finish `ps`, one round of the writer) forever; by finiteness of the memory two of the
configurations `Dᵢ, Dⱼ` after the block writes have the same memory. Run the new process `p`
solo from `Cᵢ`: either it becomes poised to write a register outside the covered set (done), or
it finishes its read writing only covered registers, and then the block write hides it
(`blockWrite_agreeOn`): the clean configuration `D'ᵢ` and the dirty configuration `D'ⱼ` are
indistinguishable to `p`, contradicting `Separates`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L} {w0 : P} {rd : P → A.Op} {ws : List A.Op}

/-- In `C`, the processes of `ps` cover `|ps|` distinct base objects. -/
def CoveredBy (I : Impl A B P L) (ps : List P) (C : Config A B P L) : Prop :=
  ∃ cs : List (P × ι), cs.map Prod.fst = ps ∧ (cs.map Prod.snd).Nodup ∧
    ∀ c ∈ cs, I.Covers C c.1 c.2

/-- **Lemma 1** of [Aghazadeh–Woelfel, PODC 2015]. -/
theorem lemma1 [Finite ι] [∀ i, Finite (B i).State]
    (hreg : ∀ i (o : (B i).Op), (B i).ReadOnly o ∨ (B i).Overwrites o)
    (hof : I.ObstructionFree) (hsep : Separates I w0 rd ws)
    (hrd : ∀ p, p ≠ w0 → I.allowed p (rd p)) (hws : ∀ o ∈ ws, I.allowed w0 o) :
    ∀ ps : List P, ps.Nodup → w0 ∉ ps → ∀ αQ Q, I.run αQ = some Q → Q.Quiescent →
      Std w0 rd ws αQ →
      ∃ α C, I.runFrom Q α = some C ∧ (∀ ℓ ∈ α, ℓ.proc ∈ w0 :: ps) ∧
        Std w0 rd ws (αQ ++ α) ∧ C.pend w0 = none ∧ CoveredBy I ps C := by
  intro ps
  induction ps with
  | nil =>
    intro _ _ αQ Q hQ hq hs
    exact ⟨[], Q, rfl, by simp, by simpa using hs, hq w0, [], rfl, by simp, by simp⟩
  | cons p ps ih =>
    intro hnd hw0 αQ Q hQ hq hs
    have hp0 : p ≠ w0 := fun h => hw0 (h ▸ List.mem_cons_self)
    have hnd' := (List.nodup_cons.1 hnd).2
    have hpps := (List.nodup_cons.1 hnd).1
    have hw0' : w0 ∉ ps := fun h => hw0 (List.mem_cons_of_mem _ h)
    have hnotp : ∀ q ∈ w0 :: ps, q ≠ p := by
      intro q hq' he; subst he
      rcases List.mem_cons.1 hq' with h | h
      · exact hp0 h
      · exact hpps h
    let G := {x : List (Label P A) × Config A B P L //
      I.run x.1 = some x.2 ∧ x.2.Quiescent ∧ Std w0 rd ws x.1}
    -- one round: induction hypothesis, block write, finishing round
    have hstep : ∀ x : G, ∃ (α : List (Label P A)) (C : Config A B P L) (cs : List (P × ι))
        (D : Config A B P L) (γ : List (Label P A)) (Q' : Config A B P L),
        I.runFrom x.1.2 α = some C ∧ (∀ ℓ ∈ α, ℓ.proc ∈ w0 :: ps) ∧
        Std w0 rd ws (x.1.1 ++ α) ∧ C.pend w0 = none ∧ cs.map Prod.fst = ps ∧
        (cs.map Prod.snd).Nodup ∧ (∀ c ∈ cs, I.Covers C c.1 c.2) ∧
        I.runFrom C (Impl.blockWrite ps) = some D ∧ I.runFrom D γ = some Q' ∧ Q'.Quiescent ∧
        (∀ ℓ ∈ γ, ℓ.proc ∈ w0 :: ps) ∧ Std w0 rd ws (x.1.1 ++ α ++ Impl.blockWrite ps ++ γ) ∧
        opsOf γ w0 = ws ∧ (respsOf γ w0).length = ws.length := by
      intro x
      obtain ⟨α, C, h1, h2, h3, h4, cs, h5, h6, h7⟩ :=
        ih hnd' hw0' x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2
      have hnd5 : (cs.map Prod.fst).Nodup := by rw [h5]; exact hnd'
      obtain ⟨D, hD, hDo, -⟩ := Impl.blockWrite_run (I := I) hnd5 h7
      rw [h5] at hD hDo
      have hrC : I.run (x.1.1 ++ α) = some C := by rw [Impl.run_append_of_eq I x.2.1]; exact h1
      have hrD : I.run (x.1.1 ++ α ++ Impl.blockWrite ps) = some D := by
        rw [Impl.run_append_of_eq I hrC]; exact hD
      have hstdD : Std w0 rd ws (x.1.1 ++ α ++ Impl.blockWrite ps) :=
        h3.append fun q o hm => absurd hm (not_inv_mem_of_opsOf (by simp) q o)
      obtain ⟨γ, Q', g1, g2, g3, g4, -, g6, g7⟩ := exists_round hof hws ps hw0' hrD hstdD
        (by
          intro q hq'
          rw [(hDo q hq').2]
          by_cases hqw : q = w0
          · subst hqw; exact h4
          · rw [(I.runFrom_other h1 (fun ℓ hℓ he => by
              rcases List.mem_cons.1 (h2 ℓ hℓ) with h | h
              · exact hqw (he ▸ h)
              · exact hq' (he ▸ h))).2]
            exact x.2.2.1 q)
      exact ⟨α, C, cs, D, γ, Q', h1, h2, h3, h4, h5, h6, h7, hD, g1, g2, g3, g4, g6, g7⟩
    choose αf Cf csf Df γf Qf h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 using hstep
    have hrC : ∀ x : G, I.run (x.1.1 ++ αf x) = some (Cf x) := fun x => by
      rw [Impl.run_append_of_eq I x.2.1]; exact h1 x
    have hrD : ∀ x : G, I.run (x.1.1 ++ αf x ++ Impl.blockWrite ps) = some (Df x) := fun x => by
      rw [Impl.run_append_of_eq I (hrC x)]; exact h8 x
    have hrQ : ∀ x : G, I.run (x.1.1 ++ αf x ++ Impl.blockWrite ps ++ γf x) = some (Qf x) :=
      fun x => by rw [Impl.run_append_of_eq I (hrD x)]; exact h9 x
    let nxt : G → G := fun x =>
      ⟨(x.1.1 ++ αf x ++ Impl.blockWrite ps ++ γf x, Qf x), hrQ x, h10 x, h12 x⟩
    let x0 : G := ⟨(αQ, Q), hQ, hq, hs⟩
    let sq : ℕ → G := fun i => nxt^[i] x0
    have hsq : ∀ i, sq (i + 1) = nxt (sq i) := fun i => Function.iterate_succ_apply' _ _ _
    have hmemβ : ∀ ℓ ∈ (Impl.blockWrite ps : List (Label P A)), ℓ.proc ∈ w0 :: ps :=
      fun ℓ hℓ => List.mem_cons_of_mem _ (Impl.mem_blockWrite hℓ)
    have hchain := chain_extends (S := {q | q ∈ w0 :: ps}) (fun i => (sq i).1.1) (fun i => by
      refine ⟨αf (sq i) ++ Impl.blockWrite ps ++ γf (sq i), by
        rw [hsq i]; simp [nxt, List.append_assoc], fun ℓ hℓ => ?_⟩
      simp only [List.mem_append] at hℓ
      rcases hℓ with (h | h) | h
      · exact h2 _ ℓ h
      · exact hmemβ ℓ h
      · exact h11 _ ℓ h)
    -- pigeonhole on the memory after the block writes
    obtain ⟨i, j, hij, hmem⟩ : ∃ i j, i < j ∧ (Df (sq i)).mem = (Df (sq j)).mem := by
      obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun i => (Df (sq i)).mem)
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a, b, h, he⟩
      · exact ⟨b, a, h, he.symm⟩
    set x := sq i with hx
    -- the new process `p` runs solo from `Cᵢ`
    have hpC : (Cf x).pend p = none := by
      rw [(I.runFrom_other (h1 x) (fun ℓ hℓ => hnotp _ (h2 x ℓ hℓ))).2]; exact x.2.2.1 p
    obtain ⟨Cp, hCp⟩ : ∃ Cp, I.step (Cf x) (.inv p (rd p)) = some Cp := by
      classical
      simp [Impl.step, hpC, hrd p hp0]
    have hrCp : I.run (x.1.1 ++ αf x ++ [.inv p (rd p)]) = some Cp := by
      rw [Impl.run_append_of_eq I (hrC x), Impl.runFrom_singleton, hCp]
    have hpCp : Cp.pend p ≠ none := by
      have := (Impl.step_inv hCp).2.2.1; simp [this]
    have hfin := hof Cp p ⟨_, hrCp⟩ hpCp
    let R : Set ι := {i | i ∈ (csf x).map Prod.snd}
    obtain ⟨m, hm1, hm2⟩ := I.exists_solo_until p Cp
      (fun act => ∃ j o k, act = .access j o k ∧ j ∉ R ∧ ¬ (B j).ReadOnly o) hfin
    set Cl := (I.soloStep p)^[m] Cp with hCl
    have hrCl : I.run (x.1.1 ++ αf x ++ [.inv p (rd p)] ++ I.soloLabels p Cp m) = some Cl := by
      rw [Impl.run_append_of_eq I hrCp, Impl.runFrom_soloLabels]
    have hoth : ∀ q, q ≠ p → Cl.loc q = (Cf x).loc q ∧ Cl.pend q = (Cf x).pend q := by
      intro q hq'
      rw [(I.iterate_soloStep_other hq' Cp m).1, (I.iterate_soloStep_other hq' Cp m).2]
      exact Impl.step_other hCp (Ne.symm hq')
    have hsoloStd : ∀ q o, Label.inv q o ∈ I.soloLabels p Cp m →
        (q = w0 ∧ o ∈ ws) ∨ (q ≠ w0 ∧ o = rd q) := fun q o hm =>
      absurd hm (not_inv_mem_of_opsOf (fun q => I.opsOf_soloLabels p q Cp m) q o)
    have hStdCl : Std w0 rd ws (x.1.1 ++ αf x ++ [.inv p (rd p)] ++ I.soloLabels p Cp m) :=
      ((h3 x).append fun q o hm => by
        simp only [List.mem_singleton, Label.inv.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm; exact Or.inr ⟨hp0, rfl⟩).append hsoloStd
    by_cases hpm : Cl.pend p = none
    · -- `p` finished its read writing only covered registers: contradiction
      exfalso
      have hmemR : ∀ i ∉ R, Cl.mem i = (Cf x).mem i := by
        intro i' hi'
        rw [hCl, I.iterate_soloStep_mem_of_readOnly p Cp R m (fun j' hj' i'' o k hact hi'' => by
          by_contra hro
          exact (hm1 j' hj').2 ⟨i'', o, k, hact, hi'', hro⟩) i' hi']
        rw [(Impl.step_inv hCp).2.2.2.2]
      have hnd5 : ((csf x).map Prod.fst).Nodup := by rw [h5 x]; exact hnd'
      obtain ⟨Di', Dx, hDi', hDx, hag⟩ := Impl.blockWrite_agreeOn (I := I)
        (Q := {q | q ≠ p}) (cs := csf x) hnd5
        (fun c hc => hnotp _ (List.mem_cons_of_mem _ (by
          rw [← h5 x]; exact List.mem_map_of_mem hc)))
        (C := Cl) (D := Cf x)
        (fun c hc => by
          have hcp : c.1 ≠ p := hnotp _ (List.mem_cons_of_mem _ (by
            rw [← h5 x]; exact List.mem_map_of_mem hc))
          exact (h7 x c hc).congr (hoth _ hcp).1.symm (hoth _ hcp).2.symm)
        (fun q hq' => (hoth q hq').1) (fun q hq' => (hoth q hq').2) hmemR
      rw [h5 x] at hDi' hDx
      rw [h8 x] at hDx
      cases hDx
      -- the dirty extension: from `Dᵢ` to `Dⱼ`
      obtain ⟨δ, hδ, hδS⟩ := hchain (i + 1) j hij
      set y := sq j with hy
      have hsq1 : (sq (i + 1)).1.1 = x.1.1 ++ αf x ++ Impl.blockWrite ps ++ γf x := by
        rw [hsq i]
      set σ := γf x ++ (δ ++ αf y ++ Impl.blockWrite ps) with hσdef
      have hEj : y.1.1 ++ αf y ++ Impl.blockWrite ps =
          x.1.1 ++ αf x ++ Impl.blockWrite ps ++ σ := by
        rw [hδ, hsq1]; simp only [hσdef, List.append_assoc]
      have hσS : ∀ ℓ ∈ σ, ℓ.proc ∈ w0 :: ps := by
        intro ℓ hℓ
        simp only [hσdef, List.mem_append] at hℓ
        rcases hℓ with h | (h | h) | h
        · exact h11 x ℓ h
        · exact hδS ℓ h
        · exact h2 y ℓ h
        · exact hmemβ ℓ h
      have hσ : I.runFrom (Df x) σ = some (Df y) :=
        runFrom_of_run_append (by rw [← hEj]; exact hrD y) (hrD x)
      obtain ⟨Dj', hDj', hag'⟩ := Impl.runFrom_agreeOn hag.symm
        (fun ℓ hℓ => hnotp _ (hσS ℓ hℓ)) hσ
      set E₁ := x.1.1 ++ αf x ++ [.inv p (rd p)] ++ I.soloLabels p Cp m ++
        Impl.blockWrite ps with hE₁
      have hrE₁ : I.run E₁ = some Di' := by rw [Impl.run_append_of_eq I hrCl]; exact hDi'
      have hrE₂ : I.run (E₁ ++ σ) = some Dj' := by rw [Impl.run_append_of_eq I hrE₁]; exact hDj'
      have hDi'o : ∀ q, q ∉ ps → Di'.loc q = Cl.loc q ∧ Di'.pend q = Cl.pend q :=
        fun q hq' => Impl.runFrom_blockWrite_other hDi' hq'
      have hpDi : Di'.pend p = none := by rw [(hDi'o p hpps).2]; exact hpm
      have hwDi : Di'.pend w0 = none := by
        rw [(hDi'o w0 hw0').2, (hoth w0 (Ne.symm hp0)).2]; exact h4 x
      have hσp := I.runFrom_other hDj' (q := p) (fun ℓ hℓ => hnotp _ (hσS ℓ hℓ))
      have hStdE₁ : Std w0 rd ws E₁ :=
        hStdCl.append fun q o hm => absurd hm (not_inv_mem_of_opsOf (by simp) q o)
      have hStdE₂ : Std w0 rd ws (E₁ ++ σ) := by
        refine hStdE₁.append fun q o hm => ?_
        have hStdEj : Std w0 rd ws (y.1.1 ++ αf y ++ Impl.blockWrite ps) :=
          (h3 y).append fun q o hm => absurd hm (not_inv_mem_of_opsOf (by simp) q o)
        rw [hEj] at hStdEj
        exact hStdEj q o (List.mem_append_right _ hm)
      have hclean : Clean w0 rd p E₁ := by
        have := clean_of_split (I := I) (rd := rd) hp0 (hrC x) (h4 x)
          (rest := I.soloLabels p Cp m ++ Impl.blockWrite ps) (C := Di')
          (by rw [← hrE₁, hE₁]; simp [List.append_assoc]) hpDi
          (by
            intro ℓ hℓ he
            rcases List.mem_append.1 hℓ with h | h
            · rw [I.soloLabels_proc p Cp m ℓ h] at he; exact hp0 he
            · exact hw0' (he ▸ Impl.mem_blockWrite h))
          (by simp [I.opsOf_soloLabels])
        simpa [hE₁, List.append_assoc] using this
      have hdirty : Dirty w0 ws p (E₁ ++ σ) := by
        have := dirty_of_split (I := I) (w0 := w0) (ws := ws) (p := p) (γ := γf x)
          (τ := δ ++ αf y ++ Impl.blockWrite ps) hrE₁ hpDi hwDi (h13 x) (h14 x)
          (fun ℓ hℓ => hnotp _ (hσS ℓ (by simpa [hσdef] using hℓ)))
        simpa [hσdef, List.append_assoc] using this
      refine hsep p hp0 E₁ (E₁ ++ σ) Di' Dj' hrE₁ hrE₂ hStdE₁ hStdE₂ hclean hdirty hpDi
        (by rw [hσp.2]; exact hpDi) ⟨?_, hσp.1.symm, hσp.2.symm⟩
      rw [hag.mem, hmem, hag'.mem]
    · -- `p` covers a register outside the covered set
      obtain ⟨j', o, k, hact, hj', hro⟩ := hm2.resolve_left hpm
      obtain ⟨δ0, hδ0, hδ0S⟩ := hchain 0 i (Nat.zero_le _)
      have hx0 : x.1.1 = αQ ++ δ0 := hδ0
      rw [hx0] at hrCl hStdCl
      refine ⟨δ0 ++ αf x ++ [.inv p (rd p)] ++ I.soloLabels p Cp m, Cl,
        runFrom_of_run_append (by rw [← hrCl]; simp [List.append_assoc]) hQ,
        fun ℓ hℓ => ?_, by simpa [List.append_assoc] using hStdCl,
        by rw [(hoth w0 (Ne.symm hp0)).2]; exact h4 x, (p, j') :: csf x, by simp [h5 x], ?_, ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hℓ
        rcases hℓ with ((h | h) | h) | h
        · rcases List.mem_cons.1 (hδ0S ℓ h) with h' | h'
          · rw [h']; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')
        · rcases List.mem_cons.1 (h2 x ℓ h) with h' | h'
          · rw [h']; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')
        · subst h; exact List.mem_cons_of_mem _ List.mem_cons_self
        · rw [I.soloLabels_proc p Cp m ℓ h]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨hj', h6 x⟩
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · refine ⟨hpm, o, k, hact, ?_⟩
          rcases hreg j' o with h | h
          · exact absurd h hro
          · exact h
        · have hcp : c.1 ≠ p := hnotp _ (List.mem_cons_of_mem _ (by
            rw [← h5 x]; exact List.mem_map_of_mem hc))
          exact (h7 x c hc).congr (hoth _ hcp).1.symm (hoth _ hcp).2.symm

/-- **Theorem 1(a), abstract form**: an obstruction-free implementation from finitely many bounded
registers (base objects whose operations are reads or blind writes) that separates clean from dirty
configurations needs at least `n - 1` base objects, `n` the number of processes. -/
theorem card_le_of_separates [Fintype P] [Fintype ι] [∀ i, Finite (B i).State]
    (hreg : ∀ i (o : (B i).Op), (B i).ReadOnly o ∨ (B i).Overwrites o)
    (hof : I.ObstructionFree) (hsep : Separates I w0 rd ws)
    (hrd : ∀ p, p ≠ w0 → I.allowed p (rd p)) (hws : ∀ o ∈ ws, I.allowed w0 o) :
    Fintype.card P - 1 ≤ Fintype.card ι := by
  set ps := (Finset.univ.erase w0).toList
  obtain ⟨-, -, -, -, -, -, cs, h5, h6, -⟩ := lemma1 hreg hof hsep hrd hws ps
    (Finset.nodup_toList _) (by simp [ps]) [] I.initCfg rfl (fun _ => rfl)
    (fun _ _ h => by simp at h)
  have h1 : ps.length = Fintype.card P - 1 := by
    simp [ps, Finset.card_erase_of_mem]
  calc Fintype.card P - 1 = (cs.map Prod.snd).length := by rw [← h1, ← h5]; simp
    _ = (cs.map Prod.snd).toFinset.card := (List.toFinset_card_of_nodup h6).symm
    _ ≤ Fintype.card ι := Finset.card_le_univ _

end Cslib.SharedMemory.ABADetection
