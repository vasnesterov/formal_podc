import Papers.PODC2015.ABADetection.Lemma2

/-!
# Lemma 3: a time–space tradeoff for writable CAS objects (Section 2.2)

`lemma3`: let an obstruction-free implementation from finitely many bounded writable CAS objects,
with worst-case step complexity at most `t`, separate clean from dirty configurations
(`Separates`). Then from every reachable quiescent configuration `Q` and for every list `ps` of
distinct readers, a `(ps ∪ {w0})`-only execution leads to a configuration `C` where
(i) all processes outside `ps` are idle, (ii) some ordering of `ps` is a successful schedule for
`C`, and (iii) for every object `R`, at most `t` processes of `ps` are poised to `Write` `R` and at
most `t` are poised to `CAS` `R`.

The proof follows the paper: iterate (induction hypothesis, successful block, finishing round)
forever, find `i < j` with configurations `Cᵢ`, `Cⱼ` of equal *signature* (memory and poised
accesses), apply Lemma 2 to the new reader `p` invoked in `Cᵢ`, and replay the schedule from `Dᵢ`
to `Cⱼ` and the block `βᵢ`. Case (a) of Lemma 2 contradicts `Separates`; in cases (b), (c) the new
configuration satisfies (i)–(iii).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq P] [DecidableEq ι] [DecidableEq V] {v₀ : V}
  {I : Impl A (fun _ : ι => wcasObj V v₀) P L} {w0 : P} {rd : P → A.Op} {ws : List A.Op}

lemma exists_act_of_poisedAcc {C : Config A (fun _ : ι => wcasObj V v₀) P L} {q : P} {R : ι}
    {o : WCasOp V} (h : poisedAcc I C q = some (R, o)) :
    ∃ k, I.act q (C.loc q) = .access R o k := by
  unfold poisedAcc at h
  split at h
  · rename_i i' o' k' h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨k', h'⟩
  · simp at h

open Classical in
lemma WCov_congr {C D : Config A (fun _ : ι => wcasObj V v₀) P L} {R : ι} {S : Finset P}
    (h : ∀ q ∈ S, poisedAcc I C q = poisedAcc I D q) : WCov I C R S = WCov I D R S := by
  unfold WCov
  exact Finset.filter_congr fun q hq => by rw [h q hq]

open Classical in
lemma CCov_congr {C D : Config A (fun _ : ι => wcasObj V v₀) P L} {R : ι} {S : Finset P}
    (h : ∀ q ∈ S, poisedAcc I C q = poisedAcc I D q) : CCov I C R S = CCov I D R S := by
  unfold CCov
  exact Finset.filter_congr fun q hq => by rw [h q hq]

open Classical in
lemma WCov_insert_card_le (C : Config A (fun _ : ι => wcasObj V v₀) P L) (R : ι) (S : Finset P)
    (p : P) : (WCov I C R (insert p S)).card ≤ (WCov I C R S).card +
      (if ∃ v, poisedAcc I C p = some (R, .write v) then 1 else 0) := by
  classical
  unfold WCov
  rw [Finset.filter_insert]
  split_ifs with h
  · exact Finset.card_insert_le _ _
  · simp

open Classical in
lemma CCov_insert_card_le (C : Config A (fun _ : ι => wcasObj V v₀) P L) (R : ι) (S : Finset P)
    (p : P) : (CCov I C R (insert p S)).card ≤ (CCov I C R S).card +
      (if ∃ x y, poisedAcc I C p = some (R, .cas x y) then 1 else 0) := by
  classical
  unfold CCov
  rw [Finset.filter_insert]
  split_ifs with h
  · exact Finset.card_insert_le _ _
  · simp

open Classical in
/-- **Lemma 3** of [Aghazadeh–Woelfel, PODC 2015]. -/
theorem lemma3 [Fintype P] [Finite ι] [Finite V] (t : ℕ)
    (hof : I.ObstructionFree) (hbound : StepBound I t) (hsep : Separates I w0 rd ws)
    (hrd : ∀ p, p ≠ w0 → I.allowed p (rd p)) (hws : ∀ o ∈ ws, I.allowed w0 o) :
    ∀ ps : List P, ps.Nodup → w0 ∉ ps → ∀ αQ Q, I.run αQ = some Q → Q.Quiescent →
      Std w0 rd ws αQ →
      ∃ α C β, I.runFrom Q α = some C ∧ (∀ ℓ ∈ α, ℓ.proc ∈ w0 :: ps) ∧
        Std w0 rd ws (αQ ++ α) ∧ (∀ q, q ∉ ps → C.pend q = none) ∧ β.Perm ps ∧ Succ I C β ∧
        ∀ R, (WCov I C R ps.toFinset).card ≤ t ∧ (CCov I C R ps.toFinset).card ≤ t := by
  intro ps
  induction ps with
  | nil =>
    intro _ _ αQ Q hQ hq hs
    exact ⟨[], Q, [], rfl, by simp, by simpa using hs, fun q _ => hq q, List.Perm.refl _,
      trivial, fun R => by simp [WCov, CCov]⟩
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
    let G := {x : List (Label P A) × Config A (fun _ : ι => wcasObj V v₀) P L //
      I.run x.1 = some x.2 ∧ x.2.Quiescent ∧ Std w0 rd ws x.1}
    have hstep : ∀ x : G, ∃ (α : List (Label P A)) (C : Config A (fun _ : ι => wcasObj V v₀) P L)
        (β : List P) (D : Config A (fun _ : ι => wcasObj V v₀) P L) (γ : List (Label P A))
        (Q' : Config A (fun _ : ι => wcasObj V v₀) P L),
        I.runFrom x.1.2 α = some C ∧ (∀ ℓ ∈ α, ℓ.proc ∈ w0 :: ps) ∧
        Std w0 rd ws (x.1.1 ++ α) ∧ (∀ q, q ∉ ps → C.pend q = none) ∧ β.Perm ps ∧
        Succ I C β ∧
        (∀ R, (WCov I C R ps.toFinset).card ≤ t ∧ (CCov I C R ps.toFinset).card ≤ t) ∧
        I.runFrom C (Impl.blockWrite β) = some D ∧ I.runFrom D γ = some Q' ∧ Q'.Quiescent ∧
        (∀ ℓ ∈ γ, ℓ.proc ∈ w0 :: ps) ∧ Std w0 rd ws (x.1.1 ++ α ++ Impl.blockWrite β ++ γ) ∧
        opsOf γ w0 = ws ∧ (respsOf γ w0).length = ws.length := by
      intro x
      obtain ⟨α, C, β, h1, h2, h3, h4, h5, h6, h7⟩ :=
        ih hnd' hw0' x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2
      obtain ⟨D, hD⟩ := h6.run
      have hrC : I.run (x.1.1 ++ α) = some C := by rw [Impl.run_append_of_eq I x.2.1]; exact h1
      have hrD : I.run (x.1.1 ++ α ++ Impl.blockWrite β) = some D := by
        rw [Impl.run_append_of_eq I hrC]; exact hD
      have hstdD : Std w0 rd ws (x.1.1 ++ α ++ Impl.blockWrite β) :=
        h3.append fun q o hm => absurd hm (not_inv_mem_of_opsOf (by simp) q o)
      obtain ⟨γ, Q', g1, g2, g3, g4, -, g6, g7⟩ := exists_round hof hws ps hw0' hrD hstdD
        (by
          intro q hq'
          have hqβ : q ∉ β := fun h => hq' (h5.subset h)
          rw [(Impl.runFrom_blockWrite_other hD hqβ).2]
          exact h4 q hq')
      exact ⟨α, C, β, D, γ, Q', h1, h2, h3, h4, h5, h6, h7, hD, g1, g2, g3, g4, g6, g7⟩
    choose αf Cf βf Df γf Qf h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 using hstep
    have hrC : ∀ x : G, I.run (x.1.1 ++ αf x) = some (Cf x) := fun x => by
      rw [Impl.run_append_of_eq I x.2.1]; exact h1 x
    have hrD : ∀ x : G, I.run (x.1.1 ++ αf x ++ Impl.blockWrite (βf x)) = some (Df x) :=
      fun x => by rw [Impl.run_append_of_eq I (hrC x)]; exact h8 x
    have hrQ : ∀ x : G, I.run (x.1.1 ++ αf x ++ Impl.blockWrite (βf x) ++ γf x) =
        some (Qf x) := fun x => by rw [Impl.run_append_of_eq I (hrD x)]; exact h9 x
    let nxt : G → G := fun x =>
      ⟨(x.1.1 ++ αf x ++ Impl.blockWrite (βf x) ++ γf x, Qf x), hrQ x, h10 x, h12 x⟩
    let x0 : G := ⟨(αQ, Q), hQ, hq, hs⟩
    let sq : ℕ → G := fun i => nxt^[i] x0
    have hsq : ∀ i, sq (i + 1) = nxt (sq i) := fun i => Function.iterate_succ_apply' _ _ _
    have hmemβ : ∀ x : G, ∀ ℓ ∈ (Impl.blockWrite (βf x) : List (Label P A)),
        ℓ.proc ∈ w0 :: ps :=
      fun x ℓ hℓ => List.mem_cons_of_mem _ ((h5 x).subset (Impl.mem_blockWrite hℓ))
    have hchain := chain_extends (S := {q | q ∈ w0 :: ps}) (fun i => (sq i).1.1) (fun i => by
      refine ⟨αf (sq i) ++ Impl.blockWrite (βf (sq i)) ++ γf (sq i), by
        rw [hsq i]; simp [nxt, List.append_assoc], fun ℓ hℓ => ?_⟩
      simp only [List.mem_append] at hℓ
      rcases hℓ with (h | h) | h
      · exact h2 _ ℓ h
      · exact hmemβ _ ℓ h
      · exact h11 _ ℓ h)
    -- pigeonhole on signatures
    obtain ⟨i, j, hij, hsig⟩ : ∃ i j, i < j ∧
        ((Cf (sq i)).mem, fun q => poisedAcc I (Cf (sq i)) q) =
          ((Cf (sq j)).mem, fun q => poisedAcc I (Cf (sq j)) q) := by
      obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite
        (β := (ι → V) × (P → Option (ι × WCasOp V)))
        (fun i => ((Cf (sq i)).mem, fun q => poisedAcc I (Cf (sq i)) q))
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a, b, h, he⟩
      · exact ⟨b, a, h, he.symm⟩
    simp only [Prod.mk.injEq] at hsig
    obtain ⟨hmemij, hpaij⟩ := hsig
    set x := sq i with hx
    set y := sq j with hy
    have hβx : p ∉ βf x := fun h => hpps ((h5 x).subset h)
    have hβnd : (βf x).Nodup := (h5 x).nodup_iff.2 hnd'
    -- the new reader `p` is invoked in `Cᵢ`
    have hpC : (Cf x).pend p = none := h4 x p (by simp [hpps])
    obtain ⟨Cp, hCp⟩ : ∃ Cp, I.step (Cf x) (.inv p (rd p)) = some Cp := by
      classical
      simp [Impl.step, hpC, hrd p hp0]
    have hrCp : I.run (x.1.1 ++ αf x ++ [.inv p (rd p)]) = some Cp := by
      rw [Impl.run_append_of_eq I (hrC x), Impl.runFrom_singleton, hCp]
    have hagCp : Impl.AgreeOn {q | q ≠ p} (Cf x) Cp :=
      ⟨(Impl.step_inv hCp).2.2.2.2.symm, fun q hq' => (Impl.step_other hCp (Ne.symm hq')).1.symm,
        fun q hq' => (Impl.step_other hCp (Ne.symm hq')).2.symm⟩
    have hbud : Budget I Cp p t := by
      intro δ C' hδ hδp
      refine hbound (x.1.1 ++ αf x) p (rd p) δ ⟨C', ?_⟩ (fun r hr => ?_)
      · rw [show x.1.1 ++ αf x ++ .inv p (rd p) :: δ = x.1.1 ++ αf x ++ [.inv p (rd p)] ++ δ by
          simp, Impl.run_append_of_eq I hrCp, hδ]
      · have := hδp _ hr rfl; cases this
    obtain ⟨hsuccCp, Dx₁, Dp, hDx₁, hDp, hagD⟩ :=
      Succ.agreeOn hagCp (fun q hq' => fun he => hβx (he ▸ hq')) (h6 x)
    rw [h8 x] at hDx₁; cases hDx₁
    obtain ⟨D, σ, D', hD, hσ, hσl, hσops, hagDD', hcase⟩ :=
      lemma2 p t Cp (βf x) hβx hβnd hsuccCp hbud
    rw [hDp] at hD; cases hD
    have hag1 : Impl.AgreeOn {q | q ≠ p} (Df x) D' := hagD.trans hagDD'
    set E₁ := x.1.1 ++ αf x ++ [.inv p (rd p)] ++ σ with hE₁
    have hrE₁ : I.run E₁ = some D' := by rw [Impl.run_append_of_eq I hrCp]; exact hσ
    -- replay the schedule from `Dᵢ` to `Cⱼ`
    obtain ⟨δ, hδ, hδS⟩ := hchain (i + 1) j hij
    have hsq1 : (sq (i + 1)).1.1 = x.1.1 ++ αf x ++ Impl.blockWrite (βf x) ++ γf x := by
      rw [hsq i]
    set σ₂ := γf x ++ (δ ++ αf y) with hσ₂def
    have hEj : y.1.1 ++ αf y = x.1.1 ++ αf x ++ Impl.blockWrite (βf x) ++ σ₂ := by
      have hδ' : y.1.1 = (sq (i + 1)).1.1 ++ δ := hδ
      rw [hδ', hsq1]; simp only [hσ₂def, List.append_assoc]
    have hσ₂S : ∀ ℓ ∈ σ₂, ℓ.proc ∈ w0 :: ps := by
      intro ℓ hℓ
      simp only [hσ₂def, List.mem_append] at hℓ
      rcases hℓ with h | h | h
      · exact h11 x ℓ h
      · exact hδS ℓ h
      · exact h2 y ℓ h
    have hσ₂ : I.runFrom (Df x) σ₂ = some (Cf y) :=
      runFrom_of_run_append (by rw [← hEj]; exact hrC y) (hrD x)
    obtain ⟨Cj', hCj', hagj⟩ := Impl.runFrom_agreeOn hag1
      (fun ℓ hℓ => hnotp _ (hσ₂S ℓ hℓ)) hσ₂
    have hrCj' : I.run (E₁ ++ σ₂) = some Cj' := by rw [Impl.run_append_of_eq I hrE₁]; exact hCj'
    have hpσ₂ := I.runFrom_other hCj' (q := p) (fun ℓ hℓ => hnotp _ (hσ₂S ℓ hℓ))
    -- the block `βᵢ` from `C'ⱼ`
    have hpaCj : ∀ q ∈ βf x, Cj'.pend q ≠ none ∧ poisedAcc I (Cf x) q = poisedAcc I Cj' q := by
      intro q hq'
      have hqp : q ≠ p := fun he => hβx (he ▸ hq')
      have hqy : q ∈ βf y := (h5 y).symm.subset ((h5 x).subset hq')
      refine ⟨?_, ?_⟩
      · rw [← hagj.pend q hqp]; exact ((h6 y).poised ((h5 y).nodup_iff.2 hnd') q hqy).1
      · rw [congrFun hpaij q]; exact poisedAcc_congr (hagj.loc q hqp)
    obtain ⟨hsuccCj, Dx₂, Dj', hDx₂, hDj', hmemDj⟩ :=
      Succ.congr hβnd (hmemij.trans hagj.mem) hpaCj (h6 x)
    rw [h8 x] at hDx₂; cases hDx₂
    have hrDj' : I.run (E₁ ++ σ₂ ++ Impl.blockWrite (βf x)) = some Dj' := by
      rw [Impl.run_append_of_eq I hrCj']; exact hDj'
    have hpβ := Impl.runFrom_blockWrite_other hDj' hβx
    have hσl' : ∀ ℓ ∈ σ, ℓ.proc ≠ w0 := by
      intro ℓ hℓ he
      rcases List.mem_cons.1 (hσl ℓ hℓ) with h | h
      · exact hp0 (he ▸ h).symm
      · exact hw0' ((h5 x).subset (he ▸ h))
    have hStdE₁ : Std w0 rd ws E₁ :=
      (((h3 x).append fun q o hm => by
        simp only [List.mem_singleton, Label.inv.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm; exact Or.inr ⟨hp0, rfl⟩).append
        fun q o hm => absurd hm (not_inv_mem_of_opsOf hσops q o))
    have hStdσ₂ : ∀ q o, Label.inv q o ∈ σ₂ → (q = w0 ∧ o ∈ ws) ∨ (q ≠ w0 ∧ o = rd q) := by
      intro q o hm
      have := h3 y
      rw [hEj] at this
      exact this q o (List.mem_append_right _ hm)
    have hStdCj : Std w0 rd ws (E₁ ++ σ₂) := hStdE₁.append hStdσ₂
    by_cases hpD' : D'.pend p = none
    · -- case (a): contradiction with `Separates`
      exfalso
      have hwD' : D'.pend w0 = none := by
        rw [← hag1.pend w0 (Ne.symm hp0), (Impl.runFrom_blockWrite_other (h8 x)
          (fun h => hw0' ((h5 x).subset h))).2]
        exact h4 x w0 hw0'
      have hclean : Clean w0 rd p E₁ := by
        have := clean_of_split (I := I) (rd := rd) hp0 (hrC x) (h4 x w0 hw0') (rest := σ)
          (C := D') (by rw [← hrE₁, hE₁]; simp [List.append_assoc]) hpD' hσl' (hσops p)
        simpa [hE₁, List.append_assoc] using this
      have hdirty : Dirty w0 ws p (E₁ ++ σ₂ ++ Impl.blockWrite (βf x)) := by
        have := dirty_of_split (I := I) (w0 := w0) (ws := ws) (p := p) (γ := γf x)
          (τ := δ ++ αf y ++ Impl.blockWrite (βf x)) hrE₁ hpD' hwD' (h13 x) (h14 x)
          (fun ℓ hℓ => by
            simp only [List.mem_append] at hℓ
            rcases hℓ with h | (h | h) | h
            · exact hnotp _ (h11 x ℓ h)
            · exact hnotp _ (hδS ℓ h)
            · exact hnotp _ (h2 y ℓ h)
            · exact hnotp _ (hmemβ x ℓ h))
        simpa [hσ₂def, List.append_assoc] using this
      have hStdE₂ : Std w0 rd ws (E₁ ++ σ₂ ++ Impl.blockWrite (βf x)) :=
        hStdCj.append fun q o hm => absurd hm (not_inv_mem_of_opsOf (by simp) q o)
      refine hsep p hp0 E₁ _ D' Dj' hrE₁ hrDj' hStdE₁ hStdE₂ hclean hdirty hpD'
        (by rw [hpβ.2, hpσ₂.2]; exact hpD') ⟨?_, ?_, ?_⟩
      · rw [← hag1.mem, hmemDj]
      · rw [hpβ.1, hpσ₂.1]
      · rw [hpβ.2, hpσ₂.2]
    · -- cases (b), (c): `p` joins the successful schedule
      have hcase' := hcase.resolve_left hpD'
      obtain ⟨δ0, hδ0, hδ0S⟩ := hchain 0 i (Nat.zero_le _)
      have hx0 : x.1.1 = αQ ++ δ0 := hδ0
      have hpaD : poisedAcc I Dj' p = poisedAcc I D' p :=
        poisedAcc_congr (hpβ.1.trans hpσ₂.1)
      have hpendDj : Dj'.pend p ≠ none := by rw [hpβ.2, hpσ₂.2]; exact hpD'
      have hmemDj' : Dj'.mem = D'.mem := by rw [← hmemDj, hag1.mem]
      -- the poised processes of `ps` in `C'ⱼ` are those of `Cᵢ`
      have hpaS : ∀ q ∈ ps.toFinset, poisedAcc I Cj' q = poisedAcc I (Cf x) q := by
        intro q hq'
        have hqp : q ≠ p := fun he => hpps (he ▸ List.mem_toFinset.1 hq')
        rw [congrFun hpaij q]; exact (poisedAcc_congr (hagj.loc q hqp)).symm
      have hpaS' : ∀ q ∈ (βf x).toFinset, poisedAcc I Cp q = poisedAcc I (Cf x) q := by
        intro q hq'
        have hqp : q ≠ p := fun he => hβx (he ▸ List.mem_toFinset.1 hq')
        exact (poisedAcc_congr (hagCp.loc q hqp)).symm
      have htf : (βf x).toFinset = ps.toFinset := by
        ext q; simp [(h5 x).mem_iff]
      have hW : ∀ R, (WCov I Cj' R (p :: ps).toFinset).card ≤ (WCov I (Cf x) R ps.toFinset).card +
          (if ∃ v, poisedAcc I D' p = some (R, .write v) then 1 else 0) := by
        intro R
        have := WCov_insert_card_le (I := I) Cj' R ps.toFinset p
        have hpaCj : poisedAcc I Cj' p = poisedAcc I D' p := poisedAcc_congr hpσ₂.1
        rw [WCov_congr hpaS, hpaCj] at this
        rw [List.toFinset_cons]; exact this
      have hC : ∀ R, (CCov I Cj' R (p :: ps).toFinset).card ≤ (CCov I (Cf x) R ps.toFinset).card +
          (if ∃ x y, poisedAcc I D' p = some (R, .cas x y) then 1 else 0) := by
        intro R
        have := CCov_insert_card_le (I := I) Cj' R ps.toFinset p
        have hpaCj : poisedAcc I Cj' p = poisedAcc I D' p := poisedAcc_congr hpσ₂.1
        rw [CCov_congr hpaS, hpaCj] at this
        rw [List.toFinset_cons]; exact this
      have hWp : ∀ R, WCov I Cp R (βf x).toFinset = WCov I (Cf x) R ps.toFinset := fun R => by
        rw [WCov_congr hpaS', htf]
      have hCp' : ∀ R, CCov I Cp R (βf x).toFinset = CCov I (Cf x) R ps.toFinset := fun R => by
        rw [CCov_congr hpaS', htf]
      -- the step of `p` after the block is successful
      have hsuccp : Succ I Dj' [p] := by
        rcases hcase' with ⟨-, R, v, hpa, -⟩ | ⟨-, R, x', y', hpa, hxy, hmx, -⟩
        · rw [← hpaD] at hpa
          obtain ⟨k, hk⟩ := exists_act_of_poisedAcc hpa
          exact ⟨hpendDj, R, _, k, _, hk, trivial, step_tau_eq hpendDj hk, trivial⟩
        · rw [← hpaD] at hpa
          obtain ⟨k, hk⟩ := exists_act_of_poisedAcc hpa
          exact ⟨hpendDj, R, _, k, _, hk, ⟨hxy, by rw [hmemDj']; exact hmx⟩,
            step_tau_eq hpendDj hk, trivial⟩
      refine ⟨δ0 ++ αf x ++ [.inv p (rd p)] ++ σ ++ σ₂, Cj', βf x ++ [p],
        runFrom_of_run_append (by rw [← hrCj', hE₁, hx0]; simp [List.append_assoc]) hQ,
        fun ℓ hℓ => ?_, ?_, fun q hq' => ?_, ?_, succ_append_singleton hsuccCj hDj' hsuccp,
        fun R => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hℓ
        have hsub : ∀ r, r ∈ w0 :: ps → r ∈ w0 :: p :: ps := fun r hr => by
          rcases List.mem_cons.1 hr with h | h
          · rw [h]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
        rcases hℓ with (((h | h) | h) | h) | h
        · exact hsub _ (hδ0S ℓ h)
        · exact hsub _ (h2 x ℓ h)
        · subst h; exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.1 (hσl ℓ h) with h' | h'
          · rw [h']; exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((h5 x).subset h'))
        · exact hsub _ (hσ₂S ℓ h)
      · have := hStdCj
        rw [hE₁, hx0] at this
        simpa [List.append_assoc] using this
      · have hqp : q ≠ p := fun he => hq' (he ▸ List.mem_cons_self)
        rw [← hagj.pend q hqp]
        exact h4 y q (fun h => hq' (List.mem_cons_of_mem _ h))
      · exact (List.perm_append_singleton p (βf x)).trans ((h5 x).cons p)
      · have hb := h7 x R
        refine ⟨(hW R).trans ?_, (hC R).trans ?_⟩
        · split_ifs with hwr
          · rcases hcase' with ⟨-, R', v, hpa, hlt⟩ | ⟨-, R', x', y', hpa, -, -, -⟩
            · obtain ⟨v', hv'⟩ := hwr
              rw [hv'] at hpa
              simp only [Option.some.injEq, Prod.mk.injEq] at hpa
              obtain ⟨rfl, -⟩ := hpa
              rw [hWp] at hlt; omega
            · obtain ⟨v', hv'⟩ := hwr
              rw [hv'] at hpa; simp at hpa
          · simpa using hb.1
        · split_ifs with hcr
          · rcases hcase' with ⟨-, R', v, hpa, -⟩ | ⟨-, R', x', y', hpa, -, -, hlt⟩
            · obtain ⟨a, b, hab⟩ := hcr
              rw [hab] at hpa; simp at hpa
            · obtain ⟨a, b, hab⟩ := hcr
              rw [hab] at hpa
              simp only [Option.some.injEq, Prod.mk.injEq] at hpa
              obtain ⟨rfl, -⟩ := hpa
              rw [hWp, hCp'] at hlt; omega
          · simpa using hb.2

end Cslib.SharedMemory.ABADetection
