import Papers.PODC2022.ConsensusFromSwap.ReadableSwap

/-!
# Readable binary swap objects: `n − 2` objects are necessary (Section 5.1)

Lemma 16 and Theorem 18 of Ovens (PODC 2022): every obstruction-free binary consensus algorithm
for `n` processes from readable binary swap objects uses at least `n − 2` objects.

`Inv16` is the statement of Lemma 16 for a configuration `C`, the set `X` of objects whose value
must not change (property (c)), and the list `cs` of pairs (covering process, covered object)
(the paper's `S_i` and `Y_i`, property (b)), with property (d) for the block update by `cs`.
-/

namespace ConsensusFromSwap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {P : Type} [DecidableEq P]
  {A : Alg (fun _ : ι => rswapObj Bool false) P Bool}

/-- The properties (a)–(d) of Lemma 16 at stage `i`. -/
structure Inv16 (C₀ : Cfg A) (q₀ q₁ : P) (ps : List P) (i : ℕ) (C : Cfg A) (X : Finset ι)
    (cs : List (P × ι)) : Prop where
  reach : Reach C₀ C
  /-- (a) `Q` is bivalent. -/
  biv : Biv {q₀, q₁} C
  /-- (b) the processes of `cs` cover the objects of `cs` (`S_i` covers `Y_i`). -/
  cov : Covering C cs
  objs_nd : (cs.map Prod.snd).Nodup
  disj : ∀ c ∈ cs, c.2 ∉ X
  card : X.card + cs.length = i
  procs : ∀ c ∈ cs, c.1 ∈ ps.take i
  /-- (c) changing an object of `X_i` makes `Q` univalent. -/
  chg : ∀ lam : List P, (∀ r ∈ lam, r ∈ RS q₀ q₁ ps i) → ∀ x ∈ X, Changes C lam x →
    ¬ Biv {q₀, q₁} (run C lam)
  /-- (d) a block update changing an object of `Y_i` makes `Q` univalent. -/
  blk : ∀ lam : List P, (∀ r ∈ lam, r ∈ RS q₀ q₁ ps i) →
    (∃ c ∈ cs, (run (run C lam) (block cs)).mem c.2 ≠ (run C lam).mem c.2) →
    ¬ Biv {q₀, q₁} (run (run C lam) (block cs))

lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

section Lemma16

variable {C₀ : Cfg A} (hS : Setting C₀) {q₀ q₁ : P} (hq : q₀ ≠ q₁) {ps : List P}
  (hnd : (q₀ :: q₁ :: ps).Nodup)
include hS hq hnd

lemma lemma16_zero (hb : Biv {q₀, q₁} C₀) : Inv16 C₀ q₀ q₁ ps 0 C₀ ∅ [] where
  reach := Reach.refl C₀
  biv := hb
  cov := ⟨by simp, by simp⟩
  objs_nd := by simp
  disj := by simp
  card := by simp
  procs := by simp
  chg := by simp
  blk := by simp

set_option maxHeartbeats 1000000 in
/-- The induction step of **Lemma 16** of [Ovens 2022]. -/
theorem lemma16_step {i : ℕ} (hi : i < ps.length) {C : Cfg A} {X : Finset ι}
    {cs : List (P × ι)} (I : Inv16 C₀ q₀ q₁ ps i C X cs) :
    ∃ C' X' cs', Inv16 C₀ q₀ q₁ ps (i + 1) C' X' cs' := by
  classical
  set Q : Set P := {q₀, q₁} with hQdef
  set p := ps[i] with hpdef
  set R := RS q₀ q₁ ps (i + 1) with hRdef
  set RI := RS q₀ q₁ ps i with hRIdef
  have hRi : RI = insert p R := RS_succ hi
  have hpR : p ∉ R := not_mem_RS_succ hnd hi
  have hQR : Q ⊆ R := Q_sub_RS _
  have hRsub : R ⊆ RI := RS_mono (Nat.le_succ i)
  have hcsR : ∀ c ∈ cs, c.1 ∉ RI := fun c hc => not_mem_RS_of_take hnd (I.procs c hc)
  have hbR : ∀ r ∈ RI, r ∉ block cs := by
    intro r hr hrb
    obtain ⟨x, hx⟩ := mem_block.1 hrb
    exact hcsR _ hx hr
  have hQb : ∀ q ∈ Q, q ∉ block cs := fun q hq => hbR q (Q_sub_RS i hq)
  have hpRi : p ∈ RI := by rw [hRi]; exact Set.mem_insert _ _
  have hpb : p ∉ block cs := hbR p hpRi
  have hpQ : p ∉ Q := fun h => hpR (hQR h)
  have hcsQ : ∀ c ∈ cs, c.1 ≠ q₀ ∧ c.1 ≠ q₁ := by
    intro c hc
    refine ⟨fun h => hcsR c hc ?_, fun h => hcsR c hc ?_⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hpq : p ≠ q₀ ∧ p ≠ q₁ := ⟨fun h => hpQ (by simp [Q, h]), fun h => hpQ (by simp [Q, h])⟩
  have hRiR : ∀ l : List P, (∀ r ∈ l, r ∈ R) → ∀ r ∈ l, r ∈ RI :=
    fun l hl r hr => hRsub (hl r hr)
  have hQRi : ∀ l : List P, (∀ r ∈ l, r ∈ Q) → ∀ r ∈ l, r ∈ RI :=
    fun l hl r hr => Q_sub_RS i (hl r hr)
  have happ : ∀ l₁ l₂ : List P, (∀ r ∈ l₁, r ∈ RI) → (∀ r ∈ l₂, r ∈ RI) →
      ∀ r ∈ l₁ ++ l₂, r ∈ RI := by
    intro l₁ l₂ h1 h2 r hr
    rcases List.mem_append.1 hr with hr | hr
    exacts [h1 r hr, h2 r hr]
  have hpRi' : ∀ r ∈ [p], r ∈ RI := by simp [hpRi]
  -- the covering processes do not move in `RI`-only executions
  have hlocRI : ∀ (D : Cfg A) (l : List P), (∀ r ∈ l, r ∈ RI) → ∀ c ∈ cs,
      (run D l).loc c.1 = D.loc c.1 := fun D l hl c hc =>
    run_loc_other _ _ (by rintro r hr rfl; exact hcsR c hc (hl _ hr))
  have hplocQ : ∀ (D : Cfg A) (l : List P), (∀ r ∈ l, r ∈ Q) → (run D l).loc p = D.loc p :=
    fun D l hl => run_loc_other _ _ (by rintro r hr rfl; exact hpQ (hl _ hr))
  -- Lemma 13 and Observation 15: a `Q`-only `γ` with `Q` bivalent in `Cγ` and `Cγβ_i`
  obtain ⟨γ, hγ, hbγ⟩ := lemma13 hS hq I.reach I.biv I.cov hcsQ
  rw [run_append] at hbγ
  have hγR := hQRi γ hγ
  set E := run C γ with hEdef
  have hcovE : Covering E cs := I.cov.run (fun r hr => hbR r (hγR r hr))
  have hnochg : ∀ c ∈ cs, (run E (block cs)).mem c.2 = E.mem c.2 := by
    by_contra h
    push Not at h
    exact I.blk γ hγR h hbγ
  have hbE : Biv Q E := (obs15 hcovE hQb hnochg).2 hbγ
  have hE : Reach C₀ E := I.reach.run γ
  -- Lemma 14 with `C = C' = Cγ`
  obtain ⟨j, ha, B, o, k, hpa, hbc⟩ := lemma14 hS hQR hpR hE hE hbE rfl
  set F := run E (solo p j) with hFdef
  set v := F.mem B with hvdef
  obtain ⟨αj, hαj, hbj, hindj⟩ := ha j le_rfl
  have hαjR : ∀ r ∈ αj, r ∈ RI := by rw [hRi]; exact hαj
  set C' := run E αj with hC'def
  have hpC' : A.act (C'.loc p) = .access B o k := by rw [hindj.2]; exact hpa
  have hcovC' : Covering C' cs := hcovE.run (fun r hr => hbR r (hαjR r hr))
  have hC' : Reach C₀ C' := hE.run αj
  have hC'C : C' = run C (γ ++ αj) := by rw [run_append]
  have hγαR := happ γ αj hγR hαjR
  have hlocC'E : ∀ c ∈ cs, C'.loc c.1 = E.loc c.1 := hlocRI E αj hαjR
  -- `p` swapped `v` into `B` during `αj` if `B` had another value before
  have hswap : E.mem B ≠ v → ∃ a₁ a₂ k', αj = a₁ ++ p :: a₂ ∧
      A.act ((run E a₁).loc p) = .access B (RSOp.swap v) k' := by
    intro hne
    obtain ⟨t, ht, k', hk'⟩ := exists_swap_solo E p B j (Ne.symm hne)
    obtain ⟨a₁, a₂, hα, hl⟩ := hindj.step_of_solo ht
    exact ⟨a₁, a₂, k', hα, by rw [hl]; exact hk'⟩
  -- Claim 17
  have claim17 : ∀ c ∈ cs, c.2 = B → (run E (block cs)).mem B = v := by
    intro c hc hcB
    by_contra hne
    have hEB : E.mem B ≠ v := by
      have := hnochg c hc
      rw [hcB] at this
      rw [← this]; exact hne
    obtain ⟨t, ht, k', hk'⟩ := exists_swap_solo E p B j (Ne.symm hEB)
    obtain ⟨αt, hαt, hbt, hindt⟩ := ha t (by omega)
    have hαtR : ∀ r ∈ αt, r ∈ RI := by rw [hRi]; exact hαt
    have hpt : A.act ((run E αt).loc p) = .access B (RSOp.swap v) k' := by
      rw [hindt.2]; exact hk'
    obtain ⟨γ', hγ', hbγ'⟩ := lemma13 hS hq (hE.run αt) hbt
      (hcovE.run (fun r hr => hbR r (hαtR r hr))) hcsQ
    rw [run_append] at hbγ'
    set G := run (run E αt) γ' with hGdef
    have hpG : A.act (G.loc p) = .access B (RSOp.swap v) k' := by
      rw [hGdef, hplocQ _ _ hγ']; exact hpt
    have hcovG : Covering G cs :=
      (hcovE.run (fun r hr => hbR r (hαtR r hr))).run (fun r hr => hQb r (hγ' r hr))
    have hbiv1 : Biv Q (run (G.step p) (block cs)) :=
      (biv_step_block_iff hcovG hQb hpb hpQ ⟨_, _, hpG⟩ ⟨c, hc, hcB⟩).2 hbγ'
    have hlam : ∀ r ∈ γ ++ αt ++ γ' ++ [p], r ∈ RI :=
      happ _ _ (happ _ _ (happ _ _ hγR hαtR) (hQRi γ' hγ')) hpRi'
    have hrun : run C (γ ++ αt ++ γ' ++ [p]) = G.step p := by
      rw [run_concat, run_append, run_append]
    have hcovGp : Covering (G.step p) cs := hcovG.of_loc (fun c hc =>
      G.step_loc_other (fun h => hpb (h ▸ List.mem_map_of_mem hc)))
    have e1 : (run (G.step p) (block cs)).mem B = (run E (block cs)).mem B := by
      have := block_mem_covered hcovGp hcovE I.objs_nd (fun c' hc' => by
        have hne' : c'.1 ≠ p := fun h => hpb (h ▸ List.mem_map_of_mem hc')
        rw [G.step_loc_other hne', hGdef,
          hlocRI _ _ (hQRi γ' hγ') c' hc', hlocRI _ _ hαtR c' hc']) c hc
      rwa [hcB] at this
    have e2 : (G.step p).mem B = v := by rw [step_swap_mem_self hpG]
    apply I.blk _ hlam ⟨c, hc, ?_⟩ (by rw [hrun]; exact hbiv1)
    rw [hrun, hcB, e1, e2]
    exact hne
  have hXchg : ∀ lam : List P, (∀ r ∈ lam, r ∈ R) → ∀ x ∈ X, Changes C' lam x →
      ¬ Biv Q (run C' lam) := by
    intro lam hlam x hx hch
    have := I.chg (γ ++ αj ++ lam) (happ _ _ hγαR (hRiR lam hlam)) x hx
      (by rw [hC'C] at hch; exact hch.of_suffix)
    rwa [run_append, ← hC'C] at this
  have hprocs : ∀ c ∈ cs, c.1 ∈ ps.take (i + 1) := fun c hc => take_sub_take_succ (I.procs c hc)
  -- after a `Q`-only `γ''` from `C'` with `Q` bivalent after `γ''β_i`: `β_i` changes nothing
  have hQonly : ∀ γ'' : List P, (∀ r ∈ γ'', r ∈ Q) →
      Biv Q (run (run C' γ'') (block cs)) →
      (∀ c ∈ cs, (run (run C' γ'') (block cs)).mem c.2 = (run C' γ'').mem c.2) := by
    intro γ'' hγ'' hb
    by_contra h
    push Not at h
    have := I.blk (γ ++ αj ++ γ'') (happ _ _ hγαR (hQRi γ'' hγ''))
      (by rw [run_append, ← hC'C]; exact h)
    rw [run_append, ← hC'C] at this
    exact this hb
  have hcovE' : ∀ γ'' : List P, (∀ r ∈ γ'', r ∈ Q) → ∀ c ∈ cs,
      (run C' γ'').loc c.1 = E.loc c.1 := fun γ'' hγ'' c hc => by
    rw [hlocRI _ _ (hQRi γ'' hγ'') c hc, hlocC'E c hc]
  by_cases hd : ((rswapObj Bool false).δ v o).1 = v
  · -- Case 1: `d` does not change `B`
    have hC'B : C'.mem B = !v := by
      apply bool_eq_not_of_ne
      intro h
      exact (hbc αj hαj hbj hindj [] (by simp)).2 hd ⟨[], [], rfl, by simpa using h⟩
        (by simpa using hbj)
    have hBX : B ∉ X := by
      intro hBX
      apply I.chg (γ ++ αj) hγαR B hBX ?_ (by rw [← hC'C]; exact hbj)
      by_cases h1 : C'.mem B = C.mem B
      · by_cases h2 : E.mem B = C.mem B
        · obtain ⟨a₁, a₂, k', hα, hk'⟩ := hswap (by rw [h2, ← h1, hC'B]; simp)
          refine ⟨γ ++ (a₁ ++ [p]), a₂, by rw [hα]; simp, ?_⟩
          rw [run_append, ← hEdef, run_concat, step_swap_mem_self hk', ← h1, hC'B]
          simp
        · exact ⟨γ, αj, rfl, h2⟩
      · exact changes_of_ne (by rw [← hC'C]; exact h1)
    have hBY : ∀ c ∈ cs, c.2 ≠ B := by
      intro c hc hcB
      have h17 := claim17 c hc hcB
      obtain ⟨γ'', hγ'', hbγ''⟩ := lemma13 hS hq hC' hbj hcovC' hcsQ
      rw [run_append] at hbγ''
      have hcovH : Covering (run C' γ'') cs := hcovC'.run (fun r hr => hQb r (hγ'' r hr))
      have hnoH := hQonly γ'' hγ'' hbγ''
      have hbH : Biv Q (run C' γ'') := (obs15 hcovH hQb hnoH).2 hbγ''
      have hHB : (run C' γ'').mem B = v := by
        have e := block_mem_covered hcovH hcovE I.objs_nd (hcovE' γ'' hγ'') c hc
        rw [hnoH c hc, hcB, h17] at e
        exact e
      exact (hbc αj hαj hbj hindj γ'' (fun r hr => hQR (hγ'' r hr))).2 hd
        ⟨γ'', [], by simp, hHB⟩ hbH
    refine ⟨C', insert B X, cs, ⟨hC', hbj, hcovC', I.objs_nd, ?_, ?_, hprocs, ?_, ?_⟩⟩
    · intro c hc h
      rcases Finset.mem_insert.1 h with h | h
      · exact hBY c hc h
      · exact I.disj c hc h
    · rw [Finset.card_insert_of_notMem hBX]; have := I.card; omega
    · intro lam hlam x hx hch
      rcases Finset.mem_insert.1 hx with rfl | hx
      · obtain ⟨l₁, l₂, rfl, hne⟩ := hch
        have hv : (run C' l₁).mem x = v := by
          rw [hC'B] at hne
          revert hne
          cases (run C' l₁).mem x <;> cases v <;> simp
        exact (hbc αj hαj hbj hindj (l₁ ++ l₂) hlam).2 hd ⟨l₁, l₂, rfl, hv⟩
      · exact hXchg lam hlam x hx hch
    · intro lam hlam h
      have := I.blk (γ ++ αj ++ lam) (happ _ _ hγαR (hRiR lam hlam))
        (by rw [run_append, ← hC'C]; exact h)
      rwa [run_append, ← hC'C] at this
  · -- Case 2: `d = Swap(B, !v)` changes `B`
    obtain ⟨k₂, hpa2⟩ : ∃ k₂, A.act (C'.loc p) = .access B (RSOp.swap (!v)) k₂ := by
      cases o with
      | read => exact absurd rfl hd
      | swap w =>
        have : w = !v := bool_eq_not_of_ne hd
        exact ⟨k, by rw [hpC', this]⟩
    have hBX : B ∉ X := by
      intro hBX
      obtain ⟨γi, hγi, hbγi⟩ := lemma13 hS hq hC' hbj (cs := [(p, B)])
        ⟨by simp, by simpa using covers_of_swap hpa2⟩ (by simpa using hpq)
      have hlam : ∀ r ∈ γ ++ αj ++ γi ++ [p], r ∈ RI :=
        happ _ _ (happ _ _ hγαR (hQRi γi hγi)) hpRi'
      have hpγi : A.act ((run C' γi).loc p) = .access B (RSOp.swap (!v)) k₂ := by
        rw [hplocQ _ _ hγi]; exact hpa2
      have hrun : run C (γ ++ αj ++ γi ++ [p]) = (run C' γi).step p := by
        rw [run_concat, run_append, ← hC'C]
      have hbγi' : Biv Q ((run C' γi).step p) := by
        simpa [run_append, block] using hbγi
      have hnc : ¬ Changes C (γ ++ αj ++ γi ++ [p]) B := fun h =>
        I.chg _ hlam B hBX h (by rw [hrun]; exact hbγi')
      have hCB : C.mem B = !v := by
        by_contra h
        apply hnc
        refine changes_of_ne ?_
        rw [hrun, step_swap_mem_self hpγi]
        exact Ne.symm h
      have hEB : E.mem B = !v := by
        by_contra h
        exact hnc ⟨γ, αj ++ γi ++ [p], by simp, by rw [hCB]; exact h⟩
      obtain ⟨a₁, a₂, k', hα, hk'⟩ := hswap (by rw [hEB]; simp)
      apply hnc
      refine ⟨γ ++ (a₁ ++ [p]), a₂ ++ γi ++ [p], by rw [hα]; simp, ?_⟩
      rw [run_append, ← hEdef, run_concat, step_swap_mem_self hk', hCB]
      simp
    have hBY : ∀ c ∈ cs, c.2 ≠ B := by
      intro c hc hcB
      have h17 := claim17 c hc hcB
      obtain ⟨γ'', hγ'', hbγ''⟩ := lemma13 hS hq hC' hbj hcovC' hcsQ
      rw [run_append] at hbγ''
      set H := run C' γ'' with hHdef
      have hcovH : Covering H cs := hcovC'.run (fun r hr => hQb r (hγ'' r hr))
      have hpH : A.act (H.loc p) = .access B (RSOp.swap (!v)) k₂ := by
        rw [hHdef, hplocQ _ _ hγ'']; exact hpa2
      have hbiv1 : Biv Q (run (H.step p) (block cs)) :=
        (biv_step_block_iff hcovH hQb hpb hpQ ⟨_, _, hpH⟩ ⟨c, hc, hcB⟩).2 hbγ''
      have hlam : ∀ r ∈ γ ++ αj ++ γ'' ++ [p], r ∈ RI :=
        happ _ _ (happ _ _ hγαR (hQRi γ'' hγ'')) hpRi'
      have hrun : run C (γ ++ αj ++ γ'' ++ [p]) = H.step p := by
        rw [run_concat, run_append, ← hC'C]
      have hcovHp : Covering (H.step p) cs := hcovH.of_loc (fun c hc =>
        H.step_loc_other (fun h => hpb (h ▸ List.mem_map_of_mem hc)))
      have e1 : (run (H.step p) (block cs)).mem B = (run E (block cs)).mem B := by
        have := block_mem_covered hcovHp hcovE I.objs_nd (fun c' hc' => by
          have hne' : c'.1 ≠ p := fun h => hpb (h ▸ List.mem_map_of_mem hc')
          rw [H.step_loc_other hne',
            hHdef, hcovE' γ'' hγ'' c' hc']) c hc
        rwa [hcB] at this
      have e2 : (H.step p).mem B = !v := by rw [step_swap_mem_self hpH]
      apply I.blk _ hlam ⟨c, hc, ?_⟩ (by rw [hrun]; exact hbiv1)
      rw [hrun, hcB, e1, e2, h17]
      simp
    refine ⟨C', X, (p, B) :: cs, ⟨hC', hbj, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, hXchg, ?_⟩⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨hpb, I.cov.1⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact covers_of_swap hpa2
      · exact hcovC'.2 c hc
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun h => by
        obtain ⟨c, hc, hcB⟩ := List.mem_map.1 h
        exact hBY c hc hcB, I.objs_nd⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hBX
      · exact I.disj c hc
    · simp only [List.length_cons]; have := I.card; omega
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact getElem_mem_take_succ hi
      · exact hprocs c hc
    · intro lam hlam h
      set G := run C' lam with hGdef
      have hblkeq : block ((p, B) :: cs) = p :: block cs := rfl
      rw [hblkeq, run_cons] at h ⊢
      have hpG : A.act (G.loc p) = .access B (RSOp.swap (!v)) k₂ := by
        rw [hGdef, run_loc_other _ _ (by rintro r hr rfl; exact hpR (hlam _ hr))]; exact hpa2
      have hlamRI := hRiR lam hlam
      have hcovG : Covering G cs := hcovC'.run (fun r hr => hbR r (hlamRI r hr))
      have hcovGp : Covering (G.step p) cs := hcovG.of_loc (fun c hc =>
        G.step_loc_other (fun h => hpb (h ▸ List.mem_map_of_mem hc)))
      have hrunp : run C (γ ++ αj ++ lam ++ [p]) = G.step p := by
        rw [run_concat, run_append, ← hC'C]
      by_cases hA : ∃ c ∈ cs, (run (G.step p) (block cs)).mem c.2 ≠ (G.step p).mem c.2
      · have := I.blk (γ ++ αj ++ lam ++ [p]) (happ _ _ (happ _ _ hγαR hlamRI) hpRi')
          (by rw [hrunp]; exact hA)
        rwa [hrunp] at this
      · push Not at hA
        have hmeq := block_mem_eq_self hcovGp hA
        obtain ⟨c, hc, hne⟩ := h
        have hGB : G.mem B = v := by
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · rw [hmeq, step_swap_mem_self hpG] at hne
            revert hne
            cases G.mem B <;> cases v <;> simp
          · exfalso
            apply hne
            rw [hmeq, G.step_mem_other ⟨_, _, hpG⟩ (hBY c hc)]
        have hnb := (hbc αj hαj hbj hindj lam hlam).1 hGB
        rw [run_append, run_singleton, ← hC'def] at hnb
        rwa [← obs15 hcovGp hQb hA]


/-- **Lemma 16** of [Ovens 2022]: for every `i ≤ n − 2` there are a configuration `C_i`, disjoint
sets of objects `X_i`, `Y_i` with `|X_i ∪ Y_i| = i` and covering processes `S_i` with
properties (a)–(d). -/
theorem lemma16 (hb : Biv {q₀, q₁} C₀) :
    ∀ i ≤ ps.length, ∃ C X cs, Inv16 C₀ q₀ q₁ ps i C X cs := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨C₀, ∅, [], lemma16_zero hS hq hnd hb⟩
  | succ i ih =>
    intro hi
    obtain ⟨C, X, cs, I⟩ := ih (by omega)
    exact lemma16_step hS hq hnd (by omega) I

/-- The objects of `X` and of `cs` are distinct, so there are at least `i` objects. -/
lemma Inv16.card_le [Fintype ι] {C : Cfg A} {X : Finset ι} {cs : List (P × ι)} {i : ℕ}
    (I : Inv16 C₀ q₀ q₁ ps i C X cs) : i ≤ Fintype.card ι := by
  classical
  have hdisj : Disjoint X (cs.map Prod.snd).toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx')
    exact I.disj c hc hx
  have h1 := Finset.card_union_of_disjoint hdisj
  rw [List.toFinset_card_of_nodup I.objs_nd, List.length_map] at h1
  rw [← I.card, ← h1]
  exact Finset.card_le_univ _

end Lemma16

/-- **Theorem 18** of [Ovens 2022]: every obstruction-free binary consensus algorithm for `n`
processes from readable binary swap objects uses at least `n − 2` objects. -/
theorem theorem18 [Fintype P] [Fintype ι] (hA : SolvesSetAgreement A 1 Set.univ)
    (hof : ObstructionFree A Set.univ) : Fintype.card P - 2 ≤ Fintype.card ι := by
  classical
  by_cases hn : Fintype.card P < 2
  · omega
  push Not at hn
  obtain ⟨q₀, q₁, hq⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card P)
  set ps := ((Finset.univ.erase q₀).erase q₁).toList
  have hlen : ps.length = Fintype.card P - 2 := by
    simp only [ps, Finset.length_toList]
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hq]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ]
    omega
  have hnd : (q₀ :: q₁ :: ps).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, ps, Finset.mem_toList, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.nodup_toList _⟩
    · rintro (h | ⟨-, h, -⟩)
      · exact hq h
      · exact h rfl
    · rintro ⟨h, -⟩; exact h rfl
  let x : P → Bool := fun p => decide (p = q₁)
  have hx0 : x q₀ = false := by simp [x, hq]
  have hx1 : x q₁ = true := by simp [x]
  have hS := setting_of hA hof (x := x) (fun _ => trivial)
  have hb := obs12 hA.validity_univ hof hx0 hx1
  obtain ⟨C, X, cs, I⟩ := lemma16 hS hq hnd hb ps.length le_rfl
  have h2 : ps.length ≤ Fintype.card ι := I.card_le hS hq hnd
  omega

end ConsensusFromSwap
