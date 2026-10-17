import Papers.PODC2021.ScannableBinaryObjects.Lemma5

/-!
# Lemma 5 of Ovens (PODC 2021): the inductive step and the lemma

`lemma5` : for a stage with `|A| ≥ j + 1` active processes and `j ≤ 2^(k'-1)` there are `α_j`,
`B_j` (`|B_j| = j`) with properties (a)–(c) of Lemma 5.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]
  {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type} {I : Impl (scannable O) B P L} {p₀ : P}

lemma curVal_append (ε β : List (Label P (scannable O))) :
    curVal p₀ (ε ++ β) = (scannable O).runOps (curVal p₀ ε) (opsOf β p₀) := by
  have := valAt_append_add (p₀ := p₀) ε β (opsOf β p₀).length
  rw [List.take_length] at this
  rw [← this]; simp [curVal]

lemma lim_solo_scanner {A : Finset P} {k' : ℕ} {β : List (Label P (scannable O))} {s : P}
    (hβ : ∀ ℓ ∈ β, ℓ.proc = s) (hsc : ∀ o ∈ opsOf β s, o = .scan) (hs : s ∈ A) (hs0 : s ≠ p₀) :
    Lim p₀ A k' β := by
  intro ℓ hℓ
  refine ⟨by rw [hβ ℓ hℓ]; exact hs, ?_⟩
  cases ℓ with
  | inv p o =>
    have hp : p = s := hβ _ hℓ
    subst hp
    have := hsc o (mem_opsOf_of_inv_mem hℓ)
    subst this
    exact ⟨hs0, fun i o' he => by cases he⟩
  | _ => trivial

lemma opsOf_eq_nil_of_solo {β : List (Label P (scannable O))} {s : P} (hβ : ∀ ℓ ∈ β, ℓ.proc = s)
    {p : P} (hp : p ≠ s) : opsOf β p = [] :=
  opsOf_eq_nil_of_proc_ne (fun ℓ hℓ he => hp (by rw [← he]; exact hβ ℓ hℓ))

variable (hnm : ∀ c, (O c).NonMonotonic) (hof : I.ObstructionFree)
  (hall : ∀ p o, SingleUpdater p₀ p o → I.allowed p o) (hlin : I.Linearizable)
  (hbit : ∀ i, OneBit (B i).State)

include hnm hof hall in
/-- **The execution `μ`.** If the top live component is `1`, `p₀` resets it to `0`. -/
lemma reset_top {E : List (Label P (scannable O))} {G : Config (scannable O) B P L}
    (hG : I.run E = some G) (hp₀ : G.pend p₀ = none) {k' : ℕ} {top : Fin k}
    (htop : top.val + 1 = k') {V : Set (Fin k → Bool)} (hV : ∀ v ∈ V, v top = true)
    (hcur : curVal p₀ E ∉ V) :
    ∃ μ G', I.runFrom G μ = some G' ∧ G'.pend p₀ = none ∧ (∀ ℓ ∈ μ, ℓ.proc = p₀) ∧
      Lim p₀ {p₀} k' μ ∧ Absent p₀ V E μ ∧ curVal p₀ (E ++ μ) top = false ∧
      ∀ c, c ≠ top → curVal p₀ (E ++ μ) c = curVal p₀ E c := by
  by_cases h : curVal p₀ E top = true
  · set op : ScanOp O := .update top (flipOp hnm top true)
    obtain ⟨G', h1, h2, h3, h4, -⟩ := I.soloOp_spec hof p₀ op (hall _ _ rfl) hG hp₀
    have hval : curVal p₀ (E ++ I.soloOp p₀ op G) =
        Function.update (curVal p₀ E) top false := by
      rw [curVal_append, h4]
      change Function.update (curVal p₀ E) top ((O top).δ (curVal p₀ E top) (flipOp hnm top true)).1 = _
      rw [h, flipOp_spec]; rfl
    refine ⟨_, G', h1, h2, h3, ?_, ?_, ?_, ?_⟩
    · intro ℓ hℓ
      refine ⟨by simp [h3 ℓ hℓ], ?_⟩
      cases ℓ with
      | inv p o =>
        have hp : p = p₀ := h3 _ hℓ
        subst hp
        have := mem_opsOf_of_inv_mem hℓ
        rw [h4, List.mem_singleton] at this
        subst this
        exact ⟨rfl, fun i o' he => by
          simp only [op, ScanOp.update.injEq] at he; obtain ⟨rfl, -⟩ := he; omega⟩
      | _ => trivial
    · intro i h1' h2' hm
      rw [opsOf_append, h4] at h2'
      simp only [List.length_append, List.length_singleton] at h2'
      rcases (show i = (opsOf E p₀).length ∨ i = (opsOf E p₀).length + 1 by omega) with rfl | rfl
      · rw [valAt_append_of_le le_rfl] at hm; exact hcur hm
      · have : valAt p₀ (E ++ I.soloOp p₀ op G) ((opsOf E p₀).length + 1) =
            curVal p₀ (E ++ I.soloOp p₀ op G) := by
          simp [curVal, h4]
        rw [this, hval] at hm
        have := hV _ hm; simp at this
    · rw [hval]; simp
    · intro c hc; rw [hval, Function.update_of_ne hc]
  · refine ⟨[], G, rfl, hp₀, by simp, by simp [Lim], absent_nil_iff.2 hcur, ?_, fun _ _ => by simp⟩
    simpa using h

/-- Lemma 5 for `j = 0`. -/
lemma lemma5_zero {ε X A F k'} (hS : Stage I p₀ ε X A F k') :
    L5Res I p₀ ε X A F k' 0 [] X A ∅ :=
  { run := rfl
    lim := by simp [Lim]
    sub := subset_refl _
    p0 := hS.p0A
    card := by simp
    disj := by simp
    bcard := by simp
    idle := hS.idle
    high := by simpa using hS.high
    fixed := by simp }

include hnm hof hall hlin hbit in
/-- **Lemma 5, inductive step** (`j → j + 1`, for `j + 2 ≤ |A|` and `j + 1 ≤ 2^(k'-1)`). -/
theorem lemma5_step {ε X A F k'} (hS : Stage I p₀ ε X A F k') {j : ℕ} (hj1 : j + 2 ≤ A.card)
    (hj2 : j + 1 ≤ 2 ^ (k' - 1)) {α Xj Aj Bj} (hR : L5Res I p₀ ε X A F k' j α Xj Aj Bj) :
    ∃ α' Xj' Aj' Bj', L5Res I p₀ ε X A F k' (j + 1) α' Xj' Aj' Bj' := by
  classical
  set E := ε ++ α with hEdef
  have hE : I.run E = some Xj := (I.run_append_of_eq hS.run _).trans hR.run
  have hsuE : SUExec p₀ E := suExec_append.2 ⟨hS.su, hR.lim.su⟩
  -- a scanner `s` (paper: `p_{n-j-1}`)
  obtain ⟨s, hsA, hs0⟩ : ∃ s ∈ Aj, s ≠ p₀ := by
    have : 1 < Aj.card := by have := hR.card; omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 this
    by_cases ha0 : a = p₀
    · exact ⟨b, hb, fun e => hab (ha0.trans e.symm)⟩
    · exact ⟨a, ha, ha0⟩
  set A' := Aj.erase s with hA'
  have hA'sub : A' ⊆ Aj := Finset.erase_subset _ _
  have hp0A' : p₀ ∈ A' := Finset.mem_erase.2 ⟨Ne.symm hs0, hR.p0⟩
  have hk1 := hS.k'pos
  have hk2 := hS.k'le
  set top : Fin k := ⟨k' - 1, by omega⟩ with htopdef
  have htop : top.val + 1 = k' := by simp [top]; omega
  set V := (Vset k' j : Set (Fin k → Bool)) with hV
  set V' := (Vset k' (j + 1) : Set (Fin k → Bool)) with hV'
  have hVV' : V ⊆ V' := Vset_mono (by omega)
  have hV'top : ∀ v ∈ V', v top = true := fun v hv => Vset_top htop hv
  have hEtop : curVal p₀ E top = false := hR.high top (by omega)
  -- `λ`: `p₀` changes the value to `V_{j+1} = vec k' j`
  obtain ⟨lam, Y, hl1, hl2, hl3, hl4, hl5, hl6⟩ := goTo_exec hnm hof hall htop hE
    (hR.idle _ hR.p0) (vec k' j) (fun c hc => by rw [hR.high c (by omega), vec_high hc])
  have hY : I.run (E ++ lam) = some Y := (I.run_append_of_eq hE _).trans hl1
  have hsY := I.runFrom_other hl1 (q := s) (fun ℓ hℓ he => hs0 (by rw [← he]; exact hl3 ℓ hℓ))
  have hlamLim : Lim p₀ Aj k' lam := hl4.mono (by simp [hR.p0]) le_rfl
  have hlamV : Absent p₀ V E lam := by
    intro i h1 h2 hm
    obtain ⟨t, rfl⟩ : ∃ t, i = (opsOf E p₀).length + t := ⟨i - (opsOf E p₀).length, by omega⟩
    by_cases ht : t < (opsOf lam p₀).length
    · have h6 := hl6 t ht
      rw [hEtop] at h6
      have := Vset_top htop hm
      rw [h6] at this; exact Bool.false_ne_true this
    · have heq : (opsOf E p₀).length + t = (opsOf (E ++ lam) p₀).length := by
        simp only [opsOf_append, List.length_append] at h2 ⊢; omega
      rw [heq] at hm
      change curVal p₀ (E ++ lam) ∈ V at hm
      rw [hl5] at hm
      exact vec_not_mem_Vset hk2 (by omega) hm
  -- `δ`: `s` performs a solo scan; it returns `V_{j+1}`
  obtain ⟨Z, hd1, hd2, hd3, hd4, hd5⟩ := solo_scan hof hall hlin hY
    (suExec_append.2 ⟨hsuE, hlamLim.su⟩) hl2 hs0 (by rw [hsY.2]; exact hR.idle s hsA)
  set δ := I.soloOp s .scan Y with hδdef
  rw [hl5] at hd5
  have hδLim : Lim p₀ Aj k' δ := lim_solo_scanner hd3
    (fun o ho => by rw [hd4] at ho; simpa using ho) hsA hs0
  have hδ0 : opsOf δ p₀ = [] := opsOf_eq_nil_of_solo hd3 (Ne.symm hs0)
  by_cases H1 : ∀ β G, Lim p₀ Aj k' β → Absent p₀ V' E β → I.runFrom Xj β = some G →
      ∀ b, b ∉ F → b ∉ Bj → ∃ β' G', Lim p₀ A' k' β' ∧ Absent p₀ V' E (β ++ β') ∧
        I.runFrom G β' = some G' ∧ G'.mem b ≠ G.mem b
  · -- (1) leads to a contradiction: construct `γ`, indistinguishable from `δ` to `s`
    exfalso
    obtain ⟨γ, G, ⟨hγL, hγA⟩, hγ, hfilt, -, -⟩ := replay (I := I) s
      (fun γ => Lim p₀ Aj k' γ ∧ Absent p₀ V' E γ) (X := Xj) (Y := Y) hsY.1.symm hsY.2.symm
      ⟨by simp [Lim], absent_nil_iff.2 (fun hm => by
        have := hV'top _ hm; rw [hEtop] at this; exact Bool.false_ne_true this)⟩ δ hd3
      (fun γ ℓ hℓ hg => ⟨lim_append.2 ⟨hg.1, fun ℓ' hℓ' => hδLim ℓ' (by
          simp only [List.mem_singleton] at hℓ'; subst hℓ'; exact hℓ)⟩,
        (absent_append_noP0 (opsOf_eq_nil_of_solo (s := s)
          (fun ℓ' hℓ' => by simp only [List.mem_singleton] at hℓ'; subst hℓ'; exact hd3 _ hℓ)
          (Ne.symm hs0))).2 hg.2⟩)
      (by
        intro γ G δ₀ H b hg hG hpre hH hne
        obtain ⟨δ₁, hδ₁⟩ := hpre
        have hmem : ∀ ℓ ∈ δ₀, ℓ ∈ δ := fun ℓ hℓ => by rw [← hδ₁]; simp [hℓ]
        have hδ₀L : Lim p₀ Aj k' δ₀ := fun ℓ hℓ => hδLim ℓ (hmem ℓ hℓ)
        have hδ₀0 : opsOf δ₀ p₀ = [] := opsOf_eq_nil_of_solo
          (fun ℓ hℓ => hd3 ℓ (hmem ℓ hℓ)) (Ne.symm hs0)
        have hbF : b ∉ F := by
          intro hb
          have e1 := hS.frozen (α ++ γ) G (lim_append.2 ⟨hR.lim, hg.1.mono hR.sub le_rfl⟩)
            (by rw [I.runFrom_append_of_eq hR.run, hG]) b hb
          have e2 := hS.frozen (α ++ (lam ++ δ₀)) H
            (lim_append.2 ⟨hR.lim, (lim_append.2 ⟨hlamLim, hδ₀L⟩).mono hR.sub le_rfl⟩)
            (by rw [I.runFrom_append_of_eq hR.run, I.runFrom_append_of_eq hl1, hH]) b hb
          exact hne (e1.trans e2.symm)
        have hbB : b ∉ Bj := by
          intro hb
          have e1 := hR.fixed γ G hg.1 (hg.2.mono hVV') hG b hb
          have e2 := hR.fixed (lam ++ δ₀) H (lim_append.2 ⟨hlamLim, hδ₀L⟩)
            ((absent_append_noP0 hδ₀0).2 hlamV)
            (by rw [I.runFrom_append_of_eq hl1, hH]) b hb
          exact hne (e1.trans e2.symm)
        obtain ⟨β', G', h1, h2, h3, h4⟩ := H1 γ G hg.1 hg.2 hG b hbF hbB
        refine ⟨β', G', fun ℓ hℓ he => ?_, ⟨lim_append.2 ⟨hg.1, h1.mono hA'sub le_rfl⟩, h2⟩, h3,
          (hbit b).eq_of_ne (Ne.symm hne) h4⟩
        have := (h1 ℓ hℓ).1
        rw [he] at this
        exact (Finset.notMem_erase s Aj) this)
      hd1
    have hresps : respsOf γ s = [.view (vec k' j)] := by
      rw [← respsOf_filter_proc, hfilt, hd5]
    have hcnt := (Impl.run_idle_counts hE (hR.idle s hsA)).symm
    have hv : I.Valid (E ++ γ) := ⟨G, (I.run_append_of_eq hE _).trans hγ⟩
    have hsu : SUExec p₀ (E ++ γ) := suExec_append.2 ⟨hsuE, hγL.su⟩
    have hrespOf : respOf (E ++ γ) (s, (opsOf E s).length) = some (.view (vec k' j)) := by
      simp [respOf, respsOf_append, hresps, ← hcnt]
    obtain ⟨i, hi1, hi2, hri⟩ := scan_resp hlin hv hsu hs0 (by simp [Invoked]) hrespOf
    rw [(Impl.run_idle_counts hE (hR.idle _ hR.p0)).symm] at hi1
    apply hγA i hi1 hi2
    simp only [ScanResp.view.injEq] at hri
    rw [← hri]; exact vec_mem_Vset_succ k' j
  · -- (1) fails: `σ_{j+1}` and the base object `b`
    push Not at H1
    obtain ⟨σ, G, hσL, hσA, hσ, b, hbF, hbB, hb⟩ := H1
    have hEσ : I.run (E ++ σ) = some G := (I.run_append_of_eq hE _).trans hσ
    -- `τ`: the processes of `A'` complete their operations
    obtain ⟨τ, G2, ht3, ht2, ht1, ht4, -⟩ :=
      I.exists_finish (hof.obstructionFreeOn fun _ => True) (fun _ _ _ _ => trivial) A'.toList hEσ
        trivial
    have hτL : Lim p₀ A' k' τ := lim_of_noInv ht2 (fun ℓ hℓ => by simpa using ht3 ℓ hℓ)
    have hEστ : I.run (E ++ σ ++ τ) = some G2 := (I.run_append_of_eq hEσ _).trans ht1
    have hστA : Absent p₀ V' E (σ ++ τ) := (absent_append_noP0 (ht2 p₀)).2 hσA
    -- `μ`: reset the top live component
    obtain ⟨μ, G3, hm1, hm2, hm3, hm4, hm5, hm6, hm7⟩ := reset_top hnm hof hall hEστ
      (ht4 p₀ (by simpa using hp0A')) htop hV'top
      (by rw [List.append_assoc]; exact hστA.curVal)
    have hμL : Lim p₀ A' k' μ := hm4.mono (by simp [hp0A']) le_rfl
    have hrun3 : I.runFrom Xj (σ ++ τ ++ μ) = some G3 := by
      rw [I.runFrom_append_of_eq (by rw [I.runFrom_append_of_eq hσ, ht1]), hm1]
    have hτμL : Lim p₀ A' k' (τ ++ μ) := lim_append.2 ⟨hτL, hμL⟩
    have hστμA : Absent p₀ V' E (σ ++ τ ++ μ) := absent_append.2 ⟨hστA, by
      rw [← List.append_assoc]; exact hm5⟩
    have hστμL : Lim p₀ Aj k' (σ ++ τ ++ μ) :=
      lim_append.2 ⟨lim_append.2 ⟨hσL, hτL.mono hA'sub le_rfl⟩, hμL.mono hA'sub le_rfl⟩
    refine ⟨α ++ (σ ++ τ ++ μ), G3, A', insert b Bj, ?_⟩
    exact
      { run := by rw [I.runFrom_append_of_eq hR.run, hrun3]
        lim := lim_append.2 ⟨hR.lim, hστμL.mono hR.sub le_rfl⟩
        sub := hA'sub.trans hR.sub
        p0 := hp0A'
        card := by
          have := Finset.card_erase_of_mem hsA
          rw [← hA'] at this
          have := hR.card
          have : 1 ≤ Aj.card := Finset.card_pos.2 ⟨s, hsA⟩
          omega
        disj := Finset.disjoint_insert_left.2 ⟨hbF, hR.disj⟩
        bcard := by rw [Finset.card_insert_of_notMem hbB, hR.bcard]
        idle := by
          intro p hp
          by_cases hp0 : p = p₀
          · subst hp0; exact hm2
          · rw [(I.runFrom_other hm1 (fun ℓ hℓ he => hp0 (by rw [← he]; exact hm3 ℓ hℓ))).2]
            exact ht4 p (by simpa using hp)
        high := by
          intro c hc
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
          by_cases hct : c = top
          · subst hct; exact hm6
          · rw [hm7 c hct]
            have hc' : k' ≤ c.val := by
              have : c.val ≠ top.val := fun e => hct (Fin.ext e)
              omega
            rw [curVal_lim hτL hc', curVal_lim hσL hc']
            exact hR.high c hc
        fixed := by
          intro β G4 hβL hβA hβ i hi
          have hβ' : I.runFrom Xj (σ ++ τ ++ μ ++ β) = some G4 := by
            rw [I.runFrom_append_of_eq hrun3, hβ]
          have hAll : Absent p₀ V' E (σ ++ τ ++ μ ++ β) := absent_append.2 ⟨hστμA, by
            simp only [hEdef, List.append_assoc] at hβA ⊢; exact hβA⟩
          rcases Finset.mem_insert.1 hi with rfl | hi
          · have hrun : I.runFrom G (τ ++ μ ++ β) = some G4 := by
              rw [I.runFrom_append_of_eq (by rw [I.runFrom_append_of_eq ht1, hm1]), hβ]
            have e1 := hb (τ ++ μ ++ β) G4 (lim_append.2 ⟨hτμL, hβL⟩)
              (by simpa [List.append_assoc] using hAll) hrun
            have e2 := hb (τ ++ μ) G3 hτμL (by simpa [List.append_assoc] using hστμA)
              (by rw [I.runFrom_append_of_eq ht1, hm1])
            exact e1.trans e2.symm
          · have e1 := hR.fixed (σ ++ τ ++ μ ++ β) G4
              (lim_append.2 ⟨hστμL, hβL.mono hA'sub le_rfl⟩) (hAll.mono hVV') hβ' i hi
            have e2 := hR.fixed (σ ++ τ ++ μ) G3 hστμL (hστμA.mono hVV') hrun3 i hi
            exact e1.trans e2.symm }

include hnm hof hall hlin hbit in
/-- **Lemma 5** (for stages): for every `j ≤ min(|A| - 1, 2^(k'-1))` there are `α_j` and `B_j`
with properties (a)–(c). -/
theorem lemma5 {ε X A F k'} (hS : Stage I p₀ ε X A F k') :
    ∀ j, j + 1 ≤ A.card → j ≤ 2 ^ (k' - 1) → ∃ α Xj Aj Bj, L5Res I p₀ ε X A F k' j α Xj Aj Bj
  | 0, _, _ => ⟨_, _, _, _, lemma5_zero hS⟩
  | j + 1, h1, h2 => by
    obtain ⟨α, Xj, Aj, Bj, hR⟩ := lemma5 hS j (by omega) (by omega)
    exact lemma5_step hnm hof hall hlin hbit hS (by omega) h2 hR

end Cslib.SharedMemory.Scannable
