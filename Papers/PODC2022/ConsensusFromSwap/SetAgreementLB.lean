import Papers.PODC2022.ConsensusFromSwap.Model

/-!
# Lower bound for k-set agreement from swap objects (Section 4)

Lemma 9 and Theorem 10 of Ovens (PODC 2022): every obstruction-free `n`-process `(k+1)`-valued
`k`-set agreement algorithm from swap objects uses at least `⌈n/k⌉ − 1` objects
(`theorem10`, stated as `n ≤ k · (#objects + 1)`; `theorem10_ceil` in the paper's form).

The proofs hold for any objects all of whose operations are *nontrivial historyless* operations
(`OnlyOverwrites`: the new value does not depend on the old one), in particular swap objects.
-/

namespace ConsensusFromSwap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {P V : Type} [DecidableEq P]
  {A : Alg T P V}

/-- The values decided by processes in `R`. -/
def Cfg.decBy (C : Cfg A) (R : Set P) : Set V := {v | ∃ p ∈ R, C.Out p v}

lemma Cfg.decBy_univ (C : Cfg A) : C.decBy Set.univ = C.decSet := by
  ext v; simp [Cfg.decBy, Cfg.decSet]

lemma decBy_mono (C : Cfg A) (R : Set P) (α : List P) : C.decBy R ⊆ (run C α).decBy R := by
  rintro v ⟨p, hp, h⟩
  exact ⟨p, hp, h.run α⟩

lemma AgreeOn.decBy_eq {R R' : Set P} {C D : Cfg A} (h : AgreeOn R C D) (hR : R' ⊆ R) :
    C.decBy R' = D.decBy R' := by
  ext v
  simp only [Cfg.decBy, Set.mem_ofPred_eq]
  exact ⟨fun ⟨p, hp, h'⟩ => ⟨p, hp, (h.out_iff (hR hp)).1 h'⟩,
    fun ⟨p, hp, h'⟩ => ⟨p, hp, (h.out_iff (hR hp)).2 h'⟩⟩

/-! ## Transfer of solo runs that only access objects with equal values -/

/-- One step of `q` from configurations that agree on `q`'s state and on the objects of `M`,
when `q` accesses an object of `M` (or has decided). -/
lemma step_agree_partial {q : P} {M : Finset ι} {C D : Cfg A} (hl : C.loc q = D.loc q)
    (hm : ∀ i ∈ M, C.mem i = D.mem i) (hM : ∀ i, D.Poised q i → i ∈ M) :
    (C.step q).loc q = (D.step q).loc q ∧ ∀ i ∈ M, (C.step q).mem i = (D.step q).mem i := by
  rcases D.dec_or_poised q with hd | ⟨i, hi⟩
  · obtain ⟨v, hv⟩ := hd
    have hv' : C.Out q v := by rw [Cfg.Out, hl]; exact hv
    rw [C.step_of_out hv', D.step_of_out hv]
    exact ⟨hl, hm⟩
  · obtain ⟨o, k, h⟩ := hi
    have h' : A.act (C.loc q) = .access i o k := by rw [hl]; exact h
    have hiM := hM i ⟨o, k, h⟩
    rw [C.step_of_access h', D.step_of_access h]
    refine ⟨by simp [hm i hiM], fun j hj => ?_⟩
    by_cases hji : j = i
    · subst hji; simp [hm j hiM]
    · simp [Function.update_of_ne hji, hm j hj]

lemma solo_agree_partial {q : P} {M : Finset ι} {C D : Cfg A} (hl : C.loc q = D.loc q)
    (hm : ∀ i ∈ M, C.mem i = D.mem i) (s : ℕ)
    (hs : ∀ s' < s, ∀ i, (run D (solo q s')).Poised q i → i ∈ M) :
    (run C (solo q s)).loc q = (run D (solo q s)).loc q ∧
      ∀ i ∈ M, (run C (solo q s)).mem i = (run D (solo q s)).mem i := by
  induction s with
  | zero => exact ⟨hl, hm⟩
  | succ s ih =>
    obtain ⟨h1, h2⟩ := ih (fun s' hs' => hs s' (by omega))
    rw [solo_succ, run_concat, run_concat]
    exact step_agree_partial h1 h2 (hs s (by omega))

/-! ## Lemma 9 -/

variable [Fintype ι]

/-- **Lemma 9** of [Ovens 2022], in a general form. Let `C` be a configuration (the paper: `Cα`)
in which the values of the finite set `W` are decided by processes of `R`, and let `Q ⊆ R` be a
set of processes that are in the same state in `C` as in a configuration `D` (the paper: the
initial configuration in which all processes have input `v`; `Q` has input `v` and took no
steps). Suppose
* (`k`-agreement from `C`) in every `Q`-only execution from `C` at most `|W|` values are decided
  by `R`,
* (validity from `D`) in `Q`-only executions from `D`, processes of `Q` can only decide `v`,
  and `v ∉ W`,
* (solo termination from `D`) processes of `Q` decide in solo runs after `Q`-only executions
  from `D`,
* every operation on every object is a nontrivial historyless operation (e.g. swap).

Then there are at least `|Q|` objects. -/
theorem lemma9 (hO : ∀ i, OnlyOverwrites (T i)) {R : Set P} {Q : Finset P} (hQR : ↑Q ⊆ R)
    {v : V} {W : Finset V} {C D : Cfg A} (hloc : ∀ q ∈ Q, C.loc q = D.loc q)
    (hW : ↑W ⊆ C.decBy R) (hvW : v ∉ W)
    (hagr : ∀ β : List P, (∀ r ∈ β, r ∈ Q) → ((run C β).decBy R).encard ≤ W.card)
    (hval : ∀ β : List P, (∀ r ∈ β, r ∈ Q) → ∀ q ∈ Q, ∀ w, (run D β).Out q w → w = v)
    (hof : ∀ β : List P, (∀ r ∈ β, r ∈ Q) → ∀ q ∈ Q, ∃ t, (run (run D β) (solo q t)).Dec q) :
    Q.card ≤ Fintype.card ι := by
  classical
  -- the induction of the paper, over subsets `L ⊆ Q`
  have key : ∀ L : Finset P, L ⊆ Q → ∃ γ δ : List P, (∀ r ∈ γ, r ∈ L) ∧ (∀ r ∈ δ, r ∈ L) ∧
      ∃ M : Finset ι, M.card = L.card ∧ ∀ i ∈ M, (run C γ).mem i = (run D δ).mem i := by
    intro L
    induction L using Finset.induction_on with
    | empty => exact fun _ => ⟨[], [], by simp, by simp, ∅, rfl, by simp⟩
    | @insert q L hqL ih =>
      intro hsub
      have hqQ : q ∈ Q := hsub (Finset.mem_insert_self q L)
      obtain ⟨γ, δ, hγ, hδ, M, hMc, hM⟩ := ih ((Finset.subset_insert q L).trans hsub)
      have hγQ : ∀ r ∈ γ, r ∈ Q := fun r hr => hsub (Finset.mem_insert_of_mem (hγ r hr))
      have hδQ : ∀ r ∈ δ, r ∈ Q := fun r hr => hsub (Finset.mem_insert_of_mem (hδ r hr))
      set C₁ := run C γ
      set D₁ := run D δ
      have hl : C₁.loc q = D₁.loc q := by
        rw [run_loc_other C γ (by rintro r hr rfl; exact hqL (hγ r hr)),
          run_loc_other D δ (by rintro r hr rfl; exact hqL (hδ r hr)), hloc q hqQ]
      obtain ⟨t, ht⟩ := hof δ hδQ q hqQ
      -- does `q` access an object outside `M` within its first `t` solo steps?
      by_cases hex : ∃ s < t, ∃ i, (run D₁ (solo q s)).Poised q i ∧ i ∉ M
      · -- the first such step `s`
        classical
        let s := Nat.find hex
        have hs : s < t ∧ ∃ i, (run D₁ (solo q s)).Poised q i ∧ i ∉ M := Nat.find_spec hex
        have hmin : ∀ s' < s, ∀ i, (run D₁ (solo q s')).Poised q i → i ∈ M := by
          intro s' hs' i hi
          by_contra hiM
          exact Nat.find_min hex hs' ⟨by omega, i, hi, hiM⟩
        obtain ⟨-, B, hB, hBM⟩ := hs
        obtain ⟨hl', hm'⟩ := solo_agree_partial hl hM s hmin
        refine ⟨γ ++ solo q (s + 1), δ ++ solo q (s + 1), ?_, ?_, insert B M, ?_, ?_⟩
        · intro r hr
          rcases List.mem_append.1 hr with hr | hr
          · exact Finset.mem_insert_of_mem (hγ r hr)
          · rw [List.eq_of_mem_replicate hr]; exact Finset.mem_insert_self q L
        · intro r hr
          rcases List.mem_append.1 hr with hr | hr
          · exact Finset.mem_insert_of_mem (hδ r hr)
          · rw [List.eq_of_mem_replicate hr]; exact Finset.mem_insert_self q L
        · rw [Finset.card_insert_of_notMem hBM, Finset.card_insert_of_notMem hqL, hMc]
        · obtain ⟨o, k, hB'⟩ := hB
          have hBC : A.act ((run C₁ (solo q s)).loc q) = .access B o k := by rw [hl']; exact hB'
          intro i hi
          rw [run_append, run_append, solo_succ, run_concat, run_concat,
            Cfg.step_of_access _ hBC, Cfg.step_of_access _ hB']
          by_cases hiB : i = B
          · subst hiB; simp only [Function.update_self]; exact hO i o _ _
          · simp only [Function.update_of_ne hiB]
            exact hm' i ((Finset.mem_insert.1 hi).resolve_left hiB)
      · -- `q` decides in `C₁` after `t` solo steps, deciding `v ∉ W`: too many values
        exfalso
        push Not at hex
        obtain ⟨hl', -⟩ := solo_agree_partial hl hM t (fun s hs i hi => hex s hs i hi)
        obtain ⟨w, hw⟩ := ht
        have hwv : w = v := by
          refine hval (δ ++ solo q t) (fun r hr => ?_) q hqQ w (by rwa [run_append])
          rcases List.mem_append.1 hr with hr | hr
          · exact hδQ r hr
          · rw [List.eq_of_mem_replicate hr]; exact hqQ
        subst hwv
        have hwC : (run C₁ (solo q t)).Out q w := by rw [Cfg.Out, hl']; exact hw
        have hsub' : ↑(insert w W) ⊆ (run C (γ ++ solo q t)).decBy R := by
          intro u hu
          rw [Finset.coe_insert, Set.mem_insert_iff] at hu
          rcases hu with rfl | hu
          · exact ⟨q, hQR hqQ, by rwa [run_append]⟩
          · exact decBy_mono C R _ (hW hu)
        have h1 := Set.encard_le_encard hsub'
        have h2 := hagr (γ ++ solo q t) (fun r hr => by
          rcases List.mem_append.1 hr with hr | hr
          · exact hγQ r hr
          · rw [List.eq_of_mem_replicate hr]; exact hqQ)
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_insert_of_notMem hvW] at h1
        have := h1.trans h2
        norm_cast at this
        omega
  obtain ⟨-, -, -, -, M, hMc, -⟩ := key Q le_rfl
  rw [← hMc]
  exact Finset.card_le_univ M

/-! ## Theorem 10 -/

lemma decBy_subset (C : Cfg A) {R R' : Set P} (h : R ⊆ R') : C.decBy R ⊆ C.decBy R' := by
  rintro v ⟨p, hp, h'⟩
  exact ⟨p, h hp, h'⟩

lemma agreeOn_initCfg {R : Set P} {x x' : P → V} (h : ∀ p ∈ R, x p = x' p) :
    AgreeOn R (initCfg A x) (initCfg A x') :=
  ⟨rfl, fun p hp => by simp [initCfg, h p hp]⟩

/-- A finite subset of size exactly `j + 1` of a set with more than `j` elements. -/
lemma exists_finset_of_lt_encard {s : Set V} {j : ℕ} (h : (j : ℕ∞) < s.encard) :
    ∃ W : Finset V, ↑W ⊆ s ∧ W.card = j + 1 := by
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_encard_eq (s := s) (k := ((j + 1 : ℕ) : ℕ∞))
    (by rw [Nat.cast_add, Nat.cast_one]; exact Order.add_one_le_of_lt h)
  have hfin : t.Finite := Set.finite_of_encard_eq_coe ht
  refine ⟨hfin.toFinset, by simpa using hts, ?_⟩
  have := ht
  rw [hfin.encard_eq_coe_toFinset_card] at this
  exact_mod_cast this

/-- The induction of Theorem 10 (generalized): if every `R`-only execution from an initial
configuration in which the processes of `R` have inputs among `e 0, …, e j` has at most `j`
values decided by `R`, then `|R| ≤ j · (#objects + 1)`. The paper splits `R` into
`⌈n(k−1)/k⌉` and `⌊n/k⌋` processes; we split off `#objects + 1` processes instead, which gives
the same bound and needs no case `k = 1`. -/
theorem theorem10_gen (hO : ∀ i, OnlyOverwrites (T i)) {S : Set V}
    (hval : ∀ x, InputsIn S x → ∀ α p v, (run (initCfg A x) α).Out p v → ∃ q, x q = v)
    (hof : ObstructionFree A S) {k : ℕ} (e : ℕ → V) (he : ∀ i ≤ k, e i ∈ S)
    (hinj : ∀ i ≤ k, ∀ i' ≤ k, e i = e i' → i = i') :
    ∀ j ≤ k, ∀ R : Finset P,
      (∀ x, InputsIn S x → (∀ r ∈ R, ∃ i ≤ j, x r = e i) →
        ∀ β : List P, (∀ r ∈ β, r ∈ R) → ((run (initCfg A x) β).decBy ↑R).encard ≤ j) →
      R.card ≤ j * (Fintype.card ι + 1) := by
  classical
  intro j
  induction j with
  | zero =>
    intro _ R H
    rcases R.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
    · simp
    exfalso
    have hx : InputsIn S (fun _ : P => e 0) := fun _ => he 0 (Nat.zero_le _)
    obtain ⟨t, w, hw⟩ := hof _ hx [] p
    have h1 := H (fun _ => e 0) hx (fun r _ => ⟨0, le_rfl, rfl⟩) (solo p t)
      (fun r hr => by rw [List.eq_of_mem_replicate hr]; exact hp)
    have h2 : w ∈ (run (initCfg A fun _ => e 0) (solo p t)).decBy ↑R := ⟨p, hp, hw⟩
    have := Set.encard_pos.2 ⟨w, h2⟩
    simp at h1
    rw [h1] at h2
    exact h2
  | succ j ih =>
    intro hjk R H
    set c := Fintype.card ι
    by_contra hlt
    push Not at hlt
    obtain ⟨Q, hQR, hQc⟩ := Finset.exists_subset_card_eq (s := R) (n := c + 1)
      (by nlinarith)
    set R' := R \ Q
    have hR'c : R'.card = R.card - (c + 1) := by
      rw [Finset.card_sdiff_of_subset hQR, hQc]
    by_cases HA : ∀ x, InputsIn S x → (∀ r ∈ R', ∃ i ≤ j, x r = e i) →
        ∀ β : List P, (∀ r ∈ β, r ∈ R') → ((run (initCfg A x) β).decBy ↑R').encard ≤ j
    · have := ih (by omega) R' HA
      rw [hR'c] at this
      have : (j + 1) * (c + 1) = j * (c + 1) + (c + 1) := by ring
      omega
    push Not at HA
    obtain ⟨x, hxS, hxR, β, hβ, hdec⟩ := HA
    let x' : P → V := fun p => if p ∈ R' then x p else e 0
    let x'' : P → V := fun p => if p ∈ R' then x p else e (j + 1)
    have hx'S : InputsIn S x' := fun p => by
      simp only [x']; split_ifs
      · exact hxS p
      · exact he 0 (Nat.zero_le _)
    have hx''S : InputsIn S x'' := fun p => by
      simp only [x'']; split_ifs
      · exact hxS p
      · exact he (j + 1) hjk
    have hβR' : ∀ r ∈ β, r ∈ (↑R' : Set P) := fun r hr => hβ r hr
    have hag' : AgreeOn (↑R' : Set P) (run (initCfg A x) β) (run (initCfg A x') β) :=
      (agreeOn_initCfg (fun p hp => by simp [x', show p ∈ R' from hp])).run hβR'
    have hag'' : AgreeOn (↑R' : Set P) (run (initCfg A x) β) (run (initCfg A x'') β) :=
      (agreeOn_initCfg (fun p hp => by simp [x'', show p ∈ R' from hp])).run hβR'
    obtain ⟨W, hW, hWc⟩ := exists_finset_of_lt_encard hdec
    -- `e (j+1)` is not decided by `R'`
    have hvW : e (j + 1) ∉ W := by
      intro hv
      obtain ⟨p, hp, hpo⟩ := hW hv
      rw [hag'.out_iff hp] at hpo
      obtain ⟨q, hq⟩ := hval x' hx'S β p _ hpo
      simp only [x'] at hq
      split_ifs at hq with hqR
      · obtain ⟨i, hi, hxi⟩ := hxR q hqR
        rw [hxi] at hq
        have := hinj i (by omega) (j + 1) hjk hq
        omega
      · have := hinj 0 (Nat.zero_le _) (j + 1) hjk hq
        omega
    have hQ' : ∀ q ∈ Q, q ∉ R' := fun q hq h => (Finset.mem_sdiff.1 h).2 hq
    have := lemma9 (A := A) hO (R := ↑R) (Q := Q) (by exact_mod_cast hQR) (v := e (j + 1))
      (W := W) (C := run (initCfg A x'') β) (D := initCfg A (fun _ => e (j + 1)))
      (fun q hq => by
        rw [run_loc_other _ β (by rintro r hr rfl; exact hQ' r hq (hβ r hr))]
        simp [initCfg, x'', hQ' q hq])
      (fun w hw => by
        have h1 : w ∈ (run (initCfg A x'') β).decBy ↑R' := by
          rw [← hag''.decBy_eq le_rfl]; exact hW hw
        exact decBy_subset _ (fun p hp => (Finset.mem_sdiff.1 (Finset.mem_coe.1 hp)).1) h1)
      hvW
      (fun β' hβ' => by
        rw [← run_append, hWc]
        refine H x'' hx''S (fun r hr => ?_) (β ++ β') (fun r hr => ?_)
        · by_cases hr' : r ∈ R'
          · obtain ⟨i, hi, hxi⟩ := hxR r hr'
            exact ⟨i, by omega, by simp [x'', hr', hxi]⟩
          · exact ⟨j + 1, le_rfl, by simp [x'', hr']⟩
        · rcases List.mem_append.1 hr with hr | hr
          · exact (Finset.mem_sdiff.1 (hβ r hr)).1
          · exact hQR (hβ' r hr))
      (fun β' _ q _ w hw => by
        obtain ⟨q', hq'⟩ := hval _ (fun _ => he (j + 1) hjk) β' q w hw
        exact hq'.symm)
      (fun β' _ q _ => hof _ (fun _ => he (j + 1) hjk) β' q)
    omega

/-- `k + 1` distinct values of `S`, indexed by `0, …, k`. -/
lemma exists_values {S : Set V} {k : ℕ} (hS : ((k + 1 : ℕ) : ℕ∞) ≤ S.encard) :
    ∃ e : ℕ → V, (∀ i ≤ k, e i ∈ S) ∧ ∀ i ≤ k, ∀ i' ≤ k, e i = e i' → i = i' := by
  classical
  obtain ⟨W, hWS, hWc⟩ := exists_finset_of_lt_encard (j := k)
    (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hS)
  let f : Fin (k + 1) ≃ W := (W.equivFinOfCardEq hWc).symm
  refine ⟨fun i => (f ⟨min i k, by omega⟩ : V), fun i _ => hWS (f _).2, ?_⟩
  intro i hi i' hi' h
  have := f.injective (Subtype.ext h)
  simp only [Fin.mk.injEq] at this
  omega

/-- **Theorem 10** of [Ovens 2022] (for obstruction-free algorithms): every obstruction-free
`n`-process `k`-set agreement algorithm (correct for inputs from a set `S` of at least `k + 1`
values) from objects supporting only nontrivial historyless operations (e.g. swap objects) uses
at least `⌈n/k⌉ − 1` objects; stated as `n ≤ k · (#objects + 1)`. No assumption `n > k ≥ 1` is
needed. -/
theorem theorem10 [Fintype P] (hO : ∀ i, OnlyOverwrites (T i)) {k : ℕ}
    {S : Set V} (hS : ((k + 1 : ℕ) : ℕ∞) ≤ S.encard) (hA : SolvesSetAgreement A k S)
    (hof : ObstructionFree A S) :
    Fintype.card P ≤ k * (Fintype.card ι + 1) := by
  obtain ⟨e, he, hinj⟩ := exists_values hS
  have := theorem10_gen hO hA.validity hof e he hinj k le_rfl Finset.univ
    (fun x hx _ β _ => by
      rw [Finset.coe_univ, Cfg.decBy_univ]; exact hA.agreement x hx β)
  simpa using this

/-- **Theorem 10** / Corollary 11 for swap objects, in the paper's form
`#objects ≥ ⌈n/k⌉ − 1` (for `k ≥ 1`). -/
theorem theorem10_swap [Fintype P] {D : ι → Type} {d₀ : (i : ι) → D i}
    {A : Alg (fun i => swapObj (D i) (d₀ i)) P V} {k : ℕ} (hk : 1 ≤ k)
    {S : Set V} (hS : ((k + 1 : ℕ) : ℕ∞) ≤ S.encard) (hA : SolvesSetAgreement A k S)
    (hof : ObstructionFree A S) :
    (Fintype.card P + k - 1) / k - 1 ≤ Fintype.card ι := by
  have h := theorem10 (fun i => onlyOverwrites_swapObj (D i) (d₀ i)) hS hA hof
  have : (Fintype.card P + k - 1) / k ≤ Fintype.card ι + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hk]
    have := mul_comm k (Fintype.card ι + 1)
    omega
  omega

/-- **Corollary of Theorem 10** for consensus (`k = 1`): every obstruction-free `n`-process
consensus algorithm (for at least two input values) from swap objects uses at least `n − 1`
objects. -/
theorem consensus_swap_lowerBound [Fintype P] {D : ι → Type} {d₀ : (i : ι) → D i}
    {A : Alg (fun i => swapObj (D i) (d₀ i)) P V} {S : Set V} (hS : 2 ≤ S.encard)
    (hA : SolvesSetAgreement A 1 S) (hof : ObstructionFree A S) :
    Fintype.card P - 1 ≤ Fintype.card ι := by
  have h := theorem10 (fun i => onlyOverwrites_swapObj (D i) (d₀ i)) (k := 1)
    (by exact_mod_cast hS) hA hof
  omega

end ConsensusFromSwap
