import Mathlib
import Papers.PODC2023.RuntimeVerification.Verifier

/-!
# Lemmas 8.1 (2) and 8.2, stability

All statements are about a finite execution `E` of `V_O` running `A*` (8 steps per operation) and
an object `O ∈ GenLin`.

* `sketch_mem_of_tight` (Lemma 8.1 (2)): if the history of the tight execution `T(E)` is in `O`,
  then so is the sketch `X(τ)` of the contents `τ` of `M` at any time.
* `tight_cut_mem_of_sketch` / `cut_mem_of_sketch` (Lemma 8.2, finite form): if every operation
  whose `N.Snapshot` happened before `t₀` has written its tuple to `M` before `s`, and the sketch
  of `M` at time `s` is in `O`, then the history of `A*` (and of `T(E)`) up to `t₀` is in `O`.
* `sketch_mono` (stability): `X(τ) ∈ O` is antitone in time: if the sketch at time `s₂` is in
  `O`, so is the sketch at any earlier time `s₁`.
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing Sketch

set_option linter.unusedSectionVars false

variable {n : ℕ} {Op Y : Type} [DecidableEq Op] [DecidableEq Y] [Inhabited Op] [Inhabited Y]

theorem TH.cut_mapRes {P Op R R' T : Type} [LinearOrder T] (h : TH P Op R T) (f : R → R')
    (t : T) : (h.mapRes f).cut t = (h.cut t).mapRes f := rfl

theorem le_of_forall_lt_imp {a b : ℕ} (h : ∀ k, k < a → k < b) : a ≤ b := by
  by_contra h'; push Not at h'; exact lt_irrefl _ (h b h')

namespace Exec

variable {E : Exec n Op Y ℕ}

theorem hT_WF (hw : E.WF) : (E.hT 8).WF := proj_WF hw _ (by norm_num) (by norm_num)
theorem hTy_WF (hw : E.WF) : (E.hTy 8).WF := proj_WF hw _ (by norm_num) (by norm_num)
theorem hSy_WF (hw : E.WF) : (E.hSy 8).WF := proj_WF hw _ (by norm_num) (by norm_num)
theorem hA_WF (hw : E.WF) : (E.hA 8).WF := proj_WF hw _ (by norm_num) (by norm_num)
theorem hVy_WF (hw : E.WF) : (E.hVy).WF := proj_WF hw _ (by norm_num) (by norm_num)

theorem lt_hT_cut_m (hw : E.WF) {t : ℕ} {p : Fin n} {k : ℕ} :
    k < ((E.hT 8).cut t).m p ↔ 8 * k + 1 < E.len p ∧ E.T p (8 * k + 1) < t := by
  rw [TH.cut_m_iff (hT_WF hw)]
  simp only [hT, proj]
  rw [lt_cnt (by norm_num)]

theorem lt_hT_cut_c (hw : E.WF) {t : ℕ} {p : Fin n} {k : ℕ} :
    k < ((E.hT 8).cut t).c p ↔ 8 * k + 4 < E.len p ∧ E.T p (8 * k + 4) < t := by
  rw [TH.cut_c_iff (hT_WF hw)]
  simp only [hT, proj]
  rw [lt_cnt (by norm_num)]

theorem tup_mem_tauAt {s : ℕ} {p : Fin n} {k : ℕ} (h1 : 8 * k + 6 < E.len p)
    (h2 : E.T p (8 * k + 6) < s) : E.tup p k ∈ E.tauAt s :=
  mem_tauAt.2 ⟨p, k, h1, h2, rfl⟩

/-- The tuple of `(p, k)` in `M`. -/
theorem lt_c_tauAt (hw : E.WF) {s : ℕ} {p : Fin n} {k : ℕ} :
    k < (XTH (E.tauAt s)).c p ↔ 8 * k + 6 < E.len p ∧ E.T p (8 * k + 6) < s := by
  rw [lt_c_iff (valid_tauAt hw s)]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    obtain ⟨q, j, h1, h2, rfl⟩ := mem_tauAt.1 ht
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, tup_mem_tauAt h1 h2, rfl, rfl⟩

theorem rec_mem_allInv (hw : E.WF) {s : ℕ} {u : Tup n Op Y} (hu : u ∈ E.tauAt s) {q : Fin n}
    {j : ℕ} (h1 : 8 * j + 1 < E.len q) (h2 : E.T q (8 * j + 1) < E.T u.p (8 * u.k + 4)) :
    ((q, j, E.op q j) : IRec n Op) ∈ allInv (E.tauAt s) := by
  obtain ⟨p, k, h3, h4, rfl⟩ := mem_tauAt.1 hu
  exact mem_allInv_tauAt.2 ⟨p, k, h3, h4, h1, h2, rfl⟩

/-- **Lemma 8.1 (2).** If the history of the tight execution `T(E)` belongs to `O ∈ GenLin`,
then the sketch of the contents of `M` at any time `s` belongs to `O`. -/
theorem sketch_mem_of_tight {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hw : E.WF)
    (hT : (E.hTy 8).toList ∈ O) (s : ℕ) : (XTHy (E.tauAt s)).toList ∈ O := by
  set τ := E.tauAt s
  have hv := valid_tauAt hw s
  set ts := τ.sup (fun u => E.T u.p (8 * u.k + 4) + 1)
  -- visibility: an `N.Write` before `ts` is in some view of `τ`
  have hvis : ∀ q j, j < ((E.hT 8).cut ts).m q → ((q, j, E.op q j) : IRec n Op) ∈ allInv τ := by
    intro q j hj
    obtain ⟨h1, h2⟩ := (lt_hT_cut_m hw).1 hj
    obtain ⟨u, hu, hlt⟩ := Finset.lt_sup_iff.1 h2
    obtain ⟨p, k, h3, h4, rfl⟩ := mem_tauAt.1 hu
    simp only [tup] at hlt
    have hne := T_ne hw (by norm_num) (by norm_num) (by norm_num : 1 ≠ 4) h1 (by omega :
      8 * k + 4 < E.len p)
    exact rec_mem_allInv hw hu h1 (by simp only [tup]; omega)
  have hsim : TH.SimTH (XTH τ) ((E.hT 8).cut ts) := by
    refine ⟨fun q => le_of_forall_lt_imp fun j hj => ?_, fun q j hj => ?_,
      fun p => le_of_forall_lt_imp fun k hk => ?_, fun p k hk => ?_, fun p k q j hk hj h => ?_⟩
    · exact (lt_m_iff hv).2 ⟨_, hvis q j hj, rfl, rfl⟩
    · exact op_eq hv (hvis q j hj)
    · obtain ⟨h1, h2⟩ := (lt_c_tauAt hw).1 hk
      refine (lt_hT_cut_c hw).2 ⟨by omega, ?_⟩
      have : E.T p (8 * k + 4) + 1 ≤ ts := by
        have := Finset.le_sup (f := fun u : Tup n Op Y => E.T u.p (8 * u.k + 4) + 1)
          (tup_mem_tauAt h1 h2)
        dsimp only [tup] at this
        exact this
      omega
    · obtain ⟨h1, h2⟩ := (lt_c_tauAt hw).1 hk
      have := res_eq hv (tup_mem_tauAt h1 h2)
      simp only [tup] at this
      rw [this]; rfl
    · obtain ⟨h1, h2⟩ := (lt_c_tauAt hw).1 hk
      have hx := hvis q j hj
      have hu := tup_mem_tauAt h1 h2
      have := (tr_lt_ti_iff hv hu hx).1 (by simpa [tup] using h)
      simp only [tup] at this
      rw [mem_view8] at this
      obtain ⟨hq1, -⟩ := (lt_hT_cut_m hw).1 hj
      show E.T p (8 * k + 4) < E.T q (8 * j + 1)
      have hne := T_ne hw (by norm_num) (by norm_num) (by norm_num : 4 ≠ 1)
        (show 8 * k + 4 < E.len p by omega) hq1
      have h' : ¬ (E.T q (8 * j + 1) < E.T p (8 * k + 4)) := fun hh => this ⟨hq1, hh, rfl⟩
      exact lt_of_le_of_ne (not_lt.1 h') hne
  have h1 := TH.SimTH.mapRes Prod.fst hsim
  exact GenLin.mem_of_simTH hO ((XTH_WF hv).mapRes _) (((hT_WF hw).cut ts).mapRes _) h1
    (hO.mem_cut (hTy_WF hw) ts hT)

end Exec

/-! ## Cutting a sketch at a stage -/

namespace Sketch

variable {τ : Finset (Tup n Op Y)}

theorem one_le_sInv (hv : Valid τ) {x : IRec n Op} (hx : x ∈ allInv τ) : 1 ≤ sInv τ x.1 x.2.1 := by
  obtain ⟨t, -, hxt, hc⟩ := sInv_spec hv hx
  rw [← hc]
  exact Finset.card_pos.2 ⟨x, hxt⟩

/-- An invocation whose stage is at most `|λ_u|` belongs to `λ_u`. -/
theorem mem_of_sInv_le (hv : Valid τ) {x : IRec n Op} (hx : x ∈ allInv τ) {u : Tup n Op Y}
    (hu : u ∈ τ) (h : sInv τ x.1 x.2.1 ≤ u.view.card) : x ∈ u.view := by
  obtain ⟨t, ht, hxt, hc⟩ := sInv_spec hv hx
  rcases hv.chain t ht u hu with h' | h'
  · exact h' hxt
  · have := Finset.eq_of_subset_of_card_le h' (by omega)
    rw [this]; exact hxt

theorem lt_cut_m (hv : Valid τ) (B : ℕ) {p : Fin n} {k : ℕ} :
    k < ((XTH τ).cut (lex3 (B + 1) 0 0)).m p ↔ k < (XTH τ).m p ∧ sInv τ p k ≤ B := by
  rw [TH.cut_m_iff (XTH_WF hv)]
  simp only [XTH, lex3_lt]
  constructor
  · rintro ⟨h1, h2 | ⟨-, h2 | ⟨-, h2⟩⟩⟩
    · exact ⟨h1, by omega⟩
    · omega
    · omega
  · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inl (by omega)⟩

theorem lt_cut_c (hv : Valid τ) (B : ℕ) {p : Fin n} {k : ℕ} :
    k < ((XTH τ).cut (lex3 (B + 1) 0 0)).c p ↔
      k < (XTH τ).c p ∧ (resOf' τ p k).2.card ≤ B := by
  rw [TH.cut_c_iff (XTH_WF hv)]
  simp only [XTH, lex3_lt]
  constructor
  · rintro ⟨h1, h2 | ⟨-, h2 | ⟨-, h2⟩⟩⟩
    · exact ⟨h1, by omega⟩
    · omega
    · omega
  · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inl (by omega)⟩

end Sketch

namespace Exec

variable {E : Exec n Op Y ℕ}

theorem hT_cut_mapRes (t : ℕ) : ((E.hT 8).cut t).mapRes Prod.fst = (E.hTy 8).cut t := rfl

/-- **Lemma 8.2** (finite form, tight history). If every operation whose `N.Snapshot` happened
before `t₀` wrote its tuple to `M` before `s`, and the sketch of `M` at time `s` is in `O`, then
the history of `T(E)` up to `t₀` is in `O`. -/
theorem tight_cut_mem_of_sketch {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hw : E.WF)
    {t₀ s : ℕ}
    (H : ∀ p k, 8 * k + 4 < E.len p → E.T p (8 * k + 4) < t₀ →
      8 * k + 6 < E.len p ∧ E.T p (8 * k + 6) < s)
    (hX : (XTHy (E.tauAt s)).toList ∈ O) : ((E.hTy 8).cut t₀).toList ∈ O := by
  set τ := E.tauAt s
  have hv := valid_tauAt hw s
  set S := τ.filter (fun u => E.T u.p (8 * u.k + 4) < t₀)
  set B := S.sup (fun u => u.view.card)
  have hrec : ∀ q j, j < ((XTH τ).cut (lex3 (B + 1) 0 0)).m q →
      8 * j + 1 < E.len q ∧ E.T q (8 * j + 1) < t₀ ∧
        ((q, j, E.op q j) : IRec n Op) ∈ allInv τ := by
    intro q j hj
    obtain ⟨hj1, hj2⟩ := (lt_cut_m hv B).1 hj
    obtain ⟨x, hx, rfl, rfl⟩ := (lt_m_iff hv).1 hj1
    have hpos := one_le_sInv hv hx
    have hS : S.Nonempty := by
      by_contra hS
      rw [Finset.not_nonempty_iff_eq_empty] at hS
      simp only [B, hS, Finset.sup_empty, bot_eq_zero'] at hj2
      omega
    obtain ⟨u, hu, huB⟩ := Finset.exists_mem_eq_sup S hS (fun u => u.view.card)
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
    have hxu := mem_of_sInv_le hv hx hu1 (by have hB : B = u.view.card := huB; rw [hB] at hj2; exact hj2)
    obtain ⟨p, k, h3, h4, rfl⟩ := mem_tauAt.1 hu1
    simp only [tup] at hxu hu2
    rw [mem_view8] at hxu
    obtain ⟨h5, h6, h7⟩ := hxu
    refine ⟨h5, lt_trans h6 hu2, ?_⟩
    rw [← h7]; exact hx
  have hsim : TH.SimTH ((E.hT 8).cut t₀) ((XTH τ).cut (lex3 (B + 1) 0 0)) := by
    refine ⟨fun q => le_of_forall_lt_imp fun j hj => ?_, fun q j hj => ?_,
      fun p => le_of_forall_lt_imp fun k hk => ?_, fun p k hk => ?_, fun p k q j hk hj h => ?_⟩
    · obtain ⟨h1, h2, -⟩ := hrec q j hj
      exact (lt_hT_cut_m hw).2 ⟨h1, h2⟩
    · exact (op_eq hv (hrec q j hj).2.2).symm
    · obtain ⟨h1, h2⟩ := (lt_hT_cut_c hw).1 hk
      obtain ⟨h3, h4⟩ := H p k h1 h2
      have hu := tup_mem_tauAt h3 h4
      refine (lt_cut_c hv B).2 ⟨(lt_c_tauAt hw).2 ⟨h3, h4⟩, ?_⟩
      have := res_eq hv hu
      simp only [tup, XTH] at this
      rw [this]
      exact Finset.le_sup (f := fun u : Tup n Op Y => u.view.card)
        (Finset.mem_filter.2 ⟨hu, by simpa [tup] using h2⟩)
    · obtain ⟨h1, h2⟩ := (lt_hT_cut_c hw).1 hk
      obtain ⟨h3, h4⟩ := H p k h1 h2
      have := res_eq hv (tup_mem_tauAt h3 h4)
      simp only [tup] at this
      show (E.y p k, E.view 8 p k) = (XTH τ).res p k
      rw [this]
    · obtain ⟨h1, h2⟩ := (lt_hT_cut_c hw).1 hk
      obtain ⟨h3, h4⟩ := H p k h1 h2
      have hu := tup_mem_tauAt h3 h4
      obtain ⟨-, -, hx⟩ := hrec q j hj
      have key := (tr_lt_ti_iff hv hu hx).2 (by
        simp only [tup]
        rw [mem_view8]
        intro hh
        have : E.T q (8 * j + 1) < E.T p (8 * k + 4) := hh.2.1
        change E.T p (8 * k + 4) < E.T q (8 * j + 1) at h
        omega)
      exact key
  have h1 := TH.SimTH.mapRes Prod.fst hsim
  rw [← hT_cut_mapRes]
  exact GenLin.mem_of_simTH hO (((hT_WF hw).cut t₀).mapRes _)
    (((XTH_WF hv).cut _).mapRes _) h1
    (by rw [← TH.cut_mapRes]; exact hO.mem_cut ((XTH_WF hv).mapRes _) _ hX)

/-- **Lemma 8.2** (finite form). Under the same hypotheses, the history of `A*` up to `t₀` is in
`O`. -/
theorem cut_mem_of_sketch {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hw : E.WF) {t₀ s : ℕ}
    (H : ∀ p k, 8 * k + 4 < E.len p → E.T p (8 * k + 4) < t₀ →
      8 * k + 6 < E.len p ∧ E.T p (8 * k + 6) < s)
    (hX : (XTHy (E.tauAt s)).toList ∈ O) : ((E.hSy 8).cut t₀).toList ∈ O := by
  have hT := tight_cut_mem_of_sketch hO hw H hX
  have e1 : (E.cut t₀).hSy 8 = (E.hSy 8).cut t₀ := proj_cut hw t₀ _ (by norm_num) (by norm_num)
  have e2 : (E.cut t₀).hTy 8 = (E.hTy 8).cut t₀ := proj_cut hw t₀ _ (by norm_num) (by norm_num)
  rw [← e1]
  rw [← e2] at hT
  exact GenLin.mem_of_simTH hO (hSy_WF (hw.cut t₀)) (hTy_WF (hw.cut t₀))
    (simTH_S_T (hw.cut t₀) (by norm_num) _) hT

theorem tauAt_mono {s₁ s₂ : ℕ} (hs : s₁ ≤ s₂) : E.tauAt s₁ ⊆ E.tauAt s₂ := by
  intro t ht
  obtain ⟨q, j, h1, h2, rfl⟩ := mem_tauAt.1 ht
  exact mem_tauAt.2 ⟨q, j, h1, by omega, rfl⟩

/-- **Stability.** If the sketch of `M` at time `s₂` is in `O`, so is the sketch at any earlier
time `s₁`. Equivalently, once a process reports `ERROR`, every later test reports `ERROR`. -/
theorem sketch_mono {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hw : E.WF) {s₁ s₂ : ℕ}
    (hs : s₁ ≤ s₂) (h₂ : (XTHy (E.tauAt s₂)).toList ∈ O) : (XTHy (E.tauAt s₁)).toList ∈ O := by
  set τ₁ := E.tauAt s₁
  set τ₂ := E.tauAt s₂
  have hv₁ := valid_tauAt hw s₁
  have hv₂ := valid_tauAt hw s₂
  have hsub : τ₁ ⊆ τ₂ := tauAt_mono hs
  set B := τ₁.sup (fun u => u.view.card)
  have hrec : ∀ q j, j < ((XTH τ₂).cut (lex3 (B + 1) 0 0)).m q →
      ((q, j, E.op q j) : IRec n Op) ∈ allInv τ₁ ∧ ((q, j, E.op q j) : IRec n Op) ∈ allInv τ₂ := by
    intro q j hj
    obtain ⟨hj1, hj2⟩ := (lt_cut_m hv₂ B).1 hj
    obtain ⟨x, hx, rfl, rfl⟩ := (lt_m_iff hv₂).1 hj1
    have hpos := one_le_sInv hv₂ hx
    have hS : τ₁.Nonempty := by
      by_contra hS
      rw [Finset.not_nonempty_iff_eq_empty] at hS
      simp only [B, hS, Finset.sup_empty, bot_eq_zero'] at hj2
      omega
    obtain ⟨u, hu, huB⟩ := Finset.exists_mem_eq_sup τ₁ hS (fun u => u.view.card)
    have hxu := mem_of_sInv_le hv₂ hx (hsub hu) (by have hB : B = u.view.card := huB; rw [hB] at hj2; exact hj2)
    have he := op_of_mem_allInv hx
    have : x = (x.1, x.2.1, E.op x.1 x.2.1) := by rw [← he]
    rw [← this]
    exact ⟨mem_allInv.2 ⟨u, hu, hxu⟩, hx⟩
  have hsim : TH.SimTH (XTH τ₁) ((XTH τ₂).cut (lex3 (B + 1) 0 0)) := by
    refine ⟨fun q => le_of_forall_lt_imp fun j hj => ?_, fun q j hj => ?_,
      fun p => le_of_forall_lt_imp fun k hk => ?_, fun p k hk => ?_, fun p k q j hk hj h => ?_⟩
    · exact (lt_m_iff hv₁).2 ⟨_, (hrec q j hj).1, rfl, rfl⟩
    · show (XTH τ₁).op q j = (XTH τ₂).op q j
      rw [op_eq hv₁ (hrec q j hj).1, op_eq hv₂ (hrec q j hj).2]
    · obtain ⟨t, ht, rfl, rfl⟩ := (lt_c_iff hv₁).1 hk
      refine (lt_cut_c hv₂ B).2 ⟨(lt_c_iff hv₂).2 ⟨t, hsub ht, rfl, rfl⟩, ?_⟩
      have := res_eq hv₂ (hsub ht)
      simp only [XTH] at this
      rw [this]
      exact Finset.le_sup (f := fun u : Tup n Op Y => u.view.card) ht
    · obtain ⟨t, ht, rfl, rfl⟩ := (lt_c_iff hv₁).1 hk
      show (XTH τ₁).res t.p t.k = (XTH τ₂).res t.p t.k
      rw [res_eq hv₁ ht, res_eq hv₂ (hsub ht)]
    · obtain ⟨t, ht, rfl, rfl⟩ := (lt_c_iff hv₁).1 hk
      obtain ⟨hx₁, hx₂⟩ := hrec q j hj
      have := (tr_lt_ti_iff hv₁ ht hx₁).1 h
      exact (tr_lt_ti_iff hv₂ (hsub ht) hx₂).2 this
  have h1 := TH.SimTH.mapRes Prod.fst hsim
  exact GenLin.mem_of_simTH hO ((XTH_WF hv₁).mapRes _) (((XTH_WF hv₂).cut _).mapRes _) h1
    (by rw [← TH.cut_mapRes]; exact hO.mem_cut ((XTH_WF hv₂).mapRes _) _ h₂)

end Exec

end Podc2023.RuntimeVerification
