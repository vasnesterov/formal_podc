import Papers.PODC2024.HistoryIndependent.Alg4StepR

/-!
# Algorithm 4: the invariant is preserved by the writer's steps (and by invocations and
responses)
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Alg4

variable {K : ℕ} [NeZero K] {v₀ : Fin K}

/-- Normalize the derived quantities of a concrete abstract state. -/
macro "norm_st" : tactic => `(tactic| simp only [St.n, St.c, St.nA, St.vals, WPC.preA,
  reduceCtorEq, ite_false, ite_true, Bool.false_eq_true, ↓reduceIte] at *)

/-- Arithmetic on `Fin K` indices. -/
macro "fin_omega" : tactic => `(tactic| (simp only [Fin.le_def, Fin.lt_def, ne_eq, Fin.ext_iff] at *; omega))

lemma RPC.s1_of_f2v {rpc : RPC K} (h : rpc.f2v = false) (x : Fin K) : rpc.s1 x := by
  cases rpc <;> simp_all [RPC.f2v, RPC.s1]

lemma RPC.cov_of_f1v {rpc : RPC K} {x : Fin K} (h : rpc.f1v = true) (h' : rpc.s1 x) :
    rpc.cov x := by
  cases rpc <;> simp_all [RPC.f1v, RPC.s1, RPC.cov]

lemma RPC.f1v_of_active {rpc : RPC K} (h : rpc.active) : rpc.f1v = true := by
  cases rpc <;> simp_all [RPC.f1v, RPC.active]

lemma RPC.f2v_of_active {rpc : RPC K} (h : rpc.active) : rpc.f2v = false := by
  cases rpc <;> simp_all [RPC.f2v, RPC.active]

lemma update_true_iff {A : Fin K → Bool} {v x : Fin K} :
    Function.update A v true x = true ↔ x = v ∨ A x = true := by
  by_cases h : x = v
  · subst h; simp
  · simp [h]

lemma update_false_iff {A : Fin K → Bool} {j x : Fin K} :
    Function.update A j false x = true ↔ x ≠ j ∧ A x = true := by
  by_cases h : x = j
  · subst h; simp
  · simp [h]

/-! ### Moves of the writer's program counter before Line 16 -/

lemma inv_stepW_scanB_one {s : St K} (hI : Inv v₀ s) {v j : Fin K} (hs : s.wpc = .scanB v j)
    (hB : s.Bm j = true) : Inv v₀ { s with wpc := .setA v } := by
  cases s; dsimp only at hs hB ⊢; subst hs
  exact { hI with
    scan := fun v j h => by simp at h
    scan' := fun v h => by simp at h
    bprot := fun x hx => by
      rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
      · exact Or.inl h
      · simp [WPC.win] at h3
      · simp [WPC.win'] at h3
    h1 := fun ha hlt => by
      obtain ⟨x, hx1, hx2, -, hx4⟩ := hI.h1 ha hlt
      exact ⟨x, hx1, hx2, fun v j h => by simp at h, hx4⟩
    h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h, fun _ _ => ⟨j, hB⟩⟩ }

lemma inv_stepW_scanB_next {s : St K} (hI : Inv v₀ s) {v j : Fin K} (hs : s.wpc = .scanB v j)
    (hB : s.Bm j = false) (hK : j.val + 1 < K) :
    Inv v₀ { s with wpc := .scanB v ⟨j.val + 1, hK⟩ } := by
  cases s; dsimp only at hs hB ⊢; subst hs
  exact { hI with
    scan := fun v' j' h x hx => by
      simp at h; obtain ⟨rfl, rfl⟩ := h
      rcases lt_or_eq_of_le (show x ≤ j by rw [Fin.lt_def] at hx; rw [Fin.le_def]; simp at hx; omega)
        with h | rfl
      · exact hI.scan _ _ rfl x h
      · exact hB
    scan' := fun v h => by simp at h
    bprot := fun x hx => by
      rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
      · exact Or.inl h
      · simp [WPC.win] at h3
      · simp [WPC.win'] at h3
    h1 := fun ha hlt => by
      obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hI.h1 ha hlt
      refine ⟨x, hx1, hx2, fun v' j' h => ?_, hx4⟩
      simp at h; obtain ⟨rfl, rfl⟩ := h
      have := hx3 _ _ rfl
      rcases lt_or_eq_of_le this with h | rfl
      · rw [Fin.le_def]; exact Fin.lt_def.1 h
      · simp_all
    h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
      fun v h => by simp at h⟩ }

lemma inv_stepW_scanB_end {s : St K} (hI : Inv v₀ s) {v j : Fin K} (hs : s.wpc = .scanB v j)
    (hB : s.Bm j = false) (hK : ¬ j.val + 1 < K) : Inv v₀ { s with wpc := .rdF1 v } := by
  cases s; dsimp only at hs hB ⊢; subst hs
  exact { hI with
    scan := fun v' j' h => by simp at h
    scan' := fun v' h x => by
      rcases lt_or_eq_of_le (show x ≤ j by rw [Fin.le_def]; have := x.isLt; omega) with h | rfl
      · exact hI.scan _ _ rfl x h
      · exact hB
    bprot := fun x hx => by
      rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
      · exact Or.inl h
      · simp [WPC.win] at h3
      · simp [WPC.win'] at h3
    h1 := fun ha hlt => by
      obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hI.h1 ha hlt
      have := hx3 _ _ rfl
      rcases lt_or_eq_of_le this with h | rfl
      · have := Fin.lt_def.1 h; have := x.isLt; omega
      · simp_all
    h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
      fun v h => by simp at h⟩ }

lemma inv_stepW_rdF1 {s : St K} (hI : Inv v₀ s) {v : Fin K} (hs : s.wpc = .rdF1 v) :
    Inv v₀ { s with wpc := if s.f1 then .setB v else .setA v } := by
  obtain ⟨A, Bm, f1, f2, last, wpc, rpc, wv, tagA, tagB, sN1, sT, lo, rf, fl, pis⟩ := s
  dsimp only at hs ⊢; subst hs
  have hno : ∀ (ha : _) (hlt : _), False := fun ha hlt => by
    obtain ⟨x, -, hx2, -⟩ := hI.h1 ha hlt; simp [WPC.noWin] at hx2
  cases f1
  · exact { hI with
      scan := fun v j h => by simp at h
      scan' := fun v h => by simp at h
      bprot := fun x hx => by
        rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · exact Or.inl h
        · simp [WPC.win] at h3
        · simp [WPC.win'] at h3
      h1 := fun ha hlt => (hno ha hlt).elim
      h2 := fun ha hlt => by
        have := hI.f1; rw [RPC.f1v_of_active ha] at this; simp at this }
  · exact { hI with
      scan := fun v j h => by simp at h
      scan' := fun v' h => by simp at h; subst h; exact hI.scan' _ (Or.inl rfl)
      bprot := fun x hx => by
        rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · exact Or.inl h
        · simp [WPC.win] at h3
        · simp [WPC.win'] at h3
      h1 := fun ha hlt => (hno ha hlt).elim
      h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
        fun v h => by simp at h⟩ }

lemma inv_stepW_setB {s : St K} (hI : Inv v₀ s) {v : Fin K} (hs : s.wpc = .setB v) :
    Inv v₀ { s with Bm := Function.update s.Bm s.last true,
                    tagB := Function.update s.tagB s.last s.n, wpc := .rdF2 v } := by
  have hn := hI.pend_n (by simp [hs])
  have hc := hI.pend_c (by simp [hs])
  have hnA : s.nA + 1 = s.n := by simp [St.nA, hs, WPC.preA]; omega
  have hB0 := hI.scan' v (Or.inr hs)
  have hlast := hI.lastv
  have hB : ∀ x, Function.update s.Bm s.last true x = true → x = s.last := by
    intro x hx; rcases update_true_iff.1 hx with h | h
    · exact h
    · simp [hB0 x] at h
  have hrf : ∀ val, s.rpc.val? = some val → s.rf < s.n := by
    intro val h; have := (hI.rf val h).2.1; omega
  have hrfl : s.rpc.late → s.rf < s.n := by
    intro hl; have := hI.l10 hl
    obtain ⟨val, hv⟩ := Option.isSome_iff_exists.1 this
    exact hrf val hv
  have hlo : s.rpc ≠ .idle → s.lo < s.n := fun hr => by have := hI.lo hr; omega
  have hfl : s.fl < s.n := by have := hI.fl1; omega
  have hval : s.last = s.vals v₀ (s.n - 1) := by rw [hlast]; congr 1; omega
  obtain ⟨A, Bm, f1, f2, last, wpc, rpc, wv, tagA, tagB, sN1, sT, lo, rf, fl, pis⟩ := s
  dsimp only at hs hB0 hB hrf hrfl hn hlo hfl hval ⊢; subst hs
  exact { hI with
    scan := fun v j h => by simp at h
    scan' := fun v h => by simp at h
    bprot := fun x hx => by
      have := hB x hx; subst this
      exact Or.inr ⟨rfl, by simp [St.n], Or.inl (by simp [WPC.win])⟩
    bval := fun x hx => by
      have := hB x hx; subst this
      simp only [Function.update_self]
      exact ⟨hn, le_rfl, hval⟩
    b11 := fun hr x hx => by
      have := hB x hx; subst this
      simp only [Function.update_self]
      exact hlo hr
    h1 := fun ha hlt => by
      obtain ⟨x, -, hx2, -⟩ := hI.h1 ha hlt; simp [WPC.noWin] at hx2
    h2 := fun ha hlt => ⟨fun v h => by simp, fun v h => by simp at h, fun v h => by simp at h⟩
    rfB := fun j val h x hx hBx => by
      dsimp only at h
      have := hB x hBx; subst this
      simp only [Function.update_self]
      exact hrfl (by simp [h, RPC.late])
    rfB' := fun hf x hBx => by
      dsimp only at hf
      have := hB x hBx; subst this
      simp only [Function.update_self]
      exact hrfl (by revert hf; cases rpc <;> simp [RPC.fin, RPC.late])
    fl2 := fun x hx => by
      have := hB x hx; subst this
      simp only [Function.update_self]
      exact hfl }

lemma inv_stepW_rdF2 {s : St K} (hI : Inv v₀ s) {v : Fin K} (hs : s.wpc = .rdF2 v) :
    Inv v₀ { s with wpc := if s.f2 then .clrB v else .rdF1' v } := by
  obtain ⟨A, Bm, f1, f2, last, wpc, rpc, wv, tagA, tagB, sN1, sT, lo, rf, fl, pis⟩ := s
  dsimp only at hs ⊢; subst hs
  have hno : ∀ (ha : _) (hlt : _), False := fun ha hlt => by
    obtain ⟨x, -, hx2, -⟩ := hI.h1 ha hlt; simp [WPC.noWin] at hx2
  have hf2 := hI.f2; dsimp only at hf2
  cases f2
  · exact { hI with
      scan := fun v j h => by simp at h
      scan' := fun v h => by simp at h
      bprot := fun x hx => by
        rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, Or.inr ⟨by simp [WPC.win'], RPC.s1_of_f2v hf2.symm x⟩⟩
        · simp [WPC.win'] at h3
      h1 := fun ha hlt => (hno ha hlt).elim
      h2 := fun ha hlt => ⟨fun v' _ => (hI.h2 ha hlt).1 v (Or.inl rfl),
        fun v h => by simp at h, fun v h => by simp at h⟩ }
  · exact { hI with
      scan := fun v j h => by simp at h
      scan' := fun v h => by simp at h
      bprot := fun x hx => by
        rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, Or.inl (by simp [WPC.win])⟩
        · simp [WPC.win'] at h3
      h1 := fun ha hlt => (hno ha hlt).elim
      h2 := fun ha hlt => by
        rw [RPC.f2v_of_active ha] at hf2; simp at hf2 }

lemma inv_stepW_rdF1' {s : St K} (hI : Inv v₀ s) {v : Fin K} (hs : s.wpc = .rdF1' v) :
    Inv v₀ { s with wpc := if s.f1 then .setA v else .clrB v } := by
  obtain ⟨A, Bm, f1, f2, last, wpc, rpc, wv, tagA, tagB, sN1, sT, lo, rf, fl, pis⟩ := s
  dsimp only at hs ⊢; subst hs
  have hno : ∀ (ha : _) (hlt : _), False := fun ha hlt => by
    obtain ⟨x, -, hx2, -⟩ := hI.h1 ha hlt; simp [WPC.noWin] at hx2
  have hf1 := hI.f1; dsimp only at hf1
  cases f1
  · exact { hI with
      scan := fun v j h => by simp at h
      scan' := fun v h => by simp at h
      bprot := fun x hx => by
        rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · exact Or.inl h
        · simp [WPC.win] at h3
        · exact Or.inr ⟨h1, h2, Or.inl (by simp [WPC.win])⟩
      h1 := fun ha hlt => (hno ha hlt).elim
      h2 := fun ha hlt => by
        rw [RPC.f1v_of_active ha] at hf1; simp at hf1 }
  · exact { hI with
      scan := fun v j h => by simp at h
      scan' := fun v h => by simp at h
      bprot := fun x hx => by
        rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · exact Or.inl h
        · simp [WPC.win] at h3
        · exact Or.inl (RPC.cov_of_f1v hf1.symm h4)
      h1 := fun ha hlt => (hno ha hlt).elim
      h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
        fun v' _ => ⟨_, (hI.h2 ha hlt).1 v (Or.inr rfl)⟩⟩ }

lemma inv_stepW_clrB {s : St K} (hI : Inv v₀ s) {v : Fin K} (hs : s.wpc = .clrB v) :
    Inv v₀ { s with Bm := Function.update s.Bm s.last false, wpc := .setA v } := by
  have hB : ∀ x, Function.update s.Bm s.last false x = true → x ≠ s.last ∧ s.Bm x = true :=
    fun x hx => update_false_iff.1 hx
  obtain ⟨A, Bm, f1, f2, last, wpc, rpc, wv, tagA, tagB, sN1, sT, lo, rf, fl, pis⟩ := s
  dsimp only at hs hB ⊢; subst hs
  exact { hI with
    scan := fun v j h => by simp at h
    scan' := fun v h => by simp at h
    bprot := fun x hx => by
      obtain ⟨hne, hx⟩ := hB x hx
      rcases hI.bprot x hx with h | ⟨h1, -⟩
      · exact Or.inl h
      · exact absurd h1 hne
    bval := fun x hx => hI.bval x (hB x hx).2
    b11 := fun hr x hx => hI.b11 hr x (hB x hx).2
    h1 := fun ha hlt => by
      obtain ⟨x, -, hx2, -⟩ := hI.h1 ha hlt; simp [WPC.noWin] at hx2
    h2 := fun ha hlt => absurd rfl ((hI.h2 ha hlt).2.1 v)
    rfB := fun j val h x hx hBx => hI.rfB j val h x hx (hB x hBx).2
    rfB' := fun hf x hBx => hI.rfB' hf x (hB x hBx).2
    fl2 := fun x hx => hI.fl2 x (hB x hx).2 }

/-! ### Line 16 -/

lemma memA_setA {A : Fin K → Bool} {last v : Fin K} {W : WPC K}
    (hA : ∀ x, A x = true ↔ x = last) (hW : W.newv = some v)
    (hold : ∀ x, x ≠ v → (W.old last x ↔ x = last)) :
    ∀ x, Function.update A v true x = true ↔ (W.newv = some x ∨ W.old last x) := by
  intro x
  rw [update_true_iff, hW]
  by_cases hx : x = v
  · subst hx; simp
  · rw [hA, hold x hx]; simp [hx, Ne.symm hx]

lemma tagA_setA {A : Fin K → Bool} {tagA : Fin K → ℕ} {v : Fin K} {W : WPC K} {n c : ℕ}
    (htag : ∀ x, A x = true → tagA x = c) (hW : W.newv = some v) :
    ∀ x, Function.update A v true x = true →
      Function.update tagA v n x = if W.newv = some x then n else c := by
  intro x hx
  rw [hW]
  by_cases h : x = v
  · subst h; simp
  · rw [Function.update_of_ne h]
    simp [Ne.symm h, htag x ((update_true_iff.1 hx).resolve_left h)]

lemma inv_stepW_setA {s : St K} (hI : Inv v₀ s) {v : Fin K} (hs : s.wpc = .setA v) :
    Inv v₀ { s with A := Function.update s.A v true, tagA := Function.update s.tagA v s.n,
                    wpc := WPC.afterSetA v } := by
  have hn1 := hI.pend_n (by simp [hs])
  have hc := hI.pend_c (by simp [hs])
  have hnA : s.nA + 1 = s.n := by simp [St.nA, hs, WPC.preA]; omega
  have hnAle : s.nA ≤ s.n := by omega
  have hv := (hI.pendv v (by simp [hs, WPC.val?])).1
  have hAold : ∀ x, s.A x = true ↔ x = s.last := fun x => by
    simpa [hs, WPC.newv, WPC.old] using hI.memA x
  have htag : ∀ x, s.A x = true → s.tagA x = s.c := fun x hx => by
    simpa [hs, WPC.newv] using hI.tagA x hx
  have h1' : s.rpc.active → s.sN1 < s.n → ∃ x, s.Bm x = true ∧
      (∀ j, s.rpc = .bscan j none → j ≤ x) := by
    intro ha hlt
    by_cases h : s.sN1 < s.nA
    · obtain ⟨x, hx1, -, -, hx4⟩ := hI.h1 ha h
      exact ⟨x, hx1, hx4⟩
    · obtain ⟨x, hx⟩ := (hI.h2 ha hlt).2.2 v hs
      refine ⟨x, hx, fun j hj => ?_⟩
      have := hI.h4'' j hj; omega
  have hup : ∀ b j, s.rpc = .up b j → s.sT < s.n := by
    intro b j h
    cases b
    · have := (hI.h4 j h).2; omega
    · have := (hI.h4' j h).2; omega
  have hrf : ∀ v', s.rpc.val? = some v' → s.rf ≤ s.c := by
    intro v' h
    rcases (hI.rf v' h).2.2.2.2 with h' | ⟨-, h', -⟩
    · exact h'
    · simp [hs, WPC.postA] at h'
  have hfl3 : s.fl ≤ s.c := by
    rcases hI.fl3 with h' | ⟨-, h', -⟩
    · exact h'
    · simp [hs, WPC.postA] at h'
  have hcov : ∀ x, s.Bm x = true → s.rpc.cov x := fun x hx =>
    (hI.bprot x hx).resolve_right (by simp [hs, WPC.win, WPC.win'])
  rcases WPC.afterSetA_spec v with ⟨hv0, hlt, hf⟩ | ⟨hv0, hlt, hf⟩ | ⟨hv0, hK, hf⟩
  all_goals
    have hold : ∀ x, x ≠ v → ((WPC.afterSetA v).old s.last x ↔ x = s.last) := by
      intro x hx
      rw [hf]
      simp only [WPC.old, and_iff_left_iff_imp]
      first
        | (intro _; rcases lt_or_gt_of_ne hx with h | h
           · left; rw [Fin.le_def]; rw [Fin.lt_def] at h; simp only; omega
           · right; exact h)
        | (intro _; rw [Fin.le_def]; simp only
           have : x.val ≠ v.val := fun h => hx (Fin.ext h)
           omega)
        | (have : x = v := Fin.ext (by have := x.isLt; have := v.isLt; omega)
           exact absurd this hx)
    have hmem := memA_setA hAold (by rw [hf]; rfl) hold
    have htg := tagA_setA (n := s.n) htag (W := WPC.afterSetA v) (by rw [hf]; rfl)
    rw [hf] at hmem htg ⊢
    obtain ⟨A, Bm, f1, f2, last, wpc, rpc, wv, tagA, tagB, sN1, sT, lo, rf, fl, pis⟩ := s
    dsimp only at hs hn1 hc hnA hnAle hv hAold htag h1' hup hrf hfl3 hcov hmem htg ⊢
    subst hs
    exact { hI with
      wf := by first | trivial | (simp only [WPC.wf]; rw [Fin.lt_def]; simp only; omega)
      pendv := fun v' h => by simp [WPC.val?] at h; subst h; exact ⟨hv, hn1⟩
      memA := hmem
      tagA := htg
      scan := fun v j h => by simp at h
      scan' := fun v h => by simp at h
      bprot := fun x hx => Or.inl (hcov x hx)
      h1 := fun ha hlt => by
        obtain ⟨x, hx1, hx2⟩ := h1' ha hlt
        exact ⟨x, hx1, by simp [WPC.noWin], fun v j h => by simp at h, hx2⟩
      h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
        fun v h => by simp at h⟩
      h3 := fun b j h e => by have := hup b j h; norm_st; omega
      h4 := fun j h => ⟨(hI.h4 j h).1, (hI.h4 j h).2.trans hnAle⟩
      h4' := fun j h => ⟨(hI.h4' j h).1, (hI.h4' j h).2.trans hnAle⟩
      h4'' := fun j h => (hI.h4'' j h).trans_le hnAle
      rf := fun v' h => by
        obtain ⟨a1, a2, a3, a4, -⟩ := hI.rf v' h
        exact ⟨a1, a2.trans hnAle, a3, a4, Or.inl (hrf v' h)⟩
      fl1 := hI.fl1.trans hnAle
      fl3 := Or.inl hfl3 }

/-! ### Lines 17-18 -/

lemma memA_clear {A : Fin K → Bool} {j v : Fin K} {P Q : Fin K → Prop}
    (hA : ∀ x, A x = true ↔ (some v = some x ∨ P x)) (hjv : j ≠ v)
    (hQ : ∀ x, x ≠ j → (Q x ↔ P x)) (hQj : ¬ Q j) :
    ∀ x, Function.update A j false x = true ↔ (some v = some x ∨ Q x) := by
  intro x
  rw [update_false_iff]
  by_cases hx : x = j
  · subst hx; simp [hQj, Ne.symm hjv]
  · rw [hA, hQ x hx]; simp [hx]

lemma inv_stepW_down {s : St K} (hI : Inv v₀ s) {v j : Fin K} (hs : s.wpc = .down v j) :
    Inv v₀ { s with A := Function.update s.A j false, wpc := WPC.downNext v j } := by
  have hjv : j < v := by simpa [hs, WPC.wf] using hI.wf
  have hcov : ∀ x, s.Bm x = true → s.rpc.cov x := fun x hx =>
    (hI.bprot x hx).resolve_right (by simp [hs, WPC.win, WPC.win'])
  have hmemA := hI.memA
  rcases WPC.downNext_spec v j with ⟨hj0, hlt, hf⟩ | ⟨hj0, hlt, hf⟩ | ⟨hj0, hK, hf⟩
  all_goals
    rw [hf]
    obtain ⟨A, Bm, f1, f2, last, wpc, rpc, wv, tagA, tagB, sN1, sT, lo, rf, fl, pis⟩ := s
    dsimp only at hs hcov hmemA ⊢
    subst hs
    have hmem : ∀ x, Function.update A j false x = true ↔
        (some v = some x ∨ WPC.old last x (WPC.downNext v j)) := by
      rw [hf]
      refine memA_clear hmemA (ne_of_lt hjv) ?_ ?_
      · intro x hx; simp only [WPC.old]
        first
          | (constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> fin_omega)
          | (simp only [false_iff, not_and]; intro _ _; fin_omega)
      · simp only [WPC.old, not_and]; first | (intro _; fin_omega) | simp
    rw [hf] at hmem
    exact { hI with
      wf := by first | trivial | (simp only [WPC.wf]; fin_omega)
      memA := hmem
      tagA := fun x hx => hI.tagA x (update_false_iff.1 hx).2
      scan := fun v j h => by simp at h
      scan' := fun v h => by simp at h
      bprot := fun x hx => Or.inl (hcov x hx)
      h1 := fun ha hlt => by
        obtain ⟨x, hx1, -, -, hx4⟩ := hI.h1 ha hlt
        exact ⟨x, hx1, by simp [WPC.noWin], fun v j h => by simp at h, hx4⟩
      h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
        fun v h => by simp at h⟩
      rf := fun v' h => by
        obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v' h
        exact ⟨a1, a2, a3, a4, a5.imp_right fun h' => ⟨h'.1, by simp [WPC.postA],
          fun x hx hd hA => h'.2.2 x hx hd (update_false_iff.1 hA).2⟩⟩
      fl3 := hI.fl3.imp_right fun h' => ⟨h'.1, by simp [WPC.postA],
          fun x hx hA => h'.2.2 x hx (update_false_iff.1 hA).2⟩ }

lemma inv_stepW_up {s : St K} (hI : Inv v₀ s) {v j : Fin K} (hs : s.wpc = .up v j) :
    Inv v₀ { s with A := Function.update s.A j false, wpc := WPC.upNext v j } := by
  have hjv : v < j := by simpa [hs, WPC.wf] using hI.wf
  have hcov : ∀ x, s.Bm x = true → s.rpc.cov x := fun x hx =>
    (hI.bprot x hx).resolve_right (by simp [hs, WPC.win, WPC.win'])
  have hmemA := hI.memA
  rcases WPC.upNext_spec v j with ⟨hlt, hf⟩ | ⟨hK, hf⟩
  all_goals
    rw [hf]
    obtain ⟨A, Bm, f1, f2, last, wpc, rpc, wv, tagA, tagB, sN1, sT, lo, rf, fl, pis⟩ := s
    dsimp only at hs hcov hmemA ⊢
    subst hs
    have hmem : ∀ x, Function.update A j false x = true ↔
        (some v = some x ∨ WPC.old last x (WPC.upNext v j)) := by
      rw [hf]
      refine memA_clear hmemA (ne_of_gt hjv) ?_ ?_
      · intro x hx; simp only [WPC.old]
        first
          | (constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> fin_omega)
          | (simp only [false_iff, not_and]; intro _ _; fin_omega)
      · simp only [WPC.old, not_and]; first | (intro _; fin_omega) | simp
    rw [hf] at hmem
    exact { hI with
      wf := by first | trivial | (simp only [WPC.wf]; fin_omega)
      memA := hmem
      tagA := fun x hx => hI.tagA x (update_false_iff.1 hx).2
      scan := fun v j h => by simp at h
      scan' := fun v h => by simp at h
      bprot := fun x hx => Or.inl (hcov x hx)
      h1 := fun ha hlt => by
        obtain ⟨x, hx1, -, -, hx4⟩ := hI.h1 ha hlt
        exact ⟨x, hx1, by simp [WPC.noWin], fun v j h => by simp at h, hx4⟩
      h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
        fun v h => by simp at h⟩
      rf := fun v' h => by
        obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v' h
        exact ⟨a1, a2, a3, a4, a5.imp_right fun h' => ⟨h'.1, by simp [WPC.postA],
          fun x hx hd hA => h'.2.2 x hx hd (update_false_iff.1 hA).2⟩⟩
      fl3 := hI.fl3.imp_right fun h' => ⟨h'.1, by simp [WPC.postA],
          fun x hx hA => h'.2.2 x hx (update_false_iff.1 hA).2⟩ }

/-! ### Invocations and responses -/

lemma inv_invW {s : St K} (hI : Inv v₀ s) (hs : s.wpc = .idle) (v : Fin K) :
    Inv v₀ { s with wpc := .scanB v 0, wv := s.wv ++ [v] } := by
  have hn : St.n { s with wpc := .scanB v 0, wv := s.wv ++ [v] } = s.n + 1 := by simp [St.n]
  have hnA : St.nA { s with wpc := .scanB v 0, wv := s.wv ++ [v] } = s.nA := by
    simp [St.nA, St.n, hs, WPC.preA]
  have hc : St.c { s with wpc := .scanB v 0, wv := s.wv ++ [v] } = s.c := by
    simp [St.c, St.n, hs]
  have hnA0 : s.nA = s.n := by simp [St.nA, hs, WPC.preA]
  have hc0 : s.c = s.n := by simp [St.c, hs]
  have hv : ∀ m ≤ s.n, St.vals v₀ { s with wpc := .scanB v 0, wv := s.wv ++ [v] } m =
      s.vals v₀ m := fun m hm => St.vals_append v₀ s v hm
  have hvl : St.vals v₀ { s with wpc := .scanB v 0, wv := s.wv ++ [v] } (s.n + 1) = v :=
    St.vals_append_last v₀ s v
  have hcov : ∀ x, s.Bm x = true → s.rpc.cov x := fun x hx =>
    (hI.bprot x hx).resolve_right (by simp [hs, WPC.win, WPC.win'])
  have hrfn : ∀ v', s.rpc.val? = some v' → s.rf ≤ s.n := fun v' h => by
    have := (hI.rf v' h).2.1; omega
  have hfln : s.fl ≤ s.n := by have := hI.fl1; omega
  exact { hI with
    wf := trivial
    pendv := fun v' h => by
      simp [WPC.val?] at h; subst h
      exact ⟨by rw [hn, hvl], by omega⟩
    lastv := by rw [hc, hv _ (by omega)]; exact hI.lastv
    memA := fun x => by
      dsimp only; rw [hI.memA x]; simp [hs, WPC.newv, WPC.old]
    tagA := fun x hx => by
      dsimp only at hx ⊢; rw [hI.tagA x hx, hc]; simp [hs, WPC.newv]
    scan := fun v' j h x hx => by
      simp at h; obtain ⟨-, rfl⟩ := h; exact absurd hx (by simp)
    scan' := fun v' h => by simp at h
    bprot := fun x hx => Or.inl (hcov x hx)
    bval := fun x hx => by
      obtain ⟨a, b, c⟩ := hI.bval x hx
      dsimp only
      refine ⟨a, by rw [hn]; omega, ?_⟩
      rw [hv _ (by omega)]; exact c
    lo := fun hr => by rw [hc]; exact hI.lo hr
    h1 := fun ha hlt => by
      rw [hnA] at hlt
      obtain ⟨x, hx1, -, -, hx4⟩ := hI.h1 ha hlt
      exact ⟨x, hx1, by simp [WPC.noWin], fun v' j h => by
        simp at h; rw [← h.2]; exact Fin.zero_le _, hx4⟩
    h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
      fun v h => by simp at h⟩
    h3 := fun b j h e => by
      rw [hnA] at e ⊢; rw [hv _ (by omega)]; exact hI.h3 b j h e
    h4 := fun j h => by rw [hnA]; exact hI.h4 j h
    h4' := fun j h => by rw [hnA]; exact hI.h4' j h
    h4'' := fun j h => by rw [hnA]; exact hI.h4'' j h
    rf := fun v' h => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v' h
      have := hrfn v' h
      refine ⟨by rw [hv _ this]; exact a1, by rw [hnA]; exact a2, a3, a4, Or.inl ?_⟩
      rw [hc]; rcases a5 with h' | ⟨-, h', -⟩
      · exact h'
      · simp [hs, WPC.postA] at h'
    fl1 := by rw [hnA]; exact hI.fl1
    fl3 := by
      rw [hc]; rcases hI.fl3 with h' | ⟨-, h', -⟩
      · exact Or.inl h'
      · simp [hs, WPC.postA] at h'
    fl4 := fun b j h => by rw [hc, hv _ hfln]; exact hI.fl4 b j h
    fl5 := fun val j h => by rw [hc, hv _ hfln]; exact hI.fl5 val j h }

lemma inv_retW {s : St K} (hI : Inv v₀ s) {v : Fin K} (hs : s.wpc = .done v) :
    Inv v₀ { s with last := v, wpc := .idle } := by
  have hn1 := hI.pend_n (by simp [hs])
  have hnA : St.nA { s with last := v, wpc := .idle } = s.nA := by
    simp [St.nA, hs, WPC.preA, St.n]
  have hc : St.c { s with last := v, wpc := .idle } = s.n := by simp [St.c, St.n]
  have hc0 : s.c + 1 = s.n := hI.pend_c (by simp [hs])
  have hnA0 : s.nA = s.n := hI.postA_nA (by simp [hs, WPC.postA])
  have hvn := (hI.pendv v (by simp [hs, WPC.val?])).1
  have hcov : ∀ x, s.Bm x = true → s.rpc.cov x := fun x hx =>
    (hI.bprot x hx).resolve_right (by simp [hs, WPC.win, WPC.win'])
  have hfl := hI.fl1
  exact { hI with
    wf := trivial
    pendv := fun v' h => by simp [WPC.val?] at h
    lastv := by rw [hc]; exact hvn
    memA := fun x => by
      dsimp only; rw [hI.memA x]; simp [hs, WPC.newv, WPC.old, eq_comm]
    tagA := fun x hx => by
      dsimp only at hx ⊢; rw [hI.tagA x hx, hc]
      have := (hI.memA x).1 hx; simp [hs, WPC.newv, WPC.old] at this; simp [hs, WPC.newv, this]
    scan := fun v' j h => by simp at h
    scan' := fun v' h => by simp at h
    bprot := fun x hx => Or.inl (hcov x hx)
    lo := fun hr => by dsimp only; rw [hc]; have := hI.lo hr; omega
    h1 := fun ha hlt => by
      rw [hnA] at hlt
      obtain ⟨x, hx1, -, -, hx4⟩ := hI.h1 ha hlt
      exact ⟨x, hx1, by simp [WPC.noWin], fun v' j h => by simp at h, hx4⟩
    h2 := fun ha hlt => ⟨fun v h => by simp at h, fun v h => by simp at h,
      fun v h => by simp at h⟩
    h3 := fun b j h e => by rw [hnA] at e ⊢; exact hI.h3 b j h e
    h4 := fun j h => by rw [hnA]; exact hI.h4 j h
    h4' := fun j h => by rw [hnA]; exact hI.h4' j h
    h4'' := fun j h => by rw [hnA]; exact hI.h4'' j h
    rf := fun v' h => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v' h
      refine ⟨a1, by rw [hnA]; exact a2, a3, a4, Or.inl ?_⟩
      dsimp only; rw [hc]; omega
    fl1 := by rw [hnA]; exact hI.fl1
    fl3 := Or.inl (by dsimp only; rw [hc]; omega)
    fl4 := fun b j h => Or.inl (by dsimp only; rw [hc]; omega)
    fl5 := fun val j h => Or.inl (by dsimp only; rw [hc]; omega) }

lemma inv_invR {s : St K} (hI : Inv v₀ s) (hs : s.rpc = .idle) :
    Inv v₀ { s with rpc := .start, lo := s.c } := by
  exact { hI with
    f1 := by simp [hI.f1, hs, RPC.f1v]
    f2 := by simp [hI.f2, hs, RPC.f2v]
    bprot := fun x hx => by
      rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
      · simp [hs, RPC.cov] at h
      · exact Or.inr ⟨h1, h2, Or.inl h3⟩
      · exact Or.inr ⟨h1, h2, Or.inr ⟨h3, by simp [RPC.s1]⟩⟩
    b11 := fun _ x hx => by
      show s.c < s.tagB x
      rcases hI.bprot x hx with h | ⟨h1, h2, h3⟩
      · simp [hs, RPC.cov] at h
      · have hw : s.wpc ≠ .idle := by
          intro hw; rcases h3 with h3 | ⟨h3, -⟩ <;> simp [hw, WPC.win, WPC.win'] at h3
        have := hI.pend_c hw; omega
    lo := fun _ => le_rfl
    h1 := fun h => by simp [RPC.active] at h
    h2 := fun h => by simp [RPC.active] at h
    h3 := fun b j h => by simp at h
    h4 := fun j h => by simp at h
    h4' := fun j h => by simp at h
    h4'' := fun j h => by simp at h
    l10 := fun h => by simp [RPC.late] at h
    rwf := fun val j h => by simp at h
    rf := fun v h => by simp [RPC.val?] at h
    rfB := fun j val h => by simp at h
    rfB' := fun h => by simp [RPC.fin] at h
    fl4 := fun b j h => by simp at h
    fl5 := fun val j h => by simp at h }

lemma inv_retR {s : St K} (hI : Inv v₀ s) {val : Option (Fin K)} (hs : s.rpc = .done val) :
    Inv v₀ { s with rpc := .idle, pis := s.pis ++ [s.rf], fl := s.rf } := by
  have hl := hI.l10 (by simp [hs, RPC.late])
  simp only [hs, RPC.val?] at hl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
  obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v (by simp [hs, RPC.val?, hv])
  exact { hI with
    f1 := by simp [hI.f1, hs, RPC.f1v]
    f2 := by simp [hI.f2, hs, RPC.f2v]
    bprot := fun x hx => by
      rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
      · simp [hs, RPC.cov] at h
      · exact Or.inr ⟨h1, h2, Or.inl h3⟩
      · exact Or.inr ⟨h1, h2, Or.inr ⟨h3, by simp [RPC.s1]⟩⟩
    b11 := fun h => absurd rfl h
    lo := fun h => absurd rfl h
    h1 := fun h => by simp [RPC.active] at h
    h2 := fun h => by simp [RPC.active] at h
    h3 := fun b j h => by simp at h
    h4 := fun j h => by simp at h
    h4' := fun j h => by simp at h
    h4'' := fun j h => by simp at h
    l10 := fun h => by simp [RPC.late] at h
    rwf := fun val j h => by simp at h
    rf := fun v h => by simp [RPC.val?] at h
    rfB := fun j val h => by simp at h
    rfB' := fun h => by simp [RPC.fin] at h
    fl1 := a2
    fl2 := hI.rfB' (by simp [hs, RPC.fin])
    fl3 := by
      rcases a5 with h | ⟨h1, h2, h3⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, h2, fun x hx hA => h3 x ?_ (by simp [hs, RPC.dlow]) hA⟩
        rw [a1]; exact hx
    fl4 := fun b j h => by simp at h
    fl5 := fun val j h => by simp at h
    pis1 := fun p hp => by
      dsimp only at hp ⊢
      rcases List.mem_append.1 hp with hp | hp
      · exact (hI.pis1 p hp).trans a4
      · simp at hp; omega
    pis2 := by
      rw [List.pairwise_append]
      refine ⟨hI.pis2, by simp, fun a ha b hb => ?_⟩
      simp at hb; subst hb; exact (hI.pis1 a ha).trans a4 }

end Alg4

end Cslib.SharedMemory
