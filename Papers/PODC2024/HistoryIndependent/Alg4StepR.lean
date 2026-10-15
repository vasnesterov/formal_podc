import Papers.PODC2024.HistoryIndependent.Alg4Inv

/-!
# Algorithm 4: the invariant is preserved by the reader's steps
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Alg4

variable {K : ℕ} [NeZero K] {v₀ : Fin K}

lemma inv_stepR_start {s : St K} (hI : Inv v₀ s) (hs : s.rpc = .start) :
    Inv v₀ { s with f1 := true, rpc := .up false 0, sN1 := s.n, sT := s.nA } := by
  exact { hI with
    f1 := rfl
    f2 := by simp [hI.f2, hs, RPC.f2v]
    bprot := fun x hx => Or.inl trivial
    b11 := fun _ => hI.b11 (by simp [hs])
    lo := fun _ => hI.lo (by simp [hs])
    h1 := fun _ h => absurd h (by simp; exact s.nA_le_n)
    h2 := fun _ h => absurd h (lt_irrefl _)
    h3 := fun b j h _ => by simp at h; rw [← h.2]; exact Fin.zero_le _
    h4 := fun j _ => ⟨by have := s.n_le_c; have := s.c_le_nA; simp; omega, le_rfl⟩
    h4' := fun j h => by simp at h
    h4'' := fun j h => by simp at h
    l10 := fun h => by simp [RPC.late] at h
    rf := fun v h => by simp [RPC.val?] at h
    rfB := fun j val h => by simp at h
    rfB' := fun h => by simp [RPC.fin] at h
    fl4 := fun b j h => by simp at h; rw [← h.2]; exact Or.inr (Fin.zero_le _)
    fl5 := fun val j h => by simp at h
    rwf := fun val j h => by simp at h }

lemma inv_stepR_up_one {s : St K} (hI : Inv v₀ s) {b : Bool} {j : Fin K}
    (hs : s.rpc = .up b j) (hA : s.A j = true) :
    Inv v₀ { s with rpc := RPC.found j, rf := s.tagA j } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hact : s.rpc.active := by simp [hs, RPC.active]
  obtain ⟨e1, e2, e3, e4, e5⟩ := hI.rf_A hA (hI.fl4 b j hs) hr
  rcases RPC.found_spec j with ⟨hj, hf⟩ | ⟨hj1, hj, hf⟩
  · exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun h => by simp [hf, RPC.active] at h
      h2 := fun h => by simp [hf, RPC.active] at h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun _ => by simp [hf, RPC.val?]
      rwf := fun val j h => by simp [hf] at h
      rf := fun v h => by
        simp [hf, RPC.val?] at h; subst h
        refine ⟨e1, e2, e3, e4, e5.imp_right fun h => ⟨h.1, h.2, fun x hx => ?_⟩⟩
        exact absurd hx (by simp [Fin.lt_def, hj])
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val j h => by simp [hf] at h }
  · exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun _ h => by
        obtain ⟨x, hx1, hx2, hx3, -⟩ := hI.h1 hact h
        exact ⟨x, hx1, hx2, hx3, fun j h => by simp [hf] at h⟩
      h2 := fun _ h => hI.h2 hact h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun h => by simp [hf, RPC.late] at h
      rwf := fun val j' h => by
        simp [hf] at h; obtain ⟨rfl, rfl⟩ := h; rw [Fin.lt_def]; simp only; omega
      rf := fun v h => by
        simp [hf, RPC.val?] at h; subst h
        refine ⟨e1, e2, e3, e4, e5.imp_right fun h => ⟨h.1, h.2, fun x hx hd => ?_⟩⟩
        simp only [hf, RPC.dlow] at hd
        have h1 := Fin.lt_def.1 hd; have h2 := Fin.lt_def.1 hx
        simp only at h1; omega
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val j' h => by
        simp [hf] at h; obtain ⟨rfl, rfl⟩ := h; exact hI.fl4 b _ hs }

lemma Inv.lt_of_zero_one {s : St K} {j j' : Fin K} (hA : s.A j = false) (hle : j ≤ j')
    (h1 : s.A j' = true) : j.val + 1 ≤ j'.val := by
  rcases lt_or_eq_of_le hle with h | rfl
  · exact Fin.lt_def.1 h
  · simp [hA] at h1

lemma Inv.nA_ne_sT {s : St K} (hI : Inv v₀ s) {b : Bool} {j : Fin K}
    (hs : s.rpc = .up b j) (hA : s.A j = false) (hK : ¬ j.val + 1 < K) : s.nA ≠ s.sT := by
  intro e
  have h1 := Inv.lt_of_zero_one hA (hI.h3 b j hs e) hI.A_cur
  have := (s.vals v₀ s.nA).isLt
  omega

lemma inv_stepR_up_zero_next {s : St K} (hI : Inv v₀ s) {b : Bool} {j : Fin K}
    (hs : s.rpc = .up b j) (hA : s.A j = false) (hK : j.val + 1 < K) :
    Inv v₀ { s with rpc := .up b ⟨j.val + 1, hK⟩ } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hact : s.rpc.active := by simp [hs, RPC.active]
  exact { hI with
    f1 := by simp [hI.f1, hs, RPC.f1v]
    f2 := by simp [hI.f2, hs, RPC.f2v]
    bprot := fun x _ => Or.inl (by simp [RPC.cov])
    b11 := fun _ => hI.b11 hr
    lo := fun _ => hI.lo hr
    h1 := fun _ h => by
      obtain ⟨x, hx1, hx2, hx3, -⟩ := hI.h1 hact h
      exact ⟨x, hx1, hx2, hx3, fun j h => by simp at h⟩
    h2 := fun _ h => hI.h2 hact h
    h3 := fun b' j' h e => by
      simp at h; obtain ⟨rfl, rfl⟩ := h
      have := Inv.lt_of_zero_one hA (hI.h3 b j hs e) hI.A_cur
      rw [Fin.le_def]; exact this
    h4 := fun j' h => hI.h4 j (by simp at h; rw [hs, h.1])
    h4' := fun j' h => hI.h4' j (by simp at h; rw [hs, h.1])
    h4'' := fun j h => by simp at h
    l10 := fun h => by simp [RPC.late] at h
    rwf := fun val j h => by simp at h
    rf := fun v h => by simp [RPC.val?] at h
    rfB := fun j val h => by simp at h
    rfB' := fun h => by simp [RPC.fin] at h
    fl4 := fun b' j' h => by
      simp at h; obtain ⟨rfl, rfl⟩ := h
      rcases hI.fl4 b j hs with h | h
      · exact Or.inl h
      rcases hI.fl3 with h' | ⟨hn, hp, -⟩
      · exact Or.inl h'
      right
      have hc : s.A (s.vals v₀ s.fl) = true := by
        rw [← hn, ← hI.postA_nA hp]; exact hI.A_cur
      rw [Fin.le_def]; exact Inv.lt_of_zero_one hA h hc
    fl5 := fun val j h => by simp at h }

lemma inv_stepR_up_zero_snd {s : St K} (hI : Inv v₀ s) {j : Fin K}
    (hs : s.rpc = .up true j) (hA : s.A j = false) (hK : ¬ j.val + 1 < K) :
    Inv v₀ { s with rpc := .bscan 0 none } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hact : s.rpc.active := by simp [hs, RPC.active]
  have hlt : s.sN1 < s.nA := by
    have := hI.nA_ne_sT hs hA hK
    have := hI.h4' j hs
    omega
  exact { hI with
    f1 := by simp [hI.f1, hs, RPC.f1v]
    f2 := by simp [hI.f2, hs, RPC.f2v]
    bprot := fun x _ => Or.inl (by simp [RPC.cov])
    b11 := fun _ => hI.b11 hr
    lo := fun _ => hI.lo hr
    h1 := fun _ h => by
      obtain ⟨x, hx1, hx2, hx3, -⟩ := hI.h1 hact h
      exact ⟨x, hx1, hx2, hx3, fun j h => by simp at h; rw [← h]; exact Fin.zero_le _⟩
    h2 := fun _ h => hI.h2 hact h
    h3 := fun b' j' h e => by simp at h
    h4 := fun j' h => by simp at h
    h4' := fun j' h => by simp at h
    h4'' := fun _ _ => hlt
    l10 := fun h => by simp [RPC.late] at h
    rwf := fun val j h => by simp at h
    rf := fun v h => by simp [RPC.val?] at h
    rfB := fun j val h => by simp at h
    rfB' := fun h => by simp [RPC.fin] at h
    fl4 := fun b' j' h => by simp at h
    fl5 := fun val j h => by simp at h }

lemma inv_stepR_up_zero_fst {s : St K} (hI : Inv v₀ s) {j : Fin K}
    (hs : s.rpc = .up false j) (hA : s.A j = false) (hK : ¬ j.val + 1 < K) :
    Inv v₀ { s with rpc := .up true 0, sT := s.nA } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hact : s.rpc.active := by simp [hs, RPC.active]
  exact { hI with
    f1 := by simp [hI.f1, hs, RPC.f1v]
    f2 := by simp [hI.f2, hs, RPC.f2v]
    bprot := fun x _ => Or.inl (by simp [RPC.cov])
    b11 := fun _ => hI.b11 hr
    lo := fun _ => hI.lo hr
    h1 := fun _ h => by
      obtain ⟨x, hx1, hx2, hx3, -⟩ := hI.h1 hact h
      exact ⟨x, hx1, hx2, hx3, fun j h => by simp at h⟩
    h2 := fun _ h => hI.h2 hact h
    h3 := fun b' j' h e => by simp at h; rw [← h.2]; exact Fin.zero_le _
    h4 := fun j' h => by simp at h
    h4' := fun j' h => by
      have := hI.nA_ne_sT hs hA hK
      have := hI.h4 j hs
      exact ⟨by simp only; omega, le_rfl⟩
    h4'' := fun j h => by simp at h
    l10 := fun h => by simp [RPC.late] at h
    rwf := fun val j h => by simp at h
    rf := fun v h => by simp [RPC.val?] at h
    rfB := fun j val h => by simp at h
    rfB' := fun h => by simp [RPC.fin] at h
    fl4 := fun b' j' h => by simp at h; rw [← h.2]; exact Or.inr (Fin.zero_le _)
    fl5 := fun val j h => by simp at h }

lemma inv_stepR_down_one {s : St K} (hI : Inv v₀ s) {val j : Fin K}
    (hs : s.rpc = .down val j) (hA : s.A j = true) :
    Inv v₀ { s with rpc := RPC.downNext val j true, rf := s.tagA j } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hact : s.rpc.active := by simp [hs, RPC.active]
  have hjv := hI.rwf val j hs
  have hfl : s.fl ≤ s.c ∨ j ≤ s.vals v₀ s.fl :=
    (hI.fl5 val j hs).imp_right fun h => (le_of_lt hjv).trans h
  obtain ⟨e1, e2, e3, e4, e5⟩ := hI.rf_A hA hfl hr
  rcases RPC.downNext_spec val j true with ⟨hj, hf⟩ | ⟨hj1, hj, hf⟩
  · simp only [ite_true] at hf
    exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun h => by simp [hf, RPC.active] at h
      h2 := fun h => by simp [hf, RPC.active] at h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun _ => by simp [hf, RPC.val?]
      rwf := fun val j h => by simp [hf] at h
      rf := fun v h => by
        simp [hf, RPC.val?] at h; subst h
        refine ⟨e1, e2, e3, e4, e5.imp_right fun h => ⟨h.1, h.2, fun x hx => ?_⟩⟩
        exact absurd hx (by simp [Fin.lt_def, hj])
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val j h => by simp [hf] at h }
  · simp only [ite_true] at hf
    exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun _ h => by
        obtain ⟨x, hx1, hx2, hx3, -⟩ := hI.h1 hact h
        exact ⟨x, hx1, hx2, hx3, fun j h => by simp [hf] at h⟩
      h2 := fun _ h => hI.h2 hact h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun h => by simp [hf, RPC.late] at h
      rwf := fun val j' h => by
        simp [hf] at h; obtain ⟨rfl, rfl⟩ := h; rw [Fin.lt_def]; simp only; omega
      rf := fun v h => by
        simp [hf, RPC.val?] at h; subst h
        refine ⟨e1, e2, e3, e4, e5.imp_right fun h => ⟨h.1, h.2, fun x hx hd => ?_⟩⟩
        simp only [hf, RPC.dlow] at hd
        have h1 := Fin.lt_def.1 hd; have h2 := Fin.lt_def.1 hx
        simp only at h1; omega
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val' j' h => by
        simp [hf] at h; obtain ⟨rfl, rfl⟩ := h; exact hfl }

lemma inv_stepR_down_zero {s : St K} (hI : Inv v₀ s) {val j : Fin K}
    (hs : s.rpc = .down val j) (hA : s.A j = false) :
    Inv v₀ { s with rpc := RPC.downNext val j false } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hact : s.rpc.active := by simp [hs, RPC.active]
  have hjv := hI.rwf val j hs
  obtain ⟨e1, e2, e3, e4, e5⟩ := hI.rf val (by simp [hs, RPC.val?])
  rcases RPC.downNext_spec val j false with ⟨hj, hf⟩ | ⟨hj1, hj, hf⟩
  · simp only [Bool.false_eq_true, ite_false] at hf
    exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun h => by simp [hf, RPC.active] at h
      h2 := fun h => by simp [hf, RPC.active] at h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun _ => by simp [hf, RPC.val?]
      rwf := fun val j h => by simp [hf] at h
      rf := fun v h => by
        simp [hf, RPC.val?] at h; subst h
        refine ⟨e1, e2, e3, e4, e5.imp_right fun h => ⟨h.1, h.2.1, fun x hx _ hAx => ?_⟩⟩
        refine h.2.2 x hx ?_ hAx
        simp only [hs, RPC.dlow]
        rcases lt_or_eq_of_le (Fin.zero_le x) with h' | h'
        · rw [Fin.lt_def] at h' ⊢; simp at h'; omega
        · rw [← h'] at hAx; rw [show j = 0 from Fin.ext hj] at hA; simp [hA] at hAx
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val j h => by simp [hf] at h }
  · simp only [Bool.false_eq_true, ite_false] at hf
    exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun _ h => by
        obtain ⟨x, hx1, hx2, hx3, -⟩ := hI.h1 hact h
        exact ⟨x, hx1, hx2, hx3, fun j h => by simp [hf] at h⟩
      h2 := fun _ h => hI.h2 hact h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun h => by simp [hf, RPC.late] at h
      rwf := fun val' j' h => by
        simp [hf] at h; obtain ⟨rfl, rfl⟩ := h
        rw [Fin.lt_def] at hjv ⊢; simp only; omega
      rf := fun v h => by
        simp [hf, RPC.val?] at h; subst h
        refine ⟨e1, e2, e3, e4, e5.imp_right fun h => ⟨h.1, h.2.1, fun x hx hd hAx => ?_⟩⟩
        refine h.2.2 x hx ?_ hAx
        simp only [hf, RPC.dlow] at hd
        simp only [hs, RPC.dlow]
        rcases eq_or_ne x j with rfl | hne
        · simp [hA] at hAx
        · rw [Fin.lt_def] at hd ⊢; simp only at hd
          have : x.val ≠ j.val := fun h => hne (Fin.ext h)
          omega
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val' j' h => by
        simp [hf] at h; obtain ⟨rfl, rfl⟩ := h; exact hI.fl5 _ _ hs }

lemma inv_stepR_bscan_one {s : St K} (hI : Inv v₀ s) {j : Fin K} {val : Option (Fin K)}
    (hs : s.rpc = .bscan j val) (hB : s.Bm j = true) :
    Inv v₀ { s with rpc := RPC.bscanNext j val true, rf := s.tagB j - 1 } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hact : s.rpc.active := by simp [hs, RPC.active]
  obtain ⟨b1, b2, b3⟩ := hI.bval j hB
  have hlo := hI.b11 hr j hB
  have hfl := hI.fl2 j hB
  have hnA := s.nA_le_n; have hnc := s.n_le_c; have hcA := s.c_le_nA
  have key : j = s.vals v₀ (s.tagB j - 1) ∧ s.tagB j - 1 ≤ s.nA ∧ s.lo ≤ s.tagB j - 1 ∧
      s.fl ≤ s.tagB j - 1 ∧ s.tagB j - 1 ≤ s.c := ⟨b3, by omega, by omega, by omega, by omega⟩
  rcases RPC.bscanNext_spec j val true with ⟨hj, hf⟩ | ⟨hj1, hf⟩
  · simp only [ite_true] at hf
    exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun h => by simp [hf, RPC.active] at h
      h2 := fun h => by simp [hf, RPC.active] at h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun _ => by simp [hf, RPC.val?]
      rwf := fun val j h => by simp [hf] at h
      rf := fun v h => by
        simp [hf, RPC.val?] at h; subst h
        exact ⟨key.1, key.2.1, key.2.2.1, key.2.2.2.1, Or.inl key.2.2.2.2⟩
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val j h => by simp [hf] at h }
  · simp only [ite_true] at hf
    exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun _ h => by
        obtain ⟨x, hx1, hx2, hx3, -⟩ := hI.h1 hact h
        exact ⟨x, hx1, hx2, hx3, fun j h => by simp [hf] at h⟩
      h2 := fun _ h => hI.h2 hact h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun h => by simp [hf, RPC.late] at h
      rwf := fun val j' h => by simp [hf] at h
      rf := fun v h => by
        simp [hf, RPC.val?] at h; subst h
        exact ⟨key.1, key.2.1, key.2.2.1, key.2.2.2.1, Or.inl key.2.2.2.2⟩
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val' j' h => by simp [hf] at h }

lemma inv_stepR_bscan_zero {s : St K} (hI : Inv v₀ s) {j : Fin K} {val : Option (Fin K)}
    (hs : s.rpc = .bscan j val) (hB : s.Bm j = false) :
    Inv v₀ { s with rpc := RPC.bscanNext j val false } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hact : s.rpc.active := by simp [hs, RPC.active]
  -- if `val = none`, the `1` in `B` is still ahead
  have hnone : val = none → s.sN1 < s.nA ∧ ∃ x, s.Bm x = true ∧ s.wpc.noWin ∧
      (∀ v j, s.wpc = .scanB v j → j ≤ x) ∧ j.val + 1 ≤ x.val := by
    intro hv; subst hv
    have h4 := hI.h4'' j hs
    obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hI.h1 hact h4
    have := hx4 j hs
    refine ⟨h4, x, hx1, hx2, hx3, ?_⟩
    rcases lt_or_eq_of_le this with h | rfl
    · exact Fin.lt_def.1 h
    · simp [hB] at hx1
  rcases RPC.bscanNext_spec j val false with ⟨hj, hf⟩ | ⟨hj1, hf⟩
  · simp only [Bool.false_eq_true, ite_false] at hf
    have hval : val.isSome := by
      cases val with
      | some _ => rfl
      | none => obtain ⟨-, x, -, -, -, hx⟩ := hnone rfl; have := x.isLt; omega
    exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun h => by simp [hf, RPC.active] at h
      h2 := fun h => by simp [hf, RPC.active] at h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun _ => by simpa [hf, RPC.val?] using hval
      rwf := fun val j h => by simp [hf] at h
      rf := fun v h => by
        simp [hf, RPC.val?] at h
        obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v (by simp [hs, RPC.val?, h])
        exact ⟨a1, a2, a3, a4, a5.imp_right fun h' =>
          ⟨h'.1, h'.2.1, fun x hx _ => h'.2.2 x hx (by simp [hs, RPC.dlow])⟩⟩
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val j h => by simp [hf] at h }
  · simp only [Bool.false_eq_true, ite_false] at hf
    exact { hI with
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x _ => Or.inl (by simp [hf, RPC.cov])
      b11 := fun _ => hI.b11 hr
      lo := fun _ => hI.lo hr
      h1 := fun _ h => by
        cases val with
        | none =>
          obtain ⟨-, x, hx1, hx2, hx3, hx4⟩ := hnone rfl
          refine ⟨x, hx1, hx2, hx3, fun j' h' => ?_⟩
          simp [hf] at h'; rw [← h', Fin.le_def]; exact hx4
        | some v =>
          obtain ⟨x, hx1, hx2, hx3, -⟩ := hI.h1 hact h
          exact ⟨x, hx1, hx2, hx3, fun j h => by simp [hf] at h⟩
      h2 := fun _ h => hI.h2 hact h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j' h => by
        simp [hf] at h; exact (hnone h.2).1
      l10 := fun h => by simp [hf, RPC.late] at h
      rwf := fun val j' h => by simp [hf] at h
      rf := fun v h => by
        simp [hf, RPC.val?] at h
        obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v (by simp [hs, RPC.val?, h])
        exact ⟨a1, a2, a3, a4, a5.imp_right fun h' =>
          ⟨h'.1, h'.2.1, fun x hx _ => h'.2.2 x hx (by simp [hs, RPC.dlow])⟩⟩
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val' j' h => by simp [hf] at h }

lemma inv_stepR_setF2 {s : St K} (hI : Inv v₀ s) {val : Option (Fin K)}
    (hs : s.rpc = .setF2 val) : Inv v₀ { s with f2 := true, rpc := .clr 0 val } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  exact { hI with
    f1 := by simp [hI.f1, hs, RPC.f1v]
    f2 := by simp [RPC.f2v]
    bprot := fun x _ => Or.inl (by simp [RPC.cov])
    b11 := fun _ => hI.b11 hr
    lo := fun _ => hI.lo hr
    h1 := fun h => by simp [RPC.active] at h
    h2 := fun h => by simp [RPC.active] at h
    h3 := fun b j h => by simp at h
    h4 := fun j h => by simp at h
    h4' := fun j h => by simp at h
    h4'' := fun j h => by simp at h
    l10 := fun _ => by simpa [hs, RPC.val?, RPC.late] using hI.l10 (by simp [hs, RPC.late])
    rwf := fun val j h => by simp at h
    rf := fun v h => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v (by simpa [hs, RPC.val?] using h)
      exact ⟨a1, a2, a3, a4, a5.imp_right fun h' =>
        ⟨h'.1, h'.2.1, fun x hx _ => h'.2.2 x hx (by simp [hs, RPC.dlow])⟩⟩
    rfB := fun j val h x hx => by
      simp at h; rw [← h.1] at hx; exact absurd hx (by simp)
    rfB' := fun h => by simp [RPC.fin] at h
    fl4 := fun b j h => by simp at h
    fl5 := fun val j h => by simp at h }

lemma inv_stepR_clr {s : St K} (hI : Inv v₀ s) {j : Fin K} {val : Option (Fin K)}
    (hs : s.rpc = .clr j val) :
    Inv v₀ { s with Bm := Function.update s.Bm j false, rpc := RPC.clrNext j val } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  have hB : ∀ x, Function.update s.Bm j false x = true → x ≠ j ∧ s.Bm x = true := by
    intro x hx
    by_cases h : x = j
    · subst h; simp at hx
    · simp [Function.update_of_ne h] at hx; exact ⟨h, hx⟩
  have hB0 : ∀ x, s.Bm x = false → Function.update s.Bm j false x = false := by
    intro x hx; by_cases h : x = j
    · subst h; simp
    · simp [Function.update_of_ne h, hx]
  -- an index `x ≠ j` with `j ≤ x` is beyond the next index
  have hlt : ∀ x, x ≠ j → j ≤ x → j.val + 1 ≤ x.val := by
    intro x hne hle
    rcases lt_or_eq_of_le hle with h | rfl
    · exact Fin.lt_def.1 h
    · exact absurd rfl hne
  rcases RPC.clrNext_spec j val with ⟨hj, hf⟩ | ⟨hj1, hf⟩
  · exact { hI with
      scan := fun v j' h x hx => hB0 x (hI.scan v j' h x hx)
      scan' := fun v h x => hB0 x (hI.scan' v h x)
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x hx => by
        obtain ⟨hne, hx⟩ := hB x hx
        rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · simp [hs, RPC.cov] at h; have := hlt x hne h; have := x.isLt; omega
        · exact Or.inr ⟨h1, h2, Or.inl h3⟩
        · simp [hs, RPC.s1] at h4; have := hlt x hne h4; have := x.isLt; omega
      bval := fun x hx => hI.bval x (hB x hx).2
      b11 := fun _ x hx => hI.b11 hr x (hB x hx).2
      lo := fun _ => hI.lo hr
      h1 := fun h => by simp [hf, RPC.active] at h
      h2 := fun h => by simp [hf, RPC.active] at h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun _ => by simpa [hs, hf, RPC.val?, RPC.late] using hI.l10 (by simp [hs, RPC.late])
      rwf := fun val j h => by simp [hf] at h
      rf := fun v h => by
        obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v (by simpa [hs, hf, RPC.val?] using h)
        exact ⟨a1, a2, a3, a4, a5.imp_right fun h' =>
          ⟨h'.1, h'.2.1, fun x hx _ => h'.2.2 x hx (by simp [hs, RPC.dlow])⟩⟩
      rfB := fun j val h => by simp [hf] at h
      rfB' := fun _ x hx => by
        obtain ⟨hne, hx⟩ := hB x hx
        refine hI.rfB j val hs x ?_ hx
        rw [Fin.lt_def]; have := x.isLt
        have : x.val ≠ j.val := fun h => hne (Fin.ext h)
        omega
      fl2 := fun x hx => hI.fl2 x (hB x hx).2
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val j h => by simp [hf] at h }
  · exact { hI with
      scan := fun v j' h x hx => hB0 x (hI.scan v j' h x hx)
      scan' := fun v h x => hB0 x (hI.scan' v h x)
      f1 := by simp [hf, hI.f1, hs, RPC.f1v]
      f2 := by simp [hf, hI.f2, hs, RPC.f2v]
      bprot := fun x hx => by
        obtain ⟨hne, hx⟩ := hB x hx
        rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · simp [hs, RPC.cov] at h; left; simp [hf, RPC.cov, Fin.le_def]; exact hlt x hne h
        · exact Or.inr ⟨h1, h2, Or.inl h3⟩
        · simp [hs, RPC.s1] at h4
          exact Or.inr ⟨h1, h2, Or.inr ⟨h3, by simp [hf, RPC.s1, Fin.le_def]; exact hlt x hne h4⟩⟩
      bval := fun x hx => hI.bval x (hB x hx).2
      b11 := fun _ x hx => hI.b11 hr x (hB x hx).2
      lo := fun _ => hI.lo hr
      h1 := fun h => by simp [hf, RPC.active] at h
      h2 := fun h => by simp [hf, RPC.active] at h
      h3 := fun b j h => by simp [hf] at h
      h4 := fun j h => by simp [hf] at h
      h4' := fun j h => by simp [hf] at h
      h4'' := fun j h => by simp [hf] at h
      l10 := fun _ => by simpa [hs, hf, RPC.val?, RPC.late] using hI.l10 (by simp [hs, RPC.late])
      rwf := fun val j h => by simp [hf] at h
      rf := fun v h => by
        obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v (by simpa [hs, hf, RPC.val?] using h)
        exact ⟨a1, a2, a3, a4, a5.imp_right fun h' =>
          ⟨h'.1, h'.2.1, fun x hx _ => h'.2.2 x hx (by simp [hs, RPC.dlow])⟩⟩
      rfB := fun j' val' h x hx hBx => by
        simp [hf] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hne, hBx⟩ := hB x hBx
        refine hI.rfB j val hs x ?_ hBx
        rw [Fin.lt_def] at hx ⊢; simp only at hx
        have : x.val ≠ j.val := fun h => hne (Fin.ext h)
        omega
      rfB' := fun h => by simp [hf, RPC.fin] at h
      fl2 := fun x hx => hI.fl2 x (hB x hx).2
      fl4 := fun b j h => by simp [hf] at h
      fl5 := fun val j h => by simp [hf] at h }

lemma inv_stepR_resF1 {s : St K} (hI : Inv v₀ s) {val : Option (Fin K)}
    (hs : s.rpc = .resF1 val) : Inv v₀ { s with f1 := false, rpc := .resF2 val } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  exact { hI with
    f1 := by simp [RPC.f1v]
    f2 := by simp [hI.f2, hs, RPC.f2v]
    bprot := fun x hx => by
      rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
      · simp [hs, RPC.cov] at h
      · exact Or.inr ⟨h1, h2, Or.inl h3⟩
      · simp [hs, RPC.s1] at h4
    b11 := fun _ => hI.b11 hr
    lo := fun _ => hI.lo hr
    h1 := fun h => by simp [RPC.active] at h
    h2 := fun h => by simp [RPC.active] at h
    h3 := fun b j h => by simp at h
    h4 := fun j h => by simp at h
    h4' := fun j h => by simp at h
    h4'' := fun j h => by simp at h
    l10 := fun _ => by simpa [hs, RPC.val?, RPC.late] using hI.l10 (by simp [hs, RPC.late])
    rwf := fun val j h => by simp at h
    rf := fun v h => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v (by simpa [hs, RPC.val?] using h)
      exact ⟨a1, a2, a3, a4, a5.imp_right fun h' =>
        ⟨h'.1, h'.2.1, fun x hx _ => h'.2.2 x hx (by simp [hs, RPC.dlow])⟩⟩
    rfB := fun j val h => by simp at h
    rfB' := fun _ => hI.rfB' (by simp [hs, RPC.fin])
    fl4 := fun b j h => by simp at h
    fl5 := fun val j h => by simp at h }

lemma inv_stepR_resF2 {s : St K} (hI : Inv v₀ s) {val : Option (Fin K)}
    (hs : s.rpc = .resF2 val) : Inv v₀ { s with f2 := false, rpc := .done val } := by
  have hr : s.rpc ≠ .idle := by simp [hs]
  exact { hI with
    f1 := by simp [hI.f1, hs, RPC.f1v]
    f2 := by simp [RPC.f2v]
    bprot := fun x hx => by
      rcases hI.bprot x hx with h | ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
      · simp [hs, RPC.cov] at h
      · exact Or.inr ⟨h1, h2, Or.inl h3⟩
      · simp [hs, RPC.s1] at h4
    b11 := fun _ => hI.b11 hr
    lo := fun _ => hI.lo hr
    h1 := fun h => by simp [RPC.active] at h
    h2 := fun h => by simp [RPC.active] at h
    h3 := fun b j h => by simp at h
    h4 := fun j h => by simp at h
    h4' := fun j h => by simp at h
    h4'' := fun j h => by simp at h
    l10 := fun _ => by simpa [hs, RPC.val?, RPC.late] using hI.l10 (by simp [hs, RPC.late])
    rwf := fun val j h => by simp at h
    rf := fun v h => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hI.rf v (by simpa [hs, RPC.val?] using h)
      exact ⟨a1, a2, a3, a4, a5.imp_right fun h' =>
        ⟨h'.1, h'.2.1, fun x hx _ => h'.2.2 x hx (by simp [hs, RPC.dlow])⟩⟩
    rfB := fun j val h => by simp at h
    rfB' := fun _ => hI.rfB' (by simp [hs, RPC.fin])
    fl4 := fun b j h => by simp at h
    fl5 := fun val j h => by simp at h }

/-- The invariant is preserved by the reader's internal steps. -/
lemma inv_stepR {s : St K} (hI : Inv v₀ s) (h1 : s.rpc ≠ .idle) (h2 : ∀ val, s.rpc ≠ .done val) :
    Inv v₀ (stepR s) := by
  cases hs : s.rpc with
  | idle => exact absurd hs h1
  | done val => exact absurd hs (h2 val)
  | start => simp only [stepR, hs]; exact inv_stepR_start hI hs
  | up b j =>
    simp only [stepR, hs]
    cases hA : s.A j
    · by_cases hK : j.val + 1 < K
      · simp only [Bool.false_eq_true, ite_false, hK, not_true_eq_false, and_false,
          RPC.upNext, dite_true]
        exact inv_stepR_up_zero_next hI hs hA hK
      · cases b
        · simp only [Bool.false_eq_true, ite_false, hK, not_false_eq_true, and_self,
            ite_true, RPC.upNext, dite_false]
          exact inv_stepR_up_zero_fst hI hs hA hK
        · simp only [Bool.false_eq_true, ite_false, hK, not_false_eq_true, and_true,
            Bool.true_eq_false, and_false, ite_true, RPC.upNext, dite_false]
          exact inv_stepR_up_zero_snd hI hs hA hK
    · simp only [ite_true, Bool.true_eq_false, false_and, ite_false]
      exact inv_stepR_up_one hI hs hA
  | down val j =>
    simp only [stepR, hs]
    cases hA : s.A j
    · simp only [Bool.false_eq_true, ite_false]; exact inv_stepR_down_zero hI hs hA
    · simp only [ite_true]; exact inv_stepR_down_one hI hs hA
  | bscan j val =>
    simp only [stepR, hs]
    cases hB : s.Bm j
    · simp only [Bool.false_eq_true, ite_false]; exact inv_stepR_bscan_zero hI hs hB
    · simp only [ite_true]; exact inv_stepR_bscan_one hI hs hB
  | setF2 val => simp only [stepR, hs]; exact inv_stepR_setF2 hI hs
  | clr j val => simp only [stepR, hs]; exact inv_stepR_clr hI hs
  | resF1 val => simp only [stepR, hs]; exact inv_stepR_resF1 hI hs
  | resF2 val => simp only [stepR, hs]; exact inv_stepR_resF2 hI hs

end Alg4

end Cslib.SharedMemory
