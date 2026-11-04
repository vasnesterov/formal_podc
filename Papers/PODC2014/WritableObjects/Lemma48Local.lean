import Papers.PODC2014.WritableObjects.Lemma48Clock

/-!
# Lemma 4.8, part 3: protection of indices across the steps of `recycle()`

`Loc.Prot l i γ`: `i ∉ free_p` and `i` is held until update time `γ`; `Loc.SlotProt l i o q`:
the same with `γ` the next time `p` reads the slot `(o, q)`. These are preserved by the three
atomic steps of `recycle()` provided the slot, when read, contains `i` (Claims 4.15–4.17).
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec}

/-- `i` is not in `free_p` and held until update time `γ`. -/
def Loc.Prot (l : Loc n T) (i : Idx n) (γ : ℕ) : Prop := i ∉ l.qs.free ∧ l.Hold i γ

/-- `i` is not in `free_p` and held until `p` next reads slot `(o, q)`. -/
def Loc.SlotProt (l : Loc n T) (i : Idx n) (o : Fin 4) (q : Fin n) : Prop :=
  l.Prot i (l.nr o q)

lemma Loc.Prot.mono {l : Loc n T} {i : Idx n} {γ γ' : ℕ} (h : l.Prot i γ) (hγ : γ' ≤ γ) :
    l.Prot i γ' := ⟨h.1, Hold.mono h.2 hγ⟩

lemma Loc.U_of_stage0 (l : Loc n T) (h : stage l.pc = 0) : l.U = fun _ => l.ctr := by
  funext o; simp [Loc.U, h]

/-- Transport along a step that changes neither the queues nor the clock. -/
lemma Loc.Prot.congr {l l' : Loc n T} {i : Idx n} {γ : ℕ} (h : l.Prot i γ) (hq : l'.qs = l.qs)
    (hU : l'.U = l.U) : l'.Prot i γ := by
  unfold Loc.Prot Loc.Hold at *; rw [hq, hU]; exact h

lemma Loc.SlotProt.congr {l l' : Loc n T} {i : Idx n} {o : Fin 4} {q : Fin n}
    (h : l.SlotProt i o q) (hq : l'.qs = l.qs) (hU : l'.U = l.U) : l'.SlotProt i o q := by
  unfold Loc.SlotProt Loc.nr at *; rw [hU]; exact h.congr hq hU

lemma Loc.U_congr {l l' : Loc n T} (hc : l'.ctr = l.ctr) (hs : stage l'.pc = stage l.pc) :
    l'.U = l.U := by
  funext o; simp [Loc.U, hc, hs]

variable [NeZero n]

section rec27

variable (l : Loc n T) (p : Fin n) (v : T.State) (f : Idx n) (a : Option (Idx n))

/-- The local state after lines 25–28. -/
abbrev Loc.r27 : Loc n T :=
  { l with
    pc := .w29 v f
    qs := upd p 1 a (upd p 0 (some f) { l.qs with free := l.qs.free.erase f })
    lc := Function.update l.lc f l.ctr
    pp := Function.update l.pp f none }

variable {l p v f a}

lemma Loc.r27_U (hpc : l.pc = .w27 v) :
    (l.r27 p v f a).U = Function.update (Function.update (fun _ => l.ctr) 0 (l.ctr + 1)) 1
      (l.ctr + 1) := by
  funext o; fin_cases o <;> simp [Loc.U, stage, hpc]

lemma Loc.r27_Prot (hpc : l.pc = .w27 v) (hs : QOK p l.qs) {i : Idx n} {γ : ℕ}
    (h : l.Prot i γ) (hγ : 4 * l.ctr + 2 ≤ γ) : (l.r27 p v f a).Prot i γ := by
  have hU := l.U_of_stage0 (by simp [hpc, stage])
  obtain ⟨hi, hh⟩ := h
  unfold Loc.Hold at hh; rw [hU] at hh
  have hs' := hs.erase f
  have hi' : i ∉ (({ l.qs with free := l.qs.free.erase f } : QS n)).free :=
    fun h => hi (Finset.mem_of_mem_erase h)
  have h1 := Hold.upd_lt hs' (s := { l.qs with free := l.qs.free.erase f }) hh 0 (some f)
    (by simp <;> omega)
  have h1f := not_mem_free_upd_lt hs' hh 0 (some f) (by simp <;> omega) hi'
  have h2 := Hold.upd_lt (hs'.updQ 0 (some f)) h1 1 a (by simp <;> omega)
  have h2f := not_mem_free_upd_lt (hs'.updQ 0 (some f)) h1 1 a (by simp <;> omega) h1f
  refine ⟨h2f, ?_⟩
  unfold Loc.Hold; rw [Loc.r27_U hpc]; simpa using h2

lemma Loc.r27_read (hpc : l.pc = .w27 v) (hs : QOK p l.qs) {i : Idx n}
    (h : l.Prot i (4 * l.ctr + 1)) (ha : a = some i) (hip : i.1 = p) :
    (l.r27 p v f a).Prot i (4 * l.ctr + 1 + (8 * n + 8)) := by
  have hU := l.U_of_stage0 (by simp [hpc, stage])
  obtain ⟨hi, hh⟩ := h
  unfold Loc.Hold at hh; rw [hU] at hh
  have hs' := hs.erase f
  have hi' : i ∉ (({ l.qs with free := l.qs.free.erase f } : QS n)).free :=
    fun h => hi (Finset.mem_of_mem_erase h)
  have h1f := not_mem_free_upd_lt hs' hh 0 (some f) (by simp) hi'
  subst ha
  have h2 := Hold.upd_enq (hs'.updQ 0 (some f))
    (U := Function.update (fun _ => l.ctr) 0 (l.ctr + 1)) 1 hip
  have h2f := not_mem_free_upd_enq (hs'.updQ 0 (some f)) 1 hip h1f
  refine ⟨h2f, ?_⟩
  unfold Loc.Hold; rw [Loc.r27_U hpc]; simpa using h2

lemma Loc.r27_chosen (hpc : l.pc = .w27 v) (hs : QOK p l.qs) (hf : f ∈ l.qs.free) :
    (l.r27 p v f a).Prot f (4 * (l.ctr + 2 * n + 2)) := by
  have hfp : f.1 = p := hs.freeOwn f hf
  have hs' := hs.erase f
  have hU := l.U_of_stage0 (by simp [hpc, stage])
  have h1 := Hold.upd_enq hs' (s := { l.qs with free := l.qs.free.erase f })
    (U := fun _ => l.ctr) 0 hfp
  have h1f := not_mem_free_upd_enq hs' (s := { l.qs with free := l.qs.free.erase f }) 0 hfp
    (by simp)
  have h2 := Hold.upd_lt (hs'.updQ 0 (some f)) h1 1 a (by simp <;> omega)
  have h2f := not_mem_free_upd_lt (hs'.updQ 0 (some f)) h1 1 a (by simp <;> omega) h1f
  refine ⟨h2f, ?_⟩
  unfold Loc.Hold; rw [Loc.r27_U hpc]
  exact Hold.mono h2 (by simp <;> omega)

lemma Loc.r27_slot (hpc : l.pc = .w27 v) (hs : QOK p l.qs) {i : Idx n} {o : Fin 4} {q : Fin n}
    (ho : o ≠ 0) (h : l.SlotProt i o q) (hip : i.1 = p)
    (hread : o = 1 → cq l.ctr = q → a = some i) : (l.r27 p v f a).SlotProt i o q := by
  have hU := l.U_of_stage0 (by simp [hpc, stage])
  have hU' := Loc.r27_U (f := f) (a := a) (p := p) hpc
  unfold Loc.SlotProt Loc.nr at *
  rw [hU] at h; rw [hU']; simp only at h
  have hq := q.isLt
  by_cases h1 : o = 1
  · subst h1; simp only [Function.update_self]
    have hv : ((1 : Fin 4) : ℕ) = 1 := rfl
    simp only [hv] at h ⊢
    by_cases hc : l.ctr % n = q
    · have e := nextR_eq_self (o := 1) hq hc
      rw [e] at h
      have hc' : cq l.ctr = q := Fin.ext hc
      have := Loc.r27_read (f := f) hpc hs h (hread rfl hc') hip
      rw [nextR_succ_of_eq hq hc]
      exact this.mono (by omega)
    · rw [nextR_succ_of_ne hq hc]
      have hge := nextR_ge (n := n) l.ctr 1 q
      have hne : nextR n l.ctr 1 q ≠ 4 * l.ctr + 1 := fun e => hc (by
        have := nextR_div (n := n) l.ctr 1 q (by omega) hq; rw [e] at this
        have h2 : (4 * l.ctr + 1) / 4 = l.ctr := by omega
        rw [h2] at this; exact this.1)
      exact Loc.r27_Prot hpc hs h (by omega)
  · have e : Function.update (Function.update (fun _ : Fin 4 => l.ctr) 0 (l.ctr + 1)) 1
        (l.ctr + 1) o = l.ctr := by
      rw [Function.update_of_ne h1, Function.update_of_ne ho]
    rw [e]
    have hge := nextR_ge (n := n) l.ctr o q
    have ho2 : 2 ≤ o.val := by
      have : o.val ≠ 0 := fun h' => ho (Fin.ext h'); have : o.val ≠ 1 := fun h' => h1 (Fin.ext h')
      omega
    exact Loc.r27_Prot hpc hs h (by omega)

end rec27

section rec29

variable (l : Loc n T) (p : Fin n) (v : T.State) (f : Idx n) (a : Option (Idx n))

/-- The local state after lines 29–30. -/
abbrev Loc.r29 : Loc n T := { l with pc := .w31 v f, qs := upd p 2 a l.qs }

variable {l p v f a}

lemma Loc.r29_U (hpc : l.pc = .w29 v f) :
    (l.r29 p v f a).U = Function.update l.U 2 (l.U 2 + 1) := by
  funext o; fin_cases o <;> simp [Loc.U, stage, hpc]

lemma Loc.r29_U2 (hpc : l.pc = .w29 v f) : l.U 2 = l.ctr := by simp [Loc.U, stage, hpc]

lemma Loc.r29_Prot (hpc : l.pc = .w29 v f) (hs : QOK p l.qs) {i : Idx n} {γ : ℕ}
    (h : l.Prot i γ) (hγ : 4 * l.ctr + 3 ≤ γ) : (l.r29 p v f a).Prot i γ := by
  obtain ⟨hi, hh⟩ := h
  have e := Loc.r29_U2 hpc
  refine ⟨not_mem_free_upd_lt hs hh 2 a (by simp [e]; omega) hi, ?_⟩
  unfold Loc.Hold; rw [Loc.r29_U hpc]
  exact Hold.upd_lt hs hh 2 a (by simp [e]; omega)

lemma Loc.r29_slot (hpc : l.pc = .w29 v f) (hs : QOK p l.qs) {i : Idx n} {o : Fin 4} {q : Fin n}
    (ho : o ≠ 0) (h : l.SlotProt i o q) (hip : i.1 = p)
    (hread : o = 2 → cq l.ctr = q → a = some i) : (l.r29 p v f a).SlotProt i o q := by
  have hU' := Loc.r29_U (a := a) (p := p) hpc
  have e2 := Loc.r29_U2 hpc
  have hq := q.isLt
  unfold Loc.SlotProt Loc.nr at *
  rw [hU']
  by_cases h2 : o = 2
  · subst h2; simp only [Function.update_self]
    have hv : ((2 : Fin 4) : ℕ) = 2 := rfl
    simp only [hv] at h ⊢
    rw [e2] at h ⊢
    by_cases hc : l.ctr % n = q
    · have e := nextR_eq_self (o := 2) hq hc
      rw [e] at h
      obtain ⟨hi, hh⟩ := h
      have ha := hread rfl (Fin.ext hc); subst ha
      have h2 := Hold.upd_enq hs (s := l.qs) (U := l.U) 2 hip
      have h2f := not_mem_free_upd_enq hs 2 hip hi
      rw [nextR_succ_of_eq hq hc]
      refine ⟨h2f, ?_⟩
      unfold Loc.Hold; rw [Loc.r29_U hpc]
      exact Hold.mono h2 (by simp [e2]; omega)
    · rw [nextR_succ_of_ne hq hc]
      have hne : nextR n l.ctr 2 q ≠ 4 * l.ctr + 2 := fun e => hc (by
        have := nextR_div (n := n) l.ctr 2 q (by omega) hq; rw [e] at this
        have h2 : (4 * l.ctr + 2) / 4 = l.ctr := by omega
        rw [h2] at this; exact this.1)
      have hge := nextR_ge (n := n) l.ctr 2 q
      exact Loc.r29_Prot hpc hs h (by omega)
  · rw [Function.update_of_ne h2]
    have hge := nextR_ge (n := n) (l.U o) o q
    have : 4 * l.ctr + 3 ≤ 4 * l.U o + o := by
      have : o.val ≠ 0 := fun h' => ho (Fin.ext h')
      have : o.val ≠ 2 := fun h' => h2 (Fin.ext h')
      fin_cases o <;> simp_all [Loc.U, stage] <;> omega
    exact Loc.r29_Prot hpc hs h (by omega)

end rec29

section rec31

variable (l : Loc n T) (p : Fin n) (v : T.State) (f : Idx n) (a : Option (Idx n))

/-- The local state after lines 31–32. -/
abbrev Loc.r31 : Loc n T := { l with pc := .w13 v f, qs := upd p 3 a l.qs }

variable {l p v f a}

lemma Loc.r31_U (hpc : l.pc = .w31 v f) :
    (l.r31 p v f a).U = Function.update l.U 3 (l.U 3 + 1) := by
  funext o; fin_cases o <;> simp [Loc.U, stage, hpc]

lemma Loc.r31_U3 (hpc : l.pc = .w31 v f) : l.U 3 = l.ctr := by simp [Loc.U, stage, hpc]

lemma Loc.r31_Prot (hpc : l.pc = .w31 v f) (hs : QOK p l.qs) {i : Idx n} {γ : ℕ}
    (h : l.Prot i γ) (hγ : 4 * l.ctr + 4 ≤ γ) : (l.r31 p v f a).Prot i γ := by
  obtain ⟨hi, hh⟩ := h
  have e := Loc.r31_U3 hpc
  refine ⟨not_mem_free_upd_lt hs hh 3 a (by simp [e]; omega) hi, ?_⟩
  unfold Loc.Hold; rw [Loc.r31_U hpc]
  exact Hold.upd_lt hs hh 3 a (by simp [e]; omega)

lemma Loc.r31_slot (hpc : l.pc = .w31 v f) (hs : QOK p l.qs) {i : Idx n} {o : Fin 4} {q : Fin n}
    (ho : o ≠ 0) (h : l.SlotProt i o q) (hip : i.1 = p)
    (hread : o = 3 → cq l.ctr = q → a = some i) : (l.r31 p v f a).SlotProt i o q := by
  have hU' := Loc.r31_U (a := a) (p := p) hpc
  have e3 := Loc.r31_U3 hpc
  have hq := q.isLt
  unfold Loc.SlotProt Loc.nr at *
  rw [hU']
  by_cases h3 : o = 3
  · subst h3; simp only [Function.update_self]
    have hv : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [hv] at h ⊢
    rw [e3] at h ⊢
    by_cases hc : l.ctr % n = q
    · have e := nextR_eq_self (o := 3) hq hc
      rw [e] at h
      obtain ⟨hi, hh⟩ := h
      have ha := hread rfl (Fin.ext hc); subst ha
      have h2 := Hold.upd_enq hs (s := l.qs) (U := l.U) 3 hip
      have h2f := not_mem_free_upd_enq hs 3 hip hi
      rw [nextR_succ_of_eq hq hc]
      refine ⟨h2f, ?_⟩
      unfold Loc.Hold; rw [Loc.r31_U hpc]
      exact Hold.mono h2 (by simp [e3]; omega)
    · rw [nextR_succ_of_ne hq hc]
      have hne : nextR n l.ctr 3 q ≠ 4 * l.ctr + 3 := fun e => hc (by
        have := nextR_div (n := n) l.ctr 3 q (by omega) hq; rw [e] at this
        have h2 : (4 * l.ctr + 3) / 4 = l.ctr := by omega
        rw [h2] at this; exact this.1)
      have hge := nextR_ge (n := n) l.ctr 3 q
      exact Loc.r31_Prot hpc hs h (by omega)
  · rw [Function.update_of_ne h3]
    have hge := nextR_ge (n := n) (l.U o) o q
    have : 4 * l.ctr + 4 ≤ 4 * l.U o + o := by
      have : o.val ≠ 0 := fun h' => ho (Fin.ext h')
      have : o.val ≠ 3 := fun h' => h3 (Fin.ext h')
      fin_cases o <;> simp_all [Loc.U, stage] <;> omega
    exact Loc.r31_Prot hpc hs h (by omega)

end rec31

end Podc.WritableObjects.WF
