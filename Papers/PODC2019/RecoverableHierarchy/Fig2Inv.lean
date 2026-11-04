import Papers.PODC2019.RecoverableHierarchy.Fig2

/-!
# Figure 2: the safety invariant (Lemmas 12–14)

An invariant `Inv` of all reachable configurations of Figure 2, in **every** execution (any
number of crashes). The heart of agreement (Lemma 14) is the *stable* predicate `G C k₀ d`
("after the decision `d` of iteration `k₀` was confirmed by a complete check of lines 23–26"):

* `D[k₀] = d`;
* every `C[k]`, `k > k₀`, is `⊥` or `d`;
* every process past line 17 in an iteration `k > k₀` already adopted `d` (it scanned `D[k₀]`
  at line 19 after `D[k₀]` was written) — `LocG`.

`G` is preserved by every event (`G_step`, `G_crash`). While a process `i` runs the check of
iteration `k₀` with decision `d` and no reset so far, at loop index `y`, either `G C k₀ d`
holds or some process `z ≠ i` with `z ≥ y` (not yet inspected) has `R[z] ≥ k₀ + 2` (`Bad`), in
which case `i` will find it and reset. When the check ends without a reset, `G C k₀ d` holds.
An output `d` thus satisfies `Decided C d`: `C[k] = d` for some `k` with `k = f` or `G C k d`.
-/

namespace Podc.RecoverableHierarchy.Fig2

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {n f : ℕ}

@[simp] lemma mem_R (C : Cfg (A n f)) (z : Fin n) : C.mem (.inl (.inl z)) = R C z := rfl
@[simp] lemma mem_D (C : Cfg (A n f)) (k : Fin (f + 1)) : C.mem (.inl (.inr k)) = D C k := rfl
@[simp] lemma mem_Cv (C : Cfg (A n f)) (k : Fin (f + 1)) : C.mem (.inr k) = Cv C k := rfl

/-- `b` is the input of some process. -/
def Val (C : Cfg (A n f)) (b : Bool) : Prop := ∃ q, C.inp q = b

/-- The local part of `G`: past line 17 in an iteration `k > k₀`, the process adopted `d`. -/
def LocG (k₀ : ℕ) (d : Bool) : PC n f → Prop
  | .scan k j v => k₀ < k.val → k₀ < j → v = d
  | .wr22 k d' _ => k₀ < k.val → d' = d
  | .chk k d' _ _ _ => k₀ < k.val → d' = d
  | _ => True

/-- The stable "confirmed decision" predicate (see the module docstring). -/
def G (C : Cfg (A n f)) (k₀ : Fin (f + 1)) (d : Bool) : Prop :=
  D C k₀ = some d ∧ (∀ k : Fin (f + 1), k₀ < k → ∀ w, Cv C k = some w → w = d) ∧
    ∀ z, LocG k₀.val d (C.loc z).pc

/-- Some process `z ≠ i` with `z ≥ y` (not yet inspected by `i`'s check) is in an iteration
`> k`. -/
def Bad (C : Cfg (A n f)) (k : Fin (f + 1)) (i : Fin n) (y : ℕ) : Prop :=
  ∃ z : Fin n, y ≤ z.val ∧ z ≠ i ∧ k.val + 2 ≤ R C z

/-- `d` was decided by some `C[k]` and is either from the last iteration or confirmed. -/
def Decided (C : Cfg (A n f)) (d : Bool) : Prop :=
  ∃ k : Fin (f + 1), Cv C k = some d ∧ (k.val = f ∨ G C k d)

/-- The local invariant of process `z` (program counter `pc`). -/
def PCInv (C : Cfg (A n f)) (z : Fin n) : PC n f → Prop
  | .rd16 k v => k ≤ R C z ∧ Val C v
  | .wr17 k v => R C z = k.val ∧ Val C v
  | .scan k _ v => R C z = k.val + 1 ∧ Val C v
  | .wr22 k d v => R C z = k.val + 1 ∧ Cv C k = some d ∧ Val C v
  | .chk k d v r y => R C z = k.val + 1 ∧ Cv C k = some d ∧ Val C v ∧
      (r = false → D C k = some d ∧ (G C k d ∨ Bad C k z y.val))
  | .done d => Decided C d

/-- The safety invariant of Figure 2. -/
structure Inv (C : Cfg (A n f)) : Prop where
  id : ∀ z, (C.loc z).id = z
  dc : ∀ k w, D C k = some w → Cv C k = some w
  cr : ∀ k w, Cv C k = some w → ∃ z, k.val + 1 ≤ R C z
  cval : ∀ k w, Cv C k = some w → Val C w
  loc : ∀ z, PCInv C z (C.loc z).pc

/-! ## Monotonicity -/

/-- `C'` extends `C`: same inputs, registers `R` grow, decisions of `C` and `D` persist. -/
structure Mono (C C' : Cfg (A n f)) : Prop where
  inp : C'.inp = C.inp
  R : ∀ z, R C z ≤ R C' z
  Cv : ∀ k w, Cv C k = some w → Cv C' k = some w
  D : ∀ k w, D C k = some w → D C' k = some w

section Mono

variable {C C' : Cfg (A n f)}

lemma Mono.val (h : Mono C C') {b : Bool} (hb : Val C b) : Val C' b := by
  obtain ⟨q, hq⟩ := hb; exact ⟨q, by rw [h.inp, hq]⟩

lemma Mono.bad (h : Mono C C') {k : Fin (f + 1)} {i : Fin n} {y : ℕ} (hb : Bad C k i y) :
    Bad C' k i y := by
  obtain ⟨z, h1, h2, h3⟩ := hb; exact ⟨z, h1, h2, h3.trans (h.R z)⟩

lemma Mono.decided (h : Mono C C') (hG : ∀ k d, G C k d → G C' k d) {d : Bool}
    (hd : Decided C d) : Decided C' d := by
  obtain ⟨k, h1, h2⟩ := hd
  exact ⟨k, h.Cv _ _ h1, h2.imp id (hG k d)⟩

lemma PCInv.mono (h : Mono C C') (hG : ∀ k d, G C k d → G C' k d) {z : Fin n}
    (hR : R C' z = R C z) {pc : PC n f} (hp : PCInv C z pc) : PCInv C' z pc := by
  cases pc with
  | rd16 k v => exact ⟨hR ▸ hp.1, h.val hp.2⟩
  | wr17 k v => exact ⟨hR ▸ hp.1, h.val hp.2⟩
  | scan k j v => exact ⟨hR ▸ hp.1, h.val hp.2⟩
  | wr22 k d v => exact ⟨hR ▸ hp.1, h.Cv _ _ hp.2.1, h.val hp.2.2⟩
  | chk k d v r y =>
    refine ⟨hR ▸ hp.1, h.Cv _ _ hp.2.1, h.val hp.2.2.1, fun hr => ?_⟩
    obtain ⟨h1, h2⟩ := hp.2.2.2 hr
    exact ⟨h.D _ _ h1, h2.imp (hG k d) h.bad⟩
  | done d => exact h.decided hG hp

lemma mono_refl_loc (C : Cfg (A n f)) (loc : Fin n → (A n f).L) :
    Mono C ⟨C.inp, loc, C.mem⟩ :=
  ⟨rfl, fun _ => le_rfl, fun _ _ h => h, fun _ _ h => h⟩

end Mono

/-! ## Basic facts -/

lemma skip_le {i z : Fin n} {y : ℕ} (hz : z ≠ i) (hy : y ≤ z.val) : skip i y ≤ z.val := by
  unfold skip
  split_ifs with h
  · have : z.val ≠ i.val := fun h' => hz (Fin.ext h')
    omega
  · exact hy

lemma Bad.skip_lt {C : Cfg (A n f)} {k : Fin (f + 1)} {i : Fin n} {y : ℕ} (h : Bad C k i y) :
    skip i y < n := by
  obtain ⟨z, h1, h2, -⟩ := h
  exact lt_of_le_of_lt (skip_le h2 h1) z.isLt

/-- A process past line 17 in iteration `k` has `R[z] = k+1`, so if `R[z] ≤ k₀ + 1` it is not in
an iteration `> k₀`. -/
lemma locG_of_R {C : Cfg (A n f)} {z : Fin n} {pc : PC n f} (h : PCInv C z pc) {k₀ : ℕ}
    (d : Bool) (hR : R C z ≤ k₀ + 1) : LocG k₀ d pc := by
  cases pc with
  | scan k j v => intro hk; have := h.1; omega
  | wr22 k d' v => intro hk; have := h.1; omega
  | chk k d' v r y => intro hk; have := h.1; omega
  | _ => trivial

lemma Inv.val_of_D {C : Cfg (A n f)} (hI : Inv C) {k : Fin (f + 1)} {w : Bool}
    (h : D C k = some w) : Val C w := hI.cval k w (hI.dc k w h)

lemma Inv.val_getD {C : Cfg (A n f)} (hI : Inv C) {k : Fin (f + 1)} {v : Bool} (hv : Val C v) :
    Val C ((D C k).getD v) := by
  rcases h : D C k with _ | w
  · simpa using hv
  · simpa using hI.val_of_D h

lemma Inv.val_getD_Cv {C : Cfg (A n f)} (hI : Inv C) {k : Fin (f + 1)} {v : Bool}
    (hv : Val C v) : Val C ((Cv C k).getD v) := by
  rcases h : Cv C k with _ | w
  · simpa using hv
  · simpa using hI.cval _ _ h

/-! ## Updates of local states -/

section Upd

variable {C : Cfg (A n f)} {p : Fin n} {l : Loc n f} {mem' : (j : Idx n f) → (Obj n f j).State}

@[simp] lemma loc_upd_self :
    (⟨C.inp, Function.update C.loc p l, mem'⟩ : Cfg (A n f)).loc p = l := by
  simp

lemma loc_upd_ne {z : Fin n} (hz : z ≠ p) :
    (⟨C.inp, Function.update C.loc p l, mem'⟩ : Cfg (A n f)).loc z = C.loc z := by
  simp [Function.update_of_ne hz]

/-- Transfer of `G` to a configuration where only `p` moved. -/
lemma G_transfer {k₀ : Fin (f + 1)} {d : Bool} (hG : G C k₀ d)
    (hD : D (⟨C.inp, Function.update C.loc p l, mem'⟩ : Cfg (A n f)) k₀ = some d)
    (hC : ∀ k : Fin (f + 1), k₀ < k → ∀ w,
      Cv (⟨C.inp, Function.update C.loc p l, mem'⟩ : Cfg (A n f)) k = some w →
        Cv C k = some w ∨ w = d)
    (hp : LocG k₀.val d l.pc) :
    G (⟨C.inp, Function.update C.loc p l, mem'⟩ : Cfg (A n f)) k₀ d := by
  refine ⟨hD, fun k hk w hw => ?_, fun z => ?_⟩
  · rcases hC k hk w hw with h | h
    · exact hG.2.1 k hk w h
    · exact h
  · by_cases hz : z = p
    · subst hz; simpa using hp
    · rw [loc_upd_ne hz]; exact hG.2.2 z

end Upd

/-! ## Stability of `G` -/

/-- The local state of `p` and its invariant. -/
lemma Inv.locOf {C : Cfg (A n f)} (hI : Inv C) {p i : Fin n} {pc : PC n f}
    (hl : C.loc p = ⟨i, pc⟩) : i = p ∧ PCInv C p pc := by
  have h1 := hI.id p; have h2 := hI.loc p; rw [hl] at h1 h2; exact ⟨h1, h2⟩

/-- `G` is stable under steps. -/
lemma G_step {C : Cfg (A n f)} (hI : Inv C) (p : Fin n) {k₀ : Fin (f + 1)} {d : Bool}
    (hG : G C k₀ d) : G (C.stepP p) k₀ d := by
  rcases hl : C.loc p with ⟨i, pc⟩
  obtain ⟨rfl, hpc⟩ := hI.locOf hl
  have hLG : LocG k₀.val d pc := by have := hG.2.2 i; rwa [hl] at this
  cases pc with
  | rd16 k v =>
    rw [stepP_rd16 hl]
    refine G_transfer hG (by simpa using hG.1) (fun k _ w hw => Or.inl (by simpa using hw)) ?_
    simp only; split_ifs <;> trivial
  | wr17 k v =>
    rw [stepP_wr17 hl]
    exact G_transfer hG (by simpa using hG.1) (fun k _ w hw => Or.inl (by simpa using hw))
      (fun _ h => absurd h (Nat.not_lt_zero _))
  | scan k j v =>
    by_cases hj : j < k.val
    · rw [stepP_scan_lt hl hj]
      refine G_transfer hG (by simpa using hG.1) (fun k _ w hw => Or.inl (by simpa using hw)) ?_
      intro hk hj'
      rcases Nat.lt_or_ge k₀.val j with h | h
      · have hv := hLG hk h
        rcases hD : D C ⟨j, lt_trans hj k.isLt⟩ with _ | w
        · simpa [hD] using hv
        · simpa [hD] using hG.2.1 ⟨j, lt_trans hj k.isLt⟩ h w (hI.dc _ _ hD)
      · have hk₀ : (⟨j, lt_trans hj k.isLt⟩ : Fin (f + 1)) = k₀ := Fin.ext (by simp; omega)
        simp [hk₀, hG.1]
    · rw [stepP_scan_ge hl hj]
      have key : k₀ < k → (Cv C k).getD v = d := by
        intro hk
        rcases hc : Cv C k with _ | w
        · simpa using hLG hk (by omega)
        · simpa using hG.2.1 k hk w hc
      refine G_transfer hG (by simpa using hG.1) (fun k' hk' w hw => ?_) key
      by_cases hkk : k' = k
      · subst hkk; right; simp at hw; rw [← hw]; exact key hk'
      · left; simpa [hkk] using hw
  | wr22 k d' v =>
    rw [stepP_wr22 hl]
    refine G_transfer hG ?_ (fun k _ w hw => Or.inl (by simpa using hw)) ?_
    · by_cases hkk : k₀ = k
      · subst hkk
        have h1 := hI.dc _ _ hG.1
        rw [hpc.2.1] at h1
        simpa using h1
      · simpa [hkk] using hG.1
    · simp only
      split_ifs with hf
      · unfold goChk; split_ifs <;> simp [LocG]; exact hLG
      · trivial
  | chk k d' v r y =>
    rw [stepP_chk hl]
    refine G_transfer hG (by simpa using hG.1) (fun k _ w hw => Or.inl (by simpa using hw)) ?_
    simp only; unfold goChk; split_ifs <;> simp [LocG]; exact hLG
  | done d' => rw [stepP_done hl]; exact hG

/-- `G` is stable under crashes. -/
lemma G_crash {C : Cfg (A n f)} (p : Fin n) {k₀ : Fin (f + 1)} {d : Bool}
    (hG : G C k₀ d) : G (C.next (.crash p)) k₀ d :=
  G_transfer (l := ⟨p, .rd16 0 (C.inp p)⟩) hG (by simpa using hG.1)
    (fun k _ w hw => Or.inl (by simpa using hw)) trivial

/-! ## Preservation of the invariant -/

lemma Bad.skip {C : Cfg (A n f)} {k : Fin (f + 1)} {i : Fin n} {y : ℕ} (h : Bad C k i y) :
    Bad C k i (skip i y) := by
  obtain ⟨z, h1, h2, h3⟩ := h
  exact ⟨z, skip_le h2 h1, h2, h3⟩

lemma Bad.next {C : Cfg (A n f)} {k : Fin (f + 1)} {i y : Fin n} (h : Bad C k i y.val)
    (hy : R C y ≤ k.val + 1) : Bad C k i (y.val + 1) := by
  obtain ⟨z, h1, h2, h3⟩ := h
  refine ⟨z, ?_, h2, h3⟩
  rcases Nat.lt_or_ge y.val z.val with h | h
  · exact h
  · have : z = y := Fin.ext (by omega)
    subst this; omega

/-- Building the invariant of a configuration where only `p` moved. -/
lemma Inv.upd {C C' : Cfg (A n f)} (hI : Inv C) {p : Fin n} {l : Loc n f}
    (hloc : C'.loc = Function.update C.loc p l) (hmono : Mono C C')
    (hRo : ∀ z, z ≠ p → R C' z = R C z) (hid : l.id = p)
    (hdc : ∀ k w, D C' k = some w → Cv C' k = some w)
    (hcr : ∀ k w, Cv C' k = some w → ∃ z, k.val + 1 ≤ R C' z)
    (hcval : ∀ k w, Cv C' k = some w → Val C' w)
    (hG : ∀ k d, G C k d → G C' k d) (hl : PCInv C' p l.pc) : Inv C' where
  id z := by
    by_cases hz : z = p
    · subst hz; simpa [hloc] using hid
    · simpa [hloc, Function.update_of_ne hz] using hI.id z
  dc := hdc
  cr := hcr
  cval := hcval
  loc z := by
    by_cases hz : z = p
    · subst hz; simpa [hloc] using hl
    · have := (hI.loc z).mono hmono hG (hRo z hz)
      simpa [hloc, Function.update_of_ne hz] using this

/-- The decision `d` of iteration `k` becomes confirmed (`G`) when no other process is in an
iteration `> k`. -/
lemma G_start {C C' : Cfg (A n f)} (hI : Inv C) {p : Fin n} {l : Loc n f}
    (hloc : C'.loc = Function.update C.loc p l) (hRo : ∀ z, z ≠ p → R C' z = R C z)
    (hCv : ∀ k w, Cv C' k = some w → Cv C k = some w) {k : Fin (f + 1)} {d : Bool}
    (hD : D C' k = some d) (hRp : R C p = k.val + 1) (hall : ∀ z, z ≠ p → R C z ≤ k.val + 1)
    (hlp : LocG k.val d l.pc) : G C' k d := by
  have hle : ∀ z, R C z ≤ k.val + 1 := fun z => by
    by_cases hz : z = p
    · subst hz; omega
    · exact hall z hz
  refine ⟨hD, fun k' hk' w hw => ?_, fun z => ?_⟩
  · obtain ⟨z, hz⟩ := hI.cr k' w (hCv k' w hw)
    have := hle z
    have : k.val < k'.val := hk'
    omega
  · by_cases hz : z = p
    · subst hz; simpa [hloc] using hlp
    · simpa [hloc, Function.update_of_ne hz] using locG_of_R (hI.loc z) d (hall z hz)

/-- Steps extend the configuration (`Mono`) and only `p` writes `R[p]`. -/
lemma Inv.mono_step {C : Cfg (A n f)} (hI : Inv C) (p : Fin n) :
    Mono C (C.stepP p) ∧ ∀ z, z ≠ p → R (C.stepP p) z = R C z := by
  rcases hl : C.loc p with ⟨i, pc⟩
  obtain ⟨rfl, hpc⟩ := hI.locOf hl
  cases pc with
  | rd16 k v => rw [stepP_rd16 hl]; exact ⟨mono_refl_loc _ _, fun _ _ => rfl⟩
  | wr17 k v =>
    rw [stepP_wr17 hl]
    refine ⟨⟨rfl, fun z => ?_, fun _ _ h => by simpa using h, fun _ _ h => by simpa using h⟩,
      fun z hz => by simp [hz]⟩
    by_cases hz : z = i
    · subst hz; simp; have := hpc.1; omega
    · simp [hz]
  | scan k j v =>
    by_cases hj : j < k.val
    · rw [stepP_scan_lt hl hj]; exact ⟨mono_refl_loc _ _, fun _ _ => rfl⟩
    · rw [stepP_scan_ge hl hj]
      refine ⟨⟨rfl, fun z => by simp, fun k' w h => ?_, fun _ _ h => by simpa using h⟩,
        fun z _ => by simp⟩
      simp only [Cv_upd_C, mem_Cv]; split_ifs with hk
      · subst hk; simp [h]
      · exact h
  | wr22 k d v =>
    rw [stepP_wr22 hl]
    refine ⟨⟨rfl, fun z => by simp, fun _ _ h => by simpa using h, fun k' w h => ?_⟩,
      fun z _ => by simp⟩
    simp only [D_upd_D, mem_D]; split_ifs with hk
    · subst hk; have := hI.dc _ _ h; rw [hpc.2.1] at this; simp [this]
    · exact h
  | chk k d v r y => rw [stepP_chk hl]; exact ⟨mono_refl_loc _ _, fun _ _ => rfl⟩
  | done d => rw [stepP_done hl]; exact ⟨⟨rfl, fun _ => le_rfl, fun _ _ h => h, fun _ _ h => h⟩,
      fun _ _ => rfl⟩

/-- **The invariant is preserved by steps.** -/
lemma Inv.step {C : Cfg (A n f)} (hI : Inv C) (p : Fin n) : Inv (C.stepP p) := by
  have hG : ∀ k d, G C k d → G (C.stepP p) k d := fun k d h => G_step hI p h
  have hM := hI.mono_step p
  rcases hl : C.loc p with ⟨i, pc⟩
  obtain ⟨rfl, hpc⟩ := hI.locOf hl
  cases pc with
  | rd16 k v =>
    rw [stepP_rd16 hl] at hG ⊢
    refine hI.upd rfl (mono_refl_loc _ _) (fun _ _ => rfl) rfl (by simpa using hI.dc)
      (by simpa using hI.cr) (fun k w hw => hI.cval k w hw) hG ?_
    obtain ⟨h1, h2⟩ := hpc
    simp only
    split_ifs with hk hR
    · exact ⟨by simpa using hR, h2⟩
    · exact ⟨by simp; omega, h2⟩
    · exact ⟨by simpa using h1, h2⟩
  | wr17 k v =>
    rw [stepP_wr17 hl] at hG hM ⊢
    obtain ⟨h1, h2⟩ := hpc
    have hmono := hM.1
    refine hI.upd rfl hmono (fun z hz => by simp [hz]) rfl (by simpa using hI.dc)
      (fun k' w hw => ?_) (fun k w hw => hI.cval k w (by simpa using hw)) hG ⟨by simp, h2⟩
    obtain ⟨z, hz⟩ := hI.cr k' w (by simpa using hw)
    exact ⟨z, hz.trans (hmono.R z)⟩
  | scan k j v =>
    obtain ⟨h1, h2⟩ := hpc
    by_cases hj : j < k.val
    · rw [stepP_scan_lt hl hj] at hG ⊢
      exact hI.upd rfl (mono_refl_loc _ _) (fun _ _ => rfl) rfl (by simpa using hI.dc)
        (by simpa using hI.cr) (fun k w hw => hI.cval k w hw) hG ⟨by simpa using h1, hI.val_getD h2⟩
    · rw [stepP_scan_ge hl hj] at hG hM ⊢
      have hmono := hM.1
      refine hI.upd rfl hmono (fun z hz => by simp) rfl (fun k' w hw => ?_) (fun k' w hw => ?_)
        (fun k' w hw => ?_) hG ⟨by simpa using h1, by simp, h2⟩
      · exact hmono.Cv _ _ (hI.dc k' w (by simpa using hw))
      · simp only [Cv_upd_C, mem_Cv] at hw
        split_ifs at hw with hk
        · subst hk; exact ⟨i, by simp; omega⟩
        · simpa using hI.cr k' w hw
      · simp only [Cv_upd_C, mem_Cv] at hw
        split_ifs at hw with hk
        · cases hw; exact hI.val_getD_Cv h2
        · exact hI.cval k' w hw
  | wr22 k d v =>
    rw [stepP_wr22 hl] at hG hM ⊢
    obtain ⟨h1, h2, h3⟩ := hpc
    have hmono := hM.1
    refine hI.upd rfl hmono (fun z hz => by simp) rfl (fun k' w hw => ?_)
      (by simpa using hI.cr) (fun k w hw => hI.cval k w (by simpa using hw)) hG ?_
    · simp only [D_upd_D, mem_D] at hw
      split_ifs at hw with hk
      · subst hk; cases hw; simpa using h2
      · simpa using hI.dc k' w hw
    · have hst : ∀ X : PC n f, LocG k.val d X → (∀ z, z ≠ i → R C z ≤ k.val + 1) →
          G ⟨C.inp, Function.update C.loc i ⟨i, X⟩,
            Function.update C.mem (.inl (.inr k)) (some d)⟩ k d :=
        fun X hX hall => G_start hI rfl (fun z _ => by simp) (fun _ _ h => by simpa using h)
          (by simp) h1 hall hX
      by_cases hf : k.val < f
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hf)] at hG ⊢
        rcases goChk_cases i k d v false 0 with ⟨hs, he⟩ | ⟨-, h, -⟩ | ⟨hs, -, he⟩
        · rw [he] at hG ⊢
          refine ⟨by simpa using h1, by simpa using h2, h3, fun _ => ⟨by simp, ?_⟩⟩
          by_cases hall : ∀ z, z ≠ i → R C z ≤ k.val + 1
          · exact Or.inl (hst _ (fun h => absurd h (lt_irrefl _)) hall)
          · push Not at hall
            obtain ⟨z, hz, hR⟩ := hall
            exact Or.inr (Bad.skip ⟨z, Nat.zero_le _, hz, by simp; omega⟩)
        · cases h
        · rw [he] at hG ⊢
          refine ⟨k, by simpa using h2, Or.inr (hst _ trivial fun z hz => ?_)⟩
          by_contra hR
          exact hs (Bad.skip_lt (C := C) (k := k) ⟨z, Nat.zero_le _, hz, by omega⟩)
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)] at hG ⊢
        exact ⟨k, by simpa using h2, Or.inl (by have := k.isLt; omega)⟩
  | chk k d v r y =>
    rw [stepP_chk hl] at hG ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hpc
    refine hI.upd rfl (mono_refl_loc _ _) (fun _ _ => rfl) rfl (by simpa using hI.dc)
      (by simpa using hI.cr) (fun k w hw => hI.cval k w hw) hG ?_
    have hcont : (r || decide (k.val + 1 < R C y)) = false →
        D C k = some d ∧ (G C k d ∨ Bad C k i (y.val + 1)) := by
      intro hr
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hr
      obtain ⟨h5, h6⟩ := h4 hr.1
      exact ⟨h5, h6.imp (fun h => h) (fun hb => hb.next hr.2)⟩
    rcases goChk_cases i k d v (r || decide (k.val + 1 < R C y)) (y.val + 1) with
      ⟨hs, he⟩ | ⟨-, -, he⟩ | ⟨hs, hr, he⟩
    · rw [he] at hG ⊢
      refine ⟨by simpa using h1, by simpa using h2, h3, fun hr => ?_⟩
      obtain ⟨h5, h6⟩ := hcont hr
      exact ⟨by simpa using h5, h6.imp (hG k d) (fun hb => (mono_refl_loc _ _).bad hb.skip)⟩
    · rw [he]; exact ⟨by simp; omega, h3⟩
    · rw [he] at hG ⊢
      obtain ⟨h5, h6⟩ := hcont hr
      exact ⟨k, by simpa using h2, Or.inr (hG k d (h6.resolve_right fun hb => hs hb.skip_lt))⟩
  | done d =>
    rw [stepP_done hl]; exact hI

/-- **The invariant is preserved by crashes.** -/
lemma Inv.crash {C : Cfg (A n f)} (hI : Inv C) (p : Fin n) : Inv (C.next (.crash p)) :=
  show Inv ⟨C.inp, Function.update C.loc p ⟨p, .rd16 0 (C.inp p)⟩, C.mem⟩ from
    hI.upd (l := ⟨p, .rd16 0 (C.inp p)⟩) rfl (mono_refl_loc _ _) (fun _ _ => rfl) rfl
    (by simpa using hI.dc) (by simpa using hI.cr) (fun k w hw => hI.cval k w hw)
    (fun k d h => G_crash p h) ⟨Nat.zero_le _, p, rfl⟩

lemma Inv.next {C : Cfg (A n f)} (hI : Inv C) : ∀ e : Ev n, Inv (C.next e)
  | .step p => hI.step p
  | .crash p => hI.crash p

lemma Inv.reach {C : Cfg (A n f)} (hI : Inv C) (α : List (Ev n)) : Inv (run C α) := by
  induction α generalizing C with
  | nil => exact hI
  | cons e α ih => exact ih (hI.next e)

lemma inv_init (x : Fin n → Bool) : Inv (initCfg (A n f) x) where
  id _ := rfl
  dc _ _ h := by simp [D, initCfg] at h
  cr _ _ h := by simp [Cv, initCfg] at h
  cval _ _ h := by simp [Cv, initCfg] at h
  loc z := ⟨Nat.zero_le _, z, rfl⟩

lemma inv_reach (x : Fin n → Bool) (α : List (Ev n)) : Inv (run (initCfg (A n f) x) α) :=
  (inv_init x).reach α

end Podc.RecoverableHierarchy.Fig2
