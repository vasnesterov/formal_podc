import Papers.PODC2026.ConflictFreedom.Alg1Inv

/-!
# Algorithm 1: outputs, commits and the inputs of the GCA objects

* `IsOut C r t` / `IsCom C r t`: some process has returned (resp. committed) `t` from `GCA_r`;
* `Inv2 C`: every input to `GCA_r` is `t · cmd` where `t` is `ε` (`r = 1`) or an output of
  `GCA_{r-1}`; the registers `S[j]` hold `(0, ε)` or a pair `(r, t)` with `t` committed at
  round `r`;
* Lemma A.1 (`lemma_A1`): a trace committed at round `r` is a prefix of every output of every
  round `r' ≥ r`.
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

namespace Alg1

variable {A : ObjSpec} {n : ℕ}

/-- Some process has returned `t` from `GCA_r`. -/
def IsOut (C : Cfg A n) (r : ℕ) (t : Tr A n) : Prop :=
  ∃ i g, locAt (C.loc i) r = some g ∧ g.pc = 4 ∧ g.output.1 = t

/-- Some process has committed `t` at `GCA_r`. -/
def IsCom (C : Cfg A n) (r : ℕ) (t : Tr A n) : Prop :=
  ∃ i g, locAt (C.loc i) r = some g ∧ g.pc = 4 ∧ g.output.1 = t ∧ g.output.2 = true

/-- Admissible base of a proposal to `GCA_r`. -/
def BaseOK (C : Cfg A n) (r : ℕ) (t : Tr A n) : Prop :=
  (r = 1 ∧ t = ⊥) ∨ (2 ≤ r ∧ IsOut C (r - 1) t)

/-- Admissible content of a register `S[j]`. -/
def SV (C : Cfg A n) (v : ℕ × Tr A n) : Prop :=
  (v.1 = 0 ∧ v.2 = ⊥) ∨ (1 ≤ v.1 ∧ IsCom C v.1 v.2)

/-- Invariant on the GCA inputs and on the registers. -/
structure Inv2 (C : Cfg A n) : Prop where
  sv : ∀ j, SV C (C.mem (.S j))
  best : ∀ i j best, (C.loc i).phase = .readS j best → SV C best
  com : ∀ i, (C.loc i).phase = .writeS ∨ (C.loc i).phase = .done →
    IsCom C (C.loc i).r (C.loc i).s ∧ (C.loc i).cmd ∈ (C.loc i).s.supp
  inp : ∀ r i g, locAt (C.loc i) r = some g → ∃ t c, BaseOK C r t ∧ g.inp = t.snoc c
  cur : ∀ i g, (C.loc i).phase = .gca g →
    ∃ t, BaseOK C (C.loc i).r t ∧ g.inp = t.snoc (C.loc i).cmd

lemma IsCom.isOut {C : Cfg A n} {r : ℕ} {t : Tr A n} (h : IsCom C r t) : IsOut C r t := by
  obtain ⟨i, g, h1, h2, h3, -⟩ := h; exact ⟨i, g, h1, h2, h3⟩

/-- Returned local GCA states live in the ghost history. -/
lemma Inv1.hist_of_locAt {C : Cfg A n} (hI : Inv1 C) {i : Fin n} {r : ℕ}
    {g : GCA.Loc n (Tr A n)} (h : locAt (C.loc i) r = some g) (hpc : g.pc = 4) :
    (C.loc i).hist r = some g := by
  unfold locAt at h
  split at h
  · rename_i g' hg'
    split_ifs at h with hr
    · cases h; have := ((hI.loc i).gca _ hg').2.2; omega
    · exact h
  · exact h

lemma Inv1.locAt_of_hist {C : Cfg A n} (hI : Inv1 C) {i : Fin n} {r : ℕ}
    {g : GCA.Loc n (Tr A n)} (h : (C.loc i).hist r = some g) : locAt (C.loc i) r = some g := by
  unfold locAt
  split
  · rename_i g' hg'
    split_ifs with hr
    · subst hr; rw [((hI.loc i).gca _ hg').2.1] at h; cases h
    · exact h
  · exact h

lemma Inv1.one_le_of_locAt {C : Cfg A n} (hI : Inv1 C) {i : Fin n} {r : ℕ}
    {g : GCA.Loc n (Tr A n)} (h : locAt (C.loc i) r = some g) : 1 ≤ r := by
  unfold locAt at h
  split at h
  · rename_i g' hg'
    split_ifs at h with hr
    · subst hr; exact ((hI.loc i).gca _ hg').1
    · exact ((hI.loc i).hist_le r (by rw [h]; simp)).1
  · exact ((hI.loc i).hist_le r (by rw [h]; simp)).1

variable [Inhabited A.Resp] [Inhabited A.Op] [NeZero n]

/-- The ghost history only grows. -/
lemma hist_mono_step {C C' : Cfg A n} (hI : Inv1 C) {ℓ : Label (Fin n) A}
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {i : Fin n} {r : ℕ}
    {g : GCA.Loc n (Tr A n)} (hg : (C.loc i).hist r = some g) : (C'.loc i).hist r = some g := by
  by_cases hi : ℓ.proc = i
  swap
  · rw [(Impl.step_other h hi).1]; exact hg
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv h
    simp only [Label.proc] at hi; subst hi
    rw [hloc]; simpa [impl, invoke] using hg
  | ret p r' =>
    simp only [Label.proc] at hi; subst hi
    obtain ⟨-, -, hC'⟩ := step_ret_cases h (hI.loc p)
    rw [hC']; simpa using hg
  | tau p =>
    simp only [Label.proc] at hi; subst hi
    obtain ⟨-, -, hT⟩ := step_tau_cases h
    cases hT with
    | readS => simpa using hg
    | readLast => simpa [Loc.afterRead, Loc.startRound] using hg
    | gca0 => simpa using hg
    | gca1 => simpa using hg
    | gca2 => simpa using hg
    | gca3 g' hph hpc =>
      have hrn := ((hI.loc p).gca g' hph).2.1
      have hr : r ≠ (C.loc p).r := by rintro rfl; rw [hrn] at hg; cases hg
      simp only [setLoc_loc, Function.update_self]
      unfold Loc.afterGCA
      split_ifs <;> simp [Loc.startRound, Function.update_of_ne hr, hg]
    | writeS => simpa using hg

lemma IsOut.step {C C' : Cfg A n} (hI : Inv1 C) (hI' : Inv1 C') {ℓ : Label (Fin n) A}
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {r : ℕ} {t : Tr A n} (ho : IsOut C r t) :
    IsOut C' r t := by
  obtain ⟨i, g, h1, h2, h3⟩ := ho
  exact ⟨i, g, hI'.locAt_of_hist (hist_mono_step hI h (hI.hist_of_locAt h1 h2)), h2, h3⟩

lemma IsCom.step {C C' : Cfg A n} (hI : Inv1 C) (hI' : Inv1 C') {ℓ : Label (Fin n) A}
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {r : ℕ} {t : Tr A n} (ho : IsCom C r t) :
    IsCom C' r t := by
  obtain ⟨i, g, h1, h2, h3, h4⟩ := ho
  exact ⟨i, g, hI'.locAt_of_hist (hist_mono_step hI h (hI.hist_of_locAt h1 h2)), h2, h3, h4⟩

lemma BaseOK.step {C C' : Cfg A n} (hI : Inv1 C) (hI' : Inv1 C') {ℓ : Label (Fin n) A}
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {r : ℕ} {t : Tr A n} (ho : BaseOK C r t) :
    BaseOK C' r t := by
  rcases ho with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h2.step hI hI' h⟩

lemma SV.step {C C' : Cfg A n} (hI : Inv1 C) (hI' : Inv1 C') {ℓ : Label (Fin n) A}
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {v : ℕ × Tr A n} (ho : SV C v) :
    SV C' v := by
  rcases ho with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h2.step hI hI' h⟩

section Preserve

variable {C C' : Cfg A n} {ℓ : Label (Fin n) A}

/-- The per-process parts of `Inv2` for a process whose local state did not change. -/
structure Inv2At (C : Cfg A n) (i : Fin n) : Prop where
  best : ∀ j best, (C.loc i).phase = .readS j best → SV C best
  com : (C.loc i).phase = .writeS ∨ (C.loc i).phase = .done →
    IsCom C (C.loc i).r (C.loc i).s ∧ (C.loc i).cmd ∈ (C.loc i).s.supp
  inp : ∀ r g, locAt (C.loc i) r = some g → ∃ t c, BaseOK C r t ∧ g.inp = t.snoc c
  cur : ∀ g, (C.loc i).phase = .gca g → ∃ t, BaseOK C (C.loc i).r t ∧ g.inp = t.snoc (C.loc i).cmd

lemma Inv2.at (hJ : Inv2 C) (i : Fin n) : Inv2At C i :=
  ⟨hJ.best i, hJ.com i, fun r g => hJ.inp r i g, hJ.cur i⟩

lemma Inv2At.transfer (hI : Inv1 C) (hI' : Inv1 C')
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {i : Fin n} (hJ : Inv2At C i)
    (hl : C'.loc i = C.loc i) : Inv2At C' i := by
  refine ⟨fun j best hb => ?_, fun hp => ?_, fun r g hg => ?_, fun g hg => ?_⟩
  · rw [hl] at hb; exact (hJ.best j best hb).step hI hI' h
  · rw [hl] at hp ⊢; exact ⟨(hJ.com hp).1.step hI hI' h, (hJ.com hp).2⟩
  · rw [hl] at hg; obtain ⟨t, c, h1, h2⟩ := hJ.inp r g hg; exact ⟨t, c, h1.step hI hI' h, h2⟩
  · rw [hl] at hg ⊢; obtain ⟨t, h1, h2⟩ := hJ.cur g hg; exact ⟨t, h1.step hI hI' h, h2⟩

lemma Inv2.of_at (hsv : ∀ j, SV C (C.mem (.S j))) (hat : ∀ i, Inv2At C i) : Inv2 C :=
  ⟨hsv, fun i => (hat i).best, fun i => (hat i).com, fun r i g => (hat i).inp r g,
    fun i => (hat i).cur⟩

/-- Assemble `Inv2 C'` from the moving process `p` and unchanged others. -/
lemma Inv2.step_of (hJ : Inv2 C) (hI : Inv1 C) (hI' : Inv1 C')
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {p : Fin n}
    (hother : ∀ i, i ≠ p → C'.loc i = C.loc i)
    (hsv : ∀ j, SV C' (C'.mem (.S j))) (hp : Inv2At C' p) : Inv2 C' :=
  Inv2.of_at hsv fun i => by
    by_cases hi : i = p
    · subst hi; exact hp
    · exact (hJ.at i).transfer hI hI' h (hother i hi)

lemma sv_better {best v : ℕ × Tr A n} (h1 : SV C best) (h2 : SV C v) : SV C (better best v) := by
  rcases better_cases best v with h | h <;> rw [h] <;> assumption

lemma baseOK_of_sv {v : ℕ × Tr A n} (h : SV C v) : BaseOK C (v.1 + 1) v.2 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by omega, h2⟩
  · exact Or.inr ⟨by omega, by simpa using h2.isOut⟩

/-- A step inside `GCA_r` that does not change the input, the round or the history. -/
lemma gca_at (hJ : Inv2 C) (hI : Inv1 C) (hI' : Inv1 C')
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {p : Fin n} {g g' : GCA.Loc n (Tr A n)}
    (hph : (C.loc p).phase = .gca g) (hinp : g'.inp = g.inp)
    (hlp : C'.loc p = { C.loc p with phase := .gca g' }) : Inv2At C' p := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hlp]
  · intro _ _ h; cases h
  · simp
  · intro r g'' hg
    rw [locAt_gca_step (l' := { C.loc p with phase := .gca g' }) hph rfl rfl rfl] at hg
    split_ifs at hg with hr
    · simp only [Option.some.injEq] at hg; subst hg
      obtain ⟨t, c, h1, h2⟩ := hJ.inp r p g (by rw [locAt_gca hph]; simp [hr])
      exact ⟨t, c, h1.step hI hI' h, hinp.trans h2⟩
    · obtain ⟨t, c, h1, h2⟩ := hJ.inp r p g'' hg
      exact ⟨t, c, h1.step hI hI' h, h2⟩
  · rintro _ ⟨⟩
    obtain ⟨t, h1, h2⟩ := hJ.cur p g hph
    exact ⟨t, h1.step hI hI' h, hinp.trans h2⟩

theorem Inv2.step (hJ : Inv2 C) (hI : Inv1 C)
    (h : (impl (A := A) (n := n)).step C ℓ = some C') : Inv2 C' := by
  have hI' := hI.step h
  have hsv_same : (∀ j, C'.mem (.S j) = C.mem (.S j)) → ∀ j, SV C' (C'.mem (.S j)) :=
    fun hS j => by rw [hS j]; exact (hJ.sv j).step hI hI' h
  cases ℓ with
  | inv p o =>
    obtain ⟨hp, -, -, hloc, hmem⟩ := Impl.step_inv h
    have hidle := (hI.loc p).pend_iff.1 hp
    have hlp : C'.loc p = invoke p (C.loc p) o := by rw [hloc]; simp; rfl
    refine hJ.step_of hI hI' h (p := p) (fun i hi => by rw [hloc]; simp [hi])
      (hsv_same fun j => by rw [hmem]) ⟨?_, ?_, ?_, ?_⟩
    · rw [hlp]; rintro j best hb; simp only [invoke, Phase.readS.injEq] at hb
      rw [← hb.2]; exact Or.inl ⟨rfl, rfl⟩
    · rw [hlp]; simp [invoke]
    · intro r g hg
      rw [hlp, locAt_of_not_gca (by simp [invoke])] at hg
      obtain ⟨t, c, h1, h2⟩ := hJ.inp r p g (by rw [locAt_of_not_gca (by simp [hidle])]; exact hg)
      exact ⟨t, c, h1.step hI hI' h, h2⟩
    · rw [hlp]; simp [invoke]
  | ret p r' =>
    obtain ⟨hdone, -, hC'⟩ := step_ret_cases h (hI.loc p)
    have hlp : C'.loc p = { C.loc p with phase := .idle } := by rw [hC']; simp
    refine hJ.step_of hI hI' h (p := p) (fun i hi => by rw [hC']; simp [hi])
      (hsv_same fun j => by rw [hC']) ⟨?_, ?_, ?_, ?_⟩
    · rw [hlp]; simp
    · rw [hlp]; simp
    · intro r g hg
      rw [hlp, locAt_of_not_gca (by simp)] at hg
      obtain ⟨t, c, h1, h2⟩ := hJ.inp r p g (by rw [locAt_of_not_gca (by simp [hdone])]; exact hg)
      exact ⟨t, c, h1.step hI hI' h, h2⟩
    · rw [hlp]; simp
  | tau p =>
    obtain ⟨hpn, -, hT⟩ := step_tau_cases h
    have hL := hI.loc p
    have hJp := (hJ.at p)
    cases hT with
    | readS j best hj hph hlt =>
      refine hJ.step_of hI hI' h (p := p) (fun i hi => by simp [hi]) (hsv_same fun _ => rfl)
        ⟨?_, ?_, ?_, ?_⟩ <;> simp only [setLoc_loc, Function.update_self]
      · rintro j' b' hb; simp only [Phase.readS.injEq] at hb; rw [← hb.2]
        exact (sv_better (hJ.best p j best hph) (hJ.sv _)).step hI hI' h
      · simp
      · intro r g hg
        rw [locAt_of_not_gca (by simp)] at hg
        obtain ⟨t, c, h1, h2⟩ := hJ.inp r p g (by rw [locAt_of_not_gca (by simp [hph])]; exact hg)
        exact ⟨t, c, h1.step hI hI' h, h2⟩
      · simp
    | readLast j best hj hph hlt =>
      have hb := sv_better (hJ.best p j best hph) (hJ.sv ⟨j, hj⟩)
      set b := better best (C.mem (.S ⟨j, hj⟩)) with hbdef
      have hbase := (baseOK_of_sv hb).step hI hI' h
      refine hJ.step_of hI hI' h (p := p) (fun i hi => by simp [hi]) (hsv_same fun _ => rfl)
        ⟨?_, ?_, ?_, ?_⟩ <;> simp only [setLoc_loc, Function.update_self]
      · simp [Loc.afterRead, Loc.startRound]
      · simp [Loc.afterRead, Loc.startRound]
      · intro r g hg
        rw [locAt_gca (g := GCA.Loc.init (b.2.snoc (C.loc p).cmd))
          (by simp [Loc.afterRead, Loc.startRound])] at hg
        split_ifs at hg with hr
        · simp only [Option.some.injEq] at hg; subst hg; refine ⟨_, _, ?_, rfl⟩; rw [hr]; simpa [Loc.afterRead, Loc.startRound] using hbase
        · obtain ⟨t, c, h1, h2⟩ := hJ.inp r p g
            (by rw [locAt_of_not_gca (by simp [hph])]; simpa [Loc.afterRead, Loc.startRound] using hg)
          exact ⟨t, c, h1.step hI hI' h, h2⟩
      · rintro g hg; simp only [Loc.afterRead, Loc.startRound, Phase.gca.injEq] at hg
        subst hg; exact ⟨_, by simpa [Loc.afterRead, Loc.startRound] using hbase, rfl⟩
    | gca0 g hph hpc =>
      exact hJ.step_of hI hI' h (p := p) (fun i hi => by simp [hi])
        (hsv_same fun j => by simp [Function.update_of_ne (show Obj.S j ≠ Obj.A (C.loc p).r
          by simp)]) (gca_at (g' := { g with pc := 1 }) hJ hI hI' h hph rfl (by simp))
    | gca1 g hph hpc =>
      exact hJ.step_of hI hI' h (p := p) (fun i hi => by simp [hi]) (hsv_same fun _ => rfl)
        (gca_at (g' := { g with pc := 2, av := C.mem (.A (C.loc p).r) }) hJ hI hI' h hph rfl
          (by simp))
    | gca2 g hph hpc =>
      exact hJ.step_of hI hI' h (p := p) (fun i hi => by simp [hi])
        (hsv_same fun j => by simp [Function.update_of_ne (show Obj.S j ≠ Obj.B (C.loc p).r
          by simp)]) (gca_at (g' := { g with pc := 3 }) hJ hI hI' h hph rfl (by simp))
    | gca3 g hph hpc =>
      have hr1 := (hL.gca g hph).1
      set g4 : GCA.Loc n (Tr A n) := { g with pc := 4, bv := C.mem (.B (C.loc p).r) } with hg4
      have hginp : ∃ t c, BaseOK (setLoc C p ((C.loc p).afterGCA g4)) (C.loc p).r t ∧ g4.inp = t.snoc c := by
        obtain ⟨t, c, h1, h2⟩ := hJ.inp (C.loc p).r p g (by rw [locAt_gca hph]; simp)
        exact ⟨t, c, h1.step hI hI' h, h2⟩
      have hold : ∀ r g', r ≠ (C.loc p).r → (C.loc p).hist r = some g' →
          ∃ t c, BaseOK (setLoc C p ((C.loc p).afterGCA g4)) r t ∧ g'.inp = t.snoc c := fun r g' hr hg' => by
        obtain ⟨t, c, h1, h2⟩ := hJ.inp r p g' (by rw [locAt_gca hph]; simp [hr, hg'])
        exact ⟨t, c, h1.step hI hI' h, h2⟩
      refine hJ.step_of hI hI' h (p := p) (fun i hi => by simp [hi]) (hsv_same fun _ => rfl) ?_
      by_cases hex : g4.output.2 = true ∧ (C.loc p).cmd ∈ g4.output.1.supp
      · have hl' : (C.loc p).afterGCA g4 = { C.loc p with
            hist := Function.update (C.loc p).hist (C.loc p).r (some g4), s := g4.output.1,
            phase := .writeS, cr := Function.update (C.loc p).cr (C.loc p).seq (C.loc p).r } := by
          simp [Loc.afterGCA, hex]
        have hloc4 : locAt ((setLoc C p ((C.loc p).afterGCA g4)).loc p) (C.loc p).r = some g4 := by
          simp only [setLoc_loc, Function.update_self, hl']
          rw [locAt_of_not_gca (by simp)]; simp
        have hlp : (setLoc C p ((C.loc p).afterGCA g4)).loc p = { C.loc p with
            hist := Function.update (C.loc p).hist (C.loc p).r (some g4), s := g4.output.1,
            phase := .writeS, cr := Function.update (C.loc p).cr (C.loc p).seq (C.loc p).r } := by
          simp [hl']
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hlp]
        · intro _ _ h; cases h
        · intro _; exact ⟨⟨p, g4, hloc4, rfl, rfl, hex.1⟩, by simpa using hex.2⟩
        · intro r g' hg
          rw [locAt_of_not_gca (by simp)] at hg
          by_cases hr : r = (C.loc p).r
          · subst hr; simp only [Function.update_self, Option.some.injEq] at hg; subst hg
            exact hginp
          · simp only [Function.update_of_ne hr] at hg; exact hold r g' hr hg
        · intro _ h; cases h
      · have hl' : (C.loc p).afterGCA g4 = { (C.loc p).startRound (C.loc p).r g4.output.1 with
            hist := Function.update (C.loc p).hist (C.loc p).r (some g4) } := by
          simp only [Loc.afterGCA, hex, if_false]
        have hloc4 : locAt ((setLoc C p ((C.loc p).afterGCA g4)).loc p) (C.loc p).r = some g4 := by
          simp only [setLoc_loc, Function.update_self, hl']
          rw [locAt_eq_hist_of_ne (by simp [Loc.startRound])]; simp
        have hbase : BaseOK (setLoc C p ((C.loc p).afterGCA g4)) ((C.loc p).r + 1) g4.output.1 :=
          Or.inr ⟨by omega, ⟨p, g4, by simpa using hloc4, rfl, rfl⟩⟩
        have hlp : (setLoc C p ((C.loc p).afterGCA g4)).loc p =
            { (C.loc p).startRound (C.loc p).r g4.output.1 with
              hist := Function.update (C.loc p).hist (C.loc p).r (some g4) } := by
          simp [hl']
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hlp]
        · intro _ _ h; cases h
        · simp [Loc.startRound]
        · intro r g' hg
          rw [locAt_gca (g := GCA.Loc.init (g4.output.1.snoc (C.loc p).cmd))
            (by simp [Loc.startRound])] at hg
          split_ifs at hg with hr
          · simp only [Option.some.injEq] at hg; subst hg
            refine ⟨_, _, ?_, rfl⟩; rw [hr]; simpa [Loc.startRound] using hbase
          · by_cases hr' : r = (C.loc p).r
            · subst hr'; simp only [Function.update_self, Option.some.injEq] at hg; subst hg
              exact hginp
            · simp only [Function.update_of_ne hr'] at hg; exact hold r g' hr' hg
        · rintro _ hg; simp only [Loc.startRound, Phase.gca.injEq] at hg; subst hg
          exact ⟨_, by simpa [Loc.startRound] using hbase, rfl⟩
    | writeS hph =>
      obtain ⟨hcom, hcmd⟩ := hJ.com p (Or.inl hph)
      have hcom' := hcom.step hI hI' h
      have hr1 : 1 ≤ (C.loc p).r := by
        obtain ⟨i, g, h1, -⟩ := hcom; exact hI.one_le_of_locAt h1
      refine hJ.step_of hI hI' h (p := p) (fun i hi => by simp [hi]) (fun j => ?_) ⟨?_, ?_, ?_, ?_⟩
      · by_cases hj : j = p
        · subst hj; simp only [setMemLoc_mem, Function.update_self]
          exact Or.inr ⟨hr1, by simpa using hcom'⟩
        · simp only [setMemLoc_mem]
          rw [Function.update_of_ne (show Obj.S j ≠ Obj.S p by simpa using hj)]
          exact (hJ.sv j).step hI hI' h
      · simp
      · intro _; simpa using ⟨hcom', hcmd⟩
      · intro r g hg
        simp only [setMemLoc_loc, Function.update_self] at hg
        rw [locAt_of_not_gca (by simp)] at hg
        obtain ⟨t, c, h1, h2⟩ := hJ.inp r p g (by rw [locAt_of_not_gca (by simp [hph])]; exact hg)
        exact ⟨t, c, h1.step hI hI' h, h2⟩
      · simp

end Preserve

theorem inv2_init : Inv2 (impl (A := A) (n := n)).initCfg := by
  refine ⟨fun j => Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩ <;> simp [Impl.initCfg, impl, locAt]

/-- `Inv1` and `Inv2` hold in every reachable configuration. -/
theorem inv12_of_run {α : List (Label (Fin n) A)} {C : Cfg A n}
    (h : (impl (A := A) (n := n)).run α = some C) : Inv1 C ∧ Inv2 C :=
  Impl.invariant_of_run (Inv := fun C => Inv1 C ∧ Inv2 C) ⟨inv1_init, inv2_init⟩
    (fun _ _ _ hI hs => ⟨hI.1.step hs, hI.2.step hI.1 hs⟩) h

/-- Lemma A.1 of [KST26]: if `s` is committed at `GCA_r`, every trace returned by `GCA_{r'}`,
`r' ≥ r`, extends `s`. -/
theorem lemma_A1 {C : Cfg A n} (hI : Inv1 C) (hJ : Inv2 C) {r : ℕ} {s : Tr A n}
    (hs : IsCom C r s) : ∀ k, ∀ t, IsOut C (r + k) t → s ≤ t := by
  obtain ⟨i, g, hg, hpc, hout, hc⟩ := hs
  have hr1 := hI.one_le_of_locAt hg
  intro k
  induction k with
  | zero =>
    rintro t ⟨j, g', hg', hpc', rfl⟩
    have := GCA.adoption_of_reach (hI.reach r) i g j g' ⟨hg, hpc⟩ ⟨hg', hpc'⟩
      (by rw [hc])
    rwa [hout] at this
  | succ k ih =>
    rintro t ⟨j, g', hg', hpc', rfl⟩
    refine GCA.commonPrefix_of_reach (hI.reach (r + (k + 1))) s ?_ j g' ⟨hg', hpc'⟩
    rintro y ⟨j', l', hl', rfl⟩
    obtain ⟨t0, c, hb, heq⟩ := hJ.inp _ j' l' hl'
    rw [heq]
    rcases hb with ⟨h1, -⟩ | ⟨-, hb⟩
    · omega
    · exact (ih t0 (by simpa [show r + (k + 1) - 1 = r + k by omega] using hb)).trans
        (NTrace.le_snoc _ _)

/-- Lemma A.1, in the form `r ≤ r'`. -/
theorem lemma_A1' {C : Cfg A n} (hI : Inv1 C) (hJ : Inv2 C) {r r' : ℕ} {s t : Tr A n}
    (hs : IsCom C r s) (hrr : r ≤ r') (ht : IsOut C r' t) : s ≤ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrr
  exact lemma_A1 hI hJ hs k t ht

end Alg1

end Podc.ConflictFreedom
