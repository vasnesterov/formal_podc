import Papers.PODC2026.LockFreeLinearProbing.Step

/-!
# Frame lemmas for the invariant `Inv`

A step of process `p` changes only `p`'s local state and one cell `x`. This file proves, field by
field, that the invariant `Inv` survives such an update under explicit side conditions.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] (h : K → Fin m)
variable {P : Type} [DecidableEq P]

/-- The configuration after process `p` moves to local state `l'` and cell `x` becomes `c'`. -/
def upd (C : Cfg K m P) (p : P) (l' : Loc K m) (x : Fin m) (c' : Cell K × List P) : Cfg K m P :=
  { C with loc := update C.loc p l', mem := update C.mem x c' }

@[simp] lemma upd_pend (C : Cfg K m P) p l' x c' : (upd C p l' x c').pend = C.pend := rfl
@[simp] lemma upd_loc_self (C : Cfg K m P) p l' x c' : (upd C p l' x c').loc p = l' := by
  simp [upd]
lemma upd_loc_ne (C : Cfg K m P) {p q} l' x c' (hq : q ≠ p) : (upd C p l' x c').loc q = C.loc q := by
  simp [upd, hq]
@[simp] lemma upd_mem_self (C : Cfg K m P) p l' x c' : (upd C p l' x c').mem x = c' := by
  simp [upd]
lemma upd_mem_ne (C : Cfg K m P) p l' {x y} c' (hy : y ≠ x) : (upd C p l' x c').mem y = C.mem y := by
  simp [upd, hy]

@[simp] lemma upd_val_self (C : Cfg K m P) p l' x c' : (upd C p l' x c').val x = c'.1 := by
  simp [Cfg.val]
lemma upd_val_ne (C : Cfg K m P) p l' {x y} c' (hy : y ≠ x) : (upd C p l' x c').val y = C.val y := by
  simp [Cfg.val, upd_mem_ne _ _ _ _ hy]
@[simp] lemma upd_lks_self (C : Cfg K m P) p l' x c' : (upd C p l' x c').lks x = c'.2 := by
  simp [Cfg.lks]
lemma upd_lks_ne (C : Cfg K m P) p l' {x y} c' (hy : y ≠ x) : (upd C p l' x c').lks y = C.lks y := by
  simp [Cfg.lks, upd_mem_ne _ _ _ _ hy]

/-- The cells an owner may hold. -/
def OwnCell (v : K) (w : Cell K) : Prop :=
  w = .key v .tent ∨ w = .key v .reval ∨ w = .deleted ∨ w = .collided

/-- The new value of cell `x` (and of all others) is never `EMPTY` unless it was. -/
def NoNewEmpty (C : Cfg K m P) (x : Fin m) (c' : Cell K × List P) : Prop :=
  c'.1 = .empty → C.val x = .empty

section
variable {h} {N : ℕ} {ts : P → ℕ} {C : Cfg K m P} {p : P} {l' : Loc K m} {x : Fin m}
  {c' : Cell K × List P}

lemma mem_val_upd (y : Fin m) :
    (upd C p l' x c').val y = if y = x then c'.1 else C.val y := by
  by_cases hy : y = x
  · subst hy; simp
  · simp [upd_val_ne _ _ _ _ hy, hy]

lemma loc_upd (q : P) : (upd C p l' x c').loc q = if q = p then l' else C.loc q := by
  by_cases hq : q = p
  · subst hq; simp
  · simp [upd_loc_ne _ _ _ _ hq, hq]

lemma empty_of_upd (hE : NoNewEmpty C x c') {y : Fin m}
    (hy : (upd C p l' x c').val y = .empty) : C.val y = .empty := by
  rw [mem_val_upd] at hy; split_ifs at hy with h1
  · subst h1; exact hE hy
  · exact hy

lemma idle_upd (hI : Inv h N ts C) (hp : C.pend p ≠ none) :
    ∀ q, (upd C p l' x c').pend q = none → ((upd C p l' x c').loc q).pc = .idle := by
  intro q hq
  simp only [upd_pend] at hq
  have : q ≠ p := by rintro rfl; exact hp hq
  rw [upd_loc_ne _ _ _ _ this]; exact hI.idle q hq

lemma loc_upd_inv (hI : Inv h N ts C) (hl : LocInv l') : ∀ q, LocInv ((upd C p l' x c').loc q) := by
  intro q; rw [loc_upd]; split_ifs
  · exact hl
  · exact hI.loc q

/-- Links: the cell `x` keeps its value and gains `p` as a link (an `LL`), or is unchanged, or
is written (all links cleared). -/
def LinkShape (C : Cfg K m P) (p : P) (x : Fin m) (c' : Cell K × List P) : Prop :=
  c' = (C.val x, C.lks x) ∨ c' = (C.val x, if p ∈ C.lks x then C.lks x else p :: C.lks x) ∨
    c'.2 = []

lemma link_upd (hI : Inv h N ts C) (hs : LinkShape C p x c')
    (hp : ∀ y w, recorded l' = some (y, w) → p ∈ (upd C p l' x c').lks y →
      (upd C p l' x c').val y = w) :
    ∀ q y w, recorded ((upd C p l' x c').loc q) = some (y, w) →
      q ∈ (upd C p l' x c').lks y → (upd C p l' x c').val y = w := by
  intro q y w hr hq
  by_cases hqp : q = p
  · subst hqp; simp only [upd_loc_self] at hr; exact hp y w hr hq
  rw [upd_loc_ne _ _ _ _ hqp] at hr
  by_cases hy : y = x
  · subst hy
    simp only [upd_lks_self, upd_val_self] at hq ⊢
    rcases hs with hs | hs | hs
    · rw [hs] at hq ⊢; exact hI.link q y w hr hq
    · rw [hs] at hq ⊢
      simp only at hq ⊢
      split_ifs at hq
      · exact hI.link q y w hr hq
      · rcases List.mem_cons.1 hq with h1 | h1
        · exact absurd h1 hqp
        · exact hI.link q y w hr h1
    · rw [hs] at hq; simp at hq
  · rw [upd_lks_ne _ _ _ _ hy] at hq; rw [upd_val_ne _ _ _ _ hy]; exact hI.link q y w hr hq

lemma ts_lt_upd (hI : Inv h N ts C) (ts' : P → ℕ) (hts : ∀ q, ts' q = ts q ∨ ts' q = N) :
    ∀ q, ts' q < N + 1 := by
  intro q; rcases hts q with h1 | h1 <;> rw [h1]
  · exact Nat.lt_succ_of_lt (hI.ts_lt q)
  · exact Nat.lt_succ_self N

/-- Frame conditions of a step that does not change any cell value (`LL`, `VL`, failed `SC`). -/
structure Unchanged (C : Cfg K m P) (p : P) (l' : Loc K m) (x : Fin m) (c' : Cell K × List P) :
    Prop where
  val : c'.1 = C.val x
  links : ∀ q, q ≠ p → (q ∈ c'.2 ↔ q ∈ C.lks x)
  op : l'.op = (C.loc p).op
  isVal : l'.pc.isVal = (C.loc p).pc.isVal
  j : l'.pc.isVal → l'.j = (C.loc p).j

lemma Unchanged.mem_val (hu : Unchanged C p l' x c') (y : Fin m) :
    (upd C p l' x c').val y = C.val y := by
  rw [mem_val_upd]; split_ifs with h1
  · subst h1; exact hu.val
  · rfl

lemma Unchanged.mem_links (hu : Unchanged C p l' x c') (y : Fin m) (q : P) (hq : q ≠ p) :
    q ∈ (upd C p l' x c').lks y ↔ q ∈ C.lks y := by
  by_cases h1 : y = x
  · subst h1; simp only [upd_lks_self]; exact hu.links q hq
  · rw [upd_lks_ne _ _ _ _ h1]

/-- The structural fields survive a step that changes no cell value. -/
lemma struct_unchanged (hI : Inv h N ts C) (hu : Unchanged C p l' x c')
    (hp3 : (l'.pc.isIns ∨ l'.pc.isVal) → ∀ c, dist h l'.op.key c < dist h l'.op.key l'.j →
      C.val c ≠ .empty) :
    let C' := upd C p l' x c'
    (∀ q, (C'.loc q).pc.isVal →
      C'.val (C'.loc q).j = .key (C'.loc q).op.key .tent ∨
      C'.val (C'.loc q).j = .key (C'.loc q).op.key .reval ∨
      C'.val (C'.loc q).j = .deleted ∨ C'.val (C'.loc q).j = .collided) ∧
    (∀ q r, (C'.loc q).pc.isVal → (C'.loc r).pc.isVal → (C'.loc q).j = (C'.loc r).j → q = r) ∧
    (∀ c v t, C'.val c = .key v t → t ≠ .fin →
      ∃ q, (C'.loc q).pc.isVal ∧ (C'.loc q).j = c ∧ (C'.loc q).op.key = v) ∧
    (∀ c v t, C'.val c = .key v t → ∀ c', dist h v c' ≤ dist h v c → C'.val c' ≠ .empty) ∧
    (∀ q, ((C'.loc q).pc.isIns ∨ (C'.loc q).pc.isVal) → ∀ c',
      dist h (C'.loc q).op.key c' < dist h (C'.loc q).op.key (C'.loc q).j →
      C'.val c' ≠ .empty) ∧
    (∀ v c c', C'.val c = .key v .fin → C'.val c' = .key v .fin → c = c') := by
  intro C'
  have hm : ∀ y, C'.val y = C.val y := hu.mem_val
  -- the view of process `q` after the step
  have hv : ∀ q, (C'.loc q).pc.isVal = true →
      (C.loc q).pc.isVal = true ∧ (C'.loc q).j = (C.loc q).j ∧ (C'.loc q).op = (C.loc q).op := by
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp only [C', upd_loc_self] at hq ⊢
      exact ⟨hu.isVal ▸ hq, hu.j hq, hu.op⟩
    · simp only [C', upd_loc_ne _ _ _ _ hqp] at hq ⊢; simp [hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hv q hq
    rw [hm, h2, h3]; exact hI.own q h1
  · intro q r hq hr hqr
    obtain ⟨h1, h2, -⟩ := hv q hq
    obtain ⟨h1', h2', -⟩ := hv r hr
    exact hI.own_inj q r h1 h1' (h2 ▸ h2' ▸ hqr)
  · intro c v t hc ht
    rw [hm] at hc
    obtain ⟨q, hq1, hq2, hq3⟩ := hI.own2 c v t hc ht
    refine ⟨q, ?_⟩
    by_cases hqp : q = p
    · subst hqp
      simp only [C', upd_loc_self]
      have : l'.pc.isVal = true := hu.isVal ▸ hq1
      exact ⟨this, (hu.j this).trans hq2, by rw [hu.op]; exact hq3⟩
    · simp only [C', upd_loc_ne _ _ _ _ hqp]; exact ⟨hq1, hq2, hq3⟩
  · intro c v t hc c'' hd
    rw [hm] at hc ⊢; exact hI.p3 c v t hc c'' hd
  · intro q hq c'' hd
    rw [hm]
    by_cases hqp : q = p
    · subst hqp; simp only [C', upd_loc_self] at hq hd; exact hp3 hq c'' hd
    · simp only [C', upd_loc_ne _ _ _ _ hqp] at hq hd; exact hI.p3' q hq c'' hd
  · intro v c c'' hc hc'
    rw [hm] at hc hc'; exact hI.l4 v c c'' hc hc'

/-- The coverage fields survive a step that changes no cell value and no timestamp, provided
they hold for the stepping process `p` itself. -/
lemma cover_unchanged (hI : Inv h N ts C) (hu : Unchanged C p l' x c')
    (ha1 : ∀ J, J ≠ p → (C.loc J).pc.isVal → l'.pc.isVal →
      (C.loc J).op.key = l'.op.key → C.val (C.loc J).j = .key l'.op.key .tent →
      covers h l' (C.loc J).j → ts p < ts J)
    (hdoc : ∀ J, ((((l'.pc = .docRD ∨ l'.pc = .docSC) ∧ p ∉ (upd C p l' x c').lks l'.i) ∨
      l'.pc = .docRD2)) → J ≠ p → (C.loc J).pc.isVal → (C.loc J).j = l'.i →
      (C.loc J).op.key = l'.op.key → C.val l'.i = .key l'.op.key .tent → ts p < ts J)
    (hdoc_self : ((((l'.pc = .docRD ∨ l'.pc = .docSC) ∧ p ∉ (upd C p l' x c').lks l'.i) ∨
      l'.pc = .docRD2)) → l'.pc.isVal → l'.j = l'.i → False)
    (ha4 : l'.pc.isVal → C.val l'.j = .key l'.op.key .tent →
      ∀ c, covers h l' c → C.val c ≠ .key l'.op.key .fin) :
    let C' := upd C p l' x c'
    (∀ I J, I ≠ J → (C'.loc I).pc.isVal → (C'.loc J).pc.isVal →
      (C'.loc J).op.key = (C'.loc I).op.key →
      C'.val (C'.loc J).j = .key (C'.loc I).op.key .tent → covers h (C'.loc I) (C'.loc J).j →
      ts I < ts J) ∧
    (∀ I J, ((((C'.loc I).pc = .docRD ∨ (C'.loc I).pc = .docSC) ∧ I ∉ C'.lks (C'.loc I).i) ∨
      (C'.loc I).pc = .docRD2) → (C'.loc J).pc.isVal → (C'.loc J).j = (C'.loc I).i →
      (C'.loc J).op.key = (C'.loc I).op.key →
      C'.val (C'.loc I).i = .key (C'.loc I).op.key .tent → ts I < ts J) ∧
    (∀ J c, (C'.loc J).pc.isVal → C'.val (C'.loc J).j = .key (C'.loc J).op.key .tent →
      covers h (C'.loc J) c → C'.val c ≠ .key (C'.loc J).op.key .fin) := by
  intro C'
  have hm : ∀ y, C'.val y = C.val y := hu.mem_val
  have hJ : ∀ J, J ≠ p → C'.loc J = C.loc J := fun J hJ => upd_loc_ne _ _ _ _ hJ
  have hpv : (C'.loc p).pc.isVal = true → (C.loc p).pc.isVal = true ∧ (C'.loc p).j = (C.loc p).j
      ∧ (C'.loc p).op = (C.loc p).op := by
    intro hq; simp only [C', upd_loc_self] at hq ⊢
    exact ⟨hu.isVal ▸ hq, hu.j hq, hu.op⟩
  refine ⟨?_, ?_, ?_⟩
  · intro I J hIJ hIv hJv hk ht hc
    rw [hm] at ht
    by_cases hIp : I = p
    · subst hIp
      have hJp : J ≠ I := Ne.symm hIJ
      rw [hJ J hJp] at hJv hk ht hc
      simp only [C', upd_loc_self] at hIv hk ht hc
      exact ha1 J hJp hJv hIv hk ht hc
    · rw [hJ I hIp] at hIv hk ht hc
      by_cases hJp : J = p
      · subst hJp
        obtain ⟨h1, h2, h3⟩ := hpv hJv
        rw [h2] at ht hc; rw [h3] at hk
        exact hI.a1 I J hIJ hIv h1 hk ht hc
      · rw [hJ J hJp] at hJv hk ht hc
        exact hI.a1 I J hIJ hIv hJv hk ht hc
  · intro I J hd hJv hj hk ht
    rw [hm] at ht
    by_cases hIp : I = p
    · subst hIp
      simp only [C', upd_loc_self] at hd hj hk ht
      by_cases hJp : J = I
      · subst hJp
        simp only [C', upd_loc_self] at hJv hj
        exact (hdoc_self hd hJv hj).elim
      · rw [hJ J hJp] at hJv hj hk
        exact hdoc J hd hJp hJv hj hk ht
    · rw [hJ I hIp] at hd hj hk ht
      have hd' : ((((C.loc I).pc = .docRD ∨ (C.loc I).pc = .docSC) ∧ I ∉ C.lks (C.loc I).i) ∨
          (C.loc I).pc = .docRD2) := by
        rcases hd with ⟨h1, h2⟩ | h1
        · exact Or.inl ⟨h1, by rwa [hu.mem_links _ _ hIp] at h2⟩
        · exact Or.inr h1
      by_cases hJp : J = p
      · subst hJp
        obtain ⟨h1, h2, h3⟩ := hpv hJv
        rw [h2] at hj; rw [h3] at hk
        exact hI.doc I J hd' h1 hj hk ht
      · rw [hJ J hJp] at hJv hj hk
        exact hI.doc I J hd' hJv hj hk ht
  · intro J c hJv ht hc
    rw [hm] at ht ⊢
    by_cases hJp : J = p
    · subst hJp
      simp only [C', upd_loc_self] at hJv ht hc ⊢
      exact ha4 hJv ht c hc
    · rw [hJ J hJp] at hJv ht hc ⊢
      exact hI.a4 J c hJv ht hc

/-- All of `Inv` survives a step that changes no cell value and no timestamp, given the
obligations about the stepping process. -/
lemma inv_of_unchanged (hI : Inv h N ts C) (hp : C.pend p ≠ none) (hu : Unchanged C p l' x c')
    (hloc : LocInv l') (hshape : LinkShape C p x c')
    (hlink : ∀ y w, recorded l' = some (y, w) → p ∈ (upd C p l' x c').lks y →
      (upd C p l' x c').val y = w)
    (hp3 : (l'.pc.isIns ∨ l'.pc.isVal) → ∀ c, dist h l'.op.key c < dist h l'.op.key l'.j →
      C.val c ≠ .empty)
    (ha1 : ∀ J, J ≠ p → (C.loc J).pc.isVal → l'.pc.isVal →
      (C.loc J).op.key = l'.op.key → C.val (C.loc J).j = .key l'.op.key .tent →
      covers h l' (C.loc J).j → ts p < ts J)
    (hdoc : ∀ J, ((((l'.pc = .docRD ∨ l'.pc = .docSC) ∧ p ∉ (upd C p l' x c').lks l'.i) ∨
      l'.pc = .docRD2)) → J ≠ p → (C.loc J).pc.isVal → (C.loc J).j = l'.i →
      (C.loc J).op.key = l'.op.key → C.val l'.i = .key l'.op.key .tent → ts p < ts J)
    (hdoc_self : ((((l'.pc = .docRD ∨ l'.pc = .docSC) ∧ p ∉ (upd C p l' x c').lks l'.i) ∨
      l'.pc = .docRD2)) → l'.pc.isVal → l'.j = l'.i → False)
    (ha4 : l'.pc.isVal → C.val l'.j = .key l'.op.key .tent →
      ∀ c, covers h l' c → C.val c ≠ .key l'.op.key .fin)
    (hisc : l'.pc = .iSC → C.val l'.j = .empty → p ∈ (upd C p l' x c').lks l'.j) :
    Inv h (N + 1) ts (upd C p l' x c') := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := struct_unchanged hI hu hp3
  obtain ⟨c1, c2, c3⟩ := cover_unchanged hI hu ha1 hdoc hdoc_self ha4
  refine ⟨idle_upd hI hp, loc_upd_inv hI hloc, link_upd hI hshape hlink, s1, s2, s3, s4, s5,
    ts_lt_upd hI ts (fun _ => Or.inl rfl), c1, c2, c3, s6, ?_⟩
  intro q hq hE
  rw [hu.mem_val] at hE
  by_cases hqp : q = p
  · subst hqp; simp only [upd_loc_self] at hq hE ⊢; exact hisc hq hE
  · rw [upd_loc_ne _ _ _ _ hqp] at hq hE ⊢
    rw [Cfg.lks, ← Cfg.lks]
    have := (hu.mem_links (C.loc q).j q hqp).2 (hI.isc q hq hE)
    exact this

/-- A step that changes no cell value and leads to a non-owner state (scans, lookups, deletes,
free-cell search at its first cell). -/
lemma inv_of_unchanged_nonval (hI : Inv h N ts C) (hp : C.pend p ≠ none)
    (hu : Unchanged C p l' x c') (hloc : LocInv l') (hshape : LinkShape C p x c')
    (hlink : ∀ y w, recorded l' = some (y, w) → p ∈ (upd C p l' x c').lks y →
      (upd C p l' x c').val y = w)
    (hnv : l'.pc.isVal = false)
    (hins : l'.pc.isIns = true → l'.j = h l'.op.key)
    (hisc : l'.pc = .iSC → C.val l'.j = .empty → p ∈ (upd C p l' x c').lks l'.j) :
    Inv h (N + 1) ts (upd C p l' x c') := by
  have hnd : ¬ (((l'.pc = .docRD ∨ l'.pc = .docSC) ∧ p ∉ (upd C p l' x c').lks l'.i) ∨
      l'.pc = .docRD2) := by
    rintro (⟨h1 | h1, -⟩ | h1) <;> simp [h1, PC.isVal] at hnv
  refine inv_of_unchanged hI hp hu hloc hshape hlink ?_ ?_ ?_ ?_ ?_ hisc
  · rintro (h1 | h1) c hc
    · rw [hins h1, dist_self] at hc; exact absurd hc (Nat.not_lt_zero _)
    · simp [hnv] at h1
  · intro J _ _ h1; simp [hnv] at h1
  · intro J hd; exact absurd hd hnd
  · intro hd; exact absurd hd hnd
  · intro h1; simp [hnv] at h1

/-- A successful `SC` by `p` writing `w'` into a cell `x` that is not `p`'s own cell, where `w'`
is neither `EMPTY`, nor a tentative copy, nor a final copy (lines 86, 88, 93, 104). -/
lemma inv_of_write (hI : Inv h N ts C) (hp : C.pend p ≠ none) {w' : Cell K}
    (hsucc : p ∈ C.lks x) (hE' : w' ≠ .empty) (hnoTt : ∀ v, w' ≠ .key v .tent)
    (hnoF : ∀ v, w' ≠ .key v .fin)
    (hown : ∀ q, q ≠ p → (C.loc q).pc.isVal → (C.loc q).j = x → OwnCell (C.loc q).op.key w')
    (hkey : ∀ v t, w' = .key v t → ∃ t', C.val x = .key v t' ∧ t' ≠ .fin)
    (hop : l'.op = (C.loc p).op)
    (hval : l'.pc.isVal = (C.loc p).pc.isVal) (hj : l'.pc.isVal → l'.j = (C.loc p).j ∧ x ≠ l'.j)
    (hloc : LocInv l') (hrec : recorded l' = none)
    (hp3 : (l'.pc.isIns ∨ l'.pc.isVal) → ∀ c, dist h l'.op.key c < dist h l'.op.key l'.j →
      C.val c ≠ .empty)
    (ha1 : ∀ J, J ≠ p → (C.loc J).pc.isVal → l'.pc.isVal →
      (C.loc J).op.key = l'.op.key → (upd C p l' x (w', [])).val (C.loc J).j = .key l'.op.key .tent →
      covers h l' (C.loc J).j → ts p < ts J)
    (hdoc : ¬ (l'.pc = .docRD ∨ l'.pc = .docSC ∨ l'.pc = .docRD2))
    (ha4 : l'.pc.isVal → (upd C p l' x (w', [])).val l'.j = .key l'.op.key .tent →
      ∀ c, covers h l' c → (upd C p l' x (w', [])).val c ≠ .key l'.op.key .fin)
    (hnisc : l'.pc ≠ .iSC) :
    Inv h (N + 1) ts (upd C p l' x (w', [])) := by
  set C' := upd C p l' x (w', []) with hC'
  have hJ : ∀ J, J ≠ p → C'.loc J = C.loc J := fun J hJ => upd_loc_ne _ _ _ _ hJ
  have hmv : ∀ y, C'.val y = if y = x then w' else C.val y := fun y => by
    rw [hC', mem_val_upd]
  have hpv : (C'.loc p).pc.isVal = true → (C.loc p).pc.isVal = true ∧ (C'.loc p).j = (C.loc p).j
      ∧ (C'.loc p).op = (C.loc p).op ∧ x ≠ (C'.loc p).j := by
    intro hq; simp only [C', upd_loc_self] at hq ⊢
    exact ⟨hval ▸ hq, (hj hq).1, hop, (hj hq).2⟩
  -- owners' cells other than `x` keep their value
  have hEold : ∀ y, C'.val y = .empty → C.val y = .empty := by
    intro y hy; rw [hmv] at hy; split_ifs at hy
    · exact absurd hy hE'
    · exact hy
  refine ⟨idle_upd hI hp, loc_upd_inv hI hloc, ?_, ?_, ?_, ?_, ?_, ?_, ts_lt_upd hI ts
    (fun _ => Or.inl rfl), ?_, ?_, ?_, ?_, ?_⟩
  · apply link_upd hI (Or.inr (Or.inr rfl))
    intro y w hr; rw [hrec] at hr; cases hr
  · -- own
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨h1, h2, h3, h4⟩ := hpv hq
      rw [hmv, if_neg (Ne.symm h4), h2, h3]; exact hI.own q h1
    · rw [hJ q hqp] at hq ⊢
      rw [hmv]; split_ifs with hx
      · exact hown q hqp hq hx
      · exact hI.own q hq
  · intro q r hq hr hqr
    have key : ∀ q, (C'.loc q).pc.isVal = true → (C.loc q).pc.isVal = true ∧
        (C'.loc q).j = (C.loc q).j := by
      intro q hq; by_cases hqp : q = p
      · subst hqp; exact ⟨(hpv hq).1, (hpv hq).2.1⟩
      · rw [hJ q hqp] at hq ⊢; exact ⟨hq, rfl⟩
    obtain ⟨a1, a2⟩ := key q hq; obtain ⟨b1, b2⟩ := key r hr
    exact hI.own_inj q r a1 b1 (a2 ▸ b2 ▸ hqr)
  · intro c v t hc ht
    rw [hmv] at hc
    have hc' : ∃ t', C.val c = .key v t' ∧ t' ≠ .fin := by
      split_ifs at hc with hx
      · subst hx; exact hkey v t hc
      · exact ⟨t, hc, ht⟩
    obtain ⟨t', hc', ht'⟩ := hc'
    obtain ⟨q, hq1, hq2, hq3⟩ := hI.own2 c v t' hc' ht'
    refine ⟨q, ?_⟩
    by_cases hqp : q = p
    · subst hqp; simp only [C', upd_loc_self]
      have : l'.pc.isVal = true := hval ▸ hq1
      exact ⟨this, (hj this).1.trans hq2, by rw [hop]; exact hq3⟩
    · rw [hJ q hqp]; exact ⟨hq1, hq2, hq3⟩
  · intro c v t hc c'' hd hc''
    rw [hmv] at hc
    have hc' : ∃ t', C.val c = .key v t' := by
      split_ifs at hc with hx
      · subst hx; obtain ⟨t', h1, -⟩ := hkey v t hc; exact ⟨t', h1⟩
      · exact ⟨t, hc⟩
    obtain ⟨t', hc'⟩ := hc'
    exact hI.p3 c v t' hc' c'' hd (hEold c'' hc'')
  · intro q hq c hd hc
    by_cases hqp : q = p
    · subst hqp; simp only [C', upd_loc_self] at hq hd; exact hp3 hq c hd (hEold c hc)
    · rw [hJ q hqp] at hq hd; exact hI.p3' q hq c hd (hEold c hc)
  · -- a1
    intro I J hIJ hIv hJv hk ht hc
    by_cases hIp : I = p
    · subst hIp
      have hJp : J ≠ I := Ne.symm hIJ
      rw [hJ J hJp] at hJv hk ht hc
      simp only [C', upd_loc_self] at hIv hk ht hc
      exact ha1 J hJp hJv hIv hk ht hc
    · rw [hJ I hIp] at hIv hk ht hc
      by_cases hJp : J = p
      · subst hJp
        obtain ⟨h1, h2, h3, h4⟩ := hpv hJv
        rw [hmv, if_neg (Ne.symm h4)] at ht
        rw [h2] at ht hc; rw [h3] at hk
        exact hI.a1 I J hIJ hIv h1 hk ht hc
      · rw [hJ J hJp] at hJv hk ht hc
        rw [hmv] at ht; split_ifs at ht with hx
        · exact absurd ht (hnoTt _)
        · exact hI.a1 I J hIJ hIv hJv hk ht hc
  · -- doc
    intro I J hd hJv hjj hk ht
    by_cases hIp : I = p
    · subst hIp; simp only [C', upd_loc_self] at hd
      rcases hd with ⟨h1 | h1, -⟩ | h1 <;> simp [h1] at hdoc
    · rw [hJ I hIp] at hd hjj hk ht
      rw [hmv] at ht; split_ifs at ht with hx
      · exact absurd ht (hnoTt _)
      have hd' : ((((C.loc I).pc = .docRD ∨ (C.loc I).pc = .docSC) ∧ I ∉ C.lks (C.loc I).i) ∨
          (C.loc I).pc = .docRD2) := by
        rcases hd with ⟨h1, h2⟩ | h1
        · refine Or.inl ⟨h1, ?_⟩
          rwa [hC', upd_lks_ne _ _ _ _ hx] at h2
        · exact Or.inr h1
      by_cases hJp : J = p
      · subst hJp
        obtain ⟨h1, h2, h3, -⟩ := hpv hJv
        rw [h2] at hjj; rw [h3] at hk
        exact hI.doc I J hd' h1 hjj hk ht
      · rw [hJ J hJp] at hJv hjj hk
        exact hI.doc I J hd' hJv hjj hk ht
  · -- a4
    intro J c hJv ht hc
    by_cases hJp : J = p
    · subst hJp
      simp only [C', upd_loc_self] at hJv ht hc ⊢
      exact ha4 hJv ht c hc
    · rw [hJ J hJp] at hJv ht hc ⊢
      rw [hmv] at ht ⊢
      split_ifs with hx
      · exact hnoF _
      · rw [if_neg] at ht
        · exact hI.a4 J c hJv ht hc
        · intro hx'; rw [if_pos hx'] at ht; exact hnoTt _ ht
  · -- l4
    intro v c c'' hc hc''
    rw [hmv] at hc hc''
    split_ifs at hc hc'' with h1 h2 h2
    · exact h1.trans h2.symm
    · exact absurd hc (hnoF v)
    · exact absurd hc'' (hnoF v)
    · exact hI.l4 v c c'' hc hc''
  · -- isc
    intro q hq hE
    by_cases hqp : q = p
    · subst hqp; simp only [C', upd_loc_self] at hq; exact absurd hq hnisc
    · rw [hJ q hqp] at hq hE ⊢
      rw [hmv] at hE; split_ifs at hE with hx
      · exact absurd hE hE'
      · rw [hC', upd_lks_ne _ _ _ _ hx]; exact hI.isc q hq hE

end

end Podc.LockFreeLinearProbing
