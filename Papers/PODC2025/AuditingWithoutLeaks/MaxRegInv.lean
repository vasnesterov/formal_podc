import Papers.PODC2025.AuditingWithoutLeaks.MaxReg

/-!
# Invariants of Algorithm 2 (the pair history of `R`)

For every choice of coins `θ` and every finite execution `α` of `alg2 θ`, the final configuration
satisfies (`Inv.of_run`):

* `SN ≤ R.seq ≤ SN + 1` (paper, Lemma 25/27), hence every successful `R.compare&swap` moves
  `R.seq` from `s` to `s + 1`;
* the pairs successively stored in `R` form a *history* `h : ℕ → Pr` with `h 0 = v₀`, strictly
  increasing on `[0, R.seq]` (Invariant 26), `h R.seq = R.val`, and every `h t` is either `v₀` or
  the pair `(w, nc x k)` of a `writeMax(w)` invoked in `α` by a writer `x` (`Good`);
* the same holds for the contents of `M` and the pairs in the writers' local states.
-/

namespace Podc.AuditingWithoutLeaks.MaxReg

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au : Type} [DecidableEq W] [DecidableEq Au]

variable (m W Au) in
/-- Configurations of Algorithm 2. -/
abbrev Cfg := Config (amaxReg m) (MBO m) (Proc m W Au) (MLoc m)

variable (m W Au) in
/-- Labels of executions of Algorithm 2. -/
abbrev Lbl := Label (Proc m W Au) (amaxReg m)

/-- Contents of `R`. -/
def rOf (C : Cfg m W Au) : RVal m Pr := C.mem .R

/-- Contents of `SN`. -/
def snOf (C : Cfg m W Au) : ℕ := C.mem .SN

/-- Contents of `M`. -/
def mOf (C : Cfg m W Au) : Pr := C.mem .M

/-- The pair `v` is the initial pair or the input pair `(w, nc x k)` of a `writeMax(w)` invoked in
`α` by some writer `x`. -/
def Good (nc : W → ℕ → ℕ) (α : List (Lbl m W Au)) (v : Pr) : Prop :=
  v = v₀ ∨ ∃ x k, MOp.writeMax v.val ∈ opsOf α (Proc.wr x) ∧ v.nonce = nc x k

lemma Good.append {nc : W → ℕ → ℕ} {α : List (Lbl m W Au)} {v : Pr} (h : Good nc α v)
    (β : List (Lbl m W Au)) : Good nc (α ++ β) v := by
  rcases h with h | ⟨x, k, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, k, by rw [opsOf_append]; exact List.mem_append.2 (Or.inl h1), h2⟩

/-- The history of the pairs stored in `R` (for the triple `r` currently in `R`). -/
def Hist (G : Pr → Prop) (r : RVal m Pr) : Prop :=
  ∃ h : ℕ → Pr, h 0 = v₀ ∧ (∀ t < r.seq, h t < h (t + 1)) ∧ h r.seq = r.val ∧
    ∀ t ≤ r.seq, G (h t)

lemma Hist.mono {G G' : Pr → Prop} (hG : ∀ v, G v → G' v) {r : RVal m Pr} (h : Hist G r) :
    Hist G' r := by
  obtain ⟨f, h0, h1, h2, h3⟩ := h
  exact ⟨f, h0, h1, h2, fun t ht => hG _ (h3 t ht)⟩

lemma Hist.of_eq {G : Pr → Prop} {r r' : RVal m Pr} (h : Hist G r) (hs : r'.seq = r.seq)
    (hv : r'.val = r.val) : Hist G r' := by
  obtain ⟨f, h0, h1, h2, h3⟩ := h
  exact ⟨f, h0, hs ▸ h1, by rw [hs, hv, h2], hs ▸ h3⟩

/-- A successful compare&swap appends a larger good pair to the history. -/
lemma Hist.cas {G : Pr → Prop} {r : RVal m Pr} (h : Hist G r) {v : Pr} (hv : r.val < v)
    (hg : G v) (b : Fin m → Bool) : Hist G ⟨r.seq + 1, v, b⟩ := by
  obtain ⟨f, h0, h1, h2, h3⟩ := h
  refine ⟨fun t => if t ≤ r.seq then f t else v, by simp [h0], fun t ht => ?_, by simp, ?_⟩
  · simp only at ht
    by_cases ht' : t + 1 ≤ r.seq
    · simp only [show t ≤ r.seq by omega, ht', ↓reduceIte]; exact h1 t (by omega)
    · obtain rfl : t = r.seq := by omega
      simp only [le_refl, ↓reduceIte, h2]
      simp only [show ¬ (r.seq + 1 ≤ r.seq) by omega, ↓reduceIte]; exact hv
  · intro t ht
    simp only
    split_ifs with h'
    · exact h3 t h'
    · exact hg

/-- Clause of the writer invariant for lines 32–34. -/
def WC (G : Pr → Prop) (snv : ℕ) (M v : Pr) (sn : ℕ) (r : RVal m Pr) (mval : Pr) : Prop :=
  G v ∧ v ≤ M ∧ r.val < v ∧ v ≤ mval ∧ G mval ∧ sn = r.seq + 1 ∧ sn ≤ snv + 1

/-- The local-state invariant, given the set `G` of good pairs, `R.seq = rs`, `SN = snv` and
`M`. -/
def LocInv (G : Pr → Prop) (rs snv : ℕ) (M : Pr) : MLoc m → Prop
  | .rCAS _ sn _ => sn ≤ rs
  | .wM _ v => G v
  | .wSN _ v => G v ∧ v ≤ M
  | .wR _ v sn => G v ∧ v ≤ M ∧ sn ≤ snv + 1
  | .wHelpL _ v sn => G v ∧ v ≤ M ∧ sn ≤ rs
  | .wMR _ v sn r => G v ∧ v ≤ M ∧ r.val < v ∧ sn = r.seq + 1 ∧ sn ≤ snv + 1
  | .wV _ v sn r mval => WC G snv M v sn r mval
  | .wB _ v sn r mval _ => WC G snv M v sn r mval
  | .wCAS _ v sn r mval => WC G snv M v sn r mval
  | .wHelp _ sn => sn ≤ rs
  | .aV _ r _ => r.seq ≤ rs
  | .aB _ r _ _ _ => r.seq ≤ rs
  | .aCAS _ r => r.seq ≤ rs
  | _ => True

lemma WC.mono {G G' : Pr → Prop} (hG : ∀ v, G v → G' v) {snv snv' : ℕ} {M M' : Pr}
    (hs : snv ≤ snv') (hM : M ≤ M') {v : Pr} {sn : ℕ} {r : RVal m Pr} {mval : Pr}
    (h : WC G snv M v sn r mval) : WC G' snv' M' v sn r mval := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨hG _ h1, h2.trans hM, h3, h4, hG _ h5, h6, by omega⟩

lemma LocInv.mono {G G' : Pr → Prop} (hG : ∀ v, G v → G' v) {rs rs' snv snv' : ℕ} {M M' : Pr}
    (hr : rs ≤ rs') (hs : snv ≤ snv') (hM : M ≤ M') {l : MLoc m} (h : LocInv G rs snv M l) :
    LocInv G' rs' snv' M' l := by
  cases l with
  | rCAS _ sn _ => exact le_trans (b := rs) h hr
  | wM _ v => exact hG _ h
  | wSN _ v => exact ⟨hG _ h.1, h.2.trans hM⟩
  | wR _ v sn => exact ⟨hG _ h.1, h.2.1.trans hM, by have := h.2.2; omega⟩
  | wHelpL _ v sn => exact ⟨hG _ h.1, h.2.1.trans hM, by have := h.2.2; omega⟩
  | wMR _ v sn r =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨hG _ h1, h2.trans hM, h3, h4, by omega⟩
  | wV _ v sn r mval => exact WC.mono hG hs hM h
  | wB _ v sn r mval _ => exact WC.mono hG hs hM h
  | wCAS _ v sn r mval => exact WC.mono hG hs hM h
  | wHelp _ sn => exact le_trans (b := rs) h hr
  | aV _ r _ => exact le_trans (b := rs) h hr
  | aB _ r _ _ _ => exact le_trans (b := rs) h hr
  | aCAS _ r => exact le_trans (b := rs) h hr
  | _ => trivial

/-- The invariant of Algorithm 2 after the execution `α` (with nonces `nc`). -/
structure Inv (nc : W → ℕ → ℕ) (α : List (Lbl m W Au)) (C : Cfg m W Au) : Prop where
  sn_le : snOf C ≤ (rOf C).seq
  seq_le : (rOf C).seq ≤ snOf C + 1
  hist : Hist (Good nc α) (rOf C)
  goodM : Good nc α (mOf C)
  loc : ∀ p, LocInv (Good nc α) (rOf C).seq (snOf C) (mOf C) (C.loc p)

section Step

variable {nc : W → ℕ → ℕ} {α α' : List (Lbl m W Au)} {C C' : Cfg m W Au}

lemma Inv.assemble (hI : Inv nc α C) (hG : ∀ v, Good nc α v → Good nc α' v)
    (p : Proc m W Au) (hloc : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (hr : (rOf C).seq ≤ (rOf C').seq) (hs : snOf C ≤ snOf C') (hM : mOf C ≤ mOf C')
    (g1 : snOf C' ≤ (rOf C').seq) (g2 : (rOf C').seq ≤ snOf C' + 1)
    (g3 : Hist (Good nc α') (rOf C')) (g4 : Good nc α' (mOf C'))
    (hown : LocInv (Good nc α') (rOf C').seq (snOf C') (mOf C') (C'.loc p)) :
    Inv nc α' C' := by
  refine ⟨g1, g2, g3, g4, fun q => ?_⟩
  by_cases hq : q = p
  · subst hq; exact hown
  · rw [hloc q hq]; exact (hI.loc q).mono hG hr hs hM

/-- A step that does not change the memory. -/
lemma Inv.of_mem (hI : Inv nc α C) (hG : ∀ v, Good nc α v → Good nc α' v)
    (p : Proc m W Au) (hloc : ∀ q, q ≠ p → C'.loc q = C.loc q) (hm : C'.mem = C.mem)
    (hown : LocInv (Good nc α') (rOf C).seq (snOf C) (mOf C) (C'.loc p)) :
    Inv nc α' C' := by
  have hR : rOf C' = rOf C := by simp [rOf, hm]
  have hS : snOf C' = snOf C := by simp [snOf, hm]
  have hMM : mOf C' = mOf C := by simp [mOf, hm]
  refine hI.assemble hG p hloc (by rw [hR]) (by rw [hS]) (by rw [hMM])
    (by rw [hR, hS]; exact hI.sn_le) (by rw [hR, hS]; exact hI.seq_le) (by rw [hR]; exact hI.hist.mono hG)
    (by rw [hMM]; exact hG _ hI.goodM) (by rw [hR, hS, hMM]; exact hown)

/-- A step whose only memory effect is `SN.compare&swap(sn - 1, sn)` with `sn ≤ R.seq`. -/
lemma Inv.of_sncas (hI : Inv nc α C) (hG : ∀ v, Good nc α v → Good nc α' v)
    (p : Proc m W Au) (hloc : ∀ q, q ≠ p → C'.loc q = C.loc q) {sn : ℕ}
    (hsn : sn ≤ (rOf C).seq)
    (hm : C'.mem = Function.update C.mem MObj.SN
      ((casObject ℕ 0).δ (C.mem MObj.SN) (CASOp.cas (sn - 1) sn)).1)
    (hown : ∀ snv', snOf C ≤ snv' →
      LocInv (Good nc α') (rOf C).seq snv' (mOf C) (C'.loc p)) :
    Inv nc α' C' := by
  have hR : rOf C' = rOf C := by simp [rOf, hm]
  have hMM : mOf C' = mOf C := by simp [mOf, hm]
  have hS : snOf C' = if snOf C = sn - 1 then sn else snOf C := by
    simp only [snOf, hm, Function.update_self]
    split_ifs <;> simp_all
  have h1 := hI.sn_le
  have h2 := hI.seq_le
  have hS1 : snOf C ≤ snOf C' := by rw [hS]; split_ifs <;> omega
  have hS2 : snOf C' ≤ (rOf C).seq := by rw [hS]; split_ifs <;> omega
  refine hI.assemble hG p hloc (by rw [hR]) hS1 (by rw [hMM]) (by rw [hR]; exact hS2)
    (by rw [hR]; omega) (by rw [hR]; exact hI.hist.mono hG)
    (by rw [hMM]; exact hG _ hI.goodM) (by rw [hR, hMM]; exact hown _ hS1)

section Tau

variable {θ : Coins m W}

lemma tau_wr (hI : Inv θ.nc α C) {x : W} {i : MObj m} {o : (MBO m i).Op}
    {k : (MBO m i).Resp → MLoc m}
    (hact : (alg2 (Au := Au) θ).act (.wr x) (C.loc (.wr x)) = .access i o k)
    (hmem : C'.mem = Function.update C.mem i ((MBO m i).δ (C.mem i) o).1)
    (hloc : C'.loc = Function.update C.loc (.wr x) (k ((MBO m i).δ (C.mem i) o).2)) :
    Inv θ.nc α C' := by
  have h1 := hI.sn_le
  have h2 := hI.seq_le
  have hr := hI.loc (.wr x)
  have hlq : ∀ q, q ≠ Proc.wr x → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hG : ∀ v, Good θ.nc α v → Good θ.nc α v := fun _ h => h
  cases hl : C.loc (.wr x) <;> rw [hl] at hr <;>
    simp only [alg2, writerAct, hl, reduceCtorEq] at hact
  case wM k v =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    have hMM : mOf C' = max (mOf C) v := by simp [mOf, hmem]
    refine hI.assemble hG _ hlq (by rw [hR]) (by rw [hS]) (by rw [hMM]; exact le_max_left _ _)
      (by rw [hR, hS]; exact h1) (by rw [hR, hS]; exact h2) (by rw [hR]; exact hI.hist) ?_ ?_
    · rw [hMM]; rcases le_total (mOf C) v with h | h
      · rw [max_eq_right h]; exact hr
      · rw [max_eq_left h]; exact hI.goodM
    · simp only [hloc, Function.update_self, LocInv, hMM]
      exact ⟨hr, le_max_right _ _⟩
  case wSN k v =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine hI.of_mem hG _ hlq (by simp [hmem]) ?_
    simp only [hloc, Function.update_self, LocInv]
    exact ⟨hr.1, hr.2, by simp [snOf]⟩
  case wR k v sn =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3⟩ := hr
    refine hI.of_mem hG _ hlq (by simp [hmem]) ?_
    simp only [hloc, Function.update_self]
    change LocInv _ _ _ _ (if v ≤ (rOf C).val then MLoc.wHelp k (rOf C).seq
      else if sn ≤ (rOf C).seq then .wHelpL k v sn else .wMR k v sn (rOf C))
    split_ifs with ha hb
    · simp [LocInv]
    · exact ⟨hp1, hp2, hb⟩
    · exact ⟨hp1, hp2, lt_of_not_ge ha, by omega, hp3⟩
  case wHelpL k v sn =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3⟩ := hr
    refine hI.of_sncas hG _ hlq hp3 hmem fun snv' _ => ?_
    simp only [hloc, Function.update_self, LocInv]
    exact ⟨hp1, hp2⟩
  case wMR k v sn r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hr
    refine hI.of_mem hG _ hlq (by simp [hmem]) ?_
    simp only [hloc, Function.update_self, LocInv]
    exact ⟨hp1, hp2, hp3, hp2, hI.goodM, hp4, hp5⟩
  case wV k v sn r mval =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    have hMM : mOf C' = mOf C := by simp [mOf, hmem]
    refine hI.assemble hG _ hlq (by rw [hR]) (by rw [hS]) (by rw [hMM])
      (by rw [hR, hS]; exact h1) (by rw [hR, hS]; exact h2) (by rw [hR]; exact hI.hist)
      (by rw [hMM]; exact hI.goodM) ?_
    simp only [hloc, Function.update_self, hR, hS, hMM]
    cases todoOf θ.rnd r <;> exact hr
  case wB k v sn r mval todo =>
    cases todo with
    | nil => simp at hact
    | cons j rest =>
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      obtain rfl := eq_of_heq ho
      obtain rfl := eq_of_heq hk
      have hR : rOf C' = rOf C := by simp [rOf, hmem]
      have hS : snOf C' = snOf C := by simp [snOf, hmem]
      have hMM : mOf C' = mOf C := by simp [mOf, hmem]
      refine hI.assemble hG _ hlq (by rw [hR]) (by rw [hS]) (by rw [hMM])
        (by rw [hR, hS]; exact h1) (by rw [hR, hS]; exact h2) (by rw [hR]; exact hI.hist)
        (by rw [hMM]; exact hI.goodM) ?_
      simp only [hloc, Function.update_self, hR, hS, hMM]
      cases rest <;> exact hr
  case wCAS k v sn r mval =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hr
    by_cases hc : rOf C = r
    · subst hc
      have hR : rOf C' = ⟨(rOf C).seq + 1, mval, θ.rnd sn⟩ := by
        simp [rOf, hmem, hp6]
      have hS : snOf C' = snOf C := by simp [snOf, hmem]
      have hMM : mOf C' = mOf C := by simp [mOf, hmem]
      refine hI.assemble hG _ hlq (by rw [hR]; simp) (by rw [hS]) (by rw [hMM])
        (by rw [hR, hS]; simp only; omega) (by rw [hR, hS]; simp only; omega)
        (by rw [hR]; exact hI.hist.cas (lt_of_lt_of_le hp3 hp4) hp5 _)
        (by rw [hMM]; exact hI.goodM) ?_
      have : C'.loc (.wr x) = .wHelp k sn := by simp [hloc, rOf]
      simp only [this, LocInv, hR]; omega
    · have hR : rOf C' = rOf C := by simp [rOf, hmem, show C.mem .R ≠ r from hc]
      have hS : snOf C' = snOf C := by simp [snOf, hmem]
      have hMM : mOf C' = mOf C := by simp [mOf, hmem]
      refine hI.assemble hG _ hlq (by rw [hR]) (by rw [hS]) (by rw [hMM])
        (by rw [hR, hS]; exact h1) (by rw [hR, hS]; exact h2) (by rw [hR]; exact hI.hist)
        (by rw [hMM]; exact hI.goodM) ?_
      have : C'.loc (.wr x) = .wR k v sn := by simp [hloc, show C.mem .R ≠ r from hc]
      simp only [this, LocInv, hS, hMM]
      exact ⟨hp1, hp2, hp7⟩
  case wHelp k sn =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine hI.of_sncas hG _ hlq hr hmem fun snv' _ => ?_
    simp [hloc, LocInv]

lemma locInv_aNext {G : Pr → Prop} {rs snv : ℕ} {M : Pr} {A : Finset (Fin m × ℕ)}
    {r : RVal m Pr} (h : r.seq ≤ rs) (s : ℕ) : LocInv G rs snv M (aNext θ.rnd A r s) := by
  unfold aNext; split_ifs <;> exact h

lemma locInv_aVnext {G : Pr → Prop} {rs snv : ℕ} {M : Pr} {A : Finset (Fin m × ℕ)}
    {r : RVal m Pr} (h : r.seq ≤ rs) (s : ℕ) (val : Option ℕ) :
    LocInv G rs snv M (aVnext θ.rnd A r s val) := by
  unfold aVnext; split_ifs
  · exact h
  · exact locInv_aNext h _

lemma locInv_aBnext {G : Pr → Prop} {rs snv : ℕ} {M : Pr} {A : Finset (Fin m × ℕ)}
    {r : RVal m Pr} (h : r.seq ≤ rs) (s : ℕ) (val : Option ℕ) (j : Fin m) :
    LocInv G rs snv M (aBnext θ.rnd A r s val j) := by
  unfold aBnext; split_ifs
  · exact h
  · exact locInv_aNext h _

lemma tau_rd (hI : Inv θ.nc α C) {j : Fin m} {i : MObj m} {o : (MBO m i).Op}
    {k : (MBO m i).Resp → MLoc m}
    (hact : (alg2 (W := W) (Au := Au) θ).act (.rd j) (C.loc (.rd j)) = .access i o k)
    (hmem : C'.mem = Function.update C.mem i ((MBO m i).δ (C.mem i) o).1)
    (hloc : C'.loc = Function.update C.loc (.rd j) (k ((MBO m i).δ (C.mem i) o).2)) :
    Inv θ.nc α C' := by
  have h1 := hI.sn_le
  have h2 := hI.seq_le
  have hr := hI.loc (.rd j)
  have hlq : ∀ q, q ≠ Proc.rd j → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hG : ∀ v, Good θ.nc α v → Good θ.nc α v := fun _ h => h
  cases hl : C.loc (.rd j) <;> rw [hl] at hr <;>
    simp only [alg2, readerAct, hl, reduceCtorEq] at hact
  case rSN prev =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine hI.of_mem hG _ hlq (by simp [hmem]) ?_
    simp only [hloc, Function.update_self]
    split_ifs <;> (try split) <;> trivial
  case rFX prev y =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hR : rOf C' = { rOf C with bits := flip (rOf C).bits j } := by simp [rOf, hmem]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    have hMM : mOf C' = mOf C := by simp [mOf, hmem]
    refine hI.assemble hG _ hlq (by rw [hR]) (by rw [hS]) (by rw [hMM])
      (by rw [hR, hS]; exact h1) (by rw [hR, hS]; exact h2)
      (hI.hist.of_eq (by rw [hR]) (by rw [hR])) (by rw [hMM]; exact hI.goodM) ?_
    simp only [hloc, Function.update_self, LocInv]
    change (rOf C).seq ≤ (rOf C').seq
    rw [hR]
  case rCAS prev sn val =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine hI.of_sncas hG _ hlq hr hmem fun snv' _ => ?_
    simp [hloc, LocInv]

lemma tau_au (hI : Inv θ.nc α C) {a : Au} {i : MObj m} {o : (MBO m i).Op}
    {k : (MBO m i).Resp → MLoc m}
    (hact : (alg2 (W := W) (Au := Au) θ).act (.au a) (C.loc (.au a)) = .access i o k)
    (hmem : C'.mem = Function.update C.mem i ((MBO m i).δ (C.mem i) o).1)
    (hloc : C'.loc = Function.update C.loc (.au a) (k ((MBO m i).δ (C.mem i) o).2)) :
    Inv θ.nc α C' := by
  have hr := hI.loc (.au a)
  have hlq : ∀ q, q ≠ Proc.au a → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hG : ∀ v, Good θ.nc α v → Good θ.nc α v := fun _ h => h
  cases hl : C.loc (.au a) <;> rw [hl] at hr <;>
    simp only [alg2, auditorAct, hl, reduceCtorEq] at hact
  case aR A lsa =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine hI.of_mem hG _ hlq (by simp [hmem]) ?_
    simp only [hloc, Function.update_self]
    exact locInv_aNext (le_refl _) _
  case aV A r s =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine hI.of_mem hG _ hlq (by simp [hmem]) ?_
    simp only [hloc, Function.update_self]
    exact locInv_aVnext hr _ _
  case aB A r s val j =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine hI.of_mem hG _ hlq (by simp [hmem]) ?_
    simp only [hloc, Function.update_self]
    exact locInv_aBnext hr _ _ _
  case aCAS A r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine hI.of_sncas hG _ hlq hr hmem fun snv' _ => ?_
    simp [hloc, LocInv]

end Tau

/-- The local invariant survives a return step. -/
lemma locInv_ret {θ : Coins m W} {G : Pr → Prop} {rs snv : ℕ} {M : Pr} {p : Proc m W Au}
    {l l' : MLoc m} {r : (amaxReg m).Resp}
    (hact : (alg2 (W := W) (Au := Au) θ).act p l = .ret r l') (h : LocInv G rs snv M l) :
    LocInv G rs snv M l' := by
  cases p <;> cases l <;>
    simp only [alg2, readerAct, writerAct, auditorAct, reduceCtorEq, Action.ret.injEq] at hact
  all_goals first
    | (obtain ⟨-, rfl⟩ := hact; exact h)
    | skip
  case wr.wB k v sn r mval todo =>
    cases todo with
    | nil => simp only [Action.ret.injEq] at hact; obtain ⟨-, rfl⟩ := hact; exact h
    | cons j rest => simp at hact

/-- The local invariant survives an invocation step. -/
lemma locInv_invoke {nc : W → ℕ → ℕ} {α : List (Lbl m W Au)} {rs snv : ℕ} {M : Pr}
    {p : Proc m W Au} {l : MLoc m} {o : (amaxReg m).Op}
    (h : LocInv (Good nc (α ++ [.inv p o])) rs snv M l) :
    LocInv (Good nc (α ++ [.inv p o])) rs snv M (invoke nc p l o) := by
  cases p with
  | rd j => cases l <;> cases o <;> exact h
  | au a => cases l <;> cases o <;> exact h
  | wr x =>
    cases l <;> cases o <;> try (first | exact h | trivial)
    case wIdle.writeMax k w =>
      refine Or.inr ⟨x, k, ?_, rfl⟩
      rw [opsOf_append]
      exact List.mem_append.2 (Or.inr (by simp [opsOf]; rfl))

lemma Inv.mono {nc : W → ℕ → ℕ} {α α' : List (Lbl m W Au)} {C : Cfg m W Au} (hI : Inv nc α C)
    (hG : ∀ v, Good nc α v → Good nc α' v) : Inv nc α' C :=
  ⟨hI.sn_le, hI.seq_le, hI.hist.mono hG, hG _ hI.goodM, fun p => (hI.loc p).mono hG le_rfl le_rfl
    le_rfl⟩

/-- The invariant is preserved by every step. -/
theorem Inv.step {θ : Coins m W} {α : List (Lbl m W Au)} {C C' : Cfg m W Au}
    (hI : Inv θ.nc α C) {ℓ : Lbl m W Au} (h : (alg2 θ).step C ℓ = some C') :
    Inv θ.nc (α ++ [ℓ]) C' := by
  have hG : ∀ v, Good θ.nc α v → Good θ.nc (α ++ [ℓ]) v := fun v hv => hv.append _
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, hloc, hm⟩ := Impl.step_inv h
    refine hI.of_mem hG p (fun q hq => by simp [hloc, Function.update_of_ne hq]) hm ?_
    simp only [hloc, Function.update_self]
    exact locInv_invoke ((hI.loc p).mono hG le_rfl le_rfl le_rfl)
  | ret p r =>
    obtain ⟨-, -, hm, l, hact, hloc⟩ := Impl.step_ret h
    refine hI.of_mem hG p (fun q hq => by simp [hloc, Function.update_of_ne hq]) hm ?_
    simp only [hloc, Function.update_self]
    exact locInv_ret hact ((hI.loc p).mono hG le_rfl le_rfl le_rfl)
  | tau p =>
    obtain ⟨-, -, i, o, k, hact, hm, hloc⟩ := Impl.step_tau h
    refine Inv.mono ?_ hG
    cases p with
    | rd j => exact tau_rd hI hact hm hloc
    | wr x => exact tau_wr hI hact hm hloc
    | au a => exact tau_au hI hact hm hloc

theorem Inv.init (θ : Coins m W) : Inv θ.nc [] (alg2 (W := W) (Au := Au) θ).initCfg := by
  refine ⟨by simp [snOf, rOf, Impl.initCfg, alg2], by simp [snOf, rOf, Impl.initCfg, alg2],
    ⟨fun _ => v₀, rfl, fun t ht => by simp [rOf, Impl.initCfg, alg2] at ht,
      by simp [rOf, Impl.initCfg, alg2], fun _ _ => Or.inl rfl⟩,
    Or.inl (by simp [mOf, Impl.initCfg, alg2]), fun p => ?_⟩
  cases p <;> trivial

/-- The invariant holds after every finite execution, for every choice of coins. -/
theorem Inv.of_run {θ : Coins m W} {α : List (Lbl m W Au)} {C : Cfg m W Au}
    (h : (alg2 θ).run α = some C) : Inv θ.nc α C :=
  Impl.run_induction (Q := fun α C => Inv θ.nc α C) (Inv.init θ)
    (fun _ _ _ _ _ hI hs => hI.step hs) h

end Step

end Podc.AuditingWithoutLeaks.MaxReg
