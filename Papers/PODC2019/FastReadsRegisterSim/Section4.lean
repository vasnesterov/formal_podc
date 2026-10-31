import Papers.PODC2019.FastReadsRegisterSim.Section4Exec

/-!
# Section 4: no atomic simulation with fast reads for two readers (Theorem 4.1)

`Setting I w r₁ r₂ m` collects the hypotheses: an atomic, obstruction-free simulation with writer
`w` and two readers `r₁ ≠ r₂` whose first reads are described by complete decision trees of depth
`m ≥ 2` (`ReaderHyp`: `TreeHyp` plus "`val` is a bijection from strings of length `m` to `V`").
Let `ρ` be the root register of the tree `T₁` of `r₁`.

* `caseA` — if some root-to-leaf path of `T₂` avoids `ρ`: the argument of the paper's proof of
  Lemma 4.2 (two reads around the first step of `W₁` that flips `ρ`) gives a contradiction;
* `caseB` — if every root-to-leaf path of `T₂` reads `ρ`: the argument of the main part of the
  paper's proof of Theorem 4.1 (writes `W₀(a) W₁(z) W₂(b)`, Cases 1 and 2) gives a contradiction.

The paper only proves (Lemma 4.2) that `T₁` and `T₂` have the same root and then runs the second
argument; its proof of Lemma 4.2 needs a path of `T₂` avoiding `ρ`, whose existence it justifies
incorrectly (see `Lemma42Gap.lean`). The case split above repairs the proof.
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι P L : Type} [DecidableEq P] [DecidableEq ι]

namespace Sec4

/-- The first read of `r` is a complete decision tree of depth `m` whose leaves are labelled
bijectively by the values. -/
structure ReaderHyp (I : Sim V v₀ ι P L) (r : P) (m : ℕ) : Prop where
  tree : TreeHyp I r m
  inj : ∀ u u' : List Bool, u.length = m → u'.length = m → vl I r u = vl I r u' → u = u'
  surj : ∀ v, ∃ u : List Bool, u.length = m ∧ vl I r u = v

/-- Hypotheses of the core of Theorem 4.1. -/
structure Setting (I : Sim V v₀ ι P L) (w r₁ r₂ : P) (m : ℕ) : Prop where
  h1w : r₁ ≠ w
  h2w : r₂ ≠ w
  h12 : r₁ ≠ r₂
  hw : ∀ v, I.allowed w (.write v)
  hr₁ : I.allowed r₁ .read
  hr₂ : I.allowed r₂ .read
  hof : I.ObstructionFree
  hatom : I.Atomic w
  hm : 2 ≤ m
  R₁ : ReaderHyp I r₁ m
  R₂ : ReaderHyp I r₂ m

variable {I : Sim V v₀ ι P L} {w r₁ r₂ r : P} {m : ℕ}

/-- The bit read at depth `j` along the path at memory `M`. -/
lemma bit_at {M : Mem ι} {j : ℕ} (hj : j < m) {i : ι}
    (hi : RdN (I.act r) (nd I r ((pth I r M m).take j)) i) :
    (pth I r M m)[j]? = some (M i) := by
  rw [path_take M (by omega)] at hi
  exact path_getElem M hj hi

lemma pth_take (M : Mem ι) {j j' : ℕ} (h : j ≤ j') : (pth I r M j').take j = pth I r M j :=
  path_take M h

lemma pth_eq_of_vl (R : ReaderHyp I r m) {M : Mem ι} {u : List Bool} (hu : u.length = m)
    (h : vl I r (pth I r M m) = vl I r u) : pth I r M m = u :=
  R.inj _ _ (length_path _ _) hu h

lemma vl_ne_of_getElem (R : ReaderHyp I r m) {u u' : List Bool} (hu : u.length = m)
    (hu' : u'.length = m) {j : ℕ} (hne : u[j]? ≠ u'[j]?) : vl I r u ≠ vl I r u' := by
  intro h; exact hne (by rw [R.inj u u' hu hu' h])

/-! ## Case A: some path of `T₂` avoids the root of `T₁` -/

theorem caseA (S : Setting I w r₁ r₂ m) {ρ : ι} (hρ : RdN (I.act r₁) (nd I r₁ []) ρ)
    {u₂ : List Bool} (hu₂ : u₂.length = m)
    (havoid : ∀ j < m, ∀ i, RdN (I.act r₂) (nd I r₂ (u₂.take j)) i → i ≠ ρ) : False := by
  have hm0 : 0 < m := by have := S.hm; omega
  set z := vl I r₂ u₂ with hz
  obtain ⟨u₁, hu₁, hz₁⟩ := S.R₁.surj z
  obtain ⟨c, t, rfl⟩ := List.exists_cons_of_length_pos (show 0 < u₁.length by omega)
  set ua : List Bool := (!c) :: List.replicate (m - 1) false with hua
  have hual : ua.length = m := by simp [hua]; omega
  set a := vl I r₁ ua with ha
  have hρ0 : ∀ (M : Mem ι), (pth I r₁ M m)[0]? = some (M ρ) := fun M =>
    bit_at hm0 (by simpa using hρ)
  -- quiescent reads after `W₀(a)` and after `W₀(a) W₁(z)`
  have hQ1 := quiescent_val S.hatom S.R₁.tree S.hr₁ S.h1w (wpre_wRun S.hw S.hof [a]).1
  have hQ2 := quiescent_val S.hatom S.R₁.tree S.hr₁ S.h1w (wpre_wRun S.hw S.hof [a, z]).1
  simp only [lastVal, List.foldl_cons, List.foldl_nil] at hQ1 hQ2
  have hP1 := pth_eq_of_vl S.R₁ hual hQ1
  have hP2 := pth_eq_of_vl S.R₁ hu₁ (hQ2.trans hz₁.symm)
  have hC1 : (wRun I w [a]).2.mem ρ = !c := by
    have := hρ0 (wRun I w [a]).2.mem; rw [hP1] at this; simpa [hua] using this.symm
  have hC2 : (wRun I w [a, z]).2.mem ρ = c := by
    have := hρ0 (wRun I w [a, z]).2.mem; rw [hP2] at this; simpa using this.symm
  -- the first step of `W₁` that sets `ρ` to `c`
  set f : ℕ → Bool := fun t => wMem I w [a] z t ρ with hf
  have hf0 : f 0 ≠ c := by simp [hf, wMem_zero, hC1]
  have hfT : f (wT I w [a] z) = c := by
    simp only [hf, wMem_T]; exact hC2
  obtain ⟨t₀, ht₀, hft, hfle⟩ := exists_flip f hf0 hfT
  have hft₀ : f t₀ ≠ c := hfle t₀ le_rfl
  set M1 := wMem I w [a] z (t₀ + 1) with hM1
  set M0 := wMem I w [a] z t₀ with hM0
  have hagree : ∀ i, i ≠ ρ → M1 i = M0 i := fun i hi =>
    wMem_succ_eq_of_ne [a] z t₀ (Ne.symm hi) (by
      intro h; apply hft₀; rw [← hft]; exact h.symm)
  -- execution `e'`: `R₁` then `R₂` right after the flip
  obtain ⟨hval, hops, hoth, hret1, hret2, hprec, hpre⟩ :=
    two_blocks S.R₁.tree S.R₂.tree S.hr₁ S.hr₂ S.h1w S.h2w S.h12
      (wpre_part S.hw S.hof [a] z (t := t₀ + 1) (by omega))
  obtain ⟨j₁, j₂, h1, h2, h3, hv1, hv2⟩ :=
    lin_reads S.hatom hval hops hoth hret1 hret2 hprec 1 hpre
  have hR1a : vl I r₁ (pth I r₁ M1 m) ≠ a := by
    intro h
    have := hρ0 M1
    rw [pth_eq_of_vl S.R₁ hual h] at this
    have hM1ρ : M1 ρ = c := hft
    simp [hua, hM1ρ] at this
  have h3' : j₂ ≤ 2 := by simpa using h3
  have hj₁ : j₁ = 2 := by
    have : j₁ ≤ 2 := by omega
    interval_cases j₁
    · exfalso; apply hR1a
      have h' : vl I r₁ (pth I r₁ (wPart I w [a] z (t₀ + 1)).mem m) = a := by
        simpa [lastVal] using hv1
      exact h'
    · rfl
  have hR2 : vl I r₂ (pth I r₂ M1 m) = z := by
    rw [show j₂ = 2 by omega] at hv2
    have hv2' : vl I r₂ (pth I r₂ (wPart I w [a] z (t₀ + 1)).mem m) = z := by
      simpa [lastVal] using hv2
    exact hv2'
  have hP2' : pth I r₂ M1 m = u₂ := pth_eq_of_vl S.R₂ hu₂ hR2
  -- `R₂` does not read `ρ`, hence behaves the same just before the flip
  have hcongr : pth I r₂ M0 m = pth I r₂ M1 m := by
    apply path_congr
    · intro j' hj' i hi
      have hi' : RdN (I.act r₂) (nd I r₂ ((pth I r₂ M1 m).take j')) i := by
        rw [pth_take M1 (le_of_lt hj')]; exact hi
      rw [hP2'] at hi'
      exact hagree i (havoid j' hj' i hi')
    · intro j' hj'
      obtain ⟨i, k, hk, -⟩ := S.R₂.tree.inner (pth I r₂ M1 j') (by simp; omega)
      exact ⟨i, k, hk⟩
  -- execution `e''`: `R₂` then `R₁` right before the flip
  obtain ⟨hval', hops', hoth', hret2', hret1', hprec', hpre'⟩ :=
    two_blocks S.R₂.tree S.R₁.tree S.hr₂ S.hr₁ S.h2w S.h1w (Ne.symm S.h12)
      (wpre_part S.hw S.hof [a] z (t := t₀) (by omega))
  obtain ⟨j₁', j₂', h1', h2', h3', hv1', hv2'⟩ :=
    lin_reads S.hatom hval' hops' hoth' hret2' hret1' hprec' 1 hpre'
  have hR2' : vl I r₂ (pth I r₂ M0 m) = z := by rw [hcongr, hR2]
  have haz : a ≠ z := by
    rw [ha, ← hz₁]
    exact vl_ne_of_getElem S.R₁ hual hu₁ (j := 0) (by simp [hua])
  have h3'' : j₂' ≤ 2 := by simpa using h3'
  have hj₁' : j₁' = 2 := by
    have : j₁' ≤ 2 := by omega
    interval_cases j₁'
    · exfalso; apply haz
      have h' : vl I r₂ (pth I r₂ (wPart I w [a] z t₀).mem m) = a := by
        simpa [lastVal] using hv1'
      exact h'.symm.trans hR2'
    · rfl
  have hR1' : vl I r₁ (pth I r₁ M0 m) = z := by
    rw [show j₂' = 2 by omega] at hv2'
    have hv2'' : vl I r₁ (pth I r₁ (wPart I w [a] z t₀).mem m) = z := by
      simpa [lastVal] using hv2'
    exact hv2''
  have hP1' := pth_eq_of_vl S.R₁ hu₁ (hR1'.trans hz₁.symm)
  have := hρ0 M0
  rw [hP1'] at this
  simp only [List.getElem?_cons_zero, Option.some.injEq] at this
  exact hft₀ this.symm

/-! ## Case B: every path of `T₂` reads the root of `T₁` -/

theorem caseB (S : Setting I w r₁ r₂ m) {ρ : ι} (hρ : RdN (I.act r₁) (nd I r₁ []) ρ)
    (hall : ∀ U : List Bool, U.length = m → ∃ j < m, RdN (I.act r₂) (nd I r₂ (U.take j)) ρ) :
    False := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by have := S.hm; omega⟩
  have hm0 : 0 < n + 2 := by omega
  set u₀ : List Bool := List.replicate (n + 1) false with hu₀
  set ua : List Bool := u₀ ++ [false] with hua
  set ub : List Bool := u₀ ++ [true] with hub
  set uz : List Bool := true :: List.replicate (n + 1) false with huz
  have hual : ua.length = n + 2 := by simp [hua, hu₀]
  have hubl : ub.length = n + 2 := by simp [hub, hu₀]
  have huzl : uz.length = n + 2 := by simp [huz]
  set a := vl I r₁ ua with ha
  set b := vl I r₁ ub with hb
  set z := vl I r₁ uz with hz
  have hab : a ≠ b := vl_ne_of_getElem S.R₁ hual hubl (j := n + 1) (by simp [hua, hub, hu₀])
  have haz : a ≠ z := vl_ne_of_getElem S.R₁ hual huzl (j := 0) (by simp [hua, huz, hu₀])
  have hbz : b ≠ z := vl_ne_of_getElem S.R₁ hubl huzl (j := 0) (by simp [hub, huz, hu₀])
  obtain ⟨x, kx, hx, -⟩ := S.R₁.tree.inner u₀ (by simp [hu₀])
  have hxN : RdN (I.act r₁) (nd I r₁ u₀) x := ⟨kx, hx⟩
  have hρ0 : ∀ (M : Mem ι), (pth I r₁ M (n + 2))[0]? = some (M ρ) := fun M =>
    bit_at hm0 (by simpa using hρ)
  have hxbit : ∀ (M : Mem ι) (e : Bool), pth I r₁ M (n + 2) = u₀ ++ [e] → M x = e := by
    intro M e hP
    have := bit_at (r := r₁) (M := M) (m := n + 2) (j := n + 1) (by omega) (i := x)
      (by rw [hP, List.take_left' (by simp [hu₀])]; exact hxN)
    rw [hP] at this
    simpa [hu₀] using this.symm
  have hρbit : ∀ (M : Mem ι) (U : List Bool), pth I r₁ M (n + 2) = U → U[0]? = some (M ρ) := by
    intro M U hP; rw [← hP]; exact hρ0 M
  -- quiescent reads
  have hQ1 := quiescent_val S.hatom S.R₁.tree S.hr₁ S.h1w (wpre_wRun S.hw S.hof [a]).1
  have hQ2 := quiescent_val S.hatom S.R₁.tree S.hr₁ S.h1w (wpre_wRun S.hw S.hof [a, z]).1
  have hQ3 := quiescent_val S.hatom S.R₁.tree S.hr₁ S.h1w (wpre_wRun S.hw S.hof [a, z, b]).1
  have hQ3' := quiescent_val S.hatom S.R₂.tree S.hr₂ S.h2w (wpre_wRun S.hw S.hof [a, z, b]).1
  simp only [lastVal, List.foldl_cons, List.foldl_nil] at hQ1 hQ2 hQ3 hQ3'
  have hP1 := pth_eq_of_vl S.R₁ hual hQ1
  have hP2 := pth_eq_of_vl S.R₁ huzl hQ2
  have hP3 := pth_eq_of_vl S.R₁ hubl hQ3
  have hC1x : (wRun I w [a]).2.mem x = false := hxbit _ _ hP1
  have hC2ρ : (wRun I w [a, z]).2.mem ρ = true := by
    have := hρbit _ _ hP2; simp [huz] at this; exact this
  have hC3ρ : (wRun I w [a, z, b]).2.mem ρ = false := by
    have := hρbit _ _ hP3; simp [hub, hu₀] at this; exact this
  have hC3x : (wRun I w [a, z, b]).2.mem x = true := hxbit _ _ hP3
  by_cases hx1 : ∃ t ≤ wT I w [a] z, wMem I w [a] z t x = true
  · -- Case 1 with the first write of `1` to `x` inside `W₁`: `R₁` returns `b` too early
    obtain ⟨t₁, ht₁, hxt₁⟩ := hx1
    obtain ⟨t', ht', hft', -⟩ := exists_flip (fun t => wMem I w [a] z t x) (N := t₁) (b := true)
      (by simp [wMem_zero, hC1x]) hxt₁
    obtain ⟨hval, hops, hoth, hret1, -, -, hpre⟩ :=
      split_two S.R₁.tree S.R₂.tree S.hr₁ S.hr₂ S.h1w S.h2w S.h12 (by omega)
        (wpre_wRun S.hw S.hof [a]).1 (wpre_part S.hw S.hof [a] z (t := t' + 1) (by omega))
    obtain ⟨j, h1, h2, hv⟩ := lin_read S.hatom hval hops hoth hret1 1 (fun j hj => hpre j hj)
    have hu : pth I r₁ (wRun I w [a]).2.mem (n + 2 - 1) = u₀ := by
      rw [show n + 2 - 1 = n + 1 by omega, ← pth_take _ (show n + 1 ≤ n + 2 by omega), hP1,
        hua, List.take_left' (by simp [hu₀])]
    have hbit : bit (I.act r₁) (wPart I w [a] z (t' + 1)).mem (nd I r₁ u₀) = true := by
      rw [bit_of_rdN hxN]; exact hft'
    rw [hu, hbit] at hv
    have h2' : j ≤ 2 := by simpa using h2
    interval_cases j
    · exact hab (by simpa [lastVal] using hv.symm)
    · exact hbz (by simpa [lastVal] using hv)
  push Not at hx1
  have hC2x : (wRun I w [a, z]).2.mem x = false := by
    have := hx1 _ le_rfl; rw [wMem_T] at this; simpa using this
  -- the writes of `W₂`
  set g := wMem I w [a, z] b with hg
  obtain ⟨wx, hwx, hgx, hgxle⟩ := exists_flip (fun t => g t x) (N := wT I w [a, z] b) (b := true)
    (by simp [hg, wMem_zero, hC2x]) (by simp only [hg, wMem_T]; exact hC3x)
  obtain ⟨wr, hwr, hgr, hgrle⟩ := exists_flip (fun t => g t ρ) (N := wT I w [a, z] b)
    (b := false) (by simp [hg, wMem_zero, hC2ρ]) (by simp only [hg, wMem_T]; exact hC3ρ)
  rcases lt_trichotomy wx wr with hlt | heq | hgt
  · -- Case 1: `R₁` returns `b`, then `R₂` sees `ρ = 1` and cannot return `b`
    have hpre2 := wpre_part S.hw S.hof [a, z] b (t := wx + 1) (by omega)
    rw [show [a, z] = [a] ++ [z] from rfl, wRun_concat, List.append_assoc] at hpre2
    obtain ⟨hval, hops, hoth, hret1, hret2, hprec, hpre⟩ :=
      split_two S.R₁.tree S.R₂.tree S.hr₁ S.hr₂ S.h1w S.h2w S.h12 (by omega)
        (wpre_wRun S.hw S.hof [a]).1 hpre2
    obtain ⟨j₁, j₂, h1, h2, h3, hv1, hv2⟩ :=
      lin_reads S.hatom hval hops hoth hret1 hret2 hprec 1 hpre
    have hu : pth I r₁ (wRun I w [a]).2.mem (n + 2 - 1) = u₀ := by
      rw [show n + 2 - 1 = n + 1 by omega, ← pth_take _ (show n + 1 ≤ n + 2 by omega), hP1,
        hua, List.take_left' (by simp [hu₀])]
    have hD : (wPart I w ([a] ++ [z]) b (wx + 1)).mem = g (wx + 1) := rfl
    have hbit : bit (I.act r₁) (wPart I w ([a] ++ [z]) b (wx + 1)).mem (nd I r₁ u₀) = true := by
      rw [bit_of_rdN hxN, hD]; exact hgx
    rw [hu, hbit] at hv1
    have h3' : j₂ ≤ 3 := by simpa using h3
    have hj₁ : j₁ = 3 := by
      have : j₁ ≤ 3 := by omega
      interval_cases j₁
      · exact absurd (by simpa [lastVal] using hv1.symm) hab
      · exact absurd (by simpa [lastVal] using hv1) hbz
      · rfl
    rw [show j₂ = 3 by omega] at hv2
    have hR2 : vl I r₂ (pth I r₂ (g (wx + 1)) (n + 2)) = b := by
      rw [← hD]; simpa [lastVal] using hv2
    have hPeq : pth I r₂ (g (wx + 1)) (n + 2) = pth I r₂ (wRun I w [a, z, b]).2.mem (n + 2) :=
      pth_eq_of_vl S.R₂ (length_path _ _) (hR2.trans hQ3'.symm)
    obtain ⟨j, hj, hjρ⟩ := hall (pth I r₂ (wRun I w [a, z, b]).2.mem (n + 2)) (length_path _ _)
    have e1 := bit_at (I := I) (r := r₂) (M := g (wx + 1)) hj (by rw [hPeq]; exact hjρ)
    have e2 := bit_at (I := I) (r := r₂) (M := (wRun I w [a, z, b]).2.mem) hj hjρ
    rw [hPeq, e2] at e1
    have hgρ : g (wx + 1) ρ ≠ false := hgrle (wx + 1) (by omega)
    rw [hC3ρ] at e1
    exact hgρ (Option.some.inj e1).symm
  · -- the same step cannot change both `x` and `ρ`
    subst heq
    have hxρ : x ≠ ρ := by
      intro h; subst h; rw [hgx] at hgr; cases hgr
    have := wMem_succ_eq_of_ne (I := I) (w := w) [a, z] b wx hxρ
      (by rw [← hg]; intro h; exact hgxle wx le_rfl (h ▸ hgx))
    rw [← hg] at this
    exact hgrle wx le_rfl (this ▸ hgr)
  · -- Case 2: `R₁` sees `ρ = 0` and `x = 0` after the first write of `0` to `ρ`
    obtain ⟨hval, hops, hoth, hret1, hpre⟩ :=
      one_block S.R₁.tree S.hr₁ S.h1w (wpre_part S.hw S.hof [a, z] b (t := wr + 1) (by omega))
    obtain ⟨j, h1, h2, hv⟩ := lin_read S.hatom hval hops hoth hret1 2 hpre
    have hD : (wPart I w [a, z] b (wr + 1)).mem = g (wr + 1) := rfl
    rw [hD] at hv
    have h2' : j ≤ 3 := by simpa using h2
    interval_cases j
    · -- returns `z`: then `ρ = 1`
      have hP := pth_eq_of_vl S.R₁ huzl (by simpa [lastVal] using hv)
      have := hρbit _ _ hP
      simp [huz] at this
      rw [this] at hgr; cases hgr
    · -- returns `b`: then `x = 1`
      have hP := pth_eq_of_vl S.R₁ hubl (by simpa [lastVal] using hv)
      have := hxbit _ _ hP
      exact hgxle (wr + 1) (by omega) this

end Sec4

end Podc.FastReadsRegisterSim
