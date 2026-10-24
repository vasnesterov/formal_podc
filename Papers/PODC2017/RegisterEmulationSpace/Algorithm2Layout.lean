import Papers.PODC2017.RegisterEmulationSpace.Algorithm2SeqSafe

/-!
# The register layout of Algorithm 2 and Theorem 3

With `k = |Wr|` writers, `n = |S|` servers and `z = ⌊(n - (f+1))/f⌋`, the `i`-th writer
(`0 ≤ i < k`) uses the set `R_⌊i/z⌋`; the `m = ⌈k/z⌉` sets `R_g` have `w_g f + f + 1` registers,
where `w_g ≤ z` is the number of writers of `R_g`, placed on distinct servers. In total
`Σ_g (w_g f + f + 1) = kf + ⌈k/z⌉ (f+1)` registers (the paper's count).

Note the 0-based index `i`: the paper's 1-based clients `c_i ↦ R_⌊i/z⌋` overload the last set
(see `Algorithm2Counterexample.lean`).
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

variable {C S : Type*} [DecidableEq C] [Fintype S] [DecidableEq S]

noncomputable section

namespace Layout2

variable (Wr : Finset C) (f n : ℕ)

/-- `z = ⌊(n - (f+1))/f⌋`: the number of writers per register set. -/
def z : ℕ := (n - (f + 1)) / f

/-- The number of register sets, `⌈k/z⌉`. -/
def m : ℕ := #Wr ⌈/⌉ z f n

/-- The set of the `i`-th writer. -/
def grpI (hz : 0 < z f n) (i : Fin #Wr) : Fin (m Wr f n) :=
  ⟨i.val / z f n, by
    have hi := i.isLt
    have := (ceilDiv_le_iff_le_mul hz).1 (le_refl (#Wr ⌈/⌉ z f n))
    rw [Nat.div_lt_iff_lt_mul hz]
    unfold m
    rw [mul_comm]; omega⟩

variable {f n}

/-- Number of writers of the set `g`. -/
def mem (hz : 0 < z f n) (g : Fin (m Wr f n)) : ℕ := #(univ.filter fun i => grpI Wr f n hz i = g)

/-- Size of the set `g`: `w_g f + f + 1`. -/
def sz (hz : 0 < z f n) (g : Fin (m Wr f n)) : ℕ := mem Wr hz g * f + f + 1

/-- Total number of registers. -/
def N (hz : 0 < z f n) : ℕ := ∑ g, sz Wr hz g

/-- Registers are pairs (set, position in the set). -/
def eqv (hz : 0 < z f n) : (Σ g : Fin (m Wr f n), Fin (sz Wr hz g)) ≃ Fin (N Wr hz) := finSigmaFinEquiv

lemma mem_le (hz : 0 < z f n) (g : Fin (m Wr f n)) : mem Wr hz g ≤ z f n := by
  unfold mem
  have : (univ.filter fun i => grpI Wr f n hz i = g).map Fin.valEmbedding ⊆
      Ico (g.val * z f n) (g.val * z f n + z f n) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.1 hx
    have hg := congrArg Fin.val (mem_filter.1 hi).2
    simp only [grpI] at hg
    simp only [Fin.valEmbedding_apply, mem_Ico]
    rw [← hg]
    constructor
    · exact Nat.div_mul_le_self _ _
    · have := Nat.lt_div_mul_add (a := i.val) hz
      linarith
  have := card_le_card this
  simpa using this

lemma sz_le (hz : 0 < z f n) (hn : f + 1 ≤ n) (g : Fin (m Wr f n)) : sz Wr hz g ≤ n := by
  have h1 := mem_le Wr hz g
  have h2 : z f n * f ≤ n - (f + 1) := Nat.div_mul_le_self _ _
  have h3 : mem Wr hz g * f ≤ z f n * f := Nat.mul_le_mul_right _ h1
  unfold sz; omega

lemma N_eq (hz : 0 < z f n) : N Wr hz = #Wr * f + m Wr f n * (f + 1) := by
  have hsum : ∑ g, mem Wr hz g = #Wr := by
    unfold mem
    rw [← card_eq_sum_card_fiberwise (f := grpI Wr f n hz) (fun _ _ => mem_univ _)]
    simp
  unfold N sz
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, hsum]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The set of a writer. -/
def gC (hz : 0 < z f n) (c : C) (h : c ∈ Wr) : Fin (m Wr f n) := grpI Wr f n hz (Wr.equivFin ⟨c, h⟩)

/-- The write sets. -/
def Rset (hz : 0 < z f n) (c : C) : Finset (Fin (N Wr hz)) :=
  if h : c ∈ Wr then
    univ.map ((Embedding.sigmaMk (β := fun g => Fin (sz Wr hz g)) (gC Wr hz c h)).trans
      (eqv Wr hz).toEmbedding)
  else ∅

/-- The server of a register: its position in its set. -/
def δL (hz : 0 < z f n) (hn : f + 1 ≤ n) (e : Fin n ≃ S) (b : Fin (N Wr hz)) : S :=
  e ⟨((eqv Wr hz).symm b).2.val, lt_of_lt_of_le ((eqv Wr hz).symm b).2.isLt (sz_le Wr hz hn _)⟩

lemma mem_Rset {hz : 0 < z f n} {c : C} {b : Fin (N Wr hz)} (hb : b ∈ Rset Wr hz c) :
    ∃ h : c ∈ Wr, ((eqv Wr hz).symm b).1 = gC Wr hz c h := by
  unfold Rset at hb
  split_ifs at hb with h
  · obtain ⟨j, -, rfl⟩ := mem_map.1 hb
    exact ⟨h, by simp⟩
  · simp at hb

lemma card_Rset (hz : 0 < z f n) (c : C) (h : c ∈ Wr) : #(Rset Wr hz c) = sz Wr hz (gC Wr hz c h) := by
  simp [Rset, h]

theorem layout (hz : 0 < z f n) (hn : f + 1 ≤ n) (e : Fin n ≃ S) :
    Layout (δL Wr hz hn e) f Wr (Rset Wr hz) := by
  refine ⟨fun c hc => by simp [Rset, hc], fun c => ?_, fun c hc => ?_⟩
  · intro b hb b' hb' hδ
    obtain ⟨h, hg⟩ := mem_Rset Wr hb
    obtain ⟨h', hg'⟩ := mem_Rset Wr hb'
    simp only [δL, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at hδ
    apply (eqv Wr hz).symm.injective
    rw [Sigma.ext_iff]
    refine ⟨hg.trans hg'.symm, ?_⟩
    exact (Fin.heq_ext_iff (by rw [hg, hg'])).2 hδ
  · -- capacity: the writers meeting `R c` are the other writers of the same set
    set g := gC Wr hz c hc
    set F := univ.filter fun i => grpI Wr f n hz i = g
    have hidx : Wr.equivFin ⟨c, hc⟩ ∈ F := by simp [F, g, gC]
    have hsub : Nb Wr (Rset Wr hz) c ⊆ (F.erase (Wr.equivFin ⟨c, hc⟩)).image
        fun i => (Wr.equivFin.symm i).val := by
      intro d hd
      obtain ⟨hdW, hdc, hdis⟩ := mem_filter.1 hd
      obtain ⟨b, hbd, hbc⟩ := not_disjoint_iff.1 hdis
      obtain ⟨h1, hg1⟩ := mem_Rset Wr hbd
      obtain ⟨h2, hg2⟩ := mem_Rset Wr hbc
      refine mem_image.2 ⟨Wr.equivFin ⟨d, hdW⟩, mem_erase.2 ⟨?_, ?_⟩, by simp⟩
      · intro h; exact hdc (congrArg Subtype.val (Wr.equivFin.injective h))
      · simp only [F, mem_filter, mem_univ, true_and]
        exact hg1.symm.trans hg2
    have h1 := (card_le_card hsub).trans card_image_le
    rw [card_erase_of_mem hidx] at h1
    have h2 : 1 ≤ #F := card_pos.2 ⟨_, hidx⟩
    rw [card_Rset Wr hz c hc]
    unfold sz
    have h3 : #(Nb Wr (Rset Wr hz) c) * f ≤ (#F - 1) * f := Nat.mul_le_mul_right _ h1
    have h4 : (#F - 1) * f + f = #F * f := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h2]
    simp only [mem, F, g] at h3 h4 ⊢
    omega

/-- Each register is written by at most `z` writers ("`z`-writer registers"). -/
lemma writers_le (hz : 0 < z f n) (b : Fin (N Wr hz)) :
    #(Wr.filter fun c => b ∈ Rset Wr hz c) ≤ z f n := by
  set g := ((eqv Wr hz).symm b).1
  have hsub : (Wr.filter fun c => b ∈ Rset Wr hz c) ⊆
      (univ.filter fun i => grpI Wr f n hz i = g).image fun i => (Wr.equivFin.symm i).val := by
    intro d hd
    obtain ⟨hdW, hb⟩ := mem_filter.1 hd
    obtain ⟨h1, hg1⟩ := mem_Rset Wr hb
    refine mem_image.2 ⟨Wr.equivFin ⟨d, hdW⟩, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and]
    exact hg1.symm
  exact (card_le_card hsub).trans (card_image_le.trans (mem_le Wr hz g))

end Layout2

end

/-- **Theorem 3** (Section 3.3, Appendix D). For all `f > 0` and `n = |S| > 2f`, and every set `Wr`
of `k` writers, Algorithm 2 with `kf + ⌈k/z⌉(f+1)` registers (`z = ⌊(n - (f+1))/f⌋`), each written
by at most `z` writers, is an `f`-tolerant wait-free emulation of a `k`-writer register that is safe
in sequential runs (in particular obstruction-free and `SeqSafe`, the hypotheses of the lower
bounds, which are therefore not vacuous). -/
theorem theorem3 {C S V : Type*} [DecidableEq C] [Fintype S] [DecidableEq S] (Wr : Finset C)
    {f : ℕ} (hf : 0 < f) (hn : 2 * f < Fintype.card S) (v₀ : V) :
    ∃ (N : ℕ) (δ : Fin N → S) (R : C → Finset (Fin N)),
      N = #Wr * f + (#Wr ⌈/⌉ ((Fintype.card S - (f + 1)) / f)) * (f + 1) ∧
      (∀ b, #(Wr.filter fun c => b ∈ R c) ≤ (Fintype.card S - (f + 1)) / f) ∧
      Layout δ f Wr R ∧ WaitFree (alg δ f R v₀) δ f ∧
      (alg δ f R v₀).ObstructionFree δ f ↑Wr ∧ (alg δ f R v₀).SeqSafe v₀ ↑Wr := by
  have hz : 0 < Layout2.z f (Fintype.card S) := Nat.div_pos (by omega) hf
  have hn' : f + 1 ≤ Fintype.card S := by omega
  set e := (Fintype.equivFin S).symm
  have hL := Layout2.layout Wr hz hn' e
  exact ⟨_, Layout2.δL Wr hz hn' e, Layout2.Rset Wr hz, Layout2.N_eq Wr hz,
    Layout2.writers_le Wr hz, hL, waitFree _ f _ v₀ hL.inj, obstructionFree _ f _ v₀ hL.inj _,
    seqSafe _ f _ v₀ Wr hL⟩

end Podc.RegisterEmulationSpace.Alg2
