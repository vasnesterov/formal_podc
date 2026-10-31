import Papers.PODC2018.InteractiveDistributedProofs.LowerBound.Counterexample
import Papers.PODC2018.InteractiveDistributedProofs.LowerBound.Packing
import Podc.Probability.Finite.LocalLemma

/-!
# The repaired lower bound (Section 3.4): Lemmas 3.8–3.11 and Theorem 1.4

Lemma 3.11 of the paper is false (`lemma_3_11_false` in `Counterexample.lean`): `μ_A(F)` is only the
*marginal* law of the random set `𝓜_A(F, r)`, while the separating event "`𝓜_A(·, r)` meets
`𝓜_B(F₁, r)`" also depends on `r`. The repair replaces `μ_A(F)` by the **joint law** `μA' F` of
the bridge challenges `(r_{x_A}, r_{x_B})` and the set `𝓜_A(F, r)`, a distribution on
`(R × R) × Set M`.

The key observation is a conditional independence: `𝓜_A(F, r)` depends only on the challenges of
`V_A ∪ {x_A, x_B}` (`MA_congr`), `𝓜_B(F₁, r)` only on those of `V_B ∪ {x_A, x_B}` (`MB_congr`), so
given the bridge challenges they are independent, and (`uprob_inter_nonempty_eq_sum`)

  `Pr_r[𝓜_A(F, r) ∩ 𝓜_B(F₁, r) ≠ ∅] = ∑_{(s, S)} μA' F (s, S) · g(s, S)`,

where `g(s, S) ∈ [0, 1]` (`gB`) is the probability over the `V_B` challenges that `S` meets
`𝓜_B(F₁, r)` when the bridge challenges are `s`; `g` does not depend on `F`. With `F = F₁` the left
side is `> 2/3` and with `F = F₂ ≠ F₁` it is `< 1/3` (Corollary 3.10), so
`1/3 < ∑ (μ₁ − μ₂) g ≤ ½ ‖μ₁ − μ₂‖₁`: the repaired Lemma 3.11 (`lemma_3_11_repaired`). The packing
Lemma 3.12 then bounds `|𝓕| < 5^(|R|² · 2^|M|)` (`card_family_lt`), and with `|R|, |M| ≤ 2^L` and
`|𝓕| ≥ 2^{c k²}` this gives `c k² < 3 · 2^{2^{L+1}}`, i.e. `L ≥ log log k − O(1)`
(`theorem_1_4_repaired`).

**The challenge length matters.** The domain of `μA'` has size `|R|² · 2^|M|`, so the bound needs
the challenge alphabet `R` to be bounded (Definition 1 gives each node `ℓ`-bit challenges, and
`InDAM` bounds `|R|`). For protocols with unbounded randomness, which the introduction claims are
also covered, this argument does not apply.

The paper's claim "`G(F_A, F_B)` is symmetric iff `F_A = F_B`" is taken as the hypothesis `hiff`
(only its direction `F_A ≠ F_B → ¬ Sym G(F_A, F_B)` has content: `sym_dumbbell_self`). The paper's
other requirement on `𝓕` (`FamilyOK`: asymmetric, pairwise non-isomorphic graphs) is only used
through `hiff`, so it is not a hypothesis here. `cex_joint_laws_far` shows the hypotheses are
satisfiable (by the counterexample to the original Lemma 3.11).

## Main statements

* `lemma_3_8`: locality — `m ∈ 𝓜_A(F_A, r) ∩ 𝓜_B(F_B, r)` iff some response with
  `M_{x_A} = M_{x_B} = m` makes all nodes of `G(F_A, F_B)` accept.
* `lemma_3_9`: the best prover's acceptance probability on `G(F_A, F_B)` is
  `Pr_r[𝓜_A(F_A, r) ∩ 𝓜_B(F_B, r) ≠ ∅]`.
* `corollary_3_10`: this probability is `> 2/3` if `F_A = F_B` and `< 1/3` otherwise.
* `uprob_inter_nonempty_eq_sum`, `sum_μA'`, `gB_nonneg`, `gB_le_one`: the conditional-independence
  decomposition.
* `lemma_3_11_repaired`, `card_family_lt`, `theorem_1_4_repaired_log`, `theorem_1_4_repaired`.
-/

open Finset Cslib.Probability

namespace Podc.InteractiveDistributedProofs.LowerBound

open DVert

/-! ### Generic finite probability -/

section Generic

-- CSLib candidate
/-- **Law of total probability (counting form).** Splitting an event along the values of a
finitely-valued random variable `key`. -/
theorem uprob_eq_sum_uprob_key {Ω Z : Type*} [Fintype Ω] [Fintype Z] (key : Ω → Z)
    (E : Ω → Prop) : uprob E = ∑ z, uprob (fun ω => key ω = z ∧ E ω) := by
  classical
  simp only [uprob_eq_card_filter, ← Finset.sum_div]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := key) (t := univ) (fun _ _ => mem_univ _)]
  push_cast
  refine sum_congr rfl fun z _ => ?_
  rw [filter_filter]
  congr 2
  ext ω
  simp [and_comm]

-- CSLib candidate
/-- If `μ` and `η` are probability vectors and `0 ≤ g ≤ 1`, then
`∑ μ g − ∑ η g ≤ ½ ‖μ − η‖₁` (an event-free form of "`|μ(Q) − η(Q)| ≤ ½ ‖μ − η‖₁`"). -/
theorem sum_mul_sub_sum_mul_le_half_l1 {ι : Type*} [Fintype ι] (μ η g : ι → ℝ)
    (hμ : ∑ i, μ i = 1) (hη : ∑ i, η i = 1) (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) :
    ∑ i, μ i * g i - ∑ i, η i * g i ≤ (∑ i, |μ i - η i|) / 2 := by
  have hpt : ∀ i, μ i * g i - η i * g i ≤ (|μ i - η i| + (μ i - η i)) / 2 := by
    intro i
    rcases abs_cases (μ i - η i) with ⟨h, hd⟩ | ⟨h, hd⟩
    · rw [h]; nlinarith [hg1 i]
    · rw [h]; nlinarith [hg0 i]
  have hsum : ∑ i, (μ i - η i) = 0 := by rw [sum_sub_distrib, hμ, hη, sub_self]
  calc ∑ i, μ i * g i - ∑ i, η i * g i = ∑ i, (μ i * g i - η i * g i) := by
        rw [sum_sub_distrib]
    _ ≤ ∑ i, (|μ i - η i| + (μ i - η i)) / 2 := sum_le_sum fun i _ => hpt i
    _ = (∑ i, |μ i - η i|) / 2 := by
        rw [← sum_div, sum_add_distrib, hsum, add_zero]

end Generic

/-! ### Locality on dumbbells -/

section Locality

variable {k : ℕ}

/-- Whether a dumbbell vertex lies on the `B` side `V_B`. -/
def DVert.isB : DVert k → Bool
  | b _ => true
  | _ => false

/-- Whether a dumbbell vertex lies on the `A` side `V_A`. -/
def DVert.isA : DVert k → Bool
  | a _ => true
  | _ => false

/-- Two views on dumbbells agree if the neighbourhoods of `v` agree and the assignments agree on
the closed neighbourhood. -/
theorem mask_dumbbell_eq {FA FB FA' FB' : SimpleGraph (Fin k)} {vA : Fin k} {v : DVert k}
    {α : Type*} {x y : DVert k → α} (hadj : ∀ u, dAdj FA FB vA v u ↔ dAdj FA' FB' vA v u)
    (h : ∀ u, (u = v ∨ dAdj FA FB vA v u) → x u = y u) :
    mask (dumbbell FA FB vA) v x = mask (dumbbell FA' FB' vA) v y := by
  funext u
  rw [mask_dumbbell, mask_dumbbell, ← hadj]
  split_ifs with hu
  · rw [h u hu]
  · rfl

/-- A vertex of the closed neighbourhood of `a i` or `x_A` is not on the `B` side. -/
theorem isB_of_nbhd_A {FA FB : SimpleGraph (Fin k)} {vA : Fin k} {v u : DVert k}
    (hv : v.isB = false) (hv' : v ≠ xB) (hu : u = v ∨ dAdj FA FB vA v u) : u.isB = false := by
  rcases hu with rfl | hu
  · exact hv
  · cases v <;> cases u <;> simp_all [dAdj, DVert.isB]

/-- A vertex of the closed neighbourhood of `b i` or `x_B` is not on the `A` side. -/
theorem isA_of_nbhd_B {FA FB : SimpleGraph (Fin k)} {vA : Fin k} {v u : DVert k}
    (hv : v.isA = false) (hv' : v ≠ xA) (hu : u = v ∨ dAdj FA FB vA v u) : u.isA = false := by
  rcases hu with rfl | hu
  · exact hv
  · cases v <;> cases u <;> simp_all [dAdj, DVert.isA]

variable {R M : Type*} (pr : AMProtocol (DVert k) R M) (vA : Fin k)
  (fA fB : (DVert k → Option R) → M → Prop)

/-- `𝓜_A(F, r)` only depends on the challenges of `V_A ∪ {x_A, x_B}`. -/
theorem MA_congr (F : SimpleGraph (Fin k)) {c c' : DVert k → R}
    (h : ∀ u, u.isB = false → c u = c' u) : MA pr vA fA F c = MA pr vA fA F c' := by
  have hm : ∀ (v : DVert k), v.isB = false → v ≠ xB → ∀ Mr : DVert k → M,
      mask (dumbbell F F vA) v (fun u => (c u, Mr u)) =
        mask (dumbbell F F vA) v (fun u => (c' u, Mr u)) := fun v hv hv' Mr =>
    mask_dumbbell_eq (fun _ => Iff.rfl) fun u hu => by rw [h u (isB_of_nbhd_A hv hv' hu)]
  have hx : mask (dumbbell F F vA) xA c = mask (dumbbell F F vA) xA c' :=
    mask_dumbbell_eq (fun _ => Iff.rfl) fun u hu => h u (isB_of_nbhd_A rfl (by simp) hu)
  ext m
  simp only [MA, Set.mem_ofPred_eq, hx]
  refine exists_congr fun Mr => and_congr_right fun _ => and_congr_left fun _ => ?_
  refine forall_congr' fun i => ?_
  rw [hm (a i) rfl (by simp) Mr]

/-- `𝓜_B(F, r)` only depends on the challenges of `V_B ∪ {x_A, x_B}`. -/
theorem MB_congr (F : SimpleGraph (Fin k)) {c c' : DVert k → R}
    (h : ∀ u, u.isA = false → c u = c' u) : MB pr vA fB F c = MB pr vA fB F c' := by
  have hm : ∀ (v : DVert k), v.isA = false → v ≠ xA → ∀ Mr : DVert k → M,
      mask (dumbbell F F vA) v (fun u => (c u, Mr u)) =
        mask (dumbbell F F vA) v (fun u => (c' u, Mr u)) := fun v hv hv' Mr =>
    mask_dumbbell_eq (fun _ => Iff.rfl) fun u hu => by rw [h u (isA_of_nbhd_B hv hv' hu)]
  have hx : mask (dumbbell F F vA) xB c = mask (dumbbell F F vA) xB c' :=
    mask_dumbbell_eq (fun _ => Iff.rfl) fun u hu => h u (isA_of_nbhd_B rfl (by simp) hu)
  ext m
  simp only [MB, Set.mem_ofPred_eq, hx]
  refine exists_congr fun Mr => and_congr_right fun _ => and_congr_left fun _ => ?_
  refine forall_congr' fun i => ?_
  rw [hm (b i) rfl (by simp) Mr]

end Locality

/-! ### Lemmas 3.8 and 3.9, Corollary 3.10 -/

section Lemma38

variable {k : ℕ} {R M : Type*} {pr : AMProtocol (DVert k) R M} {𝓕 : Finset (SimpleGraph (Fin k))}
  {vA : Fin k} {fA fB : (DVert k → Option R) → M → Prop}

/-- The response used in Lemma 3.8: `M₁` on `V_A`, `M₂` on `V_B`, `m` on both bridge nodes. -/
def glueResp (M₁ M₂ : DVert k → M) (m : M) : DVert k → M
  | a i => M₁ (a i)
  | b i => M₂ (b i)
  | xA => m
  | xB => m

/-- **Lemma 3.8** (locality). For `F_A, F_B ∈ 𝓕`: `m ∈ 𝓜_A(F_A, r) ∩ 𝓜_B(F_B, r)` iff there is a
response `M` with `M_{x_A} = M_{x_B} = m` making every node of `G(F_A, F_B)` accept. -/
theorem lemma_3_8 (hS : IsSimple pr 𝓕 vA fA fB) {FA FB : SimpleGraph (Fin k)} (hA : FA ∈ 𝓕)
    (hB : FB ∈ 𝓕) (c : DVert k → R) (m : M) :
    m ∈ MA pr vA fA FA c ∩ MB pr vA fB FB c ↔
      ∃ Mr : DVert k → M, Mr xA = m ∧ Mr xB = m ∧
        ∀ v, pr.out v (mask (dumbbell FA FB vA) v fun u => (c u, Mr u)) := by
  have hG : InClass 𝓕 vA (dumbbell FA FB vA) := ⟨FA, hA, FB, hB, rfl⟩
  have hxA : mask (dumbbell FA FB vA) xA c = mask (dumbbell FA FA vA) xA c :=
    mask_dumbbell_eq (fun u => by cases u <;> simp [dAdj]) fun _ _ => rfl
  have hxB : mask (dumbbell FA FB vA) xB c = mask (dumbbell FB FB vA) xB c :=
    mask_dumbbell_eq (fun u => by cases u <;> simp [dAdj]) fun _ _ => rfl
  constructor
  · rintro ⟨⟨M₁, h₁, hacc₁, hf₁⟩, ⟨M₂, h₂, hacc₂, hf₂⟩⟩
    refine ⟨glueResp M₁ M₂ m, rfl, rfl, ?_⟩
    rintro (i | i | - | -)
    · have := hacc₁ i
      rwa [mask_dumbbell_eq (FA' := FA) (FB' := FA) (y := fun u => (c u, M₁ u))
        (fun u => by cases u <;> simp [dAdj]) fun u hu => ?_]
      rcases hu with rfl | hu
      · rfl
      · cases u <;> simp_all [dAdj, glueResp]
    · have := hacc₂ i
      rwa [mask_dumbbell_eq (FA' := FB) (FB' := FB) (y := fun u => (c u, M₂ u))
        (fun u => by cases u <;> simp [dAdj]) fun u hu => ?_]
      rcases hu with rfl | hu
      · rfl
      · cases u <;> simp_all [dAdj, glueResp]
    · refine ((hS _ hG c _).1).2 ⟨?_, rfl⟩
      rw [hxA]
      exact hf₁
    · refine ((hS _ hG c _).2).2 ⟨?_, rfl⟩
      rw [hxB]
      exact hf₂
  · rintro ⟨Mr, h₁, h₂, hacc⟩
    refine ⟨⟨Mr, h₁, fun i => ?_, ?_⟩, ⟨Mr, h₂, fun i => ?_, ?_⟩⟩
    · have := hacc (a i)
      rwa [mask_dumbbell_eq (FA' := FA) (FB' := FA) (y := fun u => (c u, Mr u))
        (fun u => by cases u <;> simp [dAdj]) fun _ _ => rfl] at this
    · have := ((hS _ hG c Mr).1.1 (hacc xA)).1
      rwa [hxA, h₁] at this
    · have := hacc (b i)
      rwa [mask_dumbbell_eq (FA' := FB) (FB' := FB) (y := fun u => (c u, Mr u))
        (fun u => by cases u <;> simp [dAdj]) fun _ _ => rfl] at this
    · have := ((hS _ hG c Mr).2.1 (hacc xB)).1
      rwa [hxB, h₂] at this

variable [Fintype R]

/-- Every prover is accepted on `G(F_A, F_B)` with probability at most
`Pr_r[𝓜_A(F_A, r) ∩ 𝓜_B(F_B, r) ≠ ∅]` (one half of Lemma 3.9). -/
theorem accProb_le (hS : IsSimple pr 𝓕 vA fA fB) {FA FB : SimpleGraph (Fin k)} (hA : FA ∈ 𝓕)
    (hB : FB ∈ 𝓕) (P : (DVert k → R) → DVert k → M) :
    pr.accProb (dumbbell FA FB vA) P ≤
      uprob (fun c => (MA pr vA fA FA c ∩ MB pr vA fB FB c).Nonempty) := by
  refine uprob_mono fun c hc => ?_
  have hG : InClass 𝓕 vA (dumbbell FA FB vA) := ⟨FA, hA, FB, hB, rfl⟩
  have heq : P c xA = P c xB := ((hS _ hG c (P c)).1.1 (hc xA)).2
  exact ⟨P c xA, (lemma_3_8 hS hA hB c _).2 ⟨P c, rfl, heq.symm, hc⟩⟩

/-- Some prover is accepted on `G(F_A, F_B)` with probability exactly
`Pr_r[𝓜_A(F_A, r) ∩ 𝓜_B(F_B, r) ≠ ∅]` (the other half of Lemma 3.9). -/
theorem exists_accProb_eq [Nonempty M] (hS : IsSimple pr 𝓕 vA fA fB)
    {FA FB : SimpleGraph (Fin k)} (hA : FA ∈ 𝓕) (hB : FB ∈ 𝓕) :
    ∃ P, pr.accProb (dumbbell FA FB vA) P =
      uprob (fun c => (MA pr vA fA FA c ∩ MB pr vA fB FB c).Nonempty) := by
  classical
  have hG : InClass 𝓕 vA (dumbbell FA FB vA) := ⟨FA, hA, FB, hB, rfl⟩
  let Good : (DVert k → R) → (DVert k → M) → Prop := fun c Mr =>
    ∀ v, pr.out v (mask (dumbbell FA FB vA) v fun u => (c u, Mr u))
  let P : (DVert k → R) → DVert k → M := fun c =>
    if h : ∃ Mr, Good c Mr then h.choose else fun _ => Classical.arbitrary M
  refine ⟨P, congrArg uprob (funext fun c => propext ⟨fun hc => ?_, fun hc => ?_⟩)⟩
  · have heq : P c xA = P c xB := ((hS _ hG c (P c)).1.1 (hc xA)).2
    exact ⟨P c xA, (lemma_3_8 hS hA hB c _).2 ⟨P c, rfl, heq.symm, hc⟩⟩
  · obtain ⟨m, hm⟩ := hc
    obtain ⟨Mr, -, -, hMr⟩ := (lemma_3_8 hS hA hB c m).1 hm
    have h : ∃ Mr, Good c Mr := ⟨Mr, hMr⟩
    have hP : P c = h.choose := dite_eq_left h
    show Good c (P c)
    rw [hP]
    exact h.choose_spec

/-- **Lemma 3.9.** The maximal probability (over provers) that all nodes of `G(F_A, F_B)` accept is
`Pr_r[𝓜_A(F_A, r) ∩ 𝓜_B(F_B, r) ≠ ∅]`. -/
theorem lemma_3_9 [Nonempty M] (hS : IsSimple pr 𝓕 vA fA fB) {FA FB : SimpleGraph (Fin k)}
    (hA : FA ∈ 𝓕) (hB : FB ∈ 𝓕) :
    IsGreatest (Set.range fun P => pr.accProb (dumbbell FA FB vA) P)
      (uprob (fun c => (MA pr vA fA FA c ∩ MB pr vA fB FB c).Nonempty)) := by
  obtain ⟨P, hP⟩ := exists_accProb_eq hS hA hB
  exact ⟨⟨P, hP⟩, by rintro _ ⟨P', rfl⟩; exact accProb_le hS hA hB P'⟩

/-- **Corollary 3.10.** For a simple protocol deciding `Sym` on the dumbbell class: if
`F_A = F_B` then `Pr_r[𝓜_A(F_A, r) ∩ 𝓜_B(F_B, r) ≠ ∅] > 2/3`, and if `F_A ≠ F_B` then it is
`< 1/3`. (`hiff` is the paper's claim that `G(F_A, F_B)` is symmetric iff `F_A = F_B`.) -/
theorem corollary_3_10 (hS : IsSimple pr 𝓕 vA fA fB) (hD : pr.Decides (InClass 𝓕 vA) Sym)
    (hiff : ∀ FA ∈ 𝓕, ∀ FB ∈ 𝓕, Sym (dumbbell FA FB vA) ↔ FA = FB)
    {FA FB : SimpleGraph (Fin k)} (hA : FA ∈ 𝓕) (hB : FB ∈ 𝓕) :
    (FA = FB → 2 / 3 < uprob (fun c => (MA pr vA fA FA c ∩ MB pr vA fB FB c).Nonempty)) ∧
      (FA ≠ FB → uprob (fun c => (MA pr vA fA FA c ∩ MB pr vA fB FB c).Nonempty) < 1 / 3) := by
  have hG : InClass 𝓕 vA (dumbbell FA FB vA) := ⟨FA, hA, FB, hB, rfl⟩
  refine ⟨fun heq => ?_, fun hne => ?_⟩
  · obtain ⟨P, hP⟩ := (hD _ hG).1 ((hiff FA hA FB hB).2 heq)
    exact hP.trans_le (accProb_le hS hA hB P)
  · rcases isEmpty_or_nonempty M with hM | hM
    · refine lt_of_le_of_lt (le_of_eq ?_) (by norm_num : (0 : ℝ) < 1 / 3)
      rw [← uprob_false (Ω := DVert k → R)]
      exact congrArg uprob (funext fun c => propext ⟨fun ⟨m, _⟩ => hM.elim m, False.elim⟩)
    · obtain ⟨P, hP⟩ := exists_accProb_eq hS hA hB
      rw [← hP]
      exact (hD _ hG).2 (fun h => hne ((hiff FA hA FB hB).1 h)) P

end Lemma38

/-! ### The joint law of the bridge challenges and `𝓜_A`, and conditional independence -/

section JointLaw

variable {k : ℕ} {R M : Type*} (pr : AMProtocol (DVert k) R M) (vA : Fin k)
  (fA fB : (DVert k → Option R) → M → Prop)

/-- Replace the challenges of the bridge nodes by `s = (s_{x_A}, s_{x_B})`. -/
def withBridge (c : DVert k → R) (s : R × R) : DVert k → R
  | a i => c (a i)
  | b i => c (b i)
  | xA => s.1
  | xB => s.2

/-- Setting the bridge challenges to their own values changes nothing. -/
theorem withBridge_eq_self {c : DVert k → R} {s : R × R} (h : (c xA, c xB) = s) :
    withBridge c s = c := by
  funext u
  cases u <;> simp [withBridge, ← h]

variable [Fintype R]

/-- **The repaired `μ_A(F)`**: the joint law of the bridge challenges `(r_{x_A}, r_{x_B})` and the
random set `𝓜_A(F, r)`, a distribution on `(R × R) × Set M`. (The paper's `μ_A(F)` is its second
marginal, `μA`.) -/
noncomputable def μA' (F : SimpleGraph (Fin k)) (z : (R × R) × Set M) : ℝ :=
  uprob fun c : DVert k → R => (c xA, c xB) = z.1 ∧ MA pr vA fA F c = z.2

/-- The conditional probability, given bridge challenges `s` (and `𝓜_A = S`), that `S` meets
`𝓜_B(F₁, r)`: only the `V_B` challenges of `c` matter (the `V_A` ones are ignored, the bridge ones
are replaced by `s`). It does not depend on the `A` side graph. -/
noncomputable def gB (F₁ : SimpleGraph (Fin k)) (z : (R × R) × Set M) : ℝ :=
  uprob fun c : DVert k → R => (z.2 ∩ MB pr vA fB F₁ (withBridge c z.1)).Nonempty

/-- `g ≥ 0`. -/
theorem gB_nonneg (F₁ : SimpleGraph (Fin k)) (z : (R × R) × Set M) : 0 ≤ gB pr vA fB F₁ z :=
  uprob_nonneg _

/-- `g ≤ 1`. -/
theorem gB_le_one (F₁ : SimpleGraph (Fin k)) (z : (R × R) × Set M) : gB pr vA fB F₁ z ≤ 1 :=
  uprob_le_one _

/-- `μA' F ≥ 0`. -/
theorem μA'_nonneg (F : SimpleGraph (Fin k)) (z : (R × R) × Set M) : 0 ≤ μA' pr vA fA F z :=
  uprob_nonneg _

variable [Fintype M]

/-- `μA' F` is a probability distribution. -/
theorem sum_μA' [Nonempty R] (F : SimpleGraph (Fin k)) : ∑ z, μA' pr vA fA F z = 1 := by
  have h := uprob_eq_sum_uprob_key (fun c : DVert k → R => ((c xA, c xB), MA pr vA fA F c))
    fun _ => True
  rw [uprob_true_eq_one] at h
  rw [h]
  refine sum_congr rfl fun z _ => congrArg uprob (funext fun c => propext ?_)
  simp [Prod.ext_iff]

/-- **Conditional independence.** Given the bridge challenges, `𝓜_A(F, r)` (a function of the
`V_A` challenges) and `𝓜_B(F₁, r)` (a function of the `V_B` challenges) are independent, so the
probability that they meet is `∑_z μA' F z · g(z)` with `g = gB F₁` independent of `F`. -/
theorem uprob_inter_nonempty_eq_sum (F F₁ : SimpleGraph (Fin k)) :
    uprob (fun c => (MA pr vA fA F c ∩ MB pr vA fB F₁ c).Nonempty) =
      ∑ z, μA' pr vA fA F z * gB pr vA fB F₁ z := by
  classical
  rw [uprob_eq_sum_uprob_key (fun c : DVert k → R => ((c xA, c xB), MA pr vA fA F c))]
  refine sum_congr rfl fun z _ => ?_
  obtain ⟨s, S⟩ := z
  have hcongr : (fun c : DVert k → R => ((c xA, c xB), MA pr vA fA F c) = (s, S) ∧
      (MA pr vA fA F c ∩ MB pr vA fB F₁ c).Nonempty) =
      fun c => ((c xA, c xB) = s ∧ MA pr vA fA F c = S) ∧
        (S ∩ MB pr vA fB F₁ (withBridge c s)).Nonempty := by
    funext c
    apply propext
    constructor
    · rintro ⟨h, hne⟩
      simp only [Prod.mk.injEq] at h
      have hs : (c xA, c xB) = s := h.1
      refine ⟨⟨hs, h.2⟩, ?_⟩
      rwa [withBridge_eq_self hs, ← h.2]
    · rintro ⟨⟨hs, hS⟩, hne⟩
      refine ⟨by rw [hs, hS], ?_⟩
      rwa [withBridge_eq_self hs, ← hS] at hne
  rw [hcongr, μA', gB]
  refine uprob_and_eq_mul_of_dependsOn (Ω := fun _ => R) (univ.filter fun u => u.isB = false)
    (fun σ τ h => ?_) (fun σ τ h => ?_)
  · have hA : σ xA = τ xA := h xA (mem_filter.2 ⟨mem_univ _, rfl⟩)
    have hB : σ xB = τ xB := h xB (mem_filter.2 ⟨mem_univ _, rfl⟩)
    rw [hA, hB, MA_congr pr vA fA F fun u hu => h u (by simpa using hu)]
  · rw [MB_congr pr vA fB F₁ (c' := withBridge τ s) fun u hu => ?_]
    cases u with
    | a i => simp [DVert.isA] at hu
    | b i => exact h (b i) fun hb => absurd (mem_filter.1 hb).2 (by simp [DVert.isB])
    | xA => rfl
    | xB => rfl

end JointLaw

/-! ### Repaired Lemma 3.11 and Theorem 1.4 -/

section Main

variable {k : ℕ} {R M : Type*} [Fintype R] [Nonempty R] [Fintype M]
  {pr : AMProtocol (DVert k) R M} {𝓕 : Finset (SimpleGraph (Fin k))} {vA : Fin k}
  {fA fB : (DVert k → Option R) → M → Prop}

/-- **Lemma 3.11 (repaired).** For a simple protocol deciding `Sym` on the dumbbell class and
distinct `F₁, F₂ ∈ 𝓕`, the *joint* laws `μA' F₁`, `μA' F₂` of (bridge challenges, `𝓜_A(F, r)`)
are `ℓ₁`-far: `‖μA' F₁ − μA' F₂‖₁ > 2/3`. (The paper's statement, about the marginal laws of
`𝓜_A(F, r)` alone, is false: `lemma_3_11_false`.) -/
theorem lemma_3_11_repaired (hS : IsSimple pr 𝓕 vA fA fB) (hD : pr.Decides (InClass 𝓕 vA) Sym)
    (hiff : ∀ FA ∈ 𝓕, ∀ FB ∈ 𝓕, Sym (dumbbell FA FB vA) ↔ FA = FB)
    {F₁ F₂ : SimpleGraph (Fin k)} (h₁ : F₁ ∈ 𝓕) (h₂ : F₂ ∈ 𝓕) (hne : F₁ ≠ F₂) :
    2 / 3 < ∑ z, |μA' pr vA fA F₁ z - μA' pr vA fA F₂ z| := by
  have hP₁ := (corollary_3_10 hS hD hiff h₁ h₁).1 rfl
  have hP₂ := (corollary_3_10 hS hD hiff h₂ h₁).2 hne.symm
  rw [uprob_inter_nonempty_eq_sum] at hP₁ hP₂
  have := sum_mul_sub_sum_mul_le_half_l1 _ _ _ (sum_μA' pr vA fA F₁) (sum_μA' pr vA fA F₂)
    (gB_nonneg pr vA fB F₁) (gB_le_one pr vA fB F₁)
  linarith

/-- **Theorem 1.4, core counting step (repaired).** For a simple protocol with challenge alphabet
`R` and response alphabet `M` deciding `Sym` on the dumbbell class built from `𝓕`,
`|𝓕| < 5^(|R|² · 2^|M|)`: the joint laws `μA' F`, `F ∈ 𝓕`, are pairwise `ℓ₁`-far distributions
(`lemma_3_11_repaired`) on a domain of size `|R|² · 2^|M|`, so the packing Lemma 3.12 applies.

Unlike the paper's bound `5^(2^(2^L))`, this one depends on the challenge alphabet: the argument
needs bounded randomness. -/
theorem card_family_lt (hS : IsSimple pr 𝓕 vA fA fB) (hD : pr.Decides (InClass 𝓕 vA) Sym)
    (hiff : ∀ FA ∈ 𝓕, ∀ FB ∈ 𝓕, Sym (dumbbell FA FB vA) ↔ FA = FB) :
    𝓕.card < 5 ^ (Fintype.card R ^ 2 * 2 ^ Fintype.card M) := by
  classical
  let e := Fintype.equivFin ((R × R) × Set M)
  have hd : Fintype.card ((R × R) × Set M) = Fintype.card R ^ 2 * 2 ^ Fintype.card M := by
    simp [Fintype.card_prod, Fintype.card_set, sq]
  let vec : SimpleGraph (Fin k) → Fin (Fintype.card ((R × R) × Set M)) → ℝ :=
    fun F i => μA' pr vA fA F (e.symm i)
  have hsum : ∀ F₁ F₂, ∑ i, |vec F₁ i - vec F₂ i| =
      ∑ z, |μA' pr vA fA F₁ z - μA' pr vA fA F₂ z| := fun F₁ F₂ =>
    Equiv.sum_comp e.symm (fun z => |μA' pr vA fA F₁ z - μA' pr vA fA F₂ z|)
  have hinj : Set.InjOn vec 𝓕 := by
    intro F₁ h₁ F₂ h₂ heq
    by_contra hne
    have := lemma_3_11_repaired hS hD hiff h₁ h₂ hne
    rw [← hsum, heq] at this
    simp only [sub_self, abs_zero, sum_const_zero] at this
    norm_num at this
  have key := lemma_3_12 (𝓕.image vec) ?_ ?_
  · calc 𝓕.card = (𝓕.image vec).card := (card_image_of_injOn hinj).symm
      _ < 5 ^ Fintype.card ((R × R) × Set M) := key
      _ = 5 ^ (Fintype.card R ^ 2 * 2 ^ Fintype.card M) := by rw [hd]
  · simp only [mem_image]
    rintro _ ⟨F, -, rfl⟩
    refine ⟨fun i => μA'_nonneg _ _ _ _ _, ?_⟩
    rw [Equiv.sum_comp e.symm (μA' pr vA fA F)]
    exact sum_μA' pr vA fA F
  · simp only [mem_image]
    rintro _ ⟨F₁, h₁, rfl⟩ _ ⟨F₂, h₂, rfl⟩ hne
    have hne' : F₁ ≠ F₂ := fun h => hne (h ▸ rfl)
    rw [hsum]
    linarith [lemma_3_11_repaired hS hD hiff h₁ h₂ hne']

/-- `2 L ≤ 2^L`. -/
theorem two_mul_le_two_pow (L : ℕ) : 2 * L ≤ 2 ^ L := by
  induction L with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      rw [pow_succ]
      omega

/-- With `L`-bit challenges and responses, `|𝓕| < 2^(3 · 2^(2^(L+1)))`. -/
theorem card_family_lt_two_pow {L : ℕ} (hS : IsSimple pr 𝓕 vA fA fB)
    (hD : pr.Decides (InClass 𝓕 vA) Sym)
    (hiff : ∀ FA ∈ 𝓕, ∀ FB ∈ 𝓕, Sym (dumbbell FA FB vA) ↔ FA = FB)
    (hR : Fintype.card R ≤ 2 ^ L) (hM : Fintype.card M ≤ 2 ^ L) :
    𝓕.card < 2 ^ (3 * 2 ^ 2 ^ (L + 1)) := by
  have hD' : Fintype.card R ^ 2 * 2 ^ Fintype.card M ≤ 2 ^ 2 ^ (L + 1) := by
    calc Fintype.card R ^ 2 * 2 ^ Fintype.card M ≤ (2 ^ L) ^ 2 * 2 ^ 2 ^ L :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hR 2) (Nat.pow_le_pow_right (by norm_num) hM)
      _ = 2 ^ (2 * L + 2 ^ L) := by rw [← pow_mul, ← pow_add, mul_comm L 2]
      _ ≤ 2 ^ 2 ^ (L + 1) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [pow_succ]
          have := two_mul_le_two_pow L
          omega
  calc 𝓕.card < 5 ^ (Fintype.card R ^ 2 * 2 ^ Fintype.card M) := card_family_lt hS hD hiff
    _ ≤ 8 ^ (Fintype.card R ^ 2 * 2 ^ Fintype.card M) := Nat.pow_le_pow_left (by norm_num) _
    _ ≤ 8 ^ 2 ^ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) hD'
    _ = 2 ^ (3 * 2 ^ 2 ^ (L + 1)) := by rw [pow_mul]; norm_num

/-- **Theorem 1.4 (repaired; logarithmic form).** For a simple protocol with `L`-bit challenges and
responses deciding `Sym` on the dumbbell class built from `𝓕`,
`log₂ |𝓕| < 3 · 2^(2^(L+1))`. -/
theorem theorem_1_4_repaired_log {L : ℕ} (hS : IsSimple pr 𝓕 vA fA fB)
    (hD : pr.Decides (InClass 𝓕 vA) Sym)
    (hiff : ∀ FA ∈ 𝓕, ∀ FB ∈ 𝓕, Sym (dumbbell FA FB vA) ↔ FA = FB)
    (hR : Fintype.card R ≤ 2 ^ L) (hM : Fintype.card M ≤ 2 ^ L) :
    Nat.log 2 𝓕.card < 3 * 2 ^ 2 ^ (L + 1) := by
  rcases Nat.eq_zero_or_pos 𝓕.card with h0 | hpos
  · rw [h0, Nat.log_zero_right]
    positivity
  · exact Nat.log_lt_of_lt_pow hpos.ne' (card_family_lt_two_pow hS hD hiff hR hM)

/-- **Theorem 1.4 (repaired).** Let `𝓕` be a family of graphs on `k` vertices with
`|𝓕| ≥ 2^(c k²)` (the paper uses such a family of asymmetric, pairwise non-isomorphic graphs, with
`G(F_A, F_B)` symmetric iff `F_A = F_B`: hypothesis `hiff`). If a simple dAM protocol (Definition 6)
with `L`-bit challenges and `L`-bit responses decides `Sym` on the dumbbell class built from `𝓕`,
then `c k² < 3 · 2^(2^(L+1))`, i.e. `L ≥ log₂ log₂ (c k² / 3) − 1 = log log k − O(1)`.

This is the paper's `Sym ∉ dAM[o(log log n)]` (with Lemma 3.7, simple protocols cost only a factor
`4` in `L`), via the repaired Lemma 3.11. The proof needs the challenge length to be bounded by `L`
as well (as in Definition 1); for protocols with unbounded randomness, which the introduction
suggests are also covered, this argument does not apply. -/
theorem theorem_1_4_repaired {L : ℕ} {c : ℝ} (hS : IsSimple pr 𝓕 vA fA fB)
    (hD : pr.Decides (InClass 𝓕 vA) Sym)
    (hiff : ∀ FA ∈ 𝓕, ∀ FB ∈ 𝓕, Sym (dumbbell FA FB vA) ↔ FA = FB)
    (hR : Fintype.card R ≤ 2 ^ L) (hM : Fintype.card M ≤ 2 ^ L)
    (hF : (2 : ℝ) ^ (c * (k : ℝ) ^ 2) ≤ 𝓕.card) :
    c * (k : ℝ) ^ 2 < 3 * 2 ^ 2 ^ (L + 1) := by
  have h := card_family_lt_two_pow hS hD hiff hR hM
  have h' : (𝓕.card : ℝ) < (2 : ℝ) ^ ((3 * 2 ^ 2 ^ (L + 1) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast h
  have := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 (hF.trans_lt h')
  exact_mod_cast this

end Main

/-! ### Non-vacuity: the counterexample to the original Lemma 3.11 satisfies the hypotheses -/

section NonVacuity

/-- The paper's claim `hiff` holds for the counterexample family `{F₁, F₂}`. -/
theorem cexFamily_hiff :
    ∀ FA ∈ cexFamily, ∀ FB ∈ cexFamily, Sym (dumbbell FA FB 0) ↔ FA = FB := by
  intro FA hA FB hB
  rcases mem_cexFamily.1 hA with rfl | rfl <;> rcases mem_cexFamily.1 hB with rfl | rfl
  · exact iff_of_true (sym_dumbbell_self _ _) rfl
  · exact iff_of_false not_sym_G₁₂ F₁_ne_F₂
  · exact iff_of_false not_sym_G₂₁ F₁_ne_F₂.symm
  · exact iff_of_true (sym_dumbbell_self _ _) rfl

/-- On the counterexample protocol the *marginal* laws `μ_A(F₁) = μ_A(F₂)` coincide
(`μA_F₁_eq_F₂`), but the *joint* laws with the bridge challenges are `ℓ₁`-far, as the repaired
Lemma 3.11 predicts. -/
theorem cex_joint_laws_far :
    2 / 3 < ∑ z, |μA' cexPr 0 bridgeOK F₁ z - μA' cexPr 0 bridgeOK F₂ z| :=
  lemma_3_11_repaired (cexProtocol_isSimple _ _ _) cexPr_decides cexFamily_hiff
    (mem_cexFamily.2 (Or.inl rfl)) (mem_cexFamily.2 (Or.inr rfl)) F₁_ne_F₂

end NonVacuity

end Podc.InteractiveDistributedProofs.LowerBound
