import Papers.PODC2011.ErrorFreeMultivaluedBC.Algorithm

/-!
# One generation of Algorithm 1: Lemmas 1–5

Liang–Vaidya, PODC 2011 (arXiv:1101.3520), Section 3. Throughout, `σ : Gen n t α β` is one
generation, `3t < n`, at most `t` processors are faulty, and the diagnosis graph at the start of the
generation contains all edges between fault-free processors (`GoodClique`, established for every
generation in `Theorem.lean` from Lemma 4).
-/

namespace Podc.ErrorFreeMultivaluedBC

open Finset

/-- All edges between distinct fault-free processors are present ("the fault-free processors
always trust each other"). -/
def GoodClique {n : ℕ} (F : Finset (Fin n)) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j, i ∉ F → j ∉ F → i ≠ j → G.Adj i j

namespace Gen

variable {n t : ℕ} {α β : Type*} (σ : Gen n t α β)

open Classical

/-! ### Unfolding lemmas for fault-free processors -/

section Unfold

variable {σ} {i j : Fin n}

theorem R_of_notMem (hj : j ∉ σ.F) : σ.R i j = σ.S j j := by simp [R, hj]

theorem M_of_notMem (hj : j ∉ σ.F) (k : Fin n) :
    σ.M j k ↔ σ.G.Adj j k ∧ σ.R j k = σ.S j k := by simp [M, hj]

theorem Det_of_notMem (hj : j ∉ σ.F) :
    σ.Det j ↔ ¬σ.A.C.Consistent (σ.X j σ.Pm) (σ.R j) := by simp [Det, hj]

theorem Rs_of_notMem (hj : j ∉ σ.F) : σ.Rs j = σ.S j j := by simp [Rs, hj]

theorem Trust_of_notMem (hi : i ∉ σ.F) (j : Fin n) :
    σ.Trust i j ↔ σ.G.Adj i j ∧ σ.R i j = σ.Rs j := by simp [Trust, hi]

theorem mem_X {P : Finset (Fin n)} {k : Fin n} :
    k ∈ σ.X i P ↔ k ∈ P ∧ (k = i ∨ σ.G.Adj i k) := by simp [X]

theorem G1_le : σ.G1 ≤ σ.G := fun _ _ h => h.1

theorem G2_le : σ.G2 ≤ σ.G1 := by
  intro j k h
  unfold G2 at h
  split_ifs at h
  · exact h.1
  · exact h

theorem G3_le : σ.G3 ≤ σ.G2 := fun _ _ h => h.1

theorem G3_le_G : σ.G3 ≤ σ.G := σ.G1_le.trans' (σ.G2_le.trans' σ.G3_le)

theorem next_le : σ.next ≤ σ.G := by
  unfold next; split_ifs
  · exact σ.G3_le_G
  · exact le_rfl

end Unfold

/-! ### Counting fault-free members -/

theorem card_sdiff_ge {P : Finset (Fin n)} (hP : P.card = n - t) (hF : σ.F.card ≤ t) :
    n - 2 * t ≤ (P \ σ.F).card := by
  have := Finset.le_card_sdiff σ.F P
  omega

theorem exists_good_mem {P : Finset (Fin n)} (hP : P.card = n - t) (hF : σ.F.card ≤ t)
    (hnt : 3 * t < n) : ∃ k, k ∈ P ∧ k ∉ σ.F := by
  have h := σ.card_sdiff_ge hP hF
  obtain ⟨k, hk⟩ : (P \ σ.F).Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨k, (Finset.mem_sdiff.mp hk).1, (Finset.mem_sdiff.mp hk).2⟩

/-! ### Lemma 1 -/

/-- **Lemma 1.** If all fault-free processors have the same input, a matching set `P_match`
exists (assuming the fault-free processors trust each other). -/
theorem lemma_1 (hF : σ.F.card ≤ t) (hG : GoodClique σ.F σ.G) {w : α}
    (hw : ∀ i, i ∉ σ.F → σ.v i = w) : σ.MatchExists := by
  have hcard : n - t ≤ (univ \ σ.F).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]; omega
  obtain ⟨P, hPs, hPc⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨P, hPc, fun j hj k hk hjk => ?_⟩
  have hj' := (mem_sdiff.mp (hPs hj)).2
  have hk' := (mem_sdiff.mp (hPs hk)).2
  rw [M_of_notMem hj', R_of_notMem hk']
  exact ⟨hG j k hj' hk' hjk, by simp [S, hw j hj', hw k hk']⟩

/-! ### Lemma 2 -/

/-- In a matching set, the codeword of a fault-free member `i` agrees at every fault-free member
`m` with the symbol `S_m[m]` sent by `m`. -/
theorem S_eq_of_isMatch {P : Finset (Fin n)} (hP : σ.IsMatch P) {i m : Fin n} (hi : i ∈ P)
    (hiF : i ∉ σ.F) (hm : m ∈ P) (hmF : m ∉ σ.F) : σ.S i m = σ.S m m := by
  by_cases him : i = m
  · rw [him]
  have := (M_of_notMem hiF m).mp (hP.2 i hi m hm him)
  rw [R_of_notMem hmF] at this
  exact this.2.symm

/-- **Lemma 2.** The fault-free processors in a matching set have the same input. -/
theorem lemma_2 (hF : σ.F.card ≤ t) {P : Finset (Fin n)} (hP : σ.IsMatch P) {i j : Fin n}
    (hi : i ∈ P) (hiF : i ∉ σ.F) (hj : j ∈ P) (hjF : j ∉ σ.F) : σ.v i = σ.v j :=
  σ.A.C.eq_of_agree (P \ σ.F) (σ.card_sdiff_ge hP.1 hF) _ _ fun m hm => by
    have hm' := mem_sdiff.mp hm
    exact (σ.S_eq_of_isMatch hP hi hiF hm'.1 hm'.2).trans
      (σ.S_eq_of_isMatch hP hj hjF hm'.1 hm'.2).symm

/-- The symbols of the fault-free members of a matching set are those of the common codeword. -/
theorem S_self_eq (hF : σ.F.card ≤ t) {P : Finset (Fin n)} (hP : σ.IsMatch P) {k m : Fin n}
    (hk : k ∈ P) (hkF : k ∉ σ.F) (hm : m ∈ P) (hmF : m ∉ σ.F) :
    σ.S m m = σ.A.C.enc (σ.v k) m := by
  rw [σ.lemma_2 hF hP hk hkF hm hmF]; rfl

/-- A fault-free member `k` of a matching set received from every other member `m` the symbol of
its own codeword, and trusts `m`. -/
theorem R_of_isMatch {P : Finset (Fin n)} (hP : σ.IsMatch P) {k m : Fin n} (hk : k ∈ P)
    (hkF : k ∉ σ.F) (hm : m ∈ P) (hkm : k ≠ m) :
    σ.G.Adj k m ∧ σ.R k m = σ.A.C.enc (σ.v k) m :=
  (M_of_notMem hkF m).mp (hP.2 k hk m hm hkm)

/-! ### Lemma 3 -/

/-- **Lemma 3.** If no (counted) processor announces a detection, every fault-free processor
decides the common input `v_k(g)` of the fault-free members `k` of `P_match`. -/
theorem lemma_3 (hF : σ.F.card ≤ t) (hG : GoodClique σ.F σ.G)
    (hP : σ.IsMatch σ.Pm) (hD : ¬σ.Diag) {k : Fin n} (hk : k ∈ σ.Pm) (hkF : k ∉ σ.F)
    {i : Fin n} (hiF : i ∉ σ.F) : σ.out i = σ.v k := by
  have hME : σ.MatchExists := ⟨_, hP⟩
  simp only [out, hME, not_true_eq_false, ite_false, hD]
  have hB : σ.Pm \ σ.F ⊆ σ.X i σ.Pm := fun m hm => by
    obtain ⟨hm1, hm2⟩ := mem_sdiff.mp hm
    refine (mem_X).mpr ⟨hm1, ?_⟩
    by_cases hmi : m = i
    · exact Or.inl hmi
    · exact Or.inr (hG i m hiF hm2 (Ne.symm hmi))
  have hBc := σ.card_sdiff_ge hP.1 hF
  have hagree : ∀ m ∈ σ.Pm \ σ.F, σ.A.C.enc (σ.v k) m = σ.R i m := fun m hm => by
    obtain ⟨hm1, hm2⟩ := mem_sdiff.mp hm
    rw [R_of_notMem hm2, σ.S_self_eq hF hP hk hkF hm1 hm2]
  -- `R_i/X ∈ C`
  have hcons : σ.A.C.Consistent (σ.X i σ.Pm) (σ.R i) := by
    by_cases hiP : i ∈ σ.Pm
    · refine ⟨σ.v k, fun m hm => ?_⟩
      obtain ⟨hm1, hm2⟩ := (mem_X).mp hm
      rcases hm2 with rfl | _
      · rw [R_of_notMem hiF, σ.S_self_eq hF hP hk hkF hm1 hiF]
      · by_cases hmi : m = i
        · subst hmi; rw [R_of_notMem hiF, σ.S_self_eq hF hP hk hkF hm1 hiF]
        · rw [(σ.R_of_isMatch hP hiP hiF hm1 (Ne.symm hmi)).2, σ.lemma_2 hF hP hiP hiF hk hkF]
    · by_contra hnc
      apply hD
      refine ⟨i, hiP, ?_, (Det_of_notMem hiF).mpr hnc⟩
      refine Or.inr ⟨k, hG i k hiF hkF ?_⟩
      rintro rfl; exact hiP hk
  exact σ.A.C.decode_eq (hBc.trans (card_le_card hB))
    (σ.A.C.agree_of_consistent hcons hB hBc hagree)

/-! ### Lemma 4 -/

/-- **Lemma 4, invariance.** The diagnosis stage removes only edges at faulty processors: the
fault-free processors still trust each other in the updated diagnosis graph. -/
theorem lemma_4_goodClique (hF : σ.F.card ≤ t) (hG : GoodClique σ.F σ.G) :
    GoodClique σ.F σ.G3 := by
  -- step 3(e)
  have h1 : GoodClique σ.F σ.G1 := fun i j hi hj hij => by
    refine ⟨hG i j hi hj hij, fun _ => ?_, fun _ => ?_⟩
    · exact (Trust_of_notMem hi j).mpr ⟨hG i j hi hj hij, by rw [R_of_notMem hj, Rs_of_notMem hj]⟩
    · exact (Trust_of_notMem hj i).mpr
        ⟨hG j i hj hi (Ne.symm hij), by rw [R_of_notMem hi, Rs_of_notMem hi]⟩
  -- step 3(f): a fault-free processor is never isolated
  have hiso : ∀ i, i ∉ σ.F → σ.A.C.Consistent σ.Pm σ.Rs → i ∉ σ.IsoF := by
    rintro i hi ⟨x, hx⟩ ⟨hiP, -, hdet, hkeep⟩
    refine (Det_of_notMem hi).mp hdet ⟨x, fun m hm => ?_⟩
    obtain ⟨hm1, hm2⟩ := (mem_X).mp hm
    rcases hm2 with rfl | hadj
    · exact absurd hm1 hiP
    · have := ((Trust_of_notMem hi m).mp ((hkeep m hadj).2.1 hm1)).2
      rw [this]; exact hx m hm1
  have h2 : GoodClique σ.F σ.G2 := fun i j hi hj hij => by
    unfold G2; split_ifs with hc
    · exact ⟨h1 i j hi hj hij, hiso i hi hc, hiso j hj hc⟩
    · exact h1 i j hi hj hij
  -- step 3(g): a fault-free processor has at most `t` removed edges
  have hrem : ∀ i, i ∉ σ.F → removed σ.G2 i ≤ t := fun i hi => by
    refine (card_le_card fun k hk => ?_).trans hF
    simp only [mem_filter, mem_univ, true_and] at hk
    by_contra hkF
    exact hk.2 (h2 i k hi hkF (Ne.symm hk.1))
  intro i j hi hj hij
  refine ⟨h2 i j hi hj hij, ?_, ?_⟩ <;> simp only [Set.mem_ofPred_eq, not_le, Nat.lt_succ_iff]
  · exact hrem i hi
  · exact hrem j hj

/-- **Lemma 4, progress** (repaired algorithm). Every diagnosis stage removes, in steps 3(e)–3(f),
at least one edge at a faulty processor. -/
theorem lemma_4_progress (hnt : 3 * t < n) (hF : σ.F.card ≤ t) (hvar : σ.A.var = .repaired)
    (hP : σ.IsMatch σ.Pm) (hD : σ.Diag) :
    ∃ f ∈ σ.F, ∃ k, σ.G.Adj f k ∧ ¬σ.G2.Adj f k := by
  obtain ⟨k₀, hk₀, hk₀F⟩ := σ.exists_good_mem hP.1 hF hnt
  set w := σ.v k₀
  -- a faulty member `m` of `P_match` whose `R#[m]` is not the common symbol loses its edge to `k₀`
  have claimC : ∀ m ∈ σ.Pm, m ∈ σ.F → σ.Rs m ≠ σ.A.C.enc w m →
      ∃ f ∈ σ.F, ∃ k, σ.G.Adj f k ∧ ¬σ.G2.Adj f k := by
    intro m hm hmF hne
    have hk₀m : k₀ ≠ m := fun h => hk₀F (h ▸ hmF)
    obtain ⟨hadj, hR⟩ := σ.R_of_isMatch hP hk₀ hk₀F hm hk₀m
    refine ⟨m, hmF, k₀, hadj.symm, fun h => ?_⟩
    have h1 := σ.G2_le h
    have := ((Trust_of_notMem hk₀F m).mp (h1.2.2 hm)).2
    exact hne (this ▸ hR)
  obtain ⟨j, hjP, hjc, hjd⟩ := hD
  by_cases hjF : j ∈ σ.F
  · -- a faulty processor announced a detection
    by_cases hrm : ∃ k, σ.G.Adj j k ∧ ¬σ.G1.Adj j k
    · obtain ⟨k, hk1, hk2⟩ := hrm
      exact ⟨j, hjF, k, hk1, fun h => hk2 (σ.G2_le h)⟩
    push Not at hrm
    by_cases hc : σ.A.C.Consistent σ.Pm σ.Rs
    · -- step 3(f) isolates `j`, which still has an edge (here the repair is used)
      obtain ⟨k, hk⟩ : ∃ k, σ.G.Adj j k := by
        rcases hjc with h | h
        · rw [hvar] at h; cases h
        · exact h
      refine ⟨j, hjF, k, hk, fun h => ?_⟩
      unfold G2 at h
      simp only [hc, ↓reduceIte] at h
      exact h.2.1 ⟨hjP, hjc, hjd, hrm⟩
    · -- `R#/P_match ∉ C`: some faulty member of `P_match` broadcast a wrong symbol
      by_contra hcon
      apply hc
      refine ⟨w, fun m hm => ?_⟩
      by_contra hne
      by_cases hmF : m ∈ σ.F
      · exact hcon (claimC m hm hmF (Ne.symm hne))
      · exact hne (by rw [Rs_of_notMem hmF, σ.S_self_eq hF hP hk₀ hk₀F hm hmF])
  · -- a fault-free processor detected an inconsistency
    have hnc := (Det_of_notMem hjF).mp hjd
    have : ∃ m ∈ σ.X j σ.Pm, σ.A.C.enc w m ≠ σ.R j m := by
      by_contra h
      push Not at h
      exact hnc ⟨w, h⟩
    obtain ⟨m, hmX, hne⟩ := this
    obtain ⟨hm, hmj⟩ := (mem_X).mp hmX
    have hadj : σ.G.Adj j m := by
      rcases hmj with rfl | h
      · exact absurd hm hjP
      · exact h
    have hmF : m ∈ σ.F := by
      by_contra hmF
      exact hne (by rw [R_of_notMem hmF, σ.S_self_eq hF hP hk₀ hk₀F hm hmF])
    by_cases hrs : σ.Rs m = σ.A.C.enc w m
    · refine ⟨m, hmF, j, hadj.symm, fun h => ?_⟩
      have := ((Trust_of_notMem hjF m).mp ((σ.G2_le h).2.2 hm)).2
      exact hne (by rw [this, hrs])
    · exact claimC m hm hmF hrs

/-! ### Lemma 5 -/

/-- **Lemma 5, existence of `P_decide`** (first sentence of the proof): a set `P_decide ⊆ P_match`
of `n - 2t` pairwise trusting processors in the updated diagnosis graph exists, so the validity
requirement on the adversary's choice of `P_decide` in `ChoicesValid` can always be met. -/
theorem exists_pdecide (hF : σ.F.card ≤ t) (hG : GoodClique σ.F σ.G) (hP : σ.IsMatch σ.Pm) :
    ∃ P ⊆ σ.Pm, P.card = n - 2 * t ∧ ∀ j ∈ P, ∀ k ∈ P, j ≠ k → σ.G3.Adj j k := by
  obtain ⟨P, hPs, hPc⟩ := Finset.exists_subset_card_eq (σ.card_sdiff_ge hP.1 hF)
  refine ⟨P, hPs.trans sdiff_subset, hPc, fun j hj k hk hjk => ?_⟩
  exact σ.lemma_4_goodClique hF hG j k (mem_sdiff.mp (hPs hj)).2 (mem_sdiff.mp (hPs hk)).2 hjk

/-- **Lemma 5.** After the diagnosis stage, every fault-free processor decides the common input
`v_k(g)` of the fault-free members `k` of `P_match`. -/
theorem lemma_5 (hnt : 3 * t < n) (hF : σ.F.card ≤ t) (hV : σ.ChoicesValid)
    (hD : σ.Diagnosed) {k : Fin n} (hk : k ∈ σ.Pm) (hkF : k ∉ σ.F) {i : Fin n} :
    σ.out i = σ.v k := by
  have hP := hV.1 hD.1
  obtain ⟨hsub, hcard, hpair⟩ := hV.2 hD
  simp only [out, hD.1, not_true_eq_false, ite_false, hD.2, ite_true]
  -- a fault-free member `k'` of `P_decide`
  obtain ⟨k', hk', hk'F⟩ : ∃ k', k' ∈ σ.a.pdecide ∧ k' ∉ σ.F := by
    by_contra h
    push Not at h
    have := card_le_card (show σ.a.pdecide ⊆ σ.F from h)
    omega
  rw [σ.lemma_2 hF hP hk hkF (hsub hk') hk'F]
  refine σ.A.C.decode_eq (by rw [hcard]) fun m hm => ?_
  by_cases hmk : k' = m
  · subst hmk; rw [Rs_of_notMem hk'F]; rfl
  · have h1 := σ.G2_le (σ.G3_le (hpair k' hk' m hm hmk))
    have := ((Trust_of_notMem hk'F m).mp (h1.2.1 (hsub hm))).2
    rw [← this, (σ.R_of_isMatch hP (hsub hk') hk'F (hsub hm) hmk).2]

/-! ### Consensus in one generation -/

/-- If a matching set exists, every fault-free processor decides the common input of the
fault-free members of `P_match` (Lemmas 3 and 5). -/
theorem out_eq_of_matchExists (hnt : 3 * t < n) (hF : σ.F.card ≤ t) (hG : GoodClique σ.F σ.G)
    (hV : σ.ChoicesValid) (hME : σ.MatchExists) {k : Fin n} (hk : k ∈ σ.Pm) (hkF : k ∉ σ.F)
    {i : Fin n} (hiF : i ∉ σ.F) : σ.out i = σ.v k := by
  by_cases hD : σ.Diag
  · exact σ.lemma_5 hnt hF hV ⟨hME, hD⟩ hk hkF
  · exact σ.lemma_3 hF hG (hV.1 hME) hD hk hkF hiF

/-- **One generation solves consensus**: all fault-free processors decide the same value, and if
all fault-free inputs are `w`, this value is `w`. -/
theorem consensus (hnt : 3 * t < n) (hF : σ.F.card ≤ t) (hG : GoodClique σ.F σ.G)
    (hV : σ.ChoicesValid) :
    Cslib.Byzantine.Problem.Consensus σ.v (↑σ.F)ᶜ σ.out := by
  by_cases hME : σ.MatchExists
  · obtain ⟨k, hk, hkF⟩ := σ.exists_good_mem (hV.1 hME).1 hF hnt
    refine ⟨fun i hi j hj => ?_, fun w hw i hi => ?_⟩
    · rw [σ.out_eq_of_matchExists hnt hF hG hV hME hk hkF hi,
        σ.out_eq_of_matchExists hnt hF hG hV hME hk hkF hj]
    · rw [σ.out_eq_of_matchExists hnt hF hG hV hME hk hkF hi]
      exact hw k hkF
  · refine ⟨fun i _ j _ => by simp [out, hME], fun w hw i _ => ?_⟩
    exact absurd (σ.lemma_1 hF hG fun i hi => hw i hi) hME

end Gen

end Podc.ErrorFreeMultivaluedBC
