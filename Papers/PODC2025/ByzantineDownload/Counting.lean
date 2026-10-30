import Papers.PODC2025.ByzantineDownload.Model

/-!
# Round-robin leaders: `nextView` and the query-counting argument of Theorem 5.9

* `lt_nextView`, `lead_nextView_notMem`, `lead_mem_of_lt_of_lt_nextView`: `nextView F v` is the least
  view `> v` whose leader is not in `F` (when some peer is not in `F`).
* `roundRobin_count`: if a strictly increasing sequence of views `V 0 < V 1 < ⋯ < V (M-1)` skips only
  views whose leaders lie in a set `Bad`, then a peer `p ∉ Bad` leads at most
  `(M - 1)/(k - |Bad|) + 1` of them. This is the paper's "every nonfaulty peer leads at most
  `n/γk` views" (proof of Theorem 5.9).
-/

namespace Podc.ByzantineDownload

variable {k : ℕ} [NeZero k]

lemma lead_val (v : ℕ) : (lead (k := k) v).val = v % k := rfl

lemma lead_add_injective (a : ℕ) :
    Function.Injective (fun i : Fin k => lead (k := k) (a + i)) := by
  have key : ∀ i j : Fin k, (i : ℕ) ≤ j → (a + i) % k = (a + j) % k → i = j := by
    intro i j hij h
    have h0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    have e : a + j - (a + i) = j - i := by omega
    rw [e, Nat.mod_eq_of_lt (by omega)] at h0
    exact Fin.ext (by omega)
  intro i j h
  have h' : (a + i) % k = (a + j) % k := congrArg Fin.val h
  rcases le_total (i : ℕ) j with hij | hij
  · exact key i j hij h'
  · exact (key j i hij h'.symm).symm

lemma exists_lead_eq (a : ℕ) (q : Fin k) : ∃ d < k, lead (k := k) (a + d) = q := by
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp (lead_add_injective (k := k) a)) q
  exact ⟨i, i.isLt, hi⟩

lemma lt_nextView (F : Finset (Fin k)) (v : ℕ) : v < nextView F v := by
  unfold nextView
  split <;> omega

lemma lead_nextView_notMem (F : Finset (Fin k)) (v : ℕ) (hF : ∃ q, q ∉ F) :
    lead (nextView F v) ∉ F := by
  unfold nextView
  split
  · next d hd =>
    simpa using List.find?_some hd
  · next hd =>
    exfalso
    obtain ⟨q, hq⟩ := hF
    obtain ⟨d, hdk, hd'⟩ := exists_lead_eq (k := k) (v + 1) q
    rw [List.find?_eq_none] at hd
    have := hd d (List.mem_range.mpr hdk)
    simp [hd', hq] at this

lemma lead_mem_of_lt_of_lt_nextView (F : Finset (Fin k)) {v u : ℕ} (h1 : v < u)
    (h2 : u < nextView F v) : lead u ∈ F := by
  unfold nextView at h2
  split at h2
  · next d hd =>
    rw [List.find?_eq_some_iff_getElem] at hd
    obtain ⟨_, i, hi, hid, hbefore⟩ := hd
    simp only [List.getElem_range] at hid
    subst hid
    have := hbefore (u - (v + 1)) (by omega)
    have e : v + 1 + (u - (v + 1)) = u := by omega
    simpa [e] using this
  · omega

section Count

variable (Bad : Finset (Fin k))

/-- Number of views `u < b` whose leader is not in `Bad`. -/
def goodBelow (b : ℕ) : ℕ := ∑ u ∈ Finset.range b, if lead (k := k) u ∉ Bad then 1 else 0

lemma goodBelow_succ (b : ℕ) :
    goodBelow Bad (b + 1) = goodBelow Bad b + (if lead (k := k) b ∉ Bad then 1 else 0) :=
  Finset.sum_range_succ _ _

lemma goodBelow_mono {a b : ℕ} (h : a ≤ b) : goodBelow Bad a ≤ goodBelow Bad b :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

lemma goodBelow_add_k (a : ℕ) : goodBelow Bad (a + k) = goodBelow Bad a + (k - Bad.card) := by
  unfold goodBelow
  rw [Finset.sum_range_add]
  congr 1
  rw [Finset.sum_range (fun i => if lead (k := k) (a + i) ∉ Bad then 1 else 0)]
  have := Equiv.sum_comp
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (lead_add_injective (k := k) a)))
    (fun q => if q ∉ Bad then 1 else 0)
  simp only [Equiv.ofBijective_apply] at this
  rw [this, Finset.sum_boole]
  simp [Finset.filter_not, Finset.card_sdiff]

lemma goodBelow_add_mul (a j : ℕ) :
    goodBelow Bad (a + j * k) = goodBelow Bad a + j * (k - Bad.card) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show a + (j + 1) * k = (a + j * k) + k by ring, goodBelow_add_k, ih]
    ring

end Count

/-- Round-robin counting (proof of Theorem 5.9). -/
theorem roundRobin_count (Bad : Finset (Fin k)) (p : Fin k) (hp : p ∉ Bad) (M : ℕ) (V : ℕ → ℕ)
    (hmono : ∀ m, m + 1 < M → V m < V (m + 1))
    (hskip : ∀ m, m + 1 < M → ∀ u, V m < u → u < V (m + 1) → lead u ∈ Bad) :
    (((Finset.range M).filter (fun m => lead (V m) = p)).card - 1) * (k - Bad.card) ≤ M - 1 := by
  set S := (Finset.range M).filter (fun m => lead (V m) = p) with hS
  -- strict monotonicity on `[0, M)`
  have hlt : ∀ j, j < M → ∀ i, i < j → V i < V j := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi
      have := hmono j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact (ih (by omega) i hi).trans this
      · subst hi; exact this
  have hle : ∀ j, j < M → ∀ i, i ≤ j → V i ≤ V j := by
    intro j hj i hi
    rcases Nat.lt_or_eq_of_le hi with hi | hi
    · exact (hlt j hj i hi).le
    · subst hi; rfl
  -- views between consecutive `V m` contribute nothing
  have hflat : ∀ m, m + 1 < M → ∀ u, V m + 1 ≤ u → u ≤ V (m + 1) →
      goodBelow Bad u = goodBelow Bad (V m + 1) := by
    intro m hm u hu1 hu2
    induction u, hu1 using Nat.le_induction with
    | base => rfl
    | succ u hu ih =>
      have hb := hskip m hm u (by omega) (by omega)
      rw [goodBelow_succ, ih (by omega), ite_eq_right (by simpa using hb)]
      simp
  have hcount : ∀ m, m < M → goodBelow Bad (V m + 1) ≤ goodBelow Bad (V 0) + (m + 1) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [goodBelow_succ]
      split <;> omega
    | succ m ih =>
      intro hm
      rw [goodBelow_succ, hflat m hm _ (hmono m hm) le_rfl]
      have := ih (by omega)
      split <;> omega
  by_cases hc : S.card = 0
  · simp [hc]
  -- the map `m ↦ (V m - V 0) / k` is injective on `S`
  have hinj : Set.InjOn (fun m => (V m - V 0) / k) S := by
    intro m hm m' hm' h
    simp only [hS, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hm hm'
    simp only at h
    have hr : (V m - V 0) % k = (V m' - V 0) % k := by
      have h1 : V m % k = V m' % k := by
        have := congrArg Fin.val (hm.2.trans hm'.2.symm)
        simpa [lead_val] using this
      have h0m := hle m hm.1 0 (Nat.zero_le _)
      have h0m' := hle m' hm'.1 0 (Nat.zero_le _)
      have : (V m - V 0 + V 0) ≡ (V m' - V 0 + V 0) [MOD k] := by
        rw [Nat.sub_add_cancel h0m, Nat.sub_add_cancel h0m']
        exact h1
      exact Nat.ModEq.add_right_cancel' _ this
    have hV : V m = V m' := by
      have h0m := hle m hm.1 0 (Nat.zero_le _)
      have h0m' := hle m' hm'.1 0 (Nat.zero_le _)
      have e1 := Nat.div_add_mod (V m - V 0) k
      have e2 := Nat.div_add_mod (V m' - V 0) k
      rw [h, hr] at e1
      omega
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd hV (hlt m' hm'.1 m h').ne
    · exact absurd hV (hlt m hm.1 m' h').ne'
  have hcardT : (S.image (fun m => (V m - V 0) / k)).card = S.card :=
    Finset.card_image_of_injOn hinj
  -- some element of the image is `≥ S.card - 1`
  obtain ⟨x, hxT, hx⟩ : ∃ x ∈ S.image (fun m => (V m - V 0) / k), S.card - 1 ≤ x := by
    by_contra hne
    push Not at hne
    have hsub : S.image (fun m => (V m - V 0) / k) ⊆ Finset.range (S.card - 1) := by
      intro y hy
      exact Finset.mem_range.mpr (hne y hy)
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    omega
  obtain ⟨m, hmS, rfl⟩ := Finset.mem_image.mp hxT
  simp only [hS, Finset.mem_filter, Finset.mem_range] at hmS
  have hM : 0 < M := by omega
  have h0m := hle m hmS.1 0 (Nat.zero_le _)
  have hmM := hle (M - 1) (by omega) m (by omega)
  have hkpos : 0 < k := Nat.pos_of_neZero k
  have hge : (S.card - 1) * k ≤ V m - V 0 := (Nat.le_div_iff_mul_le hkpos).mp hx
  have step1 := goodBelow_add_mul Bad (V 0) (S.card - 1)
  have step2 := goodBelow_mono Bad (show V 0 + (S.card - 1) * k ≤ V m by omega)
  have step3 := goodBelow_succ Bad (V m)
  rw [ite_eq_left (by rw [hmS.2]; exact hp)] at step3
  have step4 := goodBelow_mono Bad (show V m + 1 ≤ V (M - 1) + 1 by omega)
  have step5 := hcount (M - 1) (by omega)
  rw [Nat.sub_add_cancel hM] at step5
  omega

end Podc.ByzantineDownload
