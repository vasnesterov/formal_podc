import Papers.PODC2013.CubicBitsBA.Protocol

/-!
# Section 5 of Kowalski–Mostéfaoui: the parts that hold

* `lemma_1`: correct processes confirm each other's messages and never suspect each other
  (only `|byz| ≤ t` is needed).
* `lemma_2`: the decorations of the nodes whose label ends with a correct id are the same at all
  correct processes.
* `lemma_3`: for such nodes, `newval = val` (needs `n > 3t`).
* `theorem_1`: validity.
* `lemma_4`: the nodes whose label ends with a correct id form a common path covering.
-/

namespace Podc.CubicBitsBA

variable {n : ℕ} {V : Type} [DecidableEq V]

/-! ### Generic lemmas about lists over `Fin n` -/

lemma length_filter_finRange (p : Fin n → Bool) :
    ((List.finRange n).filter p).length = (Finset.univ.filter fun k => p k = true).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext k
  simp

lemma count_add_count_le {α : Type} [DecidableEq α] (l : List α) {a b : α} (hab : a ≠ b) :
    l.count a + l.count b ≤ l.length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.count_cons, List.length_cons, beq_iff_eq]
    split_ifs with h1 h2 <;> subst_vars <;> first | exact absurd rfl hab | omega

lemma majority_eq_some {α : Type} [DecidableEq α] {l : List α} {a : α}
    (h : l.length < 2 * l.count a) : majority l = some a := by
  have ha : a ∈ l := List.count_pos_iff.mp (by omega)
  unfold majority
  cases hf : l.find? (fun b => decide (l.length < 2 * l.count b)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simpa using h) (hf a ha)
  | some b =>
    have hb := List.find?_some hf
    simp only [decide_eq_true_eq] at hb
    by_contra hne
    have := count_add_count_le l (a := a) (b := b) (fun e => hne (by rw [e]))
    omega

lemma majority_spec {α : Type} [DecidableEq α] {l : List α} {a : α} (h : majority l = some a) :
    l.length < 2 * l.count a := by
  have := List.find?_some h
  simpa using this

lemma count_map_filter_finRange {α : Type} [DecidableEq α] (p : Fin n → Bool) (f : Fin n → α)
    (a : α) : (((List.finRange n).filter p).map f).count a =
      (Finset.univ.filter fun k => p k = true ∧ f k = a).card := by
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter, List.filter_filter, length_filter_finRange]
  congr 1
  ext k
  simp [and_comm]

/-! ### The messages of correct processes -/

@[simp] lemma out_one (t : ℕ) (x : V) (ib : View n V) : out t x ib 1 = { v1 := some x } := rfl

lemma out_sus (t : ℕ) (x : V) (ib : View n V) {r : ℕ} (hr : 3 ≤ r) :
    (out t x ib r).sus = susp t ib (r - 1) := by
  match r, hr with
  | 3, _ => rfl
  | r + 4, _ => rfl

lemma out_ek (t : ℕ) (x : V) (ib : View n V) {r : ℕ} (hr : 4 ≤ r) (k : Fin n) :
    (out t x ib r).ek k = (recv t ib (r - 1) k).map (·.sus) := by
  match r, hr with
  | r + 4, _ => rfl

lemma out_e2 (t : ℕ) (x : V) (ib : View n V) (j : Fin n) :
    (out t x ib 2).e2 j = (recv t ib 1 j).bind (·.v1) := rfl

omit [DecidableEq V] in
lemma recvF_of_false {S : Fin n → Bool} (ib : View n V) (r : ℕ) {j : Fin n} (h : S j = false) :
    recvF S ib r j = ib r j := by
  simp [recvF, h]

lemma recv_succ (t : ℕ) (ib : View n V) (r : ℕ) (j : Fin n) :
    recv t ib (r + 1) j = recvF (susp t ib r) ib (r + 1) j := rfl

/-- A correct process echoes in round `r + 1` exactly what it received in round `r`. -/
lemma echoMatch_out (t : ℕ) (x : V) (ib : View n V) {r : ℕ} (hr : 1 ≤ r) {j : Fin n}
    {m : Msg n V} (hm : recv t ib r j = some m) (h1 : r = 1 → m.v1.isSome) :
    echoMatch r m (out t x ib (r + 1)) j = true := by
  match r, hr with
  | 1, _ => simp [echoMatch, out_e2, hm, h1 rfl]
  | 2, _ => simp [echoMatch, out, hm]
  | r + 3, _ => simp [echoMatch, out, hm]

/-! ### Lemma 1 -/

section Exec

variable {t : ℕ} (E : Exec n t V)

lemma card_correct_ge (hb : E.byz.card ≤ t) :
    n - t ≤ (Finset.univ.filter fun k => k ∉ E.byz).card := by
  have := Finset.card_compl E.byz
  rw [Finset.compl_eq_univ_sdiff] at this
  have h2 : (Finset.univ.filter fun k => k ∉ E.byz) = Finset.univ \ E.byz := by
    ext; simp
  rw [h2, this, Fintype.card_fin]
  omega

/-- **Lemma 1** of [Kowalski–Mostéfaoui]: a correct process never suspects a correct process
(within the `t + 1` rounds). -/
theorem susp_correct (hb : E.byz.card ≤ t) :
    ∀ r, r ≤ t + 1 → ∀ i ∉ E.byz, ∀ j ∉ E.byz, susp t (E.view i) r j = false
  | 0, _ => by intros; rfl
  | 1, _ => by intros; rfl
  | r + 2, hr => by
    intro i hi j hj
    have ih0 := susp_correct hb r (by omega)
    have ih1 := susp_correct hb (r + 1) (by omega)
    simp only [susp, ih1 i hi j hj, Bool.false_or, Bool.not_eq_false']
    have hm : recvF (susp t (E.view i) r) (E.view i) (r + 1) j =
        some (out t (E.input j) (E.view j) (r + 1)) := by
      rw [recvF_of_false _ _ (ih0 i hi j hj)]
      exact E.honest j hj i (r + 1) (by omega) (by omega)
    rw [confirmed, hm]
    simp only [decide_eq_true_eq]
    refine (card_correct_ge E hb).trans ?_
    rw [echoCount, length_filter_finRange]
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [recvF_of_false _ _ (ih1 i hi k hk),
      E.honest k hk i (r + 2) (by omega) (by omega)]
    apply echoMatch_out t _ _ (by omega)
    · rw [recv_succ, recvF_of_false _ _ (ih0 k hk j hj)]
      exact E.honest j hj k (r + 1) (by omega) (by omega)
    · intro h
      obtain rfl : r = 0 := by omega
      rfl

/-- What a correct process receives from a correct process `k` in round `1 ≤ r ≤ t + 1` is `k`'s
message (it is never discarded). -/
lemma recv_correct (hb : E.byz.card ≤ t) {i k : Fin n} (hi : i ∉ E.byz) (hk : k ∉ E.byz)
    {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1) :
    recv t (E.view i) r k = some (out t (E.input k) (E.view k) r) := by
  rw [recv, recvF_of_false _ _ (susp_correct E hb (r - 1) (by omega) i hi k hk)]
  exact E.honest k hk i r hr1 hr

/-- **Lemma 1** of [Kowalski–Mostéfaoui]: each message sent by a correct process in round `r` is
confirmed by every correct process in round `r + 1`; equivalently, a correct process never
suspects a correct process. -/
theorem lemma_1 (hb : E.byz.card ≤ t) {i j : Fin n} (hi : i ∉ E.byz) (hj : j ∉ E.byz) {r : ℕ}
    (hr1 : 1 ≤ r) (hr : r + 1 ≤ t + 1) :
    confirmed t (susp t (E.view i) (r - 1)) (susp t (E.view i) r) (E.view i) r j = true ∧
      ∀ r' ≤ t + 1, susp t (E.view i) r' j = false := by
  refine ⟨?_, fun r' hr' => susp_correct E hb r' hr' i hi j hj⟩
  have h := susp_correct E hb (r + 1) hr i hi j hj
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [susp, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
  exact h.2

/-! ### Lemma 2 -/

lemma any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih => simp_all

/-- A correct process `k`'s suspicion reports, as seen by a correct process. -/
lemma rep_correct (hb : E.byz.card ≤ t) {i k : Fin n} (hi : i ∉ E.byz) (hk : k ∉ E.byz) {r : ℕ}
    (hr3 : 3 ≤ r) (hr : r ≤ t + 1) (j : Fin n) :
    rep t (E.view i) r k j = susp t (E.view k) (r - 1) j := by
  simp only [rep, recv_correct E hb hi hk (by omega) hr, out_sus _ _ _ hr3]

/-- A correct process `k`'s echoes of suspicion reports, as seen by a correct process. -/
lemma erep_correct (hb : E.byz.card ≤ t) {i k : Fin n} (hi : i ∉ E.byz) (hk : k ∉ E.byz) {r : ℕ}
    (hr4 : 4 ≤ r) (hr : r ≤ t + 1) (j m : Fin n) :
    erep t (E.view i) r k j m =
      match recv t (E.view k) (r - 1) j with
      | some mm => mm.sus m
      | none => false := by
  simp only [erep, recv_correct E hb hi hk (by omega) hr, out_ek _ _ _ hr4]
  cases recv t (E.view k) (r - 1) j <;> rfl

lemma repBy_congr {ib ib' : View n V} {a : ℕ} {l : Fin n}
    (h : ∀ r, 3 ≤ r → r ≤ a → rep t ib r l = rep t ib' r l) (k : Fin n) :
    repBy t ib a l k = repBy t ib' a l k := by
  unfold repBy
  apply any_congr_mem
  intro r hr
  rw [List.mem_range'_1] at hr
  rw [h r (by omega) (by omega)]

lemma erepBy_congr {ib ib' : View n V} {a : ℕ} {l : Fin n}
    (h : ∀ r, 4 ≤ r → r ≤ a → erep t ib r l = erep t ib' r l) (k j : Fin n) :
    erepBy t ib a l k j = erepBy t ib' a l k j := by
  unfold erepBy
  apply any_congr_mem
  intro r hr
  rw [List.mem_range'_1] at hr
  rw [h r (by omega) (by omega)]

/-- **Lemma 2** of [Kowalski–Mostéfaoui]: if `i`, `i'` and `k` are correct, the decorations
`val` and `cval` of every node whose label ends with `k` are the same in the trees of `i` and
`i'`. -/
theorem lemma_2 (hb : E.byz.card ≤ t) {i i' k : Fin n} (hi : i ∉ E.byz) (hi' : i' ∉ E.byz)
    (hk : k ∉ E.byz) :
    val1 t (E.view i) k = val1 t (E.view i') k ∧
    (1 ≤ t → ∀ j, cval2 t (E.view i) k j = cval2 t (E.view i') k j) ∧
    (∀ y, valB t (E.view i) (k :: y) = valB t (E.view i') (k :: y)) ∧
    (∀ y, leafVal t (E.view i) (k :: y) = leafVal t (E.view i') (k :: y)) ∧
    (∀ y, cvalB t (E.view i) (k :: y) = cvalB t (E.view i') (k :: y)) := by
  have hrep : ∀ r, 3 ≤ r → r ≤ t + 1 → rep t (E.view i) r k = rep t (E.view i') r k := by
    intro r h3 hr; funext j
    rw [rep_correct E hb hi hk h3 hr, rep_correct E hb hi' hk h3 hr]
  have herep : ∀ r, 4 ≤ r → r ≤ t + 1 → erep t (E.view i) r k = erep t (E.view i') r k := by
    intro r h4 hr; funext j m
    rw [erep_correct E hb hi hk h4 hr, erep_correct E hb hi' hk h4 hr]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [val1, recv_correct E hb hi hk le_rfl (by omega),
      recv_correct E hb hi' hk le_rfl (by omega)]
  · intro ht j
    simp only [cval2, recv_correct E hb hi hk (r := 2) (by omega) (by omega),
      recv_correct E hb hi' hk (r := 2) (by omega) (by omega)]
  · rintro (_ | ⟨m, y⟩)
    · rfl
    · simp only [valB]
      rw [repBy_congr (fun r h3 hr => hrep r h3 (by omega))]
  · rintro (_ | ⟨m, y⟩)
    · rfl
    · simp only [leafVal]
      rw [repBy_congr (fun r h3 hr => hrep r h3 hr)]
  · rintro (_ | ⟨j, _ | ⟨m, y⟩⟩)
    · rfl
    · rfl
    · simp only [cvalB]
      rw [erepBy_congr (fun r h4 hr => herep r h4 hr)]

/-! ### Lemma 3 -/

/-- A correct process never reports (directly) that it suspects a correct process. -/
lemma repBy_correct (hb : E.byz.card ≤ t) {i k j : Fin n} (hi : i ∉ E.byz) (hk : k ∉ E.byz)
    (hj : j ∉ E.byz) {a : ℕ} (ha : a ≤ t + 1) : repBy t (E.view i) a k j = false := by
  simp only [repBy, List.any_eq_false, List.mem_range'_1, Bool.not_eq_true]
  intro r hr
  rw [rep_correct E hb hi hk (by omega) (by omega)]
  exact susp_correct E hb _ (by omega) k hk j hj

/-- Echoed reports of a correct `j` by a correct `k` are `j`'s direct reports, one round later. -/
lemma erepBy_eq_repBy (hb : E.byz.card ≤ t) {i k j : Fin n} (hi : i ∉ E.byz) (hk : k ∉ E.byz)
    (hj : j ∉ E.byz) (m : Fin n) :
    erepBy t (E.view i) (t + 1) k j m = repBy t (E.view i) t j m := by
  unfold erepBy repBy
  have h4 : List.range' 4 (t + 1 - 3) = (List.range' 3 (t - 2)).map (· + 1) := by
    have hf : (fun x : ℕ => x + 1) = (1 + ·) := funext fun x => Nat.add_comm _ _
    rw [hf, List.map_add_range', show t + 1 - 3 = t - 2 by omega]
  rw [h4, List.any_map]
  apply any_congr_mem
  intro r hr
  rw [List.mem_range'_1] at hr
  simp only [Function.comp_apply]
  rw [erep_correct E hb hi hk (by omega) (by omega), rep_correct E hb hi hj (by omega) (by omega),
    show r + 1 - 1 = r by omega, recv_correct E hb hk hj (r := r) (by omega) (by omega)]
  dsimp only
  rw [out_sus _ _ _ (by omega : 3 ≤ r)]

/-- Counting core of Lemma 3: if all correct children are in `T` and agree on `f`, the majority
rule returns their common value (needs `|x| + 2t < n`). -/
lemma majority_childIds {α : Type} [DecidableEq α] (byz : Finset (Fin n)) (hb : byz.card ≤ t)
    (x : List (Fin n)) (hx : x.length + 2 * t < n) (p : Fin n → Bool) (f : Fin n → α) (b : α)
    (hp : ∀ k, k ∉ x → k ∉ byz → p k = true) (hf : ∀ k, k ∉ x → k ∉ byz → f k = b) :
    n - t - x.length ≤ (childIds x p).length ∧ majority ((childIds x p).map f) = some b := by
  set C := Finset.univ.filter fun k : Fin n => k ∉ x ∧ k ∉ byz with hC
  have hCcard : n - x.length - t ≤ C.card := by
    have h1 : C = Finset.univ \ (x.toFinset ∪ byz) := by ext; simp [hC]
    have h2 := Finset.card_union_le x.toFinset byz
    have h3 := List.toFinset_card_le x
    rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hS : (childIds x p).length =
      (Finset.univ.filter fun k => (!decide (k ∈ x) && p k) = true).card :=
    length_filter_finRange _
  have hCS : C ⊆ Finset.univ.filter fun k => (!decide (k ∈ x) && p k) = true := by
    intro k hk
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp [hk.1, hp k hk.1 hk.2]
  have hSC : (Finset.univ.filter fun k => (!decide (k ∈ x) && p k) = true) ⊆ C ∪ byz := by
    intro k hk
    by_cases hkb : k ∈ byz
    · exact Finset.mem_union_right _ hkb
    · apply Finset.mem_union_left
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not] at hk
      simp [hC, hk.1, hkb]
  have hCb : C ⊆ Finset.univ.filter fun k => (!decide (k ∈ x) && p k) = true ∧ f k = b := by
    intro k hk
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp [hk.1, hp k hk.1 hk.2, hf k hk.1 hk.2]
  have hS1 := Finset.card_le_card hCS
  have hS2 := (Finset.card_le_card hSC).trans (Finset.card_union_le _ _)
  have hS3 := Finset.card_le_card hCb
  refine ⟨by rw [hS]; omega, majority_eq_some ?_⟩
  rw [List.length_map, childIds, count_map_filter_finRange, ← childIds, hS]
  omega

/-- **Lemma 3** of [Kowalski–Mostéfaoui], levels `≥ 2`, by induction on the distance `d` to the
leaves: if the label `x` ends with a correct id, `newval(x) = val(x)` at every correct process. -/
theorem nvB_correct (hn : 3 * t < n) (hb : E.byz.card ≤ t) {i : Fin n} (hi : i ∉ E.byz) :
    ∀ d (j : Fin n) (y : List (Fin n)), j ∉ E.byz → (j :: y).Nodup →
      (j :: y).length + d = t + 1 → 2 ≤ (j :: y).length →
      nvB t (E.view i) d (j :: y) =
        if d = 0 then leafVal t (E.view i) (j :: y) else valB t (E.view i) (j :: y)
  | 0, j, y, _, _, _, _ => rfl
  | d + 1, j, y, hj, hnd, hlen, h2 => by
    obtain ⟨m, y', rfl⟩ : ∃ m y', y = m :: y' := by
      cases y with
      | nil => simp at h2
      | cons m y' => exact ⟨m, y', rfl⟩
    have hA : ∀ k, k ∉ j :: m :: y' → k ∉ E.byz → nvB t (E.view i) d (k :: j :: m :: y') = true := by
      intro k hkx hk
      rw [nvB_correct hn hb hi d k (j :: m :: y') hk (List.nodup_cons.mpr ⟨hkx, hnd⟩)
        (by simp only [List.length_cons] at hlen ⊢; omega) (by simp)]
      split_ifs
      · simp [leafVal, repBy_correct E hb hi hk hj le_rfl]
      · simp only [valB, repBy_correct E hb hi hk hj (a := t) (by omega), Bool.not_false]
    have hB : ∀ k, k ∉ j :: m :: y' → k ∉ E.byz →
        cvalB t (E.view i) (k :: j :: m :: y') = valB t (E.view i) (j :: m :: y') := by
      intro k _ hk
      simp only [cvalB, valB, erepBy_eq_repBy E hb hi hk hj]
    have hlen' : (j :: m :: y').length + 2 * t < n := by
      simp only [List.length_cons] at hlen ⊢; omega
    obtain ⟨hT, hM⟩ := majority_childIds E.byz hb (j :: m :: y') hlen'
      (fun k => nvB t (E.view i) d (k :: j :: m :: y'))
      (fun k => cvalB t (E.view i) (k :: j :: m :: y')) _ hA hB
    simp only [nvB, hM, Nat.add_one_ne_zero, ↓reduceIte]
    simp only [hT, decide_true, Bool.true_and]
    cases valB t (E.view i) (j :: m :: y') <;> decide

/-- **Lemma 3** of [Kowalski–Mostéfaoui] (levels `2..t+1`): for a label `x` (distinct ids,
`2 ≤ |x| ≤ t + 1`) ending with a correct id, there is a value `v` with `val(x)_i = newval(x)_i = v`
for every correct process `i` (`val` = `leafVal` on the leaves, `valB` on the internal nodes). -/
theorem lemma_3 (hn : 3 * t < n) (hb : E.byz.card ≤ t) {j : Fin n} {y : List (Fin n)}
    (hj : j ∉ E.byz) (hnd : (j :: y).Nodup) (h2 : 2 ≤ (j :: y).length)
    (ht : (j :: y).length ≤ t + 1) :
    ∃ v : Bool, ∀ i ∉ E.byz,
      (if (j :: y).length = t + 1 then leafVal t (E.view i) (j :: y)
        else valB t (E.view i) (j :: y)) = v ∧ newvalB t (E.view i) (j :: y) = v := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ E.byz := by
    by_contra h; push Not at h
    have : (Finset.univ : Finset (Fin n)) ⊆ E.byz := fun k _ => h k
    have := Finset.card_le_card this
    simp at this; omega
  refine ⟨if (j :: y).length = t + 1 then leafVal t (E.view i₀) (j :: y)
    else valB t (E.view i₀) (j :: y), fun i hi => ⟨?_, ?_⟩⟩
  · have h := lemma_2 E hb hi hi₀ hj
    split_ifs
    · exact h.2.2.2.1 y
    · exact h.2.2.1 y
  · have h := lemma_2 E hb hi hi₀ hj
    rw [newvalB, nvB_correct E hn hb hi _ j y hj hnd (by omega) h2]
    split_ifs <;> first | omega | exact h.2.2.2.1 y | exact h.2.2.1 y

/-- `newval` of the level-2 node `[k, j]` (paper label `jk`) for correct `j`, `k` is `⊤`. -/
lemma newvalB_pair (hn : 3 * t < n) (hb : E.byz.card ≤ t) (ht : 1 ≤ t) {i j k : Fin n}
    (hi : i ∉ E.byz) (hj : j ∉ E.byz) (hk : k ∉ E.byz) (hkj : k ≠ j) :
    newvalB t (E.view i) [k, j] = true := by
  rw [newvalB, nvB_correct E hn hb hi _ k [j] hk (by simp [hkj])
    (by simp only [List.length_cons, List.length_nil]; omega) (by simp)]
  split_ifs
  · simp [leafVal, repBy_correct E hb hi hk hj le_rfl]
  · simp [valB, repBy_correct E hb hi hk hj (a := t) (by omega)]

/-- **Lemma 3** of [Kowalski–Mostéfaoui] on level 1: for a correct `j`, `val(j)_i = newval(j)_i`
is `j`'s proposal at every correct process `i`. -/
theorem lemma_3_level1 (hn : 3 * t < n) (hb : E.byz.card ≤ t) {i j : Fin n} (hi : i ∉ E.byz)
    (hj : j ∉ E.byz) :
    val1 t (E.view i) j = some (E.input j) ∧ newval1 t (E.view i) j = some (E.input j) := by
  have hval : val1 t (E.view i) j = some (E.input j) := by
    simp only [val1, recv_correct E hb hi hj le_rfl (by omega), out_one, Option.bind_some]
  have hx1 (ht : t ≠ 0) : [j].length + 2 * t < n := by
    simp only [List.length_cons, List.length_nil]; omega
  refine ⟨hval, ?_⟩
  unfold newval1
  split_ifs with ht0 hT
  · exact hval
  · have hM := (majority_childIds E.byz hb [j] (hx1 ht0)
      (fun k => newvalB t (E.view i) [k, j]) (fun k => cval2 t (E.view i) k j) (some (E.input j))
      (fun k hkx hk => newvalB_pair E hn hb (by omega) hi hj hk (by simpa using hkx))
      (fun k hkx hk => by
        simp only [cval2, recv_correct E hb hi hk (r := 2) (by omega) (by omega), out_e2,
          Option.bind_some, recv_correct E hb hk hj (r := 1) le_rfl (by omega), out_one])).2
    rw [top1, hM]; rfl
  · exfalso; apply hT
    exact (majority_childIds E.byz hb [j] (hx1 ht0)
      (fun k => newvalB t (E.view i) [k, j]) (fun _ => (0 : ℕ)) 0
      (fun k hkx hk => newvalB_pair E hn hb (by omega) hi hj hk (by simpa using hkx))
      (fun _ _ _ => rfl)).1

/-! ### Theorem 1 (validity) -/

/-- **Theorem 1** (validity) of [Kowalski–Mostéfaoui]: if all correct processes propose `v`, every
correct process decides `v`. -/
theorem theorem_1 (hn : 3 * t < n) (hb : E.byz.card ≤ t) (v0 v : V)
    (hv : ∀ j ∉ E.byz, E.input j = v) {i : Fin n} (hi : i ∉ E.byz) : E.decide v0 i = v := by
  have hM := (majority_childIds E.byz hb [] (by simp; omega) (fun _ => true)
    (fun j => newval1 t (E.view i) j) (some v) (fun _ _ _ => rfl)
    (fun k _ hk => by rw [(lemma_3_level1 E hn hb hi hk).2, hv k hk])).2
  have hc : childIds ([] : List (Fin n)) (fun _ => true) = List.finRange n := by
    simp [childIds]
  rw [hc] at hM
  simp only [Exec.decide, decision, hM]

/-! ### Lemma 4 (common path covering) -/

/-- The common value at a node: the decision at the root, `newval1` on level 1, `newvalB` below. -/
def Common (v0 : V) (x : List (Fin n)) : Prop :=
  ∀ i ∉ E.byz, ∀ i' ∉ E.byz,
    (x = [] → E.decide v0 i = E.decide v0 i') ∧
    (∀ j, x = [j] → newval1 t (E.view i) j = newval1 t (E.view i') j) ∧
    (2 ≤ x.length → newvalB t (E.view i) x = newvalB t (E.view i') x)

/-- A set `C` of nodes is a *path covering* of the subtree rooted at `z` if every path from `z` to a
leaf below `z` contains a node of `C`. Labels are reversed lists, so the leaves below `z` are the
lists `w ++ z` of `t + 1` distinct ids, and the nodes on the path are their suffixes
`(w ++ z).drop k`, `k ≤ |w|`. -/
def PathCoveringAt (t : ℕ) (C : Set (List (Fin n))) (z : List (Fin n)) : Prop :=
  ∀ w : List (Fin n), (w ++ z).Nodup → (w ++ z).length = t + 1 →
    ∃ k ≤ w.length, (w ++ z).drop k ∈ C

/-- **Lemma 4** of [Kowalski–Mostéfaoui]: the nodes whose label ends with a correct id form a
path covering of the whole tree all of whose nodes are common. -/
theorem lemma_4 (hn : 3 * t < n) (hb : E.byz.card ≤ t) (v0 : V) :
    ∃ C : Set (List (Fin n)), PathCoveringAt t C [] ∧ ∀ x ∈ C, Common E v0 x := by
  refine ⟨{x | x.Nodup ∧ x.length ≤ t + 1 ∧ ∃ k y, x = k :: y ∧ k ∉ E.byz}, ?_, ?_⟩
  · intro w hnd hlen
    rw [List.append_nil] at hnd hlen ⊢
    obtain ⟨k, hkw, hk⟩ : ∃ k ∈ w, k ∉ E.byz := by
      by_contra h; push Not at h
      have h1 : w.toFinset ⊆ E.byz := fun k hk => h k (List.mem_toFinset.mp hk)
      have := Finset.card_le_card h1
      rw [List.toFinset_card_of_nodup hnd] at this
      omega
    obtain ⟨s, u, rfl⟩ := List.append_of_mem hkw
    refine ⟨s.length, by simp, ?_, ?_, k, u, ?_, hk⟩
    · rw [List.drop_left]; exact (List.nodup_append.mp hnd).2.1
    · rw [List.drop_left]; simp only [List.length_append, List.length_cons] at hlen ⊢; omega
    · rw [List.drop_left]
  · rintro x ⟨hnd, hlen, k, y, rfl, hk⟩ i hi i' hi'
    refine ⟨fun h => absurd h (by simp), ?_, ?_⟩
    · intro j hj
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hj
      rw [(lemma_3_level1 E hn hb hi hk).2, (lemma_3_level1 E hn hb hi' hk).2]
    · intro h2
      obtain ⟨v, hv⟩ := lemma_3 E hn hb hk hnd h2 hlen
      rw [(hv i hi).2, (hv i' hi').2]

end Exec

end Podc.CubicBitsBA
