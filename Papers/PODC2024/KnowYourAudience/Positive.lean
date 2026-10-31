import Papers.PODC2024.KnowYourAudience.Algorithm
import Papers.PODC2024.KnowYourAudience.Counterexample
import Papers.PODC2024.KnowYourAudience.Impossibility

/-!
# Positive results (Sections 4.2–4.5)

The view-based algorithm (`viewAlg`) instantiated for each communication model:

* outdegree awareness and output port awareness: views tagged with the outdegree, `b` = the tag;
* symmetric communications: untagged views (simple broadcast), `b` = the number of children of
  the root of a view (indegree = outdegree in a bidirectional network).

`decode_eventually`: eventually every agent decodes a nonempty multiset `u` with
`n • u = |u| • ⟦x⟧` (same frequencies as the input). Consequences:

* `computable_of_frequencyBased` — **Theorem 4.1, (i) ⇒ (ii)** (and Corollary 4.2, (i) ⇒ (ii)).
* `computable_of_frequencyBasedFrom_two`, `computable_of_frequencyBasedFrom_three_symmetric` —
  the converses of the corrected impossibility results: with an extra test for `n = 1`
  (indegree `1`), resp. for `n ∈ {1, 2}` (symmetric communications), the corrected classes are
  computable. Together with `Impossibility.lean` this gives the exact characterisation.
* `computable_sizeEq_of_multisetBased` — Corollary 4.3, (i) ⇒ (ii): knowing `n`, the multiset of
  inputs is recovered from `u` (`recover`).
* `computable_leader_of_multisetBased` — Corollary 4.4, (i) ⇒ (ii): with one leader, `n` is
  recovered from the frequency of the leader's input.
-/

namespace Podc.KnowYourAudience

open Cslib.AnonNet Finset Filter Topology

open scoped Classical

universe u v

variable {I : Type u} {X : Type v}

/-! ### Model parameters -/

/-- Tag function: the outdegree, except with symmetric communications. -/
def ddOf : CommModel → ℕ → ℕ
  | .symmetric => fun _ => 0
  | _ => id

/-- Reading off the outdegree of the root of a view. -/
noncomputable def bOf : CommModel → ∀ s, Msg I (s + 1) → ℕ
  | .symmetric => fun s c => Multiset.card (Msg.kids s c)
  | _ => fun s c => Msg.tag (s + 1) c

lemma viewAlg_allowed {m : CommModel} (hm : m ≠ .broadcast)
    (G : (Σ t, St I t) → Option (Multiset I) → X) :
    m.Allowed (viewAlg (ddOf m) (bOf m) G) := by
  cases m with
  | broadcast => exact absurd rfl hm
  | outdegree => exact viewAlg_allowed_outdegree _ G
  | outPort => exact viewAlg_allowed_outPort _ _ G
  | symmetric => exact viewAlg_allowed_symmetric _ G

lemma bOf_msg {m : CommModel} (hm : m ≠ .broadcast) {V : Type*} [Fintype V] [DecidableEq V]
    {N : Network V} (hN : m.NetOK N) (x : V → I) (s : ℕ) (j : V) :
    bOf m s (msg N x (ddOf m) (s + 1) j) = N.outdeg j := by
  cases m with
  | broadcast => exact absurd rfl hm
  | outdegree => rfl
  | outPort => rfl
  | symmetric =>
    simp only [bOf, kids_msg, Multiset.card_map, Finset.card_val]
    rw [hN.inN_eq]; rfl

/-- Eventually every agent is in its view state and decodes the input frequencies. -/
theorem decode_eventually {m : CommModel} (hm : m ≠ .broadcast) {n : ℕ} (hn : 0 < n)
    (N : Network (Fin n)) (hsc : N.StronglyConnected) (hN : m.NetOK N) (x : Fin n → I)
    (G : (Σ t, St I t) → Option (Multiset I) → X) :
    ∀ᶠ t in atTop, ∀ i, N.run (viewAlg (ddOf m) (bOf m) G) x t i = ⟨t, stOf N x (ddOf m) t i⟩ ∧
      ∃ u, decodeQ (bOf m) ⟨t, stOf N x (ddOf m) t i⟩ = some u ∧ u ≠ 0 ∧
        n • u = Multiset.card u • (List.ofFn x : Multiset I) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  filter_upwards [viewAlg_decode N x (ddOf m) hsc (bOf m) (bOf_msg hm hN x) G] with t ht i
  obtain ⟨u, hu, hu0, he⟩ := ht i
  rw [run_viewAlg] at hu
  refine ⟨run_viewAlg N x _ _ G t i, u, hu, hu0, ?_⟩
  rw [Fintype.card_fin, Fin.univ_val_map] at he
  exact he

/-! ### From the decoded multiset to the inputs -/

/-- If `n • u = |u| • M` then `u.toList` has the frequencies of `M`. -/
lemma freq_toList_eq [DecidableEq I] {n : ℕ} {u : Multiset I} {l : List I} (hl : l.length = n)
    (hn : 0 < n)
    (hu : u ≠ 0) (he : n • u = Multiset.card u • (l : Multiset I)) : freq u.toList = freq l := by
  have hl0 : l ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hu0 : u.toList ≠ [] := by simpa using hu
  rw [freq_eq_freq_iff hu0 hl0]
  intro a
  have := congrArg (Multiset.count a) he
  rw [Multiset.count_nsmul, Multiset.count_nsmul, Multiset.coe_count] at this
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.length_toList, hl]
  linarith [Nat.mul_comm n (u.count a), Nat.mul_comm (Multiset.card u) (l.count a)]

/-- Recover a multiset `M` with `|M| = n` from `u` with `n • u = |u| • M`. -/
noncomputable def recover (n : ℕ) (u : Multiset I) : Multiset I :=
  ∑ a ∈ u.toFinset, (u.count a * n / Multiset.card u) • ({a} : Multiset I)

lemma recover_eq {n : ℕ} {u M : Multiset I} (hu : u ≠ 0)
    (he : n • u = Multiset.card u • M) : recover n u = M := by
  have hc : 0 < Multiset.card u := Multiset.card_pos.2 hu
  ext b
  rw [recover, Multiset.count_sum']
  have hb := congrArg (Multiset.count b) he
  rw [Multiset.count_nsmul, Multiset.count_nsmul] at hb
  by_cases hbu : b ∈ u.toFinset
  · rw [Finset.sum_eq_single b]
    · rw [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one, mul_comm, hb,
        Nat.mul_div_cancel_left _ hc]
    · intro a _ hab
      rw [Multiset.count_nsmul, Multiset.count_singleton, ite_eq_right (Ne.symm hab), mul_zero]
    · intro h; exact absurd hbu h
  · rw [Finset.sum_eq_zero]
    · rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hbu
      rw [hbu, mul_zero] at hb
      exact ((Nat.mul_eq_zero.1 hb.symm).resolve_left hc.ne').symm
    · intro a ha
      rw [Multiset.count_nsmul, Multiset.count_singleton, ite_eq_right, mul_zero]
      rintro rfl; exact hbu ha

/-! ### Theorem 4.1, (i) ⇒ (ii) -/

/-- Output map for frequency-based functions. -/
noncomputable def outFreq (f : List I → X) (q : Σ t, St I t) : Option (Multiset I) → X
  | some u => f u.toList
  | none => f [St.input q.1 q.2]

/-- **Theorem 4.1, (i) ⇒ (ii).** With outdegree awareness, output port awareness or symmetric
communications, every frequency-based function is computable (in finite time, hence for every
metric) in the class of static strongly connected networks. -/
theorem computable_of_frequencyBased [DecidableEq I] [TopologicalSpace X] {m : CommModel}
    (hm : m ≠ .broadcast)
    {f : List I → X} (hf : FrequencyBased f) : Computable m staticSC (fun _ => True) f := by
  refine ⟨viewAlg (ddOf m) (bOf m) (outFreq f), viewAlg_allowed hm _, ?_⟩
  intro n hn N hsc hN x _ i
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [decode_eventually hm hn N hsc hN x (outFreq f)] with t ht
  obtain ⟨hrun, u, hu, hu0, he⟩ := ht i
  rw [viewAlg_out, hrun, hu, outFreq]
  exact hf _ _ (by simpa using hu0) (List.ne_nil_of_length_pos (by simpa using hn))
    (freq_toList_eq (List.length_ofFn) hn hu0 he)

/-- Corollary 4.2, (i) ⇒ (ii): a fortiori in every class `C_{≤B}`. -/
theorem computable_sizeLE_of_frequencyBased [DecidableEq I] [TopologicalSpace X] {m : CommModel}
    (hm : m ≠ .broadcast) {f : List I → X} (hf : FrequencyBased f) (B : ℕ) :
    Computable m (sizeLE B) (fun _ => True) f := by
  obtain ⟨A, hA, hc⟩ := computable_of_frequencyBased hm hf
  exact ⟨A, hA, fun n hn N hN hok => hc n hn N hN.1 hok⟩

/-! ### The corrected classes are computable -/

/-- The number of messages received in the last round (`0` initially). -/
def inCard : (Σ t, St I t) → ℕ
  | ⟨_ + 1, s⟩ => Multiset.card s.2
  | _ => 0

lemma inCard_stOf {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) (x : V → I)
    (dd : ℕ → ℕ) (t : ℕ) (i : V) : inCard ⟨t + 1, stOf N x dd (t + 1) i⟩ = (N.inN i).card := by
  simp [inCard, stOf]

/-- Output map: `n = 1` is detected by the indegree; otherwise frequencies, doubled. -/
noncomputable def outFreq2 (f : List I → X) (q : Σ t, St I t) (o : Option (Multiset I)) : X :=
  if inCard q = 1 then f [St.input q.1 q.2] else
    match o with
    | some u => f (u + u).toList
    | none => f [St.input q.1 q.2]

/-- The corrected class for outdegree / output port awareness is computable: frequency-based on
vectors of length `≥ 2`, arbitrary on vectors of length `1`. -/
theorem computable_of_frequencyBasedFrom_two [DecidableEq I] [TopologicalSpace X] {m : CommModel}
    (hm : m ≠ .broadcast) {f : List I → X} (hf : FrequencyBasedFrom 2 f) :
    Computable m staticSC (fun _ => True) f := by
  refine ⟨viewAlg (ddOf m) (bOf m) (outFreq2 f), viewAlg_allowed hm _, ?_⟩
  intro n hn N hsc hN x _ i
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [decode_eventually hm hn N hsc hN x (outFreq2 f), eventually_ge_atTop 1]
    with t ht ht1
  obtain ⟨hrun, u, hu, hu0, he⟩ := ht i
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [viewAlg_out, hrun, hu, outFreq2, inCard_stOf, input_stOf]
  have h1 := N.card_inN_eq_one_iff hsc i
  rw [Fintype.card_fin] at h1
  by_cases hn1 : n = 1
  · subst hn1
    rw [ite_eq_left (h1.2 rfl)]
    congr 1
    apply List.ext_get (by simp)
    intro k hk _
    simp only [List.length_singleton] at hk
    simp [Fin.fin_one_eq_zero i]
  · rw [ite_eq_right (c := _) (fun h => hn1 (h1.1 h))]
    have huu : u + u ≠ 0 := by simpa using hu0
    have he2 : n • (u + u) = Multiset.card (u + u) • (List.ofFn x : Multiset I) := by
      rw [nsmul_add, he, Multiset.card_add, add_nsmul]
    refine hf _ _ (by simpa using huu) (List.ne_nil_of_length_pos (by simpa using hn)) ?_
      (by simp; omega) (freq_toList_eq List.length_ofFn hn huu he2)
    simp only [Multiset.length_toList, Multiset.card_add]
    have := Multiset.card_pos.2 hu0
    omega

/-- Values of the views in a state at time `t + 2` (the inputs of the in-neighbours). -/
noncomputable def nbrValues : (Σ t, St I t) → List I
  | ⟨t + 2, s⟩ => (s.2.map (Msg.val (t + 1))).toList
  | _ => []

/-- `K₂` test at time `t + 2`: indegree `2` and all in-neighbours of indegree `2`. -/
def isK2 : (Σ t, St I t) → Prop
  | ⟨t + 2, s⟩ => Multiset.card s.2 = 2 ∧ ∀ c ∈ s.2, Multiset.card (Msg.kids t c) = 2
  | _ => False

/-- Output map for symmetric communications: `n = 1` and `n = 2` are detected. -/
noncomputable def outFreq3 (f : List I → X) (q : Σ t, St I t) (o : Option (Multiset I)) : X :=
  if inCard q = 1 then f [St.input q.1 q.2] else
    if isK2 q then f (nbrValues q) else
    match o with
    | some u => f (u + u + u).toList
    | none => f [St.input q.1 q.2]

/-- The corrected class for symmetric communications is computable: symmetric functions that are
frequency-based on vectors of length `≥ 3`. -/
theorem computable_of_frequencyBasedFrom_three_symmetric [DecidableEq I] [TopologicalSpace X]
    {f : List I → X} (hf : FrequencyBasedFrom 3 f) (hms : MultisetBased f) :
    Computable .symmetric staticSC (fun _ => True) f := by
  have hm : CommModel.symmetric ≠ .broadcast := by decide
  refine ⟨viewAlg (ddOf .symmetric) (bOf .symmetric) (outFreq3 f), viewAlg_allowed hm _, ?_⟩
  intro n hn N hsc hN x _ i
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [decode_eventually hm hn N hsc hN x (outFreq3 f), eventually_ge_atTop 2]
    with t ht ht2
  obtain ⟨hrun, u, hu, hu0, he⟩ := ht i
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
  rw [viewAlg_out, hrun, hu, outFreq3, inCard_stOf, input_stOf]
  have h1 := N.card_inN_eq_one_iff hsc i
  rw [Fintype.card_fin] at h1
  have hK2 : isK2 ⟨t + 2, stOf N x (ddOf .symmetric) (t + 2) i⟩ ↔ n = 2 := by
    rw [← pair_iff hsc hN i]
    simp only [isK2, stOf, Multiset.card_map, Finset.card_val, Multiset.mem_map, Finset.mem_val,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, kids_msg]
  by_cases hn1 : n = 1
  · subst hn1
    rw [ite_eq_left (h1.2 rfl)]
    congr 1
    apply List.ext_get (by simp)
    intro k hk _
    simp only [List.length_singleton] at hk
    simp [Fin.fin_one_eq_zero i]
  rw [ite_eq_right (c := _) (fun h => hn1 (h1.1 h))]
  by_cases hn2 : n = 2
  · rw [ite_eq_left (hK2.2 hn2)]
    apply hms
    -- the in-neighbours of `i` are all the agents
    have hall : N.inN i = univ := by
      subst hn2
      apply Finset.eq_univ_of_forall
      intro j
      by_cases hji : j = i
      · subst hji; exact N.self_mem_inN _
      · obtain ⟨j', hj', hj'i⟩ := N.exists_mem_inN_ne hsc hji
        have : j' = j := by omega
        exact this ▸ hj'
    rw [← Multiset.coe_eq_coe]
    simp only [nbrValues, stOf, Multiset.coe_toList, Multiset.map_map, hall]
    rw [← Fin.univ_val_map]
    congr 1
  rw [ite_eq_right (c := _) (fun h => hn2 (hK2.1 h))]
  have huu : u + u + u ≠ 0 := by simpa using hu0
  have he3 : n • (u + u + u) = Multiset.card (u + u + u) • (List.ofFn x : Multiset I) := by
    rw [nsmul_add, nsmul_add, he, Multiset.card_add, Multiset.card_add, add_nsmul, add_nsmul]
  have hn3 : 3 ≤ n := by omega
  refine hf _ _ (by simpa using huu) (List.ne_nil_of_length_pos (by simpa using hn)) ?_
    (by simp; omega) (freq_toList_eq List.length_ofFn hn huu he3)
  simp only [Multiset.length_toList, Multiset.card_add]
  have := Multiset.card_pos.2 hu0
  omega

/-! ### Corollaries 4.3 and 4.4, (i) ⇒ (ii) -/

/-- Output map when the size `k` is known. -/
noncomputable def outSize (k : ℕ) (f : List I → X) (q : Σ t, St I t) : Option (Multiset I) → X
  | some u => f (recover k u).toList
  | none => f [St.input q.1 q.2]

/-- **Corollary 4.3, (i) ⇒ (ii).** Knowing the size `k`, every multiset-based function is
computable in `C^s_k`. -/
theorem computable_sizeEq_of_multisetBased [TopologicalSpace X] {m : CommModel}
    (hm : m ≠ .broadcast) {f : List I → X} (hf : MultisetBased f) (k : ℕ) :
    Computable m (sizeEq k) (fun _ => True) f := by
  refine ⟨viewAlg (ddOf m) (bOf m) (outSize k f), viewAlg_allowed hm _, ?_⟩
  rintro n hn N ⟨hsc, rfl⟩ hN x _ i
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [decode_eventually hm hn N hsc hN x (outSize n f)] with t ht
  obtain ⟨hrun, u, hu, hu0, he⟩ := ht i
  rw [viewAlg_out, hrun, hu, outSize, recover_eq hu0 he]
  apply hf
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]

/-- Output map with one leader: `n = |u| / #(leader entries of u)`. -/
noncomputable def outLeader (f : List I → X) (q : Σ t, St (I × Bool) t) :
    Option (Multiset (I × Bool)) → X
  | some u => f ((recover (Multiset.card u / Multiset.card (u.filter fun p => p.2)) u).map
      Prod.fst).toList
  | none => f [(St.input q.1 q.2).1]

/-- **Corollary 4.4, (i) ⇒ (ii).** With one leader, every multiset-based function is computable in
the class of static strongly connected networks. -/
theorem computable_leader_of_multisetBased [TopologicalSpace X] {m : CommModel}
    (hm : m ≠ .broadcast) {f : List I → X} (hf : MultisetBased f) :
    Computable m staticSC OneLeader (fun l => f (l.map Prod.fst)) := by
  refine ⟨viewAlg (ddOf m) (bOf m) (outLeader f), viewAlg_allowed hm _, ?_⟩
  intro n hn N hsc hN x hx i
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [decode_eventually hm hn N hsc hN x (outLeader f)] with t ht
  obtain ⟨hrun, u, hu, hu0, he⟩ := ht i
  rw [viewAlg_out, hrun, hu, outLeader]
  -- the number of agents is recovered from the leader's frequency
  have hL : Multiset.card ((List.ofFn x : Multiset (I × Bool)).filter fun p => p.2) = 1 := by
    rw [Multiset.filter_coe, Multiset.coe_card, ← List.countP_eq_length_filter]; exact hx
  have hf' := congrArg (fun M => Multiset.card (M.filter fun p : I × Bool => p.2)) he
  simp only [Multiset.filter_nsmul, Multiset.card_nsmul, hL, mul_one] at hf'
  have hcu : 0 < Multiset.card u := Multiset.card_pos.2 hu0
  have hlu : 0 < Multiset.card (u.filter fun p => p.2) := by
    rcases Nat.eq_zero_or_pos (Multiset.card (u.filter fun p => p.2)) with h | h
    · rw [h, mul_zero] at hf'; omega
    · exact h
  have hnval : Multiset.card u / Multiset.card (u.filter fun p => p.2) = n := by
    rw [← hf', Nat.mul_div_cancel _ hlu]
  rw [hnval, recover_eq hu0 he]
  apply hf
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, Multiset.map_coe]

end Podc.KnowYourAudience
