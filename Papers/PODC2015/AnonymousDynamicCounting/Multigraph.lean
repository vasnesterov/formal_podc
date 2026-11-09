import Papers.PODC2015.AnonymousDynamicCounting.Kernel

/-!
# Dynamic bipartite labelled `k`-multigraphs `M(DBL_k)` (Section 4.1) and the lower bound (4.2)

Di Luna, Baldoni, *Investigating the Cost of Anonymity on Dynamic Networks* (PODC 2015 brief
announcement; full version arXiv:1505.03509v1).

**Model.** Synchronous rounds `0, 1, 2, …`. A leader `v_l` and a finite set `W` of anonymous
nodes. In round `r` the adversary joins every `w ∈ W` to the leader by between `1` and `k` edges
with pairwise different labels in `{1, …, k}`; since parallel edges carry different labels, this is
just a nonempty label set `L r w ⊆ Fin k` (`DBL`). Every process broadcasts one message per round
(unbounded size) on all its edges and receives, with each message, the label of the edge it came
over. A deterministic algorithm (`DAlgo`) consists of an initial state of the leader, a common
initial state of all other nodes, a message function, a transition function from the state and the
multiset of received `(label, message)` pairs, and the leader's output. The leader *counts* if its
first output is `|W|` (Definition 2: it outputs `|W|` and terminates).

**Leader's knowledge.** `hist M w t` is the node state `S(w, t)` of Definition 6 (the list of label
sets of rounds `0, …, t-1`) and `view M t` is the multiset `C(v_l, t)` of Definition 7 (the pairs
`(j, S(w, t))` with `j ∈ L t w`). `leader_eq_of_view_eq`: if two multigraphs give the same views
in rounds `< t`, every algorithm has the same leader state after `t` rounds; `fullInfo` is an
algorithm whose leader state is exactly `S(v_l, t) = [C(v_l, 0), …, C(v_l, t-1)]`.

**Results.**
* `lemma_5`: for `3^t ≤ 2n + 1` there are `M, M' ∈ M(DBL₂)` (`⊆ M(DBL_k)`, `k ≥ 2`) with `n` and
  `n + 1` nodes that no algorithm distinguishes during the first `t` rounds.
* `lemma_5_sharp`: if `3^t > 2n + 1`, *any* two multigraphs of `M(DBL₂)` of sizes `n` and `n + 1`
  give different leader states `S(v_l, t)` — Lemma 5 is tight, and its printed bound
  `r ≤ ⌊log₃(2n+1)⌋` is off by one in the paper's own round indexing (`lemma_5_paper_indexing_false`).
* `theorem_1`: every counting algorithm for `M(DBL_k)` (`k ≥ 2`) whose leader outputs by round
  `f |W|` has `2|W| + 1 < 3^(f |W|)`, i.e. `f |W| > log₃(2|W| + 1)`.
-/

namespace Podc.AnonymousDynamicCounting

/-- A dynamic bipartite labelled `k`-multigraph `M ∈ M(DBL_k)`: in round `r` node `w ∈ W` is
joined to the leader by edges with the (nonempty) set of labels `L r w`. -/
structure DBL (k : ℕ) where
  /-- The non-leader nodes. -/
  W : Type
  [fintype : Fintype W]
  /-- The labels of the edges between `w` and the leader in round `r`. -/
  L : ℕ → W → Finset (Fin k)
  nonempty : ∀ r w, (L r w).Nonempty

attribute [instance] DBL.fintype

/-- `|W|`, the quantity the leader has to count. -/
def DBL.size {k : ℕ} (M : DBL k) : ℕ := Fintype.card M.W

/-- A deterministic algorithm for `M(DBL_k)`: all non-leader nodes run the same code from the same
initial state; the leader starts from its own state. Messages arrive with the label of their edge. -/
structure DAlgo (k : ℕ) (S Msg : Type*) where
  leaderInit : S
  init : S
  send : S → Msg
  step : S → Multiset (Fin k × Msg) → S
  /-- The leader's output (`none` = no output yet). -/
  output : S → Option ℕ

variable {k : ℕ} {S Msg : Type*}

theorem Multiset.map_finsetSum {ι α β : Type*} (s : Finset ι) (f : α → β) (g : ι → Multiset α) :
    Multiset.map f (∑ i ∈ s, g i) = ∑ i ∈ s, Multiset.map f (g i) :=
  map_sum (Multiset.mapAddMonoidHom f) g s

theorem Finset.count_val {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
    Multiset.count a s.val = if a ∈ s then 1 else 0 := by
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem s.nodup h
  · exact Multiset.count_eq_zero.2 h

/-- The execution: leader state and node states after `t` rounds. -/
def DAlgo.run (A : DAlgo k S Msg) (M : DBL k) : ℕ → S × (M.W → S)
  | 0 => (A.leaderInit, fun _ => A.init)
  | t + 1 =>
    (A.step (A.run M t).1 (∑ w, (M.L t w).val.map fun j => (j, A.send ((A.run M t).2 w))),
     fun w => A.step ((A.run M t).2 w) ((M.L t w).val.map fun j => (j, A.send (A.run M t).1)))

/-- The leader state after `t` rounds. -/
def DAlgo.leader (A : DAlgo k S Msg) (M : DBL k) (t : ℕ) : S := (A.run M t).1

/-- The state `S(w, t)` of a non-leader node (Definition 6): its label sets in rounds `< t`. -/
def hist (M : DBL k) (w : M.W) (t : ℕ) : List (Finset (Fin k)) := List.ofFn fun i : Fin t => M.L i w

/-- `C(v_l, t)` (Definition 7): the multiset of pairs `(j, S(w, t))` over the edges of round `t`. -/
def view (M : DBL k) (t : ℕ) : Multiset (Fin k × List (Finset (Fin k))) :=
  ∑ w, (M.L t w).val.map fun j => (j, hist M w t)

/-- The leader state `S(v_l, t) = [C(v_l, 0), …, C(v_l, t-1)]` of Definition 7. -/
def leaderView (M : DBL k) (t : ℕ) : List (Multiset (Fin k × List (Finset (Fin k)))) :=
  List.ofFn fun i : Fin t => view M i

theorem leaderView_eq_iff (M M' : DBL k) (t : ℕ) :
    leaderView M t = leaderView M' t ↔ ∀ i < t, view M i = view M' i := by
  simp only [leaderView, List.ofFn_inj, funext_iff]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

/-! ### Every algorithm factors through the views -/

namespace DAlgo

variable (A : DAlgo k S Msg)

/-- The state of a node with label sets `Lw` when the leader's states are `ls`. -/
def nodeSt (ls : ℕ → S) (Lw : ℕ → Finset (Fin k)) : ℕ → S
  | 0 => A.init
  | i + 1 => A.step (nodeSt ls Lw i) ((Lw i).val.map fun j => (j, A.send (ls i)))

theorem nodeSt_congr {ls ls' : ℕ → S} {Lw Lw' : ℕ → Finset (Fin k)} {t : ℕ}
    (hl : ∀ i < t, ls i = ls' i) (hL : ∀ i < t, Lw i = Lw' i) :
    A.nodeSt ls Lw t = A.nodeSt ls' Lw' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [nodeSt]
    rw [ih (fun i hi => hl i (by omega)) (fun i hi => hL i (by omega)), hl t (by omega),
      hL t (by omega)]

theorem run_snd (M : DBL k) (t : ℕ) (w : M.W) :
    (A.run M t).2 w = A.nodeSt (A.leader M) (fun i => M.L i w) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [run, nodeSt, ih, leader]

/-- Decode a history list into a label-set sequence. -/
def decode (h : List (Finset (Fin k))) (i : ℕ) : Finset (Fin k) := h.getD i ∅

theorem decode_hist (M : DBL k) (w : M.W) {t i : ℕ} (hi : i < t) :
    decode (hist M w t) i = M.L i w := by
  simp [decode, hist, hi]

theorem leader_succ (M : DBL k) (t : ℕ) :
    A.leader M (t + 1) = A.step (A.leader M t)
      ((view M t).map fun p => (p.1, A.send (A.nodeSt (A.leader M) (decode p.2) t))) := by
  simp only [leader, run, view]
  congr 1
  rw [Multiset.map_finsetSum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Multiset.map_map, Function.comp_def, run_snd]
  rw [A.nodeSt_congr (ls' := A.leader M) (Lw' := decode (hist M w t)) (fun _ _ => rfl)
    fun i hi => (decode_hist M w hi).symm]

/-- The leader's state depends only on the views `C(v_l, i)`, `i < t` (the "full information"
remark after Definition 7). -/
theorem leader_eq_of_view_eq {M M' : DBL k} {t : ℕ} (h : ∀ i < t, view M i = view M' i) :
    ∀ s ≤ t, A.leader M s = A.leader M' s := by
  intro s hs
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    cases s with
    | zero => rfl
    | succ s =>
      rw [leader_succ, leader_succ, ih s (by omega) (by omega), h s (by omega)]
      congr 1
      refine Multiset.map_congr rfl fun p _ => ?_
      congr 2
      exact A.nodeSt_congr (fun i hi => ih i (by omega) (by omega)) fun _ _ => rfl

end DAlgo

/-- The full-information algorithm: every node keeps its label history `S(w, t)` and the leader
keeps `S(v_l, t)`; messages are whole states. -/
def fullInfo (k : ℕ) :
    DAlgo k (List (Finset (Fin k)) × List (Multiset (Fin k × List (Finset (Fin k)))))
      (List (Finset (Fin k)) × List (Multiset (Fin k × List (Finset (Fin k))))) where
  leaderInit := ([], [])
  init := ([], [])
  send := id
  step s R := (s.1 ++ [(R.map Prod.fst).toFinset], s.2 ++ [R.map fun p => (p.1, p.2.1)])
  output _ := none

theorem fullInfo_node (M : DBL k) (t : ℕ) (w : M.W) : (((fullInfo k).run M t).2 w).1 = hist M w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have e : (((fullInfo k).run M (t + 1)).2 w).1 =
        (((fullInfo k).run M t).2 w).1 ++ [M.L t w] := by
      simp [DAlgo.run, fullInfo, Multiset.map_map]
    rw [e, ih, hist, hist, List.ofFn_succ_last]
    rfl

/-- The leader of `fullInfo` holds exactly `S(v_l, t)` (Definition 7). -/
theorem fullInfo_leader (M : DBL k) (t : ℕ) : ((fullInfo k).leader M t).2 = leaderView M t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [DAlgo.leader, DAlgo.run] at ih ⊢
    simp only [fullInfo, id, leaderView, List.ofFn_succ_last] at ih ⊢
    rw [ih]
    congr 2
    simp only [view, Multiset.map_finsetSum, Multiset.map_map, Function.comp_def]
    refine Finset.sum_congr rfl fun w _ => ?_
    have := fullInfo_node M t w
    simp only [fullInfo] at this
    simp [this]

/-! ### Counting -/

/-- The output sequence `o` is `none` before round `T` and `some m` at round `T`. -/
def FirstOutput (o : ℕ → Option ℕ) (T m : ℕ) : Prop := o T = some m ∧ ∀ s < T, o s = none

theorem FirstOutput.unique {o : ℕ → Option ℕ} {T m T' m' : ℕ} (h : FirstOutput o T m)
    (h' : FirstOutput o T' m') : T = T' ∧ m = m' := by
  rcases lt_trichotomy T T' with hlt | rfl | hlt
  · have := h'.2 T hlt; rw [h.1] at this; cases this
  · exact ⟨rfl, Option.some_injective _ (h.1.symm.trans h'.1)⟩
  · have := h.2 T' hlt; rw [h'.1] at this; cases this

theorem FirstOutput.of_agree {o o' : ℕ → Option ℕ} {T m : ℕ} (h : FirstOutput o T m)
    (hag : ∀ s ≤ T, o s = o' s) : FirstOutput o' T m :=
  ⟨(hag T le_rfl).symm.trans h.1, fun s hs => (hag s hs.le).symm.trans (h.2 s hs)⟩

/-- `A` counts on `M(DBL_k)` within time `f`: on every multigraph with `|W| = n`, the leader's first
output is `n` and it comes by round `f n` (Definition 2). -/
def DAlgo.CountsWithin (A : DAlgo k S Msg) (f : ℕ → ℕ) : Prop :=
  ∀ M : DBL k, ∃ T ≤ f M.size, FirstOutput (fun s => A.output (A.leader M s)) T M.size

/-! ### The two indistinguishable multigraphs of Lemma 5 -/

/-- A letter as a set of labels in `Fin k` (`k ≥ 2`). -/
def Lab.toFin (hk : 2 ≤ k) (x : Lab) : Finset (Fin k) := x.toFinset.map (Fin.castLEEmb hk)

theorem Lab.toFin_nonempty (hk : 2 ≤ k) (x : Lab) : (x.toFin hk).Nonempty := by
  simpa [Lab.toFin] using x.toFinset_nonempty

/-- The multigraph whose nodes follow the words `w` of length `t` with `kvec w = σ` (one node per
word), plus `m` extra nodes with label set `{1,2}` in every round. With `σ = -1` and `σ = 1` these
are the configurations `s_r` and `s_r + k_r` of the proof of Lemma 5. -/
def kGraph (hk : 2 ≤ k) (t : ℕ) (σ : ℤ) (m : ℕ) : DBL k where
  W := ((words t).filter (kvec · = σ)) ⊕ Fin m
  L r v := match v with
    | Sum.inl w => (w.1.getD r Lab.both).toFin hk
    | Sum.inr _ => Lab.both.toFin hk
  nonempty r v := by cases v <;> exact Lab.toFin_nonempty _ _

theorem kGraph_size (hk : 2 ≤ k) (t : ℕ) (σ : ℤ) (m : ℕ) :
    (kGraph hk t σ m).size = ((words t).filter (kvec · = σ)).card + m := by
  rw [DBL.size, Fintype.card_eq_nat_card]
  show Nat.card (_ ⊕ _) = _
  rw [Nat.card_sum, Nat.card_eq_finsetCard]
  simp

/-- The count of an element in a multiset of the shape of `view`. -/
theorem count_sum_map {ι α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset ι)
    (F : ι → Finset α) (g : ι → β) (a : α × β) :
    Multiset.count a (∑ i ∈ s, (F i).val.map fun j => (j, g i)) =
      (s.filter fun i => a.1 ∈ F i ∧ a.2 = g i).card := by
  rw [Multiset.count_sum', Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨a1, a2⟩ := a
  by_cases h2 : a2 = g i
  · subst h2
    rw [Multiset.count_map_eq_count' (fun j => (j, g i)) _ (fun x y h => (Prod.ext_iff.1 h).1),
      Finset.count_val]
    simp
  · rw [Multiset.count_eq_zero.2]
    · simp [h2]
    · simp only [Multiset.mem_map, not_exists, not_and]
      intro j _ h; exact h2 (Prod.ext_iff.1 h).2.symm


/-- Rows of `M_r` see as many `+1` as `-1` entries of `k_r`. -/
theorem card_rowMem_pos_eq_neg (t : ℕ) (j : Fin 2) (p : List Lab) :
    ((words t).filter fun w => kvec w = 1 ∧ RowMem j p w).card =
      ((words t).filter fun w => kvec w = -1 ∧ RowMem j p w).card := by
  have h0 : rowSum t (fun w => (1 : ℤ) * (kvec w : ℤ)) j p = 0 := rowSum_smul_kvec t 1 j p
  simp only [rowSum, one_mul] at h0
  have h : ∀ w, kvec w = (if kvec w = 1 then 1 else 0) - (if kvec w = -1 then 1 else 0) := by
    intro w; rcases kvec_eq_one_or w with h | h <;> simp [h]
  rw [Finset.sum_congr rfl (fun w _ => h w), Finset.sum_sub_distrib] at h0
  simp only [Finset.sum_boole, Finset.filter_filter] at h0
  have := sub_eq_zero.1 h0
  simp only [Nat.cast_inj] at this
  have e : ∀ σ : ℤ, ((words t).filter fun w => kvec w = σ ∧ RowMem j p w) =
      (words t).filter fun w => RowMem j p w ∧ kvec w = σ :=
    fun σ => Finset.filter_congr fun _ _ => and_comm
  rw [e, e]; exact this

theorem ofFn_getD_eq_map_take {α β : Type*} (f : α → β) (d : α) (w : List α) {i : ℕ}
    (hi : i ≤ w.length) : (List.ofFn fun r : Fin i => f (w.getD r d)) = (w.take i).map f := by
  apply List.ext_getElem
  · simp; omega
  · intro r h1 h2
    simp only [List.length_ofFn] at h1
    simp [List.getElem?_eq_getElem (show r < w.length by omega)]

/-- The views of the two multigraphs of Lemma 5 coincide in every round `i < t`. -/
theorem view_kGraph (hk : 2 ≤ k) {t i : ℕ} (hi : i < t) (m : ℕ) :
    view (kGraph hk t (-1) m) i = view (kGraph hk t 1 m) i := by
  simp only [view]
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  -- the nodes following the words: reduce to multisets over `Fin 2 × List Lab`
  let Φ : Fin 2 × List Lab → Fin k × List (Finset (Fin k)) :=
    fun q => (Fin.castLE hk q.1, q.2.map (Lab.toFin hk))
  have key : ∀ σ : ℤ, (∑ w : ((words t).filter (kvec · = σ)),
      ((kGraph hk t σ m).L i (Sum.inl w)).val.map
        fun j => (j, hist (kGraph hk t σ m) (Sum.inl w) i)) =
      (∑ w ∈ (words t).filter (kvec · = σ),
        (w.getD i Lab.both).toFinset.val.map fun j => (j, w.take i)).map Φ := by
    intro σ
    rw [Multiset.map_finsetSum, ← Finset.sum_coe_sort ((words t).filter (kvec · = σ))]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hw : w.1.length = t := mem_words.1 (Finset.mem_filter.1 w.2).1
    have e := ofFn_getD_eq_map_take (Lab.toFin hk) Lab.both w.1 (i := i) (by omega)
    simp only [kGraph, hist]
    rw [e]
    simp only [Lab.toFin, Finset.map_val, Multiset.map_map, Function.comp_def, Φ]
    rfl
  rw [key, key]
  congr 1
  ext ⟨j, p⟩
  rw [count_sum_map, count_sum_map, Finset.filter_filter, Finset.filter_filter]
  by_cases hp : p.length = i
  · have e : ∀ σ : ℤ, ((words t).filter fun w => kvec w = σ ∧
        j ∈ (w.getD i Lab.both).toFinset ∧ p = w.take i) =
        (words t).filter fun w => kvec w = σ ∧ RowMem j p w := by
      intro σ
      refine Finset.filter_congr fun w hw => ?_
      rw [mem_words] at hw
      rw [rowMem_iff, hp]
      simp only [List.getElem?_eq_getElem (show i < w.length by omega), Option.some.injEq,
        exists_eq_left', List.getD_eq_getElem _ _ (show i < w.length by omega)]
      tauto
    simp only at e ⊢
    rw [e, e, card_rowMem_pos_eq_neg]
  · have e : ∀ σ : ℤ, ((words t).filter fun w => kvec w = σ ∧
        j ∈ (w.getD i Lab.both).toFinset ∧ p = w.take i) = ∅ := by
      intro σ
      refine Finset.filter_false_of_mem fun w hw => ?_
      rw [mem_words] at hw
      rintro ⟨_, _, rfl⟩
      simp at hp; omega
    simp only at e ⊢
    rw [e, e]

/-- **Lemma 5** (in the round count of Definition 7: `t` rounds have been played, so the leader
knows `S(v_l, t) = [C(v_l, 0), …, C(v_l, t-1)]`). If `3^t ≤ 2n + 1`, i.e. `t ≤ ⌊log₃(2n+1)⌋`,
there are two multigraphs of `M(DBL₂) ⊆ M(DBL_k)` with `n` and `n + 1` nodes whose leader views
coincide during the first `t` rounds; hence no algorithm distinguishes them by round `t`. -/
theorem lemma_5 (hk : 2 ≤ k) {n t : ℕ} (h : 3 ^ t ≤ 2 * n + 1) :
    ∃ M M' : DBL k, M.size = n ∧ M'.size = n + 1 ∧
      (∀ r w, M.L r w ⊆ {⟨0, by omega⟩, ⟨1, by omega⟩}) ∧
      (∀ r w, M'.L r w ⊆ {⟨0, by omega⟩, ⟨1, by omega⟩}) ∧
      leaderView M t = leaderView M' t ∧
      ∀ (A : DAlgo k S Msg), ∀ s ≤ t, A.leader M s = A.leader M' s := by
  have hN := card_kvec_neg t
  have hP := card_kvec_pos t
  set N := ((words t).filter (kvec · = -1)).card
  have hNn : N ≤ n := by omega
  refine ⟨kGraph hk t (-1) (n - N), kGraph hk t 1 (n - N), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kGraph_size]; omega
  · rw [kGraph_size]; omega
  · intro r w x hx
    cases w <;> simp only [kGraph, Lab.toFin, Finset.mem_map] at hx <;>
    · obtain ⟨y, -, rfl⟩ := hx
      fin_cases y <;> simp [Fin.ext_iff]
  · intro r w x hx
    cases w <;> simp only [kGraph, Lab.toFin, Finset.mem_map] at hx <;>
    · obtain ⟨y, -, rfl⟩ := hx
      fin_cases y <;> simp [Fin.ext_iff]
  · exact (leaderView_eq_iff _ _ _).2 fun i hi => view_kGraph hk hi _
  · exact fun A => A.leader_eq_of_view_eq fun i hi => view_kGraph hk hi _

/-- **Theorem 1.** No algorithm counts on `M(DBL_k)`, `k ≥ 2`, within time `f` unless
`3^(f n) > 2n + 1` for every `n`, i.e. the leader of an `n`-node multigraph needs more than
`log₃(2n + 1)` rounds. (The paper: no algorithm solves counting at a round `r < ⌊log₃(2|W|+1)⌋ - 1`,
where round `r` is the `(r+1)`-st round, i.e. at least `⌊log₃(2|W|+1)⌋` rounds are needed; ours is
one round stronger.) -/
theorem theorem_1 (hk : 2 ≤ k) (A : DAlgo k S Msg) {f : ℕ → ℕ} (hA : A.CountsWithin f) (n : ℕ) :
    2 * n + 1 < 3 ^ f n := by
  by_contra hlt
  obtain ⟨M, M', hM, hM', -, -, -, hag⟩ := lemma_5 (S := S) (Msg := Msg) hk (not_lt.1 hlt)
  obtain ⟨T, hT, hfo⟩ := hA M
  obtain ⟨T', -, hfo'⟩ := hA M'
  rw [hM] at hT hfo
  rw [hM'] at hfo'
  have := hfo.of_agree (o' := fun s => A.output (A.leader M' s))
    fun s hs => by simp only [hag A s (hs.trans hT)]
  have := (this.unique hfo').2
  omega

/-- Theorem 1 with a logarithm: the counting time on `n`-node multigraphs exceeds `⌊log₃(2n+1)⌋`. -/
theorem theorem_1_log (hk : 2 ≤ k) (A : DAlgo k S Msg) {f : ℕ → ℕ} (hA : A.CountsWithin f)
    (n : ℕ) : Nat.log 3 (2 * n + 1) < f n :=
  Nat.log_lt_of_lt_pow (by omega) (theorem_1 hk A hA n)


/-! ### Lemma 5 is sharp (`k = 2`) -/

/-- The history of a node of an `M(DBL₂)` multigraph as a word over `Lab`. -/
def labHist (M : DBL 2) (w : M.W) (t : ℕ) : List Lab :=
  List.ofFn fun i : Fin t => Lab.ofFinset (M.L i w)

theorem labHist_mem (M : DBL 2) (w : M.W) (t : ℕ) : labHist M w t ∈ words t := by
  rw [mem_words]; simp [labHist]

/-- Number of nodes with history `u` (the component `(s_r)_u` of the paper's solution vector). -/
def cnt (M : DBL 2) (t : ℕ) (u : List Lab) : ℕ :=
  (Finset.univ.filter fun w => labHist M w t = u).card

theorem sum_cnt_filter (M : DBL 2) (t : ℕ) (P : List Lab → Prop) [DecidablePred P] :
    ∑ u ∈ (words t).filter P, cnt M t u = (Finset.univ.filter fun w => P (labHist M w t)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => labHist M w t)
    (t := (words t).filter P) (fun w hw => by
      rw [Finset.mem_coe, Finset.mem_filter] at hw ⊢
      exact ⟨labHist_mem M w t, hw.2⟩)]
  refine Finset.sum_congr rfl fun u hu => ?_
  unfold cnt
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h ▸ (Finset.mem_filter.1 hu).2, h⟩, fun h => h.2⟩

theorem take_labHist (M : DBL 2) (w : M.W) {i t : ℕ} (hi : i ≤ t) :
    (labHist M w t).take i = labHist M w i := by
  apply List.ext_getElem
  · simp [labHist]; omega
  · intro r h1 h2; simp [labHist]

theorem map_labHist (M : DBL 2) (w : M.W) (i : ℕ) :
    (labHist M w i).map Lab.toFinset = hist M w i := by
  simp [labHist, hist, Function.comp_def, Lab.toFinset_ofFinset (M.nonempty _ w)]

theorem rowMem_labHist_iff (M : DBL 2) (w : M.W) {t : ℕ} (j : Fin 2) (p : List Lab)
    (hp : p.length < t) :
    RowMem j p (labHist M w t) ↔ j ∈ M.L p.length w ∧ p.map Lab.toFinset = hist M w p.length := by
  rw [rowMem_iff, take_labHist M w hp.le]
  have hget : (labHist M w t)[p.length]? = some (Lab.ofFinset (M.L p.length w)) := by
    simp [labHist, hp]
  rw [hget]
  simp only [Option.some.injEq, exists_eq_left', Lab.toFinset_ofFinset (M.nonempty _ w)]
  rw [← map_labHist]
  have hinj : Function.Injective (List.map Lab.toFinset) :=
    List.map_injective_iff.2 fun x y h => by
      rw [← Lab.ofFinset_toFinset x, ← Lab.ofFinset_toFinset y, h]
  rw [hinj.eq_iff, eq_comm]
  tauto

theorem card_rowMem_eq_count (M : DBL 2) {t : ℕ} (j : Fin 2) (p : List Lab) (hp : p.length < t) :
    (Finset.univ.filter fun w => RowMem j p (labHist M w t)).card =
      Multiset.count (j, p.map Lab.toFinset) (view M p.length) := by
  rw [view, count_sum_map]
  congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact rowMem_labHist_iff M w j p hp

theorem not_rowMem_of_le {j : Fin 2} {p u : List Lab} (h : u.length ≤ p.length) :
    ¬ RowMem j p u := by
  rw [rowMem_iff]
  rintro ⟨-, x, hx, -⟩
  rw [List.getElem?_eq_none h] at hx
  cases hx

/-- **Lemma 5 is sharp.** If `3^t > 2n + 1`, then any two multigraphs of `M(DBL₂)` with `n` and
`n + 1` nodes give different leader states `S(v_l, t)` (and the full-information algorithm
`fullInfo` distinguishes them after `t` rounds). This is the uniqueness half of the paper's
analysis: the integer solutions of `m_r = M_r s` differ by multiples of `k_r` (Lemmas 2, 3), and
`s` and `s + k_r` are both nonnegative only if `|s| ≥ Σ⁻ k_r`. -/
theorem lemma_5_sharp (M M' : DBL 2) {t : ℕ} (hs : M'.size = M.size + 1)
    (h : 2 * M.size + 1 < 3 ^ t) : leaderView M t ≠ leaderView M' t := by
  intro hv
  rw [leaderView_eq_iff] at hv
  let d : List Lab → ℤ := fun u => (cnt M' t u : ℤ) - cnt M t u
  have hd : InKer t d := by
    intro j p
    unfold rowSum
    simp only [d, Finset.sum_sub_distrib]
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_cnt_filter, sum_cnt_filter]
    by_cases hp : p.length < t
    · rw [card_rowMem_eq_count M j p hp, card_rowMem_eq_count M' j p hp, hv _ hp, sub_self]
    · have e : ∀ N : DBL 2,
          (Finset.univ.filter fun w => RowMem j p (labHist N w t)) = ∅ := fun N =>
        Finset.filter_false_of_mem fun w _ =>
          not_rowMem_of_le (by simp [labHist]; omega)
      rw [e, e]; simp
  obtain ⟨c, hc⟩ := (inKer_iff t d).1 hd
  have hsum : ∑ u ∈ words t, d u = 1 := by
    simp only [d, Finset.sum_sub_distrib]
    have e : ∀ N : DBL 2, ∑ u ∈ words t, (cnt N t u : ℤ) = N.size := by
      intro N
      have := sum_cnt_filter N t (fun _ => True)
      simp only [Finset.filter_true] at this
      rw [← Nat.cast_sum, this]
      simp [DBL.size]
    rw [e, e, hs]; push_cast; ring
  have hc1 : c = 1 := by
    rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, ← Int.cast_sum, sum_kvec] at hsum
    simpa using hsum
  subst hc1
  -- every word with `k_r = -1` is the history of a node of `M`
  have hpos : ∀ u ∈ (words t).filter (kvec · = -1), 1 ≤ cnt M t u := by
    intro u hu
    rw [Finset.mem_filter] at hu
    have := hc u hu.1
    simp only [d, hu.2, Int.cast_neg, Int.cast_one, one_mul] at this
    omega
  have hle : ((words t).filter (kvec · = -1)).card ≤ M.size := by
    calc ((words t).filter (kvec · = -1)).card
        = ∑ u ∈ (words t).filter (kvec · = -1), 1 := by simp
      _ ≤ ∑ u ∈ (words t).filter (kvec · = -1), cnt M t u := Finset.sum_le_sum hpos
      _ ≤ ∑ u ∈ (words t).filter (fun _ => True), cnt M t u := by
          apply Finset.sum_le_sum_of_subset; intro u; simp_all
      _ = M.size := by rw [sum_cnt_filter]; simp [DBL.size]
  have := card_kvec_neg t
  omega

/-- The full-information algorithm distinguishes the two multigraphs of `lemma_5_sharp`. -/
theorem fullInfo_distinguishes (M M' : DBL 2) {t : ℕ} (hs : M'.size = M.size + 1)
    (h : 2 * M.size + 1 < 3 ^ t) : (fullInfo 2).leader M t ≠ (fullInfo 2).leader M' t := by
  intro he
  apply lemma_5_sharp M M' hs h
  rw [← fullInfo_leader, ← fullInfo_leader, he]

/-- **Lemma 5 as printed is off by one.** In the paper's own indexing (Lemma 4, the proof of
Lemma 5, and Theorem 1: "at round `r`" the leader knows `m_r = M_r s_r`, i.e. the views of rounds
`0, …, r`, which is `leaderView (r + 1)`), Lemma 5 claims indistinguishability for every
`r ≤ ⌊log₃(2n+1)⌋`. This fails for `n = 3`, `r = 1` — as the paper itself observes right after
Equation 5 ("if `n ≤ 3` it is possible to obtain the count in 2 rounds"). The proof only gives
`r ≤ ⌊log₃(2n+1)⌋ - 1`, which is what Theorem 1 uses. -/
theorem lemma_5_paper_indexing_false :
    ¬ ∀ n r : ℕ, r ≤ Nat.log 3 (2 * n + 1) →
      ∃ M M' : DBL 2, M.size = n ∧ M'.size = n + 1 ∧ leaderView M (r + 1) = leaderView M' (r + 1) := by
  intro h
  obtain ⟨M, M', hM, hM', hv⟩ := h 3 1 (by
    rw [show 2 * 3 + 1 = 7 by rfl]
    exact (Nat.le_log_iff_pow_le (by norm_num) (by norm_num)).2 (by norm_num))
  exact lemma_5_sharp M M' (by omega) (by rw [hM]; norm_num) hv

end Podc.AnonymousDynamicCounting
