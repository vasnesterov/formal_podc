import Papers.PODC2020.AsyncApproxBCDirected.Operational.BWAlg

/-!
# Basic facts about the operational Algorithm BW

* Stability under extension of the history (`xv_prefix`, `mcK_prefix`, `recvM_mono`,
  `CRop_mono`, `compSeq_prefix`, ...): what was decided at a prefix stays decided.
* `mem_allSends`, `val_sent`, `comp_sent`: what a node sends.
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

namespace BWOp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (f N : ℕ)

theorem take_of_prefix {h h' : Hist V} (hh : h <+: h') {j : ℕ} (hj : j ≤ h.length) :
    h'.take j = h.take j := by
  obtain ⟨l, rfl⟩ := hh; exact List.take_append_of_le_length hj

theorem firstIdx_prefix {P Q : ℕ → Prop} {n n' k : ℕ} (hPQ : ∀ j ≤ n, P j ↔ Q j)
    (h : firstIdx P n = some k) (hn : n ≤ n') : firstIdx Q n' = some k := by
  obtain ⟨h1, h2, h3⟩ := firstIdx_eq_some.mp h
  exact firstIdx_eq_some.mpr ⟨h1.trans hn, (hPQ k h1).mp h2,
    fun j hj hq => h3 j hj ((hPQ j (by omega)).mpr hq)⟩

section Stable

variable (v : V) (r : ℕ) (own : Hist V → Option ℝ)

theorem mcK_prefix {h h' : Hist V} (hh : h <+: h') {F' : Finset V} {k : ℕ}
    (hk : mcK G v r own h F' = some k) : mcK G v r own h' F' = some k :=
  firstIdx_prefix (fun j hj => by rw [take_of_prefix hh hj]) hk hh.length_le

theorem mcK_prefix_le {h h' : Hist V} (hh : h <+: h') {F' : Finset V} {k : ℕ}
    (hk : mcK G v r own h' F' = some k) (hkh : k ≤ h.length) : mcK G v r own h F' = some k := by
  obtain ⟨h1, h2, h3⟩ := firstIdx_eq_some.mp hk
  refine firstIdx_eq_some.mpr ⟨hkh, ?_, fun j hj hq => h3 j hj ?_⟩
  · rwa [← take_of_prefix hh hkh]
  · rwa [take_of_prefix hh (by omega)]

theorem mcContent_prefix {h h' : Hist V} (hh : h <+: h') {F' : Finset V}
    (hs : (mcK G v r own h F').isSome) : mcContent G v r own h' F' = mcContent G v r own h F' := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  have hk' := mcK_prefix G v r own hh hk
  have hkl : k ≤ h.length := (firstIdx_eq_some.mp hk).1
  simp only [mcContent, hk, hk', take_of_prefix hh hkl]

theorem faK_prefix {h h' : Hist V} (hh : h <+: h') {k : ℕ}
    (hk : faK G f v r own h = some k) : faK G f v r own h' = some k :=
  firstIdx_prefix (fun j hj => by rw [take_of_prefix hh hj]) hk hh.length_le

end Stable

theorem xv_prefix (v : V) (x : ℝ) (r : ℕ) {h h' : Hist V} (hh : h <+: h') {y : ℝ}
    (hy : xv G f N v x r h = some y) : xv G f N v x r h' = some y := by
  cases r with
  | zero => simpa [xv] using hy
  | succ r =>
    simp only [xv] at hy ⊢
    split_ifs at hy ⊢ with hr
    · rcases hk : faK G f v r (xv G f N v x r) h with _ | k
      · simp [hk] at hy
      · have hk' := faK_prefix G f v r _ hh hk
        have hkl : k ≤ h.length := (firstIdx_eq_some.mp hk).1
        simp only [hk, hk'] at hy ⊢
        rw [take_of_prefix hh hkl]; exact hy

theorem ownSet_mono {v : V} {a b : Option ℝ} (h : ∀ y, a = some y → b = some y) :
    ownSet v a ⊆ ownSet v b := by
  cases a with
  | none => simp [ownSet]
  | some y => rw [h y rfl]

theorem recvM_mono (v : V) (x : ℝ) (r : ℕ) {h h' : Hist V} (hh : h <+: h') :
    recvM v r (xv G f N v x r h) h ⊆ recvM v r (xv G f N v x r h') h' := by
  classical
  intro m hm
  simp only [recvM, mem_union, List.mem_toFinset] at hm ⊢
  rcases hm with hm | hm
  · left; obtain ⟨l, rfl⟩ := hh; simp only [List.filterMap_append, List.mem_append]; left; exact hm
  · right; exact ownSet_mono (fun y hy => xv_prefix G f N v x r hh hy) hm

theorem compSeq_prefix (v : V) (r : ℕ) (own : Hist V → Option ℝ) {h h' : Hist V}
    (hh : h <+: h') : compSeq G f v r own h <+: compSeq G f v r own h' := by
  classical
  obtain ⟨l, rfl⟩ := hh
  have e : List.range ((h ++ l).length + 1) =
      List.range (h.length + 1) ++ (List.range l.length).map (fun i => h.length + 1 + i) := by
    rw [show (h ++ l).length + 1 = (h.length + 1) + l.length by simp; omega, List.range_add]
  have hcongr : ∀ k ∈ List.range (h.length + 1),
      (threadL f v).filter (fun F' => mcK G v r own (h ++ l) F' = some k) =
      (threadL f v).filter (fun F' => mcK G v r own h F' = some k) := by
    intro k hk
    rw [List.mem_range] at hk
    apply List.filter_congr
    intro F' _
    simp only [decide_eq_decide]
    constructor
    · intro h1; exact mcK_prefix_le G v r own (List.prefix_append h l) h1 (by omega)
    · intro h1; exact mcK_prefix G v r own (List.prefix_append h l) h1
  unfold compSeq
  rw [e, List.flatMap_append, List.flatMap_congr hcongr]
  exact List.prefix_append _ _

theorem mem_compSeq {v : V} {r : ℕ} {own : Hist V → Option ℝ} {h : Hist V} {F' : Finset V} :
    F' ∈ compSeq G f v r own h ↔ F' ∈ threadL f v ∧ (mcK G v r own h F').isSome := by
  classical
  simp only [compSeq, List.mem_flatMap, List.mem_range, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨k, -, h1, h2⟩; exact ⟨h1, by simp [h2]⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h2
    exact ⟨k, by have := (firstIdx_eq_some.mp hk).1; omega, h1, hk⟩

theorem counter_prefix (v : V) (r : ℕ) (own : Hist V → Option ℝ) {h h' : Hist V}
    (hh : h <+: h') {F' : Finset V} (hF : F' ∈ compSeq G f v r own h) :
    counter G f v r own h' F' = counter G f v r own h F' := by
  classical
  obtain ⟨l, hl⟩ := compSeq_prefix G f v r own hh
  simp only [counter, ← hl, List.idxOf_append_of_mem hF]

theorem fifoCR_mono (v : V) (r : ℕ) {h h' : Hist V} (hh : h <+: h') :
    fifoCR v r h ⊆ fifoCR v r h' := by
  classical
  obtain ⟨l, rfl⟩ := hh
  intro e he
  simp only [fifoCR, mem_image, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
    List.filterMap_append, List.mem_append] at he ⊢
  obtain ⟨e₀, ⟨h1, h2⟩, rfl⟩ := he
  refine ⟨e₀, ⟨Or.inl h1, fun j hj => ?_⟩, rfl⟩
  obtain ⟨e', he', h3⟩ := h2 j hj
  exact ⟨e', Or.inl he', h3⟩

theorem ownCR_mono (v : V) (x : ℝ) (r : ℕ) {h h' : Hist V} (hh : h <+: h') :
    ownCR G f v r (xv G f N v x r) h ⊆ ownCR G f v r (xv G f N v x r) h' := by
  classical
  intro e he
  simp only [ownCR, mem_image, List.mem_toFinset, List.mem_filter] at he ⊢
  obtain ⟨F', ⟨h1, h2⟩, rfl⟩ := he
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h2
  refine ⟨F', ⟨h1, by simp [mcK_prefix G v r _ hh hk]⟩, ?_⟩
  rw [mcContent_prefix G v r _ hh h2]

theorem CRop_mono (v : V) (x : ℝ) (r : ℕ) {h h' : Hist V} (hh : h <+: h') :
    CRop G f v r (xv G f N v x r) h ⊆ CRop G f v r (xv G f N v x r) h' := by
  classical
  intro e he
  simp only [CRop, mem_union] at he ⊢
  rcases he with he | he
  · exact Or.inl (fifoCR_mono v r hh he)
  · exact Or.inr (ownCR_mono G f N v x r hh he)

/-! ## What a correct node sends -/

theorem mem_allSends {S : HistSpec V (BMsg V)} {v : V} {x : ℝ} {h : Hist V} {o : V × BMsg V} :
    o ∈ S.allSends v x h ↔ ∃ k ≤ h.length, o ∈ S.react v x (h.take k) := by
  simp only [HistSpec.allSends, List.mem_flatten, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨l, ⟨k, hk, rfl⟩, ho⟩; exact ⟨k, by omega, ho⟩
  · rintro ⟨k, hk, ho⟩; exact ⟨_, ⟨k, by omega, rfl⟩, ho⟩

variable [DecidableRel G.Adj]

theorem mem_outL {v w : V} : w ∈ outL G v ↔ G.Adj v w ∧ v ≠ w := by
  simp [outL]

/-- A `val` message sent by `v` is either the relay of the first message received on its path or
the flood of `v`'s own value. -/
theorem val_sent {v : V} {x : ℝ} {h : Hist V} {w : V} {r : ℕ} {y : ℝ} {p : List V}
    (hs : (w, BMsg.val r y p) ∈ (spec G f N).react v x h) :
    w ∈ outL G v ∧ r < N ∧
    ((∃ h₀ u p₀, h = h₀ ++ [(u, .val r y p₀)] ∧ p₀.getLast? = some u ∧ p = p₀ ++ [v] ∧
        IsRedundant G (p ++ [w]) ∧ ∀ e' ∈ h₀, ∀ m ∈ valOf v r e', m.2 ≠ p₀ ++ [v]) ∨
      (p = [v] ∧ xv G f N v x r h = some y)) := by
  classical
  simp only [spec, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · -- relay
    simp only [relay] at hs
    rcases hl : h.getLast? with _ | ⟨u, m⟩
    · simp [hl] at hs
    obtain ⟨h₀, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    cases m with
    | val r' y' p' =>
      simp only [hl] at hs
      split_ifs at hs with hc
      · simp only [List.mem_filterMap] at hs
        obtain ⟨w', hw', hw⟩ := hs
        split_ifs at hw with hred
        simp only [Option.some.injEq, Prod.mk.injEq, BMsg.val.injEq] at hw
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hw
        refine ⟨hw', hc.1, Or.inl ⟨h₀, u, p', rfl, hc.2.1, rfl, by simpa using hred, ?_⟩⟩
        simpa using hc.2.2
      · simp at hs
    | comp r' c Mc F' k p' =>
      simp only [hl] at hs
      split_ifs at hs
      · simp only [List.mem_filterMap] at hs
        obtain ⟨w', -, hw⟩ := hs
        split_ifs at hw
        simp at hw
      · simp at hs
  · -- own value
    simp only [newVals, List.mem_flatMap, List.mem_range] at hs
    obtain ⟨r', hr', hs⟩ := hs
    rcases hx : xv G f N v x r' h with _ | y'
    · simp [hx] at hs
    simp only [hx] at hs
    split_ifs at hs
    · simp only [List.mem_map, Prod.mk.injEq, BMsg.val.injEq] at hs
      obtain ⟨w', hw', rfl, rfl, rfl, rfl⟩ := hs
      exact ⟨hw', hr', Or.inr ⟨rfl, hx⟩⟩
    · simp at hs
  · -- not a `val`
    simp only [newComps, List.mem_flatMap, List.mem_range] at hs
    obtain ⟨r', -, F', -, hs⟩ := hs
    split_ifs at hs
    · simp at hs
    · simp at hs

/-- A `comp` message sent by `v` is either the relay of a received one or `v`'s own
`COMPLETE`. -/
theorem comp_sent {v : V} {x : ℝ} {h : Hist V} {w : V} {r : ℕ} {c : V} {Mc : Finset (Msg V)}
    {F' : Finset V} {k : ℕ} {p : List V}
    (hs : (w, BMsg.comp r c Mc F' k p) ∈ (spec G f N).react v x h) :
    w ∈ outL G v ∧ r < N ∧
    ((∃ h₀ u p₀, h = h₀ ++ [(u, .comp r c Mc F' k p₀)] ∧ p₀.getLast? = some u ∧
        p = p₀ ++ [v] ∧ (p ++ [w]).Nodup) ∨
      (c = v ∧ p = [v] ∧ F' ∈ threadL f v ∧
        mcK G v r (xv G f N v x r) h F' = some h.length ∧
        Mc = mcContent G v r (xv G f N v x r) h F' ∧
        k = counter G f v r (xv G f N v x r) h F')) := by
  classical
  simp only [spec, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · simp only [relay] at hs
    rcases hl : h.getLast? with _ | ⟨u, m⟩
    · simp [hl] at hs
    obtain ⟨h₀, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    cases m with
    | val r' y' p' =>
      simp only [hl] at hs
      split_ifs at hs
      · simp only [List.mem_filterMap] at hs
        obtain ⟨w', -, hw⟩ := hs
        split_ifs at hw
        simp at hw
      · simp at hs
    | comp r' c' Mc' F'' k' p' =>
      simp only [hl] at hs
      split_ifs at hs with hc
      · simp only [List.mem_filterMap] at hs
        obtain ⟨w', hw', hw⟩ := hs
        split_ifs at hw with hnd
        simp only [Option.some.injEq, Prod.mk.injEq, BMsg.comp.injEq] at hw
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hw
        exact ⟨hw', hc.1, Or.inl ⟨h₀, u, p', rfl, hc.2.1, rfl, by simpa using hnd⟩⟩
      · simp at hs
  · simp only [newVals, List.mem_flatMap, List.mem_range] at hs
    obtain ⟨r', -, hs⟩ := hs
    split at hs
    · split_ifs at hs
      · simp at hs
      · simp at hs
    · simp at hs
  · simp only [newComps, List.mem_flatMap, List.mem_range] at hs
    obtain ⟨r', hr', F'', hF'', hs⟩ := hs
    split_ifs at hs with hmc
    · simp only [List.mem_map, Prod.mk.injEq, BMsg.comp.injEq] at hs
      obtain ⟨w', hw', rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hs
      exact ⟨hw', hr', Or.inr ⟨rfl, rfl, hF'', hmc, rfl, rfl⟩⟩
    · simp at hs

/-! ## Converse: what a correct node does send -/

theorem react_relay_val {v : V} {x : ℝ} {A : Hist V} {u : V} {r : ℕ} {y : ℝ} {p₀ : List V}
    (hr : r < N) (hp₀ : p₀.getLast? = some u)
    (hfirst : ∀ e' ∈ A, ∀ m ∈ valOf v r e', m.2 ≠ p₀ ++ [v]) {w : V} (hw : w ∈ outL G v)
    (hred : IsRedundant G (p₀ ++ [v, w])) :
    (w, BMsg.val r y (p₀ ++ [v])) ∈ (spec G f N).react v x (A ++ [(u, .val r y p₀)]) := by
  classical
  simp only [spec, List.mem_append]
  left; left
  simp only [relay, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.dropLast_concat]
  rw [ite_eq_left ⟨hr, hp₀, hfirst⟩]
  simp only [List.mem_filterMap]
  exact ⟨w, hw, by rw [ite_eq_left hred]⟩

theorem react_relay_comp {v : V} {x : ℝ} {A : Hist V} {u : V} {r : ℕ} {c : V}
    {Mc : Finset (Msg V)} {F' : Finset V} {k : ℕ} {p₀ : List V}
    (hr : r < N) (hp₀ : p₀.getLast? = some u) (hnd : (p₀ ++ [v]).Nodup) {w : V}
    (hw : w ∈ outL G v) (hnd' : (p₀ ++ [v, w]).Nodup) :
    (w, BMsg.comp r c Mc F' k (p₀ ++ [v])) ∈
      (spec G f N).react v x (A ++ [(u, .comp r c Mc F' k p₀)]) := by
  classical
  simp only [spec, List.mem_append]
  left; left
  simp only [relay, List.getLast?_append, List.getLast?_singleton, Option.some_or]
  rw [ite_eq_left ⟨hr, hp₀, hnd⟩]
  simp only [List.mem_filterMap]
  exact ⟨w, hw, by rw [ite_eq_left hnd']⟩

theorem react_newVal {v : V} {x : ℝ} {h : Hist V} {r : ℕ} {y : ℝ} (hr : r < N)
    (hy : xv G f N v x r h = some y) (hnew : h = [] ∨ xv G f N v x r h.dropLast = none) {w : V}
    (hw : w ∈ outL G v) : (w, BMsg.val r y [v]) ∈ (spec G f N).react v x h := by
  classical
  simp only [spec, List.mem_append]
  left; right
  simp only [newVals, List.mem_flatMap, List.mem_range]
  refine ⟨r, hr, ?_⟩
  rw [hy]
  simp only
  rw [ite_eq_left hnew]
  exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem react_newComp {v : V} {x : ℝ} {h : Hist V} {r : ℕ} {F' : Finset V} (hr : r < N)
    (hF : F' ∈ threadL f v) (hmc : mcK G v r (xv G f N v x r) h F' = some h.length) {w : V}
    (hw : w ∈ outL G v) :
    (w, BMsg.comp r v (mcContent G v r (xv G f N v x r) h F') F'
      (counter G f v r (xv G f N v x r) h F') [v]) ∈ (spec G f N).react v x h := by
  classical
  simp only [spec, List.mem_append]
  right
  simp only [newComps, List.mem_flatMap, List.mem_range]
  refine ⟨r, hr, F', hF, ?_⟩
  rw [ite_eq_left hmc]
  exact List.mem_map.mpr ⟨w, hw, rfl⟩

end BWOp

end AsyncApproxBCDirected
