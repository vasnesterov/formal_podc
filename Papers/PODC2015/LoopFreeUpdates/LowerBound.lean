import Papers.PODC2015.LoopFreeUpdates.Basic

/-!
# Figure 2: strong loop-freedom may need `n - 1` rounds, relaxed loop-freedom needs 3

§2.2 and Figure 2 of Ludwig, Marcinkowski, Schmid, *Scheduling Loop-free Network Updates: It's Good
to Relax!* (PODC 2015).

* `Instance.hasSLF_card_sub_one`: every instance whose source has to be updated admits a strongly
  loop-free schedule with `n - 1` rounds, `n = |toUpdate|` ("This is worst possible"). Nodes are
  updated one per round from the destination backwards along the new route; the source joins the
  last round. Every intermediate state is loop-free (`Instance.loopFree_of_upClosed`).
* `fig2`: the instance of Figure 2, with nodes `0, …, l - 1` (`vᵢ = i - 1`), old route
  `0, 1, …, l - 1` and new route `0, l - 2, l - 3, …, 1, l - 1`. All nodes but `d` must be
  updated (`fig2_card_toUpdate : n = l - 1`).
* `fig2_slf_lower`: every SLF schedule of `fig2 l` has at least `l - 2 = n - 1` rounds;
  `fig2_hasSLF`: `n - 1` rounds suffice; `fig2_hasRLF`: there is an RLF schedule with 3 rounds.
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

variable {V : Type*} [DecidableEq V]

namespace Instance

variable (I : Instance V)

/-! ### Cycles -/

theorem ne_s_of_step {A : Finset V} {u v : V} (h : I.Step A u v) : v ≠ I.s := by
  rintro rfl; exact I.not_step_s A u h

/-- The source never lies on a cycle (it has no incoming edge). -/
theorem not_transGen_s (A : Finset V) : ¬ TransGen (I.Step A) I.s I.s := by
  intro h
  obtain ⟨c, -, hc⟩ := TransGen.tail'_iff.1 h
  exact I.not_step_s A c hc

/-- In the (functional) forwarding graph, every node reachable from a node on a cycle lies on that
cycle. -/
theorem transGen_self_of_cycle {A : Finset V} {v x : V} (hv : TransGen (I.Step A) v v)
    (hx : ReflTransGen (I.Step A) v x) : TransGen (I.Step A) x x := by
  obtain ⟨c, hc, hcv⟩ := TransGen.head'_iff.1 hv
  have key : ∀ y, ReflTransGen (I.Step A) v y → ReflTransGen (I.Step A) y v := by
    intro y hy
    induction hy with
    | refl => exact ReflTransGen.refl
    | tail _ hyz ih =>
      rcases ih.cases_head with rfl | ⟨y', hy', hy'v⟩
      · rw [I.step_unique A hyz hc]; exact hcv
      · rw [I.step_unique A hyz hy']; exact hy'v
  exact TransGen.trans_right (key x hx) (TransGen.trans_left hv hx)

/-! ### Upward-closed states are loop-free -/

/-- A state is *upward closed* if, apart from the source, the updated nodes form an upper set (with
respect to the position on the new route) of the nodes to be updated. -/
def UpClosed (A : Finset V) : Prop :=
  ∀ u ∈ A, u ∈ I.toUpdate → u ≠ I.s →
    ∀ x ∈ I.toUpdate, x ≠ I.s → I.pos₂ u ≤ I.pos₂ x → x ∈ A

/-- In an upward-closed state, the walk from an updated node (other than `s`) follows the new
route. -/
theorem pos₂_lt_of_upClosed {A : Finset V} (hA : I.UpClosed A) {u : V} (hu : u ∈ A)
    (hut : u ∈ I.toUpdate) (hus : u ≠ I.s) {x : V} (hx : TransGen (I.Step A) u x) :
    I.pos₂ u < I.pos₂ x ∧ x ≠ I.s := by
  induction hx with
  | single h =>
    refine ⟨?_, I.ne_s_of_step h⟩
    unfold Step at h; rw [I.fwd_of_mem hu] at h
    have := (I.out₂_spec h).2.2; omega
  | @tail b c _ hbc ih =>
    refine ⟨?_, I.ne_s_of_step hbc⟩
    have hfwd : I.fwd A b = I.out₂ b := by
      by_cases hb : b ∈ I.toUpdate
      · exact I.fwd_of_mem (hA u hu hut hus b hb ih.2 ih.1.le)
      · rw [I.fwd_of_not_toUpdate A hb]; exact I.out₁_eq_out₂_of_not_mem hb
    unfold Step at hbc; rw [hfwd] at hbc
    have := (I.out₂_spec hbc).2.2; omega

/-- Upward-closed states are (strongly) loop-free: a cycle through an updated node would only use
new rules afterwards, and a cycle without updated nodes only uses old rules. -/
theorem loopFree_of_upClosed {A : Finset V} (hA : I.UpClosed A) : I.LoopFree A := by
  intro v hv
  have hold : ∀ a, ReflTransGen (I.Step A) v a → I.fwd A a = I.out₁ a := by
    intro a ha
    have ha' := I.transGen_self_of_cycle hv ha
    by_cases h : a ∈ A ∧ a ∈ I.toUpdate
    · exfalso
      have has : a ≠ I.s := by rintro rfl; exact I.not_transGen_s A ha'
      exact lt_irrefl _ (I.pos₂_lt_of_upClosed hA h.1 h.2 has ha').1
    · by_cases hA' : a ∈ A
      · exact I.fwd_of_not_toUpdate _ (fun h' => h ⟨hA', h'⟩)
      · exact I.fwd_of_not_mem hA'
  have hrank : ∀ x, TransGen (I.Step A) v x → I.pos₁ v < I.pos₁ x := by
    intro x hx
    induction hx with
    | single h =>
      unfold Step at h; rw [hold _ ReflTransGen.refl] at h
      have := (I.out₁_spec h).2.2; omega
    | tail hab hbc ih =>
      unfold Step at hbc; rw [hold _ hab.to_reflTransGen] at hbc
      have := (I.out₁_spec hbc).2.2; omega
  exact lt_irrefl _ (hrank v hv)

/-! ### The upper bound `n - 1` -/

/-- The nodes to be updated, other than the source, in decreasing order of their position on the
new route. -/
def revOrder : List V := I.new.reverse.filter (fun v => decide (v ∈ I.toUpdate ∧ v ≠ I.s))

theorem revOrder_pairwise : I.revOrder.Pairwise (fun a b => I.pos₂ b < I.pos₂ a) := by
  have h : I.new.Pairwise (fun a b => I.pos₂ a < I.pos₂ b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [I.pos₂_getElem, I.pos₂_getElem]; exact hij
  exact (List.pairwise_reverse.2 h).filter _

theorem mem_revOrder {v : V} : v ∈ I.revOrder ↔ v ∈ I.toUpdate ∧ v ≠ I.s := by
  unfold revOrder
  simp only [List.mem_filter, List.mem_reverse, decide_eq_true_eq, I.mem_new_iff]
  exact ⟨fun h => h.2, fun h => ⟨I.mem_old_of_mem_toUpdate h.1, h⟩⟩

theorem revOrder_nodup : I.revOrder.Nodup :=
  I.revOrder_pairwise.imp (fun h e => by subst e; exact lt_irrefl _ h)

theorem length_revOrder (hs : I.s ∈ I.toUpdate) :
    I.revOrder.length = I.toUpdate.card - 1 := by
  rw [← List.toFinset_card_of_nodup I.revOrder_nodup, ← Finset.card_erase_of_mem hs]
  congr 1; ext v; simp [I.mem_revOrder, and_comm]

/-- The schedule of the upper bound: one node per round, from the destination backwards along the
new route; the source is updated together with the last of them. -/
def backwardRounds : List (Finset V) :=
  List.ofFn (n := I.revOrder.length) fun i =>
    if i.val + 1 = I.revOrder.length then {I.revOrder[i], I.s} else {I.revOrder[i]}

theorem length_backwardRounds : I.backwardRounds.length = I.revOrder.length := by
  simp [backwardRounds]

theorem mem_backwardRounds {i : ℕ} (hi : i < I.backwardRounds.length) {x : V} :
    x ∈ I.backwardRounds[i] ↔
      x = I.revOrder[i]'(by simpa [length_backwardRounds] using hi) ∨
        (i + 1 = I.revOrder.length ∧ x = I.s) := by
  simp only [backwardRounds, List.getElem_ofFn]
  split_ifs with h <;> simp [h]

/-- "This is worst possible" (§2.2 of [paper]): if the source has to be updated, there is always a
strongly loop-free schedule with `n - 1` rounds, `n = |toUpdate| ≥ 2`. -/
theorem hasSLF_card_sub_one (hs : I.s ∈ I.toUpdate) (h2 : 2 ≤ I.toUpdate.card) :
    I.HasSLF (I.toUpdate.card - 1) := by
  have hlen := I.length_revOrder hs
  have hR := I.length_backwardRounds
  have hsL : I.s ∉ I.revOrder := fun h => ((I.mem_revOrder).1 h).2 rfl
  have hpw := List.pairwise_iff_getElem.1 I.revOrder_pairwise
  have hnd := List.nodup_iff_injective_get.1 I.revOrder_nodup
  refine ⟨I.backwardRounds, by omega, ⟨?_, ?_⟩, ?_⟩
  · -- disjointness
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [I.mem_backwardRounds] at hxi hxj
    rcases hxi with rfl | ⟨h1, rfl⟩
    · rcases hxj with h | ⟨-, h⟩
      · have := hnd (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) (by simpa using h)
        simp at this; omega
      · exact hsL (h ▸ List.getElem_mem _)
    · rcases hxj with h | ⟨h2, -⟩
      · exact hsL (h ▸ List.getElem_mem _)
      · omega
  · -- covering
    intro v hv
    by_cases hvs : v = I.s
    · refine ⟨I.backwardRounds[I.revOrder.length - 1]'(by omega), List.getElem_mem _, ?_⟩
      rw [I.mem_backwardRounds]; right; exact ⟨by omega, hvs⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((I.mem_revOrder).2 ⟨hv, hvs⟩)
      exact ⟨I.backwardRounds[i]'(by omega), List.getElem_mem _,
        (I.mem_backwardRounds _).2 (Or.inl rfl)⟩
  · -- loop-freedom
    intro t ht X hX
    apply I.loopFree_of_upClosed
    intro u hu hut hus x hxt hxs hle
    -- `u` was updated in some round `i ≤ t`
    obtain ⟨i, hi, hit, hui⟩ : ∃ (i : ℕ) (hi : i < I.backwardRounds.length), i ≤ t ∧
        u ∈ I.backwardRounds[i] := by
      rcases Finset.mem_union.1 hu with h | h
      · obtain ⟨i, hi, hit, h⟩ := mem_done.1 h
        exact ⟨i, hi, hit.le, h⟩
      · exact ⟨t, ht, le_rfl, hX h⟩
    rw [I.mem_backwardRounds] at hui
    replace hui : u = I.revOrder[i]'(by omega) := hui.resolve_right (fun h => hus h.2)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((I.mem_revOrder).2 ⟨hxt, hxs⟩)
    rw [hui] at hle hu
    have hji : j ≤ i := by
      by_contra hc
      have := hpw i j (by omega) hj (by omega)
      omega
    rcases Nat.lt_or_eq_of_le hji with hji | rfl
    · exact Finset.mem_union_left _ (mem_done.2 ⟨j, by omega, by omega,
        (I.mem_backwardRounds _).2 (Or.inl rfl)⟩)
    · exact hu

/-! ### A two-cycle forces an order between rounds -/

/-- If `b`'s new rule points to `w` and `w`'s old rule points back to `b`, a strongly loop-free
schedule must update `w` in a strictly earlier round than `b` (otherwise the state right after
installing `b` contains the loop `b → w → b`). -/
theorem round_lt_of_two_cycle {rounds : List (Finset V)} (h : I.IsSLF rounds) {b w : V}
    (hbw : I.out₂ b = some w) (hwb : I.out₁ w = some b) {i k : ℕ} (hi : i < rounds.length)
    (hk : k < rounds.length) (hb : b ∈ rounds[i]) (hw : w ∈ rounds[k]) : k < i := by
  by_contra hki
  have hne : w ≠ b := by
    rintro rfl; have := (I.out₁_spec hwb).2.2; omega
  have hdisj := List.pairwise_iff_getElem.1 h.1.1
  have hwA : w ∉ done rounds i ∪ {b} := by
    rw [Finset.mem_union, Finset.mem_singleton, not_or]
    refine ⟨fun hd => ?_, hne⟩
    obtain ⟨j, hj, hji, hwj⟩ := mem_done.1 hd
    exact Finset.disjoint_left.1 (hdisj j k hj hk (by omega)) hwj hw
  apply h.2 i hi {b} (by simpa using hb) b
  refine TransGen.head (b := w) ?_ (TransGen.single ?_)
  · unfold Step; rw [I.fwd_of_mem (by simp), hbw]
  · unfold Step; rw [I.fwd_of_not_mem hwA, hwb]

end Instance

/-! ### The instance of Figure 2 -/

/-- The new route of Figure 2 on the nodes `0, …, l - 1`: `0, l - 2, l - 3, …, 1, l - 1`. -/
def fig2New (l : ℕ) : List ℕ :=
  List.ofFn (n := l) fun i => if i.val = 0 ∨ i.val + 1 = l then i.val else l - 1 - i.val

example : fig2New 7 = [0, 5, 4, 3, 2, 1, 6] := by decide

theorem fig2New_length (l : ℕ) : (fig2New l).length = l := by simp [fig2New]

theorem fig2New_getElem (l i : ℕ) (h : i < (fig2New l).length) :
    (fig2New l)[i] = if i = 0 ∨ i + 1 = l then i else l - 1 - i := by
  simp [fig2New]

theorem fig2New_nodup (l : ℕ) : (fig2New l).Nodup := by
  rw [fig2New, List.nodup_ofFn]
  intro i j h
  have := i.isLt; have := j.isLt
  ext; simp only at h; split_ifs at h <;> omega

theorem mem_fig2New {l v : ℕ} : v ∈ fig2New l ↔ v < l := by
  rw [fig2New, List.mem_ofFn']
  constructor
  · rintro ⟨i, rfl⟩; have := i.isLt; dsimp only; split_ifs <;> omega
  · intro hv
    by_cases h : v = 0 ∨ v + 1 = l
    · exact ⟨⟨v, hv⟩, by simp [h]⟩
    · refine ⟨⟨l - 1 - v, by omega⟩, ?_⟩
      have : ¬ (l - 1 - v = 0 ∨ l - 1 - v + 1 = l) := by omega
      simp only [this, ite_false]; omega

/-- Figure 2 / §2.2 of [paper]: the old route is `s = v₁, v₂, …, v_l = d`, the new route is
`s, v_{l-1}, v_{l-2}, …, v₂, d`. Here `vᵢ` is the node `i - 1`. -/
def fig2 (l : ℕ) (hl : 4 ≤ l) : Instance ℕ where
  old := List.range l
  new := fig2New l
  nodup := List.nodup_range
  perm := List.perm_of_nodup_nodup_toFinset_eq List.nodup_range (fig2New_nodup l)
    (by ext v; simp [mem_fig2New])
  ne_nil := by simp; omega
  head_eq := by
    rw [List.head?_eq_getElem?, List.head?_eq_getElem?,
      List.getElem?_eq_getElem (by simp; omega),
      List.getElem?_eq_getElem (by simp [fig2New_length]; omega), fig2New_getElem]
    simp
  getLast_eq := by
    rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by simp; omega),
      List.getElem?_eq_getElem (by simp [fig2New_length]; omega), fig2New_getElem]
    simp [fig2New_length]; omega

section Fig2

variable {l : ℕ} {hl : 4 ≤ l}

theorem fig2_s : (fig2 l hl).s = 0 := by
  simp [Instance.s, fig2, List.head_range]

theorem fig2_d : (fig2 l hl).d = l - 1 := by
  simp [Instance.d, fig2]

theorem fig2_mem_old {v : ℕ} : v ∈ (fig2 l hl).old ↔ v < l := by simp [fig2]

theorem fig2_out₁ {v : ℕ} (hv : v + 1 < l) : (fig2 l hl).out₁ v = some (v + 1) := by
  have := (fig2 l hl).out₁_getElem v (by simp [fig2]; omega)
  simpa [fig2] using this

theorem fig2_out₂_of_getElem (i : ℕ) (hi : i + 1 < l) {v w : ℕ}
    (hv : (if i = 0 ∨ i + 1 = l then i else l - 1 - i) = v)
    (hw : (if i + 1 = 0 ∨ i + 1 + 1 = l then i + 1 else l - 1 - (i + 1)) = w) :
    (fig2 l hl).out₂ v = some w := by
  have := (fig2 l hl).out₂_getElem i (by simp [fig2, fig2New_length]; omega)
  simp only [fig2, fig2New_getElem] at this
  rwa [hv, hw] at this

/-- The new rule of `s = v₁` points to `v_{l-1}`. -/
theorem fig2_out₂_zero : (fig2 l hl).out₂ 0 = some (l - 2) := by
  apply fig2_out₂_of_getElem 0 (by omega)
  · simp
  · have : ¬ (0 + 1 = 0 ∨ 0 + 1 + 1 = l) := by omega
    simp only [this, ite_false]; omega

/-- The new rule of `v₂` points to `d`. -/
theorem fig2_out₂_one : (fig2 l hl).out₂ 1 = some (l - 1) := by
  apply fig2_out₂_of_getElem (l - 2) (by omega)
  · have : ¬ (l - 2 = 0 ∨ l - 2 + 1 = l) := by omega
    simp only [this, ite_false]; omega
  · have : l - 2 + 1 = 0 ∨ l - 2 + 1 + 1 = l := by omega
    simp only [this, ite_true]; omega

/-- The new rule of `v_{j+1}`, `2 ≤ j ≤ l - 2`, points backward to `v_j`. -/
theorem fig2_out₂_bwd {j : ℕ} (h2 : 2 ≤ j) (hj : j + 2 ≤ l) :
    (fig2 l hl).out₂ j = some (j - 1) := by
  apply fig2_out₂_of_getElem (l - 1 - j) (by omega)
  · have : ¬ (l - 1 - j = 0 ∨ l - 1 - j + 1 = l) := by omega
    simp only [this, ite_false]; omega
  · have : ¬ (l - 1 - j + 1 = 0 ∨ l - 1 - j + 1 + 1 = l) := by omega
    simp only [this, ite_false]; omega

theorem fig2_mem_toUpdate {v : ℕ} : v ∈ (fig2 l hl).toUpdate ↔ v + 1 < l := by
  constructor
  · intro h
    have h1 := (fig2_mem_old (hl := hl)).1 ((fig2 l hl).mem_old_of_mem_toUpdate h)
    have h2 := (fig2 l hl).ne_d_of_mem_toUpdate h
    rw [fig2_d] at h2; omega
  · intro hv
    refine Finset.mem_filter.2 ⟨(Instance.mem_nodes _).2 (fig2_mem_old.2 (by omega)), ?_⟩
    rw [fig2_out₁ hv]
    rcases Nat.lt_or_ge v 2 with h | h
    · interval_cases v
      · rw [fig2_out₂_zero]; simp; omega
      · rw [fig2_out₂_one]; simp; omega
    · rw [fig2_out₂_bwd h (by omega)]; simp; omega

theorem fig2_toUpdate : (fig2 l hl).toUpdate = Finset.range (l - 1) := by
  ext v; rw [fig2_mem_toUpdate, Finset.mem_range]; omega

/-- Figure 2: all `n = l - 1` nodes except the destination have to be updated. -/
theorem fig2_card_toUpdate : (fig2 l hl).toUpdate.card = l - 1 := by
  rw [fig2_toUpdate, Finset.card_range]

/-- Figure 2 / §2.2 of [paper]: every strongly loop-free schedule needs at least `n - 1 = l - 2`
rounds ("a strong loop-free schedule needs to go through the backward edges one by one"). -/
theorem fig2_slf_lower {rounds : List (Finset ℕ)} (h : (fig2 l hl).IsSLF rounds) :
    l - 2 ≤ rounds.length := by
  have cover : ∀ j, j + 1 < l → ∃ (i : ℕ) (hi : i < rounds.length), j ∈ rounds[i] := by
    intro j hj
    obtain ⟨r, hr, hjr⟩ := h.1.2 j (fig2_mem_toUpdate.2 hj)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    exact ⟨i, hi, hjr⟩
  have key : ∀ j, 1 ≤ j → j + 2 ≤ l →
      ∃ (i : ℕ) (hi : i < rounds.length), j - 1 ≤ i ∧ j ∈ rounds[i] := by
    intro j hj1 hj2
    induction j, hj1 using Nat.le_induction with
    | base =>
      obtain ⟨i, hi, h1⟩ := cover 1 (by omega)
      exact ⟨i, hi, by omega, h1⟩
    | succ j hj ih =>
      obtain ⟨i, hi, hji, hj⟩ := ih (by omega)
      obtain ⟨i', hi', hj'⟩ := cover (j + 1) (by omega)
      have := (fig2 l hl).round_lt_of_two_cycle h (fig2_out₂_bwd (by omega) hj2)
        (by simpa using fig2_out₁ (hl := hl) (v := j) (by omega)) hi' hi hj' (by simpa using hj)
      exact ⟨i', hi', by omega, hj'⟩
  obtain ⟨i, hi, hle, -⟩ := key (l - 2) (by omega) (by omega)
  omega

/-- Figure 2: `n - 1 = l - 2` rounds suffice for strong loop-freedom (instance of
`Instance.hasSLF_card_sub_one`). -/
theorem fig2_hasSLF : (fig2 l hl).HasSLF (l - 2) := by
  have := (fig2 l hl).hasSLF_card_sub_one (by rw [fig2_s, fig2_mem_toUpdate]; omega)
    (by rw [fig2_card_toUpdate]; omega)
  rwa [fig2_card_toUpdate, show l - 1 - 1 = l - 2 by omega] at this

/-- Consequently no SLF schedule with fewer than `n - 1` rounds exists (e.g. none with 3 rounds once
`l ≥ 6`). -/
theorem fig2_not_hasSLF {k : ℕ} (hk : k < l - 2) : ¬ (fig2 l hl).HasSLF k := by
  rintro ⟨rounds, rfl, h⟩
  have := fig2_slf_lower h; omega

/-! #### The 3-round relaxed loop-free schedule -/

theorem fig2_step {A : Finset ℕ} {u v : ℕ} (h : (fig2 l hl).fwd A u = some v) :
    (fig2 l hl).Step A u v := h

/-- Rounds of the RLF schedule: first the forward edges `{v₁, v₂}`, then all backward edges except
the last one, then the last backward edge `v_{l-1}`. -/
def fig2RLFRounds (l : ℕ) : List (Finset ℕ) := [{0, 1}, Finset.Icc 2 (l - 3), {l - 2}]

/-- Figure 2 / §2.2 of [paper]: a relaxed loop-free schedule with 3 rounds. -/
theorem fig2_hasRLF : (fig2 l hl).HasRLF 3 := by
  set I := fig2 l hl
  have hs : I.s = 0 := fig2_s
  have hd : I.d = l - 1 := fig2_d
  -- `s → v_{l-1} → d`
  have P1 : ∀ A : Finset ℕ, 0 ∈ A → l - 2 ∉ A → I.RelaxedLoopFree A := by
    intro A h0 hl2
    rw [I.relaxedLoopFree_iff, hs, hd]
    refine ReflTransGen.head (b := l - 2) (fig2_step ?_) (ReflTransGen.single (fig2_step ?_))
    · exact (I.fwd_of_mem h0).trans fig2_out₂_zero
    · rw [I.fwd_of_not_mem hl2, fig2_out₁ (by omega)]; congr 1; omega
  -- `s → v₂ → d`
  have P2 : ∀ A : Finset ℕ, 0 ∉ A → 1 ∈ A → I.RelaxedLoopFree A := by
    intro A h0 h1
    rw [I.relaxedLoopFree_iff, hs, hd]
    refine ReflTransGen.head (b := 1) (fig2_step ?_) (ReflTransGen.single (fig2_step ?_))
    · exact (I.fwd_of_not_mem h0).trans (fig2_out₁ (by omega))
    · exact (I.fwd_of_mem h1).trans fig2_out₂_one
  -- the old route
  have P3 : ∀ A : Finset ℕ, (∀ v ∈ A, l - 1 ≤ v) → I.RelaxedLoopFree A := by
    intro A hA
    rw [I.relaxedLoopFree_iff]
    have := I.reach_old (A := A) (a := 0) (b := l - 1) (by omega) (by simp [I, fig2]; omega)
      (fun j hj _ hj2 => I.fwd_of_not_mem (fun hm => by
        have := hA _ hm; simp [I, fig2] at this; omega))
    simpa [I, fig2, ← hs, ← hd] using this
  -- the new route
  have P4 : ∀ A : Finset ℕ, (∀ v, v + 1 < l → v ∈ A) → I.RelaxedLoopFree A := by
    intro A hA
    rw [I.relaxedLoopFree_iff]
    rw [I.s_eq_new_head, I.d_eq_new_getLast, List.head_eq_getElem, List.getLast_eq_getElem]
    have hlen : I.new.length = l := fig2New_length l
    exact I.reach_new (by omega) (by omega) (fun j hj _ hj2 => I.fwd_of_mem (hA _ (by
      have := fig2New_getElem l j (by rw [fig2New_length]; omega)
      simp only [I, fig2] at hj ⊢
      rw [this]; split_ifs <;> omega)))
  refine ⟨fig2RLFRounds l, rfl, ⟨?_, ?_⟩, ?_⟩
  · simp only [fig2RLFRounds]
    simp [Finset.disjoint_left]
    exact ⟨by omega, fun a _ h => by omega⟩
  · intro v hv
    rw [fig2_mem_toUpdate] at hv
    simp only [fig2RLFRounds, List.mem_cons, List.not_mem_nil, exists_eq_or_imp]
    by_cases h1 : v ≤ 1
    · left; simp; omega
    · right
      by_cases h2 : v ≤ l - 3
      · left; simp; omega
      · right; left; simp; omega
  · intro t ht X hX
    simp only [fig2RLFRounds, List.length_cons, List.length_nil] at ht
    interval_cases t
    · simp only [fig2RLFRounds, List.getElem_cons_zero] at hX
      simp only [Instance.done_zero, Finset.empty_union]
      by_cases h0 : 0 ∈ X
      · exact P1 X h0 (fun h => by have := hX h; simp at this; omega)
      · by_cases h1 : 1 ∈ X
        · exact P2 X h0 h1
        · refine P3 X (fun v hv => ?_)
          have := hX hv; simp at this; rcases this with rfl | rfl <;> contradiction
    · simp only [fig2RLFRounds, List.getElem_cons_succ, List.getElem_cons_zero] at hX
      refine P1 _ (by simp [Instance.done, fig2RLFRounds]) (fun h => ?_)
      simp [Instance.done, fig2RLFRounds] at h
      rcases h with h | h | h <;> first | omega | (have := hX h; simp at this; omega)
    · simp only [fig2RLFRounds, List.getElem_cons_succ, List.getElem_cons_zero] at hX
      by_cases hX' : l - 2 ∈ X
      · refine P4 _ (fun v hv => ?_)
        by_cases hv2 : v = l - 2
        · subst hv2; exact Finset.mem_union_right _ hX'
        · refine Finset.mem_union_left _ ?_
          simp [Instance.done, fig2RLFRounds]; omega
      · refine P1 _ (by simp [Instance.done, fig2RLFRounds]) (fun h => ?_)
        simp [Instance.done, fig2RLFRounds] at h
        rcases h with h | h | h | h <;> first | omega | exact hX' h

end Fig2

end Podc.LoopFreeUpdates
