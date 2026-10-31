import Papers.PODC2015.LoopFreeUpdates.Model

/-!
# Basic facts about the model

Positions, the source and the destination, rank arguments for loop-freedom, and the two ways to
create a loop: a backward new rule whose target still forwards along the old route back to it, and
symmetrically a backward old rule.
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

variable {V : Type*} [DecidableEq V]

namespace Instance

variable (I : Instance V)

theorem s_eq_new_head : I.s = I.new.head I.new_ne_nil := by
  have h := I.head_eq
  rw [List.head?_eq_some_head I.ne_nil, List.head?_eq_some_head I.new_ne_nil] at h
  exact Option.some_injective _ h

theorem d_eq_new_getLast : I.d = I.new.getLast I.new_ne_nil := by
  have h := I.getLast_eq
  rw [List.getLast?_eq_some_getLast I.ne_nil, List.getLast?_eq_some_getLast I.new_ne_nil] at h
  exact Option.some_injective _ h

theorem length_new : I.new.length = I.old.length := I.perm.length_eq.symm

theorem length_pos : 0 < I.old.length := List.length_pos_iff.2 I.ne_nil

theorem mem_nodes {v : V} : v ∈ I.nodes ↔ v ∈ I.old := List.mem_toFinset

theorem s_mem : I.s ∈ I.old := List.head_mem _
theorem d_mem : I.d ∈ I.old := List.getLast_mem _

theorem pos₁_s : I.pos₁ I.s = 0 := by
  unfold pos₁ s
  rw [List.head_eq_getElem, I.nodup.idxOf_getElem]

theorem pos₂_s : I.pos₂ I.s = 0 := by
  rw [s_eq_new_head]
  unfold pos₂
  rw [List.head_eq_getElem, I.nodup_new.idxOf_getElem]

theorem pos₁_d : I.pos₁ I.d = I.old.length - 1 := by
  unfold pos₁ d
  rw [List.getLast_eq_getElem, I.nodup.idxOf_getElem]

theorem pos₂_d : I.pos₂ I.d = I.old.length - 1 := by
  rw [d_eq_new_getLast]
  unfold pos₂
  rw [List.getLast_eq_getElem, I.nodup_new.idxOf_getElem, length_new]

theorem pos₁_lt {v : V} (h : v ∈ I.old) : I.pos₁ v < I.old.length := List.idxOf_lt_length_of_mem h
theorem pos₂_lt {v : V} (h : v ∈ I.old) : I.pos₂ v < I.old.length := by
  rw [← length_new]; exact List.idxOf_lt_length_of_mem ((I.mem_new_iff).2 h)

theorem pos₁_inj {v w : V} (hv : v ∈ I.old) (hw : w ∈ I.old) (h : I.pos₁ v = I.pos₁ w) : v = w := by
  unfold pos₁ at h
  rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hv),
    ← List.getElem_idxOf (List.idxOf_lt_length_of_mem hw)]
  simp [h]

theorem pos₂_inj {v w : V} (hv : v ∈ I.old) (hw : w ∈ I.old) (h : I.pos₂ v = I.pos₂ w) : v = w := by
  have hv' := (I.mem_new_iff).2 hv
  have hw' := (I.mem_new_iff).2 hw
  unfold pos₂ at h
  rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hv'),
    ← List.getElem_idxOf (List.idxOf_lt_length_of_mem hw')]
  simp [h]

theorem getElem_pos₁ {v : V} (h : v ∈ I.old) : I.old[I.pos₁ v]'(I.pos₁_lt h) = v :=
  List.getElem_idxOf _

theorem getElem_pos₂ {v : V} (h : v ∈ I.old) :
    I.new[I.pos₂ v]'(by rw [length_new]; exact I.pos₂_lt h) = v :=
  List.getElem_idxOf _

theorem pos₁_getElem (i : ℕ) (h : i < I.old.length) : I.pos₁ I.old[i] = i :=
  I.nodup.idxOf_getElem i h

theorem pos₂_getElem (i : ℕ) (h : i < I.new.length) : I.pos₂ I.new[i] = i :=
  I.nodup_new.idxOf_getElem i h

theorem out₁_spec {v w : V} (h : I.out₁ v = some w) :
    v ∈ I.old ∧ w ∈ I.old ∧ I.pos₁ w = I.pos₁ v + 1 := by
  obtain ⟨h1, h2⟩ := mem_of_nextIn I.nodup h
  exact ⟨h1, h2, (idxOf_of_nextIn I.nodup h).1⟩

theorem out₂_spec {v w : V} (h : I.out₂ v = some w) :
    v ∈ I.old ∧ w ∈ I.old ∧ I.pos₂ w = I.pos₂ v + 1 := by
  obtain ⟨h1, h2⟩ := mem_of_nextIn I.nodup_new h
  exact ⟨(I.mem_new_iff).1 h1, (I.mem_new_iff).1 h2, (idxOf_of_nextIn I.nodup_new h).1⟩

theorem out₁_getElem (i : ℕ) (h : i + 1 < I.old.length) : I.out₁ I.old[i] = some I.old[i + 1] :=
  nextIn_getElem I.nodup i h

theorem out₂_getElem (i : ℕ) (h : i + 1 < I.new.length) : I.out₂ I.new[i] = some I.new[i + 1] :=
  nextIn_getElem I.nodup_new i h

theorem out₁_d : I.out₁ I.d = none := by
  unfold out₁ nextIn
  rw [show I.old.idxOf I.d = I.pos₁ I.d from rfl, pos₁_d]
  simp; have := I.length_pos; omega

theorem out₂_d : I.out₂ I.d = none := by
  unfold out₂ nextIn
  rw [show I.new.idxOf I.d = I.pos₂ I.d from rfl, pos₂_d]
  have := I.length_pos; have := I.length_new
  simp; omega

theorem out₁_ne_s (v : V) : I.out₁ v ≠ some I.s := by
  intro h
  have := (I.out₁_spec h).2.2
  rw [pos₁_s] at this; omega

theorem out₂_ne_s (v : V) : I.out₂ v ≠ some I.s := by
  intro h
  have := (I.out₂_spec h).2.2
  rw [pos₂_s] at this; omega

theorem out₁_of_ne_d {v : V} (hv : v ∈ I.old) (hd : v ≠ I.d) :
    ∃ w, I.out₁ v = some w := by
  have h1 := I.pos₁_lt hv
  have h2 : I.pos₁ v ≠ I.old.length - 1 := by
    intro h; rw [← pos₁_d] at h; exact hd (I.pos₁_inj hv I.d_mem h)
  exact Option.isSome_iff_exists.1 (nextIn_isSome (by unfold pos₁ at h1 h2; omega))

theorem out₂_of_ne_d {v : V} (hv : v ∈ I.old) (hd : v ≠ I.d) :
    ∃ w, I.out₂ v = some w := by
  have h1 := I.pos₂_lt hv
  have h2 : I.pos₂ v ≠ I.old.length - 1 := by
    intro h; rw [← pos₂_d] at h; exact hd (I.pos₂_inj hv I.d_mem h)
  have h3 := I.length_new
  exact Option.isSome_iff_exists.1 (nextIn_isSome (by unfold pos₂ at h1 h2; omega))

theorem out₁_eq_out₂_of_not_mem {v : V} (h : v ∉ I.toUpdate) : I.out₁ v = I.out₂ v := by
  by_cases hv : v ∈ I.old
  · by_contra hne
    exact h (Finset.mem_filter.2 ⟨(I.mem_nodes).2 hv, hne⟩)
  · unfold out₁ out₂
    rw [nextIn_eq_none_of_not_mem hv, nextIn_eq_none_of_not_mem (by rwa [I.mem_new_iff])]

theorem mem_old_of_mem_toUpdate {v : V} (h : v ∈ I.toUpdate) : v ∈ I.old :=
  (I.mem_nodes).1 (Finset.mem_filter.1 h).1

theorem ne_d_of_mem_toUpdate {v : V} (h : v ∈ I.toUpdate) : v ≠ I.d := by
  rintro rfl
  exact (Finset.mem_filter.1 h).2 (by rw [out₁_d, out₂_d])

/-- A node to be updated whose new rule does not point forward points backward. -/
theorem dashed_bwd {v : V} (hv : v ∈ I.toUpdate) (h : ¬ I.DashedFwd v) :
    ∃ w, I.out₂ v = some w ∧ I.pos₁ w < I.pos₁ v := by
  obtain ⟨w, hw⟩ := I.out₂_of_ne_d (I.mem_old_of_mem_toUpdate hv) (I.ne_d_of_mem_toUpdate hv)
  refine ⟨w, hw, ?_⟩
  have hne : w ≠ v := by
    rintro rfl; have := (I.out₂_spec hw).2.2; omega
  have : I.pos₁ w ≠ I.pos₁ v := fun e =>
    hne (I.pos₁_inj (I.out₂_spec hw).2.1 (I.out₂_spec hw).1 e)
  have : ¬ I.pos₁ v < I.pos₁ w := fun hlt => h ⟨w, hw, hlt⟩
  omega

/-- A node to be updated whose old rule does not point forward on the new route points backward. -/
theorem solid_bwd {v : V} (hv : v ∈ I.toUpdate) (h : ¬ I.SolidFwd v) :
    ∃ w, I.out₁ v = some w ∧ I.pos₂ w < I.pos₂ v := by
  obtain ⟨w, hw⟩ := I.out₁_of_ne_d (I.mem_old_of_mem_toUpdate hv) (I.ne_d_of_mem_toUpdate hv)
  refine ⟨w, hw, ?_⟩
  have hne : w ≠ v := by
    rintro rfl; have := (I.out₁_spec hw).2.2; omega
  have : I.pos₂ w ≠ I.pos₂ v := fun e =>
    hne (I.pos₂_inj (I.out₁_spec hw).2.1 (I.out₁_spec hw).1 e)
  have : ¬ I.pos₂ v < I.pos₂ w := fun hlt => h ⟨w, hw, hlt⟩
  omega

/-! ### Forwarding -/

theorem fwd_of_mem {A : Finset V} {v : V} (h : v ∈ A) : I.fwd A v = I.out₂ v := by simp [fwd, h]
theorem fwd_of_not_mem {A : Finset V} {v : V} (h : v ∉ A) : I.fwd A v = I.out₁ v := by simp [fwd, h]

theorem fwd_of_not_toUpdate (A : Finset V) {v : V} (h : v ∉ I.toUpdate) :
    I.fwd A v = I.out₁ v := by
  unfold fwd; split_ifs
  · exact (I.out₁_eq_out₂_of_not_mem h).symm
  · rfl

/-- Only the updated nodes that really have to be updated matter. -/
theorem fwd_inter (A : Finset V) : I.fwd (A ∩ I.toUpdate) = I.fwd A := by
  funext v
  by_cases hv : v ∈ I.toUpdate
  · unfold fwd; simp [hv]
  · rw [fwd_of_not_toUpdate _ _ hv, fwd_of_not_toUpdate _ _ hv]

theorem fwd_d (A : Finset V) : I.fwd A I.d = none := by
  unfold fwd; split_ifs
  · exact I.out₂_d
  · exact I.out₁_d

theorem step_mem {A : Finset V} {u v : V} (h : I.Step A u v) : u ∈ I.old ∧ v ∈ I.old := by
  unfold Step fwd at h
  split_ifs at h
  · exact ⟨(I.out₂_spec h).1, (I.out₂_spec h).2.1⟩
  · exact ⟨(I.out₁_spec h).1, (I.out₁_spec h).2.1⟩

theorem not_step_s (A : Finset V) (u : V) : ¬ I.Step A u I.s := by
  unfold Step fwd
  split_ifs
  · exact I.out₂_ne_s u
  · exact I.out₁_ne_s u

theorem step_unique (A : Finset V) : Relator.RightUnique (I.Step A) := by
  intro a b c hb hc
  unfold Step at hb hc
  rw [hb] at hc
  exact Option.some_injective _ hc

/-- The only node of the route without a forwarding rule is the destination. -/
theorem eq_d_of_fwd_none {A : Finset V} {v : V} (hv : v ∈ I.old) (h : I.fwd A v = none) :
    v = I.d := by
  by_contra hd
  unfold fwd at h
  split_ifs at h
  · obtain ⟨w, hw⟩ := I.out₂_of_ne_d hv hd; rw [hw] at h; cases h
  · obtain ⟨w, hw⟩ := I.out₁_of_ne_d hv hd; rw [hw] at h; cases h

/-! ### Rank arguments -/

/-- A forwarding graph along which some rank strictly increases is loop-free. -/
theorem loopFree_of_rank {A : Finset V} (f : V → ℕ) (hf : ∀ u v, I.Step A u v → f u < f v) :
    I.LoopFree A := by
  intro v h
  have : ∀ a b, TransGen (I.Step A) a b → f a < f b := by
    intro a b hab
    induction hab with
    | single h => exact hf _ _ h
    | tail _ h ih => exact lt_trans ih (hf _ _ h)
  exact lt_irrefl _ (this v v h)

/-- If every updated node has a forward new rule, the state is loop-free (ranked by `pos₁`). -/
theorem loopFree_of_dashedFwd {A : Finset V} (h : ∀ v ∈ A, v ∈ I.toUpdate → I.DashedFwd v) :
    I.LoopFree A := by
  refine I.loopFree_of_rank I.pos₁ (fun u v huv => ?_)
  unfold Step at huv
  by_cases hu : u ∈ A ∧ u ∈ I.toUpdate
  · rw [fwd_of_mem _ hu.1] at huv
    obtain ⟨w, hw, hlt⟩ := h u hu.1 hu.2
    rw [hw] at huv; cases huv; exact hlt
  · have : I.fwd A u = I.out₁ u := by
      by_cases hA : u ∈ A
      · exact I.fwd_of_not_toUpdate A (fun h' => hu ⟨hA, h'⟩)
      · exact I.fwd_of_not_mem hA
    rw [this] at huv
    have := (I.out₁_spec huv).2.2; omega

/-- If every node that still uses its old rule has an old rule pointing forward on the new route,
the state is loop-free (ranked by `pos₂`). -/
theorem loopFree_of_solidFwd {A : Finset V} (h : ∀ v ∈ I.toUpdate, v ∉ A → I.SolidFwd v) :
    I.LoopFree A := by
  refine I.loopFree_of_rank I.pos₂ (fun u v huv => ?_)
  unfold Step at huv
  by_cases hu : u ∉ A ∧ u ∈ I.toUpdate
  · rw [fwd_of_not_mem _ hu.1] at huv
    obtain ⟨w, hw, hlt⟩ := h u hu.2 hu.1
    rw [hw] at huv; cases huv; exact hlt
  · have : I.fwd A u = I.out₂ u := by
      by_cases hA : u ∈ A
      · exact I.fwd_of_mem hA
      · rw [I.fwd_of_not_mem hA]
        exact I.out₁_eq_out₂_of_not_mem (fun h' => hu ⟨hA, h'⟩)
    rw [this] at huv
    have := (I.out₂_spec huv).2.2; omega

/-! ### Creating loops -/

/-- Following the old route: if all nodes at old positions `a, …, b-1` use their old rule, then the
node at position `a` reaches the node at position `b`. -/
theorem reach_old {A : Finset V} {a b : ℕ} (hab : a ≤ b) (hb : b < I.old.length)
    (h : ∀ j (hj : j < I.old.length), a ≤ j → j < b → I.fwd A I.old[j] = I.out₁ I.old[j]) :
    ReflTransGen (I.Step A) (I.old[a]'(by omega)) I.old[b] := by
  induction b, hab using Nat.le_induction with
  | base => exact ReflTransGen.refl
  | succ b hab ih =>
    refine (ih (by omega) (fun j hj h1 h2 => h j hj h1 (by omega))).tail ?_
    unfold Step
    rw [h b (by omega) hab (by omega)]
    exact I.out₁_getElem b hb

/-- Following the new route: if all nodes at new positions `a, …, b-1` use their new rule, then the
node at position `a` reaches the node at position `b`. -/
theorem reach_new {A : Finset V} {a b : ℕ} (hab : a ≤ b) (hb : b < I.new.length)
    (h : ∀ j (hj : j < I.new.length), a ≤ j → j < b → I.fwd A I.new[j] = I.out₂ I.new[j]) :
    ReflTransGen (I.Step A) (I.new[a]'(by omega)) I.new[b] := by
  induction b, hab using Nat.le_induction with
  | base => exact ReflTransGen.refl
  | succ b hab ih =>
    refine (ih (by omega) (fun j hj h1 h2 => h j hj h1 (by omega))).tail ?_
    unfold Step
    rw [h b (by omega) hab (by omega)]
    exact I.out₂_getElem b hb

/-- A node with a backward new rule creates a loop if it is updated while all nodes between its
target and itself (on the old route) still use their old rule. -/
theorem loop_of_dashed_bwd {A : Finset V} {b w : V} (hb : b ∈ A) (hw : I.out₂ b = some w)
    (hlt : I.pos₁ w < I.pos₁ b)
    (hold : ∀ v ∈ I.old, I.pos₁ w ≤ I.pos₁ v → I.pos₁ v < I.pos₁ b → I.fwd A v = I.out₁ v) :
    TransGen (I.Step A) b b := by
  obtain ⟨hbm, hwm, -⟩ := I.out₂_spec hw
  have hr := I.reach_old (A := A) hlt.le (I.pos₁_lt hbm) (fun j hj h1 h2 => by
    have := hold I.old[j] (List.getElem_mem _)
    rw [I.pos₁_getElem] at this
    exact this h1 h2)
  simp only [I.getElem_pos₁ hwm, I.getElem_pos₁ hbm] at hr
  exact TransGen.head' (by unfold Step; rw [I.fwd_of_mem hb, hw]) hr

/-- A node with a backward old rule (on the new route) creates a loop if it still uses its old rule
while all nodes between its target and itself (on the new route) already use their new rule. -/
theorem loop_of_solid_bwd {A : Finset V} {b w : V} (hb : b ∉ A) (hw : I.out₁ b = some w)
    (hlt : I.pos₂ w < I.pos₂ b)
    (hnew : ∀ v ∈ I.old, I.pos₂ w ≤ I.pos₂ v → I.pos₂ v < I.pos₂ b → I.fwd A v = I.out₂ v) :
    TransGen (I.Step A) b b := by
  obtain ⟨hbm, hwm, -⟩ := I.out₁_spec hw
  have hr := I.reach_new (A := A) hlt.le (by rw [length_new]; exact I.pos₂_lt hbm)
    (fun j hj h1 h2 => by
      have := hnew I.new[j] ((I.mem_new_iff).1 (List.getElem_mem _))
      rw [I.pos₂_getElem] at this
      exact this h1 h2)
  simp only [I.getElem_pos₂ hwm, I.getElem_pos₂ hbm] at hr
  exact TransGen.head' (by unfold Step; rw [I.fwd_of_not_mem hb, hw]) hr

/-! ### Relaxed loop-freedom as reachability of the destination -/

/-- The walk from `v` in state `A` after `k` steps (`none` once it has stopped). -/
def iterFrom (A : Finset V) (v : V) (k : ℕ) : Option V := (fun o => o.bind (I.fwd A))^[k] (some v)

theorem iterFrom_succ (A : Finset V) (v : V) (k : ℕ) :
    I.iterFrom A v (k + 1) = (I.iterFrom A v k).bind (I.fwd A) := by
  unfold iterFrom; rw [Function.iterate_succ_apply']

theorem iterFrom_add (A : Finset V) (v w : V) (i m : ℕ) (h : I.iterFrom A v i = some w) :
    I.iterFrom A v (i + m) = I.iterFrom A w m := by
  unfold iterFrom at *
  rw [Nat.add_comm, Function.iterate_add_apply, h]

theorem reach_of_iterFrom {A : Finset V} {v w : V} {k : ℕ} (h : I.iterFrom A v k = some w) :
    ReflTransGen (I.Step A) v w := by
  induction k generalizing w with
  | zero => unfold iterFrom at h; cases h; exact ReflTransGen.refl
  | succ k ih =>
    rw [iterFrom_succ] at h
    cases hk : I.iterFrom A v k with
    | none => rw [hk] at h; cases h
    | some u => rw [hk] at h; exact (ih hk).tail h

theorem transGen_of_iterFrom {A : Finset V} {v w : V} {k : ℕ} (hk : 0 < k)
    (h : I.iterFrom A v k = some w) : TransGen (I.Step A) v w := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [iterFrom_succ] at h
  cases hj : I.iterFrom A v k with
  | none => rw [hj] at h; cases h
  | some u => rw [hj] at h; exact TransGen.tail' (I.reach_of_iterFrom hj) h

theorem iterFrom_mem {A : Finset V} {v w : V} {k : ℕ} (hv : v ∈ I.old)
    (h : I.iterFrom A v k = some w) : w ∈ I.old := by
  rcases (I.reach_of_iterFrom h).cases_tail with rfl | ⟨c, -, hc⟩
  · exact hv
  · exact (I.step_mem hc).2

/-- If the destination is reachable from the source, no loop is reachable from the source. -/
theorem relaxedLoopFree_of_reach {A : Finset V} (h : ReflTransGen (I.Step A) I.s I.d) :
    I.RelaxedLoopFree A := by
  intro v hv hloop
  have hvd : ReflTransGen (I.Step A) v I.d := by
    rcases ReflTransGen.total_of_right_unique (I.step_unique A) hv h with h1 | h1
    · exact h1
    · rcases h1.cases_head with rfl | ⟨c, hc, -⟩
      · exact ReflTransGen.refl
      · unfold Step at hc; rw [I.fwd_d] at hc; cases hc
  -- every node reachable from `v` lies on the cycle, in particular `d`
  obtain ⟨c, hc, hcv⟩ := TransGen.head'_iff.1 hloop
  have key : ∀ y, ReflTransGen (I.Step A) v y → ReflTransGen (I.Step A) y v := by
    intro y hy
    induction hy with
    | refl => exact ReflTransGen.refl
    | tail _ hyz ih =>
      rcases ih.cases_head with rfl | ⟨y', hy', hy'v⟩
      · rw [I.step_unique A hyz hc]; exact hcv
      · rw [I.step_unique A hyz hy']; exact hy'v
  rcases (key _ hvd).cases_head with rfl | ⟨e, he, -⟩
  · unfold Step at hc; rw [I.fwd_d] at hc; cases hc
  · unfold Step at he; rw [I.fwd_d] at he; cases he

/-- Conversely, relaxed loop-freedom means that the walk from the source reaches the destination. -/
theorem reach_of_relaxedLoopFree {A : Finset V} (h : I.RelaxedLoopFree A) :
    ReflTransGen (I.Step A) I.s I.d := by
  classical
  by_cases hall : ∀ k ≤ I.nodes.card, (I.iterFrom A I.s k).isSome
  · exfalso
    have hmaps : ∀ k ∈ Finset.range (I.nodes.card + 1),
        (I.iterFrom A I.s k).getD I.s ∈ I.nodes := by
      intro k hk
      have hs := hall k (by simpa [Nat.lt_succ_iff] using hk)
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
      rw [hw]; simpa [I.mem_nodes] using I.iterFrom_mem I.s_mem hw
    obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by simp) hmaps
    wlog hlt : i < j generalizing i j
    · exact this j hj i hi hij.symm heq.symm (by omega)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hall i (by simp at hi; omega))
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 (hall j (by simp at hj; omega))
    rw [hw, hw'] at heq
    simp only [Option.getD_some] at heq
    subst heq
    have h2 : I.iterFrom A w (j - i) = some w := by
      rw [← I.iterFrom_add A I.s w i (j - i) hw, Nat.add_sub_cancel' hlt.le, hw']
    exact h w (I.reach_of_iterFrom hw) (I.transGen_of_iterFrom (by omega) h2)
  · push Not at hall
    obtain ⟨k, -, hk⟩ := hall
    -- the least stopping time
    have hex : ∃ k, I.iterFrom A I.s k = none := ⟨k, by simpa using hk⟩
    let k₀ := Nat.find hex
    have hk₀ : I.iterFrom A I.s k₀ = none := Nat.find_spec hex
    have hpos : k₀ ≠ 0 := by
      intro h0; rw [h0] at hk₀; unfold iterFrom at hk₀; simp at hk₀
    obtain ⟨w, hw⟩ : ∃ w, I.iterFrom A I.s (k₀ - 1) = some w := by
      have := Nat.find_min hex (show k₀ - 1 < k₀ by omega)
      exact Option.ne_none_iff_exists'.1 this
    have : I.fwd A w = none := by
      have := I.iterFrom_succ A I.s (k₀ - 1)
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hpos), hk₀, hw] at this
      exact this.symm
    have hwd := I.eq_d_of_fwd_none (I.iterFrom_mem I.s_mem hw) this
    rw [← hwd]; exact I.reach_of_iterFrom hw

theorem relaxedLoopFree_iff {A : Finset V} :
    I.RelaxedLoopFree A ↔ ReflTransGen (I.Step A) I.s I.d :=
  ⟨I.reach_of_relaxedLoopFree, I.relaxedLoopFree_of_reach⟩

/-- Strong loop-freedom implies relaxed loop-freedom. -/
theorem LoopFree.relaxed {A : Finset V} (h : I.LoopFree A) : I.RelaxedLoopFree A :=
  fun v _ => h v

/-! ### Rounds -/

theorem done_zero (rounds : List (Finset V)) : done rounds 0 = ∅ := by simp [done]

theorem done_nil (t : ℕ) : done ([] : List (Finset V)) t = ∅ := by simp [done]

theorem done_cons_succ (r : Finset V) (rs : List (Finset V)) (t : ℕ) :
    done (r :: rs) (t + 1) = r ∪ done rs t := by simp [done]

theorem mem_done {rounds : List (Finset V)} {t : ℕ} {v : V} :
    v ∈ done rounds t ↔ ∃ (i : ℕ) (h : i < rounds.length), i < t ∧ v ∈ rounds[i] := by
  induction rounds generalizing t with
  | nil => simp [done_nil]
  | cons r rs ih =>
    cases t with
    | zero => simp [done_zero]
    | succ t =>
      rw [done_cons_succ, Finset.mem_union, ih]
      constructor
      · rintro (h | ⟨i, hi, hit, hv⟩)
        · exact ⟨0, by simp, by omega, h⟩
        · exact ⟨i + 1, by simp; omega, by omega, by simpa using hv⟩
      · rintro ⟨i, hi, hit, hv⟩
        cases i with
        | zero => left; simpa using hv
        | succ i => right; exact ⟨i, by simp at hi; omega, by omega, by simpa using hv⟩

theorem done_succ (rounds : List (Finset V)) (t : ℕ) (ht : t < rounds.length) :
    done rounds (t + 1) = done rounds t ∪ rounds[t] := by
  ext v
  simp only [mem_done, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, hit, hv⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hit with h | rfl
    · exact Or.inl ⟨i, hi, h, hv⟩
    · exact Or.inr hv
  · rintro (⟨i, hi, hit, hv⟩ | hv)
    · exact ⟨i, hi, by omega, hv⟩
    · exact ⟨t, ht, by omega, hv⟩

/-! ### Decidability of the node types -/

theorem dashedFwd_iff (v : V) :
    I.DashedFwd v ↔ ((I.out₂ v).map (fun w => decide (I.pos₁ v < I.pos₁ w))).getD false = true := by
  unfold DashedFwd; cases I.out₂ v <;> simp

theorem solidFwd_iff (v : V) :
    I.SolidFwd v ↔ ((I.out₁ v).map (fun w => decide (I.pos₂ v < I.pos₂ w))).getD false = true := by
  unfold SolidFwd; cases I.out₁ v <;> simp

instance : DecidablePred I.DashedFwd := fun v =>
  decidable_of_iff' _ (I.dashedFwd_iff v)

instance : DecidablePred I.SolidFwd := fun v =>
  decidable_of_iff' _ (I.solidFwd_iff v)

instance : DecidablePred I.IsFF := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred I.IsFB := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred I.IsBF := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred I.IsBB := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Every node to be updated has exactly one of the four types. -/
theorem type_cases {v : V} (hv : v ∈ I.toUpdate) : I.IsFF v ∨ I.IsFB v ∨ I.IsBF v ∨ I.IsBB v := by
  unfold IsFF IsFB IsBF IsBB; tauto

/-! ### Checking loop-freedom by running the walks (used for concrete instances) -/

theorem iterFrom_isSome_of_cycle {A : Finset V} {v : V} (hv : TransGen (I.Step A) v v) (k : ℕ) :
    ∃ w, I.iterFrom A v k = some w ∧ ReflTransGen (I.Step A) w v := by
  obtain ⟨c, hc, hcv⟩ := TransGen.head'_iff.1 hv
  induction k with
  | zero => exact ⟨v, rfl, ReflTransGen.refl⟩
  | succ k ih =>
    obtain ⟨w, hw, hwv⟩ := ih
    rw [iterFrom_succ, hw]
    rcases hwv.cases_head with rfl | ⟨w', hw', hw'v⟩
    · exact ⟨c, hc, hcv⟩
    · exact ⟨w', hw', hw'v⟩

/-- If every walk stops within `N` steps, the state is loop-free. -/
theorem loopFree_of_iterFrom {A : Finset V} (N : ℕ)
    (h : ∀ v ∈ I.old, I.iterFrom A v N = none) : I.LoopFree A := by
  intro v hv
  obtain ⟨c, hc, -⟩ := TransGen.head'_iff.1 hv
  obtain ⟨w, hw, -⟩ := I.iterFrom_isSome_of_cycle hv N
  rw [h v (I.step_mem hc).1] at hw; cases hw

/-- If the walk from the source reaches the destination, the state is relaxed loop-free. -/
theorem relaxedLoopFree_of_iterFrom {A : Finset V} (N : ℕ) (h : I.iterFrom A I.s N = some I.d) :
    I.RelaxedLoopFree A :=
  I.relaxedLoopFree_of_reach (I.reach_of_iterFrom h)

end Instance

end Podc.LoopFreeUpdates
