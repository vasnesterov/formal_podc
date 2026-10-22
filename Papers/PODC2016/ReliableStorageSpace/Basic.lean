import Papers.PODC2016.ReliableStorageSpace.Model

/-!
# Basic lemmas about the model

Step lemmas, the pending-list invariant `PendOK`, runs driven by a strategy (`srun`, `splice`), and the
block-flow lemmas.
-/

noncomputable section

namespace Podc.ReliableStorageSpace

open Finset Classical

variable {C N J V : Type}

namespace Alg

variable (A : Alg C N J V)

/-! ### Step lemmas -/

section StepLemmas

variable {A} {X : A.Config}

theorem step_inv_free {c : C} {op : Op} (h : X.cur c = none) :
    A.step X (.inv c op) =
      { X with loc := Function.update X.loc c (A.invoke c (X.cnt c) op (X.loc c))
               cur := Function.update X.cur c (some op)
               hist := X.hist ++ [.inv c (X.cnt c) op] } := by
  simp [step, h]

theorem step_inv_busy {c : C} {op : Op} (h : X.cur c ≠ none) : A.step X (.inv c op) = X := by
  simp [step, h]

theorem step_step_none {c : C} (h : X.cur c = none) :
    A.step X (.step c) = { X with tick := X.tick + 1 } := by
  simp [step, h]

theorem step_step_trigger {c : C} {op : Op} {o : N} {r : A.R} {l : A.L} (h : X.cur c = some op)
    (ha : A.act c (X.cnt c) op (X.loc c) = .trigger o r l) :
    A.step X (.step c) =
      { X with loc := Function.update X.loc c l
               pend := X.pend ++ [⟨c, X.nrmw c, o, r⟩]
               nrmw := Function.update X.nrmw c (X.nrmw c + 1)
               tick := X.tick + 1 } := by
  simp [step, h, ha]

theorem step_step_ret {c : C} {op : Op} {l : A.L} (h : X.cur c = some op)
    (ha : A.act c (X.cnt c) op (X.loc c) = .ret l) :
    A.step X (.step c) =
      { X with loc := Function.update X.loc c l
               cur := Function.update X.cur c none
               cnt := Function.update X.cnt c (X.cnt c + 1)
               tick := X.tick + 1
               hist := X.hist ++
                 [.ret c (X.cnt c) (if op = .read then some (A.rdout c (X.loc c)) else none)] } := by
  simp [step, h, ha]

theorem step_step_idle {c : C} {op : Op} (h : X.cur c = some op)
    (ha : A.act c (X.cnt c) op (X.loc c) = .idle) :
    A.step X (.step c) = { X with tick := X.tick + 1 } := by
  simp [step, h, ha]

theorem step_exec_none {c : C} {m : ℕ} (h : A.findP X c m = none) : A.step X (.exec c m) = X := by
  simp [step, h]

theorem step_exec_some {c : C} {m : ℕ} {p : Pend C N A.R} (h : A.findP X c m = some p) :
    A.step X (.exec c m) =
      { X with obj := Function.update X.obj p.obj (A.apply p.rmw (X.obj p.obj)).1
               loc := Function.update X.loc c
                 (A.recv c (X.loc c) p.obj (A.apply p.rmw (X.obj p.obj)).2)
               pend := X.pend.filter (fun q => !decide (q.cl = c ∧ q.idx = m)) } := by
  simp [step, h]

@[simp] theorem step_skip : A.step X .skip = X := rfl

theorem findP_spec {c : C} {m : ℕ} {p : Pend C N A.R} (h : A.findP X c m = some p) :
    p ∈ X.pend ∧ p.cl = c ∧ p.idx = m := by
  unfold findP at h
  have h1 := List.find?_some h
  simp only [decide_eq_true_eq] at h1
  exact ⟨List.mem_of_find?_eq_some h, h1⟩

/-- Exhaustive case analysis of a step. -/
theorem step_cases (X : A.Config) (e : Event C) :
    A.step X e = X ∨ A.step X e = { X with tick := X.tick + 1 } ∨
    (∃ c op, e = .inv c op ∧ X.cur c = none ∧ A.step X e =
      { X with loc := Function.update X.loc c (A.invoke c (X.cnt c) op (X.loc c))
               cur := Function.update X.cur c (some op)
               hist := X.hist ++ [.inv c (X.cnt c) op] }) ∨
    (∃ c op o r l, e = .step c ∧ X.cur c = some op ∧
      A.act c (X.cnt c) op (X.loc c) = .trigger o r l ∧ A.step X e =
      { X with loc := Function.update X.loc c l
               pend := X.pend ++ [⟨c, X.nrmw c, o, r⟩]
               nrmw := Function.update X.nrmw c (X.nrmw c + 1)
               tick := X.tick + 1 }) ∨
    (∃ c op l, e = .step c ∧ X.cur c = some op ∧ A.act c (X.cnt c) op (X.loc c) = .ret l ∧
      A.step X e =
      { X with loc := Function.update X.loc c l
               cur := Function.update X.cur c none
               cnt := Function.update X.cnt c (X.cnt c + 1)
               tick := X.tick + 1
               hist := X.hist ++
                 [.ret c (X.cnt c) (if op = .read then some (A.rdout c (X.loc c)) else none)] }) ∨
    (∃ c m p, e = .exec c m ∧ A.findP X c m = some p ∧ A.step X e =
      { X with obj := Function.update X.obj p.obj (A.apply p.rmw (X.obj p.obj)).1
               loc := Function.update X.loc c
                 (A.recv c (X.loc c) p.obj (A.apply p.rmw (X.obj p.obj)).2)
               pend := X.pend.filter (fun q => !decide (q.cl = c ∧ q.idx = m)) }) := by
  rcases e with ⟨c, op⟩ | c | ⟨c, m⟩ | _
  · by_cases h : X.cur c = none
    · exact Or.inr (Or.inr (Or.inl ⟨c, op, rfl, h, step_inv_free h⟩))
    · exact Or.inl (step_inv_busy h)
  · rcases hc : X.cur c with _ | op
    · exact Or.inr (Or.inl (step_step_none hc))
    · rcases ha : A.act c (X.cnt c) op (X.loc c) with ⟨o, r, l⟩ | l | _
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, op, o, r, l, rfl, hc, ha, step_step_trigger hc ha⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, op, l, rfl, hc, ha, step_step_ret hc ha⟩))))
      · exact Or.inr (Or.inl (step_step_idle hc ha))
  · rcases hp : A.findP X c m with _ | p
    · exact Or.inl (step_exec_none hp)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, m, p, rfl, hp, step_exec_some hp⟩))))
  · exact Or.inl rfl

end StepLemmas

/-! ### Runs -/

theorem runFrom_append (X : A.Config) (l₁ l₂ : List (Event C)) :
    A.runFrom X (l₁ ++ l₂) = A.runFrom (A.runFrom X l₁) l₂ := by
  simp [runFrom, List.foldl_append]

theorem runFrom_concat (X : A.Config) (l : List (Event C)) (e : Event C) :
    A.runFrom X (l ++ [e]) = A.step (A.runFrom X l) e := by
  simp [runFrom, List.foldl_append]

/-- The run driven by a strategy `σ` from `X`. -/
def srun (X : A.Config) (σ : A.Config → Event C) : ℕ → A.Config
  | 0 => X
  | t + 1 => A.step (srun X σ t) (σ (srun X σ t))

/-- The first `s` events of the strategy run, as a list. -/
def sevs (X : A.Config) (σ : A.Config → Event C) (s : ℕ) : List (Event C) :=
  List.ofFn (fun i : Fin s => σ (A.srun X σ i))

theorem sevs_succ (X : A.Config) (σ : A.Config → Event C) (s : ℕ) :
    A.sevs X σ (s + 1) = A.sevs X σ s ++ [σ (A.srun X σ s)] := by
  rw [sevs, sevs, List.ofFn_succ_last]
  simp

theorem runFrom_sevs (X : A.Config) (σ : A.Config → Event C) (s : ℕ) :
    A.runFrom X (A.sevs X σ s) = A.srun X σ s := by
  induction s with
  | zero => simp [sevs, runFrom, srun]
  | succ s ih => rw [sevs_succ, runFrom_concat, ih]; rfl

/-- A finite prefix `evs`, then the strategy `σ`. -/
def splice (evs : List (Event C)) (σ : A.Config → Event C) (t : ℕ) : Event C :=
  if h : t < evs.length then evs[t] else σ (A.srun (A.runFrom A.init evs) σ (t - evs.length))

theorem cfg_splice_le (evs : List (Event C)) (σ : A.Config → Event C) :
    ∀ t ≤ evs.length, A.cfg (A.splice evs σ) t = A.runFrom A.init (evs.take t) := by
  intro t
  induction t with
  | zero => intro _; simp [cfg, runFrom]
  | succ t ih =>
    intro ht
    rw [cfg, ih (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some]
    rw [runFrom_concat]
    simp [splice, show t < evs.length by omega]

theorem cfg_splice (evs : List (Event C)) (σ : A.Config → Event C) (s : ℕ) :
    A.cfg (A.splice evs σ) (evs.length + s) = A.srun (A.runFrom A.init evs) σ s := by
  induction s with
  | zero => simp [cfg_splice_le A evs σ evs.length le_rfl, srun]
  | succ s ih =>
    rw [← add_assoc, cfg, ih]
    simp [splice, srun]

theorem splice_ge (evs : List (Event C)) (σ : A.Config → Event C) (s : ℕ) :
    A.splice evs σ (evs.length + s) = σ (A.cfg (A.splice evs σ) (evs.length + s)) := by
  rw [cfg_splice]; simp [splice]

theorem cfg_eq_runFrom (ev : ℕ → Event C) (t : ℕ) :
    A.cfg ev t = A.runFrom A.init (List.ofFn (fun i : Fin t => ev i)) := by
  induction t with
  | zero => simp [cfg, runFrom]
  | succ t ih => rw [cfg, ih, List.ofFn_succ_last, runFrom_concat]; rfl

/-! ### The pending list -/

/-- Invariant of the pending list: per client, indices strictly increase along the list, and are below
the number of triggered RMWs. In particular `(cl, idx)` identifies a pending RMW. -/
def PendOK (X : A.Config) : Prop :=
  X.pend.Pairwise (fun p q => p.cl = q.cl → p.idx < q.idx) ∧ ∀ p ∈ X.pend, p.idx < X.nrmw p.cl

theorem pendOK_init : A.PendOK A.init := by simp [PendOK, init]

variable {A} in
theorem PendOK.step {X : A.Config} (h : A.PendOK X) (e : Event C) : A.PendOK (A.step X e) := by
  rcases step_cases X e with h1 | h1 | ⟨c, op, -, -, h1⟩ | ⟨c, op, o, r, l, -, -, -, h1⟩ |
    ⟨c, op, l, -, -, -, h1⟩ | ⟨c, m, p, -, -, h1⟩ <;> rw [h1]
  · exact h
  · exact h
  · exact h
  · refine ⟨?_, ?_⟩
    · simp only [List.pairwise_append, List.pairwise_singleton, List.mem_singleton, true_and]
      refine ⟨h.1, ?_⟩
      rintro a ha _ rfl hac
      have := h.2 a ha
      simp only at hac ⊢
      rw [hac] at this
      exact this
    · intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · have := h.2 q hq
        by_cases hq' : q.cl = c
        · rw [hq'] at this ⊢; simp; omega
        · simp [hq', this]
      · simp
  · exact h
  · refine ⟨h.1.filter _, fun q hq => h.2 q (List.mem_of_mem_filter hq)⟩

theorem pendOK_runFrom {X : A.Config} (h : A.PendOK X) (evs : List (Event C)) :
    A.PendOK (A.runFrom X evs) := by
  induction evs generalizing X with
  | nil => exact h
  | cons e evs ih => exact ih (h.step e)

theorem Reachable.pendOK {X : A.Config} (h : A.Reachable X) : A.PendOK X := by
  obtain ⟨evs, rfl⟩ := h
  exact A.pendOK_runFrom A.pendOK_init evs

theorem pendOK_cfg (ev : ℕ → Event C) (t : ℕ) : A.PendOK (A.cfg ev t) := by
  induction t with
  | zero => exact A.pendOK_init
  | succ t ih => exact ih.step _

theorem pendOK_srun {X : A.Config} (h : A.PendOK X) (σ : A.Config → Event C) (s : ℕ) :
    A.PendOK (A.srun X σ s) := by
  induction s with
  | zero => exact h
  | succ s ih => exact ih.step _

variable {A} in
/-- With `PendOK`, a pending RMW is found by its identifier. -/
theorem PendOK.findP_eq {X : A.Config} (h : A.PendOK X) {p : Pend C N A.R} (hp : p ∈ X.pend) :
    A.findP X p.cl p.idx = some p := by
  unfold findP
  rw [List.find?_eq_some_iff_append]
  refine ⟨by simp, ?_⟩
  obtain ⟨as, bs, hX⟩ := List.append_of_mem hp
  refine ⟨as, bs, hX, fun a ha => ?_⟩
  have hpw := h.1
  rw [hX, List.pairwise_append] at hpw
  have := hpw.2.2 a ha p (List.mem_cons_self ..)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_and]
  intro h1 h2
  have := this h1
  omega

/-- Effective `exec` events strictly shorten the pending list. -/
theorem length_pend_exec {X : A.Config} {c : C} {m : ℕ} {p : Pend C N A.R}
    (h : A.findP X c m = some p) :
    (A.step X (.exec c m)).pend.length < X.pend.length := by
  rw [step_exec_some h]
  obtain ⟨hp, rfl, rfl⟩ := findP_spec h
  apply List.length_filter_lt_length_iff_exists.2
  exact ⟨p, hp, by simp⟩

/-! ### Blocks -/

theorem mem_pendBlk {X : A.Config} {c : C} {b : Blk C J} :
    b ∈ A.pendBlk X c ↔ ∃ p ∈ X.pend, p.cl = c ∧ b ∈ A.rblk p.rmw := by
  unfold pendBlk
  generalize X.pend = l
  induction l with
  | nil => simp
  | cons q l ih =>
    by_cases hq : q.cl = c
    · simp only [List.filter_cons, hq, decide_true, ite_true, List.map_cons, List.foldr_cons,
        Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨p, hp, h1, h2⟩)
        · exact ⟨q, Or.inl rfl, hq, h⟩
        · exact ⟨p, Or.inr hp, h1, h2⟩
      · rintro ⟨p, rfl | hp, h1, h2⟩
        · exact Or.inl h2
        · exact Or.inr ⟨p, hp, h1, h2⟩
    · simp only [List.filter_cons, hq, decide_false, Bool.false_eq_true, ite_false, ih,
        List.mem_cons]
      constructor
      · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, Or.inr hp, h1, h2⟩
      · rintro ⟨p, rfl | hp, h1, h2⟩
        · exact absurd h1 hq
        · exact ⟨p, hp, h1, h2⟩

theorem mem_held {X : A.Config} {c : C} {b : Blk C J} :
    b ∈ A.held X c ↔ b ∈ A.lblk (X.loc c) ∨ ∃ p ∈ X.pend, p.cl = c ∧ b ∈ A.rblk p.rmw := by
  simp [held, mem_pendBlk]

theorem mem_ofW {w : OpId C} {s : Finset (Blk C J)} {b : Blk C J} :
    b ∈ ofW w s ↔ b ∈ s ∧ b.1 = w := by
  simp [ofW]

theorem bits_mono {s t : Finset (Blk C J)} (h : s ⊆ t) : A.bits s ≤ A.bits t :=
  Finset.sum_le_sum_of_subset h

theorem card_le_bits (s : Finset (Blk C J)) : s.card ≤ A.bits s := by
  rw [card_eq_sum_ones]
  exact Finset.sum_le_sum fun b _ => A.sz_pos b.2

/-- Flow of blocks in one step, for clients: a client's held blocks after an event come from its held
blocks before, from new blocks of its own current write, or (for the client receiving a response) from
the object of the executed RMW. -/
theorem held_step (X : A.Config) (e : Event C) (c : C) (b : Blk C J)
    (hb : b ∈ A.held (A.step X e) c) :
    b ∈ A.held X c ∨ (X.cur c = some .write ∨ e = .inv c .write) ∧ b.1 = (c, X.cnt c) ∨
      ∃ m p, e = .exec c m ∧ A.findP X c m = some p ∧ b ∈ A.oblk (X.obj p.obj) := by
  rw [mem_held] at hb
  rcases step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o, r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1] at hb
  · exact Or.inl (A.mem_held.2 hb)
  · exact Or.inl (A.mem_held.2 hb)
  · simp only [Function.update_apply] at hb
    split_ifs at hb with hcc
    · subst hcc
      rcases hb with hb | hb
      · rcases A.invoke_blk _ _ _ _ b hb with hb | ⟨hop, hb2⟩
        · exact Or.inl (A.mem_held.2 (Or.inl hb))
        · subst hop
          exact Or.inr (Or.inl ⟨Or.inr rfl, hb2⟩)
      · exact Or.inl (A.mem_held.2 (Or.inr hb))
    · exact Or.inl (A.mem_held.2 hb)
  · simp only [Function.update_apply] at hb
    split_ifs at hb with hcc
    · subst hcc
      rcases hb with hb | ⟨q, hq, hqc, hqb⟩
      · rcases A.act_trigger_blk _ _ _ _ _ _ _ ha b (Finset.mem_union_right _ hb) with hb | ⟨rfl, hb⟩
        · exact Or.inl (A.mem_held.2 (Or.inl hb))
        · exact Or.inr (Or.inl ⟨Or.inl hc, hb⟩)
      · simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact Or.inl (A.mem_held.2 (Or.inr ⟨q, hq, hqc, hqb⟩))
        · rcases A.act_trigger_blk _ _ _ _ _ _ _ ha b (Finset.mem_union_left _ hqb) with hb | ⟨rfl, hb⟩
          · exact Or.inl (A.mem_held.2 (Or.inl hb))
          · exact Or.inr (Or.inl ⟨Or.inl hc, hb⟩)
    · rcases hb with hb | ⟨q, hq, hqc, hqb⟩
      · exact Or.inl (A.mem_held.2 (Or.inl hb))
      · simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact Or.inl (A.mem_held.2 (Or.inr ⟨q, hq, hqc, hqb⟩))
        · exact absurd hqc.symm hcc
  · simp only [Function.update_apply] at hb
    split_ifs at hb with hcc
    · subst hcc
      rcases hb with hb | hb
      · exact Or.inl (A.mem_held.2 (Or.inl (A.act_ret_blk _ _ _ _ _ ha hb)))
      · exact Or.inl (A.mem_held.2 (Or.inr hb))
    · exact Or.inl (A.mem_held.2 hb)
  · simp only [Function.update_apply] at hb
    split_ifs at hb with hcc
    · subst hcc
      rcases hb with hb | ⟨q, hq, hqc, hqb⟩
      · rcases Finset.mem_union.1 (A.recv_blk _ _ _ _ hb) with hb | hb
        · exact Or.inl (A.mem_held.2 (Or.inl hb))
        · rcases Finset.mem_union.1 (A.apply_blk _ _ (Finset.mem_union_right _ hb)) with hb | hb
          · exact Or.inr (Or.inr ⟨m, p, rfl, hp, hb⟩)
          · obtain ⟨hp1, hp2, -⟩ := findP_spec hp
            exact Or.inl (A.mem_held.2 (Or.inr ⟨p, hp1, hp2, hb⟩))
      · exact Or.inl (A.mem_held.2 (Or.inr ⟨q, List.mem_of_mem_filter hq, hqc, hqb⟩))
    · rcases hb with hb | ⟨q, hq, hqc, hqb⟩
      · exact Or.inl (A.mem_held.2 (Or.inl hb))
      · exact Or.inl (A.mem_held.2 (Or.inr ⟨q, List.mem_of_mem_filter hq, hqc, hqb⟩))

/-- Flow of blocks in one step, for objects: only an executed RMW changes an object, and the new
contents come from the old contents and the blocks carried by the RMW. -/
theorem oblk_step (X : A.Config) (e : Event C) (o : N) (b : Blk C J)
    (hb : b ∈ A.oblk ((A.step X e).obj o)) :
    b ∈ A.oblk (X.obj o) ∨ ∃ c m p, e = .exec c m ∧ A.findP X c m = some p ∧ p.obj = o ∧
      b ∈ A.rblk p.rmw := by
  rcases step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o', r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1] at hb
  · exact Or.inl hb
  · exact Or.inl hb
  · exact Or.inl hb
  · exact Or.inl hb
  · exact Or.inl hb
  · simp only [Function.update_apply] at hb
    split_ifs at hb with ho
    · subst ho
      rcases Finset.mem_union.1 (A.apply_blk _ _ (Finset.mem_union_left _ hb)) with hb | hb
      · exact Or.inl hb
      · exact Or.inr ⟨c', m, p, rfl, hp, rfl, hb⟩
    · exact Or.inl hb

/-- Objects change only by effective `exec` events on them. -/
theorem obj_step_of_not_exec (X : A.Config) (e : Event C) (o : N)
    (h : ¬ ∃ c m p, e = .exec c m ∧ A.findP X c m = some p ∧ p.obj = o) :
    (A.step X e).obj o = X.obj o := by
  rcases step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o', r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1]
  · simp only [Function.update_apply]
    split_ifs with ho
    · exact absurd ⟨c', m, p, rfl, hp, ho.symm⟩ h
    · rfl

/-- The history only grows. -/
theorem hist_step_prefix (X : A.Config) (e : Event C) : X.hist <+: (A.step X e).hist := by
  rcases step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o', r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1] <;>
    first | exact List.prefix_refl _ | exact List.prefix_append _ _

/-- Events of other clients do not change `cur c`, except an `inv`/`step` of `c` itself. -/
theorem cur_step_of_ne (X : A.Config) (e : Event C) (c : C)
    (h : ¬ ClientEv (fun _ => e) 0 c) : (A.step X e).cur c = X.cur c := by
  simp only [ClientEv, not_or, not_exists] at h
  rcases step_cases X e with h1 | h1 | ⟨c', op, rfl, hc, h1⟩ | ⟨c', op, o', r, l, rfl, hc, ha, h1⟩ |
    ⟨c', op, l, rfl, hc, ha, h1⟩ | ⟨c', m, p, rfl, hp, h1⟩ <;> rw [h1]
  · have : c ≠ c' := fun hh => h.2 op (by rw [hh])
    simp [Function.update_apply, this]
  · have : c ≠ c' := fun hh => h.1 (by rw [hh])
    simp [Function.update_apply, this]

end Alg

end Podc.ReliableStorageSpace

end
