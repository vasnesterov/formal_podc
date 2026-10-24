import Papers.PODC2017.ZigzagCausality.Model

/-!
# Basic facts about runs of the bounded communication model

Local states only grow (`hist_prefix`), a process is activated exactly when a nonempty batch is
delivered, `timer` is the activation time of a node, messages are received within their bounds
(`recv_spec`), message chains of general nodes satisfy the bounds of their paths
(`gbasic_timer_le`, `le_gbasic_timer`), and happens-before respects time (`HB.timer_le`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

theorem LState.ext' {ℓ ℓ' : LState P S M E} (h1 : ℓ.init = ℓ'.init) (h2 : ℓ.hist = ℓ'.hist) :
    ℓ = ℓ' := by
  cases ℓ; cases ℓ'; simp_all

theorem Batch.ext' {b b' : Batch P M E} (h1 : b.msgs = b'.msgs) (h2 : b.ext = b'.ext) :
    b = b' := by
  cases b; cases b'; simp_all

@[simp] theorem lastP_nil (i : P) : lastP i [] = i := rfl

@[simp] theorem lastP_cons (i j : P) (q : List P) : lastP i (j :: q) = lastP j q := by
  simp [lastP, List.getLast_cons]

theorem lastP_append (i : P) (q q' : List P) : lastP i (q ++ q') = lastP (lastP i q) q' := by
  induction q generalizing i with
  | nil => simp
  | cons j q ih => simp [ih]

@[simp] theorem lastP_concat (i : P) (q : List P) (j : P) : lastP i (q ++ [j]) = j := by
  simp [lastP_append]

namespace Net

variable (N : Net P)

@[simp] theorem Lp_nil (i : P) : N.Lp i [] = 0 := rfl
@[simp] theorem Up_nil (i : P) : N.Up i [] = 0 := rfl
@[simp] theorem Lp_cons (i j : P) (q : List P) : N.Lp i (j :: q) = N.L i j + N.Lp j q := rfl
@[simp] theorem Up_cons (i j : P) (q : List P) : N.Up i (j :: q) = N.U i j + N.Up j q := rfl

theorem Lp_append (i : P) (q q' : List P) : N.Lp i (q ++ q') = N.Lp i q + N.Lp (lastP i q) q' := by
  induction q generalizing i with
  | nil => simp
  | cons j q ih => simp [ih]; omega

theorem Up_append (i : P) (q q' : List P) : N.Up i (q ++ q') = N.Up i q + N.Up (lastP i q) q' := by
  induction q generalizing i with
  | nil => simp
  | cons j q ih => simp [ih]; omega

end Net

@[simp] theorem GNode.ext_root (θ : GNode P S M E) (q : List P) : (θ.ext q).root = θ.root := rfl
@[simp] theorem GNode.ext_path (θ : GNode P S M E) (q : List P) : (θ.ext q).path = θ.path ++ q :=
  rfl
@[simp] theorem GNode.ext_nil (θ : GNode P S M E) : θ.ext [] = θ := by
  cases θ; simp [GNode.ext]
theorem GNode.ext_ext (θ : GNode P S M E) (q q' : List P) : (θ.ext q).ext q' = θ.ext (q ++ q') := by
  simp [GNode.ext]
theorem GNode.proc_ext (θ : GNode P S M E) (q : List P) : (θ.ext q).proc = lastP θ.proc q := by
  simp [GNode.proc, GNode.ext, lastP_append]

namespace Sys

variable (γ : Sys P S M E) (r : Sched P S E) [Finite P]

/-! ### Evolution of local states -/

theorem step_eq (ℓ : LState P S M E) (b : Batch P M E) :
    ℓ.step b = if b.msgs = ∅ ∧ b.ext = ∅ then ℓ else ⟨ℓ.init, ℓ.hist ++ [b]⟩ := rfl

@[simp] theorem st_init (t : ℕ) (i : P) : (γ.st r t i).init = r.g i := by
  induction t with
  | zero => rfl
  | succ t ih => rw [st_succ, step_eq]; split_ifs <;> simp [ih]

theorem active_succ_iff (t : ℕ) (i : P) :
    γ.Active r i (t + 1) ↔ ¬ ((γ.batch r t i).msgs = ∅ ∧ (γ.batch r t i).ext = ∅) := by
  simp only [Active, ActiveH, Nat.add_sub_cancel, st_succ, step_eq]
  split_ifs with h
  · simp [h]
  · simp only [h, not_false_eq_true, iff_true]
    refine ⟨by omega, fun he => ?_⟩
    have := congrArg (fun ℓ => ℓ.hist.length) he
    simp at this

theorem st_succ_of_active {t : ℕ} {i : P} (h : γ.Active r i (t + 1)) :
    γ.st r (t + 1) i = ⟨r.g i, (γ.st r t i).hist ++ [γ.batch r t i]⟩ := by
  rw [active_succ_iff] at h
  rw [st_succ, step_eq, if_neg h, st_init]

theorem st_succ_of_not_active {t : ℕ} {i : P} (h : ¬ γ.Active r i (t + 1)) :
    γ.st r (t + 1) i = γ.st r t i := by
  rw [active_succ_iff, not_not] at h
  rw [st_succ, step_eq, if_pos h]

theorem hist_prefix_succ (t : ℕ) (i : P) : (γ.st r t i).hist <+: (γ.st r (t + 1) i).hist := by
  by_cases h : γ.Active r i (t + 1)
  · rw [γ.st_succ_of_active r h]; exact List.prefix_append _ _
  · rw [γ.st_succ_of_not_active r h]

theorem hist_prefix {t t' : ℕ} (h : t ≤ t') (i : P) :
    (γ.st r t i).hist <+: (γ.st r t' i).hist := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (γ.hist_prefix_succ r _ i)

theorem length_succ (t : ℕ) (i : P) :
    (γ.st r (t + 1) i).hist.length =
      (γ.st r t i).hist.length + if γ.Active r i (t + 1) then 1 else 0 := by
  by_cases h : γ.Active r i (t + 1)
  · rw [γ.st_succ_of_active r h, if_pos h]; simp
  · rw [γ.st_succ_of_not_active r h, if_neg h]; simp

theorem length_mono {t t' : ℕ} (h : t ≤ t') (i : P) :
    (γ.st r t i).hist.length ≤ (γ.st r t' i).hist.length :=
  (γ.hist_prefix r h i).length_le

theorem length_le_time (t : ℕ) (i : P) : (γ.st r t i).hist.length ≤ t := by
  induction t with
  | zero => simp [st_zero]
  | succ t ih => rw [length_succ]; split_ifs <;> omega

theorem st_eq_iff_length {t t' : ℕ} {i : P} :
    γ.st r t i = γ.st r t' i ↔ (γ.st r t i).hist.length = (γ.st r t' i).hist.length := by
  refine ⟨fun h => by rw [h], fun h => LState.ext' (by simp) ?_⟩
  rcases le_total t t' with htt | htt
  · exact (γ.hist_prefix r htt i).eq_of_length h
  · exact ((γ.hist_prefix r htt i).eq_of_length h.symm).symm

theorem active_iff_length (s : ℕ) (i : P) :
    γ.Active r i s ↔ 0 < s ∧ (γ.st r (s - 1) i).hist.length < (γ.st r s i).hist.length := by
  rcases s with _ | s
  · simp [Active, ActiveH]
  · simp only [Nat.add_sub_cancel, Nat.succ_pos, true_and]
    rw [length_succ]
    split_ifs with h <;> simp [h]

theorem length_lt_of_active {t t' : ℕ} {i : P} (h : γ.Active r i t') (htt : t < t') :
    (γ.st r t i).hist.length < (γ.st r t' i).hist.length := by
  rw [active_iff_length] at h
  exact lt_of_le_of_lt (γ.length_mono r (by omega) i) h.2

theorem st_ne_of_active {t t' : ℕ} {i : P} (h : γ.Active r i t') (htt : t < t') :
    γ.st r t i ≠ γ.st r t' i := by
  intro he
  have := γ.length_lt_of_active r h htt
  rw [he] at this
  exact lt_irrefl _ this

/-- Between two times with equal local states the local state is constant. -/
theorem st_eq_of_between {t t' t'' : ℕ} {i : P} (h1 : t ≤ t'') (h2 : t'' ≤ t')
    (he : γ.st r t i = γ.st r t' i) : γ.st r t'' i = γ.st r t i := by
  rw [st_eq_iff_length] at he ⊢
  have := γ.length_mono r h1 i
  have := γ.length_mono r h2 i
  omega

/-- Every intermediate history length is attained. -/
theorem exists_length_eq {t k : ℕ} {i : P} (hk : k ≤ (γ.st r t i).hist.length) :
    ∃ t' ≤ t, (γ.st r t' i).hist.length = k := by
  induction t with
  | zero => exact ⟨0, le_rfl, by simp [st_zero] at hk ⊢; omega⟩
  | succ t ih =>
    rw [length_succ] at hk
    by_cases hk' : k ≤ (γ.st r t i).hist.length
    · obtain ⟨t', ht', h⟩ := ih hk'
      exact ⟨t', by omega, h⟩
    · refine ⟨t + 1, le_rfl, ?_⟩
      rw [length_succ]; split_ifs at hk ⊢ <;> omega

/-! ### Appearance and `timer` -/

theorem appears_st (t : ℕ) (i : P) : γ.appears r (i, γ.st r t i) := ⟨t, rfl⟩

theorem st_timer {σ : BNode P S M E} (h : γ.appears r σ) : γ.st r (γ.timer r σ) σ.1 = σ.2 := by
  rw [timer, dif_pos h]; exact Nat.find_spec h

theorem timer_le {σ : BNode P S M E} {t : ℕ} (h : γ.st r t σ.1 = σ.2) : γ.timer r σ ≤ t := by
  have ha : γ.appears r σ := ⟨t, h⟩
  rw [timer, dif_pos ha]; exact Nat.find_min' ha h

theorem timer_st_le (t : ℕ) (i : P) : γ.timer r (i, γ.st r t i) ≤ t := γ.timer_le r rfl

theorem not_appears_timer {σ : BNode P S M E} (h : ¬ γ.appears r σ) : γ.timer r σ = 0 := by
  rw [timer, dif_neg h]

/-- The state of a node holds from its `timer` up to any later time at which it is observed. -/
theorem st_eq_of_timer_le {σ : BNode P S M E} {t t' : ℕ} (h : γ.appears r σ)
    (h1 : γ.timer r σ ≤ t) (h2 : t ≤ t') (h' : γ.st r t' σ.1 = σ.2) : γ.st r t σ.1 = σ.2 := by
  rw [γ.st_eq_of_between r h1 h2 ((γ.st_timer r h).trans h'.symm), γ.st_timer r h]

theorem timer_eq_of_active {i : P} {t : ℕ} (h : γ.Active r i t) : γ.timer r (i, γ.st r t i) = t := by
  refine le_antisymm (γ.timer_st_le r t i) ?_
  by_contra hlt
  push_neg at hlt
  exact γ.st_ne_of_active r h hlt (γ.st_timer r (γ.appears_st r t i))

theorem active_timer {σ : BNode P S M E} (h : γ.appears r σ) (h0 : 0 < γ.timer r σ) :
    γ.Active r σ.1 (γ.timer r σ) := by
  refine ⟨h0, fun he => ?_⟩
  have := γ.timer_le r (he.symm.trans (γ.st_timer r h))
  omega

theorem timer_pos_iff {σ : BNode P S M E} (h : γ.appears r σ) :
    0 < γ.timer r σ ↔ σ.2.hist ≠ [] := by
  constructor
  · intro h0 hnil
    have ha := γ.active_timer r h h0
    have := γ.length_lt_of_active r ha (show 0 < γ.timer r σ from h0)
    rw [γ.st_timer r h, hnil] at this
    simp at this
  · intro hne
    by_contra h0
    push_neg at h0
    have : γ.timer r σ = 0 := by omega
    have hs := γ.st_timer r h
    rw [this, st_zero] at hs
    exact hne (by rw [← hs])

theorem eq_of_timer_eq {σ σ' : BNode P S M E} (hp : σ.1 = σ'.1) (h : γ.appears r σ)
    (h' : γ.appears r σ') (ht : γ.timer r σ = γ.timer r σ') : σ = σ' := by
  have e1 := γ.st_timer r h
  have e2 := γ.st_timer r h'
  rw [← ht, ← hp] at e2
  exact Prod.ext hp (e1.symm.trans e2)

theorem timer_lt_of_ne {σ σ' : BNode P S M E} (hp : σ.1 = σ'.1) (h : γ.appears r σ)
    (h' : γ.appears r σ') (hle : γ.timer r σ ≤ γ.timer r σ') (hne : σ ≠ σ') :
    γ.timer r σ < γ.timer r σ' :=
  lt_of_le_of_ne hle fun he => hne (γ.eq_of_timer_eq r hp h h' he)

/-- Nodes of the same process are ordered by `timer` exactly as their histories by prefix. -/
theorem timer_le_iff_prefix {σ σ' : BNode P S M E} (hp : σ.1 = σ'.1) (h : γ.appears r σ)
    (h' : γ.appears r σ') : γ.timer r σ ≤ γ.timer r σ' ↔ σ.2.hist <+: σ'.2.hist := by
  have e1 := γ.st_timer r h
  have e2 := γ.st_timer r h'
  rw [← hp] at e2
  constructor
  · intro hle; rw [← e1, ← e2]; exact γ.hist_prefix r hle _
  · intro hpre
    by_contra hlt
    push_neg at hlt
    have hpre' := γ.hist_prefix r hlt.le σ.1
    rw [e1, e2] at hpre'
    have heq : σ'.2.hist = σ.2.hist := hpre'.eq_of_length (le_antisymm hpre'.length_le hpre.length_le)
    have h2 : σ.2 = σ'.2 := LState.ext' (by rw [← e1, ← e2]; simp) heq.symm
    have : σ = σ' := Prod.ext hp h2
    subst this
    exact lt_irrefl _ hlt

theorem timer_mono {t t' : ℕ} (h : t ≤ t') (i : P) :
    γ.timer r (i, γ.st r t i) ≤ γ.timer r (i, γ.st r t' i) :=
  (γ.timer_le_iff_prefix r (σ := (i, γ.st r t i)) (σ' := (i, γ.st r t' i)) rfl
    (γ.appears_st r t i) (γ.appears_st r t' i)).2
    (γ.hist_prefix r h i)

/-- Every prefix of a local state that appears also appears, not later. -/
theorem appears_take {i : P} {ℓ : LState P S M E} (h : γ.appears r (i, ℓ)) (k : ℕ) :
    γ.appears r (i, ⟨ℓ.init, ℓ.hist.take k⟩) ∧
      γ.timer r (i, ⟨ℓ.init, ℓ.hist.take k⟩) ≤ γ.timer r (i, ℓ) := by
  obtain ⟨t, ht⟩ := h
  simp only at ht
  have hk : min k ℓ.hist.length ≤ (γ.st r t i).hist.length := by rw [ht]; exact min_le_right _ _
  obtain ⟨t', ht', hl⟩ := γ.exists_length_eq r hk
  have he : γ.st r t' i = ⟨ℓ.init, ℓ.hist.take k⟩ := by
    refine LState.ext' (by simp [← ht]) ?_
    have hpre := γ.hist_prefix r ht' i
    rw [ht] at hpre
    obtain ⟨u, hu⟩ := hpre
    have : (γ.st r t' i).hist = ℓ.hist.take (γ.st r t' i).hist.length := by
      rw [← hu]; simp
    rw [this, hl]
    rcases le_total k ℓ.hist.length with hk | hk
    · simp [min_eq_left hk]
    · simp [min_eq_right hk, List.take_of_length_le hk]
  refine ⟨⟨t', he⟩, ?_⟩
  have := γ.timer_mono r ht' i
  rw [he, ht] at this
  exact this

/-! ### Messages -/

theorem sends_timer {σ : BNode P S M E} {j : P} (h : γ.Sends r σ.1 (γ.timer r σ) j) :
    γ.appears r σ ∧ 0 < γ.timer r σ := by
  have h0 := h.1.1
  by_cases ha : γ.appears r σ
  · exact ⟨ha, h0⟩
  · rw [γ.not_appears_timer r ha] at h0; exact absurd h0 (lt_irrefl _)

theorem recv_eq_some {σ σ' : BNode P S M E} {j : P} :
    γ.recv r σ j = some σ' ↔
      γ.Sends r σ.1 (γ.timer r σ) j ∧ σ' = (j, γ.st r (r.dlv σ.1 (γ.timer r σ) j) j) := by
  unfold recv
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem recv_isSome_iff {σ : BNode P S M E} {j : P} :
    (γ.recv r σ j).isSome ↔ γ.Sends r σ.1 (γ.timer r σ) j := by
  unfold recv; split_ifs with h <;> simp [h]

/-- The local state of a node created at time `t > 0` is its predecessor's state followed by the
batch delivered at `t`. -/
theorem hist_of_timer_pos {σ : BNode P S M E} (h : γ.appears r σ) (h0 : 0 < γ.timer r σ) :
    σ.2.hist = (γ.st r (γ.timer r σ - 1) σ.1).hist ++ [γ.batch r (γ.timer r σ - 1) σ.1] := by
  have ha := γ.active_timer r h h0
  obtain ⟨t, ht⟩ : ∃ t, γ.timer r σ = t + 1 := ⟨γ.timer r σ - 1, by omega⟩
  rw [ht] at ha ⊢
  rw [← γ.st_timer r h, ht, γ.st_succ_of_active r ha]
  simp

variable {γ r}

theorem dlv_spec (hr : γ.Valid r) {i j : P} {s : ℕ} (h : γ.Sends r i s j) :
    s < r.dlv i s j ∧ s + γ.net.L i j ≤ r.dlv i s j ∧ r.dlv i s j ≤ s + γ.net.U i j := by
  have hb := hr.bounds i s j h
  have := γ.net.one_le_L i j h.2.1
  exact ⟨by omega, hb.1, hb.2⟩
  
/-- A sent message is in the batch delivered at its delivery time, and the receiver is activated. -/
theorem mem_batch_of_sends (hr : γ.Valid r) {i j : P} {s : ℕ} (h : γ.Sends r i s j) :
    ∃ m, γ.send i (γ.st r s i) j = some m ∧
      (i, m) ∈ (γ.batch r (r.dlv i s j - 1) j).msgs ∧ γ.Active r j (r.dlv i s j) := by
  obtain ⟨hlt, -, -⟩ := dlv_spec hr h
  obtain ⟨ha, hc, hm⟩ := h
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hm
  have hmem : (i, m) ∈ (γ.batch r (r.dlv i s j - 1) j).msgs := by
    rw [mem_batch_msgs]
    exact ⟨s, by omega, ha, hc, by omega, hm⟩
  refine ⟨m, hm, hmem, ?_⟩
  obtain ⟨d, hd⟩ : ∃ d, r.dlv i s j = d + 1 := ⟨r.dlv i s j - 1, by omega⟩
  rw [hd] at hmem ⊢
  rw [active_succ_iff]
  rintro ⟨he, -⟩
  simp only [Nat.add_sub_cancel] at hmem
  rw [he] at hmem
  simp at hmem

/-- Properties of message delivery in a run (bounds `[L, U]`). -/
theorem recv_spec (hr : γ.Valid r) {σ σ' : BNode P S M E} {j : P} (h : γ.recv r σ j = some σ') :
    σ'.1 = j ∧ γ.appears r σ' ∧ γ.net.Chan σ.1 j ∧
      γ.timer r σ' = r.dlv σ.1 (γ.timer r σ) j ∧
      γ.timer r σ + γ.net.L σ.1 j ≤ γ.timer r σ' ∧ γ.timer r σ' ≤ γ.timer r σ + γ.net.U σ.1 j := by
  rw [recv_eq_some] at h
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨_, -, -, hact⟩ := mem_batch_of_sends hr hs
  have ht := γ.timer_eq_of_active r hact
  obtain ⟨-, h1, h2⟩ := dlv_spec hr hs
  exact ⟨rfl, γ.appears_st r _ _, hs.2.1, ht, by rw [ht]; exact h1, by rw [ht]; exact h2⟩

theorem recv_appears_left {σ σ' : BNode P S M E} {j : P} (h : γ.recv r σ j = some σ') :
    γ.appears r σ ∧ 0 < γ.timer r σ :=
  γ.sends_timer r ((γ.recv_eq_some r).1 h).1

/-- The message received at `σ'` from `σ` is in the last batch of `σ'`. -/
theorem recv_mem_last (hr : γ.Valid r) {σ σ' : BNode P S M E} {j : P}
    (h : γ.recv r σ j = some σ') : ∃ m, γ.send σ.1 σ.2 j = some m ∧ ∃ b,
      σ'.2.hist.getLast? = some b ∧ (σ.1, m) ∈ b.msgs := by
  have hspec := recv_spec hr h
  obtain ⟨hs, rfl⟩ := (γ.recv_eq_some r).1 h
  obtain ⟨hap, h0⟩ := γ.sends_timer r hs
  obtain ⟨m, hm, hmem, hact⟩ := mem_batch_of_sends hr hs
  rw [γ.st_timer r hap] at hm
  refine ⟨m, hm, _, ?_, hmem⟩
  have hpos : 0 < r.dlv σ.1 (γ.timer r σ) j := hact.1
  have := γ.hist_of_timer_pos r (σ := (j, γ.st r (r.dlv σ.1 (γ.timer r σ) j) j))
    (γ.appears_st r _ _) (by rw [hspec.2.2.2.1]; exact hpos)
  rw [hspec.2.2.2.1] at this
  simp only at this
  rw [this]
  simp

/-- Conversely, every internal message in the last batch of a node was sent to it. -/
theorem exists_recv_of_mem_last (hr : γ.Valid r) {σ' : BNode P S M E} (h : γ.appears r σ')
    {b : Batch P M E} (hb : σ'.2.hist.getLast? = some b) {i : P} {m : M} (hm : (i, m) ∈ b.msgs) :
    ∃ σ : BNode P S M E, σ.1 = i ∧ γ.recv r σ σ'.1 = some σ' ∧ γ.send i σ.2 σ'.1 = some m := by
  have h0 : 0 < γ.timer r σ' := by
    rw [γ.timer_pos_iff r h]; rintro hnil; rw [hnil] at hb; simp at hb
  have hh := γ.hist_of_timer_pos r h h0
  rw [hh] at hb
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at hb
  subst hb
  rw [mem_batch_msgs] at hm
  obtain ⟨s, hs, ha, hc, hd, hm⟩ := hm
  have hd' : r.dlv i s σ'.1 = γ.timer r σ' := by omega
  refine ⟨(i, γ.st r s i), rfl, ?_, hm⟩
  rw [recv_eq_some]
  have ht := γ.timer_eq_of_active r ha
  simp only [ht]
  refine ⟨⟨ha, hc, by rw [hm]; rfl⟩, ?_⟩
  rw [hd', γ.st_timer r h]

/-! ### General nodes -/

variable (γ r)

@[simp] theorem gbasic_nil (σ : BNode P S M E) :
    γ.gbasic r σ [] = if γ.appears r σ then some σ else none := rfl

@[simp] theorem gbasic_cons (σ : BNode P S M E) (j : P) (q : List P) :
    γ.gbasic r σ (j :: q) = (γ.recv r σ j).bind fun σ' => γ.gbasic r σ' q := rfl

theorem gbasic_appears {σ τ : BNode P S M E} {q : List P} (h : γ.gbasic r σ q = some τ) :
    γ.appears r σ ∧ γ.appears r τ := by
  induction q generalizing σ with
  | nil =>
    simp only [gbasic_nil] at h
    split_ifs at h with ha
    cases h; exact ⟨ha, ha⟩
  | cons j q ih =>
    simp only [gbasic_cons] at h
    obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact ⟨(recv_appears_left h1).1, (ih h2).2⟩

theorem gbasic_proc {σ τ : BNode P S M E} {q : List P} (h : γ.gbasic r σ q = some τ) :
    τ.1 = lastP σ.1 q := by
  induction q generalizing σ with
  | nil =>
    simp only [gbasic_nil] at h
    split_ifs at h; cases h; rfl
  | cons j q ih =>
    simp only [gbasic_cons] at h
    obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rw [ih h2, lastP_cons, ((γ.recv_eq_some r).1 h1).2]

theorem gbasic_append (σ : BNode P S M E) (q q' : List P) :
    γ.gbasic r σ (q ++ q') = (γ.gbasic r σ q).bind fun τ => γ.gbasic r τ q' := by
  induction q generalizing σ with
  | nil =>
    simp only [List.nil_append, gbasic_nil]
    split_ifs with ha
    · rfl
    · simp only [Option.bind_none]
      cases q' with
      | nil => simp [ha]
      | cons j q' =>
        simp only [gbasic_cons]
        have : γ.recv r σ j = none := by
          rcases hh : γ.recv r σ j with _ | σ'
          · rfl
          · exact absurd (recv_appears_left hh).1 ha
        rw [this]; rfl
  | cons j q ih =>
    simp only [List.cons_append, gbasic_cons, ih, Option.bind_assoc]

theorem gbasic_self {σ : BNode P S M E} (h : γ.appears r σ) : γ.gbasic r σ [] = some σ := by
  simp [h]

theorem basic_ext (θ : GNode P S M E) (q : List P) :
    γ.basic r (θ.ext q) = (γ.basic r θ).bind fun τ => γ.gbasic r τ q := by
  simp [basic, GNode.ext, gbasic_append]

theorem basic_ofB {σ : BNode P S M E} (h : γ.appears r σ) : γ.basic r (GNode.ofB σ) = some σ :=
  γ.gbasic_self r h

theorem basic_proc {θ : GNode P S M E} {τ : BNode P S M E} (h : γ.basic r θ = some τ) :
    τ.1 = θ.proc := γ.gbasic_proc r h

theorem timerG_of_basic {θ : GNode P S M E} {τ : BNode P S M E} (h : γ.basic r θ = some τ) :
    γ.timerG r θ = γ.timer r τ := by
  simp [timerG, h]

variable {γ r}

/-- The message chain from `σ` along `q` satisfies the bounds of the path. -/
theorem gbasic_timer (hr : γ.Valid r) {σ τ : BNode P S M E} {q : List P}
    (h : γ.gbasic r σ q = some τ) :
    γ.timer r σ + γ.net.Lp σ.1 q ≤ γ.timer r τ ∧ γ.timer r τ ≤ γ.timer r σ + γ.net.Up σ.1 q := by
  induction q generalizing σ with
  | nil =>
    simp only [gbasic_nil] at h
    split_ifs at h; cases h; simp
  | cons j q ih =>
    simp only [gbasic_cons] at h
    obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have hs := recv_spec hr h1
    have := ih h2
    rw [hs.1] at this
    simp only [Net.Lp_cons, Net.Up_cons]
    omega

/-! ### Happens-before -/

theorem HB.appears {σ σ' : BNode P S M E} (h : γ.HB r σ σ') :
    γ.appears r σ ∧ γ.appears r σ' := by
  have step : ∀ a b, γ.HBStep r a b → γ.appears r a ∧ γ.appears r b := by
    rintro a b (⟨h1, h2, -⟩ | ⟨j, hj⟩)
    · exact ⟨h1, h2⟩
    · exact ⟨(recv_appears_left hj).1, (γ.recv_eq_some r).1 hj |>.2 ▸ γ.appears_st r _ _⟩
  induction h with
  | single hab => exact step _ _ hab
  | tail _ hbc ih => exact ⟨ih.1, (step _ _ hbc).2⟩

theorem HB.refl {σ : BNode P S M E} (h : γ.appears r σ) : γ.HB r σ σ :=
  Relation.TransGen.single (Or.inl ⟨h, h, rfl, le_rfl⟩)

theorem HB.trans {σ σ' σ'' : BNode P S M E} (h : γ.HB r σ σ') (h' : γ.HB r σ' σ'') :
    γ.HB r σ σ'' := Relation.TransGen.trans h h'

theorem HB.of_recv {σ σ' : BNode P S M E} {j : P} (h : γ.recv r σ j = some σ') : γ.HB r σ σ' :=
  Relation.TransGen.single (Or.inr ⟨j, h⟩)

theorem HB.of_local {σ σ' : BNode P S M E} (h : γ.appears r σ) (h' : γ.appears r σ')
    (hp : σ.1 = σ'.1) (ht : γ.timer r σ ≤ γ.timer r σ') : γ.HB r σ σ' :=
  Relation.TransGen.single (Or.inl ⟨h, h', hp, ht⟩)

theorem HB.timer_le (hr : γ.Valid r) {σ σ' : BNode P S M E} (h : γ.HB r σ σ') :
    γ.timer r σ ≤ γ.timer r σ' := by
  have step : ∀ a b, γ.HBStep r a b → γ.timer r a ≤ γ.timer r b := by
    rintro a b (⟨-, -, -, h⟩ | ⟨j, hj⟩)
    · exact h
    · have := recv_spec hr hj; omega
  induction h with
  | single hab => exact step _ _ hab
  | tail _ hbc ih => exact ih.trans (step _ _ hbc)

theorem HB.of_gbasic {σ τ : BNode P S M E} {q : List P} (h : γ.gbasic r σ q = some τ) :
    γ.HB r σ τ := by
  induction q generalizing σ with
  | nil =>
    simp only [gbasic_nil] at h
    split_ifs at h with ha; cases h; exact HB.refl ha
  | cons j q ih =>
    simp only [gbasic_cons] at h
    obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (HB.of_recv h1).trans (ih h2)

/-- In a flooding protocol every non-initial node sends to all its out-neighbours. -/
theorem recv_isSome_of_FFIP (hF : γ.IsFFIP) {σ : BNode P S M E} (h : γ.appears r σ)
    (h0 : 0 < γ.timer r σ) {j : P} (hc : γ.net.Chan σ.1 j) : (γ.recv r σ j).isSome := by
  rw [recv_isSome_iff]
  refine ⟨γ.active_timer r h h0, hc, ?_⟩
  rw [γ.st_timer r h]
  exact hF.2 _ _ _ hc

end Sys

end Podc.ZigzagCausality
