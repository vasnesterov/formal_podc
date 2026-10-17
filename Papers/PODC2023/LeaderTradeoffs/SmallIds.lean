import Papers.PODC2023.LeaderTradeoffs.Model

/-!
# Leader election for small ID universes (Algorithm 1, Theorem 3.15)

Section 3.4.2 of Kutten, Robinson, Tan, Zhu, *Improved Tradeoffs for Leader Election* (PODC 2023).

IDs are drawn from `U = {1, …, n·g}` (`n = m + 1`). For a parameter `d ≥ 1`, the IDs are split
into blocks of `d·g` consecutive IDs: block `r` (0-indexed) is `[r·d·g + 1, (r+1)·d·g]`.
In round `r` (0-indexed; the paper's round `i = r + 1`), every undecided node whose ID lies in
block `r` sends its ID on all ports. A node that receives messages (or sends) in a round selects
the smallest ID among the received IDs and its own (if it sent) as the leader, and stops: it never
sends again (the paper's pseudocode leaves this implicit; without it, nodes of later blocks would
keep broadcasting and the message bound would fail, and later rounds would overwrite the selected
leader). The clause "or sends" matters only for `n = 1`, where the paper's literal rule (select
only upon receiving messages) never selects a leader. The paper's assumption `d ≤ n` is not
needed; `d ≥ 1` is.

Main results (for every `I ⊆ U` with `|I| = n` and every port map):
* `run_of_ge`: after `T = ⌈n/d⌉` rounds every node has selected `min I` (explicit leader election);
* `electsBy`, `terminatesBy`: exactly one leader, termination by round `⌈n/d⌉`;
* `msgs_le`, `msgBound`: at most `(n-1)·d·g ≤ n·d·g` messages in total.
-/

open Classical Finset

namespace LeaderTradeoffs

namespace SmallIds

variable (m g d : ℕ)

/-- The ID universe `{1, …, n·g}` with `n = m + 1`. -/
def U : Finset ℕ := Icc 1 ((m + 1) * g)

/-- The number of rounds `⌈n/d⌉` (with `n = m + 1`). -/
def T : ℕ := (m + 1 + d - 1) / d

/-- The block of an ID: `block x = r` iff `x ∈ [r·d·g + 1, (r+1)·d·g]` (see `block_eq_iff`). -/
def block (x : ℕ) : ℕ := (x - 1) / (d * g)

theorem block_eq_iff {x r : ℕ} (hx : 1 ≤ x) (hdg : 0 < d * g) :
    block g d x = r ↔ r * (d * g) + 1 ≤ x ∧ x ≤ (r + 1) * (d * g) := by
  unfold block
  constructor
  · rintro rfl
    have h1 := Nat.div_mul_le_self (x - 1) (d * g)
    have h2 := Nat.lt_mul_div_succ (x - 1) hdg
    constructor
    · omega
    · rw [Nat.add_mul, one_mul]
      rw [Nat.mul_add, mul_one, mul_comm] at h2
      omega
  · rintro ⟨h1, h2⟩
    rw [Nat.div_eq_iff hdg]
    constructor
    · omega
    · rw [Nat.add_mul, one_mul] at h2
      omega

/-- Local state: own ID, round counter, selected leader (if decided). -/
structure St where
  /-- own ID -/
  id : ℕ
  /-- number of rounds executed so far -/
  rd : ℕ
  /-- the selected leader ID (`none` while undecided) -/
  ldr : Option ℕ

/-- The set of IDs received on the ports. -/
noncomputable def recv (v : Fin m → Option ℕ) : Finset ℕ :=
  univ.biUnion fun j => (v j).toFinset

theorem mem_recv {v : Fin m → Option ℕ} {y : ℕ} : y ∈ recv m v ↔ ∃ j, v j = some y := by
  simp [recv]

/-- The candidates of a node in the current round: received IDs and, if it sent, its own ID. -/
noncomputable def cands (s : St) (v : Fin m → Option ℕ) : Finset ℕ :=
  recv m v ∪ if block g d s.id = s.rd then {s.id} else ∅

/-- **Algorithm 1** of the paper. -/
@[reducible] noncomputable def alg : Algorithm m where
  State := St
  Msg := ℕ
  init x := ⟨x, 0, none⟩
  send s _ := if s.ldr = none ∧ block g d s.id = s.rd then some s.id else none
  step s v := ⟨s.id, s.rd + 1,
    s.ldr.or (if h : (cands m g d s v).Nonempty then some ((cands m g d s v).min' h) else none)⟩
  output s := s.ldr.map fun l => decide (l = s.id)

variable {m g d}

@[simp] theorem alg_init (x : ℕ) : (alg m g d).init x = (⟨x, 0, none⟩ : St) := rfl

@[simp] theorem alg_send (s : St) (j : Fin m) : (alg m g d).send s j =
    if s.ldr = none ∧ block g d s.id = s.rd then some s.id else none := rfl

@[simp] theorem alg_step (s : St) (v : Fin m → Option ℕ) : (alg m g d).step s v =
    (⟨s.id, s.rd + 1, s.ldr.or (if h : (cands m g d s v).Nonempty then
      some ((cands m g d s v).min' h) else none)⟩ : St) := rfl

@[simp] theorem alg_output (s : St) :
    (alg m g d).output s = s.ldr.map fun l => decide (l = s.id) := rfl

theorem inbox_of {A : Algorithm m} {p : PortMap m} {I : Finset ℕ} (hp : WF p I) {u v : ℕ}
    (hu : u ∈ I) {j i : Fin m} (hj : p u j = some v) (hi : p v i = some u) (st : ℕ → A.State) :
    inbox A p st u j = A.send (st v) i := by
  have hv := hp.mem u hu j v hj
  simp [inbox, hj, backPort_eq hp hv hi]

theorem sendCount_eq (s : St) :
    sendCount (alg m g d) s = if s.ldr = none ∧ block g d s.id = s.rd then m else 0 := by
  unfold sendCount
  split_ifs with h
  · simp [alg, h]
  · simp [alg, h]

/-- The block of the minimum ID: the round (0-indexed) in which the leader is selected. -/
noncomputable def r₀ (g d : ℕ) (I : Finset ℕ) (h : I.Nonempty) : ℕ := block g d (I.min' h)

section Exec

set_option linter.unusedSectionVars false

variable {I : Finset ℕ} {p : PortMap m} (hIU : I ⊆ U m g) (hI : I.card = m + 1)
  (hp : IsPortMap p I)
include hIU hI hp

theorem nonempty : I.Nonempty := by
  rw [← Finset.card_pos, hI]; omega


theorem g_pos : 0 < g := by
  obtain ⟨x, hx⟩ := nonempty hIU hI hp
  have := Finset.mem_Icc.1 (hIU hx)
  rcases Nat.eq_zero_or_pos g with h | h
  · subst h; simp at this; omega
  · exact h

theorem one_le {x : ℕ} (hx : x ∈ I) : 1 ≤ x := (Finset.mem_Icc.1 (hIU hx)).1

theorem r₀_le {x : ℕ} (hx : x ∈ I) : r₀ g d I (nonempty hIU hI hp) ≤ block g d x := by
  unfold r₀ block
  apply Nat.div_le_div_right
  have := I.min'_le x hx
  omega

theorem run_pre :
    ∀ r ≤ r₀ g d I (nonempty hIU hI hp), ∀ u ∈ I, run (alg m g d) p r u = (⟨u, r, none⟩ : St) := by
  intro r
  induction r with
  | zero => intro _ u _; rfl
  | succ r ih =>
    intro hr u hu
    have hst : ∀ v ∈ I, run (alg m g d) p r v = (⟨v, r, none⟩ : St) :=
      fun v hv => ih (by omega) v hv
    have hin : ∀ j, inbox (alg m g d) p (run (alg m g d) p r) u j = none := by
      intro j
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hp.2 u hu j)
      obtain ⟨i, hi⟩ := hp.1.symm u hu j v hv
      rw [inbox_of hp.1 hu hv hi, hst v (hp.1.mem u hu j v hv)]
      have := r₀_le (d := d) hIU hI hp (hp.1.mem u hu j v hv)
      rw [alg_send, ite_eq_right (by rintro ⟨-, h⟩; dsimp only at h; omega)]
    have hc : cands m g d ⟨u, r, none⟩ (inbox (alg m g d) p (run (alg m g d) p r) u) = ∅ := by
      have := r₀_le (d := d) hIU hI hp hu
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      simp only [cands, Finset.mem_union, mem_recv, hin] at hy
      rcases hy with ⟨j, hj⟩ | hy
      · cases hj
      · rw [ite_eq_right (by omega)] at hy
        simp at hy
    show (alg m g d).step _ _ = _
    rw [hst u hu]
    dsimp only
    rw [hc]
    simp

theorem run_r₀ : ∀ u ∈ I, run (alg m g d) p (r₀ g d I (nonempty hIU hI hp) + 1) u =
    (⟨u, r₀ g d I (nonempty hIU hI hp) + 1, some (I.min' (nonempty hIU hI hp))⟩ : St) := by
  intro u hu
  set x₀ := I.min' (nonempty hIU hI hp) with hx₀
  have hx₀I : x₀ ∈ I := I.min'_mem _
  have hst : ∀ v ∈ I,
      run (alg m g d) p (r₀ g d I (nonempty hIU hI hp)) v =
        (⟨v, r₀ g d I (nonempty hIU hI hp), none⟩ : St) :=
    fun v hv => run_pre hIU hI hp _ le_rfl v hv
  set C := cands m g d ⟨u, r₀ g d I (nonempty hIU hI hp), none⟩
    (inbox (alg m g d) p (run (alg m g d) p (r₀ g d I (nonempty hIU hI hp))) u) with hC
  have hCI : C ⊆ I := by
    intro y hy
    simp only [hC, cands, Finset.mem_union, mem_recv] at hy
    rcases hy with ⟨j, hj⟩ | hy
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hp.2 u hu j)
      obtain ⟨i, hi⟩ := hp.1.symm u hu j v hv
      have hvI := hp.1.mem u hu j v hv
      rw [inbox_of hp.1 hu hv hi, hst v hvI] at hj
      dsimp only at hj
      split_ifs at hj
      cases hj
      exact hvI
    · split_ifs at hy
      · simp only [Finset.mem_singleton] at hy; subst hy; exact hu
      · simp at hy
  have hx₀C : x₀ ∈ C := by
    by_cases hux : x₀ = u
    · simp only [hC, cands, Finset.mem_union]
      right
      rw [ite_eq_left (by rw [← hux]; rfl)]
      simp [hux]
    · obtain ⟨j, hj⟩ := hp.surj hI hu hx₀I hux
      obtain ⟨i, hi⟩ := hp.1.symm u hu j x₀ hj
      simp only [hC, cands, Finset.mem_union, mem_recv]
      left
      refine ⟨j, ?_⟩
      rw [inbox_of hp.1 hu hj hi, hst x₀ hx₀I, alg_send]
      exact ite_eq_left ⟨rfl, rfl⟩
  have hmin : ∀ h : C.Nonempty, C.min' h = x₀ := by
    intro h
    apply le_antisymm (C.min'_le x₀ hx₀C)
    exact C.le_min' h x₀ fun y hy => I.min'_le y (hCI hy)
  show (alg m g d).step _ _ = _
  rw [hst u hu]
  dsimp only
  rw [← hC]
  have hne : C.Nonempty := ⟨x₀, hx₀C⟩
  simp [hne, hmin]

theorem run_post (t : ℕ) : ∀ u ∈ I, run (alg m g d) p (r₀ g d I (nonempty hIU hI hp) + 1 + t) u =
    (⟨u, r₀ g d I (nonempty hIU hI hp) + 1 + t, some (I.min' (nonempty hIU hI hp))⟩ : St) := by
  induction t with
  | zero => exact run_r₀ hIU hI hp
  | succ t ih =>
    intro u hu
    have e : r₀ g d I (nonempty hIU hI hp) + 1 + (t + 1) =
        (r₀ g d I (nonempty hIU hI hp) + 1 + t) + 1 := by omega
    rw [e, run, ih u hu]
    rfl

theorem r₀_lt (hd : 0 < d) : r₀ g d I (nonempty hIU hI hp) + 1 ≤ T m d := by
  have hx := hIU (I.min'_mem (nonempty hIU hI hp))
  rw [U, Finset.mem_Icc] at hx
  have hg : 0 < g := g_pos hIU hI hp
  unfold T r₀ block
  rw [Nat.le_div_iff_mul_le hd]
  have h1 := Nat.div_mul_le_self (I.min' (nonempty hIU hI hp) - 1) (d * g)
  set r := (I.min' (nonempty hIU hI hp) - 1) / (d * g)
  have h2 : r * d * g < (m + 1) * g := by rw [mul_assoc]; omega
  have h3 : r * d < m + 1 := Nat.lt_of_mul_lt_mul_right h2
  rw [Nat.add_mul, one_mul]
  omega

theorem run_of_ge (hd : 0 < d) {r : ℕ} (hr : T m d ≤ r) {u : ℕ} (hu : u ∈ I) :
    run (alg m g d) p r u = (⟨u, r, some (I.min' (nonempty hIU hI hp))⟩ : St) := by
  have := r₀_lt hIU hI hp hd
  obtain ⟨t, rfl⟩ : ∃ t, r = r₀ g d I (nonempty hIU hI hp) + 1 + t :=
    ⟨r - (r₀ g d I (nonempty hIU hI hp) + 1), by omega⟩
  exact run_post hIU hI hp t u hu

/-- Explicit leader election: after `⌈n/d⌉` rounds every node has selected the minimum ID as the
leader, and outputs "leader" iff it is the node with the minimum ID. -/
theorem selects_min (hd : 0 < d) {r : ℕ} (hr : T m d ≤ r) {u : ℕ} (hu : u ∈ I) :
    St.ldr (run (alg m g d) p r u) = some (I.min' (nonempty hIU hI hp)) ∧
      (alg m g d).output (run (alg m g d) p r u) =
        some (decide (u = I.min' (nonempty hIU hI hp))) := by
  rw [run_of_ge hIU hI hp hd hr hu]
  refine ⟨rfl, ?_⟩
  simp only [Option.map_some]
  congr 1
  exact decide_eq_decide.2 eq_comm

theorem roundMsgs_eq (r : ℕ) : roundMsgs (alg m g d) p r I =
    if r = r₀ g d I (nonempty hIU hI hp) then
      m * (I.filter fun x => block g d x = r₀ g d I (nonempty hIU hI hp)).card else 0 := by
  unfold roundMsgs
  rcases lt_trichotomy r (r₀ g d I (nonempty hIU hI hp)) with h | h | h
  · rw [ite_eq_right h.ne]
    apply Finset.sum_eq_zero
    intro u hu
    rw [run_pre hIU hI hp r h.le u hu, sendCount_eq]
    have := r₀_le (d := d) hIU hI hp hu
    rw [ite_eq_right (by simp only [not_and]; intro _; omega)]
  · subst h
    rw [ite_eq_left rfl, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [run_pre hIU hI hp _ le_rfl u hu, sendCount_eq]
    simp only [true_and]
    split_ifs <;> simp
  · rw [ite_eq_right h.ne']
    apply Finset.sum_eq_zero
    intro u hu
    obtain ⟨t, rfl⟩ : ∃ t, r = r₀ g d I (nonempty hIU hI hp) + 1 + t :=
    ⟨r - (r₀ g d I (nonempty hIU hI hp) + 1), by omega⟩
    rw [run_post hIU hI hp t u hu, sendCount_eq]
    simp

theorem card_block_le (hd : 0 < d) :
    (I.filter fun x => block g d x = r₀ g d I (nonempty hIU hI hp)).card ≤ d * g := by
  have hx := hIU (I.min'_mem (nonempty hIU hI hp))
  rw [U, Finset.mem_Icc] at hx
  have hg : 0 < g := g_pos hIU hI hp
  have hdg : 0 < d * g := Nat.mul_pos hd hg
  set r := r₀ g d I (nonempty hIU hI hp)
  calc (I.filter fun x => block g d x = r).card
      ≤ (Icc (r * (d * g) + 1) ((r + 1) * (d * g))).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_Icc]
        exact (block_eq_iff g d (one_le hIU hI hp hx.1) hdg).1 hx.2
    _ = d * g := by
        rw [Nat.card_Icc, Nat.add_mul, one_mul]
        omega

/-- The message complexity of Algorithm 1 over any number of rounds: only the nodes of the first
nonempty block ever send, each on its `n - 1` ports. -/
theorem msgs_le (hd : 0 < d) (T' : ℕ) : msgs (alg m g d) p T' I ≤ m * (d * g) := by
  unfold msgs
  simp_rw [roundMsgs_eq hIU hI hp]
  rw [Finset.sum_ite_eq']
  split_ifs
  · exact Nat.mul_le_mul_left _ (card_block_le hIU hI hp hd)
  · exact Nat.zero_le _

end Exec

/-- **Theorem 3.15** (correctness): Algorithm 1 elects exactly one leader (the minimum ID) within
`⌈n/d⌉` rounds, for every ID assignment from `{1, …, n·g}` and every port map. -/
theorem electsBy (hd : 0 < d) : ElectsBy (alg m g d) (U m g) (T m d) := by
  intro I hIU hI p hp
  rw [Finset.card_eq_one]
  refine ⟨I.min' (nonempty hIU hI hp), ?_⟩
  have key : ∀ u ∈ I, (alg m g d).output (run (alg m g d) p (T m d) u) =
      some (decide (u = I.min' (nonempty hIU hI hp))) :=
    fun u hu => (selects_min hIU hI hp hd le_rfl hu).2
  ext u
  rw [leaders, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hu, h⟩
    rw [key u hu] at h
    simpa using h
  · rintro rfl
    exact ⟨I.min'_mem _, by rw [key _ (I.min'_mem _)]; simp⟩

/-- **Theorem 3.15** (time): Algorithm 1 terminates within `⌈n/d⌉` rounds. -/
theorem terminatesBy (hd : 0 < d) : TerminatesBy (alg m g d) (U m g) (T m d) := by
  intro I hIU hI p hp u hu
  refine ⟨by rw [(selects_min hIU hI hp hd le_rfl hu).2]; rfl, fun r hr => ⟨?_, ?_⟩⟩
  · rw [(selects_min hIU hI hp hd le_rfl hu).2, (selects_min hIU hI hp hd hr hu).2]
  · rw [run_of_ge hIU hI hp hd hr hu, sendCount_eq]
    simp

/-- **Theorem 3.15** (messages): Algorithm 1 sends at most `(n - 1)·d·g` messages. -/
theorem msgBound' (hd : 0 < d) : MsgBound (alg m g d) (U m g) (T m d) (m * d * g) := by
  intro I hIU hI p hp
  have := msgs_le hIU hI hp hd (T m d)
  rw [mul_assoc]
  exact_mod_cast this

/-- **Theorem 3.15** (messages, as stated in the paper): at most `n·d·g` messages. -/
theorem msgBound (hd : 0 < d) : MsgBound (alg m g d) (U m g) (T m d) ((m + 1) * d * g) := by
  intro I hIU hI p hp
  refine (msgBound' hd I hIU hI p hp).trans ?_
  have : (m : ℝ) * d * g ≤ (m + 1) * d * g := by
    gcongr; linarith
  exact_mod_cast this

end SmallIds

end LeaderTradeoffs
