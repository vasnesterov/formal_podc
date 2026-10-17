import Papers.PODC2024.TetraBFT.ViewLiveness

/-!
# Termination of TetraBFT with a repaired view-change echo rule (not in the paper)

The paper's echo rule ("on `f + 1` view-change messages for `v'`, send one for `v'` unless one for
`v'` *or any higher view* was sent") can deadlock (`Counterexample.lean`). With the repaired rule
(`prm.fixEcho = true`: echo every view `w ≥` the current one with `f + 1` view-change messages
for which no view-change message was sent yet), views synchronize after GST:

* **spacing**: a correct node reaches view `u + 1` only after some correct node spent a full
  timeout in a view `≥ u`; so the first time a correct node reaches `u + 1` is at least `T` after
  the first time a correct node reaches `u` (`reach_spacing`);
* **catch-up**: if the first correct node reaches `u` at time `e ≥ GST`, every correct node is in
  `u` during `[e + 2δ + 2, e + T)` (`sync_window`);
* **progress**: every view is eventually reached (`reach_all`).

With a timeout `T ≥ 8δ + 9` (the paper's `9Δ` up to the discrete-time constants) and a correct
leader for infinitely many views, the window contains the `6(δ + 1)` ticks needed by
`decides_of_synchronized_view`, so every correct node decides (`fixed_termination`), and the
repaired protocol solves consensus (`fixed_solvesConsensus`).
-/

set_option linter.unusedSectionVars false

namespace TetraBFT

open Finset Cslib.Byzantine.PartialSync

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- The views of the view-change messages in a list. -/
def vcs (l : List (Msg V)) : List ℕ :=
  l.filterMap fun m => match m with
    | .viewChange w => some w
    | _ => none

theorem mem_vcs {l : List (Msg V)} {w : ℕ} : w ∈ vcs l ↔ Msg.viewChange w ∈ l := by
  simp only [vcs, List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, he⟩
    cases m <;> simp_all
  · intro h; exact ⟨_, h, rfl⟩

theorem vcs_append (l l' : List (Msg V)) : vcs (l ++ l') = vcs l ++ vcs l' := by
  simp [vcs, List.filterMap_append]

section Stages

variable (prm : Params n)

/-- Stages after the view change do not touch the view-change bookkeeping. -/
structure PostExt (s s' : St n V) : Prop where
  clock : s'.clock = s.clock
  vcList : s'.vcList = s.vcList
  view : s'.view = s.view
  vcs : vcs s'.out = vcs s.out

theorem PostExt.refl (s : St n V) : PostExt s s := ⟨rfl, rfl, rfl, rfl⟩

theorem PostExt.trans {s s' s'' : St n V} (h : PostExt s s') (h' : PostExt s' s'') :
    PostExt s s'' :=
  ⟨h'.clock.trans h.clock, h'.vcList.trans h.vcList, h'.view.trans h.view, h'.vcs.trans h.vcs⟩

theorem PostExt.castVote (s : St n V) (k : ℕ) (x : V) : PostExt s (castVote s k x) :=
  ⟨rfl, rfl, rfl, by simp [TetraBFT.castVote, TetraBFT.vcs]⟩

theorem PostExt.proposeSt (p : Fin n) (s : St n V) : PostExt s (proposeSt prm p s) := by
  rcases proposeSt_shape prm p s with h | ⟨x, h, -⟩
  · rw [h]; exact .refl s
  · rw [h]; exact ⟨rfl, rfl, rfl, by simp [TetraBFT.vcs]⟩

theorem PostExt.vote1St (s : St n V) : PostExt s (vote1St prm s) := by
  unfold TetraBFT.vote1St
  split
  · exact .refl s
  · split
    · exact .refl s
    · split
      · exact .castVote s _ _
      · split
        · exact .castVote s _ _
        · exact .refl s

theorem PostExt.voteKSt (k : ℕ) (s : St n V) : PostExt s (voteKSt prm k s) := by
  unfold TetraBFT.voteKSt
  split
  · exact .refl s
  · split
    · exact .refl s
    · exact .castVote s _ _

theorem PostExt.decideSt (s : St n V) : PostExt s (decideSt prm s) := by
  unfold TetraBFT.decideSt
  split
  · exact .refl s
  · split
    · exact .refl s
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem PostExt.post (p : Fin n) (s : St n V) : PostExt s (post prm p s) :=
  (((((PostExt.proposeSt prm p s).trans (.vote1St prm _)).trans (.voteKSt prm 2 _)).trans
    (.voteKSt prm 3 _)).trans (.voteKSt prm 4 _)).trans (.decideSt prm _)

/-- The bookkeeping of the view-change messages sent in one step. -/
theorem preVote_vcList (s : St n V) (ib : Fin n → List (Msg V)) :
    (preVote prm s ib).vcList = s.vcList ++ vcs (preVote prm s ib).out := by
  simp only [preVote, TetraBFT.viewSt, TetraBFT.echoSt, TetraBFT.recvSt]
  split <;> split <;> (try split) <;> (try split) <;>
    simp [vcs, List.filterMap_map]

theorem echoSt_vc (s : St n V) {u : ℕ} (h : Msg.viewChange u ∈ (echoSt prm s).out) :
    Msg.viewChange u ∈ s.out ∨ prm.f + 1 ≤ (senders s.rcv (.viewChange u)).card := by
  revert h
  unfold TetraBFT.echoSt
  split
  · intro h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with h | ⟨w, hw, hwu⟩
    · exact Or.inl h
    · cases hwu
      simp only [echoViews, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hw
      exact Or.inr hw.2.1.2
  · split
    · rename_i w hw
      intro h
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inl h
      · cases h; exact Or.inr (maxVC_spec hw).2
    · exact Or.inl

theorem echoSt_clock (s : St n V) : (echoSt prm s).clock = s.clock := by
  unfold TetraBFT.echoSt; split
  · rfl
  · split <;> rfl

theorem viewSt_vc (s : St n V) {u : ℕ} (h : Msg.viewChange u ∈ (viewSt prm s).out) :
    Msg.viewChange u ∈ s.out ∨
    ((viewSt prm s).view = s.view ∧ (viewSt prm s).clock = prm.timeout ∧ u = s.view + 1) := by
  revert h
  unfold TetraBFT.viewSt
  split
  · intro h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact Or.inl h
    all_goals cases h
  · split
    · intro h
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inl h
      · cases h; exact Or.inr ⟨rfl, by omega, rfl⟩
    · exact Or.inl

/-- Origin of a view-change message sent in a step: an echo of `f + 1` messages, or the timer. -/
theorem preVote_vc_origin (s : St n V) (ib : Fin n → List (Msg V)) {u : ℕ}
    (h : Msg.viewChange u ∈ (preVote prm s ib).out) :
    prm.f + 1 ≤ (senders (preVote prm s ib).rcv (.viewChange u)).card ∨
    ((preVote prm s ib).view = s.view ∧ (preVote prm s ib).clock = prm.timeout ∧
      u = s.view + 1) := by
  have hrcv : (preVote prm s ib).rcv = (recvSt s ib).rcv := by
    simp only [preVote, (viewSt_fields prm _).2.1, (echoSt_fields prm _).2.1]
  rw [hrcv]
  rcases viewSt_vc prm _ h with h | ⟨hv, hc, rfl⟩
  · rcases echoSt_vc prm _ h with h | h
    · simp [recvSt] at h
    · exact Or.inl h
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · simp only [preVote, hv, (echoSt_fields prm _).2.2.2.2]; rfl
    · exact hc
    · rw [(echoSt_fields prm _).2.2.2.2]; rfl

theorem mem_vcViews {rcv : List (Fin n × Msg V)} {q : Fin n} {u : ℕ}
    (h : (q, Msg.viewChange u) ∈ rcv) : u ∈ vcViews rcv := by
  simp only [vcViews, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

theorem maxVC_ge {rcv : List (Fin n × Msg V)} {th lo u : ℕ} (hu : u ∈ vcViews rcv) (hlo : lo < u)
    (hth : th ≤ (senders rcv (.viewChange u)).card) : ∃ w, maxVC rcv th lo = some w ∧ u ≤ w := by
  have hmem : u ∈ (vcViews rcv).filter fun w =>
      decide (lo < w) && decide (th ≤ (senders rcv (.viewChange w)).card) := by
    simp [hu, hlo, hth]
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hmem)
  exact ⟨w, hw, (List.max?_eq_some_iff.1 hw).2 u hmem⟩

/-- How the view and the timer evolve in a step. -/
theorem viewSt_clock (s : St n V) :
    ((viewSt prm s).view = s.view ∧ (viewSt prm s).clock = s.clock + 1) ∨
    (s.view < (viewSt prm s).view ∧ (viewSt prm s).clock = 0 ∧
      n - prm.f ≤ (senders s.rcv (.viewChange (viewSt prm s).view)).card) := by
  unfold TetraBFT.viewSt
  split
  · rename_i w hw
    exact Or.inr ⟨(maxVC_spec hw).1, rfl, (maxVC_spec hw).2⟩
  · split <;> exact Or.inl ⟨rfl, rfl⟩

theorem preVote_clock (s : St n V) (ib : Fin n → List (Msg V)) :
    ((preVote prm s ib).view = s.view ∧ (preVote prm s ib).clock = s.clock + 1) ∨
    (s.view < (preVote prm s ib).view ∧ (preVote prm s ib).clock = 0 ∧
      n - prm.f ≤ (senders (preVote prm s ib).rcv
        (.viewChange (preVote prm s ib).view)).card) := by
  have h2 := echoSt_fields prm (recvSt s ib)
  have hc := echoSt_clock prm (recvSt s ib)
  rcases viewSt_clock prm (echoSt prm (recvSt s ib)) with ⟨hv, hcl⟩ | ⟨hv, hcl, hq⟩
  · left
    refine ⟨?_, ?_⟩
    · simp only [preVote, hv, h2.2.2.2.2]; rfl
    · simp only [preVote, hcl, hc]; rfl
  · right
    refine ⟨?_, hcl, ?_⟩
    · simp only [preVote]; rw [h2.2.2.2.2] at hv; exact hv
    · simp only [preVote, (viewSt_fields prm _).2.1]; exact hq

theorem viewSt_timer (t : St n V) (hv : (viewSt prm t).view = t.view)
    (hc : (viewSt prm t).clock = prm.timeout) : Msg.viewChange (t.view + 1) ∈ (viewSt prm t).out := by
  revert hv hc
  unfold TetraBFT.viewSt
  split
  · rename_i w hw
    intro hv
    have := (maxVC_spec hw).1
    change w = t.view at hv
    omega
  · split
    · intro _ _
      simp
    · rename_i h'
      intro _ hc
      exact absurd hc h'

/-- The timer: when the clock reaches the timeout without a view change, a view-change message
for the next view is sent. -/
theorem preVote_timer (s : St n V) (ib : Fin n → List (Msg V))
    (hv : (preVote prm s ib).view = s.view) (hc : (preVote prm s ib).clock = prm.timeout) :
    Msg.viewChange (s.view + 1) ∈ (preVote prm s ib).out := by
  have h2 := (echoSt_fields prm (recvSt s ib)).2.2.2.2
  have := viewSt_timer prm (echoSt prm (recvSt s ib)) (by rw [h2]; exact hv) hc
  rw [h2] at this
  exact this

/-- Entering: `n − f` view-change messages for `u` put the node in a view `≥ u`. -/
theorem preVote_view_ge (s : St n V) (ib : Fin n → List (Msg V)) {u : ℕ} {q : Fin n}
    (hq : (q, Msg.viewChange u) ∈ (preVote prm s ib).rcv)
    (hth : n - prm.f ≤ (senders (preVote prm s ib).rcv (.viewChange u)).card) :
    u ≤ (preVote prm s ib).view := by
  have hrcv : (preVote prm s ib).rcv = (echoSt prm (recvSt s ib)).rcv := by
    simp only [preVote, (viewSt_fields prm _).2.1]
  rw [hrcv] at hq hth
  have h2 := echoSt_fields prm (recvSt s ib)
  simp only [preVote]
  unfold TetraBFT.viewSt
  rcases Nat.lt_or_ge (echoSt prm (recvSt s ib)).view u with hlt | hge
  · obtain ⟨w, hw, huw⟩ := maxVC_ge (mem_vcViews hq) hlt hth
    rw [hw]; exact huw
  · split
    · rename_i w hw
      have := (maxVC_spec hw).1
      simp only; omega
    · split <;> exact hge

/-- The repaired echo rule. -/
theorem preVote_echo (hfix : prm.fixEcho = true) (s : St n V) (ib : Fin n → List (Msg V))
    {u : ℕ} {q : Fin n} (hq : (q, Msg.viewChange u) ∈ (preVote prm s ib).rcv)
    (hview : s.view ≤ u)
    (hth : prm.f + 1 ≤ (senders (preVote prm s ib).rcv (.viewChange u)).card)
    (hnot : u ∉ s.vcList) : Msg.viewChange u ∈ (preVote prm s ib).out := by
  have hrcv : (preVote prm s ib).rcv = (recvSt s ib).rcv := by
    simp only [preVote, (viewSt_fields prm _).2.1, (echoSt_fields prm _).2.1]
  rw [hrcv] at hq hth
  have hmem : u ∈ echoViews prm (recvSt s ib) := by
    have h1 := mem_vcViews hq
    simp only [echoViews, List.mem_filter, List.mem_dedup]
    refine ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hview, hth⟩, by simpa [recvSt] using hnot⟩
  have hout : Msg.viewChange u ∈ (echoSt prm (recvSt s ib)).out := by
    unfold TetraBFT.echoSt
    simp only [hfix, ite_true]
    exact List.mem_append_right _ (List.mem_map.2 ⟨u, hmem, rfl⟩)
  simp only [preVote]
  unfold TetraBFT.viewSt
  split
  · exact List.mem_append_left _ hout
  · split
    · exact List.mem_append_left _ hout
    · exact hout

end Stages

/-! ### Run-level facts about the view change -/

section Run

variable {prm : Params n} (R : Run (Fin n) (Msg V) V)

local notation "A" => tetra (V := V) prm

theorem work_clock (τ : ℕ) (p : Fin n) : (work prm R τ p).clock = (R.st A (τ + 1) p).clock := by
  rw [st_step, (PostExt.post prm p _).clock]

theorem mem_out_iff_work {τ : ℕ} {p : Fin n} {u : ℕ} :
    Msg.viewChange u ∈ (R.st A (τ + 1) p).out ↔ Msg.viewChange u ∈ (work prm R τ p).out := by
  rw [st_step, ← mem_vcs, ← mem_vcs, (PostExt.post prm p _).vcs]

theorem st_vcList (τ : ℕ) (p : Fin n) :
    (R.st A (τ + 1) p).vcList = (R.st A τ p).vcList ++ vcs (R.st A (τ + 1) p).out := by
  rw [st_step, (PostExt.post prm p _).vcList, (PostExt.post prm p _).vcs]
  exact preVote_vcList prm _ _

/-- A view recorded as sent was sent. -/
theorem vcList_sent {p : Fin n} {u : ℕ} :
    ∀ τ, u ∈ (R.st A τ p).vcList → ∃ τ' ≤ τ, Msg.viewChange u ∈ (R.st A τ' p).out := by
  intro τ
  induction τ with
  | zero => intro h; simp [tetra] at h
  | succ τ ih =>
    intro h
    rw [st_vcList, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨τ', hτ', hm⟩ := ih h; exact ⟨τ', by omega, hm⟩
    · exact ⟨τ + 1, le_rfl, mem_vcs.1 h⟩

theorem out_vc_origin {τ : ℕ} {p : Fin n} {u : ℕ} (h : Msg.viewChange u ∈ (R.st A (τ + 1) p).out) :
    prm.f + 1 ≤ (senders (R.st A (τ + 1) p).rcv (.viewChange u)).card ∨
    ((R.st A (τ + 1) p).view = (R.st A τ p).view ∧ (R.st A (τ + 1) p).clock = prm.timeout ∧
      u = (R.st A τ p).view + 1) := by
  rw [mem_out_iff_work] at h
  rw [← work_rcv, ← work_view, ← work_clock]
  exact preVote_vc_origin prm _ _ h

theorem st_clock (τ : ℕ) (p : Fin n) :
    ((R.st A (τ + 1) p).view = (R.st A τ p).view ∧
      (R.st A (τ + 1) p).clock = (R.st A τ p).clock + 1) ∨
    ((R.st A τ p).view < (R.st A (τ + 1) p).view ∧ (R.st A (τ + 1) p).clock = 0 ∧
      n - prm.f ≤ (senders (R.st A (τ + 1) p).rcv
        (.viewChange (R.st A (τ + 1) p).view)).card) := by
  rw [← work_rcv, ← work_view, ← work_clock]
  exact preVote_clock prm _ _

theorem st_timer {τ : ℕ} {p : Fin n} (hv : (R.st A (τ + 1) p).view = (R.st A τ p).view)
    (hc : (R.st A (τ + 1) p).clock = prm.timeout) :
    Msg.viewChange ((R.st A τ p).view + 1) ∈ (R.st A (τ + 1) p).out := by
  rw [mem_out_iff_work]
  rw [← work_view] at hv
  rw [← work_clock] at hc
  exact preVote_timer prm _ _ hv hc

theorem st_echo (hfix : prm.fixEcho = true) {τ : ℕ} {p q : Fin n} {u : ℕ}
    (hq : (q, Msg.viewChange u) ∈ (R.st A (τ + 1) p).rcv) (hview : (R.st A τ p).view ≤ u)
    (hth : prm.f + 1 ≤ (senders (R.st A (τ + 1) p).rcv (.viewChange u)).card)
    (hnot : u ∉ (R.st A τ p).vcList) : Msg.viewChange u ∈ (R.st A (τ + 1) p).out := by
  rw [mem_out_iff_work]
  rw [← work_rcv] at hq hth
  exact preVote_echo prm hfix _ _ hq hview hth hnot

theorem st_view_ge {τ : ℕ} {p q : Fin n} {u : ℕ}
    (hq : (q, Msg.viewChange u) ∈ (R.st A (τ + 1) p).rcv)
    (hth : n - prm.f ≤ (senders (R.st A (τ + 1) p).rcv (.viewChange u)).card) :
    u ≤ (R.st A (τ + 1) p).view := by
  rw [← work_rcv] at hq hth
  rw [← work_view]
  exact preVote_view_ge prm _ _ hq hth

/-- The timer measures the time spent in the current view. -/
theorem clock_back (p : Fin n) : ∀ τ, (R.st A τ p).clock ≤ τ ∧
    ∀ k ≤ (R.st A τ p).clock, (R.st A (τ - k) p).view = (R.st A τ p).view ∧
      (R.st A (τ - k) p).clock = (R.st A τ p).clock - k := by
  intro τ
  induction τ with
  | zero => simp [tetra]
  | succ τ ih =>
    rcases st_clock (prm := prm) R τ p with ⟨hv, hc⟩ | ⟨-, hc, -⟩
    · refine ⟨by omega, fun k hk => ?_⟩
      rcases k with _ | k
      · simp
      · have := ih.2 k (by omega)
        rw [show τ + 1 - (k + 1) = τ - k by omega, this.1, this.2, hv, hc]
        exact ⟨rfl, by omega⟩
    · rw [hc]
      refine ⟨by omega, fun k hk => ?_⟩
      obtain rfl : k = 0 := by omega
      simpa using hc

/-- While the view does not change, the clock ticks. -/
theorem clock_add {p : Fin n} {a : ℕ} :
    ∀ k, (∀ i ≤ k, (R.st A (a + i) p).view = (R.st A a p).view) →
      (R.st A (a + k) p).clock = (R.st A a p).clock + k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rcases st_clock (prm := prm) R (a + k) p with ⟨-, hc⟩ | ⟨hlt, -, -⟩
    · rw [← Nat.add_assoc, hc, ih (fun i hi => h i (by omega))]; omega
    · have h1 := h (k + 1) le_rfl
      have h2 := h k (by omega)
      rw [← Nat.add_assoc] at h1
      rw [h1, h2] at hlt
      exact absurd hlt (lt_irrefl _)

end Run

/-! ### Spacing of views -/

section Spacing

variable {prm : Params n} (R : Run (Fin n) (Msg V) V)

local notation "A" => tetra (V := V) prm

/-- Some correct node is in a view `≥ u` at time `τ`. -/
def Reach (prm : Params n) (R : Run (Fin n) (Msg V) V) (u τ : ℕ) : Prop :=
  ∃ p ∉ R.faulty, u ≤ (R.st (tetra prm) τ p).view

/-- Every view-change message of a correct node goes back to a timeout of a correct node. -/
theorem vc_origin_timeout (hF : R.faulty.card ≤ prm.f) : ∀ τ, ∀ p ∉ R.faulty, ∀ u,
    Msg.viewChange u ∈ (R.st A τ p).out →
    ∃ q ∉ R.faulty, ∃ τ' ≤ τ, (R.st A τ' q).view + 1 = u ∧ (R.st A τ' q).clock = prm.timeout := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
  intro p hp u h
  rcases τ with _ | τ
  · simp [tetra] at h
  rcases out_vc_origin R h with hq | ⟨hv, hc, rfl⟩
  · obtain ⟨c, hc, hcF⟩ := exists_mem_notMem_of_card_le_of_lt hF hq
    simp only [senders, mem_filter, mem_univ, true_and] at hc
    obtain ⟨τ'', hτ'', hm⟩ := rcv_authentic R hcF hc
    obtain ⟨q, hqF, τ', hτ', h1, h2⟩ := ih τ'' hτ'' c hcF u hm
    exact ⟨q, hqF, τ', by omega, h1, h2⟩
  · exact ⟨p, hp, τ + 1, le_rfl, by rw [hv], hc⟩

/-- A node in a view `≥ 1` entered it, on `n − f` view-change messages. -/
theorem entered_quorum {p : Fin n} : ∀ τ, 1 ≤ (R.st A τ p).view → ∃ τe < τ,
    (R.st A (τe + 1) p).view = (R.st A τ p).view ∧
    n - prm.f ≤ (senders (R.st A (τe + 1) p).rcv (.viewChange (R.st A τ p).view)).card := by
  intro τ
  induction τ with
  | zero => intro h; simp [tetra] at h
  | succ τ ih =>
    intro h
    rcases st_clock (prm := prm) R τ p with ⟨hv, -⟩ | ⟨-, -, hq⟩
    · obtain ⟨τe, hτe, h1, h2⟩ := ih (by rw [← hv]; exact h)
      exact ⟨τe, by omega, by rw [h1, hv], by rw [hv]; exact h2⟩
    · exact ⟨τ, by omega, rfl, hq⟩

/-- **Spacing.** A correct node in a view `≥ u + 1` at time `τ` implies that a correct node was
in a view `≥ u` already at time `τ − T`. -/
theorem reach_spacing (hn : 3 * prm.f < n) (hF : R.faulty.card ≤ prm.f) {u τ : ℕ}
    (h : Reach prm R (u + 1) τ) : prm.timeout ≤ τ ∧ Reach prm R u (τ - prm.timeout) := by
  obtain ⟨p, hp, hpv⟩ := h
  obtain ⟨τe, hτe, -, hq⟩ := entered_quorum (prm := prm) R τ (le_trans (by omega) hpv)
  obtain ⟨c, hc, hcF⟩ := exists_mem_notMem_of_card_le_of_lt hF (show prm.f + 1 ≤
    (senders (R.st A (τe + 1) p).rcv (.viewChange (R.st A τ p).view)).card by omega)
  simp only [senders, mem_filter, mem_univ, true_and] at hc
  obtain ⟨τc, hτc, hm⟩ := rcv_authentic R hcF hc
  obtain ⟨q, hqF, τ', hτ', h1, h2⟩ := vc_origin_timeout R hF τc c hcF _ hm
  obtain ⟨hT, hback⟩ := clock_back R q τ'
  rw [h2] at hT hback
  have hv := (hback prm.timeout le_rfl).1
  refine ⟨by omega, q, hqF, ?_⟩
  calc u ≤ (R.st A (τ' - prm.timeout) q).view := by rw [hv]; omega
    _ ≤ _ := st_view_mono R (by omega) q

end Spacing

/-! ### Catch-up, synchronization window, progress -/

section Sync

variable {prm : Params n} (R : Run (Fin n) (Msg V) V)

local notation "A" => tetra (V := V) prm

theorem card_correct_run (hF : R.faulty.card ≤ prm.f) :
    n - prm.f ≤ (univ.filter (· ∉ R.faulty)).card := by
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun q => q ∉ R.faulty)
  have h2 : (univ.filter fun q : Fin n => ¬ q ∉ R.faulty).card ≤ R.faulty.card :=
    card_le_card fun q hq => by simp only [mem_filter, not_not] at hq; exact hq.2
  rw [card_univ, Fintype.card_fin] at h1
  omega

/-- **Catch-up.** Suppose that by time `t ≥ GST` some correct node has received `n − f`
view-change messages for `u`, and that at time `t + δ` no correct node is above `u`. Then at
time `t + 2δ + 2` every correct node is in a view `≥ u`. -/
theorem catch_up (hfix : prm.fixEcho = true) (hn : 3 * prm.f < n) {δ : ℕ}
    (hR : R.Valid prm.f δ) {u t te : ℕ} {p : Fin n} (hgst : R.gst ≤ t)
    (hte : te + 1 ≤ t)
    (hq : n - prm.f ≤ (senders (R.st A (te + 1) p).rcv (.viewChange u)).card)
    (hbelow : ∀ j ∉ R.faulty, (R.st A (t + δ) j).view ≤ u) :
    ∀ i ∉ R.faulty, u ≤ (R.st A (t + 2 * δ + 2) i).view := by
  have hF := hR.card_faulty
  set C := (senders (R.st A (te + 1) p).rcv (.viewChange u)).filter (· ∉ R.faulty) with hC
  have hCcard : prm.f + 1 ≤ C.card := card_correct_quorum (by simpa using hn) hF (by simpa using hq)
  -- every correct node receives the messages of `C` by `t + δ`
  have hrecv : ∀ j ∉ R.faulty, ∀ c ∈ C, (c, Msg.viewChange u) ∈ (R.st A (t + δ + 1) j).rcv := by
    intro j hj c hc
    simp only [hC, senders, mem_filter, mem_univ, true_and] at hc
    obtain ⟨τc, hτc, hm⟩ := rcv_authentic R hc.2 hc.1
    exact deliver R hR hc.2 hj hm (by omega)
  obtain ⟨c₀, hc₀⟩ : C.Nonempty := card_pos.1 (by omega)
  -- every correct node has sent a view-change message for `u` by `t + δ + 1`
  have hsent : ∀ j ∉ R.faulty, ∃ τj ≤ t + δ + 1, Msg.viewChange u ∈ (R.st A τj j).out := by
    intro j hj
    by_cases hl : u ∈ (R.st A (t + δ) j).vcList
    · obtain ⟨τ', hτ', hm⟩ := vcList_sent R (t + δ) hl
      exact ⟨τ', by omega, hm⟩
    · refine ⟨t + δ + 1, le_rfl, st_echo R hfix (hrecv j hj c₀ hc₀) (hbelow j hj) ?_ hl⟩
      exact le_trans hCcard (card_le_card fun c hc => by
        simp only [senders, mem_filter, mem_univ, true_and]; exact hrecv j hj c hc)
  intro i hi
  have hall : ∀ j ∉ R.faulty, (j, Msg.viewChange u) ∈ (R.st A (t + 2 * δ + 1 + 1) i).rcv := by
    intro j hj
    obtain ⟨τj, hτj, hm⟩ := hsent j hj
    exact deliver R hR hj hi hm (by omega)
  obtain ⟨j₀, hj₀⟩ : (univ.filter (· ∉ R.faulty)).Nonempty :=
    card_pos.1 (by have := card_correct_run (prm := prm) R hF; omega)
  have hj₀' : j₀ ∉ R.faulty := (mem_filter.1 hj₀).2
  refine st_view_ge R (hall j₀ hj₀') (le_trans (card_correct_run (prm := prm) R hF)
    (card_le_card fun j hj => ?_))
  simp only [senders, mem_filter, mem_univ, true_and]
  exact hall j (mem_filter.1 hj).2

/-- **Synchronization window.** If `e ≥ GST` is the first time a correct node is in a view
`≥ u` (`u ≥ 1`), then every correct node is in view `u` during `[e + 2δ + 2, e + T)`. -/
theorem sync_window (hfix : prm.fixEcho = true) (hn : 3 * prm.f < n) {δ : ℕ}
    (hR : R.Valid prm.f δ) (hT : 2 * δ + 3 ≤ prm.timeout) {u e : ℕ} (hu : 1 ≤ u)
    (he : Reach prm R u e) (hmin : ∀ τ < e, ¬ Reach prm R u τ) (hgst : R.gst ≤ e) :
    ∀ i ∉ R.faulty, ∀ τ, e + 2 * δ + 2 ≤ τ → τ < e + prm.timeout →
      (R.st A τ i).view = u := by
  have hF := hR.card_faulty
  have hupper : ∀ τ < e + prm.timeout, ∀ j ∉ R.faulty, (R.st A τ j).view ≤ u := by
    intro τ hτ j hj
    by_contra hlt
    obtain ⟨hTτ, hr⟩ := reach_spacing R hn hF ⟨j, hj, (by omega : u + 1 ≤ (R.st A τ j).view)⟩
    exact hmin _ (by omega) hr
  obtain ⟨p, hp, hpv⟩ := he
  have hpe : (R.st A e p).view = u := le_antisymm (hupper e (by omega) p hp) hpv
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := by
    rcases e with _ | e'
    · simp [tetra] at hpv; omega
    · exact ⟨e', rfl⟩
  have hprev : (R.st A e' p).view < u := by
    by_contra h
    exact hmin e' (by omega) ⟨p, hp, by omega⟩
  have hq : n - prm.f ≤ (senders (R.st A (e' + 1) p).rcv (.viewChange u)).card := by
    rcases st_clock (prm := prm) R e' p with ⟨hv, -⟩ | ⟨-, -, hq⟩
    · omega
    · rwa [hpe] at hq
  have hcatch := catch_up R hfix hn hR hgst le_rfl hq
    (fun j hj => hupper _ (by omega) j hj)
  intro i hi τ h1 h2
  exact le_antisymm (hupper τ h2 i hi) (le_trans (hcatch i hi) (st_view_mono R h1 i))

/-- **Progress.** Every reached view is eventually exceeded. -/
theorem reach_succ (hfix : prm.fixEcho = true) (hn : 3 * prm.f < n) {δ : ℕ}
    (hR : R.Valid prm.f δ) (hT : 1 ≤ prm.timeout) {u τ0 : ℕ} (h0 : Reach prm R u τ0) :
    ∃ τ, Reach prm R (u + 1) τ := by
  have hF := hR.card_faulty
  by_contra H
  push Not at H
  have hle : ∀ τ, ∀ j ∉ R.faulty, (R.st A τ j).view ≤ u := by
    intro τ j hj
    by_contra hlt
    exact H τ ⟨j, hj, by omega⟩
  set t := max τ0 R.gst
  -- all correct nodes are in view `u` from `a := t + 2δ + 2` on
  have hge : ∀ i ∉ R.faulty, u ≤ (R.st A (t + 2 * δ + 2) i).view := by
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · intro i _; exact Nat.zero_le _
    obtain ⟨p, hp, hpv⟩ := h0
    obtain ⟨τe, hτe, h1, h2⟩ := entered_quorum (prm := prm) R τ0 (le_trans hu hpv)
    have hpu : (R.st A τ0 p).view = u := le_antisymm (hle τ0 p hp) hpv
    rw [hpu] at h2
    exact catch_up R hfix hn hR (le_max_right _ _) (by omega) h2
      (fun j hj => hle _ j hj)
  set a := t + 2 * δ + 2
  have hview : ∀ i ∉ R.faulty, ∀ τ, a ≤ τ → (R.st A τ i).view = u := fun i hi τ hτ =>
    le_antisymm (hle τ i hi) (le_trans (hge i hi) (st_view_mono R hτ i))
  -- every correct node times out in view `u` by `a + T`
  have hsent : ∀ j ∉ R.faulty, ∃ τj ≤ a + prm.timeout,
      Msg.viewChange (u + 1) ∈ (R.st A τj j).out := by
    intro j hj
    set c := (R.st A a j).clock with hc
    rcases Nat.lt_or_ge c prm.timeout with hlt | hge'
    · obtain ⟨k, hk⟩ : ∃ k, prm.timeout - c = k + 1 := ⟨prm.timeout - c - 1, by omega⟩
      have hclk := clock_add (prm := prm) R (p := j) (a := a) (k + 1)
        (fun i _ => by rw [hview j hj _ (by omega), hview j hj a le_rfl])
      have hv1 := hview j hj (a + k) (by omega)
      have hv2 := hview j hj (a + k + 1) (by omega)
      refine ⟨a + k + 1, by omega, ?_⟩
      have := st_timer (prm := prm) R (τ := a + k) (p := j) (by rw [hv1, hv2])
        (by rw [show a + k + 1 = a + (k + 1) by omega, hclk]; omega)
      rwa [hv1] at this
    · obtain ⟨hca, hback⟩ := clock_back (prm := prm) R j a
      have hb1 := hback (c - prm.timeout) (by omega)
      have hb2 := hback (c - prm.timeout + 1) (by omega)
      rw [← hc, hview j hj a le_rfl] at hb1 hb2
      obtain ⟨τ1, hτ1⟩ : ∃ τ1, a - (c - prm.timeout + 1) = τ1 := ⟨_, rfl⟩
      have heq : a - (c - prm.timeout) = τ1 + 1 := by omega
      rw [heq] at hb1
      rw [hτ1] at hb2
      refine ⟨τ1 + 1, by omega, ?_⟩
      have := st_timer (prm := prm) R (τ := τ1) (p := j) (by rw [hb1.1, hb2.1])
        (by rw [hb1.2]; omega)
      rwa [hb2.1] at this
  obtain ⟨j₀, hj₀⟩ : (univ.filter (· ∉ R.faulty)).Nonempty :=
    card_pos.1 (by have := card_correct_run (prm := prm) R hF; omega)
  have hj₀' : j₀ ∉ R.faulty := (mem_filter.1 hj₀).2
  have hall : ∀ j ∉ R.faulty,
      (j, Msg.viewChange (u + 1)) ∈ (R.st A (a + prm.timeout + δ + 1) j₀).rcv := by
    intro j hj
    obtain ⟨τj, hτj, hm⟩ := hsent j hj
    exact deliver R hR hj hj₀' hm (by omega)
  have := st_view_ge R (hall j₀ hj₀') (le_trans (card_correct_run (prm := prm) R hF)
    (card_le_card fun j hj => by
      simp only [senders, mem_filter, mem_univ, true_and]
      exact hall j (mem_filter.1 hj).2))
  exact H _ ⟨j₀, hj₀', this⟩

theorem reach_all (hfix : prm.fixEcho = true) (hn : 3 * prm.f < n) {δ : ℕ}
    (hR : R.Valid prm.f δ) (hT : 1 ≤ prm.timeout) : ∀ u, ∃ τ, Reach prm R u τ := by
  intro u
  induction u with
  | zero =>
    obtain ⟨j₀, hj₀⟩ : (univ.filter (· ∉ R.faulty)).Nonempty :=
      card_pos.1 (by have := card_correct_run (prm := prm) R hR.card_faulty; omega)
    exact ⟨0, j₀, (mem_filter.1 hj₀).2, Nat.zero_le _⟩
  | succ u ih =>
    obtain ⟨τ, hτ⟩ := ih
    exact reach_succ R hfix hn hR hT hτ

theorem reach_le (hn : 3 * prm.f < n) (hF : R.faulty.card ≤ prm.f) (hT : 1 ≤ prm.timeout) :
    ∀ u τ, Reach prm R u τ → u ≤ τ := by
  intro u
  induction u with
  | zero => intro _ _; exact Nat.zero_le _
  | succ u ih =>
    intro τ h
    obtain ⟨h1, h2⟩ := reach_spacing R hn hF h
    have := ih _ h2
    omega

end Sync

/-! ### Termination of the repaired protocol -/

/-- **Termination with the repaired echo rule.** With `3f < n`, a valid run with delay bound
`δ`, a timeout `T ≥ 8δ + 9`, and a correct leader in arbitrarily late views, every correct node
decides. -/
theorem fixed_termination {prm : Params n} (hfix : prm.fixEcho = true) (hn : 3 * prm.f < n)
    {δ : ℕ} (hT : 8 * δ + 9 ≤ prm.timeout) {R : Run (Fin n) (Msg V) V} (hR : R.Valid prm.f δ)
    (hlead : ∀ v, ∃ u, v ≤ u ∧ prm.leader u ∉ R.faulty) :
    ∀ p ∉ R.faulty, ∃ x, R.Decides (tetra prm) p x := by
  classical
  obtain ⟨u, hu, hℓ⟩ := hlead (R.gst + 1)
  have hex := reach_all R hfix hn hR (by omega) u
  set e := Nat.find hex
  have he : Reach prm R u e := Nat.find_spec hex
  have hmin : ∀ τ < e, ¬ Reach prm R u τ := fun τ hτ => Nat.find_min hex hτ
  have hue := reach_le R hn hR.card_faulty (by omega) u e he
  have hwin := sync_window R hfix hn hR (by omega) (by omega) he hmin (by omega)
  exact fun p hp => (decides_of_synchronized_view hn hR hℓ (t0 := e + 2 * δ + 2) (by omega)
    (fun q hq τ h1 h2 => hwin q hq τ h1 (by omega)) p hp).2

/-- The validity property of Definition 1: if all nodes are correct and have the same input `x`,
the decision is `x`. -/
def paperValidity (n : ℕ) (V : Type) : ValidityProperty (Fin n) V V :=
  fun c => {y | ∀ x, (∀ p, c p = some x) → y = x}

/-- **The repaired protocol solves consensus** (agreement, the paper's validity, termination) in
the partially synchronous model with `n > 3f`, round-robin leaders and timeout `T ≥ 8δ + 9`. -/
theorem fixed_solvesConsensus {prm : Params n} (hfix : prm.fixEcho = true) (hn : 3 * prm.f < n)
    {δ : ℕ} (hT : 8 * δ + 9 ≤ prm.timeout) (hrr : ∀ v, (prm.leader v : ℕ) = v % n) :
    SolvesConsensus prm.f δ (tetra (V := V) prm) (paperValidity n V) where
  termination R hR := by
    refine fixed_termination hfix hn hT hR fun v => ?_
    obtain ⟨c, hc⟩ : (univ.filter (· ∉ R.faulty)).Nonempty :=
      card_pos.1 (by have := card_correct_run (prm := prm) R hR.card_faulty; omega)
    have hn0 : 0 < n := by omega
    refine ⟨n * v + c.val, ?_, ?_⟩
    · calc v ≤ n * v := Nat.le_mul_of_pos_left v hn0
        _ ≤ _ := Nat.le_add_right _ _
    · have : prm.leader (n * v + c.val) = c := by
        ext; rw [hrr, Nat.mul_add_mod, Nat.mod_eq_of_lt c.isLt]
      rw [this]; exact (mem_filter.1 hc).2
  agreement R hR p hp q hq x y hx hy := tetra_agreement R hn hR.card_faulty hp hq hx hy
  validity R hR p hp y hy := by
    intro x hx
    have hF : R.faulty = ∅ := by
      ext q
      simp only [Finset.notMem_empty, iff_false]
      intro hq
      have := hx q
      simp [Run.inputConf, hq] at this
    have hinp : ∀ q, R.inp q = x := fun q => by
      have := hx q
      simp [Run.inputConf, hF] at this
      exact this
    exact tetra_validity R (by omega) hF hinp hy

end TetraBFT

namespace TetraBFT

/-- Non-vacuity: a concrete repaired instance (`n = 4`, `f = 1`, `δ = 1`, timeout 17). -/
def fixedPrm4 : Params 4 where
  f := 1
  leader v := ⟨v % 4, Nat.mod_lt _ (by omega)⟩
  timeout := 17
  fixEcho := true

example : Cslib.Byzantine.PartialSync.SolvesConsensus 1 1 (tetra (V := Bool) fixedPrm4)
    (paperValidity 4 Bool) :=
  fixed_solvesConsensus (prm := fixedPrm4) rfl (by decide) (by decide) (fun _ => rfl)

end TetraBFT
