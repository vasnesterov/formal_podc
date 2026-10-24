import Papers.PODC2017.ZigzagCausality.Knowledge

/-!
# Timed coordination: Definition 1, Lemma 4 and Theorem 3

Dan, Manohar, Moses, *On Using Time Without Clocks via Zigzag Causality*, PODC 2017
(Section 4.1 and Appendix A).

* `CoordTask` — the data of the coordination problems of Definition 1: processes `A`, `B`, `C`,
  the external message `μ_go` (when `C` receives it, `C` sends "go" to `A`, and `A` performs `a`
  when the "go" message arrives, i.e. at `σC · A`), and the local states in which `B` performs `b`.
* `ImplementsLate T x` / `ImplementsEarly T x` — the protocol implements `Late⟨a --x--> b⟩` /
  `Early⟨b --x--> a⟩` (Definition 1).
* `slowRun` — the run `r'` of the proof of Lemma 4: messages sent and received in the past of `σ`
  are delivered as in `r`, all others at their upper bound, and external messages only in the past
  of `σ`. `slowRun_st` — the past of `σ` is unchanged (`r' ∼_σ r`).
* `lemma4` — **Lemma 4**, `thm3_late`, `thm3_early` — **Theorem 3**.

All three are proved for *flooding* full-information protocols (FFIP): the proof of Lemma 4 uses
that a node outside the past of `σ` sends to all its neighbours (otherwise the slow run may deliver
"new" messages to the past of `σ`), and Theorem 3 uses Lemma 3, which needs full information.
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

/-- The data of the timed coordination problems of Definition 1: `A` performs `a` when it
receives a "go" message from `C`; `C` sends it spontaneously, when it receives the external
message `go = μ_go`; `B` performs `b` at its local states satisfying `doB` (the protocol is
deterministic, so the action is a function of the local state). -/
structure CoordTask (P S M E : Type*) where
  A : P
  B : P
  C : P
  /-- The external message `μ_go`. -/
  go : E
  /-- The local states of `B` in which `B` performs `b`. -/
  doB : LState P S M E → Prop


namespace CoordTask

/-- The general node `σC · A` at which `A` performs `a` (where the "go" message sent at `σC`
arrives). -/
def aNode (T : CoordTask P S M E) (σC : BNode P S M E) : GNode P S M E := ⟨σC, [T.A]⟩

end CoordTask

namespace Sys

variable (γ : Sys P S M E) (r : Sched P S E) [Finite P]

/-- `σC` is a basic node of `C` at which `C` receives `μ_go` (and sends "go" to `A`). -/
def GoNode (T : CoordTask P S M E) (σC : BNode P S M E) : Prop :=
  γ.appears r σC ∧ σC.1 = T.C ∧ ∃ b, σC.2.hist.getLast? = some b ∧ T.go ∈ b.ext

/-- `B` performs `b` at the basic node `σ` of `r`. -/
def Performs (T : CoordTask P S M E) (σ : BNode P S M E) : Prop :=
  γ.appears r σ ∧ σ.1 = T.B ∧ T.doB σ.2

/-- **Definition 1 (`Late⟨a --x--> b⟩`).** Whenever `B` performs `b` (at `σ`), `C` has sent "go"
at some `σC` and `a` is performed at `σC · A` at least `x` time units before `b`. -/
def ImplementsLate (T : CoordTask P S M E) (x : ℤ) : Prop :=
  ∀ r : Sched P S E, γ.Valid r → ∀ σ, γ.Performs r T σ →
    ∃ σC, γ.GoNode r T σC ∧ γ.Prec r (T.aNode σC) x (GNode.ofB σ)

/-- **Definition 1 (`Early⟨b --x--> a⟩`).** Whenever `B` performs `b` (at `σ`), `C` has sent "go"
at some `σC` and `a` is performed at `σC · A` at least `x` time units after `b`. -/
def ImplementsEarly (T : CoordTask P S M E) (x : ℤ) : Prop :=
  ∀ r : Sched P S E, γ.Valid r → ∀ σ, γ.Performs r T σ →
    ∃ σC, γ.GoNode r T σC ∧ γ.Prec r (GNode.ofB σ) x (T.aNode σC)

variable {γ r}

/-! ### Go nodes -/

theorem GoNode.mem_ext {T : CoordTask P S M E} {σC : BNode P S M E} (h : γ.GoNode r T σC) :
    T.go ∈ r.ext (γ.timer r σC) T.C ∧ 0 < γ.timer r σC := by
  obtain ⟨ha, hC, b, hb, hgo⟩ := h
  have hne : σC.2.hist ≠ [] := by rintro hn; rw [hn] at hb; simp at hb
  have h0 := (γ.timer_pos_iff r ha).2 hne
  have hh := γ.hist_of_timer_pos r ha h0
  rw [hh] at hb
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at hb
  subst hb
  rw [batch_ext, Nat.sub_add_cancel h0, hC] at hgo
  exact ⟨hgo, h0⟩

/-- Since `μ_go` is delivered at most once, there is at most one go node in a run. -/
theorem GoNode.unique (hr : γ.Valid r) {T : CoordTask P S M E} {σ₁ σ₂ : BNode P S M E}
    (h₁ : γ.GoNode r T σ₁) (h₂ : γ.GoNode r T σ₂) : σ₁ = σ₂ := by
  have e := hr.ext_unique _ _ _ _ _ h₁.mem_ext.1 h₂.mem_ext.1
  exact γ.eq_of_timer_eq r (h₁.2.1.trans h₂.2.1.symm) h₁.1 h₂.1 e.1

/-! ### The slow run of the proof of Lemma 4 -/

variable (γ r) in
/-- The run `r'` of the proof of Lemma 4: a message sent at time `s` by `k` to `i` is delivered
as in `r` if it is sent in `r` from a node in the past of `σ` and received in `r` at a node in the
past of `σ`; otherwise it is delivered at its upper bound. External messages are delivered as in
`r`, but only at nodes in the past of `σ`. -/
noncomputable def slowRun (σ : BNode P S M E) : Sched P S E where
  g := r.g
  dlv k s i :=
    if γ.Sends r k s i ∧ γ.HB r (k, γ.st r s k) σ ∧ γ.HB r (i, γ.st r (r.dlv k s i) i) σ then
      r.dlv k s i else s + γ.net.U k i
  ext t i := if γ.HB r (i, γ.st r t i) σ then r.ext t i else ∅

theorem slowRun_mem_ext {σ : BNode P S M E} {t : ℕ} {i : P} {e : E}
    (h : e ∈ (γ.slowRun r σ).ext t i) : e ∈ r.ext t i ∧ γ.HB r (i, γ.st r t i) σ := by
  simp only [slowRun] at h
  split_ifs at h with hp
  · exact ⟨h, hp⟩
  · simp at h

theorem slowRun_valid (hr : γ.Valid r) (σ : BNode P S M E) : γ.Valid (γ.slowRun r σ) where
  init := hr.init
  bounds k s i h := by
    simp only [slowRun]
    split_ifs with hc
    · exact hr.bounds k s i hc.1
    · have := γ.net.L_le_U k i h.2.1
      omega
  ext_unique e t j t' j' h h' :=
    hr.ext_unique e t j t' j' (slowRun_mem_ext h).1 (slowRun_mem_ext h').1

theorem hist_ne_nil_of_active {s : ℕ} {k : P} (h : γ.Active r k s) : (γ.st r s k).hist ≠ [] := by
  intro hn
  have := γ.length_lt_of_active r h (t := s - 1) (by have := h.1; omega)
  rw [hn] at this
  simp at this

theorem hist_ne_nil_mono {s s' : ℕ} {k : P} (h : (γ.st r s k).hist ≠ []) (hs : s ≤ s') :
    (γ.st r s' k).hist ≠ [] := by
  intro hn
  have := γ.length_mono r hs k
  rw [hn] at this
  exact h (List.eq_nil_of_length_eq_zero (by simpa using this))

/-- Past nodes at earlier times of the same process are in the past. -/
theorem HB_st_of_le {σ : BNode P S M E} {s t : ℕ} {k : P} (h : γ.HB r (k, γ.st r t k) σ)
    (hs : s ≤ t) : γ.HB r (k, γ.st r s k) σ :=
  (HB.of_local (γ.appears_st r s k) (γ.appears_st r t k) rfl (γ.timer_mono r hs k)).trans h

/-- In a flooding protocol a non-initial node `(k, r_k(s))` informs every out-neighbour `i` by
time `s + U k i`. -/
theorem flood_bound (hF : γ.IsFFIP) (hr : γ.Valid r) {s : ℕ} {k i : P}
    (h : (γ.st r s k).hist ≠ []) (hc : γ.net.Chan k i) :
    γ.HB r (k, γ.st r s k) (i, γ.st r (s + γ.net.U k i) i) ∧
      (γ.st r (s + γ.net.U k i) i).hist ≠ [] := by
  have ha := γ.appears_st r s k
  have h0 := (γ.timer_pos_iff r ha).2 h
  obtain ⟨ρ', hρ'⟩ := Option.isSome_iff_exists.1 (recv_isSome_of_FFIP hF ha h0 hc)
  obtain ⟨hp, ha', -, -, hL, hU⟩ := recv_spec hr hρ'
  have hts := γ.timer_st_le r s k
  have hst := γ.st_timer r ha'
  rw [hp] at hst
  have hle : γ.timer r ρ' ≤ s + γ.net.U k i := by simp only at hU; omega
  have hLpos := γ.net.one_le_L k i hc
  have hρ'eq : ρ' = (i, γ.st r (γ.timer r ρ') i) := Prod.ext hp hst.symm
  refine ⟨(HB.of_recv hρ').trans ?_, ?_⟩
  · rw [hρ'eq]
    exact HB.of_local (γ.appears_st r _ _) (γ.appears_st r _ _) rfl (γ.timer_mono r hle i)
  · refine hist_ne_nil_mono ?_ hle
    rw [hst]
    exact (γ.timer_pos_iff r ha').1 (by simp only at hL; omega)

theorem active_congr {r' : Sched P S E} {s : ℕ} {k : P} (h1 : γ.st r' s k = γ.st r s k)
    (h2 : γ.st r' (s - 1) k = γ.st r (s - 1) k) : γ.Active r' k s ↔ γ.Active r k s := by
  simp only [Active, ActiveH, h1, h2]

/-- In the slow run a process is activated only if it has already been activated in `r`. -/
theorem slowRun_active (hF : γ.IsFFIP) (hr : γ.Valid r) (σ : BNode P S M E) :
    ∀ s k, γ.Active (γ.slowRun r σ) k s → (γ.st r s k).hist ≠ [] := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro k ha
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by have := ha.1; omega⟩
  rw [active_succ_iff] at ha
  by_cases hm : (γ.batch (γ.slowRun r σ) t k).msgs = ∅
  · have he : (γ.batch (γ.slowRun r σ) t k).ext ≠ ∅ := fun he => ha ⟨hm, he⟩
    rw [batch_ext] at he
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 he
    have he' := (slowRun_mem_ext he).1
    refine hist_ne_nil_of_active ((γ.active_succ_iff r t k).2 fun h => ?_)
    rw [batch_ext] at h
    rw [h.2] at he'
    simp at he'
  · obtain ⟨⟨k', mk⟩, hmem⟩ := Finset.nonempty_iff_ne_empty.2 hm
    rw [mem_batch_msgs] at hmem
    obtain ⟨s', hs', ha', hc, hd, -⟩ := hmem
    simp only [slowRun] at hd
    split_ifs at hd with hcond
    · obtain ⟨_, -, -, hact⟩ := mem_batch_of_sends hr hcond.1
      rw [hd] at hact
      exact hist_ne_nil_of_active hact
    · have := (flood_bound hF hr (ih s' hs' k' ha') hc).2
      rwa [hd] at this

/-- **The slow run preserves the past of `σ`** (the main claim in the proof of Lemma 4): if
`(i, r_i(m))` is in the past of `σ` in `r`, then `r'_i(m) = r_i(m)`. -/
theorem slowRun_st (hF : γ.IsFFIP) (hr : γ.Valid r) (σ : BNode P S M E) :
    ∀ m i, γ.HB r (i, γ.st r m i) σ → γ.st (γ.slowRun r σ) m i = γ.st r m i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i hp
  rcases m with _ | t
  · rfl
  have ht : γ.st (γ.slowRun r σ) t i = γ.st r t i := ih t (by omega) i (HB_st_of_le hp (by omega))
  rw [st_succ, st_succ, ht]
  congr 1
  refine Batch.ext' ?_ ?_
  · ext ⟨k, mk⟩
    simp only [mem_batch_msgs]
    -- equal states and activity at past times `s ≤ t`
    have hpast : ∀ s ≤ t, γ.HB r (k, γ.st r s k) σ →
        γ.st (γ.slowRun r σ) s k = γ.st r s k ∧
          (γ.Active (γ.slowRun r σ) k s ↔ γ.Active r k s) := by
      intro s hs hps
      have e1 := ih s (by omega) k hps
      exact ⟨e1, active_congr e1 (ih (s - 1) (by omega) k (HB_st_of_le hps (by omega)))⟩
    constructor
    · rintro ⟨s, hs, ha', hc, hd, hm⟩
      simp only [slowRun] at hd
      split_ifs at hd with hcond
      · rw [(hpast s (by omega) hcond.2.1).1] at hm
        exact ⟨s, hs, hcond.1.1, hc, hd, hm⟩
      · exfalso
        apply hcond
        obtain ⟨hHB, -⟩ := flood_bound hF hr (slowRun_active hF hr σ s k ha') hc
        rw [hd] at hHB
        have hps := hHB.trans hp
        obtain ⟨e1, eA⟩ := hpast s (by omega) hps
        have hsend : γ.Sends r k s i := ⟨eA.1 ha', hc, hF.2 _ _ _ hc⟩
        have hb := hr.bounds k s i hsend
        exact ⟨hsend, hps, HB_st_of_le hp (by omega)⟩
    · rintro ⟨s, hs, ha, hc, hd, hm⟩
      have hsend : γ.Sends r k s i := ⟨ha, hc, by rw [hm]; rfl⟩
      have hrecv : γ.recv r (k, γ.st r s k) i = some (i, γ.st r (t + 1) i) := by
        rw [recv_eq_some]
        simp only [γ.timer_eq_of_active r ha]
        exact ⟨hsend, by rw [hd]⟩
      have hps := (HB.of_recv hrecv).trans hp
      obtain ⟨e1, eA⟩ := hpast s (by omega) hps
      refine ⟨s, hs, eA.2 ha, hc, ?_, by rw [e1]; exact hm⟩
      simp only [slowRun, hsend, hps, hd, hp, and_self, ite_true]
  · simp only [batch_ext, slowRun, hp, ite_true]

/-- The slow run is indistinguishable from `r` at every node of the past of `σ`. -/
theorem slowRun_appears (hF : γ.IsFFIP) (hr : γ.Valid r) {σ τ : BNode P S M E}
    (h : γ.HB r τ σ) : γ.appears (γ.slowRun r σ) τ := by
  have ha := (HB.appears h).1
  refine ⟨γ.timer r τ, ?_⟩
  have hst := γ.st_timer r ha
  rw [slowRun_st hF hr σ _ _ (by rw [hst]; exact h), hst]

/-- **Lemma 4.** Let `P` be an FFIP that implements `Late⟨a --x--> b⟩` or `Early⟨b --x--> a⟩`.
If `B` performs `b` at `σ` in `r ∈ R(P, γ)`, then there is a node `σC` of `r` at which `C` sends
a "go" message to `A` with `σC ⇝_r σ`. -/
theorem lemma4 (hF : γ.IsFFIP) {T : CoordTask P S M E} {x : ℤ}
    (hI : γ.ImplementsLate T x ∨ γ.ImplementsEarly T x) (hr : γ.Valid r) {σ : BNode P S M E}
    (hσ : γ.Performs r T σ) : ∃ σC, γ.GoNode r T σC ∧ γ.HB r σC σ := by
  set r' := γ.slowRun r σ
  have hr' : γ.Valid r' := slowRun_valid hr σ
  have hσ' : γ.Performs r' T σ := ⟨slowRun_appears hF hr (HB.refl hσ.1), hσ.2⟩
  obtain ⟨σC, hgo⟩ : ∃ σC, γ.GoNode r' T σC := by
    rcases hI with hI | hI
    · obtain ⟨σC, h, -⟩ := hI r' hr' σ hσ'
      exact ⟨σC, h⟩
    · obtain ⟨σC, h, -⟩ := hI r' hr' σ hσ'
      exact ⟨σC, h⟩
  obtain ⟨hext, -⟩ := hgo.mem_ext
  obtain ⟨-, hp⟩ := slowRun_mem_ext hext
  have hst := γ.st_timer r' hgo.1
  rw [hgo.2.1, slowRun_st hF hr σ _ _ hp] at hst
  have hσC : σC = (T.C, γ.st r (γ.timer r' σC) T.C) := Prod.ext hgo.2.1 hst.symm
  refine ⟨σC, ⟨?_, hgo.2⟩, ?_⟩
  · rw [hσC]; exact γ.appears_st r _ _
  · rw [hσC]; exact hp

/-- **Theorem 3 (`Late`).** Let `P` be an FFIP implementing `Late⟨a --x--> b⟩`. If `C` sends "go"
to `A` at `σC` in `r` and `B` performs `b` at `σ` in `r`, then `(R, r) ⊨ K_σ(σC · A --x--> σ)`. -/
theorem thm3_late (hF : γ.IsFFIP) {T : CoordTask P S M E} {x : ℤ} (hI : γ.ImplementsLate T x)
    (hr : γ.Valid r) {σC σ : BNode P S M E} (hC : γ.GoNode r T σC) (hσ : γ.Performs r T σ) :
    γ.Knows σ (fun r' => γ.Prec r' (T.aNode σC) x (GNode.ofB σ)) := by
  intro r' hr' hσ'
  obtain ⟨σC', hgo', hprec⟩ := hI r' hr' σ ⟨hσ', hσ.2⟩
  obtain ⟨σC'', hgo'', hHB⟩ := lemma4 hF (Or.inl hI) hr hσ
  obtain rfl := GoNode.unique hr hgo'' hC
  have hHB' := HB.transfer hF.1 hr hr' hHB hσ'
  obtain rfl := GoNode.unique hr' hgo' ⟨(HB.appears hHB').1, hC.2⟩
  exact hprec

/-- **Theorem 3 (`Early`).** Let `P` be an FFIP implementing `Early⟨b --x--> a⟩`. If `C` sends
"go" to `A` at `σC` in `r` and `B` performs `b` at `σ` in `r`, then
`(R, r) ⊨ K_σ(σ --x--> σC · A)`. -/
theorem thm3_early (hF : γ.IsFFIP) {T : CoordTask P S M E} {x : ℤ} (hI : γ.ImplementsEarly T x)
    (hr : γ.Valid r) {σC σ : BNode P S M E} (hC : γ.GoNode r T σC) (hσ : γ.Performs r T σ) :
    γ.Knows σ (fun r' => γ.Prec r' (GNode.ofB σ) x (T.aNode σC)) := by
  intro r' hr' hσ'
  obtain ⟨σC', hgo', hprec⟩ := hI r' hr' σ ⟨hσ', hσ.2⟩
  obtain ⟨σC'', hgo'', hHB⟩ := lemma4 hF (Or.inr hI) hr hσ
  obtain rfl := GoNode.unique hr hgo'' hC
  have hHB' := HB.transfer hF.1 hr hr' hHB hσ'
  obtain rfl := GoNode.unique hr' hgo' ⟨(HB.appears hHB').1, hC.2⟩
  exact hprec

end Sys

end Podc.ZigzagCausality
