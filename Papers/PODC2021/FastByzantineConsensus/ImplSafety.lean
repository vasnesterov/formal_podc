import Papers.PODC2021.FastByzantineConsensus.Implementation

/-!
# The concrete protocol: unforgeability, refinement, agreement

* `reachable_absState`: every time of every unforgeable run is a reachable state of the abstract
  transition system of `Protocol.lean` (refinement).
* `algo_agreement`: agreement, from `Protocol.consistency`.
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus.Impl

open Cslib.Byzantine.PartialSync FastByzantineConsensus.Protocol Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {pr : Params P} {L δ : ℕ}

/-! ### Refinement into the abstract transition system -/

section Refinement

theorem State.ext' {s t : State P V} (hE : s.E = t.E) (hl : s.loc = t.loc) : s = t := by
  cases s; cases t; cases hE; cases hl; rfl

variable (B : Finset P) (inp : P → V)

/-- Simulation relation between an abstract state `s` and the concrete local state `ls` of a
correct process `q` in view `v`: the known tokens of `q` are emitted, all `q`-signed emitted tokens
are known to `q`, and the abstract local state of `q` is `(v, ballot, cc)`. -/
structure Rel (q : P) (v : ℕ) (s : State P V) (ls : LState P V) : Prop where
  sub : (↑ls.known : Set (Tok P V)) ⊆ s.E
  own : ∀ k ∈ s.E, k.signer = q → k ∈ ls.known
  loc : s.loc q = ⟨v, ls.ballot, ls.cc⟩

variable (pr) in
/-- An action `f` of `q` (taking it from view `v` to view `v'`) is simulated by abstract steps of
`q` that emit exactly the new tokens of `f`. -/
def Sim (q : P) (v v' : ℕ) (f : LState P V → LState P V) : Prop :=
  ∀ s ls, Reachable pr B inp s → Rel q v s ls →
    ∃ s', Reachable pr B inp s' ∧ Rel q v' s' (f ls) ∧ s'.E = s.E ∪ ↑(f ls).known ∧
      ∀ r ≠ q, s'.loc r = s.loc r

variable {B inp}

theorem Sim.comp {q : P} {v v' v'' : ℕ} {f g : LState P V → LState P V}
    (hf : Sim pr B inp q v' v'' f) (hg : Sim pr B inp q v v' g) (hgr : Grows q f) :
    Sim pr B inp q v v'' (f ∘ g) := by
  intro s ls hs hr
  obtain ⟨s₁, hs₁, hr₁, hE₁, hl₁⟩ := hg s ls hs hr
  obtain ⟨s₂, hs₂, hr₂, hE₂, hl₂⟩ := hf s₁ (g ls) hs₁ hr₁
  refine ⟨s₂, hs₂, hr₂, ?_, fun r hr => (hl₂ r hr).trans (hl₁ r hr)⟩
  rw [hE₂, hE₁, Set.union_assoc]
  congr 1
  exact Set.union_eq_right.2 (coe_subset.2 (hgr (g ls)).1)

theorem sim_step {q : P} {v v' : ℕ} {s : State P V} {ls ls' : LState P V}
    (hs : Reachable pr B inp s) (hr : Rel q v s ls) (tk : Tok P V) (htk : tk.signer = q)
    (hk : ls'.known = insert tk ls.known) (l' : P → Local V)
    (hl'q : l' q = ⟨v', ls'.ballot, ls'.cc⟩) (hl' : ∀ r ≠ q, l' r = s.loc r)
    (hstep : Step pr B inp s ⟨insert tk s.E, l'⟩) :
    ∃ s', Reachable pr B inp s' ∧ Rel q v' s' ls' ∧ s'.E = s.E ∪ ↑ls'.known ∧
      ∀ r ≠ q, s'.loc r = s.loc r := by
  refine ⟨⟨insert tk s.E, l'⟩, hs.tail hstep, ⟨?_, ?_, hl'q⟩, ?_, hl'⟩
  · rw [hk, coe_insert]
    exact Set.insert_subset_insert hr.sub
  · intro k hk' hks
    rw [hk]
    rcases hk' with rfl | hk'
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (hr.own k hk' hks)
  · rw [hk, coe_insert]
    ext k
    simp only [Set.mem_insert_iff, Set.mem_union, mem_coe]
    constructor
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · rintro (h | h | h)
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr (hr.sub (mem_coe.2 h))

theorem sim_nop {q : P} {v : ℕ} {s : State P V} {ls ls' : LState P V}
    (hs : Reachable pr B inp s) (hr : Rel q v s ls) (h : ls' = ls) :
    ∃ s', Reachable pr B inp s' ∧ Rel q v s' ls' ∧ s'.E = s.E ∪ ↑ls'.known ∧
      ∀ r ≠ q, s'.loc r = s.loc r := by
  subst h
  exact ⟨s, hs, hr, (Set.union_eq_left.2 hr.sub).symm, fun _ _ => rfl⟩

theorem sim_vote {q : P} (hq : q ∉ B) (old : LState P V) {v : ℕ} (hv : old.clock / L ≤ v) :
    Sim pr B inp q (old.clock / L) v (actVote L q old v) := by
  intro s ls hs hr
  unfold actVote
  split_ifs with hne
  · have hlt : (s.loc q).view < v := by rw [hr.loc]; exact lt_of_le_of_ne hv (Ne.symm hne)
    have hst := Step.enterView (pr := pr) (inp := inp) s q v hq hlt
    rw [hr.loc] at hst
    refine sim_step hs hr _ rfl rfl _ ?_ ?_ hst
    · simp
    · intro r hr'; exact Function.update_of_ne hr' _ _
  · rw [show v = old.clock / L from not_not.1 hne]
    exact sim_nop hs hr rfl

theorem sel_leaderChoice {K : Finset (Tok P V)} {v : ℕ} {x₀ : V} (h : ∃ x, Sel pr K v x) :
    Sel pr K v (leaderChoice pr K v x₀) := by
  unfold leaderChoice
  split_ifs with h1
  · exact h1
  · exact Classical.choose_spec h

theorem sim_leaderCA {q : P} (hq : q ∉ B) (v : ℕ) :
    Sim pr B inp q v v (actLeaderCA pr q v) := by
  intro s ls hs hr
  unfold actLeaderCA
  split_ifs with hg
  · obtain ⟨-, -, -, hex⟩ := hg
    obtain ⟨S, bal, cc, hS, hsel⟩ := sel_leaderChoice (x₀ := ls.input) hex
    exact sim_step hs hr _ rfl rfl s.loc hr.loc (fun _ _ => rfl)
      (Step.certAck s q _ v hq S bal cc (ValidVotes.mono pr hr.sub hS) hsel)
  · exact sim_nop hs hr rfl

theorem sim_verify {q : P} (hq : q ∉ B) (v : ℕ) :
    Sim pr B inp q v v (actVerify pr q v) := by
  intro s ls hs hr
  unfold actVerify
  split_ifs with hg
  · obtain ⟨-, -, S, bal, cc, hS, hsel⟩ := Classical.choose_spec hg
    exact sim_step hs hr _ rfl rfl s.loc hr.loc (fun _ _ => rfl)
      (Step.certAck s q _ v hq S bal cc (ValidVotes.mono pr hr.sub hS) hsel)
  · exact sim_nop hs hr rfl

theorem sim_propose {q : P} (hq : q ∉ B) (v : ℕ) :
    Sim pr B inp q v v (actPropose pr q v) := by
  intro s ls hs hr
  unfold actPropose
  split_ifs with hg
  · have hview : (s.loc q).view = v := by rw [hr.loc]
    have hst := Step.propose (pr := pr) (B := B) (inp := inp) s q
      (Classical.choose hg.2.2.2) hq (by rw [hview]; exact hg.1)
      (by rw [hview]; intro y hy; exact hg.2.2.1 y (hr.own _ hy rfl))
      (Or.inr ⟨by rw [hview]; exact hg.2.1,
        by rw [hview]; exact Certified.mono pr hr.sub (Classical.choose_spec hg.2.2.2)⟩)
    rw [hview] at hst
    exact sim_step hs hr _ rfl rfl s.loc hr.loc (fun _ _ => rfl) hst
  · exact sim_nop hs hr rfl

theorem sim_ack {q : P} (hq : q ∉ B) (v : ℕ) :
    Sim pr B inp q v v (actAck pr q v) := by
  intro s ls hs hr
  unfold actAck
  split_ifs with hg
  · have hview : (s.loc q).view = v := by rw [hr.loc]
    obtain ⟨hp, hc⟩ := Classical.choose_spec hg.2
    have hst := Step.ack (pr := pr) (B := B) (inp := inp) s q (Classical.choose hg.2) hq
      (by rw [hview]; exact hr.sub hp) (by rw [hview]; exact hc.imp id (Certified.mono pr hr.sub))
      (by rw [hview]; intro y hy; exact hg.1 y (hr.own _ hy rfl))
    rw [hview] at hst
    refine sim_step hs hr _ rfl rfl _ ?_ ?_ hst
    · simp [hr.loc]
    · intro r hr'; exact Function.update_of_ne hr' _ _
  · exact sim_nop hs hr rfl

theorem sim_commit {q : P} (hq : q ∉ B) (v : ℕ) :
    Sim pr B inp q v v (actCommit pr q v) := by
  intro s ls hs hr
  unfold actCommit
  split_ifs with hg
  · have hview : (s.loc q).view = v := by rw [hr.loc]
    obtain ⟨hcc, -⟩ := Classical.choose_spec hg
    have hst := Step.commit (pr := pr) (B := B) (inp := inp) s q (Classical.choose hg) hq
      (by rw [hview]; exact HasCC.mono pr hr.sub hcc)
    rw [hview] at hst
    refine sim_step hs hr _ rfl rfl _ ?_ ?_ hst
    · simp [hr.loc]
    · intro r hr'; exact Function.update_of_ne hr' _ _
  · exact sim_nop hs hr rfl

/-- The whole action sequence of a step of a correct process is simulated. -/
theorem sim_actions {q : P} (hq : q ∉ B) (old : LState P V) :
    Sim pr B inp q (old.clock / L) ((old.clock + 1) / L)
      (actCommit pr q ((old.clock + 1) / L) ∘ actAck pr q ((old.clock + 1) / L) ∘
        actPropose pr q ((old.clock + 1) / L) ∘ actVerify pr q ((old.clock + 1) / L) ∘
        actLeaderCA pr q ((old.clock + 1) / L) ∘ actVote L q old ((old.clock + 1) / L)) :=
  Sim.comp (sim_commit hq _) (Sim.comp (sim_ack hq _) (Sim.comp (sim_propose hq _)
    (Sim.comp (sim_verify hq _) (Sim.comp (sim_leaderCA hq _)
      (sim_vote hq old (Nat.div_le_div_right (Nat.le_succ _))) (grows_leaderCA q _))
      (grows_verify q _)) (grows_propose q _)) (grows_ack q _)) (grows_commit q _)

/-- Emitting a finite set of Byzantine-signed tokens. -/
theorem reach_byz {s : State P V} (hs : Reachable pr B inp s) (F : Finset (Tok P V))
    (hF : ∀ k ∈ F, k.signer ∈ B) : Reachable pr B inp ⟨s.E ∪ ↑F, s.loc⟩ := by
  induction F using Finset.induction_on with
  | empty =>
    rw [show (⟨s.E ∪ ↑(∅ : Finset (Tok P V)), s.loc⟩ : State P V) = s from
      State.ext' (by simp) rfl]
    exact hs
  | insert a F ha ih =>
    have h1 := ih (fun k hk => hF k (mem_insert_of_mem hk))
    have h2 := h1.tail (Step.byz _ a (hF a (mem_insert_self a F)))
    have he : (⟨s.E ∪ ↑(insert a F), s.loc⟩ : State P V) = ⟨insert a (s.E ∪ ↑F), s.loc⟩ := by
      refine State.ext' ?_ rfl
      ext k
      simp only [coe_insert, Set.mem_union, Set.mem_insert_iff, mem_coe]
      tauto
    rw [he]
    exact h2

end Refinement

/-- A token known to a correct process `c` at `τ + 1` was known to a correct process at `τ`, or is
Byzantine-signed, or is signed by `c`. -/
theorem known_succ_cases (R : Run P (Tok P V) V) (hRa : R.AuthValid auth (algo pr L)) {c : P}
    (hc : c ∉ R.faulty) {τ : ℕ} {k : Tok P V} (hk : k ∈ (R.st (algo pr L) (τ + 1) c).known) :
    (∃ c' ∉ R.faulty, k ∈ (R.st (algo pr L) τ c').known) ∨ k.signer ∈ R.faulty ∨
      k.signer = c := by
  rcases mem_known_succ R hk with h | ⟨r, h⟩ | h
  · exact Or.inl ⟨c, hc, h⟩
  · rcases recv_origin hRa hc h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inl h'
  · exact Or.inr (Or.inr h)

theorem reachable_absState_zero (R : Run P (Tok P V) V) :
    Reachable pr R.faulty R.inp (absState pr L R 0) := by
  have hknown : ∀ q, (R.st (algo pr L) 0 q).known =
      if pr.leader 0 = q then {Tok.propose q (R.inp q) 0} else ∅ := fun q => rfl
  have hloc : (absState pr L R 0).loc = (init : State P V).loc := by
    funext r
    simp [absState, init, algo]
  by_cases hl : pr.leader 0 ∈ R.faulty
  · have : absState pr L R 0 = init := by
      refine State.ext' ?_ hloc
      ext k
      simp only [absState, Set.mem_ofPred_eq, hknown, init, Set.mem_empty_iff_false, iff_false]
      rintro ⟨q, hq, hk⟩
      split_ifs at hk with h
      · exact hq (h ▸ hl)
      · simp at hk
    rw [this]
    exact Relation.ReflTransGen.refl
  · have hst := Step.propose (pr := pr) (B := R.faulty) (inp := R.inp) init (pr.leader 0)
      (R.inp (pr.leader 0)) hl rfl (fun y h => h) (Or.inl ⟨rfl, rfl⟩)
    have : absState pr L R 0 =
        ⟨insert (Tok.propose (pr.leader 0) (R.inp (pr.leader 0)) 0) (init : State P V).E,
          (init : State P V).loc⟩ := by
      refine State.ext' ?_ hloc
      ext k
      simp only [absState, Set.mem_ofPred_eq, hknown, init, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false]
      constructor
      · rintro ⟨q, hq, hk⟩
        split_ifs at hk with h
        · rw [mem_singleton] at hk; rw [hk, h]
        · simp at hk
      · rintro rfl
        exact ⟨pr.leader 0, hl, by simp⟩
    rw [this]
    exact Relation.ReflTransGen.single hst

theorem reachable_absState_succ (R : Run P (Tok P V) V) (hRa : R.AuthValid auth (algo pr L))
    (τ : ℕ) (h : Reachable pr R.faulty R.inp (absState pr L R τ)) :
    Reachable pr R.faulty R.inp (absState pr L R (τ + 1)) := by
  classical
  set C : Finset P := univ.filter (· ∉ R.faulty) with hC
  set Byz : Finset (Tok P V) :=
    (C.biUnion fun q => (R.st (algo pr L) (τ + 1) q).known).filter (·.signer ∈ R.faulty) with hByz
  let st' : Finset P → State P V := fun Q =>
    ⟨(absState pr L R τ).E ∪ ↑Byz ∪ {k | ∃ q ∈ Q, k ∈ (R.st (algo pr L) (τ + 1) q).known},
      fun r => if r ∈ Q then ⟨(τ + 1) / L, (R.st (algo pr L) (τ + 1) r).ballot,
        (R.st (algo pr L) (τ + 1) r).cc⟩ else (absState pr L R τ).loc r⟩
  -- phase (a): Byzantine tokens
  have h0 : Reachable pr R.faulty R.inp (st' ∅) := by
    have := reach_byz h Byz (fun k hk => (mem_filter.1 hk).2)
    have he : st' ∅ = ⟨(absState pr L R τ).E ∪ ↑Byz, (absState pr L R τ).loc⟩ := by
      refine State.ext' ?_ ?_
      · ext k; simp [st']
      · funext r; simp [st']
    rw [he]; exact this
  -- phase (b): correct processes one at a time
  have hQ : ∀ Q : Finset P, Q ⊆ C → Reachable pr R.faulty R.inp (st' Q) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty => intro _; exact h0
    | insert q Q hqQ ih =>
      intro hsub
      have hs := ih ((subset_insert q Q).trans hsub)
      have hq : q ∉ R.faulty := (mem_filter.1 (hsub (mem_insert_self q Q))).2
      have hQC : ∀ r ∈ Q, r ∉ R.faulty := fun r hr => (mem_filter.1 (hsub (mem_insert_of_mem hr))).2
      set old := R.st (algo pr L) τ q with hold
      set s1 : LState P V := ⟨old.clock + 1, old.input,
        old.known ∪ (univ.biUnion fun r => (R.inbox (algo pr L) q τ r).toFinset),
        old.ballot, old.cc⟩ with hs1
      have hrel : Rel q (old.clock / L) (st' Q) s1 := by
        refine ⟨?_, ?_, ?_⟩
        · intro k hk
          rcases mem_union.1 (mem_coe.1 hk) with hk | hk
          · exact Or.inl (Or.inl ⟨q, hq, hk⟩)
          · obtain ⟨r, -, hr⟩ := mem_biUnion.1 hk
            have hr' := List.mem_toFinset.1 hr
            rcases recv_origin hRa hq hr' with h' | h'
            · exact Or.inl (Or.inr (mem_coe.2 (mem_filter.2
                ⟨mem_biUnion.2 ⟨q, mem_filter.2 ⟨mem_univ _, hq⟩, mem_known_of_inbox R hr'⟩, h'⟩)))
            · exact Or.inl (Or.inl h')
        · rintro k ((⟨c, hc, hk⟩ | hk) | ⟨r, hrQ, hk⟩) hks
          · exact mem_union_left _ (known_signed hRa hq hc hk hks)
          · exact absurd (hks ▸ (mem_filter.1 (mem_coe.1 hk)).2) hq
          · rcases known_succ_cases R hRa (hQC r hrQ) hk with ⟨c, hc, hk'⟩ | h' | h'
            · exact mem_union_left _ (known_signed hRa hq hc hk' hks)
            · exact absurd (hks ▸ h') hq
            · exact absurd (h'.symm.trans hks ▸ hrQ) hqQ
        · simp [st', hqQ, absState, hq, hold, s1]
      obtain ⟨s', hs', hr', hE', hl'⟩ := sim_actions hq old (st' Q) s1 hs hrel
      have hfin : (actCommit pr q ((old.clock + 1) / L) ∘ actAck pr q ((old.clock + 1) / L) ∘
          actPropose pr q ((old.clock + 1) / L) ∘ actVerify pr q ((old.clock + 1) / L) ∘
          actLeaderCA pr q ((old.clock + 1) / L) ∘ actVote L q old ((old.clock + 1) / L)) s1 =
          R.st (algo pr L) (τ + 1) q := by
        rw [st_succ_eq, stepFn_eq]
      rw [hfin] at hr' hE'
      have hclk : old.clock = τ := st_clock R τ q
      rw [hclk] at hr'
      have he : s' = st' (insert q Q) := by
        refine State.ext' ?_ ?_
        · rw [hE']
          ext k
          simp only [st', Set.mem_union, Set.mem_ofPred_eq, mem_coe, mem_insert,
            exists_eq_or_imp]
          rw [or_assoc, or_comm (a := ∃ _ ∈ Q, _)]
        · funext r
          by_cases hrq : r = q
          · subst hrq
            rw [hr'.loc]
            simp [st']
          · rw [hl' r hrq]
            simp [st', hrq]
      rw [← he]; exact hs'
  have he : st' C = absState pr L R (τ + 1) := by
    refine State.ext' ?_ ?_
    · ext k
      simp only [st', absState, Set.mem_union, Set.mem_ofPred_eq, mem_coe, hByz, mem_filter,
        mem_biUnion, hC, mem_univ, true_and]
      constructor
      · rintro ((⟨c, hc, hk⟩ | ⟨⟨c, hc, hk⟩, -⟩) | ⟨c, hc, hk⟩)
        · exact ⟨c, hc, known_mono R (Nat.le_succ τ) c hk⟩
        · exact ⟨c, hc, hk⟩
        · exact ⟨c, hc, hk⟩
      · rintro ⟨c, hc, hk⟩
        exact Or.inr ⟨c, hc, hk⟩
    · funext r
      by_cases hr : r ∈ R.faulty <;> simp [st', absState, hr, hC]
  rw [← he]
  exact hQ C subset_rfl

/-- **Refinement.** Every time of every unforgeable run corresponds to a reachable state of the
abstract transition system of `Protocol.lean`. -/
theorem reachable_absState (hL : 0 < L) (R : Run P (Tok P V) V)
    (hRa : R.AuthValid auth (algo pr L)) (τ : ℕ) :
    Reachable pr R.faulty R.inp (absState pr L R τ) := by
  induction τ with
  | zero => exact reachable_absState_zero R
  | succ τ ih => exact reachable_absState_succ R hRa τ ih

/-- Decisions are monotone in the set of tokens. -/
theorem decided_mono {E E' : Set (Tok P V)} (h : E ⊆ E') {x : V} (hx : Decided pr E x) :
    Decided pr E' x := by
  obtain ⟨v, hv⟩ := hx
  exact ⟨v, hv.imp (fun h1 => h1.trans (card_le_card (ackers_mono h x v)))
    (fun h1 => h1.trans (card_le_card (committers_mono h x v)))⟩

/-- A decision of the concrete protocol is backed by a decision quorum in its known tokens. -/
theorem decided_of_decide {ls : LState P V} {c : P} {x : V}
    (h : (algo pr L).decide c ls = some x) : Decided pr (↑ls.known : Set (Tok P V)) x := by
  simp only [algo] at h
  split_ifs at h with hd
  · rw [← Option.some.inj h]
    exact Classical.choose_spec hd

/-- **Agreement** (Theorem A.4 in the concrete model). -/
theorem algo_agreement (hL : 0 < L) (ht : 1 ≤ pr.t) (htf : pr.t ≤ pr.f)
    (hn : 3 * pr.f + 2 * pr.t - 1 ≤ Fintype.card P) (R : Run P (Tok P V) V)
    (hR : R.Valid pr.f δ) (hRa : R.AuthValid auth (algo pr L)) :
    ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w, R.Decides (algo pr L) p v →
      R.Decides (algo pr L) q w → v = w := by
  intro p hp q hq v w ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩
  have hsub : ∀ c ∉ R.faulty, ∀ τ ≤ max τ₁ τ₂,
      (↑(R.st (algo pr L) τ c).known : Set (Tok P V)) ⊆ (absState pr L R (max τ₁ τ₂)).E :=
    fun c hc τ hτ k hk => ⟨c, hc, known_mono R hτ c hk⟩
  exact consistency pr R.faulty R.inp hR.card_faulty ht htf hn
    (reachable_absState hL R hRa (max τ₁ τ₂))
    (decided_mono (hsub p hp τ₁ (le_max_left _ _)) (decided_of_decide h₁))
    (decided_mono (hsub q hq τ₂ (le_max_right _ _)) (decided_of_decide h₂))

end FastByzantineConsensus.Impl
