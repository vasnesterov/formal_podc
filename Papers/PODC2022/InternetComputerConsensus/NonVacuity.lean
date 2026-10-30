import Papers.PODC2022.InternetComputerConsensus.Liveness

/-!
# Non-vacuity of the liveness hypotheses

A single honest party (`P = Unit`, `t = 0`, no corrupt party), payloads `Unit`, rank `0`,
`Δprop ≡ 0`, `Δntry 0 = 1`, `Δntry r = 2` for `r ≥ 1`. The run repeats, for rounds
`r = 1, 2, …`, the cycle: beacon, propose, tick, echo (notarization share), finish, finalize.
Round `r` is entered at time `r - 1`.

`liveHyp_nonvacuous`: this run satisfies `LiveHyp` for `k = 2`, `T = 1`, `δ = 1`, leader `()`,
and the state `σ 20` (time `3`) satisfies all hypotheses of `liveness`.
-/

namespace Podc.InternetComputerConsensus.NonVacuity

open Finset Cslib.Byzantine Podc.InternetComputerConsensus

set_option linter.unusedSectionVars false

/-- The parameters. -/
def πU : Params Unit where
  t := 0
  rank := fun _ _ => 0
  Δprop := fun _ => 0
  Δntry := fun r => if r = 0 then 1 else 2

/-- The (empty) corrupt set. -/
abbrev FU : Finset Unit := ∅

/-- The block of round `r` of the run. -/
def canon : ℕ → Block Unit Unit
  | 0 => .root
  | r + 1 => .mk (r + 1) () (canon r) ()

@[simp] theorem canon_round : ∀ r, (canon r).round = r
  | 0 => rfl
  | _ + 1 => rfl

@[simp] theorem rank_eq (k : ℕ) (q : Unit) : πU.rank k q = 0 := rfl
@[simp] theorem t_eq : πU.t = 0 := rfl
@[simp] theorem Δntry_zero : πU.Δntry 0 = 1 := rfl
@[simp] theorem Δprop_eq (r : ℕ) : πU.Δprop r = 0 := rfl

@[simp] theorem rk_eq (B : Block Unit Unit) : B.rk πU.rank = 0 := by cases B <;> rfl

/-- Certificates of the single party. -/
theorem cert_one {X : Type} {sg : Unit → X → Prop} {x : X} (h : sg () x) {Q : ℕ} (hQ : Q ≤ 1) :
    Certified sg Q x :=
  hQ.trans (Finset.card_pos.2 ⟨(), mem_signers.2 h⟩)

theorem exists_of_cert {X : Type} {sg : Unit → X → Prop} {x : X}
    (h : Certified sg (Fintype.card Unit - πU.t) x) : sg () x := by
  obtain ⟨q, -, hq⟩ := h.exists_correct_signer (F := FU) (f := 0) (by simp) (by simp [πU])
  exact hq

/-! ### The run -/

def ph0 (s : GState Unit Unit) : GState Unit Unit :=
  actState s () ((s.loc ()).start s.now) {Msg.beacon ((s.loc ()).round + 1) ()}

def ph1 (s : GState Unit Unit) : GState Unit Unit :=
  actState s () { s.loc () with proposed := true }
    {Msg.block (.mk (s.loc ()).round () (canon ((s.loc ()).round - 1)) ()),
      Msg.auth (.mk (s.loc ()).round () (canon ((s.loc ()).round - 1)) ()),
      Msg.notar (canon ((s.loc ()).round - 1))}

def ph2 (s : GState Unit Unit) : GState Unit Unit := { s with now := s.now + 1 }

def ph3 (s : GState Unit Unit) : GState Unit Unit :=
  actState s () { s.loc () with N := insert (canon (s.loc ()).round) (s.loc ()).N }
    {m | ((canon (s.loc ()).round).rk πU.rank ≠ πU.rank (s.loc ()).round () ∧
          (m = Msg.block (canon (s.loc ()).round) ∨ m = Msg.auth (canon (s.loc ()).round) ∨
            m = Msg.notar (canon (s.loc ()).round).parent)) ∨
        m = Msg.notarShare (canon (s.loc ()).round) ()}

def ph4 (s : GState Unit Unit) : GState Unit Unit :=
  actState s () { s.loc () with round := (s.loc ()).round + 1, active := false }
    {m | m = Msg.notar (canon (s.loc ()).round) ∨
      ((s.loc ()).N ⊆ {canon (s.loc ()).round} ∧ m = Msg.finalShare (canon (s.loc ()).round) ())}

def ph5 (s : GState Unit Unit) : GState Unit Unit :=
  let L := s.loc ()
  let B := canon (L.round - 1)
  actState s () { L with kmax := B.round, out := L.out ++ B.chain.drop L.kmax } {Msg.final B}

def phase : ℕ → GState Unit Unit → GState Unit Unit
  | 0 => ph0
  | 1 => ph1
  | 2 => ph2
  | 3 => ph3
  | 4 => ph4
  | _ => ph5

/-- The run. -/
def σ : ℕ → GState Unit Unit
  | 0 => GState.init FU
  | i + 1 => phase (i % 6) (σ i)

theorem σ_succ (i : ℕ) : σ (i + 1) = phase (i % 6) (σ i) := rfl

theorem σ1 (m : ℕ) : σ (6 * m + 1) = ph0 (σ (6 * m)) := by
  rw [σ_succ, show 6 * m % 6 = 0 by omega]; rfl
theorem σ2 (m : ℕ) : σ (6 * m + 2) = ph1 (σ (6 * m + 1)) := by
  rw [σ_succ, show (6 * m + 1) % 6 = 1 by omega]; rfl
theorem σ3 (m : ℕ) : σ (6 * m + 3) = ph2 (σ (6 * m + 2)) := by
  rw [σ_succ, show (6 * m + 2) % 6 = 2 by omega]; rfl
theorem σ4 (m : ℕ) : σ (6 * m + 4) = ph3 (σ (6 * m + 3)) := by
  rw [σ_succ, show (6 * m + 3) % 6 = 3 by omega]; rfl
theorem σ5 (m : ℕ) : σ (6 * m + 5) = ph4 (σ (6 * m + 4)) := by
  rw [σ_succ, show (6 * m + 4) % 6 = 4 by omega]; rfl
theorem σ6 (m : ℕ) : σ (6 * (m + 1)) = ph5 (σ (6 * m + 5)) := by
  rw [show 6 * (m + 1) = 6 * m + 5 + 1 by ring, σ_succ, show (6 * m + 5) % 6 = 5 by omega]; rfl

/-- Certificate-type messages. -/
def IsCert : Msg Unit Unit → Prop
  | .notar _ => True
  | .notarShare _ _ => True
  | .final _ => True
  | .finalShare _ _ => True
  | _ => False

/-- The state at the start of round `m + 1`. -/
structure Good (m : ℕ) (s : GState Unit Unit) : Prop where
  now : s.now = m
  round : (s.loc ()).round = m + 1
  active : (s.loc ()).active = false
  kmax : (s.loc ()).kmax = m
  beacon : Msg.beacon (m + 1) () ∈ (s.loc ()).pool
  notarized : Notarized (s.loc ()).pool (canon m)
  bad : ∀ x ∈ (s.loc ()).pool, IsCert x → x.round ≤ m

theorem good_zero : Good 0 (σ 0) where
  now := rfl
  round := rfl
  active := rfl
  kmax := rfl
  beacon := by simp [σ, GState.init, LState.init]
  notarized := notarized_root _
  bad := by
    intro x hx hc
    simp only [σ, GState.init, LState.init, Set.mem_singleton_iff] at hx
    subst hx; exact hc.elim

/-- A party that has proposed in its round, whose echo timer has not elapsed and whose pool holds
no certificate-type message of its round or later, is settled. -/
theorem settled_of (s : GState Unit Unit) (ha : (s.loc ()).active = true)
    (hp : (s.loc ()).proposed = true) (ht : (s.loc ()).t0 (s.loc ()).round = s.now)
    (hbad : ∀ x ∈ (s.loc ()).pool, IsCert x → x.round < (s.loc ()).round)
    (hk : (s.loc ()).kmax + 1 = (s.loc ()).round) : Settled πU s () := by
  intro l M h
  cases h with
  | beacon h1 => rw [ha] at h1; cases h1
  | finish B _ hBr _ hBn =>
    rcases hBn with h | h
    · have := hbad _ h trivial; simp [Msg.round] at this; omega
    · have := hbad _ (exists_of_cert h) trivial; simp [Msg.round] at this; omega
  | propose _ _ _ h2 => rw [hp] at h2; cases h2
  | echoShare B _ _ _ _ _ h6 => rw [ht, rk_eq] at h6; simp [πU] at h6
  | echoDisq B _ _ _ _ _ h6 => rw [ht, rk_eq] at h6; simp [πU] at h6
  | final B _ hk' hf =>
    rcases hf with h | h
    · have := hbad _ h trivial; simp [Msg.round] at this; omega
    · have := hbad _ (exists_of_cert h) trivial; simp [Msg.round] at this; omega

theorem valid_canon_succ {pool : Set (Msg Unit Unit)} {m : ℕ}
    (h1 : Msg.block (canon (m + 1)) ∈ pool) (h2 : Msg.auth (canon (m + 1)) ∈ pool)
    (h3 : Notarized pool (canon m)) : Valid pool (canon (m + 1)) :=
  ⟨by simp, h1, h2, h3.1, h3.2⟩

section Cycle

variable {m : ℕ} (hG : Good m (σ (6 * m)))
include hG

theorem s1_loc : (σ (6 * m + 1)).loc () =
    { (σ (6 * m)).loc () with
      active := true,
      t0 := Function.update ((σ (6 * m)).loc ()).t0 (m + 1) m, N := ∅, D := ∅, proposed := false,
      pool := ((σ (6 * m)).loc ()).pool ∪ {Msg.beacon (m + 2) ()} } := by
  rw [σ1]; simp [ph0, LState.start, hG.round, hG.now]

theorem s1_now : (σ (6 * m + 1)).now = m := by rw [σ1]; simp [ph0, hG.now]

theorem s2_loc : (σ (6 * m + 2)).loc () =
    { (σ (6 * m)).loc () with
      active := true,
      t0 := Function.update ((σ (6 * m)).loc ()).t0 (m + 1) m, N := ∅, D := ∅, proposed := true,
      pool := ((σ (6 * m)).loc ()).pool ∪ {Msg.beacon (m + 2) ()} ∪
        {Msg.block (canon (m + 1)), Msg.auth (canon (m + 1)), Msg.notar (canon m)} } := by
  rw [σ2, ph1, actState_loc_self, s1_loc hG]
  simp [hG.round, canon]

theorem s2_now : (σ (6 * m + 2)).now = m := by rw [σ2]; simp [ph1, s1_now hG]

theorem s3_loc : (σ (6 * m + 3)).loc () = (σ (6 * m + 2)).loc () := by rw [σ3]; rfl
theorem s3_now : (σ (6 * m + 3)).now = m + 1 := by rw [σ3]; simp [ph2, s2_now hG]

theorem s4_loc : (σ (6 * m + 4)).loc () =
    { (σ (6 * m + 2)).loc () with
      N := {canon (m + 1)},
      pool := ((σ (6 * m + 2)).loc ()).pool ∪ {Msg.notarShare (canon (m + 1)) ()} } := by
  rw [σ4, ph3, actState_loc_self, s3_loc hG, s2_loc hG]
  simp only [hG.round]
  congr 1 <;> ext x <;> simp

theorem s4_now : (σ (6 * m + 4)).now = m + 1 := by rw [σ4]; simp [ph3, s3_now hG]

theorem s5_loc : (σ (6 * m + 5)).loc () =
    { (σ (6 * m + 4)).loc () with
      round := m + 2,
      active := false,
      pool := ((σ (6 * m + 4)).loc ()).pool ∪
        {Msg.notar (canon (m + 1)), Msg.finalShare (canon (m + 1)) ()} } := by
  rw [σ5, ph4, actState_loc_self]
  have hr : ((σ (6 * m + 4)).loc ()).round = m + 1 := by
    rw [s4_loc hG, s2_loc hG]; exact hG.round
  have hN : ((σ (6 * m + 4)).loc ()).N = {canon (m + 1)} := by rw [s4_loc hG]
  simp only [hr, hN]
  congr 1
  ext x; simp; tauto

theorem s5_now : (σ (6 * m + 5)).now = m + 1 := by rw [σ5]; simp [ph4, s4_now hG]

theorem s6_loc : (σ (6 * (m + 1))).loc () =
    { (σ (6 * m + 5)).loc () with
      kmax := m + 1,
      out := ((σ (6 * m + 5)).loc ()).out ++ (canon (m + 1)).chain.drop m,
      pool := ((σ (6 * m + 5)).loc ()).pool ∪ {Msg.final (canon (m + 1))} } := by
  rw [σ6, ph5]
  simp only [actState_loc_self]
  have hr : ((σ (6 * m + 5)).loc ()).round = m + 2 := by rw [s5_loc hG]
  have hk : ((σ (6 * m + 5)).loc ()).kmax = m := by
    rw [s5_loc hG, s4_loc hG, s2_loc hG]; exact hG.kmax
  simp [hr, hk]

theorem s6_now : (σ (6 * (m + 1))).now = m + 1 := by rw [σ6]; simp [ph5, s5_now hG]

theorem u0 : UStep πU FU (σ (6 * m)) (σ (6 * m + 1)) := by
  rw [σ1]
  exact UStep.step _ _ (Step.act _ () _ _ (by simp) (LStep.beacon _ hG.active
    (cert_one (by rw [hG.round]; exact hG.beacon) (by simp)))) rfl

theorem u1 : UStep πU FU (σ (6 * m + 1)) (σ (6 * m + 2)) := by
  rw [σ2]
  have hr : ((σ (6 * m + 1)).loc ()).round = m + 1 := by rw [s1_loc hG]; exact hG.round
  refine UStep.step _ _ (Step.act _ () _ _ (by simp) (LStep.propose _ _ () ?_ ?_ ?_ ?_ ?_)) rfl
  · rw [s1_loc hG]
  · rw [s1_loc hG]
  · rw [s1_now hG, hr, s1_loc hG]; simp
  · rw [hr]; simp
  · rw [hr, s1_loc hG]; simp only [Nat.add_sub_cancel]
    exact hG.notarized.mono Set.subset_union_left

theorem s2_settled : Settled πU (σ (6 * m + 2)) () := by
  apply settled_of
  · rw [s2_loc hG]
  · rw [s2_loc hG]
  · rw [s2_loc hG, s2_now hG]; simp [hG.round]
  · rw [s2_loc hG]
    dsimp only
    rw [hG.round]
    intro x hx hc
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff] at hx
    rcases hx with (hx | rfl) | rfl | rfl | rfl
    · have := hG.bad x hx hc; omega
    · exact hc.elim
    · exact hc.elim
    · exact hc.elim
    · simp [Msg.round]
  · rw [s2_loc hG]; simp [hG.round, hG.kmax]

theorem u2 : UStep πU FU (σ (6 * m + 2)) (σ (6 * m + 3)) := by
  rw [σ3]
  exact UStep.tick _ (fun p _ => by cases p; exact s2_settled hG)

theorem u3 : UStep πU FU (σ (6 * m + 3)) (σ (6 * m + 4)) := by
  rw [σ4]
  have hL : (σ (6 * m + 3)).loc () = (σ (6 * m + 2)).loc () := s3_loc hG
  have hr : ((σ (6 * m + 3)).loc ()).round = m + 1 := by rw [hL, s2_loc hG]; exact hG.round
  refine UStep.step _ _ (Step.act _ () _ _ (by simp) (LStep.echoShare _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_))
    rfl
  · rw [hL, s2_loc hG]
  · simp [hr]
  · rw [hr, hL, s2_loc hG]
    exact valid_canon_succ (by simp) (by simp)
      (hG.notarized.mono (fun x hx => by simp [hx]) |>.imp id
        (fun h => h))
  · rw [hL, s2_loc hG]; simp
  · rw [hL, s2_loc hG]; simp
  · rw [s3_now hG, hr, hL, s2_loc hG]; simp [Δntry_zero]
  · intro B' _ _ h; simp at h
  · rw [hL, s2_loc hG]; simp

theorem u4 : UStep πU FU (σ (6 * m + 4)) (σ (6 * m + 5)) := by
  rw [σ5]
  have hr : ((σ (6 * m + 4)).loc ()).round = m + 1 := by
    rw [s4_loc hG, s2_loc hG]; exact hG.round
  refine UStep.step _ _ (Step.act _ () _ _ (by simp) (LStep.finish _ _ ?_ ?_ ?_ ?_)) rfl
  · rw [s4_loc hG, s2_loc hG]
  · simp [hr]
  · rw [hr, s4_loc hG, s2_loc hG]
    exact valid_canon_succ (by simp) (by simp)
      (hG.notarized.mono (fun x hx => by simp [hx]))
  · right; rw [hr, s4_loc hG]; exact cert_one (by simp) (by simp)

theorem u5 : UStep πU FU (σ (6 * m + 5)) (σ (6 * (m + 1))) := by
  rw [σ6]
  have hr : ((σ (6 * m + 5)).loc ()).round = m + 2 := by rw [s5_loc hG]
  refine UStep.step _ _ (Step.act _ () _ _ (by simp) (LStep.final _ _ ?_ ?_ ?_)) rfl
  · rw [hr, s5_loc hG, s4_loc hG, s2_loc hG]
    exact valid_canon_succ (by simp) (by simp)
      (hG.notarized.mono (fun x hx => by simp [hx]))
  · rw [hr, s5_loc hG, s4_loc hG, s2_loc hG]; simp [hG.kmax]
  · right; rw [hr, s5_loc hG]; exact cert_one (by simp) (by simp)

theorem good_succ : Good (m + 1) (σ (6 * (m + 1))) := by
  have hL := s6_loc hG
  rw [s5_loc hG, s4_loc hG, s2_loc hG] at hL
  constructor
  · exact s6_now hG
  · rw [hL]
  · rw [hL]
  · rw [hL]
  · rw [hL]; simp
  · rw [hL]
    refine ⟨valid_canon_succ (by simp) (by simp)
      (hG.notarized.mono (fun x hx => by simp [hx])), Or.inr (by simp)⟩
  · rw [hL]
    intro x hx hc
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff] at hx
    rcases hx with ((((hx | rfl) | rfl | rfl | rfl) | rfl) | rfl | rfl) | rfl
    · have := hG.bad x hx hc; omega
    · exact hc.elim
    · exact hc.elim
    · exact hc.elim
    all_goals simp [Msg.round]

end Cycle

theorem good (m : ℕ) : Good m (σ (6 * m)) := by
  induction m with
  | zero => exact good_zero
  | succ m ih => exact good_succ ih

theorem isRun : IsRun πU FU σ where
  init := rfl
  step i := by
    obtain ⟨m, c, hc, rfl⟩ : ∃ m c, c < 6 ∧ i = 6 * m + c := ⟨i / 6, i % 6, Nat.mod_lt _ (by
      norm_num), (Nat.div_add_mod i 6).symm⟩
    have hG := good m
    interval_cases c
    · exact u0 hG
    · exact u1 hG
    · exact u2 hG
    · exact u3 hG
    · exact u4 hG
    · exact u5 hG



/-- With a single party, everything broadcast is in its pool. -/
theorem step_sent_sub {s s' : GState Unit Unit} (h : Step πU FU s s')
    (hs : s.sent ⊆ (s.loc ()).pool) : s'.sent ⊆ (s'.loc ()).pool := by
  cases h with
  | deliver p m hp hm =>
    cases p; simp only [Function.update_self]
    exact hs.trans (Set.subset_insert _ _)
  | act p l M hp hl =>
    cases p; simp only [Function.update_self, hl.pool_eq]
    exact Set.union_subset_union_left _ hs
  | tick => exact hs

theorem sent_sub : ∀ i, (σ i).sent ⊆ ((σ i).loc ()).pool
  | 0 => by
    intro x hx
    simp only [σ, GState.init, Set.mem_ofPred_eq] at hx
    obtain ⟨p, -, rfl⟩ := hx
    cases p; simp [σ, GState.init, LState.init]
  | i + 1 => step_sent_sub (isRun.step i).step' (sent_sub i)

theorem syncAt (δ T₀ : ℕ) (hδ : 1 ≤ δ) : SyncAt FU σ δ T₀ := by
  intro i i' hi hi' x hx q _
  cases q
  have hii' : i ≤ i' := by
    by_contra h
    have := isRun.now_mono (show i' ≤ i by omega)
    omega
  exact sent_sub i' (isRun.sent_mono hii' hx)

theorem not_entered_early (i : ℕ) (hi : (σ i).now < 1) : ¬ Entered (σ i) () 2 := by
  have h3 : (σ 3).now = 1 := by simpa using s3_now (good 0)
  have hi3 : i < 3 := by
    by_contra h
    have := isRun.now_mono (show 3 ≤ i by omega)
    omega
  have r1 : ((σ 1).loc ()).round = 1 := by
    have := s1_loc (good 0); simp only [Nat.mul_zero, Nat.zero_add] at this
    rw [this]; exact (good 0).round
  have r2 : ((σ 2).loc ()).round = 1 := by
    have := s2_loc (good 0); simp only [Nat.mul_zero, Nat.zero_add] at this
    rw [this]; exact (good 0).round
  unfold Entered
  interval_cases i
  · simp [σ, GState.init, LState.init]
  · rw [r1]; simp
  · rw [r2]; simp

theorem entered_seven : (σ 7).now = 1 ∧ Entered (σ 7) () 2 := by
  have h1 := s1_now (good 1)
  have h2 := s1_loc (good 1)
  simp only [Nat.mul_one] at h1 h2
  refine ⟨h1, Or.inr ⟨?_, ?_⟩⟩
  · rw [h2]; exact (good 1).round
  · rw [h2]

/-- **Non-vacuity of the liveness lemma.** The single-party run `σ` satisfies all hypotheses of
`liveness` for round `k = 2`, `T = 1`, `δ = 1`, leader `()`, at the state `σ 20` (time `3`). -/
theorem liveHyp_nonvacuous :
    LiveHyp πU FU σ 2 1 1 () ∧
      1 + 2 * 1 + πU.Δprop 0 ≤ (σ 20).now ∧ 1 + 1 + πU.Δntry 0 ≤ (σ 20).now ∧
      (∀ m ∈ (σ 20).sent, m.round = 2 → ∀ q ∉ FU, m ∈ ((σ 20).loc q).pool) ∧
      (∀ q ∉ FU, Settled πU (σ 20) q) := by
  have hnow : (σ 20).now = 3 := by simpa using s2_now (good 3)
  refine ⟨{ run := isRun
            inj := fun _ _ _ _ => rfl
            hF := by simp
            hn := by simp
            k1 := by norm_num
            before := fun i hi q _ => by cases q; exact not_entered_early i hi
            first := ⟨7, entered_seven.1, (), by simp, entered_seven.2⟩
            leader := by simp
            leader_rank := rfl
            sync₁ := syncAt 1 1 le_rfl
            sync₂ := syncAt 1 _ le_rfl
            delays := by decide
            mono := fun a b hab => by
              simp only [πU]; split_ifs <;> omega
            δpos := le_rfl }, ?_, ?_, ?_, ?_⟩
  · rw [hnow]; simp
  · rw [hnow]; simp
  · intro m hm _ q _; cases q; exact sent_sub 20 hm
  · intro q _; cases q; simpa using s2_settled (good 3)

/-- The conclusion of `liveness` in this run (sanity check). -/
example : ∃ par pl, ∀ R ∉ FU,
    Valid ((σ 20).loc R).pool (.mk 2 () par pl) ∧
    FinalShares πU ((σ 20).loc R).pool (.mk 2 () par pl) ∧
    2 ≤ ((σ 20).loc R).kmax ∧ (Block.mk 2 () par pl).chain <+: ((σ 20).loc R).out := by
  obtain ⟨L, h1, h2, h3, h4⟩ := liveHyp_nonvacuous
  exact liveness L h1 h2 h3 h4

end Podc.InternetComputerConsensus.NonVacuity
