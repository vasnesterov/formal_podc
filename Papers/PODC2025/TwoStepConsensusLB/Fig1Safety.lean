import Papers.PODC2025.TwoStepConsensusLB.Fig1Basic
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Safety of the protocol of Fig. 1 (Ryabinin–Gotsman–Sutra, PODC 2025)

Agreement and Validity of both versions of the protocol of Fig. 1, in the transition system of
`Fig1Protocol.lean` (asynchronous, message-set semantics; any process may start its own ballots).

## Proof structure

The paper derives Agreement from Lemma 1 (resp. Lemma 5) and Lemma 4 (§C.2). We use a
Paxos-style inductive invariant instead, because the paper's proof of Lemma 4 is incomplete
(see the README / `differencies.md`): its induction on the ballot `b'` does not cover a `2A(b', ·)`
computed at line 30 from a `decided_q` obtained from a decision taken at a ballot `≥ b'` (a process
may receive a `Decide` from a higher ballot before answering `1A(b')`), and the agreement of two
decisions both taken on the fast path is not argued.

* `Chosen s b v`: `v` was decided on the fast path (`b = 0`, with a "genuine" decider whose own
  ballot-0 vote, if any, is for `v`), or `n − f` processes sent `2B(b, v)` (`b ≥ 1`).
* `PotChosen s b v`: `v` *may still become* chosen at `b` — anti-monotone along executions.
  `PotFast` (`b = 0`): a would-be fast decider `p` and supporters `P'` (`|P' ∪ {p}| ≥ n − e`),
  each of which voted for `p`'s `v` at ballot 0 or still can (`bal = 0`, `val = ⊥`, line 6
  allows `v`).
  `PotSlow` (`b ≥ 1`): `2A(b, v)` was sent and `n − f` processes voted `(b, v)` or still have
  `bal ≤ b`.
* Main invariant (`Main.safe`): if `PotChosen s b v` and `2A(c, u)` was sent with `c > b`, then
  `u = v`. Working with *potentially* chosen values (rather than chosen ones) is what makes the
  line-30 case (a `decided_q` reported in a `1B`) go through without an induction on ballots.
* `recover` is Lemma 1 / Lemma 5 for potential fast decisions and for **any** `1B` quorum (sent
  before or after the decision).
-/

namespace TwoStepConsensus.Fig1

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- The resilience assumptions: `n ≥ 2f + 1`, `e ≤ f`, and `n ≥ 2e + f` (task, Theorem 1) or
`n ≥ 2e + f − 1` (object, Theorem 2). -/
structure Hyp (cfg : Config P V) : Prop where
  quorum : 2 * cfg.f + 1 ≤ Fintype.card P
  e_le_f : cfg.e ≤ cfg.f
  fast : (cfg.ver = .task ∧ 2 * cfg.e + cfg.f ≤ Fintype.card P) ∨
    (cfg.ver = .object ∧ 2 * cfg.e + cfg.f ≤ Fintype.card P + 1)

omit [DecidableEq P] [LinearOrder V] in
theorem Hyp.f_lt {cfg : Config P V} (hH : Hyp cfg) : cfg.f < Fintype.card P := by
  have := hH.quorum; omega

/-! ### Chosen and potentially chosen values -/

/-- Fast-path evidence for `v`, with would-be decider `p` and supporters `P'`. -/
def FastEv (cfg : Config P V) (s : State P V) (v : V) (p : P) (P' : Finset P) : Prop :=
  Fintype.card P - cfg.e ≤ (insert p P').card ∧
  (∀ q ∈ P', .twoB q p 0 v ∈ s.msgs ∨
    ((s.loc q).bal = 0 ∧ (s.loc q).val = none ∧ Accepts cfg.ver (s.loc q).initVal v)) ∧
  ((s.loc p).bal = 0 ∨ .decide p 0 v ∈ s.msgs)

/-- `v` may still be (or has been) decided on the fast path. -/
def PotFast (cfg : Config P V) (s : State P V) (v : V) : Prop :=
  ∃ (p : P) (P' : Finset P), FastEv cfg s v p P' ∧ (∀ p' w, .twoB p p' 0 w ∈ s.msgs → w = v) ∧
    (.propose p v ∈ s.msgs ∨ ∀ a, (s.loc p).initVal = some a → a = v)

/-- `v` was decided on the fast path by a process `p` whose own ballot-0 vote (if any) is for
`v`. -/
def GenuineFast (cfg : Config P V) (s : State P V) (v : V) : Prop :=
  ∃ (p : P) (P' : Finset P), P'.Nonempty ∧ Fintype.card P - cfg.e ≤ (insert p P').card ∧
    (∀ q ∈ P', .twoB q p 0 v ∈ s.msgs) ∧
    .decide p 0 v ∈ s.msgs ∧ (∀ p' w, .twoB p p' 0 w ∈ s.msgs → w = v)

/-- `n − f` processes sent `2B(b, v)`. -/
def SlowQuorum (cfg : Config P V) (s : State P V) (b : ℕ) (v : V) : Prop :=
  ∃ Q : Finset P, Fintype.card P - cfg.f ≤ Q.card ∧ ∀ q ∈ Q, ∃ z, .twoB q z b v ∈ s.msgs

/-- `v` is chosen at ballot `b`. -/
def Chosen (cfg : Config P V) (s : State P V) (b : ℕ) (v : V) : Prop :=
  (b = 0 ∧ GenuineFast cfg s v) ∨ (0 < b ∧ SlowQuorum cfg s b v)

/-- `2A(b, v)` was sent and `n − f` processes voted `(b, v)` or may still do so. -/
def PotSlow (cfg : Config P V) (s : State P V) (b : ℕ) (v : V) : Prop :=
  .twoA b v ∈ s.msgs ∧ ∃ Q : Finset P, Fintype.card P - cfg.f ≤ Q.card ∧
    ∀ q ∈ Q, (∃ z, .twoB q z b v ∈ s.msgs) ∨ (s.loc q).bal ≤ b

/-- `v` may still become chosen at ballot `b`. -/
def PotChosen (cfg : Config P V) (s : State P V) (b : ℕ) (v : V) : Prop :=
  (b = 0 ∧ PotFast cfg s v) ∨ (0 < b ∧ PotSlow cfg s b v)

/-- The main invariant. -/
structure Main (cfg : Config P V) (s : State P V) : Prop where
  chosen : ∀ x b v, .decide x b v ∈ s.msgs → ∃ b', Chosen cfg s b' v
  safe : ∀ b v c u, PotChosen cfg s b v → b < c → .twoA c u ∈ s.msgs → u = v

/-! ### Lemma 1 / Lemma 5 -/

section recover

variable {cfg : Config P V} {s : State P V}

/-- **Lemma 1 / Lemma 5** (general form). If `v` has fast-path evidence (`FastEv`), then for every
quorum `Q` of `1B` messages of any ballot in which no decision and no slow vote is reported (so that
lines 33–38 are executed), lines 26–38 select `v`, and only `v`. -/
theorem recover (hH : Hyp cfg) (hI : Basic cfg s) {v : V} {p : P} {P' : Finset P}
    (hF : FastEv cfg s v p P') {c : ℕ} {Q : Finset P} {rep : P → Snap P V}
    (hQc : Q.card = Fintype.card P - cfg.f) (hQ : ∀ q ∈ Q, .oneB q c (rep q) ∈ s.msgs)
    (hdec : ∀ q ∈ Q, (rep q).decided = none) (hz : ∀ q ∈ Q, (rep q).vbal = 0) :
    (∀ iv w, Select cfg Q rep iv w → w = v) ∧ ∀ iv, Select cfg Q rep iv v := by
  obtain ⟨hcard, hP', hp⟩ := hF
  have hH1 := hH.quorum
  have hH2 := hH.e_le_f
  -- the would-be decider `p` is not in `Q`
  have hpQ : p ∉ Q := by
    intro hpQ
    have h1 := hI.oneB_bal _ _ _ (hQ p hpQ)
    rcases hp with hp | hp
    · omega
    · exact (hI.decide_fast p v hp).2 c (rep p) (hQ p hpQ) (hdec p hpQ)
  -- the supporters in `Q` voted for `p`'s `v` and report it
  have hA : ∀ q ∈ Q ∩ P', (rep q).val = some v ∧ (rep q).proposer = some p ∧
      .twoB q p 0 v ∈ s.msgs := by
    intro q hq
    rw [Finset.mem_inter] at hq
    have hb := hI.oneB_bal _ _ _ (hQ q hq.1)
    have h2B : .twoB q p 0 v ∈ s.msgs := by
      rcases hP' q hq.2 with h | h
      · exact h
      · omega
    have := hI.oneB_vote _ _ _ _ _ (hQ q hq.1) h2B (hdec q hq.1) (hz q hq.1)
    exact ⟨this.1, this.2, h2B⟩
  have hAv : VotersIn Q rep v (Q ∩ P') := by
    refine ⟨Finset.inter_subset_left, fun q hq => ⟨?_, (hA q hq).1⟩⟩
    intro x hx
    rw [(hA q hq).2.1] at hx
    cases hx
    exact hpQ
  have hQX : Q ∩ insert p P' = Q ∩ P' := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, rfl | hx'⟩
      · exact absurd hx hpQ
      · exact ⟨hx, hx'⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨hx, Or.inr hx'⟩
  have hAc : Fintype.card P - cfg.f - cfg.e ≤ (Q ∩ P').card := by
    have h1 := Finset.card_add_card_le_card_inter_add_card_univ Q (insert p P')
    rw [hQX] at h1
    omega
  have hAne : (Q ∩ P').Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hprop : .propose p v ∈ s.msgs := by
    obtain ⟨q, hq⟩ := hAne
    exact (hI.twoB0 _ _ _ (hA q hq).2.2).1
  -- a vote in `R` for `w` points at a proposer of `w` outside `Q`
  have hR : ∀ q ∈ Q, ∀ w, InR Q (rep q) → (rep q).val = some w →
      ∃ pw, pw ∉ Q ∧ .propose pw w ∈ s.msgs := by
    intro q hq w hR hw
    obtain ⟨pw, hpw, h2B⟩ := hI.oneB_zero _ _ _ _ (hQ q hq) (hdec q hq) (hz q hq) hw
    exact ⟨pw, hR pw hpw, (hI.twoB0 _ _ _ h2B).1⟩
  -- if exactly `n − f − e` supporters are in `Q`, every process outside `Q` is a supporter
  have hcover : (Q ∩ P').card = Fintype.card P - cfg.f - cfg.e → ∀ x, x ∉ Q → x ∈ insert p P' := by
    intro hAeq x hxQ
    by_contra hxX
    have h1 := Finset.card_union_add_card_inter Q (insert p P')
    have h2 : Q ∪ insert p P' ⊆ Finset.univ.erase x := by
      intro y hy
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      rcases Finset.mem_union.1 hy with h | h
      · exact hxQ h
      · exact hxX h
    have h3 := Finset.card_le_card h2
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h3
    rw [hQX] at h1
    have : 0 < Fintype.card P := by omega
    omega
  -- the proposal of a supporter is `≤ v` (task) or `= v` (object): line 6
  have hsupp : (∀ x, x ∉ Q → x ∈ insert p P') → ∀ pw w, pw ∉ Q → .propose pw w ∈ s.msgs →
      w ≤ v ∧ (cfg.ver = .object → w = v) := by
    intro hcov pw w hpw hprw
    have hiv := hI.propose_initVal _ _ hprw
    rcases Finset.mem_insert.1 (hcov pw hpw) with rfl | hpw'
    · have := hI.propose_initVal _ _ hprop
      rw [hiv] at this
      cases this
      exact ⟨le_rfl, fun _ => rfl⟩
    · have hacc : Accepts cfg.ver (s.loc pw).initVal v := by
        rcases hP' pw hpw' with h | h
        · exact (hI.twoB0 _ _ _ h).2.2.2.2
        · exact h.2.2
      exact ⟨hacc.1 w hiv, fun ho => hacc.2 ho w hiv⟩
  -- no value other than `v` satisfies the condition at line 33
  have hno33 : ∀ w, Cond33 cfg Q rep w → w = v := by
    rintro w ⟨S, ⟨hSQ, hS⟩, hScard⟩
    by_contra hwv
    have hdisj : Disjoint S (Q ∩ P') := by
      rw [Finset.disjoint_left]
      intro q hqS hqA
      have h1 := (hS q hqS).2
      rw [(hA q hqA).1] at h1
      cases h1
      exact hwv rfl
    have hcu := Finset.card_union_of_disjoint hdisj
    have hsub : S ∪ (Q ∩ P') ⊆ Q := Finset.union_subset hSQ Finset.inter_subset_left
    have h2 := Finset.card_le_card hsub
    rcases hH.fast with ⟨_, hn⟩ | ⟨hobj, hn⟩
    · omega
    · have hAeq : (Q ∩ P').card = Fintype.card P - cfg.f - cfg.e := by omega
      obtain ⟨q, hq⟩ : S.Nonempty := by
        rw [← Finset.card_pos]
        omega
      obtain ⟨pw, hpw, hprw⟩ := hR q (hSQ hq) w (hS q hq).1 (hS q hq).2
      exact hwv ((hsupp (hcover hAeq) pw w hpw hprw).2 hobj)
  have hAeq : ¬ Cond33 cfg Q rep v → (Q ∩ P').card = Fintype.card P - cfg.f - cfg.e := by
    intro hn33
    by_contra hne
    exact hn33 ⟨Q ∩ P', hAv, by omega⟩
  -- every value satisfying the condition at line 35 is `≤ v`
  have hmax35 : ¬ Cond33 cfg Q rep v → ∀ w, Cond35 cfg Q rep w → w ≤ v := by
    rintro hn33 w ⟨S, ⟨hSQ, hS⟩, hScard⟩
    obtain ⟨q, hq⟩ : S.Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨pw, hpw, hprw⟩ := hR q (hSQ hq) w (hS q hq).1 (hS q hq).2
    exact (hsupp (hcover (hAeq hn33)) pw w hpw hprw).1
  refine ⟨?_, ?_⟩
  · intro iv w hsel
    cases hsel with
    | l30 hq hd =>
      rw [hdec _ hq] at hd
      cases hd
    | l32 _ hq _ hpos _ =>
      rw [hz _ hq] at hpos
      exact absurd hpos (lt_irrefl 0)
    | l34 _ _ h33 => exact hno33 w h33
    | l36 _ _ hn33 h35 hmax =>
      exact le_antisymm (hmax35 (hn33 v) w h35) (hmax v ⟨Q ∩ P', hAv, hAeq (hn33 v)⟩)
    | l38 _ _ hn33 hn35 _ => exact absurd ⟨Q ∩ P', hAv, hAeq (hn33 v)⟩ (hn35 v)
  · intro iv
    by_cases h33 : Cond33 cfg Q rep v
    · exact .l34 hdec hz h33
    · have hn33 : ∀ w, ¬ Cond33 cfg Q rep w := fun w hw => h33 (hno33 w hw ▸ hw)
      exact .l36 hdec hz hn33 ⟨Q ∩ P', hAv, hAeq h33⟩ (hmax35 h33)

end recover

/-! ### Two fast decisions agree -/

section fastfast

variable {cfg : Config P V} {s : State P V}

/-- A genuine fast decision of `u` and a potential fast decision of `v` agree (the supporter sets
intersect since `n > 2e`; ballot-0 votes are unique). Not argued in the paper. -/
theorem fast_fast (hH : Hyp cfg) (hI : Basic cfg s) {u v : V} (hu : GenuineFast cfg s u)
    (hv : PotFast cfg s v) : u = v := by
  obtain ⟨p', P'', hne, hc', hP'', hdec', hvote'⟩ := hu
  obtain ⟨p, P', ⟨hc, hP', _⟩, hvote, hpr⟩ := hv
  have h1 := Finset.card_add_card_le_card_inter_add_card_univ (insert p' P'') (insert p P')
  have hH1 := hH.quorum
  have hH2 := hH.e_le_f
  obtain ⟨x, hx⟩ : (insert p' P'' ∩ insert p P').Nonempty := by
    rw [← Finset.card_pos]
    omega
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_insert] at hx
  obtain ⟨hx1 | hx1, hx2 | hx2⟩ := hx
  · subst hx1
    subst hx2
    obtain ⟨q, hq⟩ := hne
    have hpu := hI.propose_initVal _ _ (hI.twoB0 _ _ _ (hP'' q hq)).1
    rcases hpr with h | h
    · rw [hI.propose_initVal _ _ h] at hpu
      cases hpu
      rfl
    · exact h u hpu
  · subst hx1
    rcases hP' x hx2 with h | h
    · exact (hvote' _ _ h).symm
    · exact absurd h.2.1 (hI.val_of_decided x (hI.decide_decided _ _ _ hdec'))
  · subst hx2
    exact hvote _ _ (hP'' x hx1)
  · rcases hP' x hx2 with h | h
    · exact (hI.twoB0_unique _ _ _ _ _ (hP'' x hx1) h).2
    · exact absurd h.2.1 (hI.twoB0 _ _ _ (hP'' x hx1)).2.2.2.1

theorem GenuineFast.potFast (hI : Basic cfg s) {v : V} (h : GenuineFast cfg s v) :
    PotFast cfg s v := by
  obtain ⟨p, P', hne, hc, hP', hd, hvote⟩ := h
  obtain ⟨q, hq⟩ := hne
  exact ⟨p, P', ⟨hc, fun q hq => Or.inl (hP' q hq), Or.inr hd⟩, hvote,
    Or.inl (hI.twoB0 _ _ _ (hP' q hq)).1⟩

theorem SlowQuorum.twoA (hH : Hyp cfg) (hI : Basic cfg s) {b : ℕ} {v : V} (hb : 0 < b)
    (h : SlowQuorum cfg s b v) : .twoA b v ∈ s.msgs := by
  obtain ⟨Q, hQc, hQ⟩ := h
  have := hH.f_lt
  obtain ⟨q, hq⟩ : Q.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨z, hz⟩ := hQ q hq
  exact hI.twoB_twoA _ _ _ _ hz hb

theorem SlowQuorum.potSlow (hH : Hyp cfg) (hI : Basic cfg s) {b : ℕ} {v : V} (hb : 0 < b)
    (h : SlowQuorum cfg s b v) : PotSlow cfg s b v := by
  refine ⟨h.twoA hH hI hb, ?_⟩
  obtain ⟨Q, hQc, hQ⟩ := h
  exact ⟨Q, hQc, fun q hq => Or.inl (hQ q hq)⟩

theorem Chosen.potChosen (hH : Hyp cfg) (hI : Basic cfg s) {b : ℕ} {v : V}
    (h : Chosen cfg s b v) : PotChosen cfg s b v := by
  rcases h with ⟨hb, h⟩ | ⟨hb, h⟩
  · exact Or.inl ⟨hb, h.potFast hI⟩
  · exact Or.inr ⟨hb, h.potSlow hH hI hb⟩

/-- A potentially chosen slow value is reported by some member of every later `1B` quorum. -/
theorem PotSlow.vbal (hH : Hyp cfg) (hI : Basic cfg s) {b : ℕ} {v : V} (h : PotSlow cfg s b v)
    {c : ℕ} {Q : Finset P} {rep : P → Snap P V} (hQc : Q.card = Fintype.card P - cfg.f)
    (hQ : ∀ q ∈ Q, .oneB q c (rep q) ∈ s.msgs) (hbc : b < c) : ∃ y ∈ Q, b ≤ (rep y).vbal := by
  obtain ⟨_, Q', hQ'c, hQ'⟩ := h
  have h1 := Finset.card_add_card_le_card_inter_add_card_univ Q Q'
  have hH1 := hH.quorum
  obtain ⟨y, hy⟩ : (Q ∩ Q').Nonempty := by
    rw [← Finset.card_pos]
    omega
  rw [Finset.mem_inter] at hy
  have hb := hI.oneB_bal _ _ _ (hQ y hy.1)
  rcases hQ' y hy.2 with ⟨z, hz⟩ | hz
  · exact ⟨y, hy.1, hI.oneB_order _ _ _ _ _ _ (hQ y hy.1) hz hbc⟩
  · omega

/-- Agreement between a chosen and a potentially chosen value, given `Main.safe`. -/
theorem chosen_potChosen (hH : Hyp cfg) (hI : Basic cfg s)
    (hsafe : ∀ b v c u, PotChosen cfg s b v → b < c → .twoA c u ∈ s.msgs → u = v)
    {b b' : ℕ} {u v : V} (hu : Chosen cfg s b' u) (hv : PotChosen cfg s b v) : u = v := by
  rcases hu with ⟨rfl, hu⟩ | ⟨hb', hu⟩
  · rcases hv with ⟨rfl, hv⟩ | ⟨hb, hv⟩
    · exact fast_fast hH hI hu hv
    · exact (hsafe 0 u b v (Or.inl ⟨rfl, hu.potFast hI⟩) hb hv.1).symm
  · have h2A := hu.twoA hH hI hb'
    rcases lt_trichotomy b b' with hlt | rfl | hgt
    · exact hsafe b v b' u hv hlt h2A
    · rcases hv with ⟨rfl, _⟩ | ⟨_, hv⟩
      · omega
      · exact hI.twoA_unique _ _ _ h2A hv.1
    · rcases hv with ⟨rfl, _⟩ | ⟨_, hv⟩
      · omega
      · exact (hsafe b' u b v (Or.inr ⟨hb', hu.potSlow hH hI hb'⟩) hgt hv.1).symm

end fastfast

/-! ### What a single step can change -/

section step

variable {cfg : Config P V} {s s' : State P V} {x : P} {k : Kind}

theorem Step.twoA_old (h : Step cfg x k s s') (hk : k ≠ .send2A) {c : ℕ} {u : V}
    (hm : .twoA c u ∈ s'.msgs) : .twoA c u ∈ s.msgs := by
  cases h <;> simp_all

theorem Step.twoB_new (hI : Basic cfg s) (h : Step cfg x k s s') {q z : P} {b : ℕ} {w : V}
    (hm : .twoB q z b w ∈ s'.msgs) (hn : .twoB q z b w ∉ s.msgs) :
    (b = 0 ∧ (s.loc q).bal = 0 ∧ (s.loc q).val = none ∧ Accepts cfg.ver (s.loc q).initVal w) ∨
    (0 < b ∧ (s.loc q).bal ≤ b) := by
  cases h <;> simp_all
  case recv2A hm2 _ =>
    obtain ⟨rfl, -, rfl, rfl⟩ := hm
    exact Or.inr (hI.twoA_quorum _ _ hm2).1

theorem Step.decide0_new (h : Step cfg x k s s') {p : P} {v : V}
    (hm : .decide p 0 v ∈ s'.msgs) (hn : .decide p 0 v ∉ s.msgs) : (s.loc p).bal = 0 := by
  cases h <;> simp_all

theorem Step.propose_new (h : Step cfg x k s s') {p : P} {v : V}
    (hm : .propose p v ∈ s'.msgs) (hn : .propose p v ∉ s.msgs) :
    (s.loc p).initVal = some v := by
  cases h <;> simp_all

theorem Step.initVal_stable (hI : Basic cfg s) (h : Step cfg x k s s') {q : P} {a : V}
    (ha : (s.loc q).initVal = some a) : (s'.loc q).initVal = some a := by
  cases h
  case invoke v hver hinv =>
    have := hI.initVal_obj hver _ _ ha
    simp only [State.set_loc]
    split_ifs <;> simp_all
  all_goals simp only [State.set_loc, State.send_loc]; (try split_ifs) <;> simp_all

theorem Step.unvoted_back (hI : Basic cfg s) (h : Step cfg x k s s') {q : P} {v : V}
    (hq : (s'.loc q).bal = 0 ∧ (s'.loc q).val = none ∧ Accepts cfg.ver (s'.loc q).initVal v) :
    (s.loc q).bal = 0 ∧ (s.loc q).val = none ∧ Accepts cfg.ver (s.loc q).initVal v := by
  cases h
  case invoke v hver hinv =>
    by_cases hqx : q = x
    · subst hqx
      have h0 : (s.loc q).initVal = none := by
        by_contra hne
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hne
        have := hI.initVal_obj hver _ _ ha
        simp_all
      simp only [State.set_loc, ↓reduceIte] at hq
      refine ⟨hq.1, hq.2.1, ?_⟩
      rw [h0]
      exact ⟨fun a ha => (nomatch ha), fun _ a ha => (nomatch ha)⟩
    · simpa [hqx] using hq
  all_goals simp only [State.set_loc, State.send_loc] at hq; (try split_ifs at hq) <;> simp_all

theorem Step.potFast_back (hI : Basic cfg s) (h : Step cfg x k s s') {v : V}
    (hv : PotFast cfg s' v) : PotFast cfg s v := by
  obtain ⟨p, P', ⟨hc, hP', hp⟩, hvote, hpr⟩ := hv
  refine ⟨p, P', ⟨hc, fun q hq => ?_, ?_⟩, fun p' w hw => hvote p' w (h.msgs_mono hw), ?_⟩
  · rcases hP' q hq with hm | hu
    · by_cases hn : .twoB q p 0 v ∈ s.msgs
      · exact Or.inl hn
      · rcases h.twoB_new hI hm hn with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact Or.inr h1
        · exact absurd h1 (lt_irrefl 0)
    · exact Or.inr (h.unvoted_back hI hu)
  · rcases hp with hp | hp
    · exact Or.inl (Nat.le_zero.1 (hp ▸ h.bal_mono p))
    · by_cases hn : .decide p 0 v ∈ s.msgs
      · exact Or.inr hn
      · exact Or.inl (h.decide0_new hp hn)
  · rcases hpr with hpr | hpr
    · by_cases hn : .propose p v ∈ s.msgs
      · exact Or.inl hn
      · have := h.propose_new hpr hn
        exact Or.inr fun a ha => by rw [this] at ha; cases ha; rfl
    · exact Or.inr fun a ha => hpr a (h.initVal_stable hI ha)

theorem Step.potSlow_back (hI : Basic cfg s) (h : Step cfg x k s s') {b : ℕ} {v : V}
    (hv : PotSlow cfg s' b v) (h2A : .twoA b v ∈ s.msgs) : PotSlow cfg s b v := by
  obtain ⟨-, Q, hQc, hQ⟩ := hv
  refine ⟨h2A, Q, hQc, fun q hq => ?_⟩
  rcases hQ q hq with ⟨z, hz⟩ | hb
  · by_cases hn : .twoB q z b v ∈ s.msgs
    · exact Or.inl ⟨z, hn⟩
    · rcases h.twoB_new hI hz hn with ⟨-, h1, -⟩ | ⟨-, h1⟩
      · exact Or.inr (by omega)
      · exact Or.inr h1
  · exact Or.inr (le_trans (h.bal_mono q) hb)

theorem Step.potChosen_back (hI : Basic cfg s) (h : Step cfg x k s s') {b : ℕ} {v : V}
    (hv : PotChosen cfg s' b v) (h2A : 0 < b → .twoA b v ∈ s.msgs) : PotChosen cfg s b v := by
  rcases hv with ⟨hb, hv⟩ | ⟨hb, hv⟩
  · exact Or.inl ⟨hb, h.potFast_back hI hv⟩
  · exact Or.inr ⟨hb, h.potSlow_back hI hv (h2A hb)⟩

theorem Step.chosen_mono (hI : Basic cfg s) (h : Step cfg x k s s') {b : ℕ} {v : V}
    (hv : Chosen cfg s b v) : Chosen cfg s' b v := by
  rcases hv with ⟨hb, p, P', hne, hc, hP', hd, hvote⟩ | ⟨hb, Q, hQc, hQ⟩
  · refine Or.inl ⟨hb, p, P', hne, hc, fun q hq => h.msgs_mono (hP' q hq), h.msgs_mono hd,
      fun p' w hw => ?_⟩
    by_cases hn : .twoB p p' 0 w ∈ s.msgs
    · exact hvote p' w hn
    · rcases h.twoB_new hI hw hn with ⟨-, -, h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 (hI.val_of_decided p (hI.decide_decided _ _ _ hd))
      · exact absurd h1 (lt_irrefl 0)
  · exact Or.inr ⟨hb, Q, hQc, fun q hq => (hQ q hq).imp fun z hz => h.msgs_mono hz⟩

end step

/-! ### The main invariant -/

section main

variable {cfg : Config P V} {s s' : State P V}

theorem main_init (cfg : Config P V) : Main cfg (init cfg) :=
  ⟨fun _ _ _ h => by simp [init] at h, fun _ _ _ _ _ _ h => by simp [init] at h⟩

/-- A `2A(c, u)` computed by lines 26–38 from a quorum of `1B(c, …)` messages agrees with every
value that may be chosen at a ballot `b < c` (cf. Lemma 4 and Lemma 1/5). -/
theorem safe_new2A (hH : Hyp cfg) (hI : Basic cfg s) (hM : Main cfg s) {c : ℕ} {u : V}
    {Q : Finset P} {rep : P → Snap P V} {iv : Option V}
    (hQc : Q.card = Fintype.card P - cfg.f) (hQ : ∀ q ∈ Q, .oneB q c (rep q) ∈ s.msgs)
    (hsel : Select cfg Q rep iv u) {b : ℕ} {v : V} (hpc : PotChosen cfg s b v) (hbc : b < c) :
    u = v := by
  have hsel' := hsel
  cases hsel with
  | l30 hq hd =>
    obtain ⟨x, b'', hx⟩ := hI.oneB_decided _ _ _ _ (hQ _ hq) hd
    obtain ⟨b', hch⟩ := hM.chosen _ _ _ hx
    exact chosen_potChosen hH hI hM.safe hch hpc
  | @l32 q _ hdec hq hmax hpos hval =>
    obtain ⟨u', hu', h2A⟩ := hI.oneB_vbal _ _ _ (hQ _ hq) hpos (hdec _ hq)
    rw [hval] at hu'
    cases hu'
    rcases hpc with ⟨rfl, hv⟩ | ⟨hb, hv⟩
    · exact hM.safe 0 v _ u (Or.inl ⟨rfl, hv⟩) hpos h2A
    · obtain ⟨y, hy, hby⟩ := hv.vbal hH hI hQc hQ hbc
      have := hmax y hy
      rcases (show b = (rep q).vbal ∨ b < (rep q).vbal by omega) with heq | hlt
      · rw [← heq] at h2A
        exact hI.twoA_unique _ _ _ h2A hv.1
      · exact hM.safe b v _ u (Or.inr ⟨hb, hv⟩) hlt h2A
  | l34 hdec hz _ | l36 hdec hz _ _ _ | l38 hdec hz _ _ _ =>
    rcases hpc with ⟨rfl, ⟨p, P', hF, -, -⟩⟩ | ⟨hb, hv⟩
    · exact (recover hH hI hF hQc hQ hdec hz).1 iv u hsel'
    · obtain ⟨y, hy, hby⟩ := hv.vbal hH hI hQc hQ hbc
      rw [hz y hy] at hby
      omega

theorem main_step (hH : Hyp cfg) (hI : Basic cfg s) (hM : Main cfg s) {x : P} {k : Kind}
    (h : Step cfg x k s s') : Main cfg s' := by
  constructor
  · intro y b v hd
    by_cases hold : .decide y b v ∈ s.msgs
    · obtain ⟨b', hb'⟩ := hM.chosen _ _ _ hold
      exact ⟨b', h.chosen_mono hI hb'⟩
    have hmono := fun b v (hc : Chosen cfg s b v) => h.chosen_mono hI hc
    cases h
    case fastDecide v' P' hne hP' hc hbal hval =>
      simp only [State.mem_send_msgs, Msg.decide.injEq] at hd
      rcases hd with ⟨rfl, rfl, rfl⟩ | hd
      swap
      · exact absurd hd hold
      have hvb : (s.loc y).vbal = 0 := by
        have := hI.vbal_le_bal y
        omega
      by_cases hdx : (s.loc y).decided = none
      · refine ⟨0, Or.inl ⟨rfl, y, P', hne, hP', fun q hq => Or.inr (hc q hq), Or.inl rfl,
          fun p' w hw => ?_⟩⟩
        rcases hw with hw | hw
        · cases hw
        have := hI.twoB0_val _ _ _ hw hdx hvb
        rcases hval with hv | hv <;> rw [hv] at this <;> cases this
        rfl
      · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hdx
        have hva := hI.val_eq_decided _ _ ha hvb
        have hav : a = v := by
          rcases hval with hv | hv <;> rw [hv] at hva <;> cases hva
          rfl
        subst hav
        obtain ⟨z, b', hz⟩ := hI.decided_msg _ _ ha
        obtain ⟨b'', hb''⟩ := hM.chosen _ _ _ hz
        exact ⟨b'', hmono _ _ hb''⟩
    case slowDecide v' P' _ hP' hc hbal =>
      simp only [State.mem_send_msgs, Msg.decide.injEq] at hd
      rcases hd with ⟨rfl, rfl, rfl⟩ | hd
      swap
      · exact absurd hd hold
      exact ⟨_, Or.inr ⟨Nat.pos_of_ne_zero hbal, P', hP', fun q hq => ⟨y, Or.inr (hc q hq)⟩⟩⟩
    all_goals simp_all
  · intro b v c u hpc hbc h2A
    have hback := h.potChosen_back hI hpc
    by_cases hk : k = .send2A
    · subst hk
      cases h with
      | send2A Q rep _ hno hQc hQ hsel =>
        rename_i c0 u0 _
        have hbv : 0 < b → .twoA b v ∈ s.msgs ∨ (b = c0 ∧ v = u0) := by
          intro hb
          rcases hpc with ⟨rfl, -⟩ | ⟨-, hv⟩
          · omega
          · rcases hv.1 with hv | hv
            · simp only [Msg.twoA.injEq] at hv
              exact Or.inr hv
            · exact Or.inl hv
        rcases h2A with h2A | h2A
        · simp only [Msg.twoA.injEq] at h2A
          obtain ⟨rfl, rfl⟩ := h2A
          refine safe_new2A hH hI hM hQc hQ hsel (hback fun hb => ?_) hbc
          exact (hbv hb).resolve_right (by omega)
        · by_cases hold : 0 < b → .twoA b v ∈ s.msgs
          · exact hM.safe b v c u (hback hold) hbc h2A
          · exfalso
            push Not at hold
            obtain ⟨hb, hn⟩ := hold
            obtain ⟨rfl, rfl⟩ := (hbv hb).resolve_left hn
            rcases hpc with ⟨h0, -⟩ | ⟨-, -, Q', hQ'c, hQ'⟩
            · omega
            obtain ⟨-, Q2, hQ2c, hQ2⟩ := hI.twoA_quorum _ _ h2A
            have h1 := Finset.card_add_card_le_card_inter_add_card_univ Q' Q2
            have hH1 := hH.quorum
            obtain ⟨y, hy⟩ : (Q' ∩ Q2).Nonempty := by
              rw [← Finset.card_pos]
              omega
            rw [Finset.mem_inter] at hy
            obtain ⟨d, hd⟩ := hQ2 y hy.2
            have hbal := (hI.oneB_bal _ _ _ hd).2
            rcases hQ' y hy.1 with ⟨z, hz | hz⟩ | hz
            · cases hz
            · exact hn (hI.twoB_twoA _ _ _ _ hz hb)
            · exact absurd (lt_of_lt_of_le hbc hbal) (not_lt.2 hz)
    · have h2A' := h.twoA_old hk h2A
      refine hM.safe b v c u (hback fun hb => ?_) hbc h2A'
      rcases hpc with ⟨rfl, -⟩ | ⟨-, hv⟩
      · omega
      · exact h.twoA_old hk hv.1

/-- `Basic` and `Main` hold in every reachable state. -/
theorem inv_of_reachable (hH : Hyp cfg) (h : Reachable cfg s) : Basic cfg s ∧ Main cfg s := by
  induction h with
  | refl => exact ⟨basic_init cfg, main_init cfg⟩
  | tail _ hst ih =>
    obtain ⟨p, k, hst⟩ := hst
    exact ⟨basic_step hH.f_lt ih.1 hst, main_step hH ih.1 ih.2 hst⟩

end main

/-! ### Validity -/

section validity

variable {cfg : Config P V} {s s' : State P V}

/-- Every value occurring in the state (local variables and messages) satisfies `ok`. -/
structure Occ (s : State P V) (ok : V → Prop) : Prop where
  initVal : ∀ q w, (s.loc q).initVal = some w → ok w
  val : ∀ q w, (s.loc q).val = some w → ok w
  decided : ∀ q w, (s.loc q).decided = some w → ok w
  propose : ∀ p w, .propose p w ∈ s.msgs → ok w
  twoB : ∀ q z b w, .twoB q z b w ∈ s.msgs → ok w
  twoA : ∀ b w, .twoA b w ∈ s.msgs → ok w
  decide : ∀ x b w, .decide x b w ∈ s.msgs → ok w
  oneB_val : ∀ y c d w, .oneB y c d ∈ s.msgs → d.val = some w → ok w
  oneB_decided : ∀ y c d w, .oneB y c d ∈ s.msgs → d.decided = some w → ok w

omit [Fintype P] [DecidableEq P] [LinearOrder V] in
theorem Occ.mono {ok ok' : V → Prop} (h : Occ s ok) (hok : ∀ w, ok w → ok' w) : Occ s ok' :=
  ⟨fun q w hw => hok _ (h.1 q w hw), fun q w hw => hok _ (h.2 q w hw),
    fun q w hw => hok _ (h.3 q w hw), fun p w hw => hok _ (h.4 p w hw),
    fun q z b w hw => hok _ (h.5 q z b w hw), fun b w hw => hok _ (h.6 b w hw),
    fun x b w hw => hok _ (h.7 x b w hw), fun y c d w hm hw => hok _ (h.8 y c d w hm hw),
    fun y c d w hm hw => hok _ (h.9 y c d w hm hw)⟩

omit [DecidableEq P] in
/-- Lines 26–38 only select a value reported in a `1B` message or the leader's `initial_val`. -/
theorem select_ok {ok : V → Prop} {Q : Finset P} {rep : P → Snap P V} {iv : Option V} {w : V}
    (hne : 0 < Fintype.card P - cfg.f - cfg.e)
    (hval : ∀ q ∈ Q, ∀ w, (rep q).val = some w → ok w)
    (hdec : ∀ q ∈ Q, ∀ w, (rep q).decided = some w → ok w) (hiv : ∀ w, iv = some w → ok w)
    (h : Select cfg Q rep iv w) : ok w := by
  cases h with
  | l30 hq hd => exact hdec _ hq _ hd
  | l32 _ hq _ _ hv => exact hval _ hq _ hv
  | l34 _ _ h33 =>
    obtain ⟨S, ⟨hSQ, hS⟩, hc⟩ := h33
    obtain ⟨q, hq⟩ : S.Nonempty := by
      rw [← Finset.card_pos]
      omega
    exact hval _ (hSQ hq) _ (hS q hq).2
  | l36 _ _ _ h35 _ =>
    obtain ⟨S, ⟨hSQ, hS⟩, hc⟩ := h35
    obtain ⟨q, hq⟩ : S.Nonempty := by
      rw [← Finset.card_pos]
      omega
    exact hval _ (hSQ hq) _ (hS q hq).2
  | l38 _ _ _ _ hi => exact hiv _ hi

theorem occ_step {ok : V → Prop} (hne : 0 < Fintype.card P - cfg.f - cfg.e) (hO : Occ s ok)
    {x : P} {k : Kind} (h : Step cfg x k s s') :
    Occ s' (fun w => ok w ∨ (k = .invoke ∧ (s'.loc x).inv = some w)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hO
  cases h
  case send2A Q rep _ _ _ hQ hsel =>
    have := select_ok (ok := ok) hne (fun q hq w hw => h8 _ _ _ _ (hQ q hq) hw)
      (fun q hq w hw => h9 _ _ _ _ (hQ q hq) hw) (fun w hw => by
        unfold leaderIv at hw
        split_ifs at hw
        · cases hi : (s.loc x).initVal with
          | none => rw [hi] at hw; exact h2 _ _ hw
          | some a => rw [hi] at hw; cases hw; exact h1 _ _ hi
        · exact h1 _ _ hw) hsel
    constructor <;> intros <;> simp only [State.mem_send_msgs, State.send_loc] at * <;> grind
  all_goals constructor
  all_goals intros
  all_goals simp only [State.set_loc, State.set_msgs, State.send_loc, State.mem_send_msgs,
    Loc.snap] at *
  all_goals grind

/-- The values that may legally be decided: an input (task version) or the argument of some
invocation of `propose` (object version). -/
def ValidV (cfg : Config P V) (s : State P V) (w : V) : Prop :=
  (cfg.ver = .task → ∃ q, cfg.input q = w) ∧ (cfg.ver = .object → ∃ q, (s.loc q).inv = some w)

theorem Step.inv_stable {x : P} {k : Kind} (h : Step cfg x k s s') {q : P} {w : V}
    (hw : (s.loc q).inv = some w) : (s'.loc q).inv = some w := by
  cases h <;> simp only [State.set_loc, State.send_loc] <;> (try split_ifs) <;> simp_all

theorem occ_of_reachable (hH : Hyp cfg) (hs : Reachable cfg s) : Occ s (ValidV cfg s) := by
  have hne : 0 < Fintype.card P - cfg.f - cfg.e := by
    have := hH.quorum
    have := hH.e_le_f
    omega
  induction hs with
  | refl =>
    constructor <;> intros <;> simp_all [init, ValidV]
    rename_i q w h
    by_cases hv : cfg.ver = .task
    · exact ⟨q, by simp_all⟩
    · simp [hv] at h
  | tail _ hst ih =>
    obtain ⟨x, k, hst⟩ := hst
    refine (occ_step hne ih hst).mono ?_
    rintro w (⟨ht, ho⟩ | ⟨rfl, hw⟩)
    · exact ⟨ht, fun hv => (ho hv).imp fun q hq => hst.inv_stable hq⟩
    · cases hst with
      | invoke v hver _ =>
        exact ⟨fun ht => absurd (ht.symm.trans hver) (by decide), fun _ => ⟨x, hw⟩⟩

end validity

/-! ### Main results -/

section results

variable {cfg : Config P V} {s : State P V}

/-- **Agreement** (both versions, under `Hyp`): all `Decide` messages ever sent carry the same
value. Since messages are never removed, this covers decisions taken at different times: every
decision of Fig. 1 (line 12 or 16) is the value of some `Decide` message. -/
theorem agreement_msgs (hH : Hyp cfg) (hs : Reachable cfg s) {x y : P} {b c : ℕ} {u v : V}
    (hx : .decide x b u ∈ s.msgs) (hy : .decide y c v ∈ s.msgs) : u = v := by
  obtain ⟨hI, hM⟩ := inv_of_reachable hH hs
  obtain ⟨b', hb'⟩ := hM.chosen _ _ _ hx
  obtain ⟨c', hc'⟩ := hM.chosen _ _ _ hy
  exact chosen_potChosen hH hI hM.safe hb' (hc'.potChosen hH hI)

/-- **Agreement** (both versions, under `Hyp`): in every reachable state all decided processes
have decided the same value. -/
theorem agreement (hH : Hyp cfg) (hs : Reachable cfg s) {p q : P} {u v : V}
    (hp : (s.loc p).decided = some u) (hq : (s.loc q).decided = some v) : u = v := by
  have hI := basic_of_reachable hH.f_lt hs
  obtain ⟨x, b, hx⟩ := hI.decided_msg _ _ hp
  obtain ⟨y, c, hy⟩ := hI.decided_msg _ _ hq
  exact agreement_msgs hH hs hx hy

/-- **Theorem 1 ("if"), Agreement**: the task version of Fig. 1 satisfies Agreement when
`n ≥ max(2e + f, 2f + 1)` and `e ≤ f`. -/
theorem task_agreement (hver : cfg.ver = .task) (hn1 : 2 * cfg.f + 1 ≤ Fintype.card P)
    (hn2 : 2 * cfg.e + cfg.f ≤ Fintype.card P) (hef : cfg.e ≤ cfg.f) (hs : Reachable cfg s)
    {p q : P} {u v : V} (hp : (s.loc p).decided = some u) (hq : (s.loc q).decided = some v) :
    u = v :=
  agreement ⟨hn1, hef, Or.inl ⟨hver, hn2⟩⟩ hs hp hq

/-- **Theorem 2 ("if"), Agreement**: the object version of Fig. 1 satisfies Agreement when
`n ≥ max(2e + f − 1, 2f + 1)` and `e ≤ f`. -/
theorem object_agreement (hver : cfg.ver = .object) (hn1 : 2 * cfg.f + 1 ≤ Fintype.card P)
    (hn2 : 2 * cfg.e + cfg.f - 1 ≤ Fintype.card P) (hef : cfg.e ≤ cfg.f) (hs : Reachable cfg s)
    {p q : P} {u v : V} (hp : (s.loc p).decided = some u) (hq : (s.loc q).decided = some v) :
    u = v :=
  agreement ⟨hn1, hef, Or.inr ⟨hver, by omega⟩⟩ hs hp hq

/-- **Theorem 1 ("if"), Validity**: in the task version every decided value is the input of some
process. -/
theorem task_validity (hver : cfg.ver = .task) (hn1 : 2 * cfg.f + 1 ≤ Fintype.card P)
    (hn2 : 2 * cfg.e + cfg.f ≤ Fintype.card P) (hef : cfg.e ≤ cfg.f) (hs : Reachable cfg s)
    {p : P} {v : V} (hp : (s.loc p).decided = some v) : ∃ q, cfg.input q = v :=
  ((occ_of_reachable ⟨hn1, hef, Or.inl ⟨hver, hn2⟩⟩ hs).decided p v hp).1 hver

/-- **Theorem 2 ("if"), Validity**: in the object version every decided value is the argument of
an invocation `propose(v)`. -/
theorem object_validity (hver : cfg.ver = .object) (hn1 : 2 * cfg.f + 1 ≤ Fintype.card P)
    (hn2 : 2 * cfg.e + cfg.f - 1 ≤ Fintype.card P) (hef : cfg.e ≤ cfg.f) (hs : Reachable cfg s)
    {p : P} {v : V} (hp : (s.loc p).decided = some v) : ∃ q, (s.loc q).inv = some v :=
  ((occ_of_reachable ⟨hn1, hef, Or.inr ⟨hver, by omega⟩⟩ hs).decided p v hp).2 hver

/-- Lemma 1 / Lemma 5 for an actual fast decision (`Decide(p, 0, v)`: `p` decided `v` via the first
disjunct of line 10). -/
theorem fast_recover (hH : Hyp cfg) (hs : Reachable cfg s) {p : P} {v : V}
    (hd : .decide p 0 v ∈ s.msgs) {c : ℕ} {Q : Finset P} {rep : P → Snap P V}
    (hQc : Q.card = Fintype.card P - cfg.f) (hQ : ∀ q ∈ Q, .oneB q c (rep q) ∈ s.msgs)
    (hdec : ∀ q ∈ Q, (rep q).decided = none) (hz : ∀ q ∈ Q, (rep q).vbal = 0)
    (iv : Option V) : Select cfg Q rep iv v ∧ ∀ w, Select cfg Q rep iv w → w = v := by
  have hI := basic_of_reachable hH.f_lt hs
  obtain ⟨⟨P', -, hc, hP'⟩, -⟩ := hI.decide_fast p v hd
  have h := recover hH hI ⟨hc, fun q hq => Or.inl (hP' q hq), Or.inr hd⟩ hQc hQ hdec hz
  exact ⟨h.2 iv, h.1 iv⟩

/-- **Lemma 1** (task version, `n ≥ 2e + f`). If `v` was decided via the fast path at ballot 0,
then whenever a leader runs lines 26–38 on a quorum `Q` of `n − f` `1B` messages (of any ballot,
received before or after the decision) and reaches line 33 (no `decided_q`, `b_max = 0`), lines
33–38 select `v` (and nothing else). -/
theorem lemma1 (hver : cfg.ver = .task) (hn1 : 2 * cfg.f + 1 ≤ Fintype.card P)
    (hn2 : 2 * cfg.e + cfg.f ≤ Fintype.card P) (hef : cfg.e ≤ cfg.f) (hs : Reachable cfg s)
    {p : P} {v : V} (hd : .decide p 0 v ∈ s.msgs) {c : ℕ} {Q : Finset P} {rep : P → Snap P V}
    (hQc : Q.card = Fintype.card P - cfg.f) (hQ : ∀ q ∈ Q, .oneB q c (rep q) ∈ s.msgs)
    (hdec : ∀ q ∈ Q, (rep q).decided = none) (hz : ∀ q ∈ Q, (rep q).vbal = 0)
    (iv : Option V) : Select cfg Q rep iv v ∧ ∀ w, Select cfg Q rep iv w → w = v :=
  fast_recover ⟨hn1, hef, Or.inl ⟨hver, hn2⟩⟩ hs hd hQc hQ hdec hz iv

/-- **Lemma 5** (object version, `n ≥ 2e + f − 1`): same conclusion as Lemma 1. -/
theorem lemma5 (hver : cfg.ver = .object) (hn1 : 2 * cfg.f + 1 ≤ Fintype.card P)
    (hn2 : 2 * cfg.e + cfg.f - 1 ≤ Fintype.card P) (hef : cfg.e ≤ cfg.f) (hs : Reachable cfg s)
    {p : P} {v : V} (hd : .decide p 0 v ∈ s.msgs) {c : ℕ} {Q : Finset P} {rep : P → Snap P V}
    (hQc : Q.card = Fintype.card P - cfg.f) (hQ : ∀ q ∈ Q, .oneB q c (rep q) ∈ s.msgs)
    (hdec : ∀ q ∈ Q, (rep q).decided = none) (hz : ∀ q ∈ Q, (rep q).vbal = 0)
    (iv : Option V) : Select cfg Q rep iv v ∧ ∀ w, Select cfg Q rep iv w → w = v :=
  fast_recover ⟨hn1, hef, Or.inr ⟨hver, by omega⟩⟩ hs hd hQc hQ hdec hz iv

/-- **Lemma 4** (both versions, under `Hyp`). Given `b > 0`, if at least `n − f` processes have
received `2A(b, v)` and replied with `2B(b, v)`, then every `2A(b', v')` sent with `b' ≥ b` has
`v' = v`. -/
theorem lemma4 (hH : Hyp cfg) (hs : Reachable cfg s) {b : ℕ} {v : V} (hb : 0 < b)
    (hq : ∃ Q : Finset P, Fintype.card P - cfg.f ≤ Q.card ∧
      ∀ q ∈ Q, .twoB q (cfg.owner b) b v ∈ s.msgs)
    {b' : ℕ} {v' : V} (hbb : b ≤ b') (h2A : .twoA b' v' ∈ s.msgs) : v' = v := by
  obtain ⟨hI, hM⟩ := inv_of_reachable hH hs
  obtain ⟨Q, hQc, hQ⟩ := hq
  have hsq : SlowQuorum cfg s b v := ⟨Q, hQc, fun q hq => ⟨_, hQ q hq⟩⟩
  rcases hbb.lt_or_eq with hlt | rfl
  · exact hM.safe b v b' v' (Or.inr ⟨hb, hsq.potSlow hH hI hb⟩) hlt h2A
  · exact hI.twoA_unique _ _ _ h2A (hsq.twoA hH hI hb)

end results

/-- Non-vacuity of the model: a fast decision is reachable (`n = 3`, `e = f = 1`, task version, all
inputs `0`): `p₀` broadcasts `Propose(0)`, `p₁` accepts it, and `p₀` decides on the fast path. -/
example : ∃ s, Reachable (⟨.task, 1, 1, fun _ => 0, fun _ => 0, false⟩ : Config (Fin 3) ℕ) s ∧
    (s.loc 0).decided = some 0 := by
  set cfg : Config (Fin 3) ℕ := ⟨.task, 1, 1, fun _ => 0, fun _ => 0, false⟩
  have st1 := Step.sendPropose (cfg := cfg) (s := init cfg) (p := 0) (v := 0) (by simp [init, cfg])
  set s1 := (init cfg).send (.propose 0 0) with hs1
  have st2 := Step.recvPropose (cfg := cfg) (s := s1) (p := 1) (q := 0) (v := 0) (by simp [hs1])
    (by decide) (by simp [hs1, init]) (by simp [hs1, init]) (by simp [hs1, init, cfg, Accepts])
  set s2 := (s1.set 1 _).send (.twoB 1 0 0 0) with hs2
  have st3 := Step.fastDecide (cfg := cfg) (s := s2) (p := 0) (v := 0) {1} (by simp)
    (by simp [hs2]) (by simp [cfg]) (by simp [hs2, hs1, init]) (by simp [hs2, hs1, init])
  exact ⟨_, .tail (.tail (.tail .refl ⟨_, _, st1⟩) ⟨_, _, st2⟩) ⟨_, _, st3⟩, by simp⟩

end TwoStepConsensus.Fig1
