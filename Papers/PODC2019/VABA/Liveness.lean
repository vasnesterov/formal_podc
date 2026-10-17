import Papers.PODC2019.VABA.LivenessInv

/-!
# VABA: views complete (Lemmas 7, 17–19)

If honest parties keep delivering each other's messages, every view completes. We prove the
constructive form: from every reachable state in which all honest parties are in view `≥ j`,
honest steps alone (no corruption, no Byzantine signatures; any coin) lead to a state in which all
honest parties are in view `> j` (`view_progress`). Combined with `ExpectedViews.lean` this shows
that the probability bounds there are not vacuous: views do complete, and a view completes with
everybody deciding as soon as its leader's broadcast completed (Lemma 22).

Proof outline: if a skip certificate of view `j` exists (case A), every honest party in view `j`
invokes `elect`, `elect` returns (the coin was revealed by the first invocation), every honest party
receives the view-change messages of all honest parties and leaves the view. Otherwise (case B),
all honest parties are in the broadcast phase of view `j`; they deliver all four stages of the
broadcasts of all honest proposers (stage 1 passes validation by Lemma 15, `proposal_valid`),
so `n - f ≥ Q` broadcasts complete, every honest party sends a skip share, and we are in case A.
-/

namespace VABA

open Finset Relation

variable {P V : Type*} [Fintype P] [DecidableEq P] {C : Cfg P V}

/-- A step of an honest party (no corruption, no Byzantine signature), with any coin. -/
def HStep (C : Cfg P V) (s s' : Glob P V) : Prop :=
  ∃ (c : ℕ → P) (a : Act P V), Enabled C a s ∧ (∀ p, a ≠ .corrupt p) ∧
    (∀ p st, a ≠ .byzSign p st) ∧ s' = eff c a s

lemma HStep.reach {s s' : Glob P V} (h : HStep C s s') (hR : Reach C s) : Reach C s' := by
  obtain ⟨c, a, hE, -, -, rfl⟩ := h
  have := Reach.step c a hR
  unfold VABA.step at this
  simpa [hE] using this

lemma HStep.corrupt {s s' : Glob P V} (h : HStep C s s') : s'.corrupt = s.corrupt := by
  obtain ⟨c, a, -, h1, h2, rfl⟩ := h
  cases a with
  | corrupt p => exact absurd rfl (h1 p)
  | byzSign p st => exact absurd rfl (h2 p st)
  | recvVC p q j b => simp only [eff]; split <;> rfl
  | _ => rfl

/-! ### Monotonicity along honest steps -/

section hstep

variable {s s' : Glob P V}

lemma HStep.mono (h : HStep C s s') : Mono s s' := by
  obtain ⟨c, a, -, -, -, rfl⟩ := h; exact mono_eff c a s

lemma HStep.view_le (h : HStep C s s') (p : P) : (s.loc p).view ≤ (s'.loc p).view := by
  obtain ⟨c, a, hE, -, -, rfl⟩ := h
  rcases eff_pos_mono c a hE p with h | ⟨h, -⟩ <;> omega

lemma HStep.past (h : HStep C s s') {p : P} {i : ℕ} (hp : Past (s.loc p) i) :
    Past (s'.loc p) i := by
  obtain ⟨c, a, hE, -, -, rfl⟩ := h
  rcases eff_pos_mono c a hE p with h1 | ⟨h1, h2⟩
  · left; rcases hp with hp | ⟨hp, -⟩ <;> omega
  · rcases hp with hp | ⟨hp, hph⟩
    · left; omega
    · right; refine ⟨by omega, ?_⟩
      rw [hph] at h2; revert h2
      cases ((eff c a s).loc p).ph <;> simp [Phase.rk]

lemma HStep.d (h : HStep C s s') {p : P} {i : ℕ} {k : P} {st : ℕ} {w : V}
    (hw : (s.loc p).d i k st = some w) : (s'.loc p).d i k st = some w := by
  obtain ⟨c, a, hE, -, -, rfl⟩ := h; exact eff_d_mono c a hE hw

lemma HStep.rcvd (h : HStep C s s') {p q : P} {i : ℕ} (hq : q ∈ (s.loc p).rcvd i) :
    q ∈ (s'.loc p).rcvd i := by
  obtain ⟨c, a, -, -, -, rfl⟩ := h; exact eff_rcvd_mono c a hq

lemma HStep.of_enabled (c : ℕ → P) (a : Act P V) (hE : Enabled C a s)
    (h1 : ∀ p, a ≠ .corrupt p) (h2 : ∀ p st, a ≠ .byzSign p st) : HStep C s (eff c a s) :=
  ⟨c, a, hE, h1, h2, rfl⟩

end hstep

/-- `G` is preserved by honest steps from reachable states. -/
def Pres (C : Cfg P V) (G : Glob P V → Prop) : Prop :=
  ∀ s s', Reach C s → HStep C s s' → G s → G s'

lemma rtg_reach {s s' : Glob P V} (h : ReflTransGen (HStep C) s s') (hR : Reach C s) :
    Reach C s' := by
  induction h with
  | refl => exact hR
  | tail _ hst ih => exact hst.reach ih

lemma Pres.rtg {G : Glob P V → Prop} (hG : Pres C G) {s s' : Glob P V}
    (h : ReflTransGen (HStep C) s s') (hR : Reach C s) (hs : G s) : G s' := by
  induction h with
  | refl => exact hs
  | tail h1 hst ih => exact hG _ _ (rtg_reach h1 hR) hst ih

/-- Reaching a family of monotone goals one after the other. -/
lemma iterate {ι : Type*} [DecidableEq ι] (R : Glob P V → Prop) (G : ι → Glob P V → Prop)
    (hRr : ∀ s, R s → Reach C s) (hG : ∀ i, Pres C (G i))
    (h : ∀ i s, R s → ∃ s', ReflTransGen (HStep C) s s' ∧ R s' ∧ G i s')
    (T : Finset ι) {s : Glob P V} (hs : R s) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ R s' ∧ ∀ i ∈ T, G i s' := by
  induction T using Finset.induction_on with
  | empty => exact ⟨s, .refl, hs, by simp⟩
  | insert a T ha ih =>
    obtain ⟨s1, h1, hR1, hG1⟩ := ih
    obtain ⟨s2, h2, hR2, hG2⟩ := h a s1 hR1
    refine ⟨s2, h1.trans h2, hR2, fun i hi => ?_⟩
    rw [mem_insert] at hi
    rcases hi with rfl | hi
    · exact hG2
    · exact (hG i).rtg h2 (hRr _ hR1) (hG1 i hi)

/-! ### Honest parties alone form quorums -/

lemma card_of_honest (hQf : C.Q + C.f ≤ Fintype.card P) {s : Glob P V} (hR : Reach C s)
    {T : Finset P} (h : ∀ x, x ∉ s.corrupt → x ∈ T) : C.Q ≤ T.card := by
  have hc := hR.inv.card_corrupt
  have hcard : C.Q ≤ (s.corruptᶜ).card := by rw [card_compl]; omega
  refine hcard.trans (card_le_card ?_)
  intro x hx; rw [mem_compl] at hx; exact h x hx

lemma qc_of_honest (hQf : C.Q + C.f ≤ Fintype.card P) {s : Glob P V} (hR : Reach C s)
    {st : Stmt P V} (h : ∀ x, x ∉ s.corrupt → s.tok x st) : QC C.Q s st :=
  card_of_honest hQf hR (fun x hx => by rw [mem_signers]; exact h x hx)

/-! ### Case A: a skip certificate exists -/

section caseA

variable {j : ℕ}

/-- Goal A1: `p` has sent its view-change message of view `j`. -/
def GA1 (j : ℕ) (p : P) (s : Glob P V) : Prop := p ∈ s.corrupt ∨ Past (s.loc p) j

lemma pres_GA1 (p : P) : Pres C (GA1 j p) := by
  intro s s' _ h hs
  rcases hs with hs | hs
  · left; rw [h.corrupt]; exact hs
  · right; exact h.past hs

/-- Invariant of case A. -/
def RA (C : Cfg P V) (j : ℕ) (s : Glob P V) : Prop :=
  Reach C s ∧ QC C.Q s (.skip j) ∧ ∀ x, x ∉ s.corrupt → j ≤ (s.loc x).view

lemma pres_RA : Pres C (RA C j) := by
  rintro s s' - h ⟨hR, hq, hv⟩
  refine ⟨h.reach hR, QC_mono h.mono.tok hq, fun x hx => ?_⟩
  rw [h.corrupt] at hx; exact (hv x hx).trans (h.view_le x)

lemma stepA1 (p : P) (s : Glob P V) (hs : RA C j s) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ RA C j s' ∧ GA1 j p s' := by
  obtain ⟨hR, hq, hv⟩ := id hs
  by_cases hG : GA1 j p s
  · exact ⟨s, .refl, hs, hG⟩
  simp only [GA1, Past, not_or, not_and] at hG
  obtain ⟨hp, hlt, hvc⟩ := hG
  have hvj : (s.loc p).view = j := by have := hv p hp; omega
  have hel : ∃ s1, ReflTransGen (HStep C) s s1 ∧ RA C j s1 ∧ p ∉ s1.corrupt ∧
      (s1.loc p).view = j ∧ (s1.loc p).ph = .electing := by
    cases hph : (s.loc p).ph with
    | vc => exact absurd hph (hvc hvj.symm)
    | electing => exact ⟨s, .refl, hs, hp, hvj, hph⟩
    | bc =>
      have hE : Enabled C (.invokeElect p) s := ⟨hp, hph, hvj ▸ hq⟩
      have hst := HStep.of_enabled (fun _ => p) _ hE (by intro _ h; cases h)
        (by intro _ _ h; cases h)
      refine ⟨_, .single hst, pres_RA _ _ hR hst hs, ?_, ?_, ?_⟩
      · rw [hst.corrupt]; exact hp
      · simp [eff, hvj]
      · simp [eff]
  obtain ⟨s1, h1, hs1, hp1, hv1, hph1⟩ := hel
  have hrev := hs1.1.linv.electing_rev p hph1
  have hE : Enabled C (.electReturn p) s1 := ⟨hp1, hph1, Option.ne_none_iff_isSome.mp hrev⟩
  have hst := HStep.of_enabled (fun _ => p) _ hE (by intro _ h; cases h)
    (by intro _ _ h; cases h)
  refine ⟨_, h1.tail hst, pres_RA _ _ hs1.1 hst hs1, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · simp [eff, hv1]
  · simp [eff]

/-- Goal A2: `p` has received the view-change message of view `j` of `q`. -/
def GA2 (j : ℕ) (pq : P × P) (s : Glob P V) : Prop :=
  pq.1 ∈ s.corrupt ∨ pq.2 ∈ s.corrupt ∨ j < (s.loc pq.1).view ∨ pq.2 ∈ (s.loc pq.1).rcvd j

lemma pres_GA2 (pq : P × P) : Pres C (GA2 j pq) := by
  intro s s' _ h hs
  simp only [GA2, h.corrupt] at hs ⊢
  rcases hs with hs | hs | hs | hs
  · exact Or.inl hs
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (Or.inl (lt_of_lt_of_le hs (h.view_le _))))
  · exact Or.inr (Or.inr (Or.inr (h.rcvd hs)))

def RA2 (C : Cfg P V) (j : ℕ) (s : Glob P V) : Prop := RA C j s ∧ ∀ x, GA1 j x s

lemma pres_RA2 : Pres C (RA2 C j) := fun s s' hR h hs =>
  ⟨pres_RA s s' hR h hs.1, fun x => pres_GA1 x s s' hR h (hs.2 x)⟩

lemma stepA2 (hj : 1 ≤ j) (pq : P × P) (s : Glob P V) (hs : RA2 C j s) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ RA2 C j s' ∧ GA2 j pq s' := by
  obtain ⟨p, q⟩ := pq
  by_cases hG : GA2 j (p, q) s
  · exact ⟨s, .refl, hs, hG⟩
  simp only [GA2, not_or] at hG
  obtain ⟨hp, hq, -, -⟩ := hG
  obtain ⟨⟨hR, -, -⟩, hpast⟩ := id hs
  have hpp : Past (s.loc p) j := (hpast p).resolve_left hp
  have hqp : Past (s.loc q) j := (hpast q).resolve_left hq
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (hR.inv.lead_some p j hj hpp)
  have hE : Enabled C (.recvVC p q j true) s := ⟨hp, by rw [hl]; rfl, by simpa using hqp⟩
  have hst := HStep.of_enabled (fun _ => p) _ hE (by intro _ h; cases h)
    (by intro _ _ h; cases h)
  refine ⟨_, .single hst, pres_RA2 _ _ hR hst hs, Or.inr (Or.inr (Or.inr ?_))⟩
  simp [eff, hl]

/-- Goal A3: `p` has left view `j`. -/
def GA3 (j : ℕ) (p : P) (s : Glob P V) : Prop := p ∈ s.corrupt ∨ j < (s.loc p).view

lemma pres_GA3 (p : P) : Pres C (GA3 j p) := by
  intro s s' _ h hs
  rcases hs with hs | hs
  · left; rw [h.corrupt]; exact hs
  · right; exact lt_of_lt_of_le hs (h.view_le p)

def RA3 (C : Cfg P V) (j : ℕ) (s : Glob P V) : Prop := RA2 C j s ∧ ∀ pq, GA2 j pq s

lemma pres_RA3 : Pres C (RA3 C j) := fun s s' hR h hs =>
  ⟨pres_RA2 s s' hR h hs.1, fun pq => pres_GA2 pq s s' hR h (hs.2 pq)⟩

lemma stepA3 (hQf : C.Q + C.f ≤ Fintype.card P) (p : P) (s : Glob P V) (hs : RA3 C j s) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ RA3 C j s' ∧ GA3 j p s' := by
  by_cases hG : GA3 j p s
  · exact ⟨s, .refl, hs, hG⟩
  simp only [GA3, not_or, not_lt] at hG
  obtain ⟨hp, hle⟩ := hG
  obtain ⟨⟨⟨hR, -, hv⟩, hpast⟩, hrc⟩ := id hs
  have hvj : (s.loc p).view = j := le_antisymm hle (hv p hp)
  have hph : (s.loc p).ph = .vc := by
    rcases (hpast p).resolve_left hp with h | ⟨-, h⟩
    · omega
    · exact h
  have hcard : C.Q ≤ ((s.loc p).rcvd (s.loc p).view).card := by
    rw [hvj]
    apply card_of_honest hQf hR
    intro x hx
    rcases hrc (p, x) with h | h | h | h
    · exact absurd h hp
    · exact absurd h hx
    · exact absurd h (not_lt.mpr hle)
    · exact h
  have hE : Enabled C (.exitView p) s := ⟨hp, hph, hcard⟩
  have hst := HStep.of_enabled (fun _ => p) _ hE (by intro _ h; cases h)
    (by intro _ _ h; cases h)
  refine ⟨_, .single hst, pres_RA3 _ _ hR hst hs, Or.inr ?_⟩
  simp [eff, hvj]

/-- Case A: with a skip certificate of view `j`, all honest parties leave view `j`. -/
lemma caseA (hQf : C.Q + C.f ≤ Fintype.card P) (hj : 1 ≤ j) {s : Glob P V} (hs : RA C j s) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ ∀ p, p ∉ s'.corrupt → j < (s'.loc p).view := by
  obtain ⟨s1, h1, hs1, hG1⟩ := iterate (RA C j) (GA1 j) (fun s h => h.1)
    (fun p => pres_GA1 p) (fun p s h => stepA1 p s h) univ hs
  have hs1' : RA2 C j s1 := ⟨hs1, fun x => hG1 x (mem_univ x)⟩
  obtain ⟨s2, h2, hs2, hG2⟩ := iterate (RA2 C j) (GA2 j) (fun s h => h.1.1)
    (fun pq => pres_GA2 pq) (fun pq s h => stepA2 hj pq s h) univ hs1'
  have hs2' : RA3 C j s2 := ⟨hs2, fun pq => hG2 pq (mem_univ pq)⟩
  obtain ⟨s3, h3, -, hG3⟩ := iterate (RA3 C j) (GA3 j) (fun s h => h.1.1.1)
    (fun p => pres_GA3 p) (fun p s h => stepA3 hQf p s h) univ hs2'
  exact ⟨s3, h1.trans (h2.trans h3), fun p hp => (hG3 p (mem_univ p)).resolve_left hp⟩

end caseA

/-! ### Case B: no skip certificate, all honest parties broadcast in view `j` -/

section caseB

variable {j : ℕ}

/-- Invariant of case B. -/
def RB (C : Cfg P V) (j : ℕ) (s : Glob P V) : Prop :=
  Reach C s ∧ ∀ x, x ∉ s.corrupt → (s.loc x).view = j ∧ (s.loc x).ph = .bc

/-- Goal B: `p` has delivered stage `st` of the broadcast of `q` in view `j`. -/
def GB (j st : ℕ) (pq : P × P) (s : Glob P V) : Prop :=
  pq.1 ∈ s.corrupt ∨ pq.2 ∈ s.corrupt ∨ (s.loc pq.1).d j pq.2 st ≠ none

lemma pres_GB (st : ℕ) (pq : P × P) : Pres C (GB j st pq) := by
  intro s s' _ h hs
  simp only [GB, h.corrupt] at hs ⊢
  rcases hs with hs | hs | hs
  · exact Or.inl hs
  · exact Or.inr (Or.inl hs)
  · right; right
    rcases hw : (s.loc pq.1).d j pq.2 st with _ | w
    · exact absurd hw hs
    · rw [h.d hw]; simp

/-- Honest parties deliver the proposal of an honest proposer. -/
lemma honest_val {s : Glob P V} (hR : Reach C s) {x q : P} {st : ℕ} (hq : q ∉ s.corrupt)
    (h : (s.loc x).d j q st ≠ none) : (s.loc x).d j q st = some ((s.loc q).prop j).2 := by
  rcases hw : (s.loc x).d j q st with _ | w
  · exact absurd hw h
  · rw [(hR.linv.d_prop x j q st w hq hw).2]

omit [Fintype P] in
lemma deliver_view_ph (c : ℕ → P) (p k : P) (st : ℕ) (v : V) (r : ℕ) (s : Glob P V) (x : P) :
    ((eff c (.deliver p k st v r) s).loc x).view = (s.loc x).view ∧
      ((eff c (.deliver p k st v r) s).loc x).ph = (s.loc x).ph := by
  by_cases hx : x = p
  · subst hx; simp [eff]
  · simp [eff, hx]

lemma stepB (hQ : Fintype.card P + C.f < 2 * C.Q) (hQf : C.Q + C.f ≤ Fintype.card P)
    (hinput : ∀ p, C.valid (C.input p)) (st : ℕ) (hst1 : 1 ≤ st) (hst4 : st ≤ 4)
    (pq : P × P) (s : Glob P V) (hs : RB C j s ∧ (st ≠ 1 → ∀ pq, GB j (st - 1) pq s)) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ (RB C j s' ∧ (st ≠ 1 → ∀ pq, GB j (st - 1) pq s')) ∧
      GB j st pq s' := by
  obtain ⟨p, q⟩ := pq
  by_cases hG : GB j st (p, q) s
  · exact ⟨s, .refl, hs, hG⟩
  simp only [GB, not_or, not_not] at hG
  obtain ⟨hp, hq, hnone⟩ := hG
  obtain ⟨⟨hR, hvp⟩, hprev⟩ := id hs
  obtain ⟨hpv, hpph⟩ := hvp p hp
  obtain ⟨hqv, -⟩ := hvp q hq
  have hval : Valid C s (s.loc p) q st ((s.loc q).prop j).2 ((s.loc q).prop j).1 := by
    by_cases h1 : st = 1
    · subst h1
      have := proposal_valid (q := q) hQ hinput hR hpph (le_of_eq (hpv.trans hqv.symm))
      rwa [hpv] at this
    · simp only [Valid, h1, ↓reduceIte]
      rw [hpv]
      apply qc_of_honest hQf hR
      intro x hx
      rw [hR.inv.tok_pb x hx]
      exact honest_val hR hq (((hprev h1 (x, q)).resolve_left hx).resolve_left hq)
  have hE : Enabled C (.deliver p q st ((s.loc q).prop j).2 ((s.loc q).prop j).1) s :=
    ⟨hp, hpph, hst1, hst4, by rw [hpv]; exact hnone, hval,
      Or.inr ⟨by rw [hpv, hqv], by rw [hpv], fun _ => by rw [hpv]⟩⟩
  have hst := HStep.of_enabled (fun _ => p) _ hE (by intro _ h; cases h)
    (by intro _ _ h; cases h)
  refine ⟨_, .single hst, ⟨⟨hst.reach hR, fun x hx => ?_⟩, fun h1 pq => ?_⟩, ?_⟩
  · rw [hst.corrupt] at hx
    rw [(deliver_view_ph _ _ _ _ _ _ _ x).1, (deliver_view_ph _ _ _ _ _ _ _ x).2]
    exact hvp x hx
  · exact pres_GB _ pq _ _ hR hst (hprev h1 pq)
  · right; right
    simp [eff, hpv]

lemma stageB (hQ : Fintype.card P + C.f < 2 * C.Q) (hQf : C.Q + C.f ≤ Fintype.card P)
    (hinput : ∀ p, C.valid (C.input p)) (st : ℕ) (hst1 : 1 ≤ st) (hst4 : st ≤ 4)
    {s : Glob P V} (hs : RB C j s) (hprev : st ≠ 1 → ∀ pq, GB j (st - 1) pq s) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ RB C j s' ∧ ∀ pq, GB j st pq s' := by
  obtain ⟨s', h1, hs', hG⟩ := iterate (fun s => RB C j s ∧ (st ≠ 1 → ∀ pq, GB j (st - 1) pq s))
    (GB j st) (fun s h => h.1.1) (fun pq => pres_GB st pq)
    (fun pq s h => stepB hQ hQf hinput st hst1 hst4 pq s h) univ ⟨hs, hprev⟩
  exact ⟨s', h1, hs'.1, fun pq => hG pq (mem_univ pq)⟩

/-- Goal S: `p` has sent its skip share of view `j`. -/
def GS (j : ℕ) (p : P) (s : Glob P V) : Prop := p ∈ s.corrupt ∨ s.tok p (.skip j)

lemma pres_GS (p : P) : Pres C (GS j p) := by
  intro s s' _ h hs
  rcases hs with hs | hs
  · left; rw [h.corrupt]; exact hs
  · right; exact h.mono.tok _ _ hs

def RS (C : Cfg P V) (j : ℕ) (s : Glob P V) : Prop :=
  Reach C s ∧ (∀ x, x ∉ s.corrupt → j ≤ (s.loc x).view) ∧ C.Q ≤ (completed C.Q s j).card

lemma pres_RS : Pres C (RS C j) := by
  rintro s s' - h ⟨hR, hv, hc⟩
  refine ⟨h.reach hR, fun x hx => ?_, hc.trans (card_le_card (completed_mono h.mono.tok j))⟩
  rw [h.corrupt] at hx; exact (hv x hx).trans (h.view_le x)

lemma stepS (p : P) (s : Glob P V) (hs : RS C j s) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ RS C j s' ∧ GS j p s' := by
  by_cases hG : GS j p s
  · exact ⟨s, .refl, hs, hG⟩
  simp only [GS, not_or] at hG
  have hE : Enabled C (.skipShare p j) s := ⟨hG.1, hs.2.2⟩
  have hst := HStep.of_enabled (fun _ => p) _ hE (by intro _ h; cases h)
    (by intro _ _ h; cases h)
  refine ⟨_, .single hst, pres_RS _ _ hs.1 hst hs, Or.inr ?_⟩
  simp [eff]

/-- Case B: all honest parties in the broadcast phase of view `j` produce a skip certificate. -/
lemma caseB (hQ : Fintype.card P + C.f < 2 * C.Q) (hQf : C.Q + C.f ≤ Fintype.card P)
    (hinput : ∀ p, C.valid (C.input p)) {s : Glob P V} (hs : RB C j s) :
    ∃ s', ReflTransGen (HStep C) s s' ∧ RA C j s' := by
  obtain ⟨s1, h1, hs1, hG1⟩ := stageB hQ hQf hinput 1 le_rfl (by norm_num) hs (by simp)
  obtain ⟨s2, h2, hs2, hG2⟩ := stageB hQ hQf hinput 2 (by norm_num) (by norm_num) hs1
    (fun _ => hG1)
  obtain ⟨s3, h3, hs3, hG3⟩ := stageB hQ hQf hinput 3 (by norm_num) (by norm_num) hs2
    (fun _ => hG2)
  obtain ⟨s4, h4, ⟨hR4, hv4⟩, hG4⟩ := stageB hQ hQf hinput 4 (by norm_num) le_rfl hs3
    (fun _ => hG3)
  have hcomp : C.Q ≤ (completed C.Q s4 j).card := by
    apply card_of_honest hQf hR4
    intro q hq
    rw [mem_completed]
    refine ⟨((s4.loc q).prop j).2, qc_of_honest hQf hR4 fun x hx => ?_⟩
    rw [hR4.inv.tok_pb x hx]
    exact honest_val hR4 hq (((hG4 (x, q)).resolve_left hx).resolve_left hq)
  have hRS : RS C j s4 := ⟨hR4, fun x hx => (hv4 x hx).1.ge, hcomp⟩
  obtain ⟨s5, h5, ⟨hR5, hv5, -⟩, hG5⟩ := iterate (RS C j) (GS j) (fun s h => h.1)
    (fun p => pres_GS p) (fun p s h => stepS p s h) univ hRS
  refine ⟨s5, h1.trans (h2.trans (h3.trans (h4.trans h5))), hR5, ?_, hv5⟩
  exact qc_of_honest hQf hR5 fun x hx => (hG5 x (mem_univ x)).resolve_left hx

end caseB

/-- **Lemma 19** (views complete), constructive form: from a reachable state in which every honest
party is in view `≥ j`, honest steps lead to a state in which every honest party is in view
`> j`. Needs `Q ≤ n - f` (honest parties alone form certificates) and externally valid inputs. -/
theorem view_progress (hQ : Fintype.card P + C.f < 2 * C.Q) (hQf : C.Q + C.f ≤ Fintype.card P)
    (hinput : ∀ p, C.valid (C.input p)) {s : Glob P V} (hR : Reach C s) {j : ℕ} (hj : 1 ≤ j)
    (hall : ∀ p, p ∉ s.corrupt → j ≤ (s.loc p).view) :
    ∃ s', Relation.ReflTransGen (HStep C) s s' ∧ ∀ p, p ∉ s'.corrupt → j < (s'.loc p).view := by
  have hL := hR.linv
  have I := hR.inv
  by_cases hskip : QC C.Q s (.skip j)
  · exact caseA hQf hj ⟨hR, hskip, hall⟩
  have hnp : ∀ x, ¬ Past (s.loc x) j := by
    intro x hx
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (I.lead_some x j hj hx)
    exact hskip (hL.rev_qc j (by rw [(I.lead_spec x j l hl).2]; simp))
  have hB : RB C j s := by
    refine ⟨hR, fun x hx => ?_⟩
    have h1 := hall x hx
    have h2 := hnp x
    simp only [Past, not_or, not_and] at h2
    have hv : (s.loc x).view = j := by omega
    refine ⟨hv, ?_⟩
    cases hph : (s.loc x).ph with
    | bc => rfl
    | electing =>
      have := hL.electing_rev x hph
      rw [hv] at this
      exact absurd (hL.rev_qc j this) hskip
    | vc => exact absurd hph (h2.2 hv.symm)
  obtain ⟨s1, h1, hs1⟩ := caseB hQ hQf hinput hB
  obtain ⟨s2, h2, hs2⟩ := caseA hQf hj hs1
  exact ⟨s2, h1.trans h2, hs2⟩

end VABA
