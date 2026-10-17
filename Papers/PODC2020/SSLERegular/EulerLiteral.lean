import Papers.PODC2020.SSLERegular.EulerCycle

/-!
# SS-EulerCycle as printed has no output-stable configuration (Lemma 3.1 and Theorem 3.3 fail)

In Protocol 1 the coherence check of an interaction with initiator `u` and responder `v` only
looks for a virtual edge **from `u` to `v`**; otherwise it sets `u.errFlag`. But an Euler cycle
traverses each edge `{u, v}` in only one direction, and the scheduler also lets `v` initiate.
More precisely (`literal_error_reachable`): in every configuration, either some ordered adjacent
pair has no virtual edge `u → v` (one interaction raises an error), or every node `u` has a
successor slot for each of its `> k` neighbours with only `k` successor slots, so two neighbours
share a colour, which SS-TwoHop detects by the interaction sequence `(u,v), (u,w), (u,v)` given in
the paper; the recolouring then breaks the virtual edge and raises an error. From an error the
initiator's state is randomized, so its output can change. Hence **no configuration is
output-stable** (`literal_not_outputStable`) and the printed protocol does not solve SSLE on any
graph whose degrees exceed `k` (`literal_not_solvesSSLE`), e.g. every `2k`-regular graph with
`k ≥ 1`, whatever the ring protocol.
-/

open Finset

namespace SSLERegular

variable {RS : Type*} {k : ℕ}

/-- The skeleton of a state: colour and the predecessor/successor colours of the virtual nodes. -/
def skel (s : EState k RS) : Fin (4 * k ^ 2) × (Fin k → Fin (4 * k ^ 2) × Fin (4 * k ^ 2)) :=
  (s.color, fun i => ((s.node i).pred, (s.node i).succ))

lemma fmatch_of_skel {u v u' v' : EState k RS} (hu : skel u' = skel u) (hv : skel v' = skel v)
    (i j : Fin k) : FMatch u' v' i j ↔ FMatch u v i j := by
  simp only [skel, Prod.mk.injEq] at hu hv
  have hu1 := hu.1; have hv1 := hv.1
  have hu2 := congrFun hu.2 i; have hv2 := congrFun hv.2 j
  simp only [Prod.mk.injEq] at hu2 hv2
  simp only [FMatch, hu1, hv1, hu2.2, hv2.1]

lemma ssToken_skel (lead : RS → Bool) (a b : VNode k RS) :
    (ssToken lead a b).1.pred = a.pred ∧ (ssToken lead a b).1.succ = a.succ ∧
    (ssToken lead a b).2.pred = b.pred ∧ (ssToken lead a b).2.succ = b.succ := by
  unfold ssToken; dsimp only; split_ifs <;> simp

lemma vEdge_skel (R : RingProtocol RS) (ρ : RS → RS → RS × RS) (a b : VNode k RS) :
    (vEdge R ρ a b).1.pred = a.pred ∧ (vEdge R ρ a b).1.succ = a.succ ∧
    (vEdge R ρ a b).2.pred = b.pred ∧ (vEdge R ρ a b).2.succ = b.succ := by
  unfold vEdge
  have := ssToken_skel R.lead { a with ringState := (ρ a.ringState b.ringState).1 }
    { b with ringState := (ρ a.ringState b.ringState).2 }
  simpa using this

lemma runEdge_skel (R : RingProtocol RS) (ρ : RS → RS → RS × RS) (x y : EState k RS)
    (i j : Fin k) :
    skel (runEdge R ρ x y i j).1 = skel x ∧ skel (runEdge R ρ x y i j).2 = skel y := by
  obtain ⟨h1, h2, h3, h4⟩ := vEdge_skel R ρ (x.node i) (y.node j)
  constructor
  · simp only [runEdge, skel, Prod.mk.injEq, true_and]
    funext l
    by_cases hl : l = i
    · subst hl; simp [h1, h2]
    · simp [Function.update_of_ne hl]
  · simp only [runEdge, skel, Prod.mk.injEq, true_and]
    funext l
    by_cases hl : l = j
    · subst hl; simp [h3, h4]
    · simp [Function.update_of_ne hl]

/-- The parts of a state that the ring/token/detection stages never change. -/
def Frame (s s' : EState k RS) : Prop :=
  skel s' = skel s ∧ s'.prevColor = s.prevColor ∧ s'.colorBit = s.colorBit

lemma Frame.refl (s : EState k RS) : Frame s s := ⟨rfl, rfl, rfl⟩

lemma Frame.trans {a b c : EState k RS} (h1 : Frame a b) (h2 : Frame b c) : Frame a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

lemma runEdge_frame (R : RingProtocol RS) (ρ : RS → RS → RS × RS) (x y : EState k RS)
    (i j : Fin k) : Frame x (runEdge R ρ x y i j).1 ∧ Frame y (runEdge R ρ x y i j).2 := by
  obtain ⟨h1, h2⟩ := runEdge_skel R ρ x y i j
  exact ⟨⟨h1, rfl, rfl⟩, ⟨h2, rfl, rfl⟩⟩

lemma ringPart_frame (bidir : Bool) (R : RingProtocol RS) (ch : EChoice k RS) (u v : EState k RS) :
    Frame u (ringPart bidir R ch u v).1 ∧ Frame v (ringPart bidir R ch u v).2 ∧
    (u.errFlag = true → (ringPart bidir R ch u v).1.errFlag = true) ∧
    (ringPart bidir R ch u v).2.errFlag = v.errFlag := by
  unfold ringPart
  split_ifs with h1 h2
  · obtain ⟨a, b⟩ := runEdge_frame R ch.ρ u v (ch.pick u v).1 (ch.pick u v).2
    exact ⟨a, b, fun h => by simpa [runEdge] using h, by simp [runEdge]⟩
  · obtain ⟨a, b⟩ := runEdge_frame R ch.ρ v u (ch.pick v u).1 (ch.pick v u).2
    exact ⟨b, a, fun h => by simpa [runEdge] using h, by simp [runEdge]⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, Frame.refl v, fun _ => rfl, rfl⟩

lemma tokenDetect_frame (w : EState k RS × EState k RS) :
    Frame w.1 (tokenDetect w).1 ∧ (tokenDetect w).2 = w.2 ∧
    (w.1.errFlag = true → (tokenDetect w).1.errFlag = true) := by
  unfold tokenDetect
  split_ifs
  · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl⟩
  · exact ⟨Frame.refl _, rfl, id⟩

/-- SS-TwoHop with "new colours = old colours". -/
lemma twoHopE_keep (rb : Bool) (u v : EState k RS) :
    twoHopE v.color u.color rb u v = ({ u with prevColor := v.color, colorBit := rb },
      { v with prevColor := u.color, colorBit := rb }) := by
  unfold twoHopE; split_ifs <;> rfl

/-- SS-TwoHop on a detected conflict. -/
lemma twoHopE_conflict (rc1 rc2 : Fin (4 * k ^ 2)) (rb : Bool) {u v : EState k RS}
    (h : u.prevColor = v.color ∧ v.prevColor = u.color ∧ u.colorBit ≠ v.colorBit) :
    twoHopE rc1 rc2 rb u v = ({ u with color := rc2, prevColor := rc1, colorBit := rb },
      { v with color := rc1, prevColor := rc2, colorBit := rb }) := by
  unfold twoHopE; rw [if_pos h]

/-- Outcome of an interaction: either the initiator ends with `errFlag = true` (if `b1 = true`),
or nothing but the SS-TwoHop memory changed in the skeleton/bit data. -/
lemma eulerStep_cases (bidir : Bool) (R : RingProtocol RS) (ch : EChoice k RS) (hb1 : ch.b1 = true)
    (u v : EState k RS) :
    (eulerStep bidir R ch u v).1.errFlag = true ∨
      (Frame (twoHopE ch.rc1 ch.rc2 ch.rb u v).1 (eulerStep bidir R ch u v).1 ∧
       Frame (twoHopE ch.rc1 ch.rc2 ch.rb u v).2 (eulerStep bidir R ch u v).2 ∧
       (eulerStep bidir R ch u v).1.errFlag = false ∧
       (eulerStep bidir R ch u v).2.errFlag = (twoHopE ch.rc1 ch.rc2 ch.rb u v).2.errFlag) := by
  set w := twoHopE ch.rc1 ch.rc2 ch.rb u v
  obtain ⟨a1, a2, -, a4⟩ := ringPart_frame bidir R ch w.1 w.2
  obtain ⟨b1, b2, -⟩ := tokenDetect_frame (ringPart bidir R ch w.1 w.2)
  unfold eulerStep randChangeE
  dsimp only
  split_ifs with h
  · left; simp [hb1]
  · right
    refine ⟨a1.trans b1, ?_, by simpa using h, ?_⟩
    · rw [b2]; exact a2
    · rw [b2]; exact a4

lemma eulerStep_err (bidir : Bool) (R : RingProtocol RS) (ch : EChoice k RS) (u v : EState k RS)
    (h : (tokenDetect (ringPart bidir R ch (twoHopE ch.rc1 ch.rc2 ch.rb u v).1
      (twoHopE ch.rc1 ch.rc2 ch.rb u v).2)).1.errFlag = true) :
    eulerStep bidir R ch u v = ({ ch.rand with errFlag := ch.b1 },
      { (tokenDetect (ringPart bidir R ch (twoHopE ch.rc1 ch.rc2 ch.rb u v).1
      (twoHopE ch.rc1 ch.rc2 ch.rb u v).2)).2 with errFlag := ch.b2 }) := by
  unfold eulerStep randChangeE
  dsimp only
  rw [if_pos h]

/-- An initiator with `errFlag = true` can take any state. -/
lemma eulerStep_errFlag (bidir : Bool) (R : RingProtocol RS) (ch : EChoice k RS)
    {u : EState k RS} (hu : u.errFlag = true) (v : EState k RS) :
    (eulerStep bidir R ch u v).1 = { ch.rand with errFlag := ch.b1 } := by
  rw [eulerStep_err]
  have h1 : (twoHopE ch.rc1 ch.rc2 ch.rb u v).1.errFlag = true := by
    unfold twoHopE; split_ifs <;> simpa using hu
  exact (tokenDetect_frame _).2.2 ((ringPart_frame bidir R ch _ _).2.2.1 h1)

/-- A choice with prescribed SS-TwoHop data and `RandBit1 = true`. -/
def EChoice.with3 (ch0 : EChoice k RS) (c1 c2 : Fin (4 * k ^ 2)) (rb : Bool) : EChoice k RS :=
  { ch0 with rc1 := c1, rc2 := c2, rb := rb, b1 := true }

/-- A state with a new SS-TwoHop memory. -/
def EState.withPrev (s : EState k RS) (c : Fin (4 * k ^ 2)) (b : Bool) : EState k RS :=
  { s with prevColor := c, colorBit := b }

lemma EChoice.with3_valid {R : RingProtocol RS} {ch0 : EChoice k RS} (h : ch0.Valid R)
    (c1 c2 : Fin (4 * k ^ 2)) (rb : Bool) : (ch0.with3 c1 c2 rb).Valid R := h

section Graph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {R : RingProtocol RS}

lemma step_of_choice (bidir : Bool) (C : V → EState k RS) {u v : V} (huv : G.Adj u v)
    (ch : EChoice k RS) (hch : ch.Valid R) :
    (ssEuler bidir k R).Step G C (upd C u v (eulerStep bidir R ch (C u) (C v))) :=
  ⟨u, v, huv, _, ⟨ch, hch, rfl⟩, rfl⟩

/-- From an error at `u` (with a neighbour), the output of `u` can be made `true` or `false`. -/
lemma output_flexible (bidir : Bool) (hR : ∀ a b, (R.δ a b).Nonempty) (hk : 1 ≤ k)
    {r0 r1 : RS} (hr0 : R.lead r0 = false) (hr1 : R.lead r1 = true)
    (C : V → EState k RS) {u v : V} (huv : G.Adj u v) (hu : (C u).errFlag = true) (b : Bool) :
    ∃ D, (ssEuler bidir k R).Step G C D ∧ (D u).out R = b := by
  obtain ⟨ch, hch, -⟩ := exists_valid_choice R hR (C u).color (C u)
  let s : EState k RS := { C u with node := fun i =>
    { (C u).node i with ringState := if b then (if i.val = 0 then r1 else r0) else r0 } }
  refine ⟨_, step_of_choice bidir C huv { ch with rand := s } hch, ?_⟩
  rw [upd_left _ (G.ne_of_adj huv), eulerStep_errFlag bidir R _ hu]
  simp only [EState.out, s]
  cases b
  · simp [hr0]
  · simp only [if_true]
    refine decide_eq_true ⟨⟨0, hk⟩, by simp [hr1]⟩

/-- **Errors are always reachable** in the printed protocol, on any graph whose degrees all
exceed `k`. -/
theorem literal_error_reachable [Fintype V] [DecidableRel G.Adj] (hR : ∀ a b, (R.δ a b).Nonempty)
    (hk : 1 ≤ k) (hdeg : ∀ v, k < G.degree v) (hedge : ∃ u v, G.Adj u v) (C : V → EState k RS) :
    ∃ D u, (ssEuler false k R).Reachable G C D ∧ (D u).errFlag = true := by
  classical
  obtain ⟨u, -, -⟩ := hedge
  obtain ⟨ch0, hch0, -⟩ := exists_valid_choice R hR (C u).color (C u)
  -- Case A: an error is already present
  by_cases hA : ∃ u, (C u).errFlag = true
  · obtain ⟨u, hu⟩ := hA; exact ⟨C, u, Relation.ReflTransGen.refl, hu⟩
  push Not at hA
  -- a generic "keep colours" interaction with `b1 = true`
  have keep : ∀ (C : V → EState k RS) (u v : V), G.Adj u v → ∀ rb : Bool,
      (ssEuler false k R).Step G C
        (upd C u v (eulerStep false R (ch0.with3 (C v).color (C u).color rb) (C u) (C v))) ∧
      ((eulerStep false R (ch0.with3 (C v).color (C u).color rb) (C u) (C v)).1.errFlag = true ∨
        (Frame ((C u).withPrev (C v).color rb)
          (eulerStep false R (ch0.with3 (C v).color (C u).color rb) (C u) (C v)).1 ∧
         Frame ((C v).withPrev (C u).color rb)
          (eulerStep false R (ch0.with3 (C v).color (C u).color rb) (C u) (C v)).2)) := by
    intro C u v huv rb
    refine ⟨step_of_choice false C huv _ (EChoice.with3_valid hch0 _ _ _), ?_⟩
    rcases eulerStep_cases false R (ch0.with3 (C v).color (C u).color rb) rfl (C u) (C v) with
      h | ⟨h1, h2, -, -⟩
    · exact Or.inl h
    · right
      have ht := twoHopE_keep rb (C u) (C v)
      simp only [EChoice.with3] at h1 h2 ht ⊢
      rw [ht] at h1 h2
      exact ⟨h1, h2⟩
  -- Case B: some ordered adjacent pair has no virtual edge `u → v`
  by_cases hB : ∃ u v, G.Adj u v ∧ ¬ ∃ i j, FMatch (C u) (C v) i j
  · obtain ⟨u, v, huv, hno⟩ := hB
    let ch := ch0.with3 (C v).color (C u).color ch0.rb
    refine ⟨_, u, Relation.ReflTransGen.single
      (step_of_choice false C huv ch (EChoice.with3_valid hch0 _ _ _)), ?_⟩
    rw [upd_left _ (G.ne_of_adj huv)]
    rw [eulerStep_err]
    · rfl
    · have ht := twoHopE_keep ch0.rb (C u) (C v)
      simp only [ch, EChoice.with3]
      rw [ht]
      apply (tokenDetect_frame _).2.2
      have : ¬ ∃ i j, FMatch ((C u).withPrev (C v).color ch0.rb)
          ((C v).withPrev (C u).color ch0.rb) i j := by
        simpa [FMatch, EState.withPrev] using hno
      simp only [EState.withPrev] at this
      simp [ringPart, this]
  push Not at hB
  -- Case C: two neighbours of some node share a colour (pigeonhole on successor slots)
  have hsucc : ∀ x : G.neighborSet u, ∃ i, ((C u).node i).succ = (C x).color := by
    rintro ⟨x, hx⟩
    by_contra h
    push Not at h
    obtain ⟨i, j, hij⟩ : ∃ i j, FMatch (C u) (C x) i j := by
      by_contra h'; push Not at h'
      exact absurd (hB u x hx) (by simpa using h')
    exact h i hij.1
  choose f hf using hsucc
  have hcard : Fintype.card (Fin k) < Fintype.card (G.neighborSet u) := by
    rw [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree]; exact hdeg u
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩, hvw, hfvw⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hvw' : v ≠ w := fun h => hvw (Subtype.ext h)
  have hcol : (C v).color = (C w).color := by
    have a := hf ⟨v, hv⟩; have b := hf ⟨w, hw⟩
    simp only at a b; rw [← a, ← b, hfvw]
  have huv : G.Adj u v := hv
  have huw : G.Adj u w := hw
  have hne_uv : u ≠ v := G.ne_of_adj huv
  have hne_uw : u ≠ w := G.ne_of_adj huw
  -- interaction 1: (u, v) with bit `false`
  obtain ⟨st1, r1⟩ := keep C u v huv false
  set C1 := upd C u v (eulerStep false R (ch0.with3 (C v).color (C u).color false) (C u) (C v))
    with hC1
  rcases r1 with e1 | ⟨f1u, f1v⟩
  · exact ⟨C1, u, Relation.ReflTransGen.single st1, by rw [hC1, upd_left _ hne_uv]; exact e1⟩
  have hC1u : Frame ((C u).withPrev (C v).color false) (C1 u) := by
    rw [hC1, upd_left _ hne_uv]; exact f1u
  have hC1v : Frame ((C v).withPrev (C u).color false) (C1 v) := by
    rw [hC1, upd_right]; exact f1v
  have hC1w : C1 w = C w := by rw [hC1, upd_other _ (Ne.symm hne_uw) hvw'.symm]
  -- interaction 2: (u, w) with bit `true`
  obtain ⟨st2, r2⟩ := keep C1 u w huw true
  set C2 := upd C1 u w (eulerStep false R (ch0.with3 (C1 w).color (C1 u).color true) (C1 u) (C1 w))
    with hC2
  rcases r2 with e2 | ⟨f2u, -⟩
  · exact ⟨C2, u, (Relation.ReflTransGen.single st1).tail st2,
      by rw [hC2, upd_left _ hne_uw]; exact e2⟩
  have hC2u : Frame ((C1 u).withPrev (C1 w).color true) (C2 u) := by
    rw [hC2, upd_left _ hne_uw]; exact f2u
  have hC2v : C2 v = C1 v := by rw [hC2, upd_other _ (Ne.symm hne_uv) hvw']
  -- skeleton bookkeeping
  have sku : skel (C2 u) = skel (C u) := by
    rw [hC2u.1]; simp only [skel, EState.withPrev]
    have := hC1u.1; simp only [skel, EState.withPrev] at this; exact this
  have skv : skel (C2 v) = skel (C v) := by
    rw [hC2v, hC1v.1]; simp [skel, EState.withPrev]
  have colu : (C2 u).color = (C u).color := congrArg Prod.fst sku
  have colv : (C2 v).color = (C v).color := congrArg Prod.fst skv
  have prevu : (C2 u).prevColor = (C v).color := by
    rw [hC2u.2.1]; simp only [EState.withPrev]; rw [hC1w, ← hcol]
  have bitu : (C2 u).colorBit = true := by rw [hC2u.2.2]; rfl
  have prevv : (C2 v).prevColor = (C u).color := by rw [hC2v, hC1v.2.1]; rfl
  have bitv : (C2 v).colorBit = false := by rw [hC2v, hC1v.2.2]; rfl
  -- interaction 3: (u, v) detects the conflict; recolour `v` with a colour outside `u`'s slots
  obtain ⟨c', hc'⟩ : ∃ c' : Fin (4 * k ^ 2), ∀ i, ((C u).node i).succ ≠ c' := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin (4 * k ^ 2))) ⊆
        Finset.univ.image fun i => ((C u).node i).succ := by
      intro c _; obtain ⟨i, hi⟩ := h c; exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    simp only [Finset.card_univ, Fintype.card_fin] at this
    nlinarith
  let ch3 := ch0.with3 c' (C2 u).color ch0.rb
  have hconf : (C2 u).prevColor = (C2 v).color ∧ (C2 v).prevColor = (C2 u).color ∧
      (C2 u).colorBit ≠ (C2 v).colorBit := by
    rw [prevu, colv, prevv, colu, bitu, bitv]; simp
  refine ⟨upd C2 u v (eulerStep false R ch3 (C2 u) (C2 v)), u,
    ((Relation.ReflTransGen.single st1).tail st2).tail
      (step_of_choice false C2 huv ch3 (EChoice.with3_valid hch0 _ _ _)), ?_⟩
  rw [upd_left _ hne_uv, eulerStep_err]
  · rfl
  · rw [twoHopE_conflict _ _ _ hconf]
    apply (tokenDetect_frame _).2.2
    have hsucc' : ∀ i, ((C2 u).node i).succ = ((C u).node i).succ := by
      intro i
      have := congrFun (congrArg Prod.snd sku) i
      simp only [skel, Prod.mk.injEq] at this
      exact this.2
    have hno : ¬ ∃ i, ((C2 u).node i).succ = c' := by
      rintro ⟨i, hi⟩
      exact hc' i (by rw [← hsucc' i]; exact hi)
    simp only [ch3, EChoice.with3]
    simp [ringPart, FMatch, hno]

/-- **No configuration of the printed SS-EulerCycle is output-stable** (on any graph whose
degrees exceed `k`, e.g. any `2k`-regular graph with `k ≥ 1`), for any ring protocol with a leader
and a non-leader state. In particular the configuration of Lemma 3.1 does not exist. -/
theorem literal_not_outputStable [Fintype V] [DecidableRel G.Adj]
    (hR : ∀ a b, (R.δ a b).Nonempty) (hk : 1 ≤ k) (hdeg : ∀ v, k < G.degree v)
    (hedge : ∃ u v, G.Adj u v)
    {r0 r1 : RS} (hr0 : R.lead r0 = false) (hr1 : R.lead r1 = true) (C : V → EState k RS) :
    ¬ (ssEuler false k R).OutputStable G (EState.out R) C := by
  intro hC
  obtain ⟨D, u, hCD, hu⟩ := literal_error_reachable hR hk hdeg hedge C
  obtain ⟨v, huv⟩ : ∃ v, G.Adj u v := by
    have : 0 < G.degree u := by have := hdeg u; omega
    exact (G.degree_pos_iff_exists_adj u).1 this
  obtain ⟨D1, h1, o1⟩ := output_flexible false hR hk hr0 hr1 D huv hu true
  obtain ⟨D2, h2, o2⟩ := output_flexible false hR hk hr0 hr1 D huv hu false
  have e1 := hC D1 (hCD.tail h1) u
  have e2 := hC D2 (hCD.tail h2) u
  rw [o1] at e1; rw [o2] at e2
  rw [← e1] at e2; exact absurd e2 (by simp)

/-- **Theorem 3.3 fails for the printed protocol**: SS-EulerCycle does not solve SSLE on any graph
with an edge whose degrees all exceed `k` (e.g. any `2k`-regular graph, `k ≥ 1`), for any finite
ring protocol with a leader and a non-leader state: a globally fair execution exists from every
configuration and none ever reaches a valid output-stable configuration. -/
theorem literal_not_solvesSSLE [Fintype V] [DecidableRel G.Adj] [Finite RS]
    (hR : ∀ a b, (R.δ a b).Nonempty) (hk : 1 ≤ k) (hdeg : ∀ v, k < G.degree v)
    (hedge : ∃ u v, G.Adj u v)
    {r0 r1 : RS} (hr0 : R.lead r0 = false) (hr1 : R.lead r1 = true) :
    ¬ (ssEuler false k R).SolvesSSLE G (EState.out R) ∧
      ∀ C : V → EState k RS, ¬ (ssEuler false k R).ValidStable G (EState.out R) C := by
  have := EState.finite (k := k) (RS := RS)
  have hnone : ∀ C : V → EState k RS, ¬ (ssEuler false k R).ValidStable G (EState.out R) C :=
    fun C h => literal_not_outputStable hR hk hdeg hedge hr0 hr1 C h.1
  refine ⟨fun hsol => ?_, hnone⟩
  have := (GProtocol.solvesSSLE_iff hedge (ssEuler_nonempty false R hR) _).1 hsol
  have c0 : Fin (4 * k ^ 2) := ⟨0, by positivity⟩
  obtain ⟨D, hD, -⟩ := this (fun _ => ⟨fun _ => ⟨r0, c0, c0, false, false⟩, c0, c0, false, false⟩)
  exact hnone D hD

end Graph

end SSLERegular
