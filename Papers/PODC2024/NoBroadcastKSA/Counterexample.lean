import Papers.PODC2024.NoBroadcastKSA.Spec

/-!
# Lemma 9 is false

**Lemma 9** of the paper: for all `k > 1` and every content-neutral and compositional broadcast
abstraction `B`, if some algorithm `A` solves k-SA in `CAMP_{k+1}[B]`, then there is `N > 0`
such that `B` admits no `N`-solo execution.

Counterexample (`lemma9_false`). Call a message *chained* (`Chained`) if its sender had already
B-delivered one of its own messages when it invoked `broadcast` for it. The abstraction
`chainedBO k` is *k-Bounded-Order broadcast restricted to chained messages*: among any `k + 1`
distinct chained messages, two are delivered in the same order by all processes (`PQ`). It is
compositional and content-neutral, and it contains every uniform total-order execution
(`totalOrder_mem`), so it is implementable from consensus. The algorithm `algQ`:

* broadcast a dummy message, wait until it returns and is delivered locally;
* broadcast the proposal (this message is chained);
* decide the value of the first value message delivered.

solves k-SA in `CAMP_{k+1}[chainedBO k]` (`algQ_solves`). But for every `N` the abstraction admits
an `N`-solo execution (`soloExec_mem`, `soloExec_nSolo`): every process invokes its `N`
broadcasts before delivering anything, so no message is chained and the ordering property is
void. The paper's proof fails at "`αᵢ` is indistinguishable from `δ`": an `N`-solo execution
fixes only the order of deliveries, not when the invocations happen relative to the
deliveries, so the local pattern of `pᵢ` in `δ` need not be the one of the solo run `αᵢ`.
-/

namespace Podc.NoBroadcastKSA

open BExec

variable {P M : Type}

/-! ## The abstraction `chainedBO k` -/

/-- The message `(q, m)` is *chained*: `q` invoked `broadcast(m)` after B-delivering one of its
own messages. -/
def Chained (E : BExec P M) (q : P) (m : M) : Prop :=
  ∃ t, E.ev t = some (.bc q m) ∧ ∃ t' < t, ∃ m', E.ev t' = some (.dl q q m')

/-- `a` is ordered before `b` for every process: whoever B-delivers `b` has B-delivered `a`
before. -/
def OrderedBefore (E : BExec P M) (a b : P × M) : Prop :=
  ∀ (t : ℕ) (p : P), E.ev t = some (.dl p b.1 b.2) → ∃ t' < t, E.ev t' = some (.dl p a.1 a.2)

/-- k-Bounded-Order on chained messages: among any `k + 1` distinct chained messages, two are
delivered in the same order by all processes. -/
def PQ (k : ℕ) (E : BExec P M) : Prop :=
  ∀ f : Fin (k + 1) → P × M, Function.Injective f → (∀ i, Chained E (f i).1 (f i).2) →
    ∃ i j, i ≠ j ∧ OrderedBefore E (f i) (f j)

/-- The broadcast abstraction "k-Bounded-Order broadcast on chained messages". -/
def chainedBO (k : ℕ) : Set (BExec P M) :=
  {E | E.IsBroadcast ∧ PQ k E}

lemma chainedBO_isBroadcastAbstraction (k : ℕ) :
    IsBroadcastAbstraction (chainedBO k : Set (BExec P M)) :=
  fun _ h => h.1

lemma chainedBO_compositional (k : ℕ) : Compositional (chainedBO k : Set (BExec P M)) := by
  rintro E ⟨hb, hq⟩ X
  refine ⟨hb.restrict X, ?_⟩
  intro f hf hc
  have hc' : ∀ i, Chained E (f i).1 (f i).2 := by
    intro i
    obtain ⟨t, ht, t', ht', m', h'⟩ := hc i
    exact ⟨t, (restrict_ev_eq_some.1 ht).1, t', ht', m', (restrict_ev_eq_some.1 h').1⟩
  obtain ⟨i, j, hij, hord⟩ := hq f hf hc'
  refine ⟨i, j, hij, fun t p h => ?_⟩
  obtain ⟨t', ht', h'⟩ := hord t p (restrict_ev_eq_some.1 h).1
  refine ⟨t', ht', restrict_ev_eq_some.2 ⟨h', ?_⟩⟩
  obtain ⟨s, hs, -⟩ := hc i
  exact (restrict_ev_eq_some.1 hs).2

lemma chainedBO_contentNeutral (k : ℕ) : ContentNeutral (chainedBO k : Set (BExec P M)) := by
  rintro E ⟨hb, hq⟩ r hr
  refine ⟨hb.rename hr, ?_⟩
  intro f hf hc
  -- pull the chained messages back along the renaming
  have hpre : ∀ i, ∃ m', r (f i).1 m' = (f i).2 ∧ Chained E (f i).1 m' := by
    intro i
    obtain ⟨t, ht, t', ht', m'', h'⟩ := hc i
    obtain ⟨m', hm', ht⟩ := rename_ev_bc' ht
    obtain ⟨m3, -, h3⟩ := rename_ev_dl' h'
    exact ⟨m', hm', t, ht, t', ht', m3, h3⟩
  choose g hg hgc using hpre
  have hginj : Function.Injective (fun i => ((f i).1, g i)) := by
    intro i j hij
    simp only [Prod.mk.injEq] at hij
    apply hf
    have h1 := hg i
    have h2 := hg j
    rw [hij.1, hij.2] at h1
    exact Prod.ext hij.1 (h1.symm.trans h2)
  obtain ⟨i, j, hij, hord⟩ := hq _ hginj hgc
  refine ⟨i, j, hij, fun t p h => ?_⟩
  have h' : (E.rename r).ev t = some (.dl p (f j).1 (r (f j).1 (g j))) := by rw [hg j]; exact h
  obtain ⟨t', ht', h''⟩ := hord t p ((rename_ev_dl hr).1 h')
  refine ⟨t', ht', ?_⟩
  have := (rename_ev_dl hr (p := p)).2 h''
  rwa [hg i] at this

/-! ## Non-degeneracy: uniform total order broadcast implements `chainedBO k` -/

/-- Uniform total order: there is an injective rank on messages such that every process that
B-delivers a message has previously B-delivered every broadcast message of smaller rank. -/
def UniformTotalOrder (E : BExec P M) : Prop :=
  ∃ rank : P × M → ℕ, Function.Injective rank ∧
    ∀ (t : ℕ) (p q : P) (m : M), E.ev t = some (.dl p q m) →
      ∀ (q' : P) (m' : M) (t₀ : ℕ), E.ev t₀ = some (.bc q' m') → rank (q', m') < rank (q, m) →
        ∃ t' < t, E.ev t' = some (.dl p q' m')

/-- Every execution of (uniform) total order broadcast is admitted by `chainedBO k`, `k ≥ 1`:
the abstraction is implementable wherever total order broadcast is (e.g. from consensus). -/
theorem totalOrder_mem {k : ℕ} (hk : 1 ≤ k) {E : BExec P M} (hb : E.IsBroadcast)
    (hto : UniformTotalOrder E) : E ∈ chainedBO k := by
  refine ⟨hb, fun f hf hc => ?_⟩
  obtain ⟨rank, hrank, hord⟩ := hto
  let i0 : Fin (k + 1) := ⟨0, by omega⟩
  let i1 : Fin (k + 1) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hne : rank (f i0) ≠ rank (f i1) := fun h => h01 (hf (hrank h))
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨i0, i1, h01, fun t p ht => ?_⟩
    obtain ⟨t₀, h₀, -⟩ := hc i0
    exact hord t p _ _ ht _ _ t₀ h₀ h
  · refine ⟨i1, i0, h01.symm, fun t p ht => ?_⟩
    obtain ⟨t₀, h₀, -⟩ := hc i1
    exact hord t p _ _ ht _ _ t₀ h₀ h

/-! ## The algorithm `algQ` -/

section Alg

variable {P : Type} [DecidableEq P]

/-- Message objects of `algQ`: an identifier and a content, `none` (dummy) or `some v`. -/
abbrev QM := Msg (Option ℕ)

/-- The value carried by a local event, if it is the delivery of a value message. -/
def valOf : LEv P QM ℕ → Option ℕ
  | .dl _ (_, some w) => some w
  | _ => none

/-- Whether a local event is a decision. -/
def isDec : LEv P QM ℕ → Bool
  | .dec _ => true
  | _ => false

/-- Whether a local event is an invocation. -/
def isBc : LEv P QM ℕ → Bool
  | .bc _ => true
  | _ => false

/-- Whether a local event is the invocation of a value message. -/
def isValBc : LEv P QM ℕ → Bool
  | .bc (_, some _) => true
  | _ => false

/-- Whether a local event is the delivery by `p` of one of its own dummy messages. -/
def isOwnDummyDl (p : P) : LEv P QM ℕ → Bool
  | .dl q (_, none) => decide (q = p)
  | _ => false

/-- Every invocation of the history has returned. -/
def noPending (h : List (LEv P QM ℕ)) : Bool :=
  h.all fun e => match e with
    | .bc m => h.contains (.ret m)
    | _ => true

/-- The algorithm: broadcast a dummy message; once it has returned and been delivered locally,
broadcast the proposal; decide the value of the first value message delivered. -/
def algQ : Algo P (Option ℕ) ℕ where
  act p v h :=
    if h.any isDec then none
    else match h.findSome? valOf with
      | some w => some (.decide w)
      | none =>
        if h.any isBc = false then some (.bcast none)
        else if noPending h ∧ h.any (isOwnDummyDl p) ∧ h.any isValBc = false then
          some (.bcast (some v))
        else none

lemma algQ_act_bcast {p : P} {v : ℕ} {h : List (LEv P QM ℕ)} {c : Option ℕ}
    (hact : algQ.act p v h = some (.bcast c)) :
    (c = none ∧ h.any isBc = false) ∨
      (c = some v ∧ noPending h = true ∧ h.any (isOwnDummyDl p) = true) := by
  simp only [algQ] at hact
  by_cases h1 : h.any isDec = true
  · simp only [h1, ite_true] at hact; cases hact
  · simp only [h1, Bool.false_eq_true, ite_false] at hact
    cases hfs : h.findSome? valOf with
    | some w => rw [hfs] at hact; cases hact
    | none =>
      rw [hfs] at hact
      simp only at hact
      split_ifs at hact with h4 h5 <;> cases hact
      · exact Or.inl ⟨rfl, by simpa using h4⟩
      · exact Or.inr ⟨rfl, h5.1, h5.2.1⟩

lemma algQ_act_decide {p : P} {v w : ℕ} {h : List (LEv P QM ℕ)}
    (hact : algQ.act p v h = some (.decide w)) : h.findSome? valOf = some w := by
  simp only [algQ] at hact
  by_cases h1 : h.any isDec = true
  · simp only [h1, ite_true] at hact; cases hact
  · simp only [h1, Bool.false_eq_true, ite_false] at hact
    cases hfs : h.findSome? valOf with
    | some w' => rw [hfs] at hact; cases hact; rfl
    | none =>
      rw [hfs] at hact
      simp only at hact
      split_ifs at hact <;> cases hact

/-- If the history has no decision and contains a value delivery, the algorithm decides. -/
lemma algQ_act_of_val {p : P} {v : ℕ} {h : List (LEv P QM ℕ)} {w : ℕ}
    (hd : h.any isDec = false) (hw : h.findSome? valOf = some w) :
    algQ.act p v h = some (.decide w) := by
  simp only [algQ, hd, hw, Bool.false_eq_true, ite_false]

lemma algQ_act_dummy {p : P} {v : ℕ} {h : List (LEv P QM ℕ)}
    (hd : h.any isDec = false) (hw : h.findSome? valOf = none) (hb : h.any isBc = false) :
    algQ.act p v h = some (.bcast none) := by
  simp only [algQ, hd, hw, Bool.false_eq_true, ite_false, hb, ite_true]

lemma algQ_act_val {p : P} {v : ℕ} {h : List (LEv P QM ℕ)}
    (hd : h.any isDec = false) (hw : h.findSome? valOf = none) (hb : h.any isBc = true)
    (hn : noPending h = true) (hl : h.any (isOwnDummyDl p) = true)
    (hv : h.any isValBc = false) :
    algQ.act p v h = some (.bcast (some v)) := by
  simp only [algQ, hd, hw, hb, hn, hl, hv, Bool.false_eq_true, ite_false, Bool.true_eq_false]
  simp

/-- `algQ` is well-formed: it never invokes `broadcast` while an invocation is pending. -/
theorem algQ_wellFormed : (algQ : Algo P (Option ℕ) ℕ).WellFormed := by
  intro p v h c hact m hm
  rcases algQ_act_bcast hact with ⟨-, hb⟩ | ⟨-, hn, -⟩
  · rw [List.any_eq_false] at hb
    exact absurd rfl (hb _ hm)
  · have := List.all_eq_true.1 hn _ hm
    simpa using this

end Alg

/-! ## `algQ` solves k-set agreement on top of `chainedBO k` -/

section Solves

variable {P : Type} [DecidableEq P] {k : ℕ}

open AExec

lemma aStep_bc {p : P} {m : QM} :
    (Step.b (.bc p m) : Step P QM ℕ).aStep p = some (some (.bcast m)) := by
  simp [Step.aStep]

lemma bc_act {E : AExec P QM ℕ} {S : Set (BExec P QM)}
    (hE : Admissible algQ S E) {t : ℕ} {p : P} {m : QM}
    (h : E.st t = some (.b (.bc p m))) :
    algQ.act p (E.inp p) (E.hist p t) = some (.bcast m.2) :=
  hE.consistent t p _ _ h aStep_bc

lemma dec_act {E : AExec P QM ℕ} {S : Set (BExec P QM)}
    (hE : Admissible algQ S E) {t : ℕ} {p : P} {v : ℕ}
    (h : E.st t = some (.dec p v)) :
    algQ.act p (E.inp p) (E.hist p t) = some (.decide v) :=
  hE.consistent t p _ (some (.decide v)) h (by simp [Step.aStep])

lemma loc_dl {s : Step P QM ℕ} {p q : P} {m : QM}
    (h : s.loc p = some (.dl q m)) : s = .b (.dl p q m) := by
  rcases loc_eq_some h with ⟨_, he, _⟩ | ⟨_, he, _⟩ | ⟨q', m', he, hs⟩ | ⟨_, he, _⟩ <;>
    cases he
  exact hs

lemma loc_bc {s : Step P QM ℕ} {p : P} {m : QM}
    (h : s.loc p = some (.bc m)) : s = .b (.bc p m) := by
  rcases loc_eq_some h with ⟨_, he, hs⟩ | ⟨_, he, _⟩ | ⟨_, _, he, _⟩ | ⟨_, he, _⟩ <;>
    cases he
  exact hs

lemma loc_ret {s : Step P QM ℕ} {p : P} {m : QM}
    (h : s.loc p = some (.ret m)) : s = .b (.ret p m) := by
  rcases loc_eq_some h with ⟨_, he, _⟩ | ⟨_, he, hs⟩ | ⟨_, _, he, _⟩ | ⟨_, he, _⟩ <;>
    cases he
  exact hs

lemma bind_loc_eq {E : AExec P QM ℕ} {s : ℕ} {p : P} {e : LEv P QM ℕ}
    (h : (E.st s).bind (Step.loc p) = some e) : ∃ st, E.st s = some st ∧ st.loc p = some e := by
  simpa [Option.bind_eq_some_iff] using h

lemma mem_hist_dl {E : AExec P QM ℕ} {p q : P} {t : ℕ} {m : QM}
    (h : LEv.dl q m ∈ E.hist p t) : ∃ s < t, E.st s = some (.b (.dl p q m)) := by
  obtain ⟨s, hs, h⟩ := mem_hist.1 h
  obtain ⟨st, h1, h2⟩ := bind_loc_eq h
  exact ⟨s, hs, by rw [h1, loc_dl h2]⟩

lemma mem_hist_bc {E : AExec P QM ℕ} {p : P} {t : ℕ} {m : QM}
    (h : LEv.bc m ∈ E.hist p t) : ∃ s < t, E.st s = some (.b (.bc p m)) := by
  obtain ⟨s, hs, h⟩ := mem_hist.1 h
  obtain ⟨st, h1, h2⟩ := bind_loc_eq h
  exact ⟨s, hs, by rw [h1, loc_bc h2]⟩

lemma mem_hist_of {E : AExec P QM ℕ} {p : P} {t s : ℕ} {st : Step P QM ℕ}
    {e : LEv P QM ℕ} (hs : s < t) (h : E.st s = some st) (he : st.loc p = some e) :
    e ∈ E.hist p t :=
  mem_hist.2 ⟨s, hs, by simp [h, he]⟩

/-- The value of a value message is the proposal of its sender, who had delivered one of its
own dummy messages before. -/
lemma val_bc {E : AExec P QM ℕ} {S : Set (BExec P QM)}
    (hE : Admissible algQ S E) {t : ℕ} {q : P} {i w : ℕ}
    (h : E.st t = some (.b (.bc q (i, some w)))) :
    w = E.inp q ∧ ∃ s < t, ∃ j, E.st s = some (.b (.dl q q (j, none))) := by
  rcases algQ_act_bcast (bc_act hE h) with ⟨h1, -⟩ | ⟨h1, -, h2⟩
  · cases h1
  · cases h1
    refine ⟨rfl, ?_⟩
    obtain ⟨e, he, hev⟩ := List.any_eq_true.1 h2
    rcases e with _ | _ | ⟨q', j, _ | _⟩ | _ <;> simp [isOwnDummyDl] at hev
    subst hev
    obtain ⟨s, hs, h3⟩ := mem_hist_dl he
    exact ⟨s, hs, j, h3⟩

/-- A dummy message is the first invocation of its sender. -/
lemma dummy_first {E : AExec P QM ℕ} {S : Set (BExec P QM)}
    (hE : Admissible algQ S E) {t : ℕ} {p : P} {i : ℕ}
    (h : E.st t = some (.b (.bc p (i, none)))) :
    ∀ s < t, ∀ m, E.st s ≠ some (.b (.bc p m)) := by
  intro s hs m h'
  rcases algQ_act_bcast (bc_act hE h) with ⟨-, hb⟩ | ⟨h1, -⟩
  · rw [List.any_eq_false] at hb
    exact hb _ (mem_hist_of (e := LEv.bc m) hs h' (by simp [Step.loc])) rfl
  · cases h1

theorem algQ_validity {E : AExec P QM ℕ} (hE : Admissible algQ (chainedBO k) E)
    (t : ℕ) (p : P) (v : ℕ) (h : E.st t = some (.dec p v)) :
    ∃ q, E.inp q = v ∧ E.Participates q := by
  have hw := algQ_act_decide (dec_act hE h)
  obtain ⟨s, -, e, he, hg, -⟩ := findSome?_hist hw
  obtain ⟨st, hst, hloc⟩ := bind_loc_eq he
  rcases e with _ | _ | ⟨q, i, _ | w⟩ | _ <;> simp [valOf] at hg
  subst w
  have hdl := loc_dl hloc
  subst hdl
  obtain ⟨t', -, hbc⟩ := hE.spec.1.validity s p q (i, some v) (proj_ev_eq_some.2 hst)
  have hbc := proj_ev_eq_some.1 hbc
  obtain ⟨hv, -⟩ := val_bc hE hbc
  exact ⟨q, hv.symm, t', _, _, hbc, aStep_bc⟩

/-- The first value message delivered by a decider. -/
lemma first_val {E : AExec P QM ℕ} (hE : Admissible algQ (chainedBO k) E) {t : ℕ}
    {p : P} {v : ℕ} (h : E.st t = some (.dec p v)) :
    ∃ s q i, E.st s = some (.b (.dl p q (i, some v))) ∧
      ∀ s' < s, ∀ q' i' w', E.st s' ≠ some (.b (.dl p q' (i', some w'))) := by
  have hw := algQ_act_decide (dec_act hE h)
  obtain ⟨s, -, e, he, hg, hfirst⟩ := findSome?_hist hw
  obtain ⟨st, hst, hloc⟩ := bind_loc_eq he
  rcases e with _ | _ | ⟨q, i, _ | w⟩ | _ <;> simp [valOf] at hg
  subst w
  refine ⟨s, q, i, by rw [hst, loc_dl hloc], fun s' hs' q' i' w' h' => ?_⟩
  have := hfirst s' hs' (.dl q' (i', some w')) (by simp [h', Step.loc])
  simp [valOf] at this

theorem algQ_agreement {E : AExec P QM ℕ} (hE : Admissible algQ (chainedBO k) E)
    (f : Fin (k + 1) → ℕ) (hf : Function.Injective f) : ¬ ∀ i, E.Decided (f i) := by
  intro hdec
  have hfv : ∀ i, ∃ d s q j, E.st s = some (.b (.dl d q (j, some (f i)))) ∧
      ∀ s' < s, ∀ q' i' w', E.st s' ≠ some (.b (.dl d q' (i', some w'))) := by
    intro i
    obtain ⟨t, d, h⟩ := hdec i
    obtain ⟨s, q, j, h1, h2⟩ := first_val hE h
    exact ⟨d, s, q, j, h1, h2⟩
  choose d s q j hdl hfirst using hfv
  let g : Fin (k + 1) → P × QM := fun i => (q i, (j i, some (f i)))
  have hg : Function.Injective g := by
    intro i i' hii
    simp only [g, Prod.mk.injEq, Option.some.injEq] at hii
    exact hf hii.2.2
  have hc : ∀ i, Chained E.proj (g i).1 (g i).2 := by
    intro i
    obtain ⟨t', -, hbc⟩ := hE.spec.1.validity _ _ _ _ (proj_ev_eq_some.2 (hdl i))
    have hbc' := proj_ev_eq_some.1 hbc
    obtain ⟨-, s', hs', j', h'⟩ := val_bc hE hbc'
    exact ⟨t', hbc, s', hs', _, proj_ev_eq_some.2 h'⟩
  obtain ⟨i, i', -, hord⟩ := hE.spec.2 g hg hc
  obtain ⟨t', ht', h'⟩ := hord (s i') (d i') (proj_ev_eq_some.2 (hdl i'))
  exact hfirst i' t' ht' _ _ _ (proj_ev_eq_some.1 h')

lemma any_isDec_eq_false {E : AExec P QM ℕ} {p : P} {t : ℕ}
    (h : ∀ s v, E.st s ≠ some (.dec p v)) : (E.hist p t).any isDec = false := by
  rw [List.any_eq_false]
  intro e he
  obtain ⟨s, -, h1⟩ := mem_hist.1 he
  obtain ⟨st, h2, h3⟩ := bind_loc_eq h1
  rcases loc_eq_some h3 with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨v, rfl, hs⟩ <;>
    simp [isDec]
  subst hs; exact h s v h2

theorem algQ_termination {E : AExec P QM ℕ} (hE : Admissible algQ (chainedBO k) E)
    (p : P) (hp : p ∈ E.correct) : ∃ t v, E.st t = some (.dec p v) := by
  by_contra hnd
  push Not at hnd
  have hnodec : ∀ t, (E.hist p t).any isDec = false := fun t => any_isDec_eq_false hnd
  have hb := hE.spec.1
  -- at every step of the algorithm, no value message has been delivered yet
  have hnoval : ∀ t s o, E.st t = some s → s.aStep p = some o →
      (E.hist p t).findSome? valOf = none := by
    intro t s o hs ho
    cases hw : (E.hist p t).findSome? valOf with
    | none => rfl
    | some w =>
      have hact := hE.consistent t p s o hs ho
      rw [algQ_act_of_val (hnodec t) hw] at hact
      rcases aStep_eq_some ho with ⟨m, rfl, -⟩ | ⟨v, rfl, rfl⟩ | ⟨rfl, -⟩
      · cases hact
      · exact absurd hs (hnd t v)
      · cases hact
  -- some message is broadcast
  have hsome : ∃ t m, E.st t = some (.b (.bc p m)) := by
    obtain ⟨t, -, s, o, hs, ho⟩ := hE.fair p hp 0
    cases hbm : (E.hist p t).any isBc with
    | true =>
      obtain ⟨e, he, hev⟩ := List.any_eq_true.1 hbm
      rcases e with m | _ | _ | _ <;> simp [isBc] at hev
      obtain ⟨s', -, h'⟩ := mem_hist_bc he
      exact ⟨s', m, h'⟩
    | false =>
      have hact := hE.consistent t p s o hs ho
      rw [algQ_act_dummy (hnodec t) (hnoval t s o hs ho) hbm] at hact
      rcases aStep_eq_some ho with ⟨m, rfl, rfl⟩ | ⟨v, rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨t, m, hs⟩
      · cases hact
      · cases hact
  -- a value message is broadcast
  have hval : ∃ t i w, E.st t = some (.b (.bc p (i, some w))) := by
    obtain ⟨t0, ⟨i0, c0⟩, h0⟩ := hsome
    rcases c0 with _ | w
    swap
    · exact ⟨t0, i0, w, h0⟩
    obtain ⟨t1, -, h1⟩ := hb.localTerm t0 p _ hp (proj_ev_eq_some.2 h0)
    obtain ⟨t2, h2⟩ := hb.globalCS t0 p _ hp (proj_ev_eq_some.2 h0) p hp
    have h1 := proj_ev_eq_some.1 h1
    have h2 := proj_ev_eq_some.1 h2
    obtain ⟨t, ht, s, o, hs, ho⟩ := hE.fair p hp (t0 + t1 + t2 + 1)
    cases hv : (E.hist p t).any isValBc with
    | true =>
      obtain ⟨e, he, hev⟩ := List.any_eq_true.1 hv
      rcases e with ⟨i, _ | w⟩ | _ | _ | _ <;> simp [isValBc] at hev
      obtain ⟨s', -, h'⟩ := mem_hist_bc he
      exact ⟨s', i, w, h'⟩
    | false =>
      -- the only invocation in the history is the dummy one, which has returned
      have hn : noPending (E.hist p t) = true := by
        rw [noPending, List.all_eq_true]
        intro e he
        rcases e with ⟨i, _ | w⟩ | _ | _ | _
        · obtain ⟨s', hs', h'⟩ := mem_hist_bc he
          have hss : s' = t0 := by
            rcases lt_trichotomy s' t0 with hlt | heq | hlt
            · exact absurd h' (dummy_first hE h0 s' hlt _)
            · exact heq
            · exact absurd h0 (dummy_first hE h' t0 hlt _)
          subst hss
          rw [h0] at h'
          cases h'
          simpa using mem_hist_of (e := LEv.ret (i0, none)) (by omega) h1 (by simp [Step.loc])
        · exact absurd (List.any_eq_false.1 hv _ he) (by simp [isValBc])
        all_goals simp
      have hact := hE.consistent t p s o hs ho
      rw [algQ_act_val (hnodec t) (hnoval t s o hs ho)
        (List.any_eq_true.2 ⟨_, mem_hist_of (e := LEv.bc (i0, none)) (by omega) h0
          (by simp [Step.loc]), rfl⟩) hn
        (List.any_eq_true.2 ⟨_, mem_hist_of (e := LEv.dl p (i0, none)) (by omega) h2
          (by simp [Step.loc]),
          by simp [isOwnDummyDl]⟩) hv] at hact
      rcases aStep_eq_some ho with ⟨⟨i, c⟩, rfl, rfl⟩ | ⟨v, rfl, -⟩ | ⟨rfl, -⟩
      · simp only [Option.map_some, AAct.cont, Option.some.injEq, AAct.bcast.injEq] at hact
        subst hact
        exact ⟨t, i, _, hs⟩
      · cases hact
      · cases hact
  obtain ⟨t3, i, w, h3⟩ := hval
  obtain ⟨t4, h4⟩ := hb.globalCS t3 p _ hp (proj_ev_eq_some.2 h3) p hp
  have h4 := proj_ev_eq_some.1 h4
  obtain ⟨t, ht, s, o, hs, ho⟩ := hE.fair p hp (t4 + 1)
  have := hnoval t s o hs ho
  rw [List.findSome?_eq_none_iff] at this
  have := this _ (mem_hist_of (e := LEv.dl p (i, some w)) (by omega) h4 (by simp [Step.loc]))
  simp [valOf] at this

/-- `algQ` solves k-set agreement on top of `chainedBO k`. -/
theorem algQ_solves : SolvesKSA k (algQ : Algo P (Option ℕ) ℕ) (chainedBO k) :=
  fun _ hE => ⟨algQ_validity hE, algQ_agreement hE, algQ_termination hE⟩

end Solves

/-! ## `N`-solo executions of `chainedBO k` -/

section Solo

variable (n N : ℕ)

/-- The time of each event of the `N`-solo execution: first every process (in turn) invokes and
returns from its `N` broadcasts, then every process delivers its own `N` messages, then every
process delivers the messages of the others. -/
def soloTime : BEv (Fin n) QM → ℕ
  | .bc p (j, none) => 2 * (N * p + j)
  | .ret p (j, none) => 2 * (N * p + j) + 1
  | .dl p q (j, none) => if p = q then 2 * (n * N) + (N * p + j)
      else 3 * (n * N) + ((n * N) * p + (N * q + j))
  | _ => 0

/-- The events of the `N`-solo execution. -/
def SoloEv : BEv (Fin n) QM → Prop
  | .bc _ (j, none) => j < N
  | .ret _ (j, none) => j < N
  | .dl _ _ (j, none) => j < N
  | _ => False

open Classical in
/-- The `N`-solo execution (all processes correct, every message delivered to everybody). -/
noncomputable def soloExec : BExec (Fin n) QM where
  ev t := if h : ∃ e, SoloEv n N e ∧ soloTime n N e = t then some (Classical.choose h) else none
  correct := Set.univ

variable {n N}

lemma mul_add_lt {p j : ℕ} (hp : p < n) (hj : j < N) : N * p + j < n * N := by
  have : N * p + N ≤ N * n := by nlinarith
  rw [mul_comm n N]; omega

lemma mul_add_inj {B a b a' b' : ℕ} (hb : b < B) (hb' : b' < B) (h : B * a + b = B * a' + b') :
    a = a' ∧ b = b' := by
  have hB : 0 < B := by omega
  have h1 : (B * a + b) / B = a := by
    rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hb, add_zero]
  have h2 : (B * a' + b') / B = a' := by
    rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hb', add_zero]
  have ha : a = a' := by rw [← h1, ← h2, h]
  subst ha
  exact ⟨rfl, by omega⟩

lemma soloTime_inj {e e' : BEv (Fin n) QM} (he : SoloEv n N e) (he' : SoloEv n N e')
    (h : soloTime n N e = soloTime n N e') : e = e' := by
  rcases e with ⟨p, j, _ | c⟩ | ⟨p, j, _ | c⟩ | ⟨p, q, j, _ | c⟩ <;> simp only [SoloEv] at he <;>
  rcases e' with ⟨p', j', _ | c'⟩ | ⟨p', j', _ | c'⟩ | ⟨p', q', j', _ | c'⟩ <;>
    simp only [SoloEv] at he' <;>
  simp only [soloTime] at h
  all_goals
    have hp := mul_add_lt (N := N) p.isLt he
    have hp' := mul_add_lt (N := N) p'.isLt he'
  all_goals try split_ifs at h
  all_goals first
    | omega
    | skip
  · obtain ⟨hpp, rfl⟩ := mul_add_inj he he' (by omega : N * (p : ℕ) + j = N * p' + j')
    rw [Fin.ext hpp]
  · obtain ⟨hpp, rfl⟩ := mul_add_inj he he' (by omega : N * (p : ℕ) + j = N * p' + j')
    rw [Fin.ext hpp]
  · rename_i h1 h2; subst h1 h2
    obtain ⟨hpp, rfl⟩ := mul_add_inj he he' (by omega : N * (p : ℕ) + j = N * p' + j')
    rw [Fin.ext hpp]
  · have hq := mul_add_lt (N := N) q.isLt he
    have hq' := mul_add_lt (N := N) q'.isLt he'
    obtain ⟨hpp, h3⟩ := mul_add_inj hq hq' (by omega :
      (n * N) * (p : ℕ) + (N * q + j) = (n * N) * p' + (N * q' + j'))
    obtain ⟨hqq, rfl⟩ := mul_add_inj he he' h3
    rw [Fin.ext hpp, Fin.ext hqq]

lemma soloExec_ev {t : ℕ} {e : BEv (Fin n) QM} :
    (soloExec n N).ev t = some e ↔ SoloEv n N e ∧ soloTime n N e = t := by
  simp only [soloExec]
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · rintro ⟨⟩; exact hc
    · rintro ⟨he, ht⟩
      congr 1; exact soloTime_inj hc.1 he (hc.2.trans ht.symm)
  · simp only [false_iff]; rintro ⟨he, ht⟩; exact h ⟨e, he, ht⟩

lemma soloExec_ev_of {e : BEv (Fin n) QM} (he : SoloEv n N e) :
    (soloExec n N).ev (soloTime n N e) = some e :=
  soloExec_ev.2 ⟨he, rfl⟩

lemma soloExec_some {t : ℕ} {e : BEv (Fin n) QM} (h : (soloExec n N).ev t = some e) :
    ∃ j, j < N ∧ e.msg.2 = (j, none) := by
  obtain ⟨he, -⟩ := soloExec_ev.1 h
  rcases e with ⟨p, j, _ | c⟩ | ⟨p, j, _ | c⟩ | ⟨p, q, j, _ | c⟩ <;> simp only [SoloEv] at he <;>
    exact ⟨j, he, rfl⟩

lemma soloExec_isBroadcast : (soloExec n N).IsBroadcast := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro t p q m h
    obtain ⟨j, hj, rfl⟩ := soloExec_some h
    obtain ⟨-, rfl⟩ := soloExec_ev.1 h
    refine ⟨soloTime n N (.bc q (j, none)), ?_, soloExec_ev_of (by exact hj)⟩
    have := mul_add_lt (N := N) q.isLt hj
    have := mul_add_lt (N := N) p.isLt hj
    simp only [soloTime]; split_ifs <;> omega
  · intro t t' p q m h h'
    exact (soloExec_ev.1 h).2.symm.trans (soloExec_ev.1 h').2
  · intro t t' p m h h'
    exact (soloExec_ev.1 h).2.symm.trans (soloExec_ev.1 h').2
  · intro t p m h
    obtain ⟨j, hj, rfl⟩ := soloExec_some h
    obtain ⟨-, rfl⟩ := soloExec_ev.1 h
    exact ⟨soloTime n N (.bc p (j, none)), by simp only [soloTime]; omega,
      soloExec_ev_of (by exact hj)⟩
  · intro t t' p m h h'
    exact (soloExec_ev.1 h).2.symm.trans (soloExec_ev.1 h').2
  · intro t t' p m m' htt h h'
    obtain ⟨j, hj, rfl⟩ := soloExec_some h
    obtain ⟨j', hj', rfl⟩ := soloExec_some h'
    obtain ⟨-, rfl⟩ := soloExec_ev.1 h
    obtain ⟨-, rfl⟩ := soloExec_ev.1 h'
    simp only [soloTime] at htt ⊢
    exact ⟨soloTime n N (.ret p (j', none)), by simp only [soloTime]; omega,
      by simp only [soloTime]; omega, soloExec_ev_of (by exact hj')⟩
  · intro t p m _ h
    obtain ⟨j, hj, rfl⟩ := soloExec_some h
    obtain ⟨-, rfl⟩ := soloExec_ev.1 h
    exact ⟨soloTime n N (.ret p (j, none)), by simp only [soloTime]; omega,
      soloExec_ev_of (by exact hj)⟩
  · intro t q m _ h p _
    obtain ⟨j, hj, rfl⟩ := soloExec_some h
    exact ⟨_, soloExec_ev_of (e := .dl p q (j, none)) (by exact hj)⟩

/-- No message of the solo execution is chained. -/
lemma soloExec_not_chained (q : Fin n) (m : QM) : ¬ Chained (soloExec n N) q m := by
  rintro ⟨t, h, t', ht', m', h'⟩
  obtain ⟨j, hj, rfl⟩ := soloExec_some h
  obtain ⟨j', hj', rfl⟩ := soloExec_some h'
  obtain ⟨-, rfl⟩ := soloExec_ev.1 h
  obtain ⟨-, rfl⟩ := soloExec_ev.1 h'
  have := mul_add_lt (N := N) q.isLt hj
  simp only [soloTime, ite_true] at ht'
  omega

/-- For every `N`, the solo execution is admitted by `chainedBO k`. -/
theorem soloExec_mem (k N : ℕ) : soloExec (k + 1) N ∈ chainedBO k :=
  ⟨soloExec_isBroadcast, fun _ _ hc => absurd (hc 0) (soloExec_not_chained _ _)⟩

/-- The solo execution is `N`-solo (Definition 5). -/
theorem soloExec_nSolo : (soloExec n N).NSolo N := by
  refine ⟨fun _ j => (j.val, none), fun _ _ _ h => Fin.ext (Prod.mk.inj h).1,
    fun p j => ⟨_, soloExec_ev_of (e := .bc p (j.val, none)) (by exact j.isLt)⟩, ?_⟩
  intro p q hpq j' t h j
  obtain ⟨-, rfl⟩ := soloExec_ev.1 h
  refine ⟨soloTime n N (.dl p p (j.val, none)), ?_, soloExec_ev_of (by exact j.isLt)⟩
  have := mul_add_lt (N := N) p.isLt j.isLt
  simp only [soloTime, ite_true, hpq, ite_false]
  omega

end Solo

/-! ## Lemma 9 is false -/

/-- The statement of **Lemma 9** (for `n = k + 1` processes, as in the paper). -/
def Lemma9 (k : ℕ) : Prop :=
  ∀ (C V : Type) (S : Set (BExec (Fin (k + 1)) (Msg C))) (A : Algo (Fin (k + 1)) C V),
    IsBroadcastAbstraction S → Compositional S → ContentNeutral S → SolvesKSA k A S →
      ∃ N > 0, ∀ E ∈ S, ¬ E.NSolo N

/-- **Lemma 9 is false** (for every `k`, in particular every `k > 1`): `chainedBO k` is a
content-neutral and compositional broadcast abstraction on top of which `algQ` solves k-set
agreement with `k + 1` processes, yet it admits an `N`-solo execution for every `N`. -/
theorem lemma9_false (k : ℕ) : ¬ Lemma9 k := by
  intro h
  obtain ⟨N, -, hN⟩ := h (Option ℕ) ℕ (chainedBO k) algQ (chainedBO_isBroadcastAbstraction k)
    (chainedBO_compositional k) (chainedBO_contentNeutral k) algQ_solves
  exact hN _ (soloExec_mem k N) soloExec_nSolo

/-! ## Non-vacuity: an admissible execution of `algQ` on top of `chainedBO k` -/

section NonVacuous

variable {k : ℕ}

/-- Process `0` runs `algQ` alone (the other processes crash initially): it broadcasts the
dummy message, receives it back, broadcasts its proposal `7`, delivers it and decides `7`. -/
def soloRunSt : ℕ → Option (Step (Fin (k + 1)) QM ℕ)
  | 0 => some (.b (.bc 0 (0, none)))
  | 1 => some (.b (.ret 0 (0, none)))
  | 2 => some (.b (.dl 0 0 (0, none)))
  | 3 => some (.b (.bc 0 (1, some 7)))
  | 4 => some (.b (.ret 0 (1, some 7)))
  | 5 => some (.b (.dl 0 0 (1, some 7)))
  | 6 => some (.dec 0 7)
  | _ + 7 => some (.tick 0)

/-- The solo run of `algQ`: only process `0` is correct. -/
def soloRun : AExec (Fin (k + 1)) QM ℕ where
  st := soloRunSt
  correct := {0}
  inp := fun _ => 7

lemma soloRun_proj {t : ℕ} {e : BEv (Fin (k + 1)) QM} :
    (soloRun (k := k)).proj.ev t = some e ↔
      (t = 0 ∧ e = .bc 0 (0, none)) ∨ (t = 1 ∧ e = .ret 0 (0, none)) ∨ (t = 2 ∧ e = .dl 0 0 (0, none)) ∨
      (t = 3 ∧ e = .bc 0 (1, some 7)) ∨ (t = 4 ∧ e = .ret 0 (1, some 7)) ∨
      (t = 5 ∧ e = .dl 0 0 (1, some 7)) := by
  rw [AExec.proj_ev_eq_some]
  rcases t with _ | _ | _ | _ | _ | _ | _ | t <;>
    simp [soloRun, soloRunSt, eq_comm]

lemma soloRun_isBroadcast : (soloRun (k := k)).proj.IsBroadcast := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp only [BExec.Validity, BExec.NoDuplication,
    BExec.UniqueBc, BExec.LocalTermination, BExec.GlobalCSTermination, soloRun_proj] <;>
    simp only [reduceCtorEq, BEv.bc.injEq, BEv.ret.injEq, BEv.dl.injEq, and_false,
      or_false, false_or]
  · rintro t p q m (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨3, by omega, by simp⟩
  · rintro t t' p q m (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> simp <;> omega
  · rintro t t' p m (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> simp <;> omega
  · rintro t p m (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨3, by omega, by simp⟩
  · rintro t t' p m (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> simp <;> omega
  · rintro t t' p m m' htt (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) (⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩) <;>
      try omega
    exact ⟨1, by omega, by omega, by simp⟩
  · rintro t p m - (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact ⟨1, by omega, by simp⟩
    · exact ⟨4, by omega, by simp⟩
  · rintro t q m hq (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) p hp <;>
      simp only [soloRun] at hp <;> subst hp
    · exact ⟨2, by simp⟩
    · exact ⟨5, by simp⟩

lemma soloRun_mem (hk : 1 ≤ k) : (soloRun (k := k)).proj ∈ chainedBO k := by
  refine ⟨soloRun_isBroadcast, fun f hf hc => ?_⟩
  -- the only chained message is `(0, some 7)`
  have hch : ∀ i, f i = (0, (1, some 7)) := by
    intro i
    obtain ⟨t, ht, t', ht', m', h'⟩ := hc i
    rw [soloRun_proj] at ht h'
    simp only [reduceCtorEq, BEv.bc.injEq, BEv.dl.injEq, and_false, or_false,
      false_or] at ht h'
    rcases ht with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;> rcases h' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      try omega
    exact Prod.ext h1 h2
  have : (⟨0, by omega⟩ : Fin (k + 1)) = ⟨1, by omega⟩ := hf ((hch _).trans (hch _).symm)
  simp [Fin.ext_iff] at this

lemma soloRun_hist_late (t : ℕ) :
    LEv.dec 7 ∈ (soloRun (k := k)).hist 0 (t + 7) :=
  AExec.mem_hist.2 ⟨6, by omega, by simp [soloRun, soloRunSt, Step.loc]⟩

/-- `algQ` has admissible executions on top of `chainedBO k` (`k ≥ 1`): `SolvesKSA` is not
vacuous. -/
theorem soloRun_admissible (hk : 1 ≤ k) : Admissible algQ (chainedBO k) (soloRun (k := k)) := by
  refine ⟨soloRun_mem hk, ?_, ?_, ?_⟩
  · intro t p s o hs ho
    rcases AExec.aStep_eq_some ho with ⟨m, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases t with _ | _ | _ | _ | _ | _ | _ | t <;> simp [soloRun, soloRunSt] at hs
      · obtain ⟨rfl, rfl⟩ := hs; rfl
      · obtain ⟨rfl, rfl⟩ := hs
        simp [algQ, AExec.hist, soloRun, soloRunSt, Step.loc, isDec, valOf, isValBc, isBc, noPending,
          isOwnDummyDl, AAct.cont, List.findSome?_cons]
    · rcases t with _ | _ | _ | _ | _ | _ | _ | t <;> simp [soloRun, soloRunSt] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp [algQ, AExec.hist, soloRun, soloRunSt, Step.loc, isDec, valOf, isValBc, isBc, noPending,
          isOwnDummyDl, AAct.cont, List.findSome?_cons]
    · rcases t with _ | _ | _ | _ | _ | _ | _ | t <;> simp [soloRun, soloRunSt] at hs
      subst hs
      have h := soloRun_hist_late (k := k) t
      have hany : ((soloRun (k := k)).hist 0 (t + 7)).any isDec = true :=
        List.any_eq_true.2 ⟨_, h, rfl⟩
      show algQ.act 0 7 ((soloRun (k := k)).hist 0 (t + 7)) = none
      simp only [algQ, hany, ite_true]
  · intro p hp t
    simp only [soloRun] at hp
    subst hp
    exact ⟨t + 7, by omega, _, (none : Option (AAct QM ℕ)), rfl, by simp [Step.aStep]⟩
  · intro p hp
    refine ⟨0, fun t _ s hs => ?_⟩
    have hp0 : (0 : Fin (k + 1)) ≠ p := fun h => hp (by simp [soloRun, h])
    rcases t with _ | _ | _ | _ | _ | _ | _ | t <;> simp [soloRun, soloRunSt] at hs <;> subst hs <;>
      simp [Step.aStep, Step.loc, hp0]

end NonVacuous

end Podc.NoBroadcastKSA
