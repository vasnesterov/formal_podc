import Papers.PODC2022.BindingCrusaderAgreement.EchoLayer

/-!
# Algorithm 4: Binding Crusader Agreement with Byzantine faults (`BCA_Byz`)

Abraham, Ben-David, Yandamuri, PODC 2022, Section 4.2, Algorithm 4, Theorem 4.3 and
Lemmas 4.4–4.9.

The protocol (`n ≥ 3t + 1`, asynchronous, adaptive Byzantine adversary), after the echo layer
(`EchoLayer.lean`):
* lines 8–12: once `|approvedVals| > 1`, or `⟨echo2, v⟩` was received from `n − t` parties,
  send `⟨echo3, ⊥⟩` resp. `⟨echo3, v⟩` (only one `echo3`);
* lines 13–17: once `|approvedVals| > 1` and `n − t` `echo3` messages were received, decide
  `⊥`; once `⟨echo3, v⟩` was received from `n − t` parties, decide `v` (after the own `echo3`).

Guards are liberal (see `Cslib.Byzantine.AsyncBroadcast`): when both conditions of a "wait until"
hold, either branch may be taken. This only adds behaviours, so the safety results apply to the
paper's deterministic precedence as well.

## Main results
* `agreement` (Lemma 4.4) — for *all* recorded decisions, including those of parties corrupted
  after deciding;
* `validity` (Lemma 4.5);
* `echo3_consistent` (Lemma 4.8);
* `binding` (Lemma 4.9, Definition 3.1 (Binding)) — against the adaptive adversary;
* `termination` (Lemma 4.7) — in every fair execution all correct parties decide;
* `out_ncard_le_four` (Lemma 4.7, "within 4 communication rounds"): every party broadcasts at
  most 4 messages.
-/

namespace Podc.BindingCrusaderAgreement.Alg4

open Cslib.Byzantine.AsyncBroadcast Podc.BindingCrusaderAgreement

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Broadcast guards of Algorithm 4 (input `x`, inbox `ib`, own broadcasts `out`). -/
def sendG (t : ℕ) (x : Bool) (ib : P → Set Msg) (out : Set Msg) : Msg → Prop
  | .echo v => v = x ∨ t + 1 ≤ cnt ib (.echo v)
  | .echo2 v => Approved t ib v ∧ ∀ w, .echo2 w ∉ out
  | .echo3 none => BothApproved t ib ∧ ∀ o, .echo3 o ∉ out
  | .echo3 (some v) => Fintype.card P - t ≤ cnt ib (.echo2 v) ∧ ∀ o, .echo3 o ∉ out
  | _ => False

/-- Decision guards of Algorithm 4 (`none` = `⊥`). -/
def decideG (t : ℕ) (ib : P → Set Msg) (out : Set Msg) : Option Bool → Prop
  | none => BothApproved t ib ∧ Fintype.card P - t ≤ cntP ib Msg.IsEcho3 ∧ ∃ o, .echo3 o ∈ out
  | some v => Fintype.card P - t ≤ cnt ib (.echo3 (some v)) ∧ ∃ o, .echo3 o ∈ out

/-- Algorithm 4 as a broadcast protocol with binary inputs and outputs in `{0, 1, ⊥}`. -/
def alg (t : ℕ) : Protocol P Msg Bool (Option Bool) where
  send _ x ib out m := sendG t x ib out m
  decide _ _ ib out o := decideG t ib out o

omit [DecidableEq P] in
theorem isEchoLayer (t : ℕ) : IsEchoLayer t (alg (P := P) t) :=
  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

variable {t : ℕ} {x : P → Bool} {k : FaultKind} {σ : State P Msg (Option Bool)}

/-! ### Justifications -/

theorem echo3_some_just (h : Reachable (alg t) x k t σ) {p : P} {v : Bool}
    (hm : (p, .echo3 (some v)) ∈ σ.sent) :
    Fintype.card P - t ≤ cnt (σ.inbox p) (.echo2 v) := by
  refine h.sent_just (J := fun _ m ib _ => ∀ v, m = .echo3 (some v) →
    Fintype.card P - t ≤ cnt ib (.echo2 v)) ?_ ?_ hm v rfl
  · intro p m ib ib' out out' hib _ hj v hv
    exact (hj v hv).trans (cnt_mono hib _)
  · intro p ib out m hs v hv
    subst hv
    exact hs.1

theorem echo3_none_just (h : Reachable (alg t) x k t σ) {p : P}
    (hm : (p, .echo3 none) ∈ σ.sent) : BothApproved t (σ.inbox p) := by
  refine h.sent_just (J := fun _ m ib _ => m = .echo3 none → BothApproved t ib) ?_ ?_ hm rfl
  · intro p m ib ib' out out' hib _ hj hv
    exact (hj hv).mono hib
  · intro p ib out m hs hv
    subst hv
    exact hs.1

theorem echo3_unique (h : Reachable (alg t) x k t σ) {p : P} {o o' : Option Bool}
    (hv : (p, .echo3 o) ∈ σ.sent) (hw : (p, .echo3 o') ∈ σ.sent) : o = o' := by
  have := h.sent_excl Msg.IsEcho3 ?_ hv hw trivial trivial
  · simpa using this
  · intro p ib out m hs hm m' hm' h2
    cases m with
    | echo3 o =>
      cases m' with
      | echo3 o' => cases o <;> exact hs.2 o' hm'
      | _ => exact h2
    | _ => exact hm

/-- Only `echo`, `echo2`, `echo3` messages are broadcast. -/
theorem sent_kind (h : Reachable (alg t) x k t σ) {p : P} {m : Msg} (hm : (p, m) ∈ σ.sent) :
    (∃ v, m = .echo v) ∨ (∃ v, m = .echo2 v) ∨ (∃ o, m = .echo3 o) := by
  refine h.sent_just (J := fun _ m _ _ =>
    (∃ v, m = .echo v) ∨ (∃ v, m = .echo2 v) ∨ (∃ o, m = .echo3 o)) ?_ ?_ hm
  · intro _ _ _ _ _ _ _ _ hj; exact hj
  · intro p ib out m hs
    cases m with
    | echo v => exact Or.inl ⟨v, rfl⟩
    | echo2 v => exact Or.inr (Or.inl ⟨v, rfl⟩)
    | echo3 o => exact Or.inr (Or.inr ⟨o, rfl⟩)
    | echo4 o => exact hs.elim
    | echo5 o => exact hs.elim

theorem dec_some_just (h : Reachable (alg t) x k t σ) {p : P} {v : Bool}
    (hd : σ.dec p = some (some v)) : Fintype.card P - t ≤ cnt (σ.inbox p) (.echo3 (some v)) := by
  refine h.dec_just (J := fun _ o ib _ => ∀ v, o = some v →
    Fintype.card P - t ≤ cnt ib (.echo3 (some v))) ?_ ?_ hd v rfl
  · intro p o ib ib' out out' hib _ hj v hv
    exact (hj v hv).trans (cnt_mono hib _)
  · intro p ib out o hs v hv
    subst hv
    exact hs.1

theorem dec_none_just (h : Reachable (alg t) x k t σ) {p : P} (hd : σ.dec p = some none) :
    BothApproved t (σ.inbox p) ∧ Fintype.card P - t ≤ cntP (σ.inbox p) Msg.IsEcho3 := by
  refine h.dec_just (J := fun _ o ib _ => o = none →
    BothApproved t ib ∧ Fintype.card P - t ≤ cntP ib Msg.IsEcho3) ?_ ?_ hd rfl
  · intro p o ib ib' out out' hib _ hj hv
    exact ⟨(hj hv).1.mono hib, (hj hv).2.trans (cntP_mono hib _)⟩
  · intro p ib out o hs hv
    subst hv
    exact ⟨hs.1, hs.2.1⟩

/-! ### Safety -/

/-- Lemma 4.8: two `echo3` messages with non-`⊥` values broadcast by (then uncorrupted) parties
carry the same value. -/
theorem echo3_consistent (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ)
    {s s' : P} {v w : Bool} (hv : (s, .echo3 (some v)) ∈ σ.sent)
    (hw : (s', .echo3 (some w)) ∈ σ.sent) : v = w := by
  have h1 := echo3_some_just h hv
  have h2 := echo3_some_just h hw
  have hb := h.bad_ncard_le
  obtain ⟨r, hr1, hr2, hrb⟩ := exists_mem_inter_not_mem (S₁ := {r | Msg.echo2 v ∈ σ.inbox s r})
    (S₂ := {r | Msg.echo2 w ∈ σ.inbox s' r}) (B := σ.bad) (by unfold cnt at h1 h2; omega)
  exact echo2_unique (isEchoLayer t) h (h.genuine hr1 hrb) (h.genuine hr2 hrb)

/-- Lemma 4.4 (Agreement): no two parties decide different non-`⊥` values. This holds for all
recorded decisions, also those of parties corrupted after deciding. -/
theorem agreement (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ) {p q : P}
    {a b : Bool} (hp : σ.dec p = some (some a)) (hq : σ.dec q = some (some b)) : a = b := by
  have h1 := dec_some_just h hp
  have h2 := dec_some_just h hq
  have hb := h.bad_ncard_le
  obtain ⟨r, hr1, hr2, hrb⟩ := exists_mem_inter_not_mem
    (S₁ := {r | Msg.echo3 (some a) ∈ σ.inbox p r})
    (S₂ := {r | Msg.echo3 (some b) ∈ σ.inbox q r}) (B := σ.bad) (by unfold cnt at h1 h2; omega)
  simpa using echo3_unique h (h.genuine hr1 hrb) (h.genuine hr2 hrb)

/-- Lemma 4.5 (Validity): if all non-faulty parties have input `v`, every decision is `v`.
Non-faulty parties are those of a set `H` with `|Hᶜ| ≤ t` that contains no corrupted party
(with adaptive corruption, `H` is the set of parties that are never corrupted). The conclusion
holds for every recorded decision. -/
theorem validity (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ) {H : Set P}
    (hbad : σ.bad ⊆ Hᶜ) (hH : Hᶜ.ncard ≤ t) {v : Bool} (hx : ∀ p ∈ H, x p = v) (p : P) :
    σ.dec p = none ∨ σ.dec p = some (some v) := by
  have hA := isEchoLayer (P := P) t
  have ht2 : 2 * t < Fintype.card P := by omega
  have hb := h.bad_ncard_le
  rcases hd : σ.dec p with _ | o
  · exact Or.inl rfl
  · right
    rcases o with _ | w
    · obtain ⟨⟨h1, h2⟩, _⟩ := dec_none_just h hd
      exfalso
      cases v
      · exact not_approved_of_inputs hA ht2 h hbad hH hx p h1
      · exact not_approved_of_inputs hA ht2 h hbad hH hx p h2
    · by_cases hw : w = v
      · rw [hw]
      exfalso
      have hw' : w = !v := by cases w <;> cases v <;> simp_all
      subst hw'
      have h1 := dec_some_just h hd
      obtain ⟨r, hr, hrb⟩ := h.exists_good (S := {r | Msg.echo3 (some (!v)) ∈ σ.inbox p r})
        (by unfold cnt at h1; omega)
      have h2 := echo3_some_just h (h.genuine hr hrb)
      obtain ⟨r', hr', hrb'⟩ := h.exists_good (S := {r' | Msg.echo2 (!v) ∈ σ.inbox r r'})
        (by unfold cnt at h2; omega)
      exact not_echo2_of_inputs hA ht2 h hbad hH hx r' (h.genuine hr' hrb')

/-- Lemma 4.9 (Binding, Definition 3.1): once some party has decided, there is a value `b`
such that in every extension of the execution no party ever decides `1 − b`.

The paper fixes `b` at the first decision of a non-faulty party; we prove the statement for
every reachable state with a decision (in particular the first one), against the adaptive
adversary (extensions may corrupt further parties) and for all recorded decisions. -/
theorem binding (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ) {p : P}
    (hp : σ.dec p ≠ none) : ∃ b : Bool, ∀ σ', Reach (alg t) x k t σ σ' →
      ∀ q, σ'.dec q ≠ some (some (!b)) := by
  have hb := h.bad_ncard_le
  by_cases hex : ∃ s u, (s, Msg.echo3 (some u)) ∈ σ.sent
  · obtain ⟨s, u, hs⟩ := hex
    refine ⟨u, fun σ' hσ' q hq => ?_⟩
    have h' := h.reach hσ'
    have hb' := h'.bad_ncard_le
    have h1 := dec_some_just h' hq
    obtain ⟨r, hr, hrb⟩ := h'.exists_good (S := {r | Msg.echo3 (some (!u)) ∈ σ'.inbox q r})
      (by unfold cnt at h1; omega)
    have := echo3_consistent ht h' (hσ'.sent_subset hs) (h'.genuine hr hrb)
    cases u <;> simp at this
  · push Not at hex
    refine ⟨true, fun σ' hσ' q hq => ?_⟩
    have h' := h.reach hσ'
    have hb' := h'.bad_ncard_le
    rcases hd : σ.dec p with _ | o
    · exact hp hd
    rcases o with _ | v
    · -- `p` decided `⊥`: the uncorrupted senders of its `n − t` `echo3` messages sent `⊥`.
      obtain ⟨_, h1⟩ := dec_none_just h hd
      let S := {s | ∃ m ∈ σ.inbox p s, Msg.IsEcho3 m}
      let G := S \ σ.bad
      have hG : ∀ s ∈ G, (s, Msg.echo3 none) ∈ σ.sent := by
        intro s ⟨⟨m, hm, hm3⟩, hsb⟩
        have hsent := h.genuine hm hsb
        cases m with
        | echo3 o =>
          cases o with
          | none => exact hsent
          | some u => exact absurd hsent (hex s u)
        | _ => exact hm3.elim
      have h2 := dec_some_just h' hq
      let T := {r | Msg.echo3 (some false) ∈ σ'.inbox q r}
      have hTG : T ∩ G ⊆ σ'.bad \ σ.bad := by
        intro r ⟨hrT, hrG⟩
        refine ⟨by_contra fun hrb => ?_, hrG.2⟩
        have := echo3_unique h' (h'.genuine hrT hrb) (hσ'.sent_subset (hG r hrG))
        simp at this
      have hS : S ⊆ G ∪ σ.bad := fun s hs => by
        by_cases hsb : s ∈ σ.bad
        · exact Or.inr hsb
        · exact Or.inl ⟨hs, hsb⟩
      have e1 := (Set.ncard_le_ncard hS).trans (Set.ncard_union_le _ _)
      have hT : T ⊆ Gᶜ ∪ (σ'.bad \ σ.bad) := fun r hr => by
        by_cases hrG : r ∈ G
        · exact Or.inr (hTG ⟨hr, hrG⟩)
        · exact Or.inl hrG
      have e2 := (Set.ncard_le_ncard hT).trans (Set.ncard_union_le _ _)
      have e3 := Set.ncard_add_ncard_compl G
      have e4 := Set.ncard_sdiff_add_ncard_of_subset hσ'.bad_subset
      rw [Nat.card_eq_fintype_card] at e3
      have e5 : Fintype.card P - t ≤ T.ncard := h2
      have e6 : Fintype.card P - t ≤ S.ncard := h1
      omega
    · -- `p` decided a value: some uncorrupted party sent a non-`⊥` `echo3`.
      have h1 := dec_some_just h hd
      obtain ⟨r, hr, hrb⟩ := h.exists_good (S := {r | Msg.echo3 (some v) ∈ σ.inbox p r})
        (by unfold cnt at h1; omega)
      exact absurd (h.genuine hr hrb) (hex r v)

/-- The number of broadcasts of every party is at most 4: one or two `echo`, one `echo2`, one
`echo3` (the content of "terminates within 4 communication rounds" in Lemma 4.7). -/
theorem out_ncard_le_four (h : Reachable (alg t) x k t σ) (p : P) : (σ.out p).ncard ≤ 4 := by
  classical
  let w0 : Bool := if hw : ∃ w, (p, Msg.echo2 w) ∈ σ.sent then hw.choose else true
  let o0 : Option Bool := if ho : ∃ o, (p, Msg.echo3 o) ∈ σ.sent then ho.choose else none
  have hsub : σ.out p ⊆ {.echo true, .echo false, .echo2 w0, .echo3 o0} := by
    intro m hm
    rcases sent_kind h hm with ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨o, rfl⟩
    · cases v <;> simp
    · have hw : ∃ w, (p, Msg.echo2 w) ∈ σ.sent := ⟨v, hm⟩
      have : v = w0 := by
        simp only [w0, dite_eq_left_of_eq_true (eq_true hw)]
        exact echo2_unique (isEchoLayer t) h hm hw.choose_spec
      simp [this]
    · have ho : ∃ o, (p, Msg.echo3 o) ∈ σ.sent := ⟨o, hm⟩
      have : o = o0 := by
        simp only [o0, dite_eq_left_of_eq_true (eq_true ho)]
        exact echo3_unique h hm ho.choose_spec
      simp [this]
  refine (Set.ncard_le_ncard hsub).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
  simp

/-! ### Termination (Lemma 4.7) -/

section Termination

variable (E : Exec (alg t) x k t) (hF : E.Fair)
include hF

/-- Every correct party eventually broadcasts an `echo3` message. -/
theorem eventually_echo3 (ht : 3 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i o, (q, Msg.echo3 o) ∈ (E.σ i).sent := by
  have hA := isEchoLayer (P := P) t
  have ht2 : 2 * t < Fintype.card P := by omega
  by_cases hmix : ∃ s₁ s₂ i₁ i₂ w, E.Correct s₁ ∧ E.Correct s₂ ∧
      (s₁, Msg.echo2 w) ∈ (E.σ i₁).sent ∧ (s₂, Msg.echo2 (!w)) ∈ (E.σ i₂).sent
  · -- some correct parties sent different `echo2` values: everybody approves both.
    obtain ⟨s₁, s₂, i₁, i₂, w, -, -, h₁, h₂⟩ := hmix
    obtain ⟨j₁, hj₁⟩ := Exec.approved_spread hA E hF ht
      (echo2_approved hA (E.reachable i₁) h₁) hq
    obtain ⟨j₂, hj₂⟩ := Exec.approved_spread hA E hF ht
      (echo2_approved hA (E.reachable i₂) h₂) hq
    obtain ⟨j, m', hm', hj⟩ := E.eventually_sent hF hq (φ := Msg.IsEcho3) (m := .echo3 none)
      trivial (i := max j₁ j₂) fun j hij hno => ⟨bothApproved_of_ne (by cases w <;> simp)
        (hj₁ j (le_of_max_le_left hij)) (hj₂ j (le_of_max_le_right hij)),
        fun o ho => hno (.echo3 o) trivial ho⟩
    cases m' with
    | echo3 o => exact ⟨j, o, hj⟩
    | _ => exact absurd hm' id
  · -- all correct parties sent the same `echo2` value `w`.
    push Not at hmix
    obtain ⟨i, w, hi⟩ := Exec.eventually_echo2 hA E hF ht hq
    have hall : ∀ s ∈ {s | E.Correct s}, ∃ i, (s, Msg.echo2 w) ∈ (E.σ i).sent := by
      intro s hs
      obtain ⟨i', w', hi'⟩ := Exec.eventually_echo2 hA E hF ht hs
      by_cases hww : w' = w
      · exact ⟨i', hww ▸ hi'⟩
      · have : w' = !w := by cases w <;> cases w' <;> simp_all
        subst this
        exact absurd hi' (hmix q s i i' w hq hs hi)
    obtain ⟨j, hj⟩ := E.eventually_rcv_all hF (fun s hs => hs) (m := fun _ => .echo2 w) hall hq
    obtain ⟨j', m', hm', hj'⟩ := E.eventually_sent hF hq (φ := Msg.IsEcho3)
      (m := .echo3 (some w)) trivial (i := j) fun j₂ hij hno =>
        ⟨(E.card_sub_le_ncard_correct).trans (le_cnt fun s hs => E.rcv_mono hij (hj s hs)),
          fun o ho => hno (.echo3 o) trivial ho⟩
    cases m' with
    | echo3 o => exact ⟨j', o, hj'⟩
    | _ => exact absurd hm' id

/-- Lemma 4.7 (Termination): in every fair execution, every correct (never corrupted) party
decides. -/
theorem termination (ht : 3 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i, (E.σ i).dec q ≠ none := by
  have hA := isEchoLayer (P := P) t
  obtain ⟨iq, oq, hiq⟩ := eventually_echo3 E hF ht hq
  by_cases hbot : ∃ s i, E.Correct s ∧ (s, Msg.echo3 none) ∈ (E.σ i).sent
  · -- some correct party sent `⟨echo3, ⊥⟩`: everybody approves both values and gets `n − t`
    -- `echo3` messages, so decides `⊥` (unless it decided before).
    obtain ⟨s, i, -, hs⟩ := hbot
    have hboth := echo3_none_just (E.reachable i) hs
    obtain ⟨j₁, hj₁⟩ := Exec.approved_spread hA E hF ht hboth.1 hq
    obtain ⟨j₂, hj₂⟩ := Exec.approved_spread hA E hF ht hboth.2 hq
    obtain ⟨j₃, hj₃⟩ := E.eventually_rcv_all' hF (S := {s | E.Correct s}) (fun s hs => hs)
      (φ := Msg.IsEcho3) (fun s hs => by
        obtain ⟨i, o, hi⟩ := eventually_echo3 E hF ht hs
        exact ⟨i, .echo3 o, trivial, hi⟩) hq
    refine E.eventually_dec hF hq (o := none) (i := max (max j₁ j₂) (max j₃ iq))
      fun j hij _ => ⟨⟨hj₁ j (by omega), hj₂ j (by omega)⟩,
        (E.card_sub_le_ncard_correct).trans (le_cntP fun s hs => ?_),
        ⟨oq, E.sent_mono (by omega) hiq⟩⟩
    obtain ⟨m, hm, hm'⟩ := hj₃ s hs
    exact ⟨m, E.rcv_mono (by omega) hm', hm⟩
  · -- all correct parties sent `⟨echo3, w⟩` for the same `w` (Lemma 4.8).
    push Not at hbot
    obtain ⟨w, rfl⟩ : ∃ w, oq = some w := by
      cases oq with
      | none => exact absurd hiq (hbot q iq hq)
      | some w => exact ⟨w, rfl⟩
    have hall : ∀ s ∈ {s | E.Correct s}, ∃ i, (s, Msg.echo3 (some w)) ∈ (E.σ i).sent := by
      intro s hs
      obtain ⟨i, o, hi⟩ := eventually_echo3 E hF ht hs
      cases o with
      | none => exact absurd hi (hbot s i hs)
      | some w' =>
        refine ⟨i, ?_⟩
        have := echo3_consistent ht (E.reachable (max i iq)) (E.sent_mono (le_max_left _ _) hi)
          (E.sent_mono (le_max_right _ _) hiq)
        rwa [this] at hi
    obtain ⟨j, hj⟩ := E.eventually_rcv_all hF (fun s hs => hs) (m := fun _ => .echo3 (some w))
      hall hq
    exact E.eventually_dec hF hq (o := some w) (i := max j iq) fun j' hij _ =>
      ⟨(E.card_sub_le_ncard_correct).trans
        (le_cnt fun s hs => E.rcv_mono (le_of_max_le_left hij) (hj s hs)),
        ⟨some w, E.sent_mono (le_of_max_le_right hij) hiq⟩⟩

end Termination

/-- Theorem 4.3 (Algorithm 4 implements BCA): agreement, validity, binding, termination and
at most 4 broadcasts per party, for `n ≥ 3t + 1` and an adaptive Byzantine adversary. -/
theorem theorem_4_3 (ht : 3 * t < Fintype.card P) :
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ p q a b,
      σ.dec p = some (some a) → σ.dec q = some (some b) → a = b) ∧
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ (H : Set P) v, σ.bad ⊆ Hᶜ → Hᶜ.ncard ≤ t →
      (∀ p ∈ H, x p = v) → ∀ p, σ.dec p = none ∨ σ.dec p = some (some v)) ∧
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ p, σ.dec p ≠ none →
      ∃ b : Bool, ∀ σ', Reach (alg t) x .byzantine t σ σ' → ∀ q, σ'.dec q ≠ some (some (!b))) ∧
    (∀ E : Exec (alg t) x .byzantine t, E.Fair → ∀ q, E.Correct q → ∃ i, (E.σ i).dec q ≠ none) ∧
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ p, (σ.out p).ncard ≤ 4) :=
  ⟨fun _ h _ _ _ _ hp hq => agreement ht h hp hq,
   fun _ h _ _ hbad hH hx p => validity ht h hbad hH hx p,
   fun _ h _ hp => binding ht h hp,
   fun E hF _ hq => termination E hF ht hq,
   fun _ h p => out_ncard_le_four h p⟩

end Podc.BindingCrusaderAgreement.Alg4
