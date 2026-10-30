import Papers.PODC2022.BindingCrusaderAgreement.EchoLayer

/-!
# Algorithm 6: Graded Binding Crusader Agreement with Byzantine faults (`GBCA_Byz`)

Abraham, Ben-David, Yandamuri, PODC 2022, Section 5.2, Algorithm 6, Theorem 5.3 (its proof is
deferred to the full version; we give our own).

After the echo layer (`EchoLayer.lean`), with `n ≥ 3t + 1`:
* lines 8–12: `⟨echo3, v⟩` after `⟨echo2, v⟩` from `n − t` parties; `⟨echo3, ⊥⟩` after `echo2`
  from `n − t` parties and `|approvedVals| > 1`;
* lines 13–17 (`echo4`) and 18–22 (`echo5`): the same with `echo3` resp. `echo4`;
* lines 23–29: decide `v` grade 2 after `⟨echo5, v⟩` from `n − t` parties; `v` grade 1 after
  `echo5` from `n − t` parties, one of them `⟨echo5, v⟩`, `⟨echo4, v⟩` from `t + 1` parties and
  `|approvedVals| > 1`; `⊥` grade 0 after `⟨echo5, ⊥⟩` from `n − t` parties and
  `|approvedVals| > 1`.

The "wait until" clauses are sequential in the paper, so we require the previous `echo` level to
be sent before the next one; precedence between simultaneously enabled branches is liberal.

## Main results
* `graded_agreement`, `graded_agreement_zero` (Definition 3.2, Graded Agreement);
* `validity` (all decisions are `v` grade 2 if all non-faulty inputs are `v`);
* `graded_binding` (Definition 3.2, Graded Binding, against the adaptive adversary);
* `termination` (every correct party decides in every fair execution);
* `out_ncard_le_six` ("terminates in at most 6 communication rounds": at most 6 broadcasts);
* `theorem_5_3`.
-/

namespace Podc.BindingCrusaderAgreement.Alg6

open Cslib.Byzantine.AsyncBroadcast Podc.BindingCrusaderAgreement

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Some `echo3` was broadcast. -/
def Sent3 (out : Set Msg) : Prop := ∃ o, Msg.echo3 o ∈ out
/-- Some `echo4` was broadcast. -/
def Sent4 (out : Set Msg) : Prop := ∃ o, Msg.echo4 o ∈ out
/-- Some `echo5` was broadcast. -/
def Sent5 (out : Set Msg) : Prop := ∃ o, Msg.echo5 o ∈ out

/-- The monotone part of the broadcast guards of Algorithm 6. -/
def sendJ (t : ℕ) (x : Bool) (ib : P → Set Msg) (out : Set Msg) : Msg → Prop
  | .echo v => v = x ∨ t + 1 ≤ cnt ib (.echo v)
  | .echo2 v => Approved t ib v
  | .echo3 (some v) => Fintype.card P - t ≤ cnt ib (.echo2 v)
  | .echo3 none => Fintype.card P - t ≤ cntP ib Msg.IsEcho2 ∧ BothApproved t ib
  | .echo4 (some v) => Fintype.card P - t ≤ cnt ib (.echo3 (some v)) ∧ Sent3 out
  | .echo4 none => Fintype.card P - t ≤ cntP ib Msg.IsEcho3 ∧ BothApproved t ib ∧ Sent3 out
  | .echo5 (some v) => Fintype.card P - t ≤ cnt ib (.echo4 (some v)) ∧ Sent4 out
  | .echo5 none => Fintype.card P - t ≤ cntP ib Msg.IsEcho4 ∧ BothApproved t ib ∧ Sent4 out

/-- "Only one message of each level" (`echo2` … `echo5`). -/
def Fresh (out : Set Msg) : Msg → Prop
  | .echo _ => True
  | .echo2 _ => ∀ w, .echo2 w ∉ out
  | .echo3 _ => ∀ o, .echo3 o ∉ out
  | .echo4 _ => ∀ o, .echo4 o ∉ out
  | .echo5 _ => ∀ o, .echo5 o ∉ out

/-- Decision guards of Algorithm 6 (lines 23–29). -/
def decideJ (t : ℕ) (ib : P → Set Msg) (out : Set Msg) : Grade → Prop
  | .two v => Fintype.card P - t ≤ cnt ib (.echo5 (some v)) ∧ Sent5 out
  | .one v => Fintype.card P - t ≤ cntP ib Msg.IsEcho5 ∧ 1 ≤ cnt ib (.echo5 (some v)) ∧
      t + 1 ≤ cnt ib (.echo4 (some v)) ∧ BothApproved t ib ∧ Sent5 out
  | .zero => Fintype.card P - t ≤ cnt ib (.echo5 none) ∧ BothApproved t ib ∧ Sent5 out

/-- Algorithm 6 as a broadcast protocol. -/
def alg (t : ℕ) : Protocol P Msg Bool Grade where
  send _ x ib out m := sendJ t x ib out m ∧ Fresh out m
  decide _ _ ib out g := decideJ t ib out g

omit [DecidableEq P] in
theorem isEchoLayer (t : ℕ) : IsEchoLayer t (alg (P := P) t) :=
  ⟨fun _ _ _ _ _ => by simp [alg, sendJ, Fresh], fun _ _ _ _ _ => Iff.rfl⟩

variable {t : ℕ} {x : P → Bool} {k : FaultKind} {σ : State P Msg Grade}

/-! ### Justifications -/

omit [DecidableEq P] in
theorem sendJ_mono {x : Bool} {ib ib' : P → Set Msg} {out out' : Set Msg}
    (hib : ∀ s, ib s ⊆ ib' s) (hout : out ⊆ out') {m : Msg} (h : sendJ t x ib out m) :
    sendJ t x ib' out' m := by
  have s3 : Sent3 out → Sent3 out' := fun ⟨o, ho⟩ => ⟨o, hout ho⟩
  have s4 : Sent4 out → Sent4 out' := fun ⟨o, ho⟩ => ⟨o, hout ho⟩
  rcases m with v | v | (_ | v) | (_ | v) | (_ | v) <;> simp only [sendJ] at h ⊢
  · exact h.imp id fun h => h.trans (cnt_mono hib _)
  · exact h.mono hib
  · exact ⟨h.1.trans (cntP_mono hib _), h.2.mono hib⟩
  · exact h.trans (cnt_mono hib _)
  · exact ⟨h.1.trans (cntP_mono hib _), h.2.1.mono hib, s3 h.2.2⟩
  · exact ⟨h.1.trans (cnt_mono hib _), s3 h.2⟩
  · exact ⟨h.1.trans (cntP_mono hib _), h.2.1.mono hib, s4 h.2.2⟩
  · exact ⟨h.1.trans (cnt_mono hib _), s4 h.2⟩

theorem just (h : Reachable (alg t) x k t σ) {p : P} {m : Msg} (hm : (p, m) ∈ σ.sent) :
    sendJ t (x p) (σ.inbox p) (σ.out p) m :=
  h.sent_just (J := fun p m ib out => sendJ t (x p) ib out m)
    (fun _ _ _ _ _ _ hib hout hj => sendJ_mono hib hout hj)
    (fun _ _ _ _ (hs : sendJ _ _ _ _ _ ∧ _) => hs.1) hm

theorem dec_just (h : Reachable (alg t) x k t σ) {p : P} {g : Grade} (hd : σ.dec p = some g) :
    decideJ t (σ.inbox p) (σ.out p) g := by
  refine h.dec_just (J := fun _ g ib out => decideJ t ib out g) ?_ (fun _ _ _ _ hs => hs) hd
  intro p g ib ib' out out' hib hout hj
  have s5 : Sent5 out → Sent5 out' := fun ⟨o, ho⟩ => ⟨o, hout ho⟩
  rcases g with v | v | _ <;> simp only [decideJ] at hj ⊢
  · exact ⟨hj.1.trans (cnt_mono hib _), s5 hj.2⟩
  · exact ⟨hj.1.trans (cntP_mono hib _), hj.2.1.trans (cnt_mono hib _),
      hj.2.2.1.trans (cnt_mono hib _), hj.2.2.2.1.mono hib, s5 hj.2.2.2.2⟩
  · exact ⟨hj.1.trans (cnt_mono hib _), hj.2.1.mono hib, s5 hj.2.2⟩

theorem excl (h : Reachable (alg t) x k t σ) (φ : Msg → Prop)
    (hφ : ∀ out m, Fresh out m → φ m → ∀ m' ∈ out, ¬ φ m') {p : P} {m m' : Msg}
    (hm : (p, m) ∈ σ.sent) (hm' : (p, m') ∈ σ.sent) (h1 : φ m) (h2 : φ m') : m = m' :=
  h.sent_excl φ (fun _ _ out m (hs : sendJ _ _ _ _ _ ∧ _) hm => hφ out m hs.2 hm) hm hm' h1 h2

theorem echo3_unique (h : Reachable (alg t) x k t σ) {p : P} {o o' : Option Bool}
    (hv : (p, .echo3 o) ∈ σ.sent) (hw : (p, .echo3 o') ∈ σ.sent) : o = o' := by
  have := excl h Msg.IsEcho3 (fun out m hf hm m' hm' h3 => by
    cases m <;> (try exact hm.elim)
    cases m' <;> (try exact h3.elim)
    exact hf _ hm') hv hw trivial trivial
  simpa using this

theorem echo4_unique (h : Reachable (alg t) x k t σ) {p : P} {o o' : Option Bool}
    (hv : (p, .echo4 o) ∈ σ.sent) (hw : (p, .echo4 o') ∈ σ.sent) : o = o' := by
  have := excl h Msg.IsEcho4 (fun out m hf hm m' hm' h3 => by
    cases m <;> (try exact hm.elim)
    cases m' <;> (try exact h3.elim)
    exact hf _ hm') hv hw trivial trivial
  simpa using this

theorem echo5_unique (h : Reachable (alg t) x k t σ) {p : P} {o o' : Option Bool}
    (hv : (p, .echo5 o) ∈ σ.sent) (hw : (p, .echo5 o') ∈ σ.sent) : o = o' := by
  have := excl h Msg.IsEcho5 (fun out m hf hm m' hm' h3 => by
    cases m <;> (try exact hm.elim)
    cases m' <;> (try exact h3.elim)
    exact hf _ hm') hv hw trivial trivial
  simpa using this

/-! ### Consistency of the levels -/

section Consistency

variable (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ)
include ht h

/-- Some uncorrupted party broadcasts `m` if `n − t` parties sent it to `p`. -/
theorem exists_sent_of_cnt {p : P} {m : Msg} (hc : Fintype.card P - t ≤ cnt (σ.inbox p) m) :
    ∃ r, (r, m) ∈ σ.sent := by
  have hb := h.bad_ncard_le
  obtain ⟨r, hr, hrb⟩ := h.exists_good (S := {r | m ∈ σ.inbox p r}) (by unfold cnt at hc; omega)
  exact ⟨r, h.genuine hr hrb⟩

/-- Analogue of Lemma 4.8 for Algorithm 6. -/
theorem echo3_consistent {s s' : P} {v w : Bool} (hv : (s, .echo3 (some v)) ∈ σ.sent)
    (hw : (s', .echo3 (some w)) ∈ σ.sent) : v = w := by
  have h1 : Fintype.card P - t ≤ cnt (σ.inbox s) (.echo2 v) := just h hv
  have h2 : Fintype.card P - t ≤ cnt (σ.inbox s') (.echo2 w) := just h hw
  have hb := h.bad_ncard_le
  obtain ⟨r, hr1, hr2, hrb⟩ := exists_mem_inter_not_mem (S₁ := {r | Msg.echo2 v ∈ σ.inbox s r})
    (S₂ := {r | Msg.echo2 w ∈ σ.inbox s' r}) (B := σ.bad) (by unfold cnt at h1 h2; omega)
  exact echo2_unique (isEchoLayer t) h (h.genuine hr1 hrb) (h.genuine hr2 hrb)

theorem echo3_of_echo4 {r : P} {v : Bool} (hr : (r, .echo4 (some v)) ∈ σ.sent) :
    ∃ r', (r', .echo3 (some v)) ∈ σ.sent :=
  exists_sent_of_cnt ht h (just h hr).1

theorem echo4_of_echo5 {r : P} {v : Bool} (hr : (r, .echo5 (some v)) ∈ σ.sent) :
    ∃ r', (r', .echo4 (some v)) ∈ σ.sent :=
  exists_sent_of_cnt ht h (just h hr).1

theorem echo4_consistent {s s' : P} {v w : Bool} (hv : (s, .echo4 (some v)) ∈ σ.sent)
    (hw : (s', .echo4 (some w)) ∈ σ.sent) : v = w := by
  obtain ⟨r, hr⟩ := echo3_of_echo4 ht h hv
  obtain ⟨r', hr'⟩ := echo3_of_echo4 ht h hw
  exact echo3_consistent ht h hr hr'

theorem echo5_consistent {s s' : P} {v w : Bool} (hv : (s, .echo5 (some v)) ∈ σ.sent)
    (hw : (s', .echo5 (some w)) ∈ σ.sent) : v = w := by
  obtain ⟨r, hr⟩ := echo4_of_echo5 ht h hv
  obtain ⟨r', hr'⟩ := echo4_of_echo5 ht h hw
  exact echo4_consistent ht h hr hr'

/-- A decision `v` with grade `≥ 1` requires an `⟨echo4, v⟩` broadcast. -/
theorem echo4_of_hasVal {q : P} {g : Grade} {v : Bool} (hq : σ.dec q = some g)
    (hg : g.HasVal v) : ∃ r, (r, .echo4 (some v)) ∈ σ.sent := by
  have hd := dec_just h hq
  rcases hg with rfl | rfl
  · obtain ⟨r, hr⟩ := exists_sent_of_cnt ht h hd.1
    exact echo4_of_echo5 ht h hr
  · have hb := h.bad_ncard_le
    obtain ⟨r, hr, hrb⟩ := h.exists_good (S := {r | Msg.echo4 (some v) ∈ σ.inbox q r})
      (by have := hd.2.2.1; unfold cnt at this; omega)
    exact ⟨r, h.genuine hr hrb⟩

/-- Definition 3.2 (Graded Agreement), first part: no two parties decide different values with
grades `≥ 1` (all recorded decisions). -/
theorem graded_agreement {p q : P} {g g' : Grade} {v w : Bool} (hp : σ.dec p = some g)
    (hq : σ.dec q = some g') (hgv : g.HasVal v) (hgw : g'.HasVal w) : v = w := by
  obtain ⟨r, hr⟩ := echo4_of_hasVal ht h hp hgv
  obtain ⟨r', hr'⟩ := echo4_of_hasVal ht h hq hgw
  exact echo4_consistent ht h hr hr'

/-- Definition 3.2 (Graded Agreement), second part: if a party decides `v` grade 2, nobody
decides `⊥` grade 0. -/
theorem graded_agreement_zero {p q : P} {v : Bool} (hp : σ.dec p = some (.two v)) :
    σ.dec q ≠ some .zero := by
  intro hq
  have h1 := (dec_just h hp).1
  have h2 := (dec_just h hq).1
  have hb := h.bad_ncard_le
  obtain ⟨r, hr1, hr2, hrb⟩ := exists_mem_inter_not_mem
    (S₁ := {r | Msg.echo5 (some v) ∈ σ.inbox p r}) (S₂ := {r | Msg.echo5 none ∈ σ.inbox q r})
    (B := σ.bad) (by unfold cnt at h1 h2; omega)
  simpa using echo5_unique h (h.genuine hr1 hrb) (h.genuine hr2 hrb)

end Consistency


/-! ### Validity -/

/-- Definition 3.2 (Validity): if all non-faulty parties (a set `H` without corrupted parties,
`|Hᶜ| ≤ t`) have input `v`, every recorded decision is `v` grade 2. -/
theorem validity (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ) {H : Set P}
    (hbad : σ.bad ⊆ Hᶜ) (hH : Hᶜ.ncard ≤ t) {v : Bool} (hx : ∀ p ∈ H, x p = v) (p : P) :
    σ.dec p = none ∨ σ.dec p = some (.two v) := by
  have hA := isEchoLayer (P := P) t
  have ht2 : 2 * t < Fintype.card P := by omega
  have hnb : ¬ BothApproved t (σ.inbox p) := fun hb => by
    cases v
    · exact not_approved_of_inputs hA ht2 h hbad hH hx p hb.1
    · exact not_approved_of_inputs hA ht2 h hbad hH hx p hb.2
  rcases hd : σ.dec p with _ | g
  · exact Or.inl rfl
  right
  have hj := dec_just h hd
  rcases g with w | w | _
  · by_cases hw : w = v
    · rw [hw]
    exfalso
    have hw' : w = !v := by cases w <;> cases v <;> simp_all
    subst hw'
    obtain ⟨r, hr⟩ := echo4_of_hasVal ht h hd (Or.inl rfl)
    obtain ⟨r', hr'⟩ := echo3_of_echo4 ht h hr
    obtain ⟨r'', hr''⟩ := exists_sent_of_cnt ht h (just h hr')
    exact not_echo2_of_inputs hA ht2 h hbad hH hx r'' hr''
  · exact absurd hj.2.2.2.1 hnb
  · exact absurd hj.2.1 hnb

/-! ### Graded binding -/

/-- If, at `σ`, parties `G` (uncorrupted at `σ`, `|G| + |σ.bad| ≥ n − t`) have broadcast
`⟨echo3, ⊥⟩`, then in no extension does anybody receive `⟨echo3, w⟩` from `n − t` parties. -/
theorem no_echo3_quorum (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ)
    {G : Set P} (hGb : ∀ g ∈ G, g ∉ σ.bad) (hGs : ∀ g ∈ G, (g, .echo3 none) ∈ σ.sent)
    (hG : Fintype.card P - t ≤ G.ncard + σ.bad.ncard) {σ' : State P Msg Grade}
    (hσ' : Reach (alg t) x k t σ σ') (q : P) (w : Bool) :
    ¬ Fintype.card P - t ≤ cnt (σ'.inbox q) (.echo3 (some w)) := by
  intro hT
  have h' := h.reach hσ'
  have hb' := h'.bad_ncard_le
  let T := {r | Msg.echo3 (some w) ∈ σ'.inbox q r}
  have hTG : T ∩ G ⊆ σ'.bad \ σ.bad := by
    intro r ⟨hrT, hrG⟩
    refine ⟨by_contra fun hrb => ?_, hGb r hrG⟩
    have := echo3_unique h' (h'.genuine hrT hrb) (hσ'.sent_subset (hGs r hrG))
    simp at this
  have hT' : T ⊆ Gᶜ ∪ (σ'.bad \ σ.bad) := fun r hr => by
    by_cases hrG : r ∈ G
    · exact Or.inr (hTG ⟨hr, hrG⟩)
    · exact Or.inl hrG
  have e2 := (Set.ncard_le_ncard hT').trans (Set.ncard_union_le _ _)
  have e3 := Set.ncard_add_ncard_compl G
  have e4 := Set.ncard_sdiff_add_ncard_of_subset hσ'.bad_subset
  rw [Nat.card_eq_fintype_card] at e3
  have e5 : Fintype.card P - t ≤ T.ncard := hT
  omega

/-- From `n − t` senders of class `φ` in an inbox, an uncorrupted one broadcast such a message. -/
theorem exists_sent_of_cntP (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ)
    {p : P} {φ : Msg → Prop} (hc : Fintype.card P - t ≤ cntP (σ.inbox p) φ) :
    ∃ r m, φ m ∧ (r, m) ∈ σ.sent := by
  have hb := h.bad_ncard_le
  obtain ⟨r, ⟨m, hm, hφ⟩, hrb⟩ := h.exists_good (S := {r | ∃ m ∈ σ.inbox p r, φ m})
    (by unfold cntP at hc; omega)
  exact ⟨r, m, hφ, h.genuine hm hrb⟩

/-- Definition 3.2 (Graded Binding): once some party has decided, there is a value `b` such that
in no extension does any party decide `1 − b` with grade `1` or `2`. -/
theorem graded_binding (ht : 3 * t < Fintype.card P) (h : Reachable (alg t) x k t σ) {p : P}
    (hp : σ.dec p ≠ none) : ∃ b : Bool, ∀ σ', Reach (alg t) x k t σ σ' →
      ∀ q g, σ'.dec q = some g → ¬ g.HasVal (!b) := by
  have hb := h.bad_ncard_le
  by_cases hex : ∃ s u, (s, Msg.echo3 (some u)) ∈ σ.sent
  · obtain ⟨s, u, hs⟩ := hex
    refine ⟨u, fun σ' hσ' q g hq hg => ?_⟩
    have h' := h.reach hσ'
    obtain ⟨r, hr⟩ := echo4_of_hasVal ht h' hq hg
    obtain ⟨r', hr'⟩ := echo3_of_echo4 ht h' hr
    have := echo3_consistent ht h' (hσ'.sent_subset hs) hr'
    cases u <;> simp at this
  · push Not at hex
    refine ⟨true, fun σ' hσ' q g hq hg => ?_⟩
    have h' := h.reach hσ'
    obtain ⟨g₀, hg₀⟩ := Option.ne_none_iff_exists'.1 hp
    -- the decider received `echo5` from `n − t` parties
    have h5 : Fintype.card P - t ≤ cntP (σ.inbox p) Msg.IsEcho5 := by
      have hj := dec_just h hg₀
      rcases g₀ with v | v | _
      · exact hj.1.trans (cnt_le_cntP trivial)
      · exact hj.1
      · exact hj.1.trans (cnt_le_cntP trivial)
    obtain ⟨s₁, m₁, hm₁, hs₁⟩ := exists_sent_of_cntP ht h h5
    have h4 : Fintype.card P - t ≤ cntP (σ.inbox s₁) Msg.IsEcho4 := by
      rcases m₁ with _ | _ | _ | _ | (_ | v) <;> try exact hm₁.elim
      · exact (just h hs₁).1
      · exact (just h hs₁).1.trans (cnt_le_cntP trivial)
    obtain ⟨s₂, m₂, hm₂, hs₂⟩ := exists_sent_of_cntP ht h h4
    rcases m₂ with _ | _ | _ | (_ | v) | _ <;> try exact hm₂.elim
    · -- `s₂` broadcast `⟨echo4, ⊥⟩`: `n − t` parties sent it `echo3`, all of them `⊥`
      have h3 : Fintype.card P - t ≤ cntP (σ.inbox s₂) Msg.IsEcho3 := (just h hs₂).1
      let S := {r | ∃ m ∈ σ.inbox s₂ r, Msg.IsEcho3 m}
      let G := S \ σ.bad
      have hGs : ∀ g ∈ G, (g, Msg.echo3 none) ∈ σ.sent := by
        intro g ⟨⟨m, hm, hm3⟩, hgb⟩
        have hsent := h.genuine hm hgb
        rcases m with _ | _ | (_ | u) | _ | _ <;> try exact hm3.elim
        · exact hsent
        · exact absurd hsent (hex g u)
      have hS : S ⊆ G ∪ σ.bad := fun r hr => by
        by_cases hrb : r ∈ σ.bad
        · exact Or.inr hrb
        · exact Or.inl ⟨hr, hrb⟩
      have e1 := (Set.ncard_le_ncard hS).trans (Set.ncard_union_le _ _)
      have e6 : Fintype.card P - t ≤ S.ncard := h3
      obtain ⟨r, hr⟩ := echo4_of_hasVal ht h' hq hg
      exact no_echo3_quorum ht h (G := G) (fun g hg => hg.2) hGs (by omega) hσ' r _
        (just h' hr).1
    · obtain ⟨r, hr⟩ := echo3_of_echo4 ht h hs₂
      exact hex r v hr

/-! ### Number of broadcasts -/

/-- Every party broadcasts at most 6 messages (two `echo`, one each of `echo2` … `echo5`): the
content of "terminates in at most 6 communication rounds" (Theorem 5.3). -/
theorem out_ncard_le_six (h : Reachable (alg t) x k t σ) (p : P) : (σ.out p).ncard ≤ 6 := by
  classical
  let w0 : Bool := if hw : ∃ w, (p, Msg.echo2 w) ∈ σ.sent then hw.choose else true
  let o3 : Option Bool := if ho : ∃ o, (p, Msg.echo3 o) ∈ σ.sent then ho.choose else none
  let o4 : Option Bool := if ho : ∃ o, (p, Msg.echo4 o) ∈ σ.sent then ho.choose else none
  let o5 : Option Bool := if ho : ∃ o, (p, Msg.echo5 o) ∈ σ.sent then ho.choose else none
  have hsub : σ.out p ⊆
      {.echo true, .echo false, .echo2 w0, .echo3 o3, .echo4 o4, .echo5 o5} := by
    intro m hm
    rcases m with v | v | o | o | o
    · cases v <;> simp
    · have hw : ∃ w, (p, Msg.echo2 w) ∈ σ.sent := ⟨v, hm⟩
      have : v = w0 := by
        simp only [w0, dite_eq_left_of_eq_true (eq_true hw)]
        exact echo2_unique (isEchoLayer t) h hm hw.choose_spec
      simp [this]
    · have ho : ∃ o, (p, Msg.echo3 o) ∈ σ.sent := ⟨o, hm⟩
      have : o = o3 := by
        simp only [o3, dite_eq_left_of_eq_true (eq_true ho)]
        exact echo3_unique h hm ho.choose_spec
      simp [this]
    · have ho : ∃ o, (p, Msg.echo4 o) ∈ σ.sent := ⟨o, hm⟩
      have : o = o4 := by
        simp only [o4, dite_eq_left_of_eq_true (eq_true ho)]
        exact echo4_unique h hm ho.choose_spec
      simp [this]
    · have ho : ∃ o, (p, Msg.echo5 o) ∈ σ.sent := ⟨o, hm⟩
      have : o = o5 := by
        simp only [o5, dite_eq_left_of_eq_true (eq_true ho)]
        exact echo5_unique h hm ho.choose_spec
      simp [this]
  refine (Set.ncard_le_ncard hsub).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
  simp


/-! ### Termination -/

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
  · obtain ⟨s₁, s₂, i₁, i₂, w, -, -, h₁, h₂⟩ := hmix
    obtain ⟨j₁, hj₁⟩ := Exec.approved_spread hA E hF ht
      (echo2_approved hA (E.reachable i₁) h₁) hq
    obtain ⟨j₂, hj₂⟩ := Exec.approved_spread hA E hF ht
      (echo2_approved hA (E.reachable i₂) h₂) hq
    obtain ⟨j₃, hj₃⟩ := E.eventually_rcv_all' hF (S := {s | E.Correct s}) (fun s hs => hs)
      (φ := Msg.IsEcho2) (fun s hs => by
        obtain ⟨i, w, hi⟩ := Exec.eventually_echo2 hA E hF ht hs
        exact ⟨i, .echo2 w, trivial, hi⟩) hq
    obtain ⟨j, m', hm', hj⟩ := E.eventually_sent hF hq (φ := Msg.IsEcho3) (m := .echo3 none)
      trivial (i := max (max j₁ j₂) j₃) fun j hij hno =>
        ⟨⟨(E.card_sub_le_ncard_correct).trans (le_cntP fun s hs => by
            obtain ⟨m, hm2, hm⟩ := hj₃ s hs
            exact ⟨m, E.rcv_mono (by omega) hm, hm2⟩),
          bothApproved_of_ne (by cases w <;> simp) (hj₁ j (by omega)) (hj₂ j (by omega))⟩,
        fun o ho => hno (.echo3 o) trivial ho⟩
    rcases m' with _ | _ | o | _ | _ <;> try exact hm'.elim
    exact ⟨j, o, hj⟩
  · push Not at hmix
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
    rcases m' with _ | _ | o | _ | _ <;> try exact hm'.elim
    exact ⟨j', o, hj'⟩

/-- One "wait until" level (`echo4` after `echo3`, `echo5` after `echo4`): if every correct party
broadcasts a message of the previous level, these are consistent, and `⊥` there implies
`|approvedVals| > 1`, then every correct party broadcasts a message of the next level. -/
theorem stage (ht : 3 * t < Fintype.card P) (prev cur : Option Bool → Msg)
    (φp φc : Msg → Prop) (hφp : ∀ o, φp (prev o)) (hφc : ∀ o, φc (cur o))
    (hall : ∀ s, E.Correct s → ∃ i o, (s, prev o) ∈ (E.σ i).sent)
    (hcons : ∀ i s s' v w, (s, prev (some v)) ∈ (E.σ i).sent →
      (s', prev (some w)) ∈ (E.σ i).sent → v = w)
    (hnone : ∀ i s, (s, prev none) ∈ (E.σ i).sent → BothApproved t ((E.σ i).inbox s))
    {q : P} (hq : E.Correct q)
    (hsome : ∀ j v, Fintype.card P - t ≤ cnt ((E.σ j).inbox q) (prev (some v)) →
      (∃ o, (q, prev o) ∈ (E.σ j).sent) → (∀ m, φc m → (q, m) ∉ (E.σ j).sent) →
      (alg t).send q (x q) ((E.σ j).inbox q) ((E.σ j).out q) (cur (some v)))
    (hbot : ∀ j, Fintype.card P - t ≤ cntP ((E.σ j).inbox q) φp →
      BothApproved t ((E.σ j).inbox q) → (∃ o, (q, prev o) ∈ (E.σ j).sent) →
      (∀ m, φc m → (q, m) ∉ (E.σ j).sent) →
      (alg t).send q (x q) ((E.σ j).inbox q) ((E.σ j).out q) (cur none)) :
    ∃ i m, φc m ∧ (q, m) ∈ (E.σ i).sent := by
  have hA := isEchoLayer (P := P) t
  obtain ⟨iq, oq, hiq⟩ := hall q hq
  by_cases hb : ∃ s i, E.Correct s ∧ (s, prev none) ∈ (E.σ i).sent
  · obtain ⟨s, i, -, hs⟩ := hb
    have hboth := hnone i s hs
    obtain ⟨j₁, hj₁⟩ := Exec.approved_spread hA E hF ht hboth.1 hq
    obtain ⟨j₂, hj₂⟩ := Exec.approved_spread hA E hF ht hboth.2 hq
    obtain ⟨j₃, hj₃⟩ := E.eventually_rcv_all' hF (S := {s | E.Correct s}) (fun s hs => hs)
      (φ := φp) (fun s hs => by
        obtain ⟨i, o, hi⟩ := hall s hs
        exact ⟨i, prev o, hφp o, hi⟩) hq
    exact E.eventually_sent hF hq (φ := φc) (m := cur none) (hφc none)
      (i := max (max j₁ j₂) (max j₃ iq)) fun j hij hno =>
        hbot j ((E.card_sub_le_ncard_correct).trans (le_cntP fun s hs => by
            obtain ⟨m, hm2, hm⟩ := hj₃ s hs
            exact ⟨m, E.rcv_mono (by omega) hm, hm2⟩))
          ⟨hj₁ j (by omega), hj₂ j (by omega)⟩ ⟨oq, E.sent_mono (by omega) hiq⟩ hno
  · push Not at hb
    obtain ⟨w, rfl⟩ : ∃ w, oq = some w := by
      cases oq with
      | none => exact absurd hiq (hb q iq hq)
      | some w => exact ⟨w, rfl⟩
    have hall' : ∀ s ∈ {s | E.Correct s}, ∃ i, (s, prev (some w)) ∈ (E.σ i).sent := by
      intro s hs
      obtain ⟨i, o, hi⟩ := hall s hs
      cases o with
      | none => exact absurd hi (hb s i hs)
      | some w' =>
        refine ⟨i, ?_⟩
        have := hcons (max i iq) _ _ _ _ (E.sent_mono (le_max_left _ _) hi)
          (E.sent_mono (le_max_right _ _) hiq)
        rwa [this] at hi
    obtain ⟨j, hj⟩ := E.eventually_rcv_all hF (fun s hs => hs) (m := fun _ => prev (some w))
      hall' hq
    exact E.eventually_sent hF hq (φ := φc) (m := cur (some w)) (hφc _) (i := max j iq)
      fun j' hij hno => hsome j' w ((E.card_sub_le_ncard_correct).trans
        (le_cnt fun s hs => E.rcv_mono (le_of_max_le_left hij) (hj s hs)))
        ⟨some w, E.sent_mono (le_of_max_le_right hij) hiq⟩ hno

/-- Every correct party eventually broadcasts an `echo4` message. -/
theorem eventually_echo4 (ht : 3 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i o, (q, Msg.echo4 o) ∈ (E.σ i).sent := by
  obtain ⟨i, m, hm, hi⟩ := stage E hF ht Msg.echo3 Msg.echo4 Msg.IsEcho3 Msg.IsEcho4
    (fun _ => trivial) (fun _ => trivial) (fun s hs => eventually_echo3 E hF ht hs)
    (fun i _ _ _ _ h1 h2 => echo3_consistent ht (E.reachable i) h1 h2)
    (fun i _ hs => (just (E.reachable i) hs).2) hq
    (fun _ _ hc h3 hno => ⟨⟨hc, h3⟩, fun o ho => hno (.echo4 o) trivial ho⟩)
    (fun _ hc hb h3 hno => ⟨⟨hc, hb, h3⟩, fun o ho => hno (.echo4 o) trivial ho⟩)
  rcases m with _ | _ | _ | o | _ <;> try exact hm.elim
  exact ⟨i, o, hi⟩

/-- Every correct party eventually broadcasts an `echo5` message. -/
theorem eventually_echo5 (ht : 3 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i o, (q, Msg.echo5 o) ∈ (E.σ i).sent := by
  obtain ⟨i, m, hm, hi⟩ := stage E hF ht Msg.echo4 Msg.echo5 Msg.IsEcho4 Msg.IsEcho5
    (fun _ => trivial) (fun _ => trivial) (fun s hs => eventually_echo4 E hF ht hs)
    (fun i _ _ _ _ h1 h2 => echo4_consistent ht (E.reachable i) h1 h2)
    (fun i _ hs => (just (E.reachable i) hs).2.1) hq
    (fun _ _ hc h4 hno => ⟨⟨hc, h4⟩, fun o ho => hno (.echo5 o) trivial ho⟩)
    (fun _ hc hb h4 hno => ⟨⟨hc, hb, h4⟩, fun o ho => hno (.echo5 o) trivial ho⟩)
  rcases m with _ | _ | _ | _ | o <;> try exact hm.elim
  exact ⟨i, o, hi⟩

/-- Theorem 5.3 (Termination): in every fair execution every correct party decides. -/
theorem termination (ht : 3 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i, (E.σ i).dec q ≠ none := by
  have hA := isEchoLayer (P := P) t
  obtain ⟨iq, oq, hiq⟩ := eventually_echo5 E hF ht hq
  by_cases hb : ∃ s i, E.Correct s ∧ (s, Msg.echo5 none) ∈ (E.σ i).sent
  · obtain ⟨s, i, -, hs⟩ := hb
    have hboth := (just (E.reachable i) hs).2.1
    obtain ⟨j₁, hj₁⟩ := Exec.approved_spread hA E hF ht hboth.1 hq
    obtain ⟨j₂, hj₂⟩ := Exec.approved_spread hA E hF ht hboth.2 hq
    by_cases hv : ∃ s i w, E.Correct s ∧ (s, Msg.echo5 (some w)) ∈ (E.σ i).sent
    · -- decide `w` grade 1
      obtain ⟨s', i', w, hs'c, hs'⟩ := hv
      have h4 : Fintype.card P - t ≤ cnt ((E.σ i').inbox s') (.echo4 (some w)) :=
        (just (E.reachable i') hs').1
      let T := {r | Msg.echo4 (some w) ∈ (E.σ i').inbox s' r} ∩ {r | E.Correct r}
      have hT : t + 1 ≤ T.ncard := by
        show t + 1 ≤ ({r | Msg.echo4 (some w) ∈ (E.σ i').inbox s' r} ∩ {r | E.Correct r}).ncard
        have := E.ncard_le_ncard_inter_correct_add {r | Msg.echo4 (some w) ∈ (E.σ i').inbox s' r}
        unfold cnt at h4
        omega
      obtain ⟨j₄, hj₄⟩ := E.eventually_rcv_all hF (S := T) (fun r hr => hr.2)
        (m := fun _ => .echo4 (some w))
        (fun r hr => ⟨i', (E.reachable i').genuine hr.1 (hr.2 i')⟩) hq
      obtain ⟨j₅, hj₅⟩ := hF.deliver q s' _ i' hq hs'c hs'
      obtain ⟨j₆, hj₆⟩ := E.eventually_rcv_all' hF (S := {s | E.Correct s}) (fun s hs => hs)
        (φ := Msg.IsEcho5) (fun s hs => by
          obtain ⟨i, o, hi⟩ := eventually_echo5 E hF ht hs
          exact ⟨i, .echo5 o, trivial, hi⟩) hq
      refine E.eventually_dec hF hq (o := .one w)
        (i := max (max (max j₁ j₂) (max j₄ j₅)) (max j₆ iq)) fun j hij _ => ⟨?_, ?_, ?_,
          ⟨hj₁ j (by omega), hj₂ j (by omega)⟩, ⟨oq, E.sent_mono (by omega) hiq⟩⟩
      · exact (E.card_sub_le_ncard_correct).trans (le_cntP fun s hs => by
          obtain ⟨m, hm2, hm⟩ := hj₆ s hs
          exact ⟨m, E.rcv_mono (by omega) hm, hm2⟩)
      · have : ({s'} : Set P).ncard ≤ cnt ((E.σ j).inbox q) (.echo5 (some w)) :=
          le_cnt fun r hr => by
            rw [Set.mem_singleton_iff] at hr
            subst hr
            exact E.rcv_mono (by omega) hj₅
        simpa using this
      · exact hT.trans (le_cnt fun r hr => E.rcv_mono (by omega) (hj₄ r hr))
    · -- all correct parties sent `⟨echo5, ⊥⟩`: decide `⊥` grade 0
      push Not at hv
      have hall : ∀ s ∈ {s | E.Correct s}, ∃ i, (s, Msg.echo5 none) ∈ (E.σ i).sent := by
        intro s hs
        obtain ⟨i, o, hi⟩ := eventually_echo5 E hF ht hs
        cases o with
        | none => exact ⟨i, hi⟩
        | some w => exact absurd hi (hv s i w hs)
      obtain ⟨j₃, hj₃⟩ := E.eventually_rcv_all hF (fun s hs => hs) (m := fun _ => .echo5 none)
        hall hq
      exact E.eventually_dec hF hq (o := .zero) (i := max (max j₁ j₂) (max j₃ iq))
        fun j hij _ => ⟨(E.card_sub_le_ncard_correct).trans
          (le_cnt fun s hs => E.rcv_mono (by omega) (hj₃ s hs)),
          ⟨hj₁ j (by omega), hj₂ j (by omega)⟩, ⟨oq, E.sent_mono (by omega) hiq⟩⟩
  · -- all correct parties sent `⟨echo5, w⟩` for one `w`: decide `w` grade 2
    push Not at hb
    obtain ⟨w, rfl⟩ : ∃ w, oq = some w := by
      cases oq with
      | none => exact absurd hiq (hb q iq hq)
      | some w => exact ⟨w, rfl⟩
    have hall : ∀ s ∈ {s | E.Correct s}, ∃ i, (s, Msg.echo5 (some w)) ∈ (E.σ i).sent := by
      intro s hs
      obtain ⟨i, o, hi⟩ := eventually_echo5 E hF ht hs
      cases o with
      | none => exact absurd hi (hb s i hs)
      | some w' =>
        refine ⟨i, ?_⟩
        have := echo5_consistent ht (E.reachable (max i iq)) (E.sent_mono (le_max_left _ _) hi)
          (E.sent_mono (le_max_right _ _) hiq)
        rwa [this] at hi
    obtain ⟨j, hj⟩ := E.eventually_rcv_all hF (fun s hs => hs) (m := fun _ => .echo5 (some w))
      hall hq
    exact E.eventually_dec hF hq (o := .two w) (i := max j iq) fun j' hij _ =>
      ⟨(E.card_sub_le_ncard_correct).trans
        (le_cnt fun s hs => E.rcv_mono (le_of_max_le_left hij) (hj s hs)),
        ⟨some w, E.sent_mono (le_of_max_le_right hij) hiq⟩⟩

end Termination

/-- Theorem 5.3 (Algorithm 6 implements GBCA, Definition 3.2): graded agreement, validity,
graded binding, termination and at most 6 broadcasts per party, for `n ≥ 3t + 1` and an
adaptive Byzantine adversary. -/
theorem theorem_5_3 (ht : 3 * t < Fintype.card P) :
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ p q g g' v w, σ.dec p = some g →
      σ.dec q = some g' → g.HasVal v → g'.HasVal w → v = w) ∧
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ p q v, σ.dec p = some (.two v) →
      σ.dec q ≠ some .zero) ∧
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ (H : Set P) v, σ.bad ⊆ Hᶜ → Hᶜ.ncard ≤ t →
      (∀ p ∈ H, x p = v) → ∀ p, σ.dec p = none ∨ σ.dec p = some (.two v)) ∧
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ p, σ.dec p ≠ none →
      ∃ b : Bool, ∀ σ', Reach (alg t) x .byzantine t σ σ' →
        ∀ q g, σ'.dec q = some g → ¬ g.HasVal (!b)) ∧
    (∀ E : Exec (alg t) x .byzantine t, E.Fair → ∀ q, E.Correct q → ∃ i, (E.σ i).dec q ≠ none) ∧
    (∀ σ, Reachable (alg t) x .byzantine t σ → ∀ p, (σ.out p).ncard ≤ 6) :=
  ⟨fun _ h _ _ _ _ _ _ hp hq hg hg' => graded_agreement ht h hp hq hg hg',
   fun _ h _ _ _ hp => graded_agreement_zero ht h hp,
   fun _ h _ _ hbad hH hx p => validity ht h hbad hH hx p,
   fun _ h _ hp => graded_binding ht h hp,
   fun E hF _ hq => termination E hF ht hq,
   fun _ h p => out_ncard_le_six h p⟩

end Podc.BindingCrusaderAgreement.Alg6
