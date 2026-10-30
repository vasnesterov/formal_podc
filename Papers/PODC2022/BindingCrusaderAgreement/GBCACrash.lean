import Papers.PODC2022.BindingCrusaderAgreement.BCACrash

/-!
# Algorithm 5: Graded Binding Crusader Agreement with crash faults (`GBCA_Crash`)

Abraham, Ben-David, Yandamuri, PODC 2022, Section 5.1, Algorithm 5, Theorem 5.1 (proof deferred to
the full version in the paper; we give our own). See `BCACrash.lean` for the shared `val`/`echo`
layer and the modelling conventions.

Line 9 of Algorithm 5 ("if all of the messages contain the same value `v` then decide `v, 2`")
read literally also covers "all `⊥`"; the text says that then the party decides `⊥` (grade 0),
which is what we model (there is no "`⊥` grade 2" bucket in Definition 3.2).
-/

namespace Podc.BindingCrusaderAgreement.Alg5

open Cslib.Byzantine.AsyncBroadcast Podc.BindingCrusaderAgreement

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Broadcast guards of Algorithm 5. -/
def sendG (t : ℕ) (x : Bool) (ib : P → Set CMsg) (out : Set CMsg) : CMsg → Prop
  | .val v => v = x
  | .echo (some v) => Fintype.card P - t ≤ cnt ib (.val v) ∧ ∀ o, .echo o ∉ out
  | .echo none => Fintype.card P - t ≤ cntP ib CMsg.IsVal ∧ 0 < cnt ib (.val true) ∧
      0 < cnt ib (.val false) ∧ ∀ o, .echo o ∉ out
  | .echo2 (some v) => Fintype.card P - t ≤ cnt ib (.echo (some v)) ∧ ∀ o, .echo2 o ∉ out
  | .echo2 none => Mixed t ib CMsg.IsEcho CMsg.echo ∧ ∀ o, .echo2 o ∉ out

/-- Decision guards of Algorithm 5 (lines 8–11). -/
def decideG (t : ℕ) (ib : P → Set CMsg) : Grade → Prop
  | .two v => Fintype.card P - t ≤ cnt ib (.echo2 (some v))
  | .one v => Fintype.card P - t ≤ cntP ib CMsg.IsEcho2 ∧ 0 < cnt ib (.echo2 (some v)) ∧
      (0 < cnt ib (.echo2 none) ∨ 0 < cnt ib (.echo2 (some (!v))))
  | .zero => Fintype.card P - t ≤ cnt ib (.echo2 none)

/-- Algorithm 5. -/
def alg (t : ℕ) : Protocol P CMsg Bool Grade where
  send _ x ib out m := sendG t x ib out m
  decide _ _ ib _ g := decideG t ib g

omit [DecidableEq P] in
theorem isValLayer (t : ℕ) : IsValLayer t (alg (P := P) t) :=
  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

variable {t : ℕ} {x : P → Bool} {σ : State P CMsg Grade}

theorem dec_just (h : Reachable (alg t) x .crash t σ) {p : P} {g : Grade}
    (hd : σ.dec p = some g) : decideG t (σ.inbox p) g := by
  refine h.dec_just (J := fun _ g ib _ => decideG t ib g) ?_ (fun _ _ _ _ hs => hs) hd
  intro _ g _ _ _ _ hib _ hj
  rcases g with v | v | _
  · exact (show Fintype.card P - t ≤ _ from hj).trans (cnt_mono hib _)
  · exact ⟨hj.1.trans (cntP_mono hib _), lt_of_lt_of_le hj.2.1 (cnt_mono hib _),
      hj.2.2.imp (fun h1 => lt_of_lt_of_le h1 (cnt_mono hib _))
        (fun h1 => lt_of_lt_of_le h1 (cnt_mono hib _))⟩
  · exact (show Fintype.card P - t ≤ _ from hj).trans (cnt_mono hib _)

theorem echo2_some_just (h : Reachable (alg t) x .crash t σ) {p : P} {v : Bool}
    (hm : (p, .echo2 (some v)) ∈ σ.sent) :
    Fintype.card P - t ≤ cnt (σ.inbox p) (.echo (some v)) := by
  refine h.sent_just (J := fun _ m ib _ => ∀ v, m = .echo2 (some v) →
    Fintype.card P - t ≤ cnt ib (.echo (some v))) ?_ ?_ hm v rfl
  · intro _ _ _ _ _ _ hib _ hj v hv; exact (hj v hv).trans (cnt_mono hib _)
  · intro p ib out m hs v hv
    subst hv
    exact hs.1

theorem echo2_none_just (h : Reachable (alg t) x .crash t σ) {p : P}
    (hm : (p, .echo2 none) ∈ σ.sent) : Mixed t (σ.inbox p) CMsg.IsEcho CMsg.echo := by
  refine h.sent_just (J := fun _ m ib _ => m = .echo2 none →
    Mixed t ib CMsg.IsEcho CMsg.echo) ?_ ?_ hm rfl
  · intro _ _ _ _ _ _ hib _ hj hv; exact (hj hv).mono hib
  · intro p ib out m hs hv
    subst hv
    exact hs.1

theorem echo2_unique (h : Reachable (alg t) x .crash t σ) {p : P} {o o' : Option Bool}
    (hv : (p, .echo2 o) ∈ σ.sent) (hw : (p, .echo2 o') ∈ σ.sent) : o = o' := by
  have := h.sent_excl CMsg.IsEcho2 ?_ hv hw trivial trivial
  · simpa using this
  · intro p ib out m hs hm m' hm' h2
    rcases m with _ | _ | (_ | v) <;> try exact hm.elim
    all_goals rcases m' with _ | _ | o' <;> try exact h2.elim
    · exact hs.2 o' hm'
    · exact hs.2 o' hm'

/-- Every broadcast `⟨echo2, v⟩` (`v ≠ ⊥`) needs an `⟨echo, v⟩` broadcast. -/
theorem echo_of_echo2 (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ)
    {r : P} {v : Bool} (hr : (r, .echo2 (some v)) ∈ σ.sent) :
    ∃ r', (r', .echo (some v)) ∈ σ.sent :=
  ValLayer.exists_sent ht h (ValLayer.pos_of_quorum ht (echo2_some_just h hr))

theorem echo2_consistent (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ)
    {s s' : P} {v w : Bool} (hv : (s, .echo2 (some v)) ∈ σ.sent)
    (hw : (s', .echo2 (some w)) ∈ σ.sent) : v = w := by
  obtain ⟨r, hr⟩ := echo_of_echo2 ht h hv
  obtain ⟨r', hr'⟩ := echo_of_echo2 ht h hw
  exact ValLayer.echo_consistent (isValLayer t) ht h hr hr'

/-- A decision `v` with grade `≥ 1` needs an `⟨echo2, v⟩` broadcast. -/
theorem echo2_of_hasVal (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ)
    {q : P} {g : Grade} {v : Bool} (hq : σ.dec q = some g) (hg : g.HasVal v) :
    ∃ r, (r, .echo2 (some v)) ∈ σ.sent := by
  have hd := dec_just h hq
  rcases hg with rfl | rfl
  · exact ValLayer.exists_sent ht h (ValLayer.pos_of_quorum ht hd)
  · exact ValLayer.exists_sent ht h hd.2.1

/-- Graded Agreement (Definition 3.2, crash version, all parties), first part. -/
theorem graded_agreement (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ)
    {p q : P} {g g' : Grade} {v w : Bool} (hp : σ.dec p = some g) (hq : σ.dec q = some g')
    (hgv : g.HasVal v) (hgw : g'.HasVal w) : v = w := by
  obtain ⟨r, hr⟩ := echo2_of_hasVal ht h hp hgv
  obtain ⟨r', hr'⟩ := echo2_of_hasVal ht h hq hgw
  exact echo2_consistent ht h hr hr'

/-- Graded Agreement, second part: `v` grade 2 excludes `⊥` grade 0. -/
theorem graded_agreement_zero (ht : 2 * t < Fintype.card P)
    (h : Reachable (alg t) x .crash t σ) {p q : P} {v : Bool} (hp : σ.dec p = some (.two v)) :
    σ.dec q ≠ some .zero := by
  intro hq
  obtain ⟨r, h1, h2⟩ := ValLayer.exists_common ht (dec_just h hp) (dec_just h hq)
  simpa using echo2_unique h (h.genuine_crash h1) (h.genuine_crash h2)

/-- Weak validity: if all parties have input `v`, every decision is `v` grade 2. -/
theorem weak_validity (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ)
    {v : Bool} (hx : ∀ p, x p = v) (p : P) : σ.dec p = none ∨ σ.dec p = some (.two v) := by
  have hA := isValLayer (P := P) t
  -- every broadcast `echo` carries `v`, hence every broadcast `echo2` carries `v`
  have hecho : ∀ (q : P) (o : Option Bool), 0 < cnt (σ.inbox q) (.echo o) → o = some v :=
    fun q o hc => by
      obtain ⟨r, hr⟩ := ValLayer.exists_sent ht h hc
      exact ValLayer.echo_of_inputs hA ht h hx hr
  have hecho2 : ∀ (q : P) (o : Option Bool), 0 < cnt (σ.inbox q) (.echo2 o) → o = some v :=
    fun q o hc => by
      obtain ⟨r, hr⟩ := ValLayer.exists_sent ht h hc
      rcases o with _ | w
      · rcases (echo2_none_just h hr).2 with h1 | ⟨h1, h2⟩
        · exact absurd (hecho r _ h1) (by simp)
        · have e1 := hecho r _ h1
          have e2 := hecho r _ h2
          simp only [Option.some.injEq] at e1 e2
          exact absurd (e1.trans e2.symm) (by simp)
      · exact hecho r _ (ValLayer.pos_of_quorum ht (echo2_some_just h hr))
  rcases hd : σ.dec p with _ | g
  · exact Or.inl rfl
  right
  have hj := dec_just h hd
  rcases g with w | w | _
  · have := hecho2 p _ (ValLayer.pos_of_quorum ht hj)
    simp only [Option.some.injEq] at this
    rw [this]
  · have e1 := hecho2 p _ hj.2.1
    rcases hj.2.2 with h2 | h2
    · exact absurd (hecho2 p _ h2) (by simp)
    · have e2 := hecho2 p _ h2
      simp only [Option.some.injEq] at e1 e2
      rw [e1] at e2
      cases v <;> simp at e2
  · exact absurd (hecho2 p _ (ValLayer.pos_of_quorum ht hj)) (by simp)

/-- Graded Binding (Definition 3.2, crash version): once some party has decided, there is `b`
such that no party decides `1 − b` with grade `≥ 1` in any extension. -/
theorem graded_binding (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ)
    {p : P} (hp : σ.dec p ≠ none) : ∃ b : Bool, ∀ σ', Reach (alg t) x .crash t σ σ' →
      ∀ q g, σ'.dec q = some g → ¬ g.HasVal (!b) := by
  have hA := isValLayer (P := P) t
  by_cases hex : ∃ s u, (s, CMsg.echo (some u)) ∈ σ.sent
  · obtain ⟨s, u, hs⟩ := hex
    refine ⟨u, fun σ' hσ' q g hq hg => ?_⟩
    have h' := h.reach hσ'
    obtain ⟨r, hr⟩ := echo2_of_hasVal ht h' hq hg
    obtain ⟨r', hr'⟩ := echo_of_echo2 ht h' hr
    have := ValLayer.echo_consistent hA ht h' (hσ'.sent_subset hs) hr'
    cases u <;> simp at this
  · push Not at hex
    refine ⟨true, fun σ' hσ' q g hq hg => ?_⟩
    have h' := h.reach hσ'
    obtain ⟨g₀, hg₀⟩ := Option.ne_none_iff_exists'.1 hp
    have h2 : Fintype.card P - t ≤ cntP (σ.inbox p) CMsg.IsEcho2 := by
      have hj := dec_just h hg₀
      rcases g₀ with v | v | _
      · exact (show Fintype.card P - t ≤ _ from hj).trans (cnt_le_cntP trivial)
      · exact hj.1
      · exact (show Fintype.card P - t ≤ _ from hj).trans (cnt_le_cntP trivial)
    obtain ⟨s₁, ⟨m₁, hm₁, hm₁2⟩⟩ := Set.nonempty_of_ncard_ne_zero
      (s := {s | ∃ m ∈ σ.inbox p s, CMsg.IsEcho2 m}) (by unfold cntP at h2; omega)
    have hs₁ := h.genuine_crash hm₁
    have h1 : Fintype.card P - t ≤ cntP (σ.inbox s₁) CMsg.IsEcho := by
      rcases m₁ with _ | _ | (_ | v) <;> try exact hm₁2.elim
      · exact (echo2_none_just h hs₁).1
      · exact (echo2_some_just h hs₁).trans (cnt_le_cntP trivial)
    obtain ⟨r, hr⟩ := echo2_of_hasVal ht h' hq hg
    obtain ⟨r', ⟨m, hm, hm1⟩, hr'2⟩ := ValLayer.exists_common ht h1 (echo2_some_just h' hr)
    rcases m with _ | (_ | u) | _ <;> try exact hm1.elim
    · have := ValLayer.echo_unique hA h' (hσ'.sent_subset (h.genuine_crash hm))
        (h'.genuine_crash hr'2)
      simp at this
    · exact hex r' u (h.genuine_crash hm)

/-- Every party broadcasts at most 3 messages (`val`, `echo`, `echo2`): "terminates in at most 3
communication rounds" (Theorem 5.1). -/
theorem out_ncard_le_three (h : Reachable (alg t) x .crash t σ) (p : P) :
    (σ.out p).ncard ≤ 3 := by
  classical
  have hA := isValLayer (P := P) t
  let o1 : Option Bool := if ho : ∃ o, (p, CMsg.echo o) ∈ σ.sent then ho.choose else none
  let o2 : Option Bool := if ho : ∃ o, (p, CMsg.echo2 o) ∈ σ.sent then ho.choose else none
  have hsub : σ.out p ⊆ {.val (x p), .echo o1, .echo2 o2} := by
    intro m hm
    rcases m with v | o | o
    · simp [ValLayer.val_just hA h hm]
    · have ho : ∃ o, (p, CMsg.echo o) ∈ σ.sent := ⟨o, hm⟩
      have : o = o1 := by
        simp only [o1, dite_eq_left_of_eq_true (eq_true ho)]
        exact ValLayer.echo_unique hA h hm ho.choose_spec
      simp [this]
    · have ho : ∃ o, (p, CMsg.echo2 o) ∈ σ.sent := ⟨o, hm⟩
      have : o = o2 := by
        simp only [o2, dite_eq_left_of_eq_true (eq_true ho)]
        exact echo2_unique h hm ho.choose_spec
      simp [this]
  refine (Set.ncard_le_ncard hsub).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
  simp

section Termination

variable (E : Exec (alg t) x .crash t) (hF : E.Fair)
include hF

omit hF in
theorem singleton_le_cnt {s q : P} {m : CMsg} {i j : ℕ} (hij : i ≤ j)
    (h : (q, s, m) ∈ (E.σ i).rcv) : 0 < cnt ((E.σ j).inbox q) m := by
  have : ({s} : Set P).ncard ≤ cnt ((E.σ j).inbox q) m := le_cnt fun r hr => by
    rw [Set.mem_singleton_iff] at hr; subst hr; exact E.rcv_mono hij h
  simp at this; omega

/-- Every correct party eventually broadcasts an `echo2`. -/
theorem eventually_echo2 (ht : 2 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i o, (q, CMsg.echo2 o) ∈ (E.σ i).sent := by
  have hA := isValLayer (P := P) t
  have hc := E.card_sub_le_ncard_correct
  obtain ⟨iq, oq, hiq⟩ := ValLayer.eventually_echo hA E hF ht hq
  by_cases hb : ∃ s i, E.Correct s ∧ (s, CMsg.echo none) ∈ (E.σ i).sent
  · obtain ⟨s, i, hs, hsi⟩ := hb
    obtain ⟨j', hj'⟩ := hF.deliver q s _ i hq hs hsi
    obtain ⟨j, hj⟩ := E.eventually_rcv_all' hF (S := {s | E.Correct s}) (fun s hs => hs)
      (φ := CMsg.IsEcho) (fun s hs => by
        obtain ⟨i, o, hi⟩ := ValLayer.eventually_echo hA E hF ht hs
        exact ⟨i, .echo o, trivial, hi⟩) hq
    obtain ⟨i₂, m', hm', hi₂⟩ := E.eventually_sent hF hq (φ := CMsg.IsEcho2) (m := .echo2 none)
      trivial (i := max j j') fun j₂ hij hno =>
        ⟨⟨hc.trans (le_cntP fun s hs => by
            obtain ⟨m, hm2, hm⟩ := hj s hs
            exact ⟨m, E.rcv_mono (le_of_max_le_left hij) hm, hm2⟩),
          Or.inl (singleton_le_cnt E (le_of_max_le_right hij) hj')⟩,
          fun o ho => hno (.echo2 o) trivial ho⟩
    rcases m' with _ | _ | o <;> try exact hm'.elim
    exact ⟨i₂, o, hi₂⟩
  · push Not at hb
    obtain ⟨w, rfl⟩ : ∃ w, oq = some w := by
      cases oq with
      | none => exact absurd hiq (hb q iq hq)
      | some w => exact ⟨w, rfl⟩
    have hall : ∀ s ∈ {s | E.Correct s}, ∃ i, (s, CMsg.echo (some w)) ∈ (E.σ i).sent := by
      intro s hs
      obtain ⟨i, o, hi⟩ := ValLayer.eventually_echo hA E hF ht hs
      cases o with
      | none => exact absurd hi (hb s i hs)
      | some w' =>
        refine ⟨i, ?_⟩
        have := ValLayer.echo_consistent hA ht (E.reachable (max i iq))
          (E.sent_mono (le_max_left _ _) hi) (E.sent_mono (le_max_right _ _) hiq)
        rwa [this] at hi
    obtain ⟨j₁, hj₁⟩ := E.eventually_rcv_all hF (fun s hs => hs) (m := fun _ => .echo (some w))
      hall hq
    obtain ⟨i₂, m', hm', hi₂⟩ := E.eventually_sent hF hq (φ := CMsg.IsEcho2)
      (m := .echo2 (some w)) trivial (i := j₁) fun j₂ hij hno =>
        ⟨hc.trans (le_cnt fun s hs => E.rcv_mono hij (hj₁ s hs)),
          fun o ho => hno (.echo2 o) trivial ho⟩
    rcases m' with _ | _ | o <;> try exact hm'.elim
    exact ⟨i₂, o, hi₂⟩

/-- Termination: in every fair execution every correct party decides. -/
theorem termination (ht : 2 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i, (E.σ i).dec q ≠ none := by
  have hc := E.card_sub_le_ncard_correct
  obtain ⟨iq, oq, hiq⟩ := eventually_echo2 E hF ht hq
  obtain ⟨j, hj⟩ := E.eventually_rcv_all' hF (S := {s | E.Correct s}) (fun s hs => hs)
    (φ := CMsg.IsEcho2) (fun s hs => by
      obtain ⟨i, o, hi⟩ := eventually_echo2 E hF ht hs
      exact ⟨i, .echo2 o, trivial, hi⟩) hq
  have hall2 : ∀ j', j ≤ j' → Fintype.card P - t ≤ cntP ((E.σ j').inbox q) CMsg.IsEcho2 :=
    fun j' hij => hc.trans (le_cntP fun s hs => by
      obtain ⟨m, hm2, hm⟩ := hj s hs
      exact ⟨m, E.rcv_mono hij hm, hm2⟩)
  by_cases hb : ∃ s i, E.Correct s ∧ (s, CMsg.echo2 none) ∈ (E.σ i).sent
  · obtain ⟨s, i, hs, hsi⟩ := hb
    obtain ⟨j', hj'⟩ := hF.deliver q s _ i hq hs hsi
    by_cases hv : ∃ s i w, E.Correct s ∧ (s, CMsg.echo2 (some w)) ∈ (E.σ i).sent
    · obtain ⟨s', i', w, hs', hs'i⟩ := hv
      obtain ⟨j'', hj''⟩ := hF.deliver q s' _ i' hq hs' hs'i
      exact E.eventually_dec hF hq (o := .one w) (i := max j (max j' j'')) fun j₂ hij _ =>
        ⟨hall2 j₂ (by omega), singleton_le_cnt E (by omega) hj'',
          Or.inl (singleton_le_cnt E (by omega) hj')⟩
    · push Not at hv
      have hall : ∀ s ∈ {s | E.Correct s}, ∃ i, (s, CMsg.echo2 none) ∈ (E.σ i).sent := by
        intro s hs
        obtain ⟨i, o, hi⟩ := eventually_echo2 E hF ht hs
        cases o with
        | none => exact ⟨i, hi⟩
        | some w => exact absurd hi (hv s i w hs)
      obtain ⟨j₁, hj₁⟩ := E.eventually_rcv_all hF (fun s hs => hs) (m := fun _ => .echo2 none)
        hall hq
      exact E.eventually_dec hF hq (o := .zero) (i := j₁) fun j₂ hij _ =>
        hc.trans (le_cnt fun s hs => E.rcv_mono hij (hj₁ s hs))
  · push Not at hb
    obtain ⟨w, rfl⟩ : ∃ w, oq = some w := by
      cases oq with
      | none => exact absurd hiq (hb q iq hq)
      | some w => exact ⟨w, rfl⟩
    have hall : ∀ s ∈ {s | E.Correct s}, ∃ i, (s, CMsg.echo2 (some w)) ∈ (E.σ i).sent := by
      intro s hs
      obtain ⟨i, o, hi⟩ := eventually_echo2 E hF ht hs
      cases o with
      | none => exact absurd hi (hb s i hs)
      | some w' =>
        refine ⟨i, ?_⟩
        have := echo2_consistent ht (E.reachable (max i iq)) (E.sent_mono (le_max_left _ _) hi)
          (E.sent_mono (le_max_right _ _) hiq)
        rwa [this] at hi
    obtain ⟨j₁, hj₁⟩ := E.eventually_rcv_all hF (fun s hs => hs) (m := fun _ => .echo2 (some w))
      hall hq
    exact E.eventually_dec hF hq (o := .two w) (i := j₁) fun j₂ hij _ =>
      hc.trans (le_cnt fun s hs => E.rcv_mono hij (hj₁ s hs))

end Termination

/-- Theorem 5.1: Algorithm 5 implements GBCA-Crash (graded agreement and graded binding for all
parties, weak validity, termination) for `n ≥ 2t + 1` crash faults, with at most 3 broadcasts
per party. -/
theorem theorem_5_1 (ht : 2 * t < Fintype.card P) :
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ p q g g' v w, σ.dec p = some g →
      σ.dec q = some g' → g.HasVal v → g'.HasVal w → v = w) ∧
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ p q v, σ.dec p = some (.two v) →
      σ.dec q ≠ some .zero) ∧
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ v, (∀ p, x p = v) →
      ∀ p, σ.dec p = none ∨ σ.dec p = some (.two v)) ∧
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ p, σ.dec p ≠ none →
      ∃ b : Bool, ∀ σ', Reach (alg t) x .crash t σ σ' →
        ∀ q g, σ'.dec q = some g → ¬ g.HasVal (!b)) ∧
    (∀ E : Exec (alg t) x .crash t, E.Fair → ∀ q, E.Correct q → ∃ i, (E.σ i).dec q ≠ none) ∧
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ p, (σ.out p).ncard ≤ 3) :=
  ⟨fun _ h _ _ _ _ _ _ hp hq hg hg' => graded_agreement ht h hp hq hg hg',
   fun _ h _ _ _ hp => graded_agreement_zero ht h hp,
   fun _ h _ hx p => weak_validity ht h hx p,
   fun _ h _ hp => graded_binding ht h hp,
   fun E hF _ hq => termination E hF ht hq,
   fun _ h p => out_ncard_le_three h p⟩

end Podc.BindingCrusaderAgreement.Alg5
