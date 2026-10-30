import Podc.Computability.Distributed.Byzantine.AsyncBroadcast
import Papers.PODC2022.BindingCrusaderAgreement.Basic

/-!
# Algorithms 3 and 5: (Graded) Binding Crusader Agreement with crash faults

Abraham, Ben-David, Yandamuri, PODC 2022, Section 4.1 (Algorithm 3, Theorem 4.1) and
Section 5.1 (Algorithm 5, Theorem 5.1). The proofs are deferred to the full version in the paper;
we give our own.

Both algorithms tolerate `t < n/2` crash faults (adaptive: the adversary crashes parties at any
time, possibly in the middle of a broadcast). They share the first two steps:
* send `⟨val, x⟩`;
* upon `val` from `n − t` parties (and no `echo` sent yet): if they all carry the same `v`, send
  `⟨echo, v⟩`, otherwise `⟨echo, ⊥⟩`.

Algorithm 3 then decides upon `echo` from `n − t` parties: `v` if they all carry `v`, else `⊥`.
Algorithm 5 sends `echo2` in the same way and decides upon `echo2` from `n − t` parties: `v`
grade 2 if they all carry `v ≠ ⊥`, `v` grade 1 if one carries `v ≠ ⊥` and another one a different
value, `⊥` grade 0 if they all carry `⊥`.

"From `n − t` parties, all with `v`" is modelled as "`v` from `n − t` parties", "not all the same"
as "from `n − t` parties, and two different values among the received ones" (liberal guards, see
`Cslib.Byzantine.AsyncBroadcast`).

The crash versions of the properties (paper: "the full definition of BCA-Crash appears in the full
version"; "all parties that terminate satisfy agreement … binding applies to all parties") are
proved for *all* parties, including those that crash after deciding, with weak validity: if all
parties have input `v`, every decision is `v` (grade 2).

## Main results
* `Alg3.theorem_4_1`: Algorithm 3 implements BCA-Crash with at most 2 broadcasts per party;
* `Alg5.theorem_5_1`: Algorithm 5 implements GBCA-Crash with at most 3 broadcasts per party.
-/

namespace Podc.BindingCrusaderAgreement

open Cslib.Byzantine.AsyncBroadcast

/-- Messages of Algorithms 3 and 5 (`none` = `⊥`). -/
inductive CMsg
  | val (v : Bool)
  | echo (o : Option Bool)
  | echo2 (o : Option Bool)
  deriving DecidableEq, Fintype

/-- Message class. -/
def CMsg.IsVal : CMsg → Prop
  | .val _ => True
  | _ => False

/-- Message class. -/
def CMsg.IsEcho : CMsg → Prop
  | .echo _ => True
  | _ => False

/-- Message class. -/
def CMsg.IsEcho2 : CMsg → Prop
  | .echo2 _ => True
  | _ => False

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- "`n − t` messages of class `mk`, not all with the same non-`⊥` value": `n − t` senders and
a `⊥` or two different values among them. -/
def Mixed (t : ℕ) (ib : P → Set CMsg) (φ : CMsg → Prop) (mk : Option Bool → CMsg) : Prop :=
  Fintype.card P - t ≤ cntP ib φ ∧
    (0 < cnt ib (mk none) ∨ (0 < cnt ib (mk (some true)) ∧ 0 < cnt ib (mk (some false))))

omit [DecidableEq P] in
theorem Mixed.mono {t : ℕ} {ib ib' : P → Set CMsg} (h : ∀ s, ib s ⊆ ib' s) {φ mk}
    (hm : Mixed t ib φ mk) : Mixed t ib' φ mk :=
  ⟨hm.1.trans (cntP_mono h _), hm.2.imp (fun h1 => lt_of_lt_of_le h1 (cnt_mono h _))
    fun h1 => ⟨lt_of_lt_of_le h1.1 (cnt_mono h _), lt_of_lt_of_le h1.2 (cnt_mono h _)⟩⟩

/-- The `val`/`echo` guards of `A` are lines 1–4 of Algorithms 3 and 5. -/
structure IsValLayer {O : Type*} (t : ℕ) (A : Protocol P CMsg Bool O) : Prop where
  send_val : ∀ p x ib out v, A.send p x ib out (.val v) ↔ v = x
  send_echo_some : ∀ p x ib out v, A.send p x ib out (.echo (some v)) ↔
    (Fintype.card P - t ≤ cnt ib (.val v) ∧ ∀ o, .echo o ∉ out)
  send_echo_none : ∀ p x ib out, A.send p x ib out (.echo none) ↔
    (Fintype.card P - t ≤ cntP ib CMsg.IsVal ∧ 0 < cnt ib (.val true) ∧
      0 < cnt ib (.val false) ∧ ∀ o, .echo o ∉ out)

namespace ValLayer

variable {O : Type*} {t : ℕ} {A : Protocol P CMsg Bool O} {x : P → Bool}
  {σ : State P CMsg O}

/-- A message received by `p` from some party was broadcast (crash faults). -/
theorem exists_sent (_ht : 2 * t < Fintype.card P) (h : Reachable A x .crash t σ) {p : P}
    {m : CMsg} (hc : 0 < cnt (σ.inbox p) m) : ∃ r, (r, m) ∈ σ.sent := by
  obtain ⟨r, hr⟩ := Set.nonempty_of_ncard_ne_zero (s := {r | m ∈ σ.inbox p r}) (by
    unfold cnt at hc; omega)
  exact ⟨r, h.genuine_crash hr⟩

omit [DecidableEq P] in
theorem pos_of_quorum (ht : 2 * t < Fintype.card P) {n : ℕ} (h : Fintype.card P - t ≤ n) :
    0 < n := by omega

omit [DecidableEq P] in
/-- Two quorums of `n − t` parties intersect (`2t < n`). -/
theorem exists_common (ht : 2 * t < Fintype.card P) {S₁ S₂ : Set P}
    (h₁ : Fintype.card P - t ≤ S₁.ncard) (h₂ : Fintype.card P - t ≤ S₂.ncard) :
    ∃ r ∈ S₁, r ∈ S₂ := by
  obtain ⟨r, h1, h2, -⟩ := exists_mem_inter_not_mem (S₁ := S₁) (S₂ := S₂) (B := ∅)
    (by simp; omega)
  exact ⟨r, h1, h2⟩

variable (hA : IsValLayer t A)
include hA

theorem val_just (h : Reachable A x .crash t σ) {p : P} {v : Bool}
    (hm : (p, .val v) ∈ σ.sent) : v = x p := by
  refine h.sent_just (J := fun p m _ _ => ∀ v, m = .val v → v = x p) ?_ ?_ hm v rfl
  · intro _ _ _ _ _ _ _ _ hj; exact hj
  · intro p ib out m hs v hv
    subst hv
    exact (hA.send_val _ _ _ _ _).1 hs

theorem echo_some_just (h : Reachable A x .crash t σ) {p : P} {v : Bool}
    (hm : (p, .echo (some v)) ∈ σ.sent) : Fintype.card P - t ≤ cnt (σ.inbox p) (.val v) := by
  refine h.sent_just (J := fun _ m ib _ => ∀ v, m = .echo (some v) →
    Fintype.card P - t ≤ cnt ib (.val v)) ?_ ?_ hm v rfl
  · intro _ _ _ _ _ _ hib _ hj v hv; exact (hj v hv).trans (cnt_mono hib _)
  · intro p ib out m hs v hv
    subst hv
    exact ((hA.send_echo_some _ _ _ _ _).1 hs).1

theorem echo_none_just (h : Reachable A x .crash t σ) {p : P}
    (hm : (p, .echo none) ∈ σ.sent) :
    0 < cnt (σ.inbox p) (.val true) ∧ 0 < cnt (σ.inbox p) (.val false) := by
  refine h.sent_just (J := fun _ m ib _ => m = .echo none →
    0 < cnt ib (.val true) ∧ 0 < cnt ib (.val false)) ?_ ?_ hm rfl
  · intro _ _ _ _ _ _ hib _ hj hv
    exact ⟨lt_of_lt_of_le (hj hv).1 (cnt_mono hib _), lt_of_lt_of_le (hj hv).2 (cnt_mono hib _)⟩
  · intro p ib out m hs hv
    subst hv
    have := (hA.send_echo_none _ _ _ _).1 hs
    exact ⟨this.2.1, this.2.2.1⟩

theorem echo_unique (h : Reachable A x .crash t σ) {p : P} {o o' : Option Bool}
    (hv : (p, .echo o) ∈ σ.sent) (hw : (p, .echo o') ∈ σ.sent) : o = o' := by
  have := h.sent_excl CMsg.IsEcho ?_ hv hw trivial trivial
  · simpa using this
  · intro p ib out m hs hm m' hm' h2
    rcases m with _ | (_ | v) | _ <;> try exact hm.elim
    all_goals rcases m' with _ | o' | _ <;> try exact h2.elim
    · exact ((hA.send_echo_none _ _ _ _).1 hs).2.2.2 o' hm'
    · exact ((hA.send_echo_some _ _ _ _ _).1 hs).2 o' hm'

/-- All non-`⊥` `echo` messages carry the same value. -/
theorem echo_consistent (ht : 2 * t < Fintype.card P) (h : Reachable A x .crash t σ)
    {s s' : P} {v w : Bool} (hv : (s, .echo (some v)) ∈ σ.sent)
    (hw : (s', .echo (some w)) ∈ σ.sent) : v = w := by
  obtain ⟨r, h1, h2⟩ := exists_common ht (echo_some_just hA h hv) (echo_some_just hA h hw)
  rw [val_just hA h (h.genuine_crash h1), val_just hA h (h.genuine_crash h2)]

/-- If all parties have input `v`, no `⟨echo, ⊥⟩` and no `⟨echo, 1 − v⟩` is ever broadcast. -/
theorem echo_of_inputs (ht : 2 * t < Fintype.card P) (h : Reachable A x .crash t σ) {v : Bool}
    (hx : ∀ p, x p = v) {p : P} {o : Option Bool} (hm : (p, .echo o) ∈ σ.sent) :
    o = some v := by
  have noval : ∀ q, ¬ 0 < cnt (σ.inbox q) (.val (!v)) := fun q hc => by
    obtain ⟨r, hr⟩ := exists_sent ht h hc
    have := val_just hA h hr
    rw [hx r] at this
    cases v <;> simp at this
  rcases o with _ | w
  · have := echo_none_just hA h hm
    cases v
    · exact absurd this.1 (noval p)
    · exact absurd this.2 (noval p)
  · by_cases hw : w = v
    · rw [hw]
    · have hw' : w = !v := by cases w <;> cases v <;> simp_all
      subst hw'
      exact absurd (pos_of_quorum ht (echo_some_just hA h hm)) (noval p)

/-! #### Liveness of the layer -/

section Liveness

variable (E : Exec A x .crash t) (hF : E.Fair)
include hF

theorem eventually_val {q : P} (hq : E.Correct q) : ∃ i, (q, .val (x q)) ∈ (E.σ i).sent := by
  obtain ⟨j, m', hm', hj⟩ := E.eventually_sent hF hq (φ := fun m => m = .val (x q)) rfl (i := 0)
    fun j _ _ => (hA.send_val _ _ _ _ _).2 rfl
  subst hm'
  exact ⟨j, hj⟩

/-- Every correct party eventually broadcasts an `echo`. -/
theorem eventually_echo (_ht : 2 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i o, (q, .echo o) ∈ (E.σ i).sent := by
  obtain ⟨j, hj⟩ := E.eventually_rcv_all hF (S := {s | E.Correct s}) (fun s hs => hs)
    (m := fun s => .val (x s)) (fun s hs => eventually_val hA E hF hs) hq
  have hc := E.card_sub_le_ncard_correct
  by_cases hsame : ∃ v, ∀ s, E.Correct s → x s = v
  · obtain ⟨v, hv⟩ := hsame
    obtain ⟨i, m', hm', hi⟩ := E.eventually_sent hF hq (φ := CMsg.IsEcho) (m := .echo (some v))
      trivial (i := j) fun j' hij hno => (hA.send_echo_some _ _ _ _ _).2
        ⟨hc.trans (le_cnt fun s hs => by
          have := E.rcv_mono hij (hj s hs); rwa [hv s hs] at this),
          fun o ho => hno (.echo o) trivial ho⟩
    rcases m' with _ | o | _ <;> try exact hm'.elim
    exact ⟨i, o, hi⟩
  · push Not at hsame
    obtain ⟨s₁, hs₁, h₁⟩ := hsame false
    obtain ⟨s₀, hs₀, h₀⟩ := hsame true
    simp only [ne_eq, Bool.not_eq_false] at h₁
    simp only [ne_eq, Bool.not_eq_true] at h₀
    have pos : ∀ j', j ≤ j' → ∀ s, E.Correct s → 0 < cnt ((E.σ j').inbox q) (.val (x s)) :=
      fun j' hij s hs => by
        have : ({s} : Set P).ncard ≤ cnt ((E.σ j').inbox q) (.val (x s)) := le_cnt fun r hr => by
          rw [Set.mem_singleton_iff] at hr; subst hr; exact E.rcv_mono hij (hj r hs)
        simp at this; omega
    obtain ⟨i, m', hm', hi⟩ := E.eventually_sent hF hq (φ := CMsg.IsEcho) (m := .echo none)
      trivial (i := j) fun j' hij hno => (hA.send_echo_none _ _ _ _).2
        ⟨hc.trans (le_cntP fun s hs => ⟨_, E.rcv_mono hij (hj s hs), trivial⟩),
          h₁ ▸ pos j' hij s₁ hs₁, h₀ ▸ pos j' hij s₀ hs₀,
          fun o ho => hno (.echo o) trivial ho⟩
    rcases m' with _ | o | _ <;> try exact hm'.elim
    exact ⟨i, o, hi⟩

end Liveness

end ValLayer

/-! ## Algorithm 3 -/

namespace Alg3

/-- Broadcast guards of Algorithm 3. -/
def sendG (t : ℕ) (x : Bool) (ib : P → Set CMsg) (out : Set CMsg) : CMsg → Prop
  | .val v => v = x
  | .echo (some v) => Fintype.card P - t ≤ cnt ib (.val v) ∧ ∀ o, .echo o ∉ out
  | .echo none => Fintype.card P - t ≤ cntP ib CMsg.IsVal ∧ 0 < cnt ib (.val true) ∧
      0 < cnt ib (.val false) ∧ ∀ o, .echo o ∉ out
  | .echo2 _ => False

/-- Decision guards of Algorithm 3 (lines 5–7). -/
def decideG (t : ℕ) (ib : P → Set CMsg) : Option Bool → Prop
  | some v => Fintype.card P - t ≤ cnt ib (.echo (some v))
  | none => Mixed t ib CMsg.IsEcho CMsg.echo

/-- Algorithm 3. -/
def alg (t : ℕ) : Protocol P CMsg Bool (Option Bool) where
  send _ x ib out m := sendG t x ib out m
  decide _ _ ib _ o := decideG t ib o

omit [DecidableEq P] in
theorem isValLayer (t : ℕ) : IsValLayer t (alg (P := P) t) :=
  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

variable {t : ℕ} {x : P → Bool} {σ : State P CMsg (Option Bool)}

theorem dec_just (h : Reachable (alg t) x .crash t σ) {p : P} {o : Option Bool}
    (hd : σ.dec p = some o) : decideG t (σ.inbox p) o := by
  refine h.dec_just (J := fun _ o ib _ => decideG t ib o) ?_ (fun _ _ _ _ hs => hs) hd
  intro _ o _ _ _ _ hib _ hj
  rcases o with _ | v
  · exact Mixed.mono hib hj
  · exact (show Fintype.card P - t ≤ _ from hj).trans (cnt_mono hib _)

/-- Agreement (Definition 3.1, crash version): no two parties (correct or not) decide different
non-`⊥` values. -/
theorem agreement (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ)
    {p q : P} {a b : Bool} (hp : σ.dec p = some (some a)) (hq : σ.dec q = some (some b)) :
    a = b := by
  obtain ⟨r, h1, h2⟩ := ValLayer.exists_common ht (dec_just h hp) (dec_just h hq)
  simpa using ValLayer.echo_unique (isValLayer t) h (h.genuine_crash h1) (h.genuine_crash h2)

/-- Weak validity: if all parties have input `v`, every decision is `v`. -/
theorem weak_validity (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ)
    {v : Bool} (hx : ∀ p, x p = v) (p : P) : σ.dec p = none ∨ σ.dec p = some (some v) := by
  have hA := isValLayer (P := P) t
  have hecho : ∀ (_q : P) (o : Option Bool), 0 < cnt (σ.inbox p) (.echo o) → o = some v :=
    fun _ o hc => by
    obtain ⟨r, hr⟩ := ValLayer.exists_sent ht h hc
    exact ValLayer.echo_of_inputs hA ht h hx hr
  rcases hd : σ.dec p with _ | o
  · exact Or.inl rfl
  right
  rcases o with _ | w
  · rcases (dec_just h hd).2 with h1 | ⟨h1, h2⟩
    · exact absurd (hecho p _ h1) (by simp)
    · have e1 := hecho p _ h1
      have e2 := hecho p _ h2
      simp only [Option.some.injEq] at e1 e2
      exact absurd (e1.trans e2.symm) (by simp)
  · have := hecho p _ (ValLayer.pos_of_quorum ht (dec_just h hd))
    rw [this]

/-- Binding (Definition 3.1, crash version): once some party has decided, there is `b` such
that no party (correct or not) decides `1 − b` in any extension. -/
theorem binding (ht : 2 * t < Fintype.card P) (h : Reachable (alg t) x .crash t σ) {p : P}
    (hp : σ.dec p ≠ none) : ∃ b : Bool, ∀ σ', Reach (alg t) x .crash t σ σ' →
      ∀ q, σ'.dec q ≠ some (some (!b)) := by
  have hA := isValLayer (P := P) t
  by_cases hex : ∃ s u, (s, CMsg.echo (some u)) ∈ σ.sent
  · obtain ⟨s, u, hs⟩ := hex
    refine ⟨u, fun σ' hσ' q hq => ?_⟩
    have h' := h.reach hσ'
    obtain ⟨r, hr⟩ := ValLayer.exists_sent ht h' (ValLayer.pos_of_quorum ht (dec_just h' hq))
    have := ValLayer.echo_consistent hA ht h' (hσ'.sent_subset hs) hr
    cases u <;> simp at this
  · push Not at hex
    refine ⟨true, fun σ' hσ' q hq => ?_⟩
    have h' := h.reach hσ'
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
    rcases o with _ | v
    · obtain ⟨r, h1, h2⟩ := ValLayer.exists_common ht (dec_just h ho).1 (dec_just h' hq)
      obtain ⟨m, hm, hm1⟩ := h1
      rcases m with _ | (_ | u) | _ <;> try exact hm1.elim
      · have := ValLayer.echo_unique hA h' (hσ'.sent_subset (h.genuine_crash hm))
          (h'.genuine_crash h2)
        simp at this
      · exact hex r u (h.genuine_crash hm)
    · obtain ⟨r, hr⟩ := ValLayer.exists_sent ht h (ValLayer.pos_of_quorum ht (dec_just h ho))
      exact hex r v hr

/-- Every party broadcasts at most 2 messages (`val`, `echo`): "all parties decide within 2
communication rounds" (Theorem 4.1). -/
theorem out_ncard_le_two (h : Reachable (alg t) x .crash t σ) (p : P) :
    (σ.out p).ncard ≤ 2 := by
  classical
  have hA := isValLayer (P := P) t
  let o0 : Option Bool := if ho : ∃ o, (p, CMsg.echo o) ∈ σ.sent then ho.choose else none
  have hsub : σ.out p ⊆ {.val (x p), .echo o0} := by
    intro m hm
    rcases m with v | o | o
    · simp [ValLayer.val_just hA h hm]
    · have ho : ∃ o, (p, CMsg.echo o) ∈ σ.sent := ⟨o, hm⟩
      have : o = o0 := by
        simp only [o0, dite_eq_left_of_eq_true (eq_true ho)]
        exact ValLayer.echo_unique hA h hm ho.choose_spec
      simp [this]
    · exact (h.sent_just (J := fun _ m _ _ => ¬ CMsg.IsEcho2 m) (fun _ _ _ _ _ _ _ _ h => h)
        (fun p ib out m hs hm2 => by rcases m with _ | _ | _ <;> first | exact hm2 | exact hs)
        hm trivial).elim
  refine (Set.ncard_le_ncard hsub).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  simp

section Termination

variable (E : Exec (alg t) x .crash t) (hF : E.Fair)
include hF

/-- Termination: in every fair execution every correct party decides. -/
theorem termination (ht : 2 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i, (E.σ i).dec q ≠ none := by
  have hA := isValLayer (P := P) t
  have hc := E.card_sub_le_ncard_correct
  obtain ⟨iq, oq, hiq⟩ := ValLayer.eventually_echo hA E hF ht hq
  obtain ⟨j, hj⟩ := E.eventually_rcv_all' hF (S := {s | E.Correct s}) (fun s hs => hs)
    (φ := CMsg.IsEcho) (fun s hs => by
      obtain ⟨i, o, hi⟩ := ValLayer.eventually_echo hA E hF ht hs
      exact ⟨i, .echo o, trivial, hi⟩) hq
  by_cases hb : ∃ s i, E.Correct s ∧ (s, CMsg.echo none) ∈ (E.σ i).sent
  · obtain ⟨s, i, hs, hsi⟩ := hb
    obtain ⟨j', hj'⟩ := hF.deliver q s _ i hq hs hsi
    refine E.eventually_dec hF hq (o := none) (i := max j j') fun j₂ hij _ =>
      ⟨hc.trans (le_cntP fun s hs => ?_), Or.inl ?_⟩
    · obtain ⟨m, hm2, hm⟩ := hj s hs
      exact ⟨m, E.rcv_mono (le_of_max_le_left hij) hm, hm2⟩
    · have : ({s} : Set P).ncard ≤ cnt ((E.σ j₂).inbox q) (.echo none) := le_cnt fun r hr => by
        rw [Set.mem_singleton_iff] at hr; subst hr; exact E.rcv_mono (le_of_max_le_right hij) hj'
      simp at this; omega
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
    exact E.eventually_dec hF hq (o := some w) (i := j₁) fun j₂ hij _ =>
      hc.trans (le_cnt fun s hs => E.rcv_mono hij (hj₁ s hs))

end Termination

/-- Theorem 4.1: Algorithm 3 implements weak-validity BCA (BCA-Crash) tolerating `t < n/2`
crash faults (the paper's `t < ⌈n/2⌉` is the same condition), and every party broadcasts at most
2 messages. -/
theorem theorem_4_1 (ht : 2 * t < Fintype.card P) :
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ p q a b,
      σ.dec p = some (some a) → σ.dec q = some (some b) → a = b) ∧
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ v, (∀ p, x p = v) →
      ∀ p, σ.dec p = none ∨ σ.dec p = some (some v)) ∧
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ p, σ.dec p ≠ none →
      ∃ b : Bool, ∀ σ', Reach (alg t) x .crash t σ σ' → ∀ q, σ'.dec q ≠ some (some (!b))) ∧
    (∀ E : Exec (alg t) x .crash t, E.Fair → ∀ q, E.Correct q → ∃ i, (E.σ i).dec q ≠ none) ∧
    (∀ σ, Reachable (alg t) x .crash t σ → ∀ p, (σ.out p).ncard ≤ 2) :=
  ⟨fun _ h _ _ _ _ hp hq => agreement ht h hp hq,
   fun _ h _ hx p => weak_validity ht h hx p,
   fun _ h _ hp => binding ht h hp,
   fun E hF _ hq => termination E hF ht hq,
   fun _ h p => out_ncard_le_two h p⟩

end Alg3

end Podc.BindingCrusaderAgreement
