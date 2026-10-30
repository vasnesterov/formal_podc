import Podc.Computability.Distributed.Byzantine.AsyncBroadcast
import Papers.PODC2022.BindingCrusaderAgreement.Basic

/-!
# The echo / amplify / approve layer of Algorithms 4 and 6

Abraham, Ben-David, Yandamuri, *Efficient and Adaptively Secure Asynchronous Binary Agreement via
Binding Crusader Agreement*, PODC 2022, Section 4.2 (Algorithm 4, lines 1–7) and Section 5.2
(Algorithm 6, lines 1–7).

Both Byzantine algorithms start with the same layer:
* send `⟨echo, x⟩` (own input);
* upon `⟨echo, v⟩` from `t + 1` parties, send `⟨echo, v⟩` (amplification);
* upon `⟨echo, v⟩` from `n − t` parties, add `v` to `approvedVals` and, if no `echo2` was sent
  yet, send `⟨echo2, v⟩`.

`approvedVals` is not stored: `Approved t ib v` (`v` has `n − t` echoes) is read off the inbox.
`IsEchoLayer t A` says that the guards of a protocol `A` for `echo`/`echo2` are exactly these.
We prove the facts shared by both algorithms: justification and uniqueness of `echo2`
(`echo2_approved`, `echo2_unique`), the first half of validity (`not_echo_of_inputs`,
`not_approved_of_inputs`), Lemma 4.6 (`approved_spread`) and the first liveness steps
(`eventually_approved`, `eventually_echo2`).
-/

namespace Podc.BindingCrusaderAgreement

open Cslib.Byzantine.AsyncBroadcast

/-- Messages of Algorithms 4 and 6 (instance identifiers are implicit: one instance). `none`
stands for `⊥`. -/
inductive Msg
  | echo (v : Bool)
  | echo2 (v : Bool)
  | echo3 (o : Option Bool)
  | echo4 (o : Option Bool)
  | echo5 (o : Option Bool)
  deriving DecidableEq, Fintype

/-- Message classes. -/
def Msg.IsEcho2 : Msg → Prop
  | .echo2 _ => True
  | _ => False

/-- Message classes. -/
def Msg.IsEcho3 : Msg → Prop
  | .echo3 _ => True
  | _ => False

/-- Message classes. -/
def Msg.IsEcho4 : Msg → Prop
  | .echo4 _ => True
  | _ => False

/-- Message classes. -/
def Msg.IsEcho5 : Msg → Prop
  | .echo5 _ => True
  | _ => False

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- `v ∈ approvedVals`: `⟨echo, v⟩` was received from `n − t` parties. -/
def Approved (t : ℕ) (ib : P → Set Msg) (v : Bool) : Prop :=
  Fintype.card P - t ≤ cnt ib (.echo v)

/-- `|approvedVals| > 1`. -/
def BothApproved (t : ℕ) (ib : P → Set Msg) : Prop := Approved t ib true ∧ Approved t ib false

omit [DecidableEq P] in
theorem Approved.mono {t : ℕ} {ib ib' : P → Set Msg} (h : ∀ s, ib s ⊆ ib' s) {v : Bool}
    (hv : Approved t ib v) : Approved t ib' v :=
  le_trans hv (cnt_mono h _)

omit [DecidableEq P] in
theorem BothApproved.mono {t : ℕ} {ib ib' : P → Set Msg} (h : ∀ s, ib s ⊆ ib' s)
    (hv : BothApproved t ib) : BothApproved t ib' :=
  ⟨hv.1.mono h, hv.2.mono h⟩

omit [DecidableEq P] in
theorem bothApproved_of_ne {t : ℕ} {ib : P → Set Msg} {v w : Bool} (hvw : v ≠ w)
    (hv : Approved t ib v) (hw : Approved t ib w) : BothApproved t ib := by
  cases v <;> cases w <;> first | exact absurd rfl hvw | exact ⟨hw, hv⟩ | exact ⟨hv, hw⟩

/-- The `echo`/`echo2` guards of `A` are those of lines 1–7 of Algorithms 4 and 6. -/
structure IsEchoLayer {O : Type*} (t : ℕ) (A : Protocol P Msg Bool O) : Prop where
  send_echo : ∀ p x ib out v, A.send p x ib out (.echo v) ↔ (v = x ∨ t + 1 ≤ cnt ib (.echo v))
  send_echo2 : ∀ p x ib out v,
    A.send p x ib out (.echo2 v) ↔ (Approved t ib v ∧ ∀ w, .echo2 w ∉ out)

variable {O : Type*} {t : ℕ} {A : Protocol P Msg Bool O} {x : P → Bool} {k : FaultKind}

section Safety

variable (hA : IsEchoLayer t A) {σ : State P Msg O}
include hA

theorem echo2_approved (h : Reachable A x k t σ) {p : P} {v : Bool}
    (hm : (p, .echo2 v) ∈ σ.sent) : Approved t (σ.inbox p) v := by
  refine h.sent_just (J := fun _ m ib _ => ∀ v, m = .echo2 v → Approved t ib v) ?_ ?_ hm v rfl
  · intro p m ib ib' out out' hib _ hj v hv
    exact (hj v hv).mono hib
  · intro p ib out m hs v hv
    subst hv
    exact ((hA.send_echo2 _ _ _ _ _).1 hs).1

theorem echo2_unique (h : Reachable A x k t σ) {p : P} {v w : Bool}
    (hv : (p, .echo2 v) ∈ σ.sent) (hw : (p, .echo2 w) ∈ σ.sent) : v = w := by
  have := h.sent_excl Msg.IsEcho2 ?_ hv hw trivial trivial
  · simpa using this
  · intro p ib out m hs hm m' hm' h2
    cases m with
    | echo2 v =>
      cases m' with
      | echo2 w' => exact ((hA.send_echo2 _ _ _ _ _).1 hs).2 w' hm'
      | _ => exact h2
    | _ => exact hm

/-- If all parties of `H` (which contains all corrupted parties' complement, `|Hᶜ| ≤ t`) have
input `v`, no party of `H` ever echoes `1 − v` (proof of Lemma 4.5). -/
theorem not_echo_of_inputs (h : Reachable A x k t σ) {H : Set P} (hbad : σ.bad ⊆ Hᶜ)
    (hH : Hᶜ.ncard ≤ t) {v : Bool} (hx : ∀ p ∈ H, x p = v) :
    ∀ p ∈ H, (p, .echo (!v)) ∉ σ.sent := by
  revert hbad
  refine Reachable.induction (Inv := fun σ => σ.bad ⊆ Hᶜ → ∀ p ∈ H, (p, .echo (!v)) ∉ σ.sent)
    (by simp [State.init]) ?_ h
  intro σ σ' hr ih hst hbad' p hp hm
  have hbad : σ.bad ⊆ Hᶜ := hst.bad_subset.trans hbad'
  have ih := ih hbad
  cases hst with
  | send p' m' hb hg =>
    rcases Set.mem_insert_iff.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases (hA.send_echo _ _ _ _ _).1 hg with hg | hg
      · rw [hx p hp] at hg; cases v <;> simp at hg
      · have hsub : {s | Msg.echo (!v) ∈ σ.inbox p s} ⊆ Hᶜ := by
          intro s hs hsH
          exact ih s hsH (hr.genuine hs (fun hb => hbad hb hsH))
        have := (Set.ncard_le_ncard hsub).trans hH
        unfold cnt at hg
        omega
    · exact ih p hp hm
  | _ => exact ih p hp hm

/-- Under the hypotheses of `not_echo_of_inputs`, nobody has `1 − v` approved. -/
theorem not_approved_of_inputs (ht : 2 * t < Fintype.card P) (h : Reachable A x k t σ)
    {H : Set P} (hbad : σ.bad ⊆ Hᶜ) (hH : Hᶜ.ncard ≤ t) {v : Bool} (hx : ∀ p ∈ H, x p = v)
    (q : P) : ¬ Approved t (σ.inbox q) (!v) := by
  intro hap
  have hsub : {s | Msg.echo (!v) ∈ σ.inbox q s} ⊆ Hᶜ := by
    intro s hs hsH
    exact not_echo_of_inputs hA h hbad hH hx s hsH (h.genuine hs (fun hb => hbad hb hsH))
  have := (Set.ncard_le_ncard hsub).trans hH
  unfold Approved cnt at hap
  omega

/-- Nobody sends `echo2 (1 − v)` under the hypotheses of `not_echo_of_inputs`. -/
theorem not_echo2_of_inputs (ht : 2 * t < Fintype.card P) (h : Reachable A x k t σ)
    {H : Set P} (hbad : σ.bad ⊆ Hᶜ) (hH : Hᶜ.ncard ≤ t) {v : Bool} (hx : ∀ p ∈ H, x p = v)
    (q : P) : (q, .echo2 (!v)) ∉ σ.sent := fun hm =>
  not_approved_of_inputs hA ht h hbad hH hx q (echo2_approved hA h hm)

end Safety

/-! ### Liveness of the layer -/

namespace Exec

variable (hA : IsEchoLayer t A) (E : Exec A x k t) (hF : E.Fair)
include hA hF

/-- If `t + 1` correct parties broadcast `⟨echo, u⟩`, every correct party eventually does. -/
theorem eventually_echo {T : Set P} (hT : ∀ s ∈ T, E.Correct s) (hTc : t + 1 ≤ T.ncard)
    (hTs : ∀ s ∈ T, ∃ i, (s, .echo u) ∈ (E.σ i).sent) {q : P} (hq : E.Correct q) :
    ∃ i, (q, .echo u) ∈ (E.σ i).sent := by
  obtain ⟨i, hi⟩ := E.eventually_rcv_all hF hT (m := fun _ => .echo u) hTs hq
  obtain ⟨j, m', hm', hj⟩ := E.eventually_sent hF hq (φ := fun m => m = .echo u) rfl
    (i := i) fun j hij _ => (hA.send_echo _ _ _ _ _).2 (Or.inr (hTc.trans (le_cnt
      fun s hs => E.rcv_mono hij (hi s hs))))
  subst hm'
  exact ⟨j, hj⟩

omit hA in
/-- If all correct parties eventually broadcast `⟨echo, u⟩`, all eventually approve `u`. -/
theorem eventually_approved_of_all {u : Bool}
    (hall : ∀ s, E.Correct s → ∃ i, (s, .echo u) ∈ (E.σ i).sent) {q : P} (hq : E.Correct q) :
    ∃ i, ∀ j, i ≤ j → Approved t ((E.σ j).inbox q) u := by
  obtain ⟨i, hi⟩ := E.eventually_rcv_all hF (S := {s | E.Correct s}) (fun s hs => hs)
    (m := fun _ => .echo u) (fun s hs => hall s hs) hq
  refine ⟨i, fun j hij => (E.card_sub_le_ncard_correct).trans (le_cnt fun s hs => ?_)⟩
  exact E.rcv_mono hij (hi s hs)

/-- Lemma 4.6: a value approved by anybody (with `n − t` echoes in its inbox) is eventually
approved by every correct party. -/
theorem approved_spread (ht : 3 * t < Fintype.card P) {p : P} {i : ℕ} {u : Bool}
    (hp : Approved t ((E.σ i).inbox p) u) {q : P} (hq : E.Correct q) :
    ∃ i, ∀ j, i ≤ j → Approved t ((E.σ j).inbox q) u := by
  let S := {s | Msg.echo u ∈ (E.σ i).inbox p s}
  let T := S ∩ {s | E.Correct s}
  have hT : t + 1 ≤ T.ncard := by
    have h1 : S ⊆ T ∪ {s | ¬ E.Correct s} := fun s hs => by
      by_cases hc : E.Correct s
      · exact Or.inl ⟨hs, hc⟩
      · exact Or.inr hc
    have h2 := (Set.ncard_le_ncard h1).trans (Set.ncard_union_le _ _)
    have h3 := E.ncard_not_correct_le
    unfold Approved cnt at hp
    change Fintype.card P - t ≤ S.ncard at hp
    omega
  have hTs : ∀ s ∈ T, ∃ i, (s, .echo u) ∈ (E.σ i).sent := fun s hs =>
    ⟨i, (E.reachable i).genuine hs.1 (hs.2 i)⟩
  exact eventually_approved_of_all E hF
    (fun s hs => eventually_echo hA E hF (fun s hs => hs.2) hT hTs hs) hq

omit hA hF in
/-- Some value has `t + 1` correct parties with that input (`n ≥ 3t + 1`). -/
theorem exists_input (ht : 3 * t < Fintype.card P) :
    ∃ v : Bool, t + 1 ≤ {s | E.Correct s ∧ x s = v}.ncard := by
  by_contra hne
  push Not at hne
  have h1 : {s | E.Correct s} ⊆ {s | E.Correct s ∧ x s = true} ∪ {s | E.Correct s ∧ x s = false} :=
    fun s hs => by
      simp only [Set.mem_ofPred_eq] at hs
      cases hx : x s <;> simp [hs, hx]
  have h2 := (Set.ncard_le_ncard h1).trans (Set.ncard_union_le _ _)
  have h3 := E.card_sub_le_ncard_correct
  have := hne true
  have := hne false
  omega

/-- First liveness step of Lemma 4.7: some value `v` is eventually approved by all correct
parties. -/
theorem eventually_approved (ht : 3 * t < Fintype.card P) :
    ∃ v : Bool, ∀ q, E.Correct q → ∃ i, ∀ j, i ≤ j → Approved t ((E.σ j).inbox q) v := by
  obtain ⟨v, hv⟩ := exists_input E ht
  refine ⟨v, fun q hq => eventually_approved_of_all E hF (fun s hs => ?_) hq⟩
  refine eventually_echo hA E hF (T := {s | E.Correct s ∧ x s = v}) (fun s hs => hs.1) hv
    (fun s hs => ?_) hs
  obtain ⟨j, m', hm', hj⟩ := E.eventually_sent hF hs.1 (φ := fun m => m = .echo v) rfl (i := 0)
    fun j _ _ => (hA.send_echo _ _ _ _ _).2 (Or.inl hs.2.symm)
  subst hm'
  exact ⟨j, hj⟩

/-- Every correct party eventually broadcasts an `echo2` message. -/
theorem eventually_echo2 (ht : 3 * t < Fintype.card P) {q : P} (hq : E.Correct q) :
    ∃ i w, (q, .echo2 w) ∈ (E.σ i).sent := by
  obtain ⟨v, hv⟩ := eventually_approved hA E hF ht
  obtain ⟨i, hi⟩ := hv q hq
  obtain ⟨j, m', hm', hj⟩ := E.eventually_sent hF hq (φ := Msg.IsEcho2) (m := .echo2 v)
    trivial (i := i) fun j hij hno => (hA.send_echo2 _ _ _ _ _).2
      ⟨hi j hij, fun w hw => hno (.echo2 w) trivial hw⟩
  cases m' with
  | echo2 w => exact ⟨j, w, hj⟩
  | _ => exact absurd hm' id

end Exec

end Podc.BindingCrusaderAgreement
