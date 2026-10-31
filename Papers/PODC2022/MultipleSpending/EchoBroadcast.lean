import Papers.PODC2022.MultipleSpending.Broadcast

/-!
# A quorum-echo `k`-Consistent Broadcast matching the source-restricted lower bound (§5)

The proof of Theorem 5.1 only uses graphs `G_{F,S}` with the source in `F`; the matching upper
bound is achieved by a quorum-echo algorithm:

* `echoAlg T s`: the source `s` sends `val v` for its input `v`; a process that received
  `val v` from `s` sends `echo v` (at most one `echo`); a process delivers `v` once all members of
  one of its quorums echoed `v`.
* `echoAlg_isKCB`: with `SelfMem` and `HasQuorums`, `echoAlg T s` implements `k`-CB with
  `k = max 1 λ_s`, where `λ_s = srcInconsistencyNumber T s` is the inconsistency number
  restricted to faulty sets containing the source. (`HasQuorums` is needed: if some process
  has no quorum, there is no quorum map and `λ_s = 0` by convention, while a faulty source can
  still make two processes with singleton quorums deliver different values.)
* `echoAlg_localProgressAll`: it satisfies (per-value) Local Progress.
* `theorem_5_1_false'`: a robust counterexample to Theorem 5.1 — four processes forming two
  "pairs" `{0, 1}`, `{2, 3}` (the processes `1`, `3` trust everybody), fault model
  `{∅, {0}, {2}}`. The inconsistency number is `2`, yet for every source the echo algorithm
  implements `1`-CB with Local Progress (quorums have size `2` or `4`, so this is not an artefact
  of singleton quorums as in `theorem_5_1_false`).
-/

namespace Podc.MultipleSpending

open Cslib.Byzantine.AsyncBroadcast Finset

variable {P V : Type*}

/-- Messages of the echo algorithm. -/
inductive EchoMsg (V : Type*)
  /-- The source's value. -/
  | val (v : V)
  /-- An echo of the value received from the source. -/
  | echo (v : V)

/-- The quorum-echo broadcast algorithm with source `s`:
* send `val v` iff the own input is `some v` (only the source has an input);
* send `echo v` iff `val v` was received from `s` and no `echo` was sent yet;
* deliver `v` iff all members of one of the own quorums echoed `v`. -/
def echoAlg (T : TrustModel P) (s : P) : Protocol P (EchoMsg V) (Option V) V where
  send _ xp ib out m := match m with
    | .val v => xp = some v
    | .echo v => EchoMsg.val v ∈ ib s ∧ ∀ w, EchoMsg.echo w ∉ out
  decide p _ ib _ v := ∃ Q ∈ T.Q p, ∀ q ∈ Q, EchoMsg.echo v ∈ ib q

variable [DecidableEq P]

/-! ### Invariants -/

section Invariants

variable {T : TrustModel P} {s : P} {x : P → Option V} {k : FaultKind} {t : ℕ}
  {σ : State P (EchoMsg V) V}

/-- Justification of a broadcast of the echo algorithm. -/
private def echoJ (s : P) (x : P → Option V) (p : P) (m : EchoMsg V)
    (ib : P → Set (EchoMsg V)) : Prop :=
  match m with
  | .val v => x p = some v
  | .echo v => EchoMsg.val v ∈ ib s

private theorem echoJ_of_sent (h : Reachable (echoAlg T s) x k t σ) {p : P} {m : EchoMsg V}
    (hm : (p, m) ∈ σ.sent) : echoJ s x p m (σ.inbox p) := by
  refine h.sent_just (J := fun p m ib _ => echoJ s x p m ib) ?_ ?_ hm
  · intro p m ib ib' _ _ hib _ hJ
    cases m with
    | val v => exact hJ
    | echo v => exact hib s hJ
  · intro p ib out m hg
    cases m with
    | val v => exact hg
    | echo v => exact hg.1

/-- Only an input value is sent as `val`. -/
theorem echo_val_of_sent (h : Reachable (echoAlg T s) x k t σ) {p : P} {v : V}
    (hm : (p, EchoMsg.val v) ∈ σ.sent) : x p = some v :=
  echoJ_of_sent h hm

/-- An `echo v` was preceded by the reception of `val v` from the source. -/
theorem echo_rcv_of_sent (h : Reachable (echoAlg T s) x k t σ) {p : P} {v : V}
    (hm : (p, EchoMsg.echo v) ∈ σ.sent) : EchoMsg.val v ∈ σ.inbox p s :=
  echoJ_of_sent h hm

/-- A process sends at most one `echo`. -/
theorem echo_excl (h : Reachable (echoAlg T s) x k t σ) {p : P} {v w : V}
    (hv : (p, EchoMsg.echo v) ∈ σ.sent) (hw : (p, EchoMsg.echo w) ∈ σ.sent) : v = w := by
  have := h.sent_excl (φ := fun m => ∃ u, m = EchoMsg.echo u) ?_ hv hw ⟨v, rfl⟩ ⟨w, rfl⟩
  · cases this; rfl
  · rintro p ib out m hg ⟨u, rfl⟩ m' hm' ⟨u', rfl⟩
    exact hg.2 u' hm'

/-- A decision is justified by echoes from a whole quorum. -/
theorem echo_quorum_of_dec (h : Reachable (echoAlg T s) x k t σ) {p : P} {v : V}
    (hv : σ.dec p = some v) : ∃ Q ∈ T.Q p, ∀ q ∈ Q, EchoMsg.echo v ∈ σ.inbox p q := by
  refine h.dec_just (J := fun p v ib _ => ∃ Q ∈ T.Q p, ∀ q ∈ Q, EchoMsg.echo v ∈ ib q) ?_
    (fun _ _ _ _ hg => hg) hv
  rintro p v ib ib' _ _ hib _ ⟨Q, hQ, hQe⟩
  exact ⟨Q, hQ, fun q hq => hib q (hQe q hq)⟩

/-- If a currently uncorrupted process received `echo v` from a currently uncorrupted `q`, then
`q` received `val v` from the source. -/
theorem echo_rcv_val (h : Reachable (echoAlg T s) x k t σ) {p q : P} {v : V}
    (hv : EchoMsg.echo v ∈ σ.inbox p q) (hq : q ∉ σ.bad) : EchoMsg.val v ∈ σ.inbox q s :=
  echo_rcv_of_sent h (h.genuine hv hq)

/-- If a process `p` in one of its own quorums and the source are uncorrupted, `p` decides only
the source's input. -/
theorem echo_dec_input (hself : T.SelfMem) (h : Reachable (echoAlg T s) x k t σ) {p : P}
    {v : V} (hp : p ∉ σ.bad) (hs : s ∉ σ.bad) (hv : σ.dec p = some v) : x s = some v := by
  obtain ⟨Q, hQ, hQe⟩ := echo_quorum_of_dec h hv
  have h1 := echo_rcv_val h (hQe p (hself p Q hQ)) hp
  exact echo_val_of_sent h (h.genuine h1 hs)

end Invariants

/-! ### `k`-Consistent Broadcast -/

section KCB

variable [Fintype P] {T : TrustModel P} {s : P} {mo : Option V}

omit [Fintype P] in
private theorem srcInput_self {s : P} {mo : Option V} : srcInput s mo s = mo := by
  simp [srcInput]

/-- Integrity: with a correct source, a correct process delivers only the broadcast value. -/
theorem echo_integrity (hself : T.SelfMem) (E : BExec (echoAlg T s) s mo) (hs : E.Correct s)
    {p : P} {i : ℕ} {v : V} (hp : E.Correct p) (hv : (E.σ i).dec p = some v) : mo = some v := by
  have := echo_dec_input hself (E.reachable i) (hp i) (hs i) hv
  rwa [srcInput_self] at this

/-- `k`-Consistency with `k = max 1 λ_s`: with a correct source at most one value is delivered;
otherwise the correct deliverers of distinct values, with the quorums that justified their
decisions, form an independent set of `G_{F,S}` for the faulty set `F ∋ s` (a correct process
common to two such quorums would have sent two different echoes). -/
theorem echo_consistency (hself : T.SelfMem) (hQ : T.HasQuorums)
    (E : BExec (echoAlg T s) s mo) (hFT : faultySet E ∈ T.F) :
    (delivered E).encard ≤ max 1 (srcInconsistencyNumber T s) := by
  classical
  have hfaulty : ∀ r, r ∈ faultySet E ↔ ¬ E.Correct r := by simp [faultySet]
  by_cases hs : E.Correct s
  · calc (delivered E).encard ≤ 1 := by
          rw [Set.encard_le_one_iff]
          rintro v w ⟨p, i, hp, hv⟩ ⟨q, j, hq, hw⟩
          have h1 := echo_integrity hself E hs hp hv
          have h2 := echo_integrity hself E hs hq hw
          rw [h1] at h2; exact Option.some_injective _ h2
      _ ≤ _ := by exact_mod_cast le_max_left _ _
  have hsF : s ∈ faultySet E := (hfaulty s).2 hs
  refine le_trans ?_ (by exact_mod_cast le_max_right _ _ :
    ((srcInconsistencyNumber T s : ℕ) : ℕ∞) ≤ ((max 1 (srcInconsistencyNumber T s) : ℕ) : ℕ∞))
  apply encard_le_of_finset
  intro D hD
  have hdel : ∀ v ∈ D, ∃ p i Q, E.Correct p ∧ (E.σ i).dec p = some v ∧ Q ∈ T.Q p ∧
      ∀ q ∈ Q, EchoMsg.echo v ∈ (E.σ i).inbox p q := by
    intro v hv
    obtain ⟨p, i, hp, hpv⟩ := hD hv
    obtain ⟨Q, hQ, hQe⟩ := echo_quorum_of_dec (E.reachable i) hpv
    exact ⟨p, i, Q, hp, hpv, hQ, hQe⟩
  rcases D.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · simp
  obtain ⟨p₀, -⟩ := hD hv₀
  have : Nonempty P := ⟨p₀⟩
  choose! f i R hf using hdel
  have hinj : Set.InjOn f (D : Set V) := by
    intro v hv w hw he
    have h1 := (hf v hv).2.1
    have h2 := (hf w hw).2.1
    rw [he] at h1
    exact dec_unique E h1 h2
  let C := D.image f
  have hC : C.card = D.card := Finset.card_image_of_injOn hinj
  let R' : P → Finset P := fun p => if h : ∃ v ∈ D, f v = p then R h.choose else ∅
  have hR' : ∀ p ∈ C, ∃ v ∈ D, f v = p ∧ R' p = R v := by
    intro p hp
    have h : ∃ v ∈ D, f v = p := by simpa [C] using hp
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dite_eq_left_of_eq_true (eq_true h)⟩
  rw [← hC]
  show C.card ≤ inconsistencyNumber ⟨T.Q, {F | F ∈ T.F ∧ s ∈ F}⟩
  refine TrustModel.card_le_inconsistencyNumber_of_family ⟨T.Q, {F | F ∈ T.F ∧ s ∈ F}⟩ hQ (F := faultySet E) ⟨hFT, hsF⟩
    ?_ R' ?_ ?_
  · rw [Finset.disjoint_left]
    intro p hp hpF
    obtain ⟨v, hv, rfl, -⟩ := hR' p hp
    exact (hfaulty _).1 hpF (hf v hv).1
  · intro p hp
    obtain ⟨v, hv, rfl, he⟩ := hR' p hp
    rw [he]; exact (hf v hv).2.2.1
  · intro p hp q hq hpq r hr
    obtain ⟨v, hv, rfl, hev⟩ := hR' p hp
    obtain ⟨w, hw, rfl, hew⟩ := hR' q hq
    rw [hev, hew, Finset.mem_inter] at hr
    by_contra hrF
    have hrc : E.Correct r := by simpa [hfaulty] using hrF
    have h1 := (E.reachable _).genuine ((hf v hv).2.2.2 r hr.1) (hrc _)
    have h2 := (E.reachable _).genuine ((hf w hw).2.2.2 r hr.2) (hrc _)
    have h1' := E.sent_mono (le_max_left (i v) (i w)) h1
    have h2' := E.sent_mono (le_max_right (i v) (i w)) h2
    exact hpq (by rw [echo_excl (E.reachable _) h1' h2'])

/-- Validity: in a fair execution with a correct source broadcasting `m`, every correct live
process delivers `m` (the members of its fault-free quorum echo `m`). -/
theorem echo_validity (hself : T.SelfMem) (m : V) (E : BExec (echoAlg T s) s (some m))
    (hF : E.Fair) (hs : E.Correct s) (p : P) (hp : E.Correct p)
    (hlive : T.Live (faultySet E) p) : ∃ i, (E.σ i).dec p = some m := by
  classical
  obtain ⟨Q, hQ, hQF⟩ := hlive
  have hQc : ∀ q ∈ Q, E.Correct q := fun q hq => by
    by_contra hc
    exact Finset.disjoint_left.mp hQF hq (by simp [faultySet, hc])
  -- the source sends `val m`
  obtain ⟨j0, hj0⟩ := hF.send s (EchoMsg.val m) 0 hs fun _ _ => by
    simp [echoAlg, srcInput]
  -- every member of `Q` echoes `m`
  have hecho : ∀ q ∈ (Q : Set P), ∃ i, (q, EchoMsg.echo m) ∈ (E.σ i).sent := by
    intro q hq
    obtain ⟨j1, hj1⟩ := hF.deliver q s (EchoMsg.val m) j0 (hQc q hq) hs hj0
    obtain ⟨j2, m', ⟨u, rfl⟩, hj2⟩ := E.eventually_sent hF (hQc q hq)
      (φ := fun m => ∃ u, m = EchoMsg.echo u) (m := EchoMsg.echo m) ⟨m, rfl⟩ (i := j1)
      (fun j hj hno => ⟨E.inbox_mono hj q s hj1, fun w hw => hno _ ⟨w, rfl⟩ hw⟩)
    have h1 := echo_rcv_of_sent (E.reachable j2) hj2
    have h2 := echo_val_of_sent (E.reachable j2) ((E.reachable j2).genuine h1 (hs j2))
    rw [srcInput_self, Option.some_inj] at h2
    subst h2
    exact ⟨j2, hj2⟩
  -- `p` receives all these echoes and then decides
  obtain ⟨j3, hj3⟩ := E.eventually_rcv_all hF (S := ↑Q) (fun q hq => hQc q hq)
    (m := fun _ => EchoMsg.echo m) hecho hp
  obtain ⟨j4, hj4⟩ := hF.decide p m j3 hp fun j hj =>
    ⟨Q, hQ, fun q hq => E.rcv_mono hj (hj3 q hq)⟩
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hj4
  have := echo_integrity hself E hs hp hv
  exact ⟨j4, by rw [hv, ← this]⟩

/-- **Upper bound matching the lower bound of Theorem 5.1 (as actually proved).** With
self-membership and nonempty quorum sets, the echo algorithm implements `k`-CB with
`k = max 1 λ_s`, `λ_s = srcInconsistencyNumber T s`. -/
theorem echoAlg_isKCB (hself : T.SelfMem) (hQ : T.HasQuorums) (s : P) :
    IsKCB (V := V) T s (max 1 (srcInconsistencyNumber T s)) (echoAlg T s) where
  validity m E hF _ hs p hp hlive := echo_validity hself m E hF hs p hp hlive
  consistency _ E hFT := echo_consistency hself hQ E hFT
  integrity _ E _ hs _ _ _ hp hv := echo_integrity hself E hs hp hv

end KCB

/-! ### Local Progress -/

section Batch

variable {M I O : Type*} {A : Protocol P M I O} {x : P → I} {k : FaultKind} {t : ℕ}

-- Copied from `Papers/PODC2025/AsymmetricDAGConsensus/RoundGather.lean` (CSLib candidate there).
/-- Deliver a finite set of sent messages. -/
private theorem reach_deliver_set (σ : State P M O) {X : Set (P × P × M)} (hX : X.Finite)
    (hs : ∀ e ∈ X, (e.2.1, e.2.2) ∈ σ.sent) :
    Reach A x k t σ { σ with rcv := σ.rcv ∪ X } := by
  induction X, hX using Set.Finite.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | @insert a X _ _ ih =>
    have ih := ih fun e he => hs e (Set.mem_insert_of_mem _ he)
    refine ih.tail ?_
    have := Step.deliver (A := A) (x := x) (k := k) (t := t)
      { σ with rcv := σ.rcv ∪ X } a.1 a.2.1 a.2.2 (hs a (Set.mem_insert _ _))
    convert this using 2
    ext e; simp

-- Copied from `Papers/PODC2025/AsymmetricDAGConsensus/RoundGather.lean` (CSLib candidate there).
/-- Every process of `D` broadcasts one message allowed by its guard in `σ`. -/
private theorem reach_send_finset (σ : State P M O) (m : P → M) (D : Finset P)
    (hg : ∀ p ∈ D, p ∉ σ.bad ∧ A.send p (x p) (σ.inbox p) (σ.out p) (m p)) :
    Reach A x k t σ { σ with sent := σ.sent ∪ {e | ∃ p ∈ D, e = (p, m p)} } := by
  classical
  induction D using Finset.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | @insert a D ha ih =>
    have ih := ih fun p hp => hg p (Finset.mem_insert_of_mem hp)
    refine ih.tail ?_
    obtain ⟨hb, hga⟩ := hg a (Finset.mem_insert_self a D)
    have hout : ({ σ with sent := σ.sent ∪ {e | ∃ p ∈ D, e = (p, m p)} } : State P M O).out a =
        σ.out a := by
      ext m'
      simp only [State.mem_out, Set.mem_union, Set.mem_ofPred_eq, Prod.mk.injEq]
      constructor
      · rintro (h | ⟨p, hp, rfl, -⟩)
        · exact h
        · exact absurd hp ha
      · exact Or.inl
    have := Step.send (A := A) (x := x) (k := k) (t := t)
      { σ with sent := σ.sent ∪ {e | ∃ p ∈ D, e = (p, m p)} } a (m a) hb (by rw [hout]; exact hga)
    convert this using 2
    ext e
    simp only [Finset.mem_insert, exists_eq_or_imp, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_insert_iff]
    tauto

end Batch

/-- **Local Progress** of the echo algorithm (for every value): the source sends `val m` to the
members of `Q`, they echo `m` to `p`, and `p` delivers `m`; only `s` and `Q` take steps. -/
theorem echoAlg_localProgressAll [Fintype P] (T : TrustModel P) (hself : T.SelfMem) (s : P) :
    LocalProgressAll (V := V) T s (echoAlg T s) := by
  classical
  intro p Q hQ m
  have hpQ : p ∈ Q := hself p Q hQ
  let x := srcInput s (some m)
  let A := echoAlg (V := V) T s
  let N := Fintype.card P
  -- the source sends `val m`
  let σ1 : State P (EchoMsg V) V :=
    { (State.init : State P (EchoMsg V) V) with sent := {(s, .val m)} }
  have h1 : Step A x .byzantine N State.init σ1 := by
    have := Step.send (A := A) (x := x) (k := .byzantine) (t := N) State.init s (.val m)
      (by simp [State.init]) (by simp [A, x, echoAlg, srcInput])
    convert this using 2
    simp [State.init]
  -- it is delivered to every member of `Q`
  let X2 : Set (P × P × EchoMsg V) := {e | ∃ q ∈ Q, e = (q, s, .val m)}
  have hX2 : X2.Finite := (Q.finite_toSet.image fun q => (q, s, EchoMsg.val m)).subset
    (by rintro e ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩)
  have h2 := reach_deliver_set (A := A) (x := x) (k := .byzantine) (t := N) σ1 hX2
    (by rintro e ⟨q, hq, rfl⟩; simp [σ1])
  let σ2 : State P (EchoMsg V) V := { σ1 with rcv := σ1.rcv ∪ X2 }
  -- every member of `Q` echoes `m`
  have h3 := reach_send_finset (A := A) (x := x) (k := .byzantine) (t := N) σ2
    (fun _ => .echo m) Q (by
      intro q hq
      refine ⟨by simp [σ2, σ1, State.init], ?_⟩
      refine ⟨?_, ?_⟩
      · simp [σ2, σ1, X2, State.init, hq]
      · intro w hw
        simp [σ2, σ1] at hw)
  let σ3 : State P (EchoMsg V) V :=
    { σ2 with sent := σ2.sent ∪ {e | ∃ q ∈ Q, e = (q, EchoMsg.echo m)} }
  -- the echoes are delivered to `p`
  let X4 : Set (P × P × EchoMsg V) := {e | ∃ q ∈ Q, e = (p, q, .echo m)}
  have hX4 : X4.Finite := (Q.finite_toSet.image fun q => (p, q, EchoMsg.echo m)).subset
    (by rintro e ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩)
  have h4 := reach_deliver_set (A := A) (x := x) (k := .byzantine) (t := N) σ3 hX4
    (by rintro e ⟨q, hq, rfl⟩; simp [σ3, hq])
  let σ4 : State P (EchoMsg V) V := { σ3 with rcv := σ3.rcv ∪ X4 }
  -- `p` delivers `m`
  let σ5 : State P (EchoMsg V) V := { σ4 with dec := Function.update σ4.dec p (some m) }
  have h5 : Step A x .byzantine N σ4 σ5 :=
    Step.decide _ p m (by simp [σ4, σ3, σ2, σ1, State.init])
      (by simp [σ4, σ3, σ2, σ1, State.init])
      ⟨Q, hQ, fun q hq => by simp [σ4, X4, hq]⟩
  refine ⟨σ5, ?_, by simp [σ5, σ4, σ3, σ2, σ1, State.init], by simp [σ5], ?_, ?_, ?_⟩
  · exact (((Relation.ReflTransGen.single h1).trans h2).trans h3 |>.trans h4).tail h5
  · intro q m' hq
    simp only [σ5, σ4, σ3, σ2, σ1, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Prod.mk.injEq] at hq
    rcases hq with ⟨rfl, -⟩ | ⟨q', hq', rfl, -⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem hq'
  · intro q r m' hq
    simp only [σ5, σ4, σ3, σ2, σ1, X2, X4, State.init, Set.empty_union, Set.mem_union,
      Set.mem_ofPred_eq, Prod.mk.injEq] at hq
    rcases hq with ⟨q', hq', rfl, -⟩ | ⟨q', hq', rfl, -⟩
    · exact Finset.mem_insert_of_mem hq'
    · exact Finset.mem_insert_of_mem hpQ
  · intro q hq
    by_cases hqp : q = p
    · rw [hqp]; exact Finset.mem_insert_of_mem hpQ
    · simp [σ5, σ4, σ3, σ2, σ1, State.init, Function.update_of_ne hqp] at hq

/-! ### A robust counterexample to Theorem 5.1 -/

/-- Quorums of the counterexample: `0` trusts `{0, 1}`, `2` trusts `{2, 3}`, and `1`, `3` trust
everybody. -/
def pairsQ : Fin 4 → Set (Finset (Fin 4))
  | 0 => {{0, 1}}
  | 1 => {Finset.univ}
  | 2 => {{2, 3}}
  | 3 => {Finset.univ}

/-- The trust model of the counterexample: at most one of `0`, `2` may fail. -/
def pairsT : TrustModel (Fin 4) := ⟨pairsQ, {∅, {0}, {2}}⟩

theorem pairsT_selfMem : pairsT.SelfMem := by
  intro p Q hQ
  fin_cases p <;> simp only [pairsT, pairsQ, Set.mem_singleton_iff] at hQ <;> subst hQ <;> decide

theorem pairsT_downClosed : pairsT.DownClosed := by
  intro F hF F' hF'
  simp only [pairsT, Set.mem_insert_iff, Set.mem_singleton_iff] at hF ⊢
  rcases hF with rfl | rfl | rfl
  · exact Or.inl (Finset.subset_empty.mp hF')
  · rcases Finset.subset_singleton_iff.mp hF' with h | h <;> simp [h]
  · rcases Finset.subset_singleton_iff.mp hF' with h | h <;> simp [h]

theorem pairsT_hasQuorums : pairsT.HasQuorums := by
  intro p; fin_cases p <;> simp [pairsT, pairsQ]

/-- The only quorum map of `pairsT`. -/
private theorem pairsT_quorumMap {S : Fin 4 → Finset (Fin 4)} (hS : ∀ p, S p ∈ pairsQ p) :
    S = ![{0, 1}, Finset.univ, {2, 3}, Finset.univ] := by
  funext p; fin_cases p; exacts [hS 0, hS 1, hS 2, hS 3]

private theorem pairs_check : ∀ F ∈ ({∅, {0}, {2}} : Finset (Finset (Fin 4))),
    ∀ C : Finset (Fin 4), (Disjoint C F ∧ ∀ p ∈ C, ∀ q ∈ C, p ≠ q →
      (![{0, 1}, Finset.univ, {2, 3}, Finset.univ] p) ∩
        (![{0, 1}, Finset.univ, {2, 3}, Finset.univ] q) ⊆ F) →
    C.card ≤ 2 := by
  decide

private theorem pairs_src_check : ∀ F ∈ ({{0}, {2}} : Finset (Finset (Fin 4))),
    ∀ C : Finset (Fin 4), (Disjoint C F ∧ ∀ p ∈ C, ∀ q ∈ C, p ≠ q →
      (![{0, 1}, Finset.univ, {2, 3}, Finset.univ] p) ∩
        (![{0, 1}, Finset.univ, {2, 3}, Finset.univ] q) ⊆ F) →
    C.card ≤ 1 := by
  decide

/-- The inconsistency number of `pairsT` is `2`: with nobody faulty, `{0, 2}` is independent
since `{0, 1} ∩ {2, 3} = ∅`. -/
theorem pairsT_inconsistencyNumber : inconsistencyNumber pairsT = 2 := by
  apply le_antisymm
  · apply TrustModel.inconsistencyNumber_le
    intro F hF S hS C hC
    rw [pairsT_quorumMap hS] at hC
    refine pairs_check F ?_ C hC
    simp only [pairsT, Set.mem_insert_iff, Set.mem_singleton_iff] at hF
    rcases hF with rfl | rfl | rfl <;> decide
  · have hS : ![{0, 1}, Finset.univ, {2, 3}, Finset.univ] ∈ pairsT.QuorumMaps := by
      intro p; fin_cases p <;> rfl
    have := pairsT.card_le_inconsistencyNumber (F := ∅) (by simp [pairsT]) hS (C := {0, 2})
      ⟨by decide, by decide⟩
    simpa using this

/-- For every source, the source-restricted inconsistency number of `pairsT` is at most `1`. -/
theorem pairsT_srcInconsistencyNumber_le (s : Fin 4) : srcInconsistencyNumber pairsT s ≤ 1 := by
  apply TrustModel.inconsistencyNumber_le
  rintro F ⟨hF, hsF⟩ S hS C hC
  rw [pairsT_quorumMap hS] at hC
  refine pairs_src_check F ?_ C hC
  simp only [pairsT, Set.mem_insert_iff, Set.mem_singleton_iff] at hF
  rcases hF with rfl | rfl | rfl
  · simp at hsF
  · decide
  · decide

/-- **Theorem 5.1 is false, robustly.** Four processes, quorums `{0, 1}` (for `0`), `{2, 3}` (for
`2`) and `Π` (for `1` and `3`), at most one of `0`, `2` faulty. The inconsistency number is `2`,
yet for every source the echo algorithm implements `1`-Consistent Broadcast with (per-value)
Local Progress. -/
theorem theorem_5_1_false' : pairsT.SelfMem ∧ pairsT.DownClosed ∧ inconsistencyNumber pairsT = 2 ∧
    ∀ s, IsKCB (V := ℕ) pairsT s 1 (echoAlg pairsT s) ∧
      LocalProgressAll (V := ℕ) pairsT s (echoAlg pairsT s) := by
  refine ⟨pairsT_selfMem, pairsT_downClosed, pairsT_inconsistencyNumber, fun s =>
    ⟨?_, echoAlg_localProgressAll _ pairsT_selfMem s⟩⟩
  have h := echoAlg_isKCB (V := ℕ) pairsT_selfMem pairsT_hasQuorums s
  rwa [max_eq_left (pairsT_srcInconsistencyNumber_le s)] at h

end Podc.MultipleSpending
