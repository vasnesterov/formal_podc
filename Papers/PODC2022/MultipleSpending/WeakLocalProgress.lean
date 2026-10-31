import Papers.PODC2022.MultipleSpending.Broadcast

/-!
# Local Progress as stated is too weak for Theorem 5.1

The proof of Theorem 5.1 takes, for each `p_i` of an independent set, a Local-Progress execution in
which `p_i` delivers a value `m_i`, and needs the `m_i` to be **distinct**. The paper's Local
Progress only provides *some* delivered value. Here the source is faulty in the faulty set that
maximizes the independence number (so the other defect of Theorem 5.1, see `theorem_5_1_false`,
does not apply), yet a `1`-CB with (the paper's) Local Progress exists although
`k_max = λ_s = 2`: correct processes deliver a default value `0` on their own, and any other value
only after hearing from the other non-source process.

Trust model `T3` on `Fin 3` (source `0`): `Q 0 = {Π}`, `Q 1 = {{0,1}}`, `Q 2 = {{0,2}}`,
`F = {∅, {0}}`.
-/

namespace Podc.MultipleSpending

namespace WeakLP

open Cslib.Byzantine.AsyncBroadcast Finset

/-- Messages: the source's value and echoes. -/
inductive Msg
  | val (v : ℕ)
  | echo (v : ℕ)
  deriving DecidableEq

/-- The trust model. -/
def T3 : TrustModel (Fin 3) :=
  ⟨fun p => match p with
    | 0 => {Finset.univ}
    | 1 => {{0, 1}}
    | 2 => {{0, 2}}, {∅, {0}}⟩

/-- The algorithm (source `0`): the source sends and delivers its value; the others echo the first
value received from the source; a non-source process delivers the value it echoed if it is the
default value `0`, and any value echoed by both non-source processes. -/
def alg : Protocol (Fin 3) Msg (Option ℕ) ℕ where
  send _ xp ib out m := match m with
    | .val v => xp = some v
    | .echo v => Msg.val v ∈ ib 0 ∧ ∀ w, Msg.echo w ∉ out
  decide _ xp ib out v :=
    xp = some v ∨ (Msg.echo v ∈ out ∧ v = 0) ∨ ∀ q : Fin 3, q ≠ 0 → Msg.echo v ∈ ib q

abbrev R (mo : Option ℕ) (σ : State (Fin 3) Msg ℕ) : Prop :=
  Reachable alg (srcInput 0 mo) .byzantine (Fintype.card (Fin 3)) σ

theorem sent_val {mo : Option ℕ} {σ : State (Fin 3) Msg ℕ} (h : R mo σ) {p : Fin 3} {v : ℕ}
    (hm : (p, Msg.val v) ∈ σ.sent) : p = 0 ∧ mo = some v := by
  have := h.sent_just (J := fun p m _ _ => ∀ v, m = Msg.val v → srcInput 0 mo p = some v)
    (fun _ _ _ _ _ _ _ _ h => h)
    (fun p ib out m hg v hv => by subst hv; exact hg) hm v rfl
  simp only [srcInput] at this
  split_ifs at this with hp
  · exact ⟨hp, this⟩

theorem sent_echo {mo : Option ℕ} {σ : State (Fin 3) Msg ℕ} (h : R mo σ) {p : Fin 3} {v : ℕ}
    (hm : (p, Msg.echo v) ∈ σ.sent) : Msg.val v ∈ σ.inbox p 0 := by
  exact h.sent_just (J := fun p m ib _ => ∀ v, m = Msg.echo v → Msg.val v ∈ ib 0)
    (fun _ _ _ _ _ _ hib _ h v hv => hib _ (h v hv))
    (fun p ib out m hg v hv => by subst hv; exact hg.1) hm v rfl

theorem echo_unique {mo : Option ℕ} {σ : State (Fin 3) Msg ℕ} (h : R mo σ) {p : Fin 3}
    {v w : ℕ} (hv : (p, Msg.echo v) ∈ σ.sent) (hw : (p, Msg.echo w) ∈ σ.sent) : v = w := by
  have := h.sent_excl (φ := fun m => ∃ v, m = Msg.echo v)
    (by
      rintro p ib out m hg ⟨v, rfl⟩ m' hm' ⟨w, rfl⟩
      exact hg.2 w hm') hv hw ⟨v, rfl⟩ ⟨w, rfl⟩
  simpa using this

/-- With an uncorrupted source, only the source's value is delivered. -/
theorem dec_eq {mo : Option ℕ} {σ : State (Fin 3) Msg ℕ} (h : R mo σ) (hbad : σ.bad = ∅)
    {p : Fin 3} {v : ℕ} (hd : σ.dec p = some v) : mo = some v := by
  have hJ := h.dec_just (J := fun p v ib out => srcInput 0 mo p = some v ∨
      (Msg.echo v ∈ out ∧ v = 0) ∨ ∀ q : Fin 3, q ≠ 0 → Msg.echo v ∈ ib q)
    (fun _ _ _ _ _ _ hib hout h => h.imp_right (Or.imp (fun h => ⟨hout h.1, h.2⟩)
      fun h q hq => hib q (h q hq))) (fun _ _ _ _ h => h) hd
  have hnb : ∀ q, q ∉ σ.bad := by simp [hbad]
  rcases hJ with h1 | ⟨h1, -⟩ | h1
  · simp only [srcInput] at h1; split_ifs at h1; exact h1
  · exact (sent_val h (h.genuine (sent_echo h h1) (hnb 0))).2
  · have := h.genuine (h1 1 (by decide)) (hnb 1)
    exact (sent_val h (h.genuine (sent_echo h this) (hnb 0))).2

theorem T3_selfMem : T3.SelfMem := by
  intro p Q hQ
  fin_cases p <;> simp [T3] at hQ <;> subst hQ <;> decide

theorem T3_downClosed : T3.DownClosed := by
  intro F hF F' hF'
  simp only [T3, Set.mem_insert_iff, Set.mem_singleton_iff] at hF ⊢
  rcases hF with rfl | rfl
  · exact Or.inl (Finset.subset_empty.mp hF')
  · rcases Finset.subset_singleton_iff.mp hF' with h | h
    · exact Or.inl h
    · exact Or.inr h

private theorem T3_check : ∀ F ∈ ({∅, {0}} : Finset (Finset (Fin 3))), ∀ C : Finset (Fin 3),
    (Disjoint C F ∧ ∀ p ∈ C, ∀ q ∈ C, p ≠ q →
      (![Finset.univ, {0, 1}, {0, 2}] p) ∩ (![Finset.univ, {0, 1}, {0, 2}] q) ⊆ F) →
    C.card ≤ 2 := by
  decide

theorem T3_le (F : Finset (Fin 3)) (hF : F ∈ T3.F) (S : Fin 3 → Finset (Fin 3))
    (hS : S ∈ T3.QuorumMaps) (C : Finset (Fin 3)) (hC : IsIndep F S C) : C.card ≤ 2 := by
  have hSeq : S = ![Finset.univ, {0, 1}, {0, 2}] := by
    funext p; have := hS p; fin_cases p <;> simpa [T3] using this
  subst hSeq
  refine T3_check F ?_ C hC
  simp only [T3, Set.mem_insert_iff, Set.mem_singleton_iff] at hF
  rcases hF with rfl | rfl <;> simp

theorem T3_inconsistencyNumber : inconsistencyNumber T3 = 2 := by
  apply le_antisymm
  · exact TrustModel.inconsistencyNumber_le _ fun F hF S hS C hC => T3_le F hF S hS C hC
  · have hS : ![Finset.univ, {0, 1}, {0, 2}] ∈ T3.QuorumMaps := by
      intro p; fin_cases p <;> simp [T3]
    have := T3.card_le_inconsistencyNumber (F := {0}) (by simp [T3]) hS (C := {1, 2})
      ⟨by decide, by decide⟩
    simpa using this

theorem T3_srcInconsistencyNumber : srcInconsistencyNumber T3 0 = 2 := by
  apply le_antisymm
  · exact TrustModel.inconsistencyNumber_le _ fun F hF S hS C hC => T3_le F hF.1 S hS C hC
  · have hS : ![Finset.univ, {0, 1}, {0, 2}] ∈ (⟨T3.Q, {F | F ∈ T3.F ∧ 0 ∈ F}⟩ :
        TrustModel (Fin 3)).QuorumMaps := by
      intro p; fin_cases p <;> simp [T3]
    have := TrustModel.card_le_inconsistencyNumber _ (F := {0}) (by simp [T3]) hS
      (C := {1, 2}) ⟨by decide, by decide⟩
    simpa [srcInconsistencyNumber] using this

/-- The algorithm is a `1`-Consistent Broadcast with source `0` in `T3`. -/
theorem alg_isKCB : IsKCB T3 0 1 alg where
  validity := by
    intro m E hF hFT hs p hp _
    have hall : ∀ q, E.Correct q := by
      intro q
      by_contra hq
      have : q ∈ faultySet E := by classical simp [faultySet, hq]
      have hs' : (0 : Fin 3) ∉ faultySet E := by classical simp [faultySet, hs]
      simp only [T3, Set.mem_insert_iff, Set.mem_singleton_iff] at hFT
      rcases hFT with h | h <;> rw [h] at this hs' <;> simp_all
    have hbad : ∀ i, (E.σ i).bad = ∅ := fun i =>
      Set.eq_empty_iff_forall_notMem.mpr fun q => hall q i
    -- the value decided (if any) is `m`
    have hval : ∀ i v, (E.σ i).dec p = some v → v = m := fun i v hv =>
      (Option.some_injective _ (dec_eq (E.reachable i) (hbad i) hv)).symm
    -- the source sends `m`, everybody receives it and echoes, everybody receives the echoes
    obtain ⟨j0, hj0⟩ := hF.send 0 (Msg.val m) 0 (hall 0) fun _ _ => by simp [alg, srcInput]
    have hrcv : ∀ q, ∃ j, (q, 0, Msg.val m) ∈ (E.σ j).rcv := fun q =>
      hF.deliver q 0 _ j0 (hall q) (hall 0) hj0
    have hecho : ∀ q, ∃ j, (q, Msg.echo m) ∈ (E.σ j).sent := by
      intro q
      obtain ⟨j, hj⟩ := hrcv q
      obtain ⟨j', w, ⟨w', rfl⟩, hw⟩ := E.eventually_sent hF (hall q) (φ := fun m => ∃ w, m = Msg.echo w)
        (m := Msg.echo m) ⟨m, rfl⟩ (i := j) fun l hl hno =>
          ⟨E.rcv_mono hl hj, fun w hw => hno _ ⟨w, rfl⟩ hw⟩
      have h1 := sent_echo (E.reachable j') hw
      have := (sent_val (E.reachable j') ((E.reachable j').genuine h1 (hall 0 j'))).2
      simp only [Option.some.injEq] at this
      exact ⟨j', this ▸ hw⟩
    obtain ⟨j1, hj1⟩ := E.eventually_rcv_all hF (S := Set.univ) (fun s _ => hall s)
      (m := fun _ => Msg.echo m) (fun s _ => hecho s) (hp)
    obtain ⟨j2, hj2⟩ := hF.decide p m j1 hp fun l hl =>
      Or.inr (Or.inr fun q _ => E.rcv_mono hl (hj1 q (Set.mem_univ q)))
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hj2
    exact ⟨j2, by rw [hv, hval _ _ hv]⟩
  consistency := by
    intro mo E hFT
    rw [Nat.cast_one, Set.encard_le_one_iff]
    rintro v w ⟨p, i, hp, hv⟩ ⟨q, j, hq, hw⟩
    by_cases hs : E.Correct 0
    · -- correct source: everybody is correct
      have hall : ∀ r, E.Correct r := by
        intro r
        by_contra hr
        have : r ∈ faultySet E := by classical simp [faultySet, hr]
        have hs' : (0 : Fin 3) ∉ faultySet E := by classical simp [faultySet, hs]
        simp only [T3, Set.mem_insert_iff, Set.mem_singleton_iff] at hFT
        rcases hFT with h | h <;> rw [h] at this hs' <;> simp_all
      have hbad : ∀ i, (E.σ i).bad = ∅ := fun i =>
        Set.eq_empty_iff_forall_notMem.mpr fun r => hall r i
      have h1 := dec_eq (E.reachable i) (hbad i) hv
      have h2 := dec_eq (E.reachable j) (hbad j) hw
      rw [h1] at h2; exact Option.some_injective _ h2
    · -- faulty source: the correct processes are `1` and `2`
      have hF0 : faultySet E = {0} := by
        simp only [T3, Set.mem_insert_iff, Set.mem_singleton_iff] at hFT
        rcases hFT with h | h
        · exfalso; have : (0 : Fin 3) ∈ faultySet E := by classical simp [faultySet, hs]
          rw [h] at this; simp at this
        · exact h
      have hc : ∀ r, E.Correct r ↔ r ≠ 0 := by
        intro r
        have := congrArg (r ∈ ·) hF0
        classical simp [faultySet] at this
        tauto
      -- a correct non-source decider echoed its value, and either it is `0` or the other
      -- non-source process echoed it too
      let N := max i j
      have hR := E.reachable N
      have hv' := E.dec_mono (le_max_left i j) hv
      have hw' := E.dec_mono (le_max_right i j) hw
      have key : ∀ r u, E.Correct r → (E.σ N).dec r = some u →
          (r, Msg.echo u) ∈ (E.σ N).sent ∧ (u = 0 ∨ ∀ r', r' ≠ 0 → (r', Msg.echo u) ∈ (E.σ N).sent) := by
        intro r u hr hd
        have hr0 : r ≠ 0 := (hc r).mp hr
        have hJ := hR.dec_just (J := fun p v ib out => srcInput 0 mo p = some v ∨
            (Msg.echo v ∈ out ∧ v = 0) ∨ ∀ q : Fin 3, q ≠ 0 → Msg.echo v ∈ ib q)
          (fun _ _ _ _ _ _ hib hout h => h.imp_right (Or.imp (fun h => ⟨hout h.1, h.2⟩)
            fun h q hq => hib q (h q hq))) (fun _ _ _ _ h => h) hd
        rcases hJ with h1 | ⟨h1, h2⟩ | h1
        · simp [srcInput, hr0] at h1
        · exact ⟨h1, Or.inl h2⟩
        · have hall : ∀ r', r' ≠ 0 → (r', Msg.echo u) ∈ (E.σ N).sent := fun r' hr' =>
            hR.genuine (h1 r' hr') (((hc r').mpr hr') N)
          exact ⟨hall r hr0, Or.inr hall⟩
      obtain ⟨e1, o1⟩ := key p v hp hv'
      obtain ⟨e2, o2⟩ := key q w hq hw'
      by_cases hpq : p = q
      · subst hpq; rw [hv'] at hw'; exact Option.some_injective _ hw'
      rcases o1 with rfl | o1
      · rcases o2 with rfl | o2
        · rfl
        · exact echo_unique hR (o2 p ((hc p).mp hp)) e1 |>.symm
      · exact echo_unique hR (o1 q ((hc q).mp hq)) e2
  integrity := by
    intro mo E hFT hs p i v _ hv
    have hall : ∀ r, E.Correct r := by
      intro r
      by_contra hr
      have : r ∈ faultySet E := by classical simp [faultySet, hr]
      have hs' : (0 : Fin 3) ∉ faultySet E := by classical simp [faultySet, hs]
      simp only [T3, Set.mem_insert_iff, Set.mem_singleton_iff] at hFT
      rcases hFT with h | h <;> rw [h] at this hs' <;> simp_all
    exact dec_eq (E.reachable i) (Set.eq_empty_iff_forall_notMem.mpr fun r => hall r i) hv

/-- The paper's Local Progress holds (with the default value `0`). -/
theorem alg_localProgress : LocalProgress T3 0 alg := by
  intro p Q hQ
  refine ⟨0, ?_⟩
  let σ1 : State (Fin 3) Msg ℕ := { (State.init : State (Fin 3) Msg ℕ) with
    sent := insert (0, Msg.val 0) ∅ }
  have h1 : Step alg (srcInput 0 (some 0)) .byzantine (Fintype.card (Fin 3)) State.init σ1 :=
    Step.send _ 0 (Msg.val 0) (by simp [State.init]) (by simp [alg, srcInput])
  by_cases hp0 : p = 0
  · subst hp0
    have hQ' : Q = Finset.univ := by simpa [T3] using hQ
    subst hQ'
    let σ2 : State (Fin 3) Msg ℕ := { σ1 with dec := Function.update σ1.dec 0 (some 0) }
    have h2 : Step alg (srcInput 0 (some 0)) .byzantine (Fintype.card (Fin 3)) σ1 σ2 :=
      Step.decide _ 0 0 (by simp [σ1, State.init]) (by simp [σ1, State.init])
        (Or.inl (by simp [srcInput]))
    exact ⟨σ2, (Relation.ReflTransGen.refl.tail h1).tail h2, by simp [σ2, σ1, State.init],
      by simp [σ2], fun _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ => by simp⟩
  · have hpQ : p ∈ Q := T3_selfMem p Q hQ
    have hQ0 : (0 : Fin 3) ∈ Q := by
      fin_cases p <;> simp [T3] at hQ hp0 <;> subst hQ <;> decide
    let σ2 : State (Fin 3) Msg ℕ := { σ1 with rcv := insert (p, 0, Msg.val 0) ∅ }
    let σ3 : State (Fin 3) Msg ℕ := { σ2 with sent := insert (p, Msg.echo 0) σ2.sent }
    let σ4 : State (Fin 3) Msg ℕ := { σ3 with dec := Function.update σ3.dec p (some 0) }
    have h2 : Step alg (srcInput 0 (some 0)) .byzantine (Fintype.card (Fin 3)) σ1 σ2 :=
      Step.deliver _ p 0 (Msg.val 0) (by simp [σ1])
    have h3 : Step alg (srcInput 0 (some 0)) .byzantine (Fintype.card (Fin 3)) σ2 σ3 :=
      Step.send _ p (Msg.echo 0) (by simp [σ2, σ1, State.init])
        ⟨by simp [σ2, State.inbox], fun w => by simp [σ2, σ1, State.out, hp0]⟩
    have h4 : Step alg (srcInput 0 (some 0)) .byzantine (Fintype.card (Fin 3)) σ3 σ4 :=
      Step.decide _ p 0 (by simp [σ3, σ2, σ1, State.init]) (by simp [σ3, σ2, σ1, State.init])
        (Or.inr (Or.inl ⟨by simp [σ3, State.out], rfl⟩))
    refine ⟨σ4, (((Relation.ReflTransGen.refl.tail h1).tail h2).tail h3).tail h4,
      by simp [σ4, σ3, σ2, σ1, State.init], by simp [σ4], ?_, ?_, ?_⟩
    · intro q m hq
      simp only [σ4, σ3, σ2, σ1, Set.mem_insert_iff, Prod.mk.injEq, Set.mem_empty_iff_false,
        or_false] at hq
      rcases hq with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Finset.mem_insert_of_mem hpQ
      · exact Finset.mem_insert_self _ _
    · intro q r m hq
      simp only [σ4, σ3, σ2, Set.mem_insert_iff, Prod.mk.injEq, Set.mem_empty_iff_false,
        or_false] at hq
      rw [hq.1]; exact Finset.mem_insert_of_mem hpQ
    · intro q hq
      by_cases hqp : q = p
      · rw [hqp]; exact Finset.mem_insert_of_mem hpQ
      · simp [σ4, σ3, σ2, σ1, State.init, Function.update_of_ne hqp] at hq

/-- Per-value Local Progress fails: process `1` alone with the source cannot deliver `1`. -/
theorem alg_not_localProgressAll : ¬ LocalProgressAll T3 0 alg := by
  intro h
  obtain ⟨σ, hR, hbad, hd, hS, -, -⟩ := h 1 {0, 1} (by simp [T3]) 1
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hd
  have hv1 : v = 1 := (Option.some_injective _ (dec_eq hR hbad hv)).symm
  subst hv1
  have hJ := hR.dec_just (J := fun p v ib out => srcInput 0 (some 1) p = some v ∨
      (Msg.echo v ∈ out ∧ v = 0) ∨ ∀ q : Fin 3, q ≠ 0 → Msg.echo v ∈ ib q)
    (fun _ _ _ _ _ _ hib hout h => h.imp_right (Or.imp (fun h => ⟨hout h.1, h.2⟩)
      fun h q hq => hib q (h q hq))) (fun _ _ _ _ h => h) hv
  rcases hJ with h1 | ⟨-, h2⟩ | h1
  · simp [srcInput] at h1
  · exact absurd h2 (by decide)
  · have := hR.genuine (h1 2 (by decide)) (by simp [hbad])
    have := hS 2 _ this
    revert this; decide

/-- **Theorem 5.1 needs per-value Local Progress.** In `T3` the source `0` is faulty in the only
faulty set realizing `k_max = λ_0 = 2`, the algorithm `alg` satisfies the paper's Local Progress
and implements `1`-CB; it does not satisfy per-value Local Progress. -/
theorem theorem_5_1_needs_localProgressAll :
    T3.SelfMem ∧ T3.DownClosed ∧ inconsistencyNumber T3 = 2 ∧
      srcInconsistencyNumber T3 0 = 2 ∧ IsKCB T3 0 1 alg ∧ LocalProgress T3 0 alg ∧
      ¬ LocalProgressAll T3 0 alg :=
  ⟨T3_selfMem, T3_downClosed, T3_inconsistencyNumber, T3_srcInconsistencyNumber, alg_isKCB,
    alg_localProgress, alg_not_localProgressAll⟩

end WeakLP

end Podc.MultipleSpending
