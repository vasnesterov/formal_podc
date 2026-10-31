import Papers.PODC2011.SimultaneousAllCaseOptimal.Consensus

/-!
# Connectivity of the similarity graph at times 0 and 1

Indistinguishability chains for an arbitrary protocol, for complete sets of input vectors:
* at time `0` all runs are connected (`n ≥ 2`): `connected_zero`;
* at time `1`, with `n ≥ 3` and `t ≥ 1`, all failure-free runs are connected (silence one process
  in round 1 one receiver at a time, change its input, and restore it): `connected_one_ffRun`;
* with `t = 1` and `n ≥ 3`, all runs are connected at time `1`: `connected_one_t1`.

Consequences: Lemma 5 holds for `t = 1`, `n ≥ 3` (`lemma5_t1`, non-vacuity of the hypothesis of
Theorem 6), and consensus needs two rounds for `n ≥ 3`, `1 ≤ t < n` (`consensus_lb_two`).
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I M O : Type} [Fintype P]

/-! ### Toolkit: similarity and connectivity -/

omit [Fintype P] in
lemma Similar.symm {A : Protocol P I M O} {k : ℕ} {r r' : Run P I} (h : Similar A k r r') :
    Similar A k r' r := by
  obtain ⟨p, h1, h2, h3, h4⟩ := h
  exact ⟨p, h2, h1, h3.symm, h4.symm⟩

lemma Connected.symm {A : Protocol P I M O} {T : Task P I O} {t k : ℕ} {r r' : Run P I}
    (h : Connected A T t k r r') : Connected A T t k r' r := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.head ⟨hs.2.1, hs.1, hs.2.2.symm⟩ ih

lemma Connected.trans {A : Protocol P I M O} {T : Task P I O} {t k : ℕ} {r r' r'' : Run P I}
    (h : Connected A T t k r r') (h' : Connected A T t k r' r'') : Connected A T t k r r'' :=
  Relation.ReflTransGen.trans h h'

lemma Connected.of_similar {A : Protocol P I M O} {T : Task P I O} {t k : ℕ} {r r' : Run P I}
    (hr : T.IsRun t r) (hr' : T.IsRun t r') (h : Similar A k r r') : Connected A T t k r r' :=
  Relation.ReflTransGen.single ⟨hr, hr', h⟩

omit [Fintype P] in
/-- Two runs are similar at time `0` via any process alive at `0` in both with the same input. -/
lemma similar_zero {A : Protocol P I M O} {r r' : Run P I} (p : P) (hp : r.Alive p 0)
    (hp' : r'.Alive p 0) (hin : r.input p = r'.input p) : Similar A 0 r r' :=
  ⟨p, hp, hp', hin, rfl⟩

omit [Fintype P] in
/-- Two runs are similar at time `1` via `q` if `q` survives round `1` in both, has the same
input, and receives round-`1` messages from the same senders, which have the same inputs. -/
lemma similar_one_of {A : Protocol P I M O} {r r' : Run P I} (q : P) (hq : r.Alive q 1)
    (hq' : r'.Alive q 1) (hin : r.input q = r'.input q)
    (hd : ∀ s, s ≠ q → (r.Deliv s q 0 ↔ r'.Deliv s q 0))
    (hds : ∀ s, s ≠ q → r.Deliv s q 0 → r.input s = r'.input s) : Similar A 1 r r' := by
  refine ⟨q, hq, hq', hin, ?_⟩
  show hist A r 0 q ++ [fun s => msg A r s q 0] = hist A r' 0 q ++ [fun s => msg A r' s q 0]
  simp only [Cslib.SyncCrash.hist_zero, List.nil_append, List.cons.injEq, and_true]
  funext s
  rw [msg_eq_deliv, msg_eq_deliv]
  by_cases hs : s = q
  · subst hs; simp
  · by_cases h : r.Deliv s q 0
    · rw [ite_eq_left ⟨hs, h⟩, ite_eq_left ⟨hs, (hd s hs).1 h⟩, hds s hs h]; rfl
    · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right (fun h' => h ((hd s hs).2 h'.2))]

/-- Changing input vectors one coordinate at a time. -/
lemma reflTransGen_ffRun {R : Run P I → Run P I → Prop}
    (h : ∀ (ι ι' : P → I) (p : P), (∀ q, q ≠ p → ι q = ι' q) →
      Relation.ReflTransGen R (ffRun ι) (ffRun ι'))
    (ι ι' : P → I) : Relation.ReflTransGen R (ffRun ι) (ffRun ι') := by
  classical
  have key : ∀ F : Finset P, ∀ ι, (∀ q, q ∉ F → ι q = ι' q) →
      Relation.ReflTransGen R (ffRun ι) (ffRun ι') := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro ι hι
      have : ι = ι' := funext fun q => hι q (by simp)
      rw [this]
    | insert a F ha ih =>
      intro ι hι
      refine (h ι (Function.update ι a (ι' a)) a fun q hq => ?_).trans (ih _ fun q hq => ?_)
      · rw [Function.update_of_ne hq]
      · by_cases hqa : q = a
        · subst hqa; simp
        · rw [Function.update_of_ne hqa]; exact hι q (by simp [hqa, hq])
  exact key Finset.univ ι (by simp)

lemma exists_ne_ne (hn : 3 ≤ Fintype.card P) (p a : P) : ∃ b, b ≠ p ∧ b ≠ a := by
  classical
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({p, a} : Finset P)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact lt_of_le_of_lt (Finset.card_le_two) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  exact ⟨b, hb.1, hb.2⟩

lemma ffRun_isRun' {T : Task P I O} (hT : T.inputs = Set.univ) (t : ℕ) (ι : P → I) :
    T.IsRun t (ffRun ι) :=
  ffRun_isRun t (by rw [hT]; exact Set.mem_univ _)

lemma ffRun_deliv {ι : P → I} (s q : P) (t : ℕ) : (ffRun ι).Deliv s q t :=
  Run.deliv_of_not_faulty (ffRun_not_faulty s) q t

lemma ffRun_alive {ι : P → I} (q : P) (m : ℕ) : (ffRun ι).Alive q m :=
  Run.alive_of_not_faulty (ffRun_not_faulty q) m

/-! ### Runs with one crash in round `1` -/

/-- The run with inputs `ι` in which only `p` crashes, in round `1`, still reaching `S`. -/
def crash1 [DecidableEq P] (ι : P → I) (p : P) (S : Set P) : Run P I :=
  ⟨ι, fun q => if q = p then some 1 else none, fun _ => S⟩

section crash1

variable [DecidableEq P]

omit [Fintype P] in
lemma crash1_alive_one {ι : P → I} {p q : P} {S : Set P} (hq : q ≠ p) :
    (crash1 ι p S).Alive q 1 := by
  intro c hc; simp [crash1, hq] at hc

omit [Fintype P] in
lemma crash1_deliv_zero {ι : P → I} {p s q : P} {S : Set P} :
    (crash1 ι p S).Deliv s q 0 ↔ (s = p → q ∈ S) := by
  unfold Run.Deliv Run.Alive crash1
  by_cases hs : s = p <;> simp [hs]

lemma crash1_isRun {T : Task P I O} (hT : T.inputs = Set.univ) {t : ℕ} (ht : 1 ≤ t)
    (ι : P → I) (p : P) (S : Set P) : T.IsRun t (crash1 ι p S) := by
  refine ⟨⟨?_, fun q c hc => ?_⟩, by rw [hT]; exact Set.mem_univ _⟩
  · refine le_trans (Finset.card_le_one.2 fun a ha b hb => ?_) ht
    simp only [Run.mem_faulty, Run.Faulty, crash1] at ha hb
    by_cases hap : a = p
    · by_cases hbp : b = p
      · rw [hap, hbp]
      · simp [hbp] at hb
    · simp [hap] at ha
  · by_cases hq : q = p
    · simp [crash1, hq] at hc; omega
    · simp [crash1, hq] at hc

/-- Removing the receivers of `p`'s round-`1` messages one at a time. -/
lemma conn_crash1_empty {T : Task P I O} (hT : T.inputs = Set.univ)
    (hn : 3 ≤ Fintype.card P) {t : ℕ} (ht : 1 ≤ t) (A : Protocol P I M O) (ι : P → I) (p : P)
    (F : Finset P) : Connected A T t 1 (crash1 ι p ↑F) (crash1 ι p ∅) := by
  induction F using Finset.induction_on with
  | empty => rw [Finset.coe_empty]; exact Relation.ReflTransGen.refl
  | insert a F ha ih =>
    refine Connected.trans (Connected.of_similar (crash1_isRun hT ht _ _ _)
      (crash1_isRun hT ht _ _ _) ?_) ih
    obtain ⟨b, hbp, hba⟩ := exists_ne_ne hn p a
    refine similar_one_of b (crash1_alive_one hbp) (crash1_alive_one hbp) rfl
      (fun s _ => ?_) (fun _ _ _ => rfl)
    simp only [crash1_deliv_zero, Finset.coe_insert, Set.mem_insert_iff, hba, false_or]

lemma conn_crash1_ff {T : Task P I O} (hT : T.inputs = Set.univ)
    (hn : 3 ≤ Fintype.card P) {t : ℕ} (ht : 1 ≤ t) (A : Protocol P I M O) (ι : P → I) (p : P)
    (S : Set P) : Connected A T t 1 (crash1 ι p S) (ffRun ι) := by
  classical
  have h1 : Connected A T t 1 (crash1 ι p S) (crash1 ι p ∅) := by
    have := conn_crash1_empty hT hn ht A ι p S.toFinset
    rwa [Set.coe_toFinset] at this
  have h2 : Connected A T t 1 (crash1 ι p Set.univ) (crash1 ι p ∅) := by
    have := conn_crash1_empty hT hn ht A ι p Finset.univ
    rwa [Finset.coe_univ] at this
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card (by omega) p
  have h3 : Connected A T t 1 (crash1 ι p Set.univ) (ffRun ι) :=
    Connected.of_similar (crash1_isRun hT ht _ _ _) (ffRun_isRun' hT t ι)
      (similar_one_of q (crash1_alive_one hq) (ffRun_alive q 1) rfl
        (fun s _ => by simp [crash1_deliv_zero, ffRun_deliv]) (fun _ _ _ => rfl))
  exact h1.trans (h2.symm.trans h3)

end crash1

/-! ### Main results -/

/-- At time `0` all runs (with complete inputs) are connected, if `n ≥ 2`. -/
theorem connected_zero {T : Task P I O} (hT : T.inputs = Set.univ) (hn : 2 ≤ Fintype.card P)
    {t : ℕ} (A : Protocol P I M O) {r r' : Run P I} (hr : T.IsRun t r) (hr' : T.IsRun t r') :
    Connected A T t 0 r r' := by
  obtain ⟨p₀⟩ : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  have hff : ∀ {r : Run P I}, T.IsRun t r → Connected A T t 0 r (ffRun r.input) := fun hr =>
    Connected.of_similar hr (ffRun_isRun' hT t _)
      (similar_zero p₀ (hr.1.alive_zero p₀) (ffRun_alive p₀ 0) rfl)
  refine (hff hr).trans (Connected.trans ?_ (hff hr').symm)
  refine reflTransGen_ffRun (fun ι ι' p hι => ?_) _ _
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card (by omega) p
  exact Connected.of_similar (ffRun_isRun' hT t _) (ffRun_isRun' hT t _)
    (similar_zero q (ffRun_alive q 0) (ffRun_alive q 0) (hι q hq))

/-- At time `1`, with `n ≥ 3` and `t ≥ 1`, the failure-free runs on any two input vectors are
connected. -/
theorem connected_one_ffRun {T : Task P I O} (hT : T.inputs = Set.univ)
    (hn : 3 ≤ Fintype.card P) {t : ℕ} (ht : 1 ≤ t) (A : Protocol P I M O) (ι ι' : P → I) :
    Connected A T t 1 (ffRun ι) (ffRun ι') := by
  classical
  refine reflTransGen_ffRun (fun ι ι' p hι => ?_) _ _
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card (by omega) p
  have hmid : Connected A T t 1 (crash1 ι p ∅) (crash1 ι' p ∅) :=
    Connected.of_similar (crash1_isRun hT ht _ _ _) (crash1_isRun hT ht _ _ _)
      (similar_one_of q (crash1_alive_one hq) (crash1_alive_one hq) (hι q hq)
        (fun _ _ => Iff.rfl) (fun s _ hs => hι s fun hsp => by
          simp [crash1_deliv_zero, hsp] at hs))
  exact (conn_crash1_ff hT hn ht A ι p ∅).symm.trans
    (hmid.trans (conn_crash1_ff hT hn ht A ι' p ∅))

/-- With at most one crash, a run is connected at time `1` to the failure-free run on its inputs. -/
lemma conn_ffRun_t1 {T : Task P I O} (hT : T.inputs = Set.univ) (hn : 3 ≤ Fintype.card P)
    (A : Protocol P I M O) {r : Run P I} (hr : T.IsRun 1 r) :
    Connected A T 1 1 r (ffRun r.input) := by
  classical
  by_cases h : ∃ p, r.crash p = some 1
  · obtain ⟨p, hp⟩ := h
    have hfp : r.Faulty p := by simp [Run.Faulty, hp]
    have honly : ∀ q, r.Faulty q → q = p := fun q hq =>
      Finset.card_le_one.1 hr.1.1 q (by simpa using hq) p (by simpa using hfp)
    obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card (by omega) p
    have hqf : ¬ r.Faulty q := fun h => hq (honly q h)
    refine Connected.trans (Connected.of_similar hr (crash1_isRun hT le_rfl _ _ _)
      (similar_one_of q (Run.alive_of_not_faulty hqf 1) (crash1_alive_one hq) rfl
        (fun s _ => ?_) (fun _ _ _ => rfl))) (conn_crash1_ff hT hn le_rfl A r.input p (r.reach p))
    rw [crash1_deliv_zero]
    by_cases hsp : s = p
    · subst hsp
      simp only [Run.Deliv, hp, true_and, not_not, forall_const]
      exact ⟨fun h => h.2, fun h => ⟨hr.1.alive_zero _, h⟩⟩
    · simp only [hsp, false_implies, iff_true]
      exact Run.deliv_of_not_faulty (fun h => hsp (honly s h)) q 0
  · push Not at h
    obtain ⟨q⟩ : Nonempty P := Fintype.card_pos_iff.1 (by omega)
    have hal : ∀ s, r.Alive s 1 := fun s c hc => by
      have := hr.1.2 s c hc
      have : c ≠ 1 := fun h1 => h s (h1 ▸ hc)
      omega
    refine Connected.of_similar hr (ffRun_isRun' hT 1 _)
      (similar_one_of q (hal q) (ffRun_alive q 1) rfl (fun s _ => ?_) (fun _ _ _ => rfl))
    simp only [ffRun_deliv, iff_true]
    exact ⟨(hal s).mono (by omega), fun h' => h s h'.1⟩

/-- With `t = 1` and `n ≥ 3`, all runs are connected at time `1`. -/
theorem connected_one_t1 {T : Task P I O} (hT : T.inputs = Set.univ) (hn : 3 ≤ Fintype.card P)
    (A : Protocol P I M O) {r r' : Run P I} (hr : T.IsRun 1 r) (hr' : T.IsRun 1 r') :
    Connected A T 1 1 r r' :=
  (conn_ffRun_t1 hT hn A hr).trans
    ((connected_one_ffRun hT hn le_rfl A _ _).trans (conn_ffRun_t1 hT hn A hr').symm)

/-- Lemma 5 holds for `t = 1`, `n ≥ 3` and complete input sets. -/
theorem lemma5_t1 {T : Task P I O} (hT : T.inputs = Set.univ) (hn : 3 ≤ Fintype.card P) :
    Lemma5Hyp T 1 := by
  intro M A k r r' hr hr' hk _
  have hw := waste_lt hr.1 le_rfl
  unfold Premature at hk
  rcases Nat.lt_or_ge k 1 with h0 | h1
  · obtain rfl : k = 0 := by omega
    exact connected_zero hT (by omega) A hr hr'
  · obtain rfl : k = 1 := by omega
    exact connected_one_t1 hT hn A hr hr'

/-- Consensus on a set with two distinct values needs two rounds when `n ≥ 3` and `1 ≤ t < n`:
`2` is a worst-case lower bound. -/
theorem consensus_lb_two (hn : 3 ≤ Fintype.card P) {t : ℕ} (ht : 1 ≤ t)
    (htn : t < Fintype.card P) {a b : I} (hab : a ≠ b) : WorstCaseLB (consensus P I) t 2 := by
  intro M A k hA
  by_contra hk
  push Not at hk
  have hA1 : SolvesWithin A (consensus P I) t 1 :=
    { toSolves := hA.toSolves
      within := fun r hr p hp => by
        obtain ⟨m, hm, d, hd⟩ := hA.within r hr p hp
        exact ⟨m, by omega, d, hd⟩ }
  have hT : (consensus P I).inputs = Set.univ := rfl
  -- the common decision value is invariant along similarity edges at time `1`
  let Q : Run P I → Prop := fun r => ∀ p m d, Decides A r p m d → d = a
  have hQa : Q (ffRun fun _ => a) := fun p m d hd => by
    obtain ⟨q, hq⟩ := consensus_valid hA.toSolves (ffRun_isRun' hT t _) hd
    exact hq.symm
  have hQ : Q (ffRun fun _ => b) := by
    suffices ∀ r, Connected A (consensus P I) t 1 (ffRun fun _ => a) r → Q r from
      this _ (connected_one_ffRun hT hn ht A (fun _ => a) (fun _ => b))
    intro r hc
    induction hc with
    | refl => exact hQa
    | tail _ hstep ih =>
      obtain ⟨hr₁, hr₂, p, hp₁, hp₂, hin, hh⟩ := hstep
      obtain ⟨m, hm, d, hd⟩ := hA1.decides_of_alive hr₁ hp₁
      have hd₂ : Decides A _ p m d :=
        decides_congr hin (hist_eq_of_le hm hh) (hp₂.mono hm) hd
      intro q m' d' hq
      rw [← consensus_agree hA.toSolves hr₂ hd₂ hq]
      exact ih p m d hd
  obtain ⟨p₀, -⟩ := (ffRun_isRun' hT t (fun _ => b)).exists_correct htn
  obtain ⟨m, d, hd⟩ := hA.complete _ (ffRun_isRun' hT t _) p₀ (ffRun_not_faulty _)
  obtain ⟨q, hq⟩ := consensus_valid hA.toSolves (ffRun_isRun' hT t _) hd
  exact hab ((hQ p₀ m d hd).symm.trans hq.symm)

end Podc.SimultaneousAllCaseOptimal
