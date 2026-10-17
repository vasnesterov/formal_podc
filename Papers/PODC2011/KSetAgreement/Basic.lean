import Papers.PODC2011.KSetAgreement.Replay

/-!
# Basic facts about compiled `KAlgorithm`s

* decisions are stable (`dec_stable_mTr`);
* CSLib's Boolean output field mirrors the decision (`out_eq`);
* wake-up messages carry the initial bits (`wake_bit`);
* `solo_prefix`: if `A` terminates in the solo runs of a group `G` (everybody else never takes a
  step), then there is a finite execution in which only `G` takes steps and all of `G` decides;
* `merge`: finite executions of pairwise disjoint groups can be merged into one execution
  (partitioning argument: no group hears from another one).
-/

namespace KSetAgreement

open Cslib Cslib.FLP

variable {P M S V : Type*} [DecidableEq P] [DecidableEq M]

namespace KAlgorithm

variable (A : KAlgorithm P M S V)

omit [DecidableEq P] [DecidableEq M] in
@[simp] theorem decOf_nextLoc_of_some (ι : P → Bool → V) (p : P) (msg : Bool ⊕ M)
    (l : Loc M S V) (v : V) (h : decOf l = some v) : decOf (A.nextLoc ι p msg l) = some v := by
  rcases l with buf | st
  · simp [decOf] at h
  · rcases msg with b | m
    · simpa [nextLoc] using h
    · simp only [decOf] at h
      simp [nextLoc, decOf, apply, h]

end KAlgorithm

/-- Decisions are stable under steps. -/
theorem dec_stable_tr {A : KAlgorithm P M S V} {ι : P → Bool → V} {δ : V → Bool}
    {s s' : State P M (Loc M S V)} {x : Action P M} (htr : (A.alg ι δ).lts.Tr s x s')
    {p : P} {v : V} (h : dec s p = some v) : dec s' p = some v := by
  cases x with
  | none =>
    have : s' = s := htr
    subst this; exact h
  | some m =>
    obtain ⟨_, rfl⟩ := htr
    by_cases hp : p = m.dest
    · subst hp
      simp only [dec, Algorithm.recvMsg, ↓reduceIte, KAlgorithm.alg]
      exact A.decOf_nextLoc_of_some ι _ _ _ v h
    · simpa [dec, Algorithm.recvMsg, hp] using h

/-- Decisions are stable under executions. -/
theorem dec_stable_mTr {A : KAlgorithm P M S V} {ι : P → Bool → V} {δ : V → Bool}
    {s s' : State P M (Loc M S V)} {xl : List (Action P M)} (h : (A.alg ι δ).lts.MTr s xl s')
    {p : P} {v : V} (hd : dec s p = some v) : dec s' p = some v := by
  induction h with
  | refl => exact hd
  | stepL htr _ ih => exact ih (dec_stable_tr htr hd)

/-- Decisions are stable along infinite executions. -/
theorem dec_stable_omega {A : KAlgorithm P M S V} {ι : P → Bool → V} {δ : V → Bool}
    {ss : ωSequence (State P M (Loc M S V))} {xs : ωSequence (Action P M)}
    (h : (A.alg ι δ).lts.OmegaExecution ss xs) {i j : ℕ} (hij : i ≤ j) {p : P} {v : V}
    (hd : dec (ss i) p = some v) : dec (ss j) p = some v :=
  dec_stable_mTr (LTS.OmegaExecution.extract_mTr h hij) hd

/-- Invariant: CSLib's Boolean output field is the image of the decision under `δ`, and every
message with a Boolean payload is the wake-up message of its destination. -/
def GoodState (inp : P → Bool) (δ : V → Bool) (s : State P M (Loc M S V)) : Prop :=
  (∀ p, (s.proc p).out = (dec s p).map δ) ∧
    ∀ m ∈ s.msgs, ∀ b, m.msg = Sum.inl b → b = inp m.dest

omit [DecidableEq P] [DecidableEq M] in
theorem goodState_start [Fintype P] (A : KAlgorithm P M S V) (ι : P → Bool → V) (δ : V → Bool)
    (inp : P → Bool) : GoodState inp δ ((A.alg ι δ).start inp) := by
  refine ⟨fun p => by simp [Algorithm.start, dec, KAlgorithm.alg, KAlgorithm.decOf], ?_⟩
  intro m hm b hb
  simp only [Algorithm.start, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hm
  obtain ⟨p, rfl⟩ := hm
  simpa using hb.symm

theorem goodState_tr (A : KAlgorithm P M S V) (ι : P → Bool → V) (δ : V → Bool)
    (inp : P → Bool) {s s' : State P M (Loc M S V)} {x : Action P M}
    (hg : GoodState inp δ s) (htr : (A.alg ι δ).lts.Tr s x s') : GoodState inp δ s' := by
  cases x with
  | none =>
    have : s' = s := htr
    subst this; exact hg
  | some m =>
    obtain ⟨hm, rfl⟩ := htr
    refine ⟨fun p => ?_, ?_⟩
    · simp only [Algorithm.recvMsg, dec]
      split_ifs with hp h1
      · subst hp
        simp [KAlgorithm.alg]
      · subst hp
        have h2 := hg.1 m.dest
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (by simpa using h1)
        rw [hb] at h2 ⊢
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h2.symm
        have := (A.decOf_nextLoc_of_some ι m.dest m.msg _ v hv)
        simp only [KAlgorithm.alg]
        rw [this]; rfl
      · exact hg.1 p
    · intro m' hm' b hb
      simp only [Algorithm.recvMsg, Multiset.mem_add] at hm'
      rcases hm' with hm' | hm'
      · exact hg.2 m' (Multiset.mem_of_mem_erase hm') b hb
      · simp only [KAlgorithm.alg, Multiset.mem_map] at hm'
        obtain ⟨qm, _, rfl⟩ := hm'
        simp [KAlgorithm.wrap] at hb

theorem goodState_mTr (A : KAlgorithm P M S V) (ι : P → Bool → V) (δ : V → Bool)
    (inp : P → Bool) {s s' : State P M (Loc M S V)} {xl : List (Action P M)}
    (hg : GoodState inp δ s) (h : (A.alg ι δ).lts.MTr s xl s') : GoodState inp δ s' := by
  induction h with
  | refl => exact hg
  | stepL htr _ ih => exact ih (goodState_tr A ι δ inp hg htr)

theorem goodState_of_reachable [Fintype P] (A : KAlgorithm P M S V) (ι : P → Bool → V)
    (δ : V → Bool) (inp : P → Bool) {s : State P M (Loc M S V)}
    (h : (A.alg ι δ).Reachable inp s) : GoodState inp δ s := by
  obtain ⟨xl, hxl⟩ := h
  exact goodState_mTr A ι δ inp (goodState_start A ι δ inp) hxl

omit [DecidableEq P] [DecidableEq M] in
/-- Algorithms with input assignments that coincide on `G` behave identically on `G`. -/
theorem sameOn_algX (A : KAlgorithm P M S V) {G : Set P} {x y : P → V}
    (h : ∀ p ∈ G, x p = y p) : SameOn G (A.algX x) (A.algX y) := by
  intro m hm ps
  simp only [KAlgorithm.alg, KAlgorithm.nextLoc, KAlgorithm.sendLoc, h _ hm, and_self]

omit [DecidableEq P] [DecidableEq M] in
theorem mem_extract {α : Type*} {xs : ωSequence α} {m n : ℕ} {a : α} (h : a ∈ xs.extract m n) :
    ∃ i, xs i = a := by
  rw [ωSequence.extract_eq_ofFn, List.mem_ofFn] at h
  obtain ⟨k, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- **Solo prefixes.** If `A` terminates in every infinite execution in which exactly the processes
of `G` take steps and are correct, then there is a finite execution from the initial state in which
only processes of `G` take steps and at the end of which every process of `G` has decided. -/
theorem solo_prefix [Fintype P] (A : KAlgorithm P M S V) (R : RunPred P M (Loc M S V))
    (hT : Terminates A R) (x : P → V) (inp : P → Bool) (G : Finset P)
    (hR : ∀ ss xs, IsRun (A.algX x) inp ss xs → (∀ j, DestIn (↑G : Set P) (xs j)) →
      (∀ p ∈ G, ProcFair p ss xs) → R (A.algX x) inp ss xs) :
    ∃ xl s, (A.algX x).lts.MTr ((A.algX x).start inp) xl s ∧ (∀ a ∈ xl, DestIn (↑G : Set P) a) ∧
      ∀ p ∈ G, ∃ v, dec s p = some v := by
  classical
  set a := A.algX x
  let d : DeliverMsg P M (Loc M S V) := fun s m =>
    if m.dest ∈ G then ([some m], a.recvMsg m s) else ([none], s)
  have hd : a.FairDeliverMsg d (↑G : Set P) (fun _ => True) := by
    intro s m ⟨hm, hG, _⟩
    simp only [d, show m.dest ∈ G from hG, ↓reduceIte]
    exact ⟨LTS.MTr.single _ ⟨hm, rfl⟩, List.mem_singleton_self _, trivial⟩
  have hda : d.ForallActions (DestIn (↑G : Set P)) := by
    intro s m
    simp only [d]
    split_ifs with h
    · simpa [DestIn] using h
    · simp [DestIn]
  obtain ⟨ss, hex, h0, -, -, -, hfair⟩ :=
    FairScheduler.fair_omegaExecution hd (a.start inp) trivial
  have hdest := FairScheduler.omega_forall_actions hd (a.start inp) trivial hda trivial
  set xs := (a.fairSegActions d (↑G : Set P) (a.start inp)).flatten
  have hrun : IsRun a inp ss xs := ⟨h0, hex⟩
  have hdec : ∀ p ∈ G, ∃ j, ∃ v, dec (ss j) p = some v := by
    intro p hp
    rcases hT x inp ss xs (hR ss xs hrun hdest hfair) p with hf | h
    · exact absurd ⟨hf, hfair p hp⟩ (not_procFaulty_and_procFair p ss xs)
    · exact h
  choose! J hJ using hdec
  let K := G.sup J
  refine ⟨xs.extract 0 K, ss K, ?_, ?_, ?_⟩
  · rw [← h0]; exact LTS.OmegaExecution.extract_mTr hex (Nat.zero_le _)
  · intro y hy
    obtain ⟨i, rfl⟩ := mem_extract hy
    exact hdest i
  · intro p hp
    obtain ⟨v, hv⟩ := hJ p hp
    exact ⟨v, dec_stable_omega hex (Finset.le_sup hp) hv⟩

/-- **Merging.** Let `G i` (`i ∈ l`) be pairwise disjoint groups, and for each `i` let `xl i` be a
finite execution from the initial state, with input assignment `y i` agreeing with `x` on `G i`, in
which only processes of `G i` take steps, ending in `s i`. Then there is a state reachable with
inputs `x` in which every process of every `G i` has the same local state as in `s i`. -/
theorem merge [Fintype P] (A : KAlgorithm P M S V) (x : P → V) (inp : P → Bool) {ι : Type*}
    (G : ι → Set P) (y : ι → P → V) (hy : ∀ i, ∀ p ∈ G i, y i p = x p)
    (xl : ι → List (Action P M)) (s : ι → State P M (Loc M S V))
    (hxl : ∀ i, (A.algX (y i)).lts.MTr ((A.algX (y i)).start inp) (xl i) (s i))
    (hdest : ∀ i, ∀ a ∈ xl i, DestIn (G i) a) :
    ∀ l : List ι, l.Pairwise (fun i j => Disjoint (G i) (G j)) →
      ∃ zl t, (A.algX x).lts.MTr ((A.algX x).start inp) zl t ∧
        (∀ a ∈ zl, DestIn (⋃ i ∈ l, G i) a) ∧ ∀ i ∈ l, ∀ p ∈ G i, t.proc p = (s i).proc p := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨[], _, LTS.MTr.refl, by simp, by simp⟩
  | cons j l ih =>
    intro hpw
    rw [List.pairwise_cons] at hpw
    obtain ⟨zl, t, ht, hzl, hag⟩ := ih hpw.2
    -- the initial states of all `algX` coincide
    have hstart : (A.algX (y j)).start inp = (A.algX x).start inp := rfl
    -- `t` agrees with the initial state on `G j`, since only other groups took steps
    have h1 : AgreeOn (G j) ((A.algX (y j)).start inp) t := by
      rw [hstart]
      refine agreeOn_mTr_outside (AgreeOn.refl _ _) ht (fun a ha => DestIn.mono (hzl a ha) ?_)
      intro p hp hpj
      simp only [Set.mem_iUnion] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      exact Set.disjoint_left.1 (hpw.1 i hi) hpj hpi
    obtain ⟨t', ht', hag'⟩ := replay_mTr (sameOn_algX A (hy j)) h1 (hxl j) (hdest j)
    refine ⟨zl ++ xl j, t', LTS.MTr.comp _ ht ht', ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · refine DestIn.mono (hzl a ha) ?_
        intro p hp
        simp only [Set.mem_iUnion, List.mem_cons] at hp ⊢
        obtain ⟨i, hi, hpi⟩ := hp
        exact ⟨i, Or.inr hi, hpi⟩
      · refine DestIn.mono (hdest j a ha) ?_
        intro p hp
        simp only [Set.mem_iUnion, List.mem_cons]
        exact ⟨j, Or.inl rfl, hp⟩
    · intro i hi p hp
      rcases List.mem_cons.1 hi with rfl | hi
      · exact (hag'.1 p hp).symm
      · have h2 : AgreeOn (G i) t t := AgreeOn.refl _ _
        have h3 := agreeOn_mTr_outside h2 ht' (fun a ha => DestIn.mono (hdest j a ha) (by
          intro q hq hqi
          exact Set.disjoint_left.1 (hpw.1 i hi) hq hqi))
        rw [← h3.1 p hp]
        exact hag i hi p hp

end KSetAgreement
