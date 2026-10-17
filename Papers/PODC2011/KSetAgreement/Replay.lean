import Papers.PODC2011.KSetAgreement.Model

/-!
# Replaying group-local executions (partitioning arguments)

Generic facts about CSLib's asynchronous model (`Cslib.FLP.Algorithm`), used for the partitioning
arguments of the paper:

* `AgreeOn G s t`: the processes of `G` have the same local states in `s` and `t`, and every
  message in flight to `G` in `s` is also in flight in `t`.
* `replay_mTr`: an execution in which only processes of `G` take steps can be replayed from any
  state that agrees on `G`, also for a different algorithm that behaves identically on `G`.
* `agreeOn_mTr_outside`: steps of processes outside `G` preserve agreement on `G`.
* `neverSteps_procFaulty`: a process that never takes a step is faulty (its wake-up message stays
  in flight).
-/

namespace KSetAgreement

open Cslib Cslib.FLP

variable {P M L : Type*} [DecidableEq P] [DecidableEq M]

-- CSLib candidate: `AgreeOn`, `SameOn`, `replay_mTr`, `agreeOn_mTr_outside` (locality of
-- executions in `Cslib.FLP`).

open Classical in
/-- `s` and `t` agree on the processes of `G`: same local states, and the messages in flight to
`G` in `s` are a sub-multiset of those in `t`. -/
def AgreeOn (G : Set P) (s t : State P M L) : Prop :=
  (∀ p ∈ G, s.proc p = t.proc p) ∧
    s.msgs.filter (fun m => m.dest ∈ G) ≤ t.msgs.filter (fun m => m.dest ∈ G)

/-- Two algorithms behave identically at the processes of `G`. -/
def SameOn (G : Set P) (a₁ a₂ : Algorithm P M L) : Prop :=
  ∀ m : Message P M, m.dest ∈ G → ∀ ps,
    a₁.next m ps = a₂.next m ps ∧ a₁.send m ps = a₂.send m ps ∧ a₁.out m ps = a₂.out m ps

omit [DecidableEq P] [DecidableEq M] in
theorem AgreeOn.refl (G : Set P) (s : State P M L) : AgreeOn G s s := ⟨fun _ _ => rfl, le_rfl⟩

theorem multiset_filter_erase {α : Type*} [DecidableEq α] (q : α → Prop) [DecidablePred q]
    (s : Multiset α) (a : α) (ha : q a) : (s.erase a).filter q = (s.filter q).erase a := by
  by_cases h : a ∈ s
  · conv_rhs => rw [← Multiset.cons_erase h]
    rw [Multiset.filter_cons_of_pos _ ha, Multiset.erase_cons_head]
  · rw [Multiset.erase_of_notMem h, Multiset.erase_of_notMem]
    exact fun h' => h (Multiset.mem_of_mem_filter h')

theorem multiset_filter_erase_neg {α : Type*} [DecidableEq α] (q : α → Prop) [DecidablePred q]
    (s : Multiset α) (a : α) (ha : ¬ q a) : (s.erase a).filter q = s.filter q := by
  by_cases h : a ∈ s
  · conv_rhs => rw [← Multiset.cons_erase h]
    rw [Multiset.filter_cons_of_neg _ ha]
  · rw [Multiset.erase_of_notMem h]

/-- One step of a process of `G` can be replayed. -/
theorem replay_tr {G : Set P} {a₁ a₂ : Algorithm P M L} (hsame : SameOn G a₁ a₂)
    {s t s' : State P M L} {x : Action P M} (hag : AgreeOn G s t) (htr : a₁.lts.Tr s x s')
    (hx : DestIn G x) : ∃ t', a₂.lts.Tr t x t' ∧ AgreeOn G s' t' := by
  classical
  cases x with
  | none =>
    have : s' = s := htr
    subst this
    exact ⟨t, rfl, hag⟩
  | some m =>
    obtain ⟨hm, rfl⟩ := htr
    have hd : m.dest ∈ G := hx
    have hmt : m ∈ t.msgs := by
      have h1 : m ∈ s.msgs.filter (fun m => m.dest ∈ G) := Multiset.mem_filter.2 ⟨hm, hd⟩
      have h2 := Multiset.mem_of_le (by simpa using hag.2) h1
      exact (Multiset.mem_filter.1 h2).1
    obtain ⟨hn, hs, ho⟩ := hsame m hd (s.proc m.dest)
    refine ⟨a₂.recvMsg m t, ⟨hmt, rfl⟩, ?_, ?_⟩
    · intro p hp
      have heq := hag.1 _ hd
      simp only [Algorithm.recvMsg]
      by_cases h : p = m.dest
      · subst h
        simp only [↓reduceIte]
        rw [hn, ho, heq]
      · simp only [h, ↓reduceIte]
        exact hag.1 p hp
    · simp only [Algorithm.recvMsg]
      rw [← hag.1 _ hd, ← hs]
      simp only [Multiset.filter_add]
      have e1 := multiset_filter_erase (fun m : Message P M => m.dest ∈ G) s.msgs m hd
      have e2 := multiset_filter_erase (fun m : Message P M => m.dest ∈ G) t.msgs m hd
      have := add_le_add (Multiset.erase_le_erase m hag.2)
        (le_refl ((a₁.send m (s.proc m.dest)).filter (fun m : Message P M => m.dest ∈ G)))
      convert this using 2

/-- An execution in which only processes of `G` take steps can be replayed. -/
theorem replay_mTr {G : Set P} {a₁ a₂ : Algorithm P M L} (hsame : SameOn G a₁ a₂)
    {s t s' : State P M L} {xl : List (Action P M)} (hag : AgreeOn G s t)
    (hmtr : a₁.lts.MTr s xl s') (hx : ∀ x ∈ xl, DestIn G x) :
    ∃ t', a₂.lts.MTr t xl t' ∧ AgreeOn G s' t' := by
  induction hmtr generalizing t with
  | refl => exact ⟨t, LTS.MTr.refl, hag⟩
  | stepL htr _ ih =>
    obtain ⟨t₁, ht₁, hag₁⟩ := replay_tr hsame hag htr (hx _ (List.mem_cons_self ..))
    obtain ⟨t', ht', hag'⟩ := ih hag₁ (fun x hx' => hx x (List.mem_cons_of_mem _ hx'))
    exact ⟨t', LTS.MTr.stepL ht₁ ht', hag'⟩

/-- A step of a process outside `G` preserves agreement on `G`. -/
theorem agreeOn_tr_outside {G : Set P} {a : Algorithm P M L} {s t t' : State P M L}
    {x : Action P M} (hag : AgreeOn G s t) (htr : a.lts.Tr t x t') (hx : DestIn Gᶜ x) :
    AgreeOn G s t' := by
  classical
  cases x with
  | none =>
    have : t' = t := htr
    subst this
    exact hag
  | some m =>
    obtain ⟨_, rfl⟩ := htr
    have hd : m.dest ∉ G := hx
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [Algorithm.recvMsg]
      have hne : p ≠ m.dest := by rintro rfl; exact hd hp
      simp only [hne, ↓reduceIte]
      exact hag.1 p hp
    · simp only [Algorithm.recvMsg, Multiset.filter_add]
      have e1 := multiset_filter_erase_neg (fun m : Message P M => m.dest ∈ G) t.msgs m hd
      refine le_trans hag.2 (le_trans (le_of_eq ?_) (Multiset.le_add_right _ _))
      convert e1.symm

/-- Steps of processes outside `G` preserve agreement on `G`. -/
theorem agreeOn_mTr_outside {G : Set P} {a : Algorithm P M L} {s t t' : State P M L}
    {xl : List (Action P M)} (hag : AgreeOn G s t) (hmtr : a.lts.MTr t xl t')
    (hx : ∀ x ∈ xl, DestIn Gᶜ x) : AgreeOn G s t' := by
  induction hmtr with
  | refl => exact hag
  | stepL htr _ ih =>
    exact ih (agreeOn_tr_outside hag htr (hx _ (List.mem_cons_self ..)))
      (fun x hx' => hx x (List.mem_cons_of_mem _ hx'))

omit [DecidableEq P] [DecidableEq M] in
/-- `DestIn` is monotone. -/
theorem DestIn.mono {G H : Set P} {x : Action P M} (h : DestIn G x) (hGH : G ⊆ H) :
    DestIn H x := by
  cases x with
  | none => trivial
  | some m => exact hGH h

/-- A process that never takes a step is faulty: its wake-up message stays in flight. -/
theorem neverSteps_procFaulty [Fintype P] {a : Algorithm P M L} {inp : P → Bool}
    {ss : ωSequence (State P M L)} {xs : ωSequence (Action P M)} (hrun : IsRun a inp ss xs)
    {p : P} (hp : NeverSteps p xs) : ProcFaulty p ss xs := by
  refine ⟨0, ⟨⟨p, Sum.inl (inp p)⟩, ?_, rfl⟩, fun j _ m' hj => hp j m' hj⟩
  rw [hrun.1]
  simp [Algorithm.start]

end KSetAgreement
