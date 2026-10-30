import Papers.PODC2024.SleepyTOB.ExtendedGA

/-!
# The η-sleepy model with one bounded asynchronous period, and the modified Algorithm 1

D'Amato, Losa, Zanolini, PODC 2024, Sections 2.1, 2.3 and 3.3.

**Model** (`Exec`).
* `n` processes (`Fintype P`), rounds `0, 1, 2, …`. `O r`: processes awake at (the beginning of)
  round `r`; `B r ⊆ O r`: Byzantine processes at round `r`; the adversary is *growing*
  (`B r ⊆ B (r+1)`; Byzantine processes never sleep). `H r = O r \ B r`. The processes awake at the
  end of round `r` are those awake at the beginning of round `r + 1`, so the receivers of round
  `r` are `H (r+1)`.
* Messages are vote messages `(sender, round tag, log)` (signed: a message with sender `q` was
  sent by `q`). In every round `t ≥ 1` each `q ∈ H t` multicasts exactly one vote
  `(q, t, vote t q)`; a Byzantine `q ∈ B t` may send any set `byz t` of messages with sender `q`,
  with arbitrary round tags.
* `rcv p r`: messages received by `p` by the end of round `r`. Only sent messages are received,
  received messages are kept (`rcv_mono`), and in a *synchronous* round `r` every `p ∈ H (r+1)` has
  received every message sent in rounds `≤ r` (`rcv_sync`). All rounds are synchronous except the
  rounds `ra + 1, …, ra + π` of the single asynchronous period, in which delivery is arbitrary.
* Message expiration `η`: the GA instance of round `r` is computed by `p ∈ H (r+1)` from the
  *latest* messages with round tag in `[r - η, r]` that `p` has received (`tally`), discarding a
  sender whose latest messages equivocate.

**Protocol** (`Follows`, the modified Algorithm 1, with the input rule of [MMR]). View `v ≥ 1`
consists of rounds `2v - 1` (GA_{v,1}) and `2v` (GA_{v,2}); the GA of round `r` is tallied at
the beginning of round `r + 1`.
* Odd round `r ≥ 3` (round 1 of view `v ≥ 2`): decide every log output with grade 1 by the GA of
  round `r - 1` (`Decides`); let `L` be a longest log output with any grade; vote for (the
  proposal with the highest VRF among those that) extend(s) `L`, or `L` itself. As the adversary
  controls the proposals that can win the VRF lottery, we only require `L <+: vote`.
* Even round `r ≥ 2`: vote for the longest log output with grade 1 by the GA of round `r - 1`
  (if there is one; otherwise the vote is unconstrained).
* Round 1 (view 1): vote for any proposal (unconstrained).

The paper's Algorithm 1 says "not conflicting with `L`" instead of "extending `L`"; that version is
unsafe, see `Counterexample.lean`.
-/

namespace Podc.SleepyTOB

open Finset

noncomputable section
open Classical

variable {P α : Type*}

/-- A vote message: sender, round tag, log. -/
abbrev Msg (P α : Type*) := P × ℕ × List α

/-- The messages sent in round `t`: the honest votes of `H t = O t \ B t` (from round 1 on) and
the messages `byz t` of Byzantine processes. -/
def SentIn (O B : ℕ → Finset P) (vote : ℕ → P → List α) (byz : ℕ → Set (Msg P α)) (t : ℕ)
    (m : Msg P α) : Prop :=
  (1 ≤ t ∧ m.1 ∈ O t \ B t ∧ m.2 = (t, vote t m.1)) ∨ m ∈ byz t

/-- An execution of the modified Algorithm 1's voting layer in the η-sleepy model with a growing
adversary and one asynchronous period `[ra + 1, ra + π]`. -/
structure Exec (P α : Type*) where
  /-- Expiration period. -/
  η : ℕ
  /-- Last synchronous round before the asynchronous period. -/
  ra : ℕ
  /-- Length of the asynchronous period. -/
  π : ℕ
  /-- `O r`: processes awake at round `r`. -/
  O : ℕ → Finset P
  /-- `B r`: Byzantine processes at round `r`. -/
  B : ℕ → Finset P
  B_subset : ∀ r, B r ⊆ O r
  B_mono : ∀ r, B r ⊆ B (r + 1)
  /-- `vote r q`: the vote multicast by `q ∈ H r` in round `r`. -/
  vote : ℕ → P → List α
  /-- Messages sent by Byzantine processes in round `t`. -/
  byz : ℕ → Set (Msg P α)
  byz_sender : ∀ t m, m ∈ byz t → m.1 ∈ B t
  /-- `rcv p r`: messages received by `p` by the end of round `r`. -/
  rcv : P → ℕ → Set (Msg P α)
  rcv_mono : ∀ p r, rcv p r ⊆ rcv p (r + 1)
  rcv_sent : ∀ p r m, m ∈ rcv p r → ∃ t ≤ r, SentIn O B vote byz t m
  rcv_sync : ∀ r, ¬ (ra < r ∧ r ≤ ra + π) → ∀ p ∈ O (r + 1) \ B (r + 1), ∀ t ≤ r, ∀ m,
    SentIn O B vote byz t m → m ∈ rcv p r

namespace Exec

variable (E : Exec P α)

/-- `H r`: honest processes awake at round `r`. -/
def H (r : ℕ) : Finset P := E.O r \ E.B r

/-- `O_{a,b} = ⋃_{a ≤ r' ≤ b} O_{r'}`. -/
def Ow (a b : ℕ) : Finset P := (Icc a b).biUnion E.O

/-- Round `r` is synchronous. -/
def IsSync (r : ℕ) : Prop := ¬ (E.ra < r ∧ r ≤ E.ra + E.π)

/-- Messages sent in round `t`. -/
def Sent (t : ℕ) (m : Msg P α) : Prop := SentIn E.O E.B E.vote E.byz t m

/-- η-sleepiness at round `r` (Equation 3 with `β = 1/3`): `|H_r| > 2/3 |O_{r-η,r}|`. -/
def Sleepy (r : ℕ) : Prop := 2 * #(E.Ow (r - E.η) r) < 3 * #(E.H r)

/-- Equation 4 (with `β = 1/3`): `|H_ra \ B_r| > 2/3 |O_{r-η,r}|` for `r ∈ [ra+1, ra+π+1]`. -/
def Eq4 : Prop :=
  ∀ r, E.ra + 1 ≤ r → r ≤ E.ra + E.π + 1 → 2 * #(E.Ow (r - E.η) r) < 3 * #(E.H E.ra \ E.B r)

/-- Equation 5: `H_ra ⊆ H_{ra+1}`. -/
def Eq5 : Prop := E.H E.ra ⊆ E.H (E.ra + 1)

end Exec

/-! ### Latest messages -/

/-- `l` is the unique latest vote of `q` among the messages `S` with round tag in the window `W`. -/
def IsLatest (S : Set (Msg P α)) (W : ℕ → Prop) (q : P) (l : List α) : Prop :=
  ∃ s, W s ∧ (q, s, l) ∈ S ∧ ∀ s' l', W s' → (q, s', l') ∈ S → s' < s ∨ (s' = s ∧ l' = l)

/-- The latest vote of `q` among the messages `S` with round tag in `W`; `none` if there is no
such message or if the latest ones equivocate. -/
def latest (S : Set (Msg P α)) (W : ℕ → Prop) (q : P) : Option (List α) :=
  if h : ∃ l, IsLatest S W q l then some h.choose else none

theorem IsLatest.unique {S : Set (Msg P α)} {W : ℕ → Prop} {q : P} {l l' : List α}
    (h : IsLatest S W q l) (h' : IsLatest S W q l') : l = l' := by
  obtain ⟨s, hs, hm, hmax⟩ := h
  obtain ⟨s', hs', hm', hmax'⟩ := h'
  rcases hmax s' l' hs' hm' with h1 | ⟨rfl, rfl⟩
  · rcases hmax' s l hs hm with h2 | ⟨rfl, -⟩
    · omega
    · omega
  · rfl

theorem latest_eq_some {S : Set (Msg P α)} {W : ℕ → Prop} {q : P} {l : List α}
    (h : IsLatest S W q l) : latest S W q = some l := by
  have hex : ∃ l, IsLatest S W q l := ⟨l, h⟩
  simp only [latest, hex, ↓reduceDIte]
  exact congrArg some (hex.choose_spec.unique h)

theorem latest_eq_none {S : Set (Msg P α)} {W : ℕ → Prop} {q : P}
    (h : ¬ ∃ l, IsLatest S W q l) : latest S W q = none := by
  simp [latest, h]

theorem latest_eq_some_iff {S : Set (Msg P α)} {W : ℕ → Prop} {q : P} {l : List α} :
    latest S W q = some l ↔ IsLatest S W q l := by
  refine ⟨fun h => ?_, latest_eq_some⟩
  by_cases hex : ∃ l, IsLatest S W q l
  · rw [latest_eq_some hex.choose_spec] at h
    cases h; exact hex.choose_spec
  · rw [latest_eq_none hex] at h; cases h

/-- If all messages of `q` in `S` with tag in a bounded window `W` carry the vote `f s` of their
round tag `s`, and one of them has tag `s₀`, then the latest vote of `q` is `f s` for the largest
such tag `s ≥ s₀`. -/
theorem latest_eq_of_functional {S : Set (Msg P α)} {W : ℕ → Prop} {q : P} (f : ℕ → List α)
    (N : ℕ) (hbdd : ∀ s, W s → s ≤ N) (hfun : ∀ s l, W s → (q, s, l) ∈ S → l = f s)
    {s₀ : ℕ} (hs₀ : W s₀) (hm₀ : (q, s₀, f s₀) ∈ S) :
    ∃ s, s₀ ≤ s ∧ W s ∧ (q, s, f s) ∈ S ∧ latest S W q = some (f s) := by
  let Q : ℕ → Prop := fun s => W s ∧ ∃ l, (q, s, l) ∈ S
  have hQ₀ : Q s₀ := ⟨hs₀, _, hm₀⟩
  set s := Nat.findGreatest Q N with hsdef
  have hQs : Q s := Nat.findGreatest_spec (hbdd s₀ hs₀) hQ₀
  obtain ⟨hWs, l, hl⟩ := hQs
  have hl' := hfun s l hWs hl
  subst hl'
  refine ⟨s, Nat.le_findGreatest (hbdd s₀ hs₀) hQ₀, hWs, hl, latest_eq_some ⟨s, hWs, hl, ?_⟩⟩
  intro s' l' hs' hm'
  have hle : s' ≤ s := Nat.le_findGreatest (hbdd s' hs') ⟨hs', _, hm'⟩
  rcases lt_or_eq_of_le hle with h | h
  · exact Or.inl h
  · subst h; exact Or.inr ⟨rfl, hfun _ _ hs' hm'⟩

/-- No message of `q` in the window: no vote. -/
theorem latest_eq_none_of_forall {S : Set (Msg P α)} {W : ℕ → Prop} {q : P}
    (h : ∀ s l, W s → (q, s, l) ∉ S) : latest S W q = none :=
  latest_eq_none fun ⟨_, s, hs, hm, _⟩ => h s _ hs hm

/-- Splitting the window `W = W' ∪ {r}` at its top tag `r`: the latest vote is the round-`r`
vote if exactly one was received, nothing if round-`r` votes equivocate, and the latest vote in
`W'` if there is no round-`r` vote. This is the correspondence of Section 3.3 between the modified
Algorithm 1 and the extended graded agreement. -/
theorem latest_split (S : Set (Msg P α)) (W W' : ℕ → Prop) (q : P) (r : ℕ)
    (hW : ∀ s, W s ↔ W' s ∨ s = r) (hW' : ∀ s, W' s → s < r) :
    latest S W q =
      if {l | (q, r, l) ∈ S} = ∅ then latest S W' q
      else if hq : ∃ l, {l | (q, r, l) ∈ S} = {l} then some hq.choose else none := by
  have hWr : W r := (hW r).2 (Or.inr rfl)
  by_cases hR : {l | (q, r, l) ∈ S} = ∅
  · simp only [hR, ↓reduceIte]
    have hnot : ∀ l, (q, r, l) ∉ S := fun l hl => by
      have : l ∈ {l | (q, r, l) ∈ S} := hl
      rw [hR] at this; exact this
    have key : ∀ l, IsLatest S W q l ↔ IsLatest S W' q l := by
      intro l
      constructor
      · rintro ⟨s, hs, hm, hmax⟩
        rcases (hW s).1 hs with hs' | rfl
        · exact ⟨s, hs', hm, fun s' l' h1 h2 => hmax s' l' ((hW s').2 (Or.inl h1)) h2⟩
        · exact absurd hm (hnot l)
      · rintro ⟨s, hs, hm, hmax⟩
        refine ⟨s, (hW s).2 (Or.inl hs), hm, fun s' l' h1 h2 => ?_⟩
        rcases (hW s').1 h1 with h1' | rfl
        · exact hmax s' l' h1' h2
        · exact absurd h2 (hnot l')
    by_cases hex : ∃ l, IsLatest S W' q l
    · rw [latest_eq_some ((key _).2 hex.choose_spec), latest_eq_some hex.choose_spec]
    · rw [latest_eq_none hex, latest_eq_none fun ⟨l, hl⟩ => hex ⟨l, (key l).1 hl⟩]
  · simp only [hR, ↓reduceIte]
    by_cases hex : ∃ l, {l | (q, r, l) ∈ S} = {l}
    · rw [dite_eq_left_of_eq_true (eq_true hex)]
      apply latest_eq_some
      have hspec := hex.choose_spec
      have hmem : (q, r, hex.choose) ∈ S := (Set.ext_iff.1 hspec hex.choose).2 rfl
      refine ⟨r, hWr, hmem, fun s' l' hs' hm' => ?_⟩
      rcases (hW s').1 hs' with h1 | rfl
      · exact Or.inl (hW' s' h1)
      · right; refine ⟨rfl, ?_⟩
        have : l' ∈ {l | (q, s', l) ∈ S} := hm'
        rw [hspec] at this; exact this
    · rw [dite_eq_right_of_eq_false (eq_false hex)]
      apply latest_eq_none
      rintro ⟨l, s, hs, hm, hmax⟩
      obtain ⟨l₁, hl₁⟩ := Set.nonempty_iff_ne_empty.2 hR
      have hsr : s = r := by
        rcases (hW s).1 hs with h1 | h1
        · rcases hmax r l₁ hWr hl₁ with h2 | ⟨h2, -⟩
          · exact absurd h2 (not_lt.2 (le_of_lt (hW' s h1)))
          · exact h2.symm
        · exact h1
      subst hsr
      apply hex
      refine ⟨l, Set.eq_singleton_iff_unique_mem.2 ⟨hm, fun l' hl' => ?_⟩⟩
      rcases hmax s l' hWr hl' with h2 | ⟨-, h2⟩
      · exact absurd h2 (lt_irrefl _)
      · exact h2

namespace Exec

variable {E : Exec P α}

theorem H_subset_O (r : ℕ) : E.H r ⊆ E.O r := sdiff_subset

theorem B_mono' {t r : ℕ} (h : t ≤ r) : E.B t ⊆ E.B r :=
  (monotone_nat_of_le_succ E.B_mono) h

theorem rcv_mono' {p : P} {t r : ℕ} (h : t ≤ r) : E.rcv p t ⊆ E.rcv p r :=
  (monotone_nat_of_le_succ (E.rcv_mono p)) h

theorem O_subset_Ow {a b r : ℕ} (h1 : a ≤ r) (h2 : r ≤ b) : E.O r ⊆ E.Ow a b :=
  subset_biUnion_of_mem E.O (mem_Icc.2 ⟨h1, h2⟩)

theorem sent_honest {t : ℕ} {q : P} (ht : 1 ≤ t) (hq : q ∈ E.H t) : E.Sent t (q, t, E.vote t q) :=
  Or.inl ⟨ht, hq, rfl⟩

end Exec

variable [Fintype P]

namespace Exec

variable (E : Exec P α)

/-- The tally of the GA instance of round `r` computed by `p` (at the end of round `r`): the
latest unexpired votes, i.e. those with round tag in `[r - η, r]`. -/
def tally (p : P) (r : ℕ) : Votes P α := latest (E.rcv p r) (fun s => r - E.η ≤ s ∧ s ≤ r)

/-- The initial vote set of the extended GA of round `r` (Section 3.3): latest votes with round
tag in `[r - η, r)`. -/
def M0 (p : P) (r : ℕ) : Votes P α := latest (E.rcv p r) (fun s => r - E.η ≤ s ∧ s < r)

/-- `p` decides `Λ` in round `r` (line 3 of Algorithm 1): `r = 2v - 1` with `v ≥ 2` and `Λ` is
output with grade 1 by the GA of round `r - 1` (that is, `GA_{v-1,2}`). -/
def Decides (p : P) (r : ℕ) (Λ : List α) : Prop :=
  3 ≤ r ∧ Odd r ∧ p ∈ E.H r ∧ Grade1 (E.tally p (r - 1)) Λ

/-- Honest processes follow the modified Algorithm 1 (with the input rule of [MMR]: the input of
`GA_{v,1}` extends the longest log `L_{v-1}` output by `GA_{v-1,2}`). -/
structure Follows : Prop where
  odd : ∀ r p, 3 ≤ r → Odd r → p ∈ E.H r → (∃ Λ, Outputs (E.tally p (r - 1)) Λ) →
    ∃ L, IsLongest (Outputs (E.tally p (r - 1))) L ∧ L <+: E.vote r p
  even : ∀ r p, 2 ≤ r → Even r → p ∈ E.H r → (∃ Λ, Grade1 (E.tally p (r - 1)) Λ) →
    IsLongest (Grade1 (E.tally p (r - 1))) (E.vote r p)

variable {E}

omit [Fintype P] in
/-- The sender of a message received by the end of round `r` with round tag `s` is in `O_s`
(honest message) or in `B_r` (Byzantine message). -/
theorem sender_of_rcv {p : P} {r : ℕ} {m : Msg P α} (hm : m ∈ E.rcv p r) :
    (m.1 ∈ E.H m.2.1 ∧ m.2.2 = E.vote m.2.1 m.1) ∨ m.1 ∈ E.B r := by
  obtain ⟨t, ht, hs⟩ := E.rcv_sent p r m hm
  rcases hs with ⟨-, hH, heq⟩ | hb
  · left; rw [heq]; exact ⟨hH, rfl⟩
  · right; exact B_mono' ht (E.byz_sender t m hb)

omit [Fintype P] in
/-- A message received by the end of round `r` from a process not Byzantine at round `r` is the
honest vote of its round tag. -/
theorem honest_of_rcv {p q : P} {r s : ℕ} {l : List α} (hm : (q, s, l) ∈ E.rcv p r)
    (hq : q ∉ E.B r) : q ∈ E.H s ∧ l = E.vote s q := by
  rcases sender_of_rcv hm with h | h
  · exact h
  · exact absurd h hq

/-! ### The GA instance of round `r` is an extended graded agreement (Section 3.3) -/

/-- The extended graded agreement instance of round `r` of the modified Algorithm 1:
`M0` = latest votes with tag in `[r - η, r)`, round-`r` messages as `R`, and
`P0 = O_{r-η,r}` (a superset of all possible senders of initial votes). -/
def ga (E : Exec P α) (r : ℕ) : ExtGA P α where
  H := E.H r
  B := E.B r
  Hnext := E.H (r + 1)
  P0 := E.Ow (r - E.η) r
  input := E.vote r
  M0 p := E.M0 p r
  R p q := {l | (q, r, l) ∈ E.rcv p r}
  disjoint_H_B := sdiff_disjoint
  disjoint_Hnext_B := by
    rw [Finset.disjoint_left]
    intro q hq hqB
    exact (mem_sdiff.1 hq).2 (E.B_mono r hqB)
  M0_mem p q hq := by
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hq
    obtain ⟨s, ⟨hs1, hs2⟩, hm, -⟩ := latest_eq_some_iff.1 hl
    rcases sender_of_rcv hm with ⟨hH, -⟩ | hB
    · exact O_subset_Ow hs1 hs2.le (H_subset_O _ hH)
    · exact O_subset_Ow (Nat.sub_le r E.η) le_rfl (E.B_subset r hB)
  R_asleep p q hq := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hm
    apply hq
    rcases sender_of_rcv hm with ⟨hH, -⟩ | hB
    · exact mem_union_left _ hH
    · exact mem_union_right _ hB
  R_honest p q hq := by
    intro l hm
    have hqB : q ∉ E.B r := (mem_sdiff.1 hq).2
    exact (honest_of_rcv hm hqB).2

/-- The tally of the modified Algorithm 1 coincides with the final vote set of the extended graded
agreement instance (the correspondence claimed in Section 3.3). -/
theorem tally_eq_ga_M (p : P) (r : ℕ) : E.tally p r = (E.ga r).M p := by
  funext q
  simp only [tally, ExtGA.M, ga, M0]
  exact latest_split _ _ _ q r (fun s => by omega) (fun s hs => hs.2)

theorem ga_O_union_P0 (r : ℕ) : (E.ga r).O ∪ (E.ga r).P0 = E.Ow (r - E.η) r := by
  refine union_eq_right.2 ?_
  exact union_subset (subset_trans (H_subset_O r) (O_subset_Ow (Nat.sub_le r E.η) le_rfl))
    (subset_trans (E.B_subset r) (O_subset_Ow (Nat.sub_le r E.η) le_rfl))

theorem ga_quorum {r : ℕ} (h : E.Sleepy r) : (E.ga r).Quorum := by
  unfold ExtGA.Quorum; rw [ga_O_union_P0]; exact h

theorem ga_sync {r : ℕ} (hr : 1 ≤ r) (hs : E.IsSync r) : (E.ga r).Sync := by
  intro p hp q hq
  apply Set.Subset.antisymm ((E.ga r).R_honest p q hq)
  rw [Set.singleton_subset_iff]
  exact E.rcv_sync r hs p hp r le_rfl _ (sent_honest hr hq)

/-- In a synchronous η-sleepy round `r ≥ 1`, the GA instance of the modified Algorithm 1 satisfies
the five graded agreement properties (Lemma 1 applied as in Section 3.3). -/
theorem isGA {r : ℕ} (hr : 1 ≤ r) (hs : E.IsSync r) (hsl : E.Sleepy r) :
    IsGradedAgreement (E.H r) (E.H (r + 1)) (E.vote r) (fun p => E.tally p r) := by
  have h := lemma_1 (E.ga r) (ga_quorum hsl) (ga_sync hr hs)
  simp only [funext fun p => tally_eq_ga_M (E := E) p r]
  exact h

/-- Clique validity for the GA instance of round `r` of the modified Algorithm 1 (any round). -/
theorem clique {r : ℕ} {Λ : List α} {H' : Finset P} (hH' : Disjoint H' (E.B r))
    (hin : ∀ q ∈ H', q ∈ E.H r → Λ <+: E.vote r q) {p : P}
    (hM0 : ∀ q ∈ H', ∃ l, E.M0 p r q = some l ∧ Λ <+: l)
    (hc : 2 * #(E.Ow (r - E.η) r) < 3 * #H') : Grade1 (E.tally p r) Λ := by
  rw [tally_eq_ga_M]
  exact clique_validity (E.ga r) hH' hin hM0 (by rw [ga_O_union_P0]; exact hc)

/-- Under the protocol, a grade-1 output of the GA of round `r ≥ 1` is extended by the vote of
round `r + 1`. -/
theorem Follows.vote_extends (hF : E.Follows) {r : ℕ} (hr : 1 ≤ r) {p : P} (hp : p ∈ E.H (r + 1))
    {Λ : List α} (hg : Grade1 (E.tally p r) Λ) : Λ <+: E.vote (r + 1) p := by
  rcases Nat.even_or_odd (r + 1) with he | ho
  · have := hF.even (r + 1) p (by omega) he hp ⟨Λ, by simpa using hg⟩
    simp only [Nat.add_sub_cancel] at this
    exact prefix_of_isLongest_grade1 this hg
  · have h3 : 3 ≤ r + 1 := by
      rcases ho with ⟨k, hk⟩; omega
    obtain ⟨L, hL, hLv⟩ := hF.odd (r + 1) p h3 ho hp ⟨Λ, by simpa using hg.outputs⟩
    simp only [Nat.add_sub_cancel] at hL
    exact (prefix_of_isLongest_outputs hL hg).trans hLv

end Exec

end

end Podc.SleepyTOB
