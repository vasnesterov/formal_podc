import Papers.PODC2024.SleepyTOB.Model

/-!
# Asynchrony resilience: Lemmas 2, 3 and Theorem 2

D'Amato, Losa, Zanolini, PODC 2024, Section 3.3.

Setting: an execution `E` of the modified Algorithm 1 (`Exec.Follows`) with a single asynchronous
period `[ra + 1, ra + π]`, `π < η`, Equations 4 and 5, and η-sleepiness in the synchronous
rounds outside `[ra + 1, ra + π + 1]`.
-/

namespace Podc.SleepyTOB

open Finset

noncomputable section
open Classical

variable {P α : Type*} [Fintype P]

namespace Exec

variable {E : Exec P α}

omit [Fintype P] in
/-- If `p` has received the round-`ra` vote of `q`, `q` is honest up to round `r`, the round tag
`ra` is unexpired in the initial vote set of round `r`, and all votes of `q` in rounds
`[ra, r)` extend `Λ`, then the initial vote set `M0 p r` contains a vote of `q` for an extension
of `Λ`. -/
theorem M0_extends {p q : P} {r ra : ℕ} {Λ : List α} (hqB : q ∉ E.B r)
    (hm : (q, ra, E.vote ra q) ∈ E.rcv p r) (h1 : r - E.η ≤ ra) (h2 : ra < r)
    (hv : ∀ s, ra ≤ s → s < r → q ∈ E.H s → Λ <+: E.vote s q) :
    ∃ l, E.M0 p r q = some l ∧ Λ <+: l := by
  obtain ⟨s, hs, hW, hms, heq⟩ := latest_eq_of_functional (S := E.rcv p r)
    (W := fun s => r - E.η ≤ s ∧ s < r) (q := q) (fun s => E.vote s q) r
    (fun s hs => hs.2.le) (fun s l _ hm => (honest_of_rcv hm hqB).2) ⟨h1, h2⟩ hm
  exact ⟨_, heq, hv s hs hW.2 (honest_of_rcv hms hqB).1⟩

/-- The core of Lemma 2 (and of the second half of Theorem 2's proof). Suppose that, in all rounds
`s ∈ [ra, r]`, every process of `H_ra ∩ H_s` votes for an extension of `Λ`, where
`ra ≤ r ≤ ra + π + 1`. Then the GA of round `r` outputs `Λ` with grade 1 at every receiver
`p ∈ H_{r+1}` that is in `H_ra`, or at every receiver if round `r` is synchronous.
For `r = ra` this is validity (Lemma 1); for `r > ra` it is clique validity with
`H' = H_ra \ B_r` and Equation 4. -/
theorem grade1_window (hra : 1 ≤ E.ra) (hπη : E.π < E.η) (hsl : E.Sleepy E.ra) (h4 : E.Eq4)
    (h5 : E.Eq5) {Λ : List α} {r : ℕ} (hr1 : E.ra ≤ r) (hr2 : r ≤ E.ra + E.π + 1)
    (hv : ∀ s, E.ra ≤ s → s ≤ r → ∀ q ∈ E.H E.ra, q ∈ E.H s → Λ <+: E.vote s q)
    {p : P} (hp : p ∈ E.H E.ra ∨ E.IsSync r) (hpr : p ∈ E.H (r + 1)) :
    Grade1 (E.tally p r) Λ := by
  have hsra : E.IsSync E.ra := by unfold IsSync; omega
  rcases eq_or_lt_of_le hr1 with rfl | hlt
  · exact (isGA hra hsra hsl).validity Λ (fun q hq => hv _ le_rfl le_rfl q hq hq) p hpr
  · refine clique (H' := E.H E.ra \ E.B r) sdiff_disjoint
      (fun q hq hqr => hv r hr1 le_rfl q (mem_sdiff.1 hq).1 hqr) (fun q hq => ?_)
      (h4 r hlt hr2)
    obtain ⟨hqa, hqB⟩ := mem_sdiff.1 hq
    have hsent : E.Sent E.ra (q, E.ra, E.vote E.ra q) := sent_honest hra hqa
    have hm : (q, E.ra, E.vote E.ra q) ∈ E.rcv p r := by
      rcases hp with hp | hp
      · exact rcv_mono' hlt.le (E.rcv_sync E.ra hsra p (h5 hp) E.ra le_rfl _ hsent)
      · exact E.rcv_sync r hp p hpr E.ra hr1 _ hsent
    exact M0_extends hqB hm (by omega) hlt
      (fun s hs1 hs2 hqs => hv s hs1 hs2.le q hqa hqs)

/-- **Lemma 2.** Let `[ra + 1, ra + π]` with `π < η` be the period of asynchrony. If every process
in `H_ra` multicasts a vote for an extension of `Λ` in round `ra`, then every process in
`H_ra ∩ H_r` multicasts a vote for an extension of `Λ` in every round `r ∈ [ra + 1, ra + π + 1]`.
(Assumptions: Equations 4 and 5, η-sleepiness in the synchronous round `ra ≥ 1`.) -/
theorem lemma_2 (hF : E.Follows) (hra : 1 ≤ E.ra) (hπη : E.π < E.η) (hsl : E.Sleepy E.ra)
    (h4 : E.Eq4) (h5 : E.Eq5) {Λ : List α} (hv : ∀ q ∈ E.H E.ra, Λ <+: E.vote E.ra q) :
    ∀ r, E.ra + 1 ≤ r → r ≤ E.ra + E.π + 1 → ∀ q ∈ E.H E.ra ∩ E.H r, Λ <+: E.vote r q := by
  have key : ∀ n s, E.ra ≤ s → s ≤ E.ra + n → s ≤ E.ra + E.π + 1 →
      ∀ q ∈ E.H E.ra, q ∈ E.H s → Λ <+: E.vote s q := by
    intro n
    induction n with
    | zero =>
      intro s hs1 hs2 _ q hq _
      obtain rfl : s = E.ra := by omega
      exact hv q hq
    | succ n ih =>
      intro s hs1 hs2 hs3 q hq hqs
      rcases lt_or_eq_of_le hs2 with hlt | rfl
      · exact ih s hs1 (by omega) hs3 q hq hqs
      · have hg := grade1_window hra hπη hsl h4 h5 (r := E.ra + n) (by omega) (by omega)
          (fun s' h1 h2 q' hq' hq's => ih s' h1 h2 (by omega) q' hq' hq's) (Or.inl hq) hqs
        exact hF.vote_extends (r := E.ra + n) (by omega) hqs hg
  intro r hr1 hr2 q hq
  exact key (r - E.ra) r (by omega) (by omega) hr2 q (mem_inter.1 hq).1 (mem_inter.1 hq).2

/-- MMR's lock argument (the base case of Lemma 3). If `p` decides `Λ` in round `r` and rounds
`r - 2`, `r - 1` are synchronous and η-sleepy, then every process of `H_r` votes for an extension
of `Λ` in round `r`. Graded consistency alone (as cited in the paper) does not suffice: one also
needs integrity of `GA_{v-1,2}` and uniqueness of `GA_{v-1,1}`, to exclude a longer conflicting
grade-0 output (see `graded_consistency_insufficient`). -/
theorem Follows.decision_lock (hF : E.Follows) {p : P} {r : ℕ} {Λ : List α}
    (hd : E.Decides p r Λ) (hs1 : E.IsSync (r - 2)) (hs2 : E.IsSync (r - 1))
    (hl1 : E.Sleepy (r - 2)) (hl2 : E.Sleepy (r - 1)) : ∀ q ∈ E.H r, Λ <+: E.vote r q := by
  obtain ⟨hr3, hodd, hp, hg⟩ := hd
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
  simp only [Nat.add_sub_cancel] at hs1 hl1
  have e1 : a + 2 - 1 = a + 1 := rfl
  rw [e1] at hs2 hl2 hg
  have hA := isGA (r := a) (by omega) hs1 hl1
  have hB := isGA (r := a + 1) (by omega) hs2 hl2
  have heven : Even (a + 1) := by
    rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  -- every honest vote of round `a + 1` is a grade-1 output of the GA of round `a`
  have hvote : ∀ y ∈ E.H (a + 1), Grade1 (E.tally y a) (E.vote (a + 1) y) := by
    intro y hy
    have hex : ∃ Λ, Grade1 (E.tally y (a + 1 - 1)) Λ :=
      ⟨[], hA.validity [] (fun _ _ => List.nil_prefix) y hy⟩
    exact (hF.even (a + 1) y (by omega) heven hy hex).1
  obtain ⟨y, hy, hΛy⟩ := hB.integrity p hp Λ hg.outputs
  -- no output of `GA_{v-1,2}` conflicts with `Λ`
  have hcompat : ∀ q ∈ E.H (a + 2), ∀ X, Outputs (E.tally q (a + 1)) X → Compatible X Λ := by
    intro q hq X hX
    obtain ⟨z, hz, hXz⟩ := hB.integrity q hq X hX
    exact compatible_of_prefix_compatible hXz hΛy
      (hA.uniqueness y hy z hz _ _ (hvote y hy) (hvote z hz))
  intro q hq
  have hΛq : Outputs (E.tally q (a + 1)) Λ := hB.graded_consistency p hp q hq Λ hg
  obtain ⟨L, hL, hLv⟩ := hF.odd (a + 2) q hr3 hodd hq ⟨Λ, hΛq⟩
  have hL' : Λ <+: L :=
    prefix_of_compatible_of_length_le (hcompat q hq L hL.1).symm (hL.2 Λ hΛq)
  exact hL'.trans hLv

/-- The lock persists through synchronous η-sleepy rounds: if `p` decides `Λ` in round `r` and all
rounds `≤ N` are synchronous and η-sleepy, every process of `H_r'` votes for an extension of `Λ`
in every round `r' ∈ [r, N]`. -/
theorem Follows.lock_until (hF : E.Follows) (N : ℕ) (hsync : ∀ s ≤ N, E.IsSync s)
    (hsl : ∀ s ≤ N, E.Sleepy s) {p : P} {r : ℕ} {Λ : List α} (hd : E.Decides p r Λ) :
    ∀ r', r ≤ r' → r' ≤ N → ∀ q ∈ E.H r', Λ <+: E.vote r' q := by
  have h3 := hd.1
  intro r' hr1 hr2
  induction r', hr1 using Nat.le_induction with
  | base =>
    exact hF.decision_lock hd (hsync _ (by omega)) (hsync _ (by omega)) (hsl _ (by omega))
      (hsl _ (by omega))
  | succ s hs ih =>
    intro q hq
    have hGA := isGA (r := s) (by omega) (hsync s (by omega)) (hsl s (by omega))
    exact hF.vote_extends (by omega) hq
      (hGA.validity Λ (ih (by omega)) q hq)

/-- **Lemma 3.** Let `Λ ∈ D_ra` be a log decided in a round `r ≤ ra`. In every round
`r' ∈ [r, ra]`, every process of `H_r'` multicasts a vote for an extension of `Λ`.
(The hypothesis `r ≤ ra` is implicit: otherwise the range of `r'` is empty.)
(Rounds `≤ ra` are synchronous; we assume η-sleepiness in them.) -/
theorem lemma_3 (hF : E.Follows) (hsl : ∀ r ≤ E.ra, E.Sleepy r) {p : P} {r : ℕ} {Λ : List α}
    (hd : E.Decides p r Λ) :
    ∀ r', r ≤ r' → r' ≤ E.ra → ∀ q ∈ E.H r', Λ <+: E.vote r' q :=
  hF.lock_until E.ra (fun s hs => by unfold IsSync; omega) hsl hd

/-- **Theorem 1, safety half** (for the modified Algorithm 1, in executions without asynchrony,
`π = 0`, that are η-sleepy in every round): any two logs decided by honest processes are
compatible. (The paper defers to [MMR]'s Lemma 6; liveness is not formalized.) -/
theorem theorem_1_safety (hF : E.Follows) (hπ : E.π = 0) (hsl : ∀ r, E.Sleepy r)
    {p q : P} {r s : ℕ} {Λ Λ' : List α} (hd : E.Decides p r Λ) (hd' : E.Decides q s Λ') :
    Compatible Λ Λ' := by
  have hsync : ∀ t, E.IsSync t := fun t => by unfold IsSync; omega
  -- w.l.o.g. `r ≤ s`
  suffices key : ∀ {p q : P} {r s : ℕ} {Λ Λ' : List α}, E.Decides p r Λ → E.Decides q s Λ' →
      r ≤ s → Compatible Λ Λ' by
    rcases le_total r s with h | h
    · exact key hd hd' h
    · exact (key hd' hd h).symm
  intro p q r s Λ Λ' hd hd' hrs
  obtain ⟨h3, hodd, hp, hg⟩ := hd
  obtain ⟨h3', -, hq, hg'⟩ := hd'
  rcases eq_or_lt_of_le hrs with rfl | hlt
  · exact (isGA (r := r - 1) (by omega) (hsync _) (hsl _)).uniqueness p
      (by rwa [Nat.sub_add_cancel (by omega)]) q (by rwa [Nat.sub_add_cancel (by omega)]) _ _ hg hg'
  · have hlock := hF.lock_until (s - 1) (fun t _ => hsync t) (fun t _ => hsl t) ⟨h3, hodd, hp, hg⟩
    have hG := (isGA (r := s - 1) (by omega) (hsync _) (hsl _)).validity Λ
      (hlock (s - 1) (by omega) le_rfl) q (by rwa [Nat.sub_add_cancel (by omega)])
    exact compatible_of_grade1_of_outputs hG hg'.outputs

/-- **Theorem 2** (π-asynchrony resilience, Definition 5). Let `Λ ∈ D_ra` be decided in a round
`r ≤ ra` and let `[ra + 1, ra + π]`, with `π < η`, be the period of asynchrony. Then
1. no process of `H_ra` decides a log conflicting with `Λ` in a round of `[ra + 1, ra + π + 1]`;
2. no honest process decides a log conflicting with `Λ` in a round `> ra + π + 1`.

Assumptions: honest processes follow the modified Algorithm 1 (with [MMR]'s input rule), Equations 4
and 5, and η-sleepiness in all rounds outside `[ra + 1, ra + π + 1]`. -/
theorem theorem_2 (hF : E.Follows) (hπη : E.π < E.η)
    (hsl : ∀ r, r ≤ E.ra ∨ E.ra + E.π + 1 < r → E.Sleepy r) (h4 : E.Eq4) (h5 : E.Eq5)
    {p : P} {r : ℕ} {Λ : List α} (hd : E.Decides p r Λ) (hr : r ≤ E.ra) :
    (∀ q s Λ', E.ra + 1 ≤ s → s ≤ E.ra + E.π + 1 → q ∈ E.H E.ra → E.Decides q s Λ' →
      Compatible Λ Λ') ∧
    (∀ q s Λ', E.ra + E.π + 1 < s → E.Decides q s Λ' → Compatible Λ Λ') := by
  have hra : 1 ≤ E.ra := by have := hd.1; omega
  have hslra : E.Sleepy E.ra := hsl _ (Or.inl le_rfl)
  -- Lemma 3 at round `ra`, then Lemma 2
  have h3 := lemma_3 hF (fun r hr => hsl r (Or.inl hr)) hd E.ra hr le_rfl
  have h2 := lemma_2 hF hra hπη hslra h4 h5 h3
  have hv : ∀ s, E.ra ≤ s → s ≤ E.ra + E.π + 1 → ∀ q ∈ E.H E.ra, q ∈ E.H s →
      Λ <+: E.vote s q := by
    intro s hs1 hs2 q hq hqs
    rcases eq_or_lt_of_le hs1 with rfl | hlt
    · exact h3 q hq
    · exact h2 s hlt hs2 q (mem_inter.2 ⟨hq, hqs⟩)
  constructor
  · rintro q s Λ' hs1 hs2 hq ⟨-, -, hqs, hg'⟩
    have hg := grade1_window hra hπη hslra h4 h5 (r := s - 1) (by omega) (by omega)
      (fun s' h1 h2 => hv s' h1 (by omega)) (Or.inl hq) (by rwa [Nat.sub_add_cancel (by omega)])
    exact compatible_of_grade1_of_outputs hg hg'.outputs
  · -- after the asynchronous period every honest receiver outputs `Λ` with grade 1
    have hall : ∀ n, ∀ q ∈ E.H (E.ra + E.π + 1 + n + 1),
        Grade1 (E.tally q (E.ra + E.π + 1 + n)) Λ := by
      intro n
      induction n with
      | zero =>
        intro q hq
        exact grade1_window hra hπη hslra h4 h5 (by omega) le_rfl hv
          (Or.inr (by unfold IsSync; omega)) hq
      | succ n ih =>
        intro q hq
        have hGA := isGA (r := E.ra + E.π + 1 + (n + 1)) (by omega)
          (by unfold IsSync; omega) (hsl _ (Or.inr (by omega)))
        refine hGA.validity Λ (fun q' hq' => ?_) q hq
        exact hF.vote_extends (r := E.ra + E.π + 1 + n) (by omega) hq' (ih q' hq')
    rintro q s Λ' hs ⟨-, -, hqs, hg'⟩
    obtain ⟨n, rfl⟩ : ∃ n, s = E.ra + E.π + 1 + n + 1 := ⟨s - (E.ra + E.π + 2), by omega⟩
    have hg := hall n q hqs
    simp only [Nat.add_sub_cancel] at hg'
    exact compatible_of_grade1_of_outputs hg hg'.outputs

end Exec

end

end Podc.SleepyTOB
