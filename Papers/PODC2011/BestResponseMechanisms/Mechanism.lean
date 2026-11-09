import Podc.Foundations.GameTheory.NeverBestResponse

/-!
# Best-response mechanisms and Theorem 2.7

[NSVZ] N. Nisan, M. Schapira, G. Valiant, A. Zohar, *Best-Response Mechanisms*, ICS 2011
(brief announcement *Incentive-compatible distributed greedy protocols*, PODC 2011).

We fix one realization of the private utilities (the theorem is ex-post, i.e. per realization),
so the base game is a `TieBreakGame ι S R`.

## Two layers

1. **Asynchronous runs** (`FreshBR`, `AsyncRounds`). A run is any sequence of profiles
   `s : ℕ → ∀ i, S i`. We do not fix how players are scheduled; instead, the hypothesis
   `AsyncRounds G s P T m` says that the time points `T 0, T 1, …, T m` delimit `m` *rounds* for
   the players in `P`: from time `T (k + 1)` on, the current strategy of every player of `P` is a
   tie-broken best response to *some* profile whose entries were all current at times `≥ T k`.
   This covers sequential activations, simultaneous activations, outdated information and
   adaptive (history-dependent) schedules, extensions (1) and (2) after Theorem 2.7: for
   outdated information the round boundaries must be placed so that information read in round
   `k + 1` was produced in round `k` or later (see `Counterexamples.lean` for why a round cannot
   just be "every player was active once").
   * `converges` (Theorem 2.7 (1)): after `r` rounds, `s t = s*` (where `E 0, …, E r` is any
     NBR-elimination sequence ending at `s*`).
   * `deviator_utility_le` (core of Theorem 2.7 (2)): if all players but `i` best-respond, then
     after `k` rounds, where `k` is the index of a clear-outcome witness for `i`, the stage utility
     of `i` never exceeds `u_i(s*)`, whatever `i` does.
   * `eq_of_all_pass`, `utility_le_of_others_pass`: extension (3) (termination when all players
     pass): a profile at which everybody passes is `s*`, and a profile at which everybody but `i`
     passes gives `i` at most `u_i(s*)`.
2. **The repeated game** (`Mechanism`, `run`, `IsIncentiveCompatible`). A repeated-response
   mechanism: an initial profile, an adaptive activation rule (who is active next, as a function of
   the history), and a horizon. A player's strategy in the repeated game maps histories to
   announcements; a best-response mechanism prescribes a tie-broken best response to the current
   profile. Total utility: last-stage utility (finite horizon) or `lim sup` of stage utilities.
   * `theorem_2_7_convergence`, `theorem_2_7_incentive_compatible`: the corrected Theorem 2.7: the
     mechanism converges to `s*` once every run has `≥ r` rounds, and is incentive compatible
     (repeated best response is a pure Nash equilibrium of the repeated game) once every run has
     at least `max r kᵢ` rounds, `kᵢ` being the indices of the clear-outcome witnesses.
     `Counterexamples.theorem_2_7_false` shows that `e_G` rounds (the paper's bound) do not
     suffice.
   * `theorem_2_7_limsup`: the same for infinite runs with `lim sup` utilities.
   * `informal_theorem`: in finite games `Σᵢ |Sᵢ| - n` rounds suffice (the bound of the informal
     theorem of Section 1.3).
   * `roundRobin`, `roundRobin_hasRounds`: round robin on `Fin (n + 1)`; `m` rounds take
     `(n + 1) * m` steps.
-/

open Set Function Filter

namespace Podc.BestResponseMechanisms

open Cslib.GameTheory TieBreakGame

variable {ι : Type*} {S : ι → Type*} {R : Type*} [DecidableEq ι] [LinearOrder R]
variable {G : TieBreakGame ι S R}

/-! ## Asynchronous runs -/

/-- In the run `s`, the strategy of player `j` at time `t` is a tie-broken best response to a
profile `v` all of whose other entries are strategies that were current at times `≥ t₀`
(possibly outdated, possibly different times for different players). -/
def FreshBR (G : TieBreakGame ι S R) (s : ℕ → ∀ i, S i) (j : ι) (t t₀ : ℕ) : Prop :=
  ∃ v : ∀ l, S l, (∀ l, l ≠ j → ∃ τ, t₀ ≤ τ ∧ v l = s τ l) ∧ G.IsBR j (s t j) v

/-- The times `T 0, …, T m` delimit `m` (asynchronous) rounds of the run `s` for the players in
`P`: from time `T (k + 1)` on, the current strategy of every `j ∈ P` is a tie-broken best response
to information produced at times `≥ T k`. -/
def AsyncRounds (G : TieBreakGame ι S R) (s : ℕ → ∀ i, S i) (P : Set ι) (T : ℕ → ℕ) (m : ℕ) :
    Prop :=
  ∀ k < m, ∀ t, T (k + 1) ≤ t → ∀ j ∈ P, FreshBR G s j t (T k)

lemma AsyncRounds.mono {s : ℕ → ∀ i, S i} {P Q : Set ι} {T : ℕ → ℕ} {m m' : ℕ}
    (h : AsyncRounds G s P T m) (hQ : Q ⊆ P) (hm : m' ≤ m) : AsyncRounds G s Q T m' :=
  fun k hk t ht j hj => h k (by omega) t ht j (hQ hj)

/-- Invariant of the convergence proof: after `k` rounds the run stays inside `E k`, as long as
the players outside `P` cannot leave `E k` (for the deviation argument: `i` is never restricted
before step `k`). -/
lemma mem_of_asyncRounds {E : ℕ → Subgame S} {r : ℕ} (hE : G.IsElimSeq E r)
    {s : ℕ → ∀ i, S i} {P : Set ι} {T : ℕ → ℕ} {m : ℕ} (hR : AsyncRounds G s P T m)
    (hout : ∀ k ≤ m, ∀ j ∉ P, E k j = univ) :
    ∀ k ≤ m, k ≤ r → ∀ t, T k ≤ t → ∀ j, s t j ∈ E k j := by
  intro k
  induction k with
  | zero => intro _ _ t _ j; exact hE.zero j _
  | succ k ih =>
    intro hkm hkr t ht j
    by_cases hj : j ∈ P
    · obtain ⟨v, hv, hbr⟩ := hR k (by omega) t ht j hj
      refine hE.mem_of_isBR hbr (k := k) (by omega) ?_ le_rfl hkr
      intro l hl
      obtain ⟨τ, hτ, hvl⟩ := hv l hl
      rw [hvl]
      exact ih (by omega) (by omega) τ hτ l
    · rw [hout (k + 1) hkm j hj]; trivial

/-- **Theorem 2.7 (1)** (asynchronous form): if `E 0, …, E r` is an NBR-elimination sequence
ending at `s*` and the run has `r` rounds in which all players best-respond, then from time `T r`
on the run is at `s*`. -/
theorem converges {E : ℕ → Subgame S} {r : ℕ} {sstar : ∀ i, S i} (hE : G.Solves E r sstar)
    {s : ℕ → ∀ i, S i} {T : ℕ → ℕ} (hR : AsyncRounds G s univ T r) :
    ∀ t, T r ≤ t → s t = sstar := by
  intro t ht
  funext j
  have := mem_of_asyncRounds hE.1 hR (by simp) r le_rfl le_rfl t ht j
  rw [hE.2] at this
  exact this

/-- **Core of Theorem 2.7 (2)**: let `(E, r, k)` be a clear-outcome witness for player `i`. If
in the run all players other than `i` best-respond, with `k` rounds delimited by `T`, then
whatever `i` does, from time `T k` on the stage utility of `i` is at most `u_i(s*)`. -/
theorem deviator_utility_le {sstar : ∀ i, S i} {i : ι} {E : ℕ → Subgame S} {r k : ℕ}
    (hW : G.ClearWitness sstar i E r k) {s : ℕ → ∀ i, S i} {T : ℕ → ℕ}
    (hR : AsyncRounds G s {j | j ≠ i} T k) :
    ∀ t, T k ≤ t → G.utility i (s t) ≤ G.utility i sstar := by
  obtain ⟨hS, hkr, hEi, hopt⟩ := hW
  intro t ht
  apply hopt
  have hout : ∀ k' ≤ k, ∀ j ∉ ({j | j ≠ i} : Set ι), E k' j = univ := by
    intro k' hk' j hj
    simp only [mem_ofPred_eq, not_not] at hj
    subst hj
    apply Set.eq_univ_of_univ_subset
    rw [← hS.1.antitone hk' hkr j |>.antisymm ?_]
    · rw [hEi]
    · rw [hEi]; exact subset_univ _
  exact mem_of_asyncRounds hS.1 hR hout k le_rfl hkr t ht

/-- **Theorem 2.7 (3)**, honest case: if every player passes at `p` (each player's strategy is
its tie-broken best response), then `p = s*`. -/
theorem eq_of_all_pass {E : ℕ → Subgame S} {r : ℕ} {sstar : ∀ i, S i}
    (hE : G.Solves E r sstar) {p : ∀ i, S i} (hp : G.IsBRFixed p) : p = sstar :=
  hE.eq_of_isBRFixed hp

/-- **Theorem 2.7 (3)**, deviation: if the mechanism stops at a profile `p` at which every player
other than `i` passes, then `u_i(p) ≤ u_i(s*)`. No round bound is needed. -/
theorem utility_le_of_others_pass {sstar : ∀ i, S i} {i : ι} {E : ℕ → Subgame S} {r k : ℕ}
    (hW : G.ClearWitness sstar i E r k) {p : ∀ i, S i} (hp : ∀ j, j ≠ i → G.IsBR j (p j) p) :
    G.utility i p ≤ G.utility i sstar := by
  -- the constant run at `p` has arbitrarily many rounds for the players `≠ i`
  have hR : AsyncRounds G (fun _ => p) {j | j ≠ i} id k :=
    fun k' _ t ht j hj => ⟨p, fun l _ => ⟨t, by simp only [id] at ht ⊢; omega, rfl⟩, hp j hj⟩
  exact deviator_utility_le hW hR k le_rfl

/-! ## The repeated game -/

/-- A history: the profiles so far, most recent first. -/
abbrev History (S : ι → Type*) := List (∀ i, S i)

/-- A repeated-response mechanism: the starting profile and the (adaptive) activation rule:
`active h` is the set of players that announce a strategy at the next step, given the history `h`
(several players may be active simultaneously). -/
structure Mechanism (S : ι → Type*) where
  /-- The starting profile. -/
  init : ∀ i, S i
  /-- The players active at the next time step, as a function of the history. -/
  active : History S → Set ι

/-- A strategy of player `i` in the repeated game: the announcement as a function of the history
(used only when `i` is active). -/
abbrev RStrategy (S : ι → Type*) (i : ι) := History S → S i

variable (M : Mechanism S)

/-- The current profile of a history. -/
def Mechanism.current (h : History S) : ∀ i, S i := h.headD M.init

open Classical in
/-- The history after `t` steps when the players use the strategies `σ`. -/
noncomputable def Mechanism.hist (σ : ∀ i, RStrategy S i) : ℕ → History S
  | 0 => [M.init]
  | t + 1 =>
    let h := Mechanism.hist σ t
    (fun j => if j ∈ M.active h then σ j h else M.current h j) :: h

/-- The profile at time `t`. -/
noncomputable def Mechanism.prof (σ : ∀ i, RStrategy S i) (t : ℕ) : ∀ i, S i :=
  M.current (M.hist σ t)

/-- The players active at time `t` (they announce the profile of time `t + 1`). -/
noncomputable def Mechanism.acts (σ : ∀ i, RStrategy S i) (t : ℕ) : Set ι :=
  M.active (M.hist σ t)

omit [DecidableEq ι] in
lemma Mechanism.prof_zero (σ : ∀ i, RStrategy S i) : M.prof σ 0 = M.init := rfl

omit [DecidableEq ι] in
open Classical in
lemma Mechanism.prof_succ (σ : ∀ i, RStrategy S i) (t : ℕ) (j : ι) :
    M.prof σ (t + 1) j =
      if j ∈ M.acts σ t then σ j (M.hist σ t) else M.prof σ t j := by
  simp [prof, hist, current, acts]

/-- A best-response rule: `br i p` is a tie-broken best response of `i` to the profile `p`. -/
def IsBRRule (G : TieBreakGame ι S R) (br : ∀ i, (∀ j, S j) → S i) : Prop :=
  ∀ i p, G.IsBR i (br i p) p

/-- The prescribed behaviour of a best-response mechanism: announce `br i` of the current
profile. -/
def brStrategy (br : ∀ i, (∀ j, S j) → S i) : ∀ i, RStrategy S i :=
  fun i h => br i (M.current h)

/-- The activation sets `A 0, A 1, …` contain `m` rounds ending by time `N`: there are times
`T 0 ≤ T 1 ≤ …` with `T m ≤ N` such that every player is active at some time in
`[T k, T (k + 1))` (the paper: "a round is a sequence of consecutive time steps in which each
player is active at least once"). -/
def HasRounds (A : ℕ → Set ι) (N m : ℕ) : Prop :=
  ∃ T : ℕ → ℕ, Monotone T ∧ T m ≤ N ∧ ∀ k < m, ∀ j, ∃ t, T k ≤ t ∧ t < T (k + 1) ∧ j ∈ A t

/-- In a run of the mechanism, the strategy of a best-responding player at time `t` was announced
at its last activation, as a best response to the then-current profile. -/
lemma Mechanism.freshBR_of_hasRounds {br : ∀ i, (∀ j, S j) → S i} (hbr : IsBRRule G br)
    (σ : ∀ i, RStrategy S i) {T : ℕ → ℕ} {k : ℕ} {j : ι} (hσ : σ j = brStrategy M br j)
    (hT : ∃ t, T k ≤ t ∧ t < T (k + 1) ∧ j ∈ M.acts σ t) :
    ∀ t, T (k + 1) ≤ t → FreshBR G (M.prof σ) j t (T k) := by
  intro t ht
  obtain ⟨a, ha, hat, hja⟩ := hT
  -- induction on `t` from `a + 1`: the strategy of `j` is a best response to some `prof σ τ`
  -- with `T k ≤ τ`
  have key : ∀ t, a < t → ∃ τ, T k ≤ τ ∧ G.IsBR j (M.prof σ t j) (M.prof σ τ) := by
    intro t hat'
    induction t with
    | zero => omega
    | succ t ih =>
      rw [M.prof_succ]
      split_ifs with hj
      · refine ⟨t, by omega, ?_⟩
        rw [hσ]; exact hbr j _
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hat' with h | h
        · exact ih h
        · subst h; exact absurd hja hj
  obtain ⟨τ, hτ, hb⟩ := key t (by omega)
  exact ⟨M.prof σ τ, fun l _ => ⟨τ, hτ, rfl⟩, hb⟩

lemma Mechanism.asyncRounds_of_hasRounds {br : ∀ i, (∀ j, S j) → S i} (hbr : IsBRRule G br)
    (σ : ∀ i, RStrategy S i) {P : Set ι} (hσ : ∀ j ∈ P, σ j = brStrategy M br j) {m : ℕ}
    {T : ℕ → ℕ} (hT : ∀ k < m, ∀ j, ∃ t, T k ≤ t ∧ t < T (k + 1) ∧ j ∈ M.acts σ t) :
    AsyncRounds G (M.prof σ) P T m :=
  fun k hk t ht j hj => M.freshBR_of_hasRounds hbr σ (hσ j hj) (hT k hk j) t ht

omit [DecidableEq ι] in
lemma Mechanism.length_hist (σ : ∀ i, RStrategy S i) (t : ℕ) : (M.hist σ t).length = t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [Mechanism.hist, ih]

/-- The player active at time `t` under round robin on `Fin (n + 1)`. -/
def rrPlayer (n t : ℕ) : Fin (n + 1) := ⟨t % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- The round-robin mechanism on players `Fin (n + 1)`: at time `t` player `t mod (n + 1)` is
active. -/
def roundRobin {n : ℕ} {S : Fin (n + 1) → Type*} (init : ∀ i, S i) : Mechanism S where
  init := init
  active h := {rrPlayer n (h.length - 1)}

lemma roundRobin_acts {n : ℕ} {S : Fin (n + 1) → Type*} (init : ∀ i, S i)
    (σ : ∀ i, RStrategy S i) (t : ℕ) : (roundRobin init).acts σ t = {rrPlayer n t} := by
  simp [Mechanism.acts, roundRobin, Mechanism.length_hist]

/-- `m` rounds of round robin take `(n + 1) * m` time steps. -/
lemma roundRobin_hasRounds {n : ℕ} {S : Fin (n + 1) → Type*} (init : ∀ i, S i)
    (σ : ∀ i, RStrategy S i) (m : ℕ) :
    HasRounds ((roundRobin init).acts σ) ((n + 1) * m) m := by
  refine ⟨fun k => (n + 1) * k, fun a b h => Nat.mul_le_mul_left _ h, le_rfl, ?_⟩
  intro k _ j
  have hj := j.2
  refine ⟨(n + 1) * k + j, by simp, by simp only [Nat.mul_add, Nat.mul_one]; omega, ?_⟩
  rw [roundRobin_acts]
  simp only [mem_singleton_iff, rrPlayer]
  ext
  simp [Nat.add_mod, Nat.mod_eq_of_lt hj]

/-- One step of round robin: only player `t mod (n + 1)` updates its strategy. -/
lemma roundRobin_prof_succ {n : ℕ} {S : Fin (n + 1) → Type*} (init : ∀ i, S i)
    (σ : ∀ i, RStrategy S i) (t : ℕ) :
    (roundRobin init).prof σ (t + 1) =
      update ((roundRobin init).prof σ t) (rrPlayer n t)
        (σ (rrPlayer n t) ((roundRobin init).hist σ t)) := by
  funext j
  rw [Mechanism.prof_succ, roundRobin_acts]
  by_cases hj : j = rrPlayer n t
  · subst hj; simp
  · simp [hj]

omit [DecidableEq ι] in
lemma brStrategy_hist (br : ∀ i, (∀ j, S j) → S i) (σ : ∀ i, RStrategy S i) (j : ι) (t : ℕ) :
    brStrategy M br j (M.hist σ t) = br j (M.prof σ t) := rfl

/-- **Theorem 2.7 (1)**: if all players best-respond and the activation order has at least `r`
rounds by time `N` (where an NBR elimination of length `r` ends at `s*`, e.g. `r = e_G`), then
the mechanism is at `s*` at time `N` and at every later time. -/
theorem theorem_2_7_convergence {E : ℕ → Subgame S} {r : ℕ} {sstar : ∀ i, S i}
    (hE : G.Solves E r sstar) {br : ∀ i, (∀ j, S j) → S i} (hbr : IsBRRule G br) {N m : ℕ}
    (hm : r ≤ m) (hR : HasRounds (M.acts (brStrategy M br)) N m) :
    ∀ t, N ≤ t → M.prof (brStrategy M br) t = sstar := by
  obtain ⟨T, hTmono, hTN, hT⟩ := hR
  have hA := M.asyncRounds_of_hasRounds hbr (brStrategy M br) (P := univ)
    (fun _ _ => rfl) hT
  intro t ht
  exact converges hE (hA.mono subset_rfl hm) t ((hTmono hm).trans (hTN.trans ht))

/-- Under the strategy profile `σ'`, where all players but `i` follow the best-response rule,
the deviator `i` gets at most `u_i(s*)` from time `N` on, provided the run has `k` rounds by time
`N`, `k` being the index of a clear-outcome witness for `i`. -/
theorem Mechanism.deviation_le {sstar : ∀ i, S i} {i : ι} {E : ℕ → Subgame S} {r k : ℕ}
    (hW : G.ClearWitness sstar i E r k) {br : ∀ i, (∀ j, S j) → S i} (hbr : IsBRRule G br)
    (σ : ∀ i, RStrategy S i) (hσ : ∀ j, j ≠ i → σ j = brStrategy M br j) {N : ℕ}
    (hR : HasRounds (M.acts σ) N k) :
    ∀ t, N ≤ t → G.utility i (M.prof σ t) ≤ G.utility i sstar := by
  obtain ⟨T, -, hTN, hT⟩ := hR
  have hA := M.asyncRounds_of_hasRounds hbr σ (P := {j | j ≠ i}) hσ hT
  intro t ht
  exact deviator_utility_le hW hA t (hTN.trans ht)

/-- The repeated game with total utility = stage utility at the last time step `N`: the
best-response mechanism is incentive compatible if repeated best response is a pure Nash
equilibrium of the repeated game, i.e. no player `i` gains by any strategy `τ` of the repeated
game while the others keep best-responding. -/
def IsIncentiveCompatible (G : TieBreakGame ι S R) (M : Mechanism S)
    (br : ∀ i, (∀ j, S j) → S i) (N : ℕ) : Prop :=
  ∀ (i : ι) (τ : RStrategy S i),
    G.utility i (M.prof (update (brStrategy M br) i τ) N) ≤ G.utility i (M.prof (brStrategy M br) N)

/-- **Theorem 2.7 (2), corrected.** Let `s*` be the outcome of an NBR elimination of length `r`
and, for every player `i`, let `kᵢ` be the index of a clear-outcome witness for `i`
(`HasClearOutcome`). If every run of the mechanism (whatever the players do; the activation
order may be adaptive) has at least `m ≥ max(r, kᵢ)` rounds by the horizon `N`, the
best-response mechanism is incentive compatible, and it implements `s*`.

The paper requires only `m ≥ e_G`; this is not enough (`Counterexamples.theorem_2_7_false`).
Every `kᵢ` can be taken `≤ Σᵢ (|Sᵢ| - 1)` in finite games, which is the bound of the informal
theorem in the introduction. -/
theorem theorem_2_7_incentive_compatible {E : ℕ → Subgame S} {r : ℕ} {sstar : ∀ i, S i}
    (hE : G.Solves E r sstar) {m : ℕ} (hm : r ≤ m)
    (hW : ∀ i, ∃ (E' : ℕ → Subgame S) (r' k : ℕ), k ≤ m ∧ G.ClearWitness sstar i E' r' k)
    {br : ∀ i, (∀ j, S j) → S i} (hbr : IsBRRule G br) {N : ℕ}
    (hR : ∀ σ : ∀ i, RStrategy S i, HasRounds (M.acts σ) N m) :
    IsIncentiveCompatible G M br N ∧ M.prof (brStrategy M br) N = sstar := by
  have hconv := theorem_2_7_convergence M hE hbr hm (hR _) N le_rfl
  refine ⟨fun i τ => ?_, hconv⟩
  rw [hconv]
  obtain ⟨E', r', k, hkm, hWi⟩ := hW i
  obtain ⟨T, hTmono, hTN, hT⟩ := hR (update (brStrategy M br) i τ)
  refine M.deviation_le hWi hbr _ (fun j hj => by simp [hj]) ?_ N le_rfl
  exact ⟨T, hTmono, (hTmono hkm).trans hTN, fun k' hk' => hT k' (by omega)⟩

/-- **The informal theorem of Section 1.3** (finite strategy spaces): if `s*` is a clear outcome,
then with at least `T = Σᵢ |Sᵢ| - n` rounds in every run, the best-response mechanism converges
to `s*` and is incentive compatible. (Unlike Theorem 2.7's `e_G`, this bound is correct.) -/
theorem informal_theorem [Fintype ι] [∀ i, Fintype (S i)] {sstar : ∀ i, S i}
    (hC : G.HasClearOutcome sstar) {m : ℕ}
    (hm : (∑ i, Fintype.card (S i)) - Fintype.card ι ≤ m)
    {br : ∀ i, (∀ j, S j) → S i} (hbr : IsBRRule G br) {N : ℕ}
    (hR : ∀ σ : ∀ i, RStrategy S i, HasRounds (M.acts σ) N m) :
    IsIncentiveCompatible G M br N ∧ M.prof (brStrategy M br) N = sstar := by
  obtain ⟨⟨E, r, hE⟩, hW⟩ := hC
  obtain ⟨E', r', -, hE', -, -, hr'⟩ := hE.exists_short (Nat.zero_le r)
  refine theorem_2_7_incentive_compatible M hE' (by omega) (fun i => ?_) hbr hR
  obtain ⟨E₁, r₁, k₁, hW₁⟩ := hW i
  obtain ⟨E₂, r₂, k₂, hW₂, hr₂⟩ := hW₁.exists_short
  exact ⟨E₂, r₂, k₂, by have := hW₂.2.1; omega, hW₂⟩

/-- **Theorem 2.7, infinite runs**: total utility `lim sup_t u_i(s^t)`. Under the hypotheses of
`theorem_2_7_incentive_compatible` (rounds counted up to some time `N`), the best-response run
converges to `s*` and no deviation of a single player increases its `lim sup` utility. Utilities
are real numbers bounded below (e.g. finite games). -/
theorem theorem_2_7_limsup {G : TieBreakGame ι S ℝ} (M : Mechanism S) {E : ℕ → Subgame S}
    {r : ℕ} {sstar : ∀ i, S i} (hE : G.Solves E r sstar) {m : ℕ} (hm : r ≤ m)
    (hW : ∀ i, ∃ (E' : ℕ → Subgame S) (r' k : ℕ), k ≤ m ∧ G.ClearWitness sstar i E' r' k)
    {br : ∀ i, (∀ j, S j) → S i} (hbr : IsBRRule G br) {N : ℕ}
    (hR : ∀ σ : ∀ i, RStrategy S i, HasRounds (M.acts σ) N m)
    (hbdd : ∀ i, BddBelow (Set.range (G.utility i))) (i : ι) (τ : RStrategy S i) :
    (∀ t, N ≤ t → M.prof (brStrategy M br) t = sstar) ∧
    limsup (fun t => G.utility i (M.prof (update (brStrategy M br) i τ) t)) atTop ≤
      limsup (fun t => G.utility i (M.prof (brStrategy M br) t)) atTop := by
  have hconv := theorem_2_7_convergence M hE hbr hm (hR _)
  refine ⟨hconv, ?_⟩
  have hlim : limsup (fun t => G.utility i (M.prof (brStrategy M br) t)) atTop =
      G.utility i sstar := by
    apply Tendsto.limsup_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with t ht
    rw [hconv t ht]
  rw [hlim]
  obtain ⟨E', r', k, hkm, hWi⟩ := hW i
  obtain ⟨T, hTmono, hTN, hT⟩ := hR (update (brStrategy M br) i τ)
  have hdev := M.deviation_le hWi hbr _ (fun j hj => by simp [hj])
    ⟨T, hTmono, (hTmono hkm).trans hTN, fun k' hk' => hT k' (by omega)⟩
  obtain ⟨b, hb⟩ := hbdd i
  refine limsup_le_of_le ?_ ?_
  · exact isCoboundedUnder_le_of_le atTop (fun t => hb ⟨_, rfl⟩)
  · filter_upwards [eventually_ge_atTop N] with t ht
    exact hdev t ht

end Podc.BestResponseMechanisms
