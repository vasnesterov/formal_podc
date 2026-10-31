import Papers.PODC2014.SignatureFreeBA.Safety

/-!
# Theorem 1: the BV-broadcast algorithm of Figure 1

Mostéfaoui, Moumen, Raynal, PODC 2014, Section 3.

The BV-broadcast instance of round `r` consists of the messages `B_VAL[r](·)`. A process
*BV-broadcasts* `v` in round `r` when it broadcasts its own estimate `bval r v (some _)`
(Figure 1, line 01), and `v ∈ bin_values[r]` at `q` is `BinVal t (inbox q) r v`.

* `bv_justification` (safety, every reachable state).
* `Exec.bv_obligation`, `Exec.bv_uniformity`, `Exec.bv_termination` (liveness, every weakly
  fair execution).
* `theorem_1` collects the four properties.
-/

namespace Podc.SignatureFreeBA

open Cslib.Byzantine.AsyncBroadcast

variable {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {coin : ℕ → Bool} {x : P → Bool}
  {k : FaultKind} {σ : State P Msg Bool}

/-- Invariant behind BV-Justification: a correct process broadcasts `B_VAL[r](v)` (own or
echo) only if some correct process BV-broadcast `v`. -/
theorem bval_origin (h : Reachable (mmr t coin) x k t σ) {H : Set P} (hbad : σ.bad ⊆ Hᶜ)
    (hH : Hᶜ.ncard ≤ t) {r : ℕ} {v : Bool} :
    ∀ p ∈ H, ∀ d, (p, .bval r v d) ∈ σ.sent → ∃ s ∈ H, ∃ d', (s, .bval r v (some d')) ∈ σ.sent := by
  revert hbad
  refine Reachable.induction (Inv := fun σ => σ.bad ⊆ Hᶜ → ∀ p ∈ H, ∀ d,
    (p, .bval r v d) ∈ σ.sent → ∃ s ∈ H, ∃ d', (s, .bval r v (some d')) ∈ σ.sent)
    (by simp [State.init]) ?_ h
  intro σ σ' hr ih hst hbad'
  have hbad : σ.bad ⊆ Hᶜ := hst.bad_subset.trans hbad'
  have ih := ih hbad
  have lift : (∃ s ∈ H, ∃ d', (s, Msg.bval r v (some d')) ∈ σ.sent) →
      ∃ s ∈ H, ∃ d', (s, Msg.bval r v (some d')) ∈ σ'.sent := fun ⟨s, hs, d', hm⟩ =>
    ⟨s, hs, d', hst.sent_subset hm⟩
  cases hst with
  | send p' m hb hg =>
    intro p hp d hm
    rcases Set.mem_insert_iff.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      cases d with
      | none =>
        obtain ⟨s, hs, d', hm'⟩ := exists_bval_sender_mem hH hg.1
        exact lift (ih s hs d' (hr.genuine hm' fun hb => hbad hb hs))
      | some d => exact ⟨p, hp, d, Set.mem_insert _ _⟩
    · exact lift (ih p hp d hm)
  | _ => exact ih

/-- **BV-Justification.** If `v ∈ bin_values[r]` at some process, `v` was BV-broadcast in
round `r` by a correct process. -/
theorem bv_justification (h : Reachable (mmr t coin) x k t σ) {H : Set P} (hbad : σ.bad ⊆ Hᶜ)
    (hH : Hᶜ.ncard ≤ t) {q : P} {r : ℕ} {v : Bool} (hv : BinVal t (σ.inbox q) r v) :
    ∃ s ∈ H, ∃ d, (s, .bval r v (some d)) ∈ σ.sent := by
  obtain ⟨s, hs, d, hm⟩ := exists_bval_sender_mem (H := H) (c := 2 * t) (by omega) hv
  exact bval_origin h hbad hH s hs d (h.genuine hm fun hb => hbad hb hs)

namespace Exec

variable (E : Exec (mmr t coin) x k t) (hF : E.Fair)
include hF

/-- If `t + 1` correct processes broadcast `B_VAL[r](v)`, every correct process eventually
does (Figure 1, lines 02–03). -/
theorem eventually_bval {T : Set P} (hT : ∀ s ∈ T, E.Correct s) (hTc : t + 1 ≤ T.ncard)
    {r : ℕ} {v : Bool} (hTs : ∀ s ∈ T, ∃ i d, (s, .bval r v d) ∈ (E.σ i).sent) {q : P}
    (hq : E.Correct q) : ∃ i d, (q, .bval r v d) ∈ (E.σ i).sent := by
  obtain ⟨i, hi⟩ := E.eventually_rcv_all' hF hT (φ := IsBval r v)
    (fun s hs => by obtain ⟨i, d, h⟩ := hTs s hs; exact ⟨i, _, ⟨d, rfl⟩, h⟩) hq
  obtain ⟨j, m', ⟨d, rfl⟩, hj⟩ := E.eventually_sent hF hq (φ := IsBval r v) (m := .bval r v none)
    ⟨none, rfl⟩ (i := i) fun j hij hno => ⟨hTc.trans (le_cntP fun s hs => by
      obtain ⟨m, hm, hm'⟩ := hi s hs
      exact ⟨m, E.rcv_mono hij hm', hm⟩), fun d hd => hno _ ⟨d, rfl⟩ hd⟩
  exact ⟨j, d, hj⟩

omit hF in
/-- If all correct processes eventually broadcast `B_VAL[r](v)`, eventually `v` stays in
`bin_values[r]` of every correct process. -/
theorem eventually_binVal_of_all (hF : E.Fair) (ht : 3 * t < Fintype.card P) {r : ℕ} {v : Bool}
    (hall : ∀ s, E.Correct s → ∃ i d, (s, .bval r v d) ∈ (E.σ i).sent) {q : P}
    (hq : E.Correct q) : ∃ i, ∀ j, i ≤ j → BinVal t ((E.σ j).inbox q) r v := by
  obtain ⟨i, hi⟩ := E.eventually_rcv_all' hF (S := {s | E.Correct s}) (fun s hs => hs)
    (φ := IsBval r v) (fun s hs => by
      obtain ⟨i, d, h⟩ := hall s hs; exact ⟨i, _, ⟨d, rfl⟩, h⟩) hq
  refine ⟨i, fun j hij => ?_⟩
  have h1 := E.card_sub_le_ncard_correct
  have h2 : {s | E.Correct s}.ncard ≤ bvCnt ((E.σ j).inbox q) r v := le_cntP fun s hs => by
    obtain ⟨m, hm, hm'⟩ := hi s hs
    exact ⟨m, E.rcv_mono hij hm', hm⟩
  unfold BinVal
  omega

/-- If `t + 1` correct processes broadcast `B_VAL[r](v)` (own or echo), eventually `v` stays in
`bin_values[r]` of every correct process. -/
theorem eventually_binVal (ht : 3 * t < Fintype.card P) {T : Set P} (hT : ∀ s ∈ T, E.Correct s)
    (hTc : t + 1 ≤ T.ncard) {r : ℕ} {v : Bool}
    (hTs : ∀ s ∈ T, ∃ i d, (s, .bval r v d) ∈ (E.σ i).sent) {q : P} (hq : E.Correct q) :
    ∃ i, ∀ j, i ≤ j → BinVal t ((E.σ j).inbox q) r v :=
  eventually_binVal_of_all E hF ht (fun _ hs => eventually_bval E hF hT hTc hTs hs) hq

/-- **BV-Obligation.** If at least `t + 1` correct processes BV-broadcast `v` in round `r`, `v`
is eventually (and then forever) in `bin_values[r]` of every correct process. -/
theorem bv_obligation (ht : 3 * t < Fintype.card P) {T : Set P} (hT : ∀ s ∈ T, E.Correct s)
    (hTc : t + 1 ≤ T.ncard) {r : ℕ} {v : Bool}
    (hTs : ∀ s ∈ T, ∃ i d, (s, .bval r v (some d)) ∈ (E.σ i).sent) {q : P} (hq : E.Correct q) :
    ∃ i, ∀ j, i ≤ j → BinVal t ((E.σ j).inbox q) r v :=
  eventually_binVal E hF ht hT hTc (fun s hs => by
    obtain ⟨i, d, h⟩ := hTs s hs; exact ⟨i, some d, h⟩) hq

/-- **BV-Uniformity.** If `v ∈ bin_values[r]` at a process at some time, eventually `v` stays in
`bin_values[r]` of every correct process. -/
theorem bv_uniformity (ht : 3 * t < Fintype.card P) {p : P} {i : ℕ} {r : ℕ} {v : Bool}
    (hp : BinVal t ((E.σ i).inbox p) r v) {q : P} (hq : E.Correct q) :
    ∃ i, ∀ j, i ≤ j → BinVal t ((E.σ j).inbox q) r v := by
  let S := {s | ∃ m ∈ (E.σ i).inbox p s, IsBval r v m}
  let T := S ∩ {s | E.Correct s}
  have hT : t + 1 ≤ T.ncard := by
    have := E.ncard_le_ncard_inter_correct_add S
    have hp' : 2 * t + 1 ≤ S.ncard := hp
    show t + 1 ≤ (S ∩ {s | E.Correct s}).ncard
    omega
  refine eventually_binVal E hF ht (T := T) (fun s hs => hs.2) hT (fun s hs => ?_) hq
  obtain ⟨m, hm, d, rfl⟩ := hs.1
  exact ⟨i, d, (E.reachable i).genuine hm (hs.2 i)⟩

/-- **BV-Termination.** If every correct process BV-broadcasts a value in round `r`,
eventually `bin_values[r]` of every correct process is (and stays) non-empty. -/
theorem bv_termination (ht : 3 * t < Fintype.card P) {r : ℕ}
    (hall : ∀ s, E.Correct s → ∃ i v d, (s, .bval r v (some d)) ∈ (E.σ i).sent) {q : P}
    (hq : E.Correct q) : ∃ v i, ∀ j, i ≤ j → BinVal t ((E.σ j).inbox q) r v := by
  let C := {s | E.Correct s}
  let Cv : Bool → Set P := fun v => {s | E.Correct s ∧ ∃ i d, (s, .bval r v (some d)) ∈ (E.σ i).sent}
  have hcov : C ⊆ Cv true ∪ Cv false := by
    intro s hs
    obtain ⟨i, v, d, h⟩ := hall s hs
    cases v
    · exact Or.inr ⟨hs, i, d, h⟩
    · exact Or.inl ⟨hs, i, d, h⟩
  have h1 : C.ncard ≤ (Cv true).ncard + (Cv false).ncard :=
    (Set.ncard_le_ncard hcov).trans (Set.ncard_union_le _ _)
  have h2 : Fintype.card P - t ≤ C.ncard := E.card_sub_le_ncard_correct
  have h3 : 2 * t + 1 ≤ Fintype.card P - t := by omega
  obtain ⟨v, hv⟩ : ∃ v, t + 1 ≤ (Cv v).ncard := by
    by_contra hne
    push Not at hne
    have := hne true
    have := hne false
    omega
  exact ⟨v, bv_obligation E hF ht (T := Cv v) (fun s hs => hs.1) hv (fun s hs => hs.2) hq⟩

end Exec

/-- **Theorem 1.** In the system model `BZ_AS[n > 3t]`, the algorithm of Figure 1 (round `r`
of `mmr`) implements BV-broadcast: BV-Obligation, BV-Justification, BV-Uniformity and
BV-Termination. -/
theorem theorem_1 (ht : 3 * t < Fintype.card P) (r : ℕ) :
    -- BV-Obligation
    (∀ E : Exec (mmr t coin) x k t, E.Fair → ∀ (T : Set P) v, (∀ s ∈ T, E.Correct s) →
      t + 1 ≤ T.ncard → (∀ s ∈ T, ∃ i d, (s, .bval r v (some d)) ∈ (E.σ i).sent) →
      ∀ q, E.Correct q → ∃ i, ∀ j, i ≤ j → BinVal t ((E.σ j).inbox q) r v) ∧
    -- BV-Justification
    (∀ σ, Reachable (mmr t coin) x k t σ → ∀ H : Set P, σ.bad ⊆ Hᶜ → Hᶜ.ncard ≤ t →
      ∀ q v, BinVal t (σ.inbox q) r v → ∃ s ∈ H, ∃ d, (s, .bval r v (some d)) ∈ σ.sent) ∧
    -- BV-Uniformity
    (∀ E : Exec (mmr t coin) x k t, E.Fair → ∀ p i v, BinVal t ((E.σ i).inbox p) r v →
      ∀ q, E.Correct q → ∃ i, ∀ j, i ≤ j → BinVal t ((E.σ j).inbox q) r v) ∧
    -- BV-Termination
    (∀ E : Exec (mmr t coin) x k t, E.Fair →
      (∀ s, E.Correct s → ∃ i v d, (s, .bval r v (some d)) ∈ (E.σ i).sent) →
      ∀ q, E.Correct q → ∃ v i, ∀ j, i ≤ j → BinVal t ((E.σ j).inbox q) r v) :=
  ⟨fun E hF _ _ hT hTc hTs _ hq => Exec.bv_obligation E hF ht hT hTc hTs hq,
    fun _ h _ hbad hH _ _ hv => bv_justification h hbad hH hv,
    fun E hF _ _ _ hp _ hq => Exec.bv_uniformity E hF ht hp hq,
    fun E hF hall _ hq => Exec.bv_termination E hF ht hall hq⟩

end Podc.SignatureFreeBA
