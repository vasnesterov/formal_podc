-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/LockStep/Basic.lean (additions)
import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel
import Mathlib

/-!
# Lock-step Byzantine model: basic API complements

Small general facts about CSLib's synchronous lock-step model (`Cslib.Byzantine.LockStep`) that
several formalized papers need:

* `atMost t`: the threshold adversary structure (`≤ t` Byzantine parties), with `mem_atMost`,
  `coe_mem_atMost`, `atMost_mono`, `eq_empty_of_mem_atMost_zero`;
* `Scenario.honestFinset`: the honest parties as a `Finset`, with `card_honestFinset`;
* `deliver_honest`, `deliver_byz`: what a round delivers from honest / Byzantine senders;
  `exists_of_mem_hist`, `getElem?_hist`: inboxes of a history are the delivered inboxes;
* `hist_eq_of_send_eq`, `status_comapInput`: histories depend only on the send function;
  status under input translation;
* `FirstSome` helpers: `firstSome_shift` (skip silent rounds), `firstSome_iff_of_ne` (a single
  possible decision round), `firstSome_iff_of_forall` (constant from round `0`),
  `firstSome_map_iff`, and `firstSome?`, the first `some` value of a sequence.
-/

namespace Cslib.Byzantine.LockStep

variable {P I M O : Type*}

/-! ### Threshold adversaries -/

section AtMost

/-- The threshold adversary structure: at most `t` Byzantine parties. -/
def atMost (t : ℕ) : AdvStructure P := {B | B.ncard ≤ t}

variable {t t' : ℕ} {B : Set P}

/-- Membership in the threshold structure. -/
@[simp] lemma mem_atMost : B ∈ (atMost t : AdvStructure P) ↔ B.ncard ≤ t := Iff.rfl

/-- A finset is admissible iff it has at most `t` elements. -/
lemma coe_mem_atMost (F : Finset P) : (F : Set P) ∈ (atMost t : AdvStructure P) ↔ F.card ≤ t := by
  simp [Set.ncard_coe_finset]

/-- The threshold structure grows with the threshold. -/
lemma atMost_mono (h : t ≤ t') : (atMost t : AdvStructure P) ⊆ atMost t' :=
  fun _ hB => le_trans hB h

/-- With threshold `0`, the only admissible set is `∅`. -/
lemma eq_empty_of_mem_atMost_zero [Finite P] (h : B ∈ (atMost 0 : AdvStructure P)) : B = ∅ :=
  (Set.ncard_eq_zero (Set.toFinite _)).1 (Nat.le_zero.1 h)

end AtMost

/-! ### Honest parties as a finset -/

section HonestFinset

variable [Fintype P] (s : Scenario P I M)

open Classical in
/-- The honest parties of a scenario, as a `Finset`. -/
noncomputable def Scenario.honestFinset : Finset P := Finset.univ.filter (· ∉ s.byz)

/-- Membership in `honestFinset`. -/
@[simp] lemma Scenario.mem_honestFinset {p : P} : p ∈ s.honestFinset ↔ p ∉ s.byz := by
  classical simp [Scenario.honestFinset]

/-- `honestFinset` as a set is `s.honest`. -/
@[simp] lemma Scenario.coe_honestFinset : (s.honestFinset : Set P) = s.honest := by
  ext p; simp [Scenario.honest]

/-- The number of honest parties is `n` minus the number of Byzantine parties. -/
lemma Scenario.card_honestFinset : s.honestFinset.card = Fintype.card P - s.byz.ncard := by
  classical
  rw [← Set.ncard_coe_finset, coe_honestFinset, Scenario.honest, Set.ncard_compl,
    Nat.card_eq_fintype_card]

/-- With at most `t` Byzantine parties, at least `n - t` parties are honest. -/
lemma Scenario.sub_le_card_honestFinset {t : ℕ} (h : s.byz.ncard ≤ t) :
    Fintype.card P - t ≤ s.honestFinset.card := by
  rw [card_honestFinset]; omega

end HonestFinset

/-! ### Histories and deliveries -/

section Hist

variable (G : SimpleGraph P) (alg : Protocol P I M O) (s : Scenario P I M)

/-- A reliable link from an honest neighbour delivers the protocol message. -/
lemma deliver_honest (hrel : s.Reliable) {h : P → History P M} {r : ℕ} {q p : P}
    (hq : q ∉ s.byz) (hadj : G.Adj q p) :
    deliver G alg s h r q p = alg.send q (s.input q) (h q) p := by
  simp [deliver, hadj, hq, hrel r q p]

/-- A Byzantine neighbour delivers the adversary's message. -/
lemma deliver_byz {h : P → History P M} {r : ℕ} {q p : P} (hq : q ∈ s.byz) (hadj : G.Adj q p) :
    deliver G alg s h r q p = s.adv r q p := by
  simp [deliver, hadj, hq]

/-- An inbox occurring in a history is the inbox delivered in an earlier round. -/
lemma exists_of_mem_hist {r : ℕ} {p : P} {ib : Inbox P M} (h : ib ∈ hist G alg s r p) :
    ∃ r' < r, ib = fun q => deliver G alg s (hist G alg s r') r' q p := by
  induction r with
  | zero => simp at h
  | succ r ih =>
    rw [hist_succ, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · obtain ⟨r', hr', e⟩ := ih h; exact ⟨r', by omega, e⟩
    · exact ⟨r, by omega, rfl⟩

/-- The `k`-th inbox of a history is the inbox delivered in round `k`. -/
lemma getElem?_hist {k r : ℕ} (hk : k < r) (p : P) :
    (hist G alg s r p)[k]? = some (fun q => deliver G alg s (hist G alg s k) k q p) := by
  rw [← List.getElem?_take_of_lt (l := hist G alg s r p) (j := k + 1) (by omega),
    take_hist G alg s (show k + 1 ≤ r by omega), hist_succ, List.getElem?_append_right (by simp)]
  simp

/-- Histories only depend on the send function of the protocol. -/
lemma hist_eq_of_send_eq {O' : Type*} {alg' : Protocol P I M O'} (h : alg.send = alg'.send) :
    hist G alg s = hist G alg' s := by
  funext r
  induction r with
  | zero => rfl
  | succ r ih =>
    funext q
    rw [hist_succ, hist_succ, ih]
    simp only [deliver, h]

/-- The status under translated inputs is the status in the scenario with translated inputs. -/
lemma status_comapInput {I' : Type*} (f : I' → I) (s : Scenario P I' M) (r : ℕ) (p : P) :
    status G (alg.comapInput f) s r p = status G alg (s.mapInput f) r p := by
  simp only [status, hist_comapInput]; rfl

end Hist

/-! ### First decisions -/

section FirstSome

variable {f : ℕ → Option O} {o : O}

/-- `FirstSome` after `n` silent steps. -/
lemma firstSome_shift (n : ℕ) (hf : ∀ r < n, f r = none) :
    FirstSome f o ↔ FirstSome (fun r => f (n + r)) o := by
  constructor
  · rintro ⟨r, hr, hlt⟩
    have hnr : n ≤ r := by by_contra h; rw [hf r (by omega)] at hr; simp at hr
    exact ⟨r - n, by simp [Nat.add_sub_cancel' hnr, hr], fun r' hr' => hlt _ (by omega)⟩
  · rintro ⟨r, hr, hlt⟩
    refine ⟨n + r, hr, fun r' hr' => ?_⟩
    rcases Nat.lt_or_ge r' n with h | h
    · exact hf r' h
    · have := hlt (r' - n) (by omega); simp only at this; rwa [Nat.add_sub_cancel' h] at this

/-- If `f` can only be `some` at step `r₀`, its first value is `f r₀`. -/
lemma firstSome_iff_of_ne (r₀ : ℕ) (hne : ∀ r, r ≠ r₀ → f r = none) :
    FirstSome f o ↔ f r₀ = some o := by
  constructor
  · rintro ⟨r, hr, -⟩
    by_cases h : r = r₀
    · rwa [h] at hr
    · rw [hne r h] at hr; cases hr
  · intro h; exact ⟨r₀, h, fun r hr => hne r (Nat.ne_of_lt hr)⟩

/-- A sequence that is `some v` from step `0` on has first value `v`. -/
lemma firstSome_iff_of_forall {v : O} (h : ∀ r, f r = some v) : FirstSome f o ↔ o = v := by
  constructor
  · rintro ⟨r, hr, -⟩; rw [h] at hr; exact (Option.some_injective _ hr).symm
  · rintro rfl; exact ⟨0, h 0, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- First values of a mapped sequence are images of first values. -/
lemma firstSome_map_iff {O' : Type*} {g : O → O'} {o' : O'} :
    FirstSome (fun r => (f r).map g) o' ↔ ∃ o, FirstSome f o ∧ g o = o' := by
  constructor
  · rintro ⟨r, hr, hlt⟩
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨o, ⟨r, ho, fun r' h => Option.map_eq_none_iff.mp (hlt r' h)⟩, rfl⟩
  · rintro ⟨o, ⟨r, ho, hlt⟩, rfl⟩
    exact ⟨r, by simp [ho], fun r' h => by simp [hlt r' h]⟩

open Classical in
/-- The first `some` value of a sequence (`none` if there is none). -/
noncomputable def firstSome? (f : ℕ → Option O) : Option O :=
  if h : ∃ r, (f r).isSome then f (Nat.find h) else none

/-- `firstSome?` returns exactly the first `some` value. -/
lemma firstSome?_eq_some_iff : firstSome? f = some o ↔ FirstSome f o := by
  classical
  unfold firstSome?
  split_ifs with h
  · constructor
    · intro hx
      refine ⟨Nat.find h, hx, fun r' hr' => ?_⟩
      have := Nat.find_min h hr'
      simpa using this
    · rintro ⟨r, hr, hmin⟩
      rcases lt_or_eq_of_le (Nat.find_min' h (show (f r).isSome by simp [hr])) with hlt | heq
      · have := Nat.find_spec h
        rw [hmin _ hlt] at this
        simp at this
      · rw [heq, hr]
  · simp only [false_iff]
    rintro ⟨r, hr, -⟩
    exact h ⟨r, by simp [hr]⟩

/-- `firstSome?` is defined iff the sequence takes some `some` value. -/
lemma isSome_firstSome?_iff : (firstSome? f).isSome ↔ ∃ r, (f r).isSome := by
  classical
  unfold firstSome?
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => Nat.find_spec h⟩
  · simpa using h

end FirstSome

end Cslib.Byzantine.LockStep
