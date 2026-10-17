import Papers.PODC2026.AgreementDCK.Necessity

/-!
# Sufficiency of dynamic common knowledge (Theorem 1.7)

David–Moses, *Brief Announcement: What is Agreement About if not Common Knowledge?*, PODC 2026,
Theorem 1.7. The paper gives no proof; the construction and proof here are ours.

Given run facts `θ v` and local profiles `ψ v` satisfying Θ-Validity, Θ-Exclusivity and
Θ-Epistemic Sufficiency, the *extended protocol* `P_A` runs `P` unchanged (same system of runs and
local states) and adds the decision rule

  `newDecᵢ(v) := ψᵢ(v) ∧ K_i (i ∈ N → θ_v)`,

i.e. process `i` decides `v` when it is in its trigger state `ψᵢ(v)` and believes `θ_v`
(nonfaulty knowledge without the conjunct `i ∈ N`, which is not local). This rule is local, so it
is a legitimate decision rule (`theorem_1_7`, part `DecLocal`). We prove:

* `P_A` satisfies AoN for every value, Agreement and `A`'s validity condition;
* decisions are *conscious* in the paper's sense: once a nonfaulty process decides it keeps
  satisfying its decision condition (`newDec_stable`; this is where the memory hypothesis is used);
* if the run has a nonfaulty process, the nonfaulty processes decide `v` iff `θ_v`
  (`allDecide_newDec_iff`); without any nonfaulty process this "iff" of the paper is false
  (`theorem_1_7_iff_false_without_nonfaulty`);
* if `⊨ ⋁_v θ_v` then `P_A` satisfies Decision.

We also prove the converse remark of the paper ("underlying the design of every AoN protocol is a
set of facts Θ as described in Theorem 1.7") for protocols whose nonfaulty processes remember their
decisions (`exists_theta_of_AoN`), and show by a counterexample that some memory assumption is
needed (`no_theta_for_forgetful_protocol`).
-/

open Cslib.Knowledge Cslib.Knowledge.RunFact Cslib.Knowledge.System

namespace Podc.Knowledge

namespace Decisions

variable {ι R V : Type*} {L : ι → Type*} {S : System ι R L}

/-- The decision rule added by Theorem 1.7: `i` decides `v` when `ψᵢ(v)` holds and `i` knows that
`θ_v` holds if `i` is nonfaulty. -/
def newDec (S : System ι R L) (θ : V → R → Prop) (ψ : V → ι → Fact R) : ι → V → Fact R :=
  fun i v r t => ψ v i r t ∧ S.K i (fun r' _ => i ∈ S.nf r' → θ v r') r t

/-- The hypotheses of Theorem 1.7 on `Θ = {θ_v}` and the profiles `𝛙(v)`. -/
structure Sufficient (S : System ι R L) (valid θ : V → R → Prop) (ψ : V → ι → Fact R) : Prop where
  /-- (1) Θ-Validity: `⊨ θ_v → valid(v)`. -/
  validity : ∀ v r, θ v r → valid v r
  /-- (2) Θ-Exclusivity: `⊨ θ_v → ¬ θ_w` for `w ≠ v`. -/
  exclusive : ∀ v w r, v ≠ w → θ v r → ¬ θ w r
  /-- Each `𝛙(v)` is a local profile. -/
  local_profile : ∀ v, S.IsLocalProfile (ψ v)
  /-- (3a) `⊨ θ_v → C^N@𝛙(v) (θ_v)`. -/
  ck : ∀ v r, θ v r → S.CN (ψ v) (lift (θ v)) r
  /-- (3b) Nonfaulty processes remember being in `𝛙(v)`. -/
  memory : ∀ v r, ∀ i ∈ S.nf r, ∀ t t', t < t' → ψ v i r t → ψ v i r t'

variable {valid θ : V → R → Prop} {ψ : V → ι → Fact R}

lemma newDec_local (hloc : ∀ v, S.IsLocalProfile (ψ v)) : DecLocal S (newDec S θ ψ) := by
  intro i v w w' h
  exact and_congr ((hloc v i) w w' h) ((isLocal_K i _) w w' h)

/-- A nonfaulty process that decides `v` in `P_A` is in a run satisfying `θ_v`. -/
lemma theta_of_newDec {i : ι} {v : V} {r : R} {t : ℕ} (hi : i ∈ S.nf r)
    (h : newDec S θ ψ i v r t) : θ v r :=
  belief_true (φ := lift (θ v)) hi h.2

/-- If `θ_v` holds, every nonfaulty process decides `v` in `P_A`. Only `⊨ θ_v → E^N@𝛙(v) (θ_v)` is
used, not the full `C^N`. -/
lemma allDecide_newDec_of_EN (hE : ∀ v r, θ v r → S.EN (ψ v) (lift (θ v)) r) {v : V} {r : R}
    (h : θ v r) : allDecide S (newDec S θ ψ) v r := by
  intro i hi
  obtain ⟨t, ht⟩ := (hE v r h i hi).1
  exact ⟨t, ht, ((hE v r h i hi).2 t ht).2⟩

/-- Conscious decisions: once a nonfaulty process satisfies its decision condition for `v`, it
keeps satisfying it (uses the memory hypothesis and `θ_v → E^N@𝛙(v) (θ_v)`). -/
theorem newDec_stable (hS : Sufficient S valid θ ψ) : Stable S (newDec S θ ψ) := by
  intro i v r t t' hi htt' h
  rcases htt'.lt_or_eq with hlt | rfl
  · have hψ := hS.memory v r i hi t t' hlt h.1
    exact ⟨hψ, ((hS.ck v r (theta_of_newDec hi h)).EN i hi).2 t' hψ |>.2⟩
  · exact h

/-- **Theorem 1.7 (DCK is sufficient for agreement)**, our formalization. Under hypotheses (1)–(3),
the decision rule `newDec` is local, AoN for every value, satisfies Agreement and `A`'s validity
condition, its decisions are stable for nonfaulty processes, and in every run `θ_v` implies that all
nonfaulty processes decide `v`, while a nonfaulty decision on `v` implies `θ_v`; if `⊨ ⋁_v θ_v`,
it satisfies Decision. The paper's "the nonfaulty processes decide `v` in `r` iff `r ⊨ θ_v`" is
`allDecide_newDec_iff` (requires a nonfaulty process in `r`). -/
theorem theorem_1_7 (hS : Sufficient S valid θ ψ) :
    DecLocal S (newDec S θ ψ) ∧ (∀ v, AoN S (newDec S θ ψ) v) ∧ Agreement S (newDec S θ ψ) ∧
      Validity S (newDec S θ ψ) valid ∧ Stable S (newDec S θ ψ) ∧
      (∀ v r, θ v r → allDecide S (newDec S θ ψ) v r) ∧
      (∀ v r, ∀ i ∈ S.nf r, ∀ t, newDec S θ ψ i v r t → θ v r) ∧
      ((∀ r, ∃ v, θ v r) → Decision S (newDec S θ ψ)) := by
  have hE : ∀ v r, θ v r → S.EN (ψ v) (lift (θ v)) r := fun v r h => (hS.ck v r h).EN
  refine ⟨newDec_local hS.local_profile, ?_, ?_, ?_, newDec_stable hS,
    fun v r h => allDecide_newDec_of_EN hE h, fun v r i hi t h => theta_of_newDec hi h, ?_⟩
  · exact fun v i r t hi h => allDecide_newDec_of_EN hE (theta_of_newDec hi h)
  · intro i j r t t' v w hi hj hv hw
    by_contra hne
    exact hS.exclusive v w r hne (theta_of_newDec hi hv) (theta_of_newDec hj hw)
  · exact fun v i r t hi h => hS.validity v r (theta_of_newDec hi h)
  · intro hall r i hi
    obtain ⟨v, hv⟩ := hall r
    obtain ⟨t, ht⟩ := allDecide_newDec_of_EN hE hv i hi
    exact ⟨v, t, ht⟩

/-- Theorem 1.7, "for every run `r` of `P_A` the nonfaulty processes decide `v` in `r` iff
`r ⊨ θ_v`", for runs with at least one nonfaulty process. -/
theorem allDecide_newDec_iff (hS : Sufficient S valid θ ψ) {v : V} {r : R}
    (hne : (S.nf r).Nonempty) : allDecide S (newDec S θ ψ) v r ↔ θ v r := by
  refine ⟨fun h => ?_, (theorem_1_7 hS).2.2.2.2.2.1 v r⟩
  obtain ⟨i, hi⟩ := hne
  obtain ⟨t, ht⟩ := h i hi
  exact theta_of_newDec hi ht

/-- Theorem 1.7 holds with hypothesis (3a) weakened to `⊨ θ_v → E^N@𝛙(v) (θ_v)`: the two are
equivalent by the induction rule. -/
theorem sufficient_of_EN (hval : ∀ v r, θ v r → valid v r)
    (hexcl : ∀ v w r, v ≠ w → θ v r → ¬ θ w r) (hloc : ∀ v, S.IsLocalProfile (ψ v))
    (hE : ∀ v r, θ v r → S.EN (ψ v) (lift (θ v)) r)
    (hmem : ∀ v r, ∀ i ∈ S.nf r, ∀ t t', t < t' → ψ v i r t → ψ v i r t') :
    Sufficient S valid θ ψ :=
  ⟨hval, hexcl, hloc, fun v => CN_self_of_EN_self (hE v), hmem⟩

/-! ### The "iff" fails in runs without nonfaulty processes -/

/-- **Counterexample (degenerate case).** In a system with a single run in which every process is
faulty, `Θ = {θ_v}` with all `θ_v` false satisfies all hypotheses of Theorem 1.7 for any
validity condition, but "the nonfaulty processes decide `v`" holds vacuously while `θ_v` does
not. So the last-but-one claim of Theorem 1.7 needs `N(r) ≠ ∅`. -/
theorem theorem_1_7_iff_false_without_nonfaulty :
    ∃ (S : System Unit Unit (fun _ => Unit)) (valid θ : Bool → Unit → Prop)
      (ψ : Bool → Unit → Fact Unit),
      Sufficient S valid θ ψ ∧ ∃ v r, allDecide S (newDec S θ ψ) v r ∧ ¬ θ v r := by
  refine ⟨⟨fun _ _ _ => (), fun _ => ∅⟩, fun _ _ => True, fun _ _ => False, fun _ _ _ _ => True,
    ⟨fun _ _ _ => trivial, fun _ _ _ _ h => h.elim, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ h => h.elim, fun _ _ _ hi => by simp at hi⟩, true, (), ?_, fun h => h⟩
  intro i hi
  simp at hi

/-! ### The converse: every AoN protocol has an underlying Θ (with memory of decisions) -/

/-- **Converse to Theorem 1.7** (the paper's remark "underlying the design of every AoN protocol
is a set of facts Θ as described in Theorem 1.7"), our formalization: for a protocol with local
decisions that is AoN for every value and satisfies Agreement and the validity condition, and in
which nonfaulty processes remember their decisions, `θ_v := "some nonfaulty process decides v"`
and the profiles `𝛅(v)` satisfy the hypotheses of Theorem 1.7, and the protocol's own decisions
are exactly those described by Θ. -/
theorem exists_theta_of_AoN {dec : ι → V → Fact R} {valid : V → R → Prop}
    (hloc : DecLocal S dec) (haon : ∀ v, AoN S dec v) (hagr : Agreement S dec)
    (hval : Validity S dec valid) (hstab : Stable S dec) :
    Sufficient S valid (fun v r => ∃ i ∈ S.nf r, ∃ t, dec i v r t) (δ dec) ∧
      ∀ v r, (S.nf r).Nonempty → (allDecide S dec v r ↔ ∃ i ∈ S.nf r, ∃ t, dec i v r t) := by
  refine ⟨⟨?_, ?_, fun v i => hloc i v, ?_, ?_⟩, ?_⟩
  · rintro v r ⟨i, hi, t, ht⟩
    exact hval v i r t hi ht
  · rintro v w r hvw ⟨i, hi, t, ht⟩ ⟨j, hj, t', ht'⟩
    exact hvw (hagr i j r t t' v w hi hj ht ht')
  · rintro v r ⟨i, hi, t, ht⟩
    exact CN_of_precondition hloc (haon v) (fun i r t hi hd => ⟨i, hi, t, hd⟩) r
      (haon v i r t hi ht)
  · exact fun v r i hi t t' htt' h => hstab i v r t t' hi htt'.le h
  · intro v r hne
    constructor
    · intro h
      obtain ⟨i, hi⟩ := hne
      obtain ⟨t, ht⟩ := h i hi
      exact ⟨i, hi, t, ht⟩
    · rintro ⟨i, hi, t, ht⟩
      exact haon v i r t hi ht

/-- **Counterexample: the converse needs memory.** A one-process, failure-free system with two
runs `b ∈ {false, true}`: the process learns `b` at time 1 (local state `some b`) and forgets it
afterwards (local state `none` at all other times); it decides `b` exactly at time 1. This
protocol has local decisions, is AoN, satisfies Agreement, Validity (`valid(v) := b = v`) and
Decision. Yet no Θ with profiles as in Theorem 1.7 describes its decisions: there are no run facts
`θ_v` with `θ_v ↔ all_decide(v)` and local profiles `𝛙(v)` that nonfaulty processes remember
such that `⊨ θ_v → E^N@𝛙(v) (θ_v)` (hence a fortiori none with `C^N`). -/
theorem no_theta_for_forgetful_protocol :
    let S : System Unit Bool (fun _ => Option Bool) :=
      ⟨fun _ b t => if t = 1 then some b else none, fun _ => Set.univ⟩
    let dec : Unit → Bool → Fact Bool := fun _ v b t => t = 1 ∧ b = v
    (DecLocal S dec ∧ (∀ v, AoN S dec v) ∧ Agreement S dec ∧
        Validity S dec (fun v b => b = v) ∧ Decision S dec) ∧
      ¬ ∃ (θ : Bool → Bool → Prop) (ψ : Bool → Unit → Fact Bool),
        (∀ v r, θ v r ↔ allDecide S dec v r) ∧ (∀ v, S.IsLocalProfile (ψ v)) ∧
        (∀ v r, θ v r → S.EN (ψ v) (lift (θ v)) r) ∧
        (∀ v r, ∀ i ∈ S.nf r, ∀ t t', t < t' → ψ v i r t → ψ v i r t') := by
  intro S dec
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine fun i v => isLocal_iff.2 fun r t r' t' h => ?_
    simp only [S, dec] at h ⊢
    split_ifs at h with h1 h2 h2 <;> simp_all
  · intro v i r t _ h j _
    exact ⟨t, h⟩
  · intro i j r t t' v w _ _ hv hw
    exact hv.2.symm.trans hw.2
  · intro v i r t _ h
    exact h.2
  · intro r i _
    exact ⟨r, 1, rfl, rfl⟩
  · rintro ⟨θ, ψ, hθ, -, hE, hmem⟩
    have htrue : θ true true := (hθ true true).2 fun _ _ => ⟨1, rfl, rfl⟩
    have hfalse : ¬ θ true false := fun h => by
      obtain ⟨t, -, ht⟩ := (hθ true false).1 h () (Set.mem_univ _)
      exact Bool.false_ne_true ht
    obtain ⟨⟨t, ht⟩, hK⟩ := hE true true htrue () (Set.mem_univ _)
    -- At any time `t' ≠ 1` the local state is `none`, which is also the state at time `0` of the
    -- run `false`, where `θ_true` fails.
    have hnot : ∀ t', t' ≠ 1 → ψ true () true t' → False := fun t' ht' hψ =>
      hfalse ((hK t' hψ).2 (false, 0) (by simp [S, ht']) (Set.mem_univ _))
    have h1 : t = 1 := by_contra fun h => hnot t h ht
    exact hnot 2 (by decide) (hmem true true () (Set.mem_univ _) t 2 (by omega) ht)

end Decisions

end Podc.Knowledge
