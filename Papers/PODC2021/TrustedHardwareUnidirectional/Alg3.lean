import Mathlib

/-!
# Claim of Section 4.2: unidirectional rounds implement SRB (Algorithm 3), safety core

We formalize the certificate-level argument of Lemmas 3 (Case 1) and 4 for one instance of
Algorithm 3: a fixed sender `p` and sequence number `k`. An instance (`Inst`) records
* `signed`: the values `v` such that `p` signed `(k, v)` (one value if `p` is correct);
* `fwd r`: the value a correct `r` forwarded (line 26) in its unidirectional round;
* `heard r r'`: the value of `r'` that `r` received in that round before compiling its L1 proof
  (including `r`'s own copy, `heard r r`);
* `l1 r`: the values for which `r` issued an L1 proof.

`Valid` collects what the model guarantees: copies carry the sender's signature (`sValid`), copies
from correct processes are genuine, Byzantine processes can only build L1 proofs of
sender-signed values, and unidirectionality of the forwarding round (both forwarders take part in
the same round instance).

Two L1 rules for correct processes:
* `RuleText`: the rule of the text of §4.2 — at least `t+1` copies of the own value "*and no other
  value*";
* `RulePseudo`: the rule of the pseudocode (lines 29–39, `validateValue`): at least `t+1` copies of
  the own value; other values are just ignored.

An L2 proof of `v` is a set of `t+1` processes with L1 proofs of `v`; a correct process delivers
`(k, v)` once it has a valid L2 proof (lines 12–14).

* `agreement` (Lemma 3, Case 1): with `RuleText`, no two different values have L2 proofs.
* `pseudo_disagreement`: with `RulePseudo` this fails already for `n = 3`, `t = 1` (a Byzantine
  sender), so Algorithm 3 as written violates property 2 of SRB.
* `l2_signed` (Lemma 4): an L2-proved value was signed by the sender.
* `validity_core` (combinatorial core of Lemma 2): with a correct sender and `n ≥ 2t + 1`, once a
  correct process has the copies of all correct processes, `RuleText` lets it issue its L1 proof,
  and the L1 proofs of the correct processes form an L2 proof.
-/

namespace Podc.TrustedHW

namespace Alg3

variable {P Val : Type} [Fintype P] [DecidableEq P]

/-- One instance `(p, k)` of Algorithm 3 (see module docstring). -/
structure Inst (P Val : Type) where
  /-- Byzantine processes. -/
  F : Finset P
  /-- Values the sender signed with sequence number `k`. -/
  signed : Set Val
  /-- Value forwarded by each (correct) process. -/
  fwd : P → Option Val
  /-- `heard r r'`: copy of `r'` received by `r` before compiling its L1 proof. -/
  heard : P → P → Option Val
  /-- Values for which a process issued an L1 proof. -/
  l1 : P → Set Val

open Classical in
/-- The processes whose copy of `v` was received by `r`. -/
noncomputable def copies (I : Inst P Val) (r : P) (v : Val) : Finset P :=
  Finset.univ.filter fun r' => I.heard r r' = some v

/-- What the system guarantees. -/
structure Valid (I : Inst P Val) : Prop where
  fwd_signed : ∀ r, r ∉ I.F → ∀ v, I.fwd r = some v → v ∈ I.signed
  heard_signed : ∀ r r' v, I.heard r r' = some v → v ∈ I.signed
  heard_correct : ∀ r r', r' ∉ I.F → ∀ v, I.heard r r' = some v → I.fwd r' = some v
  /-- Unidirectionality of the forwarding round. -/
  unidir : ∀ r r', r ∉ I.F → r' ∉ I.F → r ≠ r' → (I.fwd r).isSome → (I.fwd r').isSome →
    I.heard r r' = I.fwd r' ∨ I.heard r' r = I.fwd r
  byz_l1 : ∀ r, r ∈ I.F → ∀ v ∈ I.l1 r, v ∈ I.signed

/-- L1 rule of the text of §4.2 ("at least `t+1` copies of the same value as their own, and no
other value"). -/
def RuleText (I : Inst P Val) (t : ℕ) : Prop :=
  ∀ r, r ∉ I.F → ∀ v ∈ I.l1 r,
    I.fwd r = some v ∧ t + 1 ≤ (copies I r v).card ∧ ∀ r' v', I.heard r r' = some v' → v' = v

/-- L1 rule of the pseudocode of Algorithm 3 (no check for conflicting values). -/
def RulePseudo (I : Inst P Val) (t : ℕ) : Prop :=
  ∀ r, r ∉ I.F → ∀ v ∈ I.l1 r, I.fwd r = some v ∧ t + 1 ≤ (copies I r v).card

/-- `v` has an L2 proof: `t + 1` distinct processes issued L1 proofs of `v`. -/
def HasL2 (I : Inst P Val) (t : ℕ) (v : Val) : Prop :=
  ∃ S : Finset P, t + 1 ≤ S.card ∧ ∀ r ∈ S, v ∈ I.l1 r

lemma exists_correct_of_hasL2 {I : Inst P Val} {t : ℕ} (hF : I.F.card ≤ t) {v : Val}
    (h : HasL2 I t v) : ∃ r, r ∉ I.F ∧ v ∈ I.l1 r := by
  obtain ⟨S, hS, hv⟩ := h
  obtain ⟨r, hrS, hrF⟩ : ∃ r ∈ S, r ∉ I.F := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (show S ⊆ I.F from hcon)
    omega
  exact ⟨r, hrF, hv r hrS⟩

/-- **Lemma 3, Case 1** (with the rule of the text): two L2 proofs prove the same value. Hence two
correct processes never deliver different messages with the same sequence number. -/
theorem agreement {I : Inst P Val} {t : ℕ} (hI : Valid I) (hR : RuleText I t)
    (hF : I.F.card ≤ t) {v v' : Val} (h : HasL2 I t v) (h' : HasL2 I t v') : v = v' := by
  obtain ⟨r, hr, hv⟩ := exists_correct_of_hasL2 hF h
  obtain ⟨r', hr', hv'⟩ := exists_correct_of_hasL2 hF h'
  obtain ⟨h1, -, h3⟩ := hR r hr v hv
  obtain ⟨h1', -, h3'⟩ := hR r' hr' v' hv'
  by_cases hrr : r = r'
  · subst hrr; rw [h1] at h1'; exact Option.some_injective _ h1'
  · rcases hI.unidir r r' hr hr' hrr (by simp [h1]) (by simp [h1']) with h | h
    · rw [h1'] at h; exact (h3 r' v' h).symm
    · rw [h1] at h; exact h3' r v h

/-- **Lemma 4**: an L2-proved value was signed by the sender (so, for a correct sender, it was
broadcast by it). Holds for both rules. -/
theorem l2_signed {I : Inst P Val} {t : ℕ} (hI : Valid I) (hR : RulePseudo I t)
    (hF : I.F.card ≤ t) {v : Val} (h : HasL2 I t v) : v ∈ I.signed := by
  obtain ⟨r, hr, hv⟩ := exists_correct_of_hasL2 hF h
  exact hI.fwd_signed r hr v (hR r hr v hv).1

lemma RuleText.pseudo {I : Inst P Val} {t : ℕ} (h : RuleText I t) : RulePseudo I t :=
  fun r hr v hv => ⟨(h r hr v hv).1, (h r hr v hv).2.1⟩

/-- The counterexample instance: `n = 3`, `t = 1`; process `0` is the Byzantine sender and signs
both `true` and `false`; it sends `true` to `1` and `false` to `2`. In the forwarding round `2`
receives `1`'s copy (unidirectionality holds) but `1` does not receive `2`'s. Both have two copies
of their own value (their own and `0`'s) and, under the pseudocode rule, issue L1 proofs; `0`
issues L1 proofs of both values. -/
def badInst : Inst (Fin 3) Bool where
  F := {0}
  signed := Set.univ
  fwd r := if r = 1 then some true else if r = 2 then some false else none
  heard r r' :=
    if r = 1 then (if r' = 2 then none else some true)
    else if r = 2 then (if r' = 1 then some true else some false)
    else none
  l1 r := if r = 0 then Set.univ else if r = 1 then {true} else {false}

lemma badInst_valid : Valid badInst := by
  refine ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, ?_, ?_, fun _ _ _ _ => trivial⟩
  · intro r r' hr' v h
    simp only [badInst, Finset.mem_singleton] at hr' h ⊢
    fin_cases r <;> fin_cases r' <;> simp_all
  · intro r r' hr hr' hrr _ _
    simp only [badInst, Finset.mem_singleton] at hr hr' ⊢
    fin_cases r <;> fin_cases r' <;> simp_all

lemma badInst_pseudo : RulePseudo badInst 1 := by
  intro r hr v hv
  simp only [badInst, Finset.mem_singleton] at hr hv
  fin_cases r
  · exact absurd rfl hr
  · simp at hv; subst hv; refine ⟨rfl, ?_⟩
    refine le_trans (by decide : 2 ≤ ({0, 1} : Finset (Fin 3)).card) (Finset.card_le_card ?_)
    intro x hx; fin_cases hx <;> simp [copies, badInst]
  · simp at hv; subst hv; refine ⟨rfl, ?_⟩
    refine le_trans (by decide : 2 ≤ ({0, 2} : Finset (Fin 3)).card) (Finset.card_le_card ?_)
    intro x hx; fin_cases hx <;> simp [copies, badInst]

/-- **Algorithm 3 as written violates agreement** (property 2 of SRB): in `badInst`, which
satisfies all model constraints and the pseudocode's L1 rule with `n = 3 = 2t + 1`, both `true`
and `false` have L2 proofs (`{1, 0}` and `{2, 0}`), so the correct processes `1` and `2` deliver
different messages with the same sequence number. -/
theorem pseudo_disagreement :
    ∃ I : Inst (Fin 3) Bool, Valid I ∧ RulePseudo I 1 ∧ I.F.card ≤ 1 ∧
      HasL2 I 1 true ∧ HasL2 I 1 false :=
  ⟨badInst, badInst_valid, badInst_pseudo, by decide,
    ⟨{1, 0}, by decide, by intro r hr; fin_cases hr <;> simp [badInst]⟩,
    ⟨{2, 0}, by decide, by intro r hr; fin_cases hr <;> simp [badInst]⟩⟩

/-- The text's rule rejects `badInst`: process `2` heard the conflicting value `true`. -/
theorem badInst_not_text : ¬ RuleText badInst 1 := by
  intro h
  have := (h 2 (by decide) false (by simp [badInst])).2.2 1 true (by simp [badInst])
  exact Bool.noConfusion this

/-- **Combinatorial core of Lemma 2** (correct sender): if the sender signed only `v`, every
correct process forwarded `v` and has received the copies of all correct processes, and
`n ≥ 2t + 1`, then every correct process satisfies the text's L1 condition for `v`; and if all
correct processes issue their L1 proofs of `v`, then `v` has an L2 proof. -/
theorem validity_core {I : Inst P Val} {t : ℕ} (hI : Valid I) (hF : I.F.card ≤ t)
    (hn : 2 * t + 1 ≤ Fintype.card P) {v : Val} (hs : I.signed ⊆ {v})
    (hall : ∀ r, r ∉ I.F → ∀ r', r' ∉ I.F → I.heard r r' = some v) :
    (∀ r, r ∉ I.F → t + 1 ≤ (copies I r v).card ∧ ∀ r' v', I.heard r r' = some v' → v' = v) ∧
      ((∀ r, r ∉ I.F → v ∈ I.l1 r) → HasL2 I t v) := by
  have hcorr : t + 1 ≤ (Finset.univ \ I.F).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]; omega
  refine ⟨fun r hr => ⟨?_, fun r' v' h => hs (hI.heard_signed r r' v' h)⟩, fun h => ?_⟩
  · refine hcorr.trans (Finset.card_le_card fun r' hr' => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hr'
    simp only [copies, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hall r hr r' hr'
  · refine ⟨Finset.univ \ I.F, hcorr, fun r hr => ?_⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hr
    exact h r hr

/-- Non-vacuity of `agreement`: an instance satisfying all its hypotheses in which a value has an
L2 proof (correct sender `0` broadcasting `true`, no faults, `n = 3`, `t = 1`). -/
theorem agreement_nonvacuous :
    ∃ I : Inst (Fin 3) Bool, Valid I ∧ RuleText I 1 ∧ I.F.card ≤ 1 ∧ HasL2 I 1 true := by
  refine ⟨⟨∅, {true}, fun _ => some true, fun _ _ => some true, fun _ => {true}⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, by decide, ⟨{0, 1}, by decide, by intro r _; simp⟩⟩
  · intro r _ v h; simp at h; simp [h]
  · intro r r' v h; simp at h; simp [h]
  · intro r r' _ v h; exact h
  · intro r r' _ _ _ _ _; left; rfl
  · intro r hr; simp at hr
  · intro r _ v hv
    simp only [Set.mem_singleton_iff] at hv; subst hv
    refine ⟨rfl, ?_, fun _ _ h => by simpa using h.symm⟩
    refine le_trans (by decide : 2 ≤ ({0, 1} : Finset (Fin 3)).card) (Finset.card_le_card ?_)
    intro x _; simp [copies]

end Alg3

end Podc.TrustedHW
