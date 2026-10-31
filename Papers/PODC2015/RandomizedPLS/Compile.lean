import Papers.PODC2015.RandomizedPLS.Basic
import Papers.PODC2015.RandomizedPLS.Fingerprint

/-!
# From a PLS to a one-sided RPLS with exponentially smaller certificates (Theorem 3.1 of [BFP15])

M. Baruch, P. Fraigniaud, B. Patt-Shamir. *Randomized Proof-Labeling Schemes.* PODC 2015.

Given a deterministic PLS `(ver, prover)` for `(F, P)` with labels of at most `κ` bits, the
compiled scheme is exactly the paper's:

* `compileProver prover`: the label of `v` is the list `ℓ(v), ℓ(w₁), …, ℓ(w_d)` (own label, then
  the labels of the neighbours ordered by port);
* `compileScheme ver` (an edge-independent scheme): on every port `v` sends the fingerprint
  `fpSend ℓ(v) x` of its own label (Lemma 3.3), with an independent coin `x` per port;
  `v` rejects if its label is not of the form `ℓ₀ :: ℓ₁ … ℓ_d` with `d = deg v`, otherwise it runs
  the fingerprint decider for each port `i` against `ℓᵢ` and, if all pass, outputs
  `ver (state v) ℓ₀ [ℓ₁, …, ℓ_d]`.

## Main statements

* `compile_isRPLS`: the compiled scheme accepts legal configurations with probability `1` and
  rejects illegal ones with probability `> 2/3` (`compile_sound`), whatever the labels.
* `compile_certBound`: certificates have `2 · fpBits κ ≤ 2 log₂ κ + 6` bits.
* `theorem_3_1`: Theorem 3.1 of [BFP15]; corollaries `theorem_3_1_oneSided`, `theorem_3_1_twoSided`.
-/

namespace Podc.RandomizedPLS

open Cslib.Probability Classical

variable {S : Type}

/-- The prover of Theorem 3.1: the own label followed by the labels of the neighbours, by port. -/
def compileProver (prover : ∀ c : Config S, c.V → List Bool) (c : Config S) (v : c.V) :
    List (List Bool) :=
  prover c v :: (c.nbrs v).map (prover c)

/-- The local decision of the compiled verifier: format check, a fingerprint check per port
against the corresponding entry of the label, then the deterministic verifier. -/
noncomputable def compileDec (ver : Verifier S) (s : S) :
    List (List Bool) → List (List Bool) → Bool
  | [], _ => false
  | h :: t, rs => decide (List.Forall₂ (fun b r => fpDecide b r = true) t rs) && ver s h t

/-- The compiled randomized verifier of Theorem 3.1 (edge-independent: one fingerprint
evaluation point per port). -/
noncomputable def compileScheme (ver : Verifier S) : EIScheme S (List (List Bool)) where
  Ω₀ _ ℓ _ := GaloisField 2 (fpBits (ℓ.headD []).length)
  cert _ ℓ _ _ x := fpSend (ℓ.headD []) x
  dec := compileDec ver

lemma Config.port_lt_deg (c : Config S) {v w : c.V} (hw : w ∈ c.nbrs v) :
    c.port w v < c.deg w := by
  rw [c.deg_eq, Config.port]
  exact List.idxOf_lt_length_iff.mpr (c.symm v w hw)

section

variable (ver : Verifier S) (c : Config S) (ℓ : c.V → List (List Bool))

lemma compile_sent (ω : (compileScheme ver).toRScheme.Coins c ℓ) {v w : c.V}
    (hw : w ∈ c.nbrs v) :
    (compileScheme ver).toRScheme.sent c ℓ ω w (c.port w v) =
      fpSend ((ℓ w).headD []) (ω w ⟨c.port w v, c.port_lt_deg hw⟩) := by
  simp only [RScheme.sent, EIScheme.toRScheme, c.port_lt_deg hw, ↓reduceDIte]
  rfl

-- CSLib candidate
/-- In an edge-independent scheme, an event depending on the coin of one port of one node has
the probability of that event for a single uniform coin. -/
lemma EIScheme.uprob_port {L : Type} (e : EIScheme S L) (c : Config S) (ℓ : c.V → L) (w : c.V)
    (j : Fin (c.deg w)) (p : e.Ω₀ (c.state w) (ℓ w) (c.deg w) → Prop) :
    uprob (fun ω : e.toRScheme.Coins c ℓ => p (ω w j)) = uprob p := by
  rw [uprob_apply_eq (α := fun u => e.toRScheme.Ω (c.state u) (ℓ u) (c.deg u)) w
    (fun ωw => p (ωw j))]
  exact uprob_apply_eq (α := fun _ : Fin (c.deg w) => e.Ω₀ (c.state w) (ℓ w) (c.deg w)) j p

/-- If every outcome of the coins makes some node reject, the acceptance probability is `0`. -/
lemma RScheme.accProb_eq_zero {L : Type} (σ : RScheme S L) (c : Config S) (ℓ : c.V → L)
    (h : ∀ ω, ¬ σ.AcceptsAll c ℓ ω) : σ.accProb c ℓ = 0 :=
  le_antisymm ((uprob_mono fun ω hω => h ω hω).trans uprob_false.le) (σ.accProb_nonneg c ℓ)

end

/-- Completeness of the compiled scheme: with the compiled labels of a PLS-accepted labelling,
every node accepts for every outcome of the coins. -/
lemma compile_acceptsAll (ver : Verifier S) (c : Config S) (ℓ : c.V → List Bool)
    (hacc : Accepts ver c ℓ) (ω) :
    (compileScheme ver).toRScheme.AcceptsAll c (fun v => ℓ v :: (c.nbrs v).map ℓ) ω := by
  intro v
  change compileDec ver _ (ℓ v :: (c.nbrs v).map ℓ) _ = true
  simp only [compileDec, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, hacc v⟩
  rw [RScheme.received, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro w hw
  rw [compile_sent ver c _ ω hw]
  exact fpDecide_fpSend (ℓ w) _

/-- Soundness of the compiled scheme: on an illegal configuration, whatever the labels, the
acceptance probability is less than `1/3`. -/
theorem compile_sound {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} (hpls : IsPLS ver prover F P) (c : Config S) (hF : F c)
    (hP : ¬ P c) (ℓ : c.V → List (List Bool)) :
    (compileScheme ver).toRScheme.accProb c ℓ < 1 / 3 := by
  set σ := (compileScheme ver).toRScheme
  -- the label that each node claims for itself
  set L : c.V → List Bool := fun v => (ℓ v).headD []
  by_cases hcons : ∀ v, ℓ v = L v :: (c.nbrs v).map L
  · -- consistent labels: the deterministic verifier rejects somewhere
    rw [RScheme.accProb_eq_zero σ c ℓ]
    · norm_num
    intro ω hω
    apply hpls.2 c hF hP L
    intro v
    have hv := hω v
    change compileDec ver _ (ℓ v) _ = true at hv
    rw [hcons v] at hv
    simp only [compileDec, Bool.and_eq_true] at hv
    exact hv.2
  push Not at hcons
  obtain ⟨v, hv⟩ := hcons
  -- the node `v` checks its label
  have hacc : ∀ ω, σ.AcceptsAll c ℓ ω → ∃ t, ℓ v = L v :: t ∧
      List.Forall₂ (fun b r => fpDecide b r = true) t (σ.received c ℓ ω v) := by
    intro ω hω
    have h := hω v
    change compileDec ver _ (ℓ v) _ = true at h
    cases hℓ : ℓ v with
    | nil => rw [hℓ] at h; simp [compileDec] at h
    | cons h₀ t =>
      rw [hℓ] at h
      simp only [compileDec, Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨t, ?_, h.1⟩
      simp [L, hℓ]
  by_cases hfmt : ∃ t, ℓ v = L v :: t ∧ t.length = (c.nbrs v).length
  · obtain ⟨t, ht, hlen⟩ := hfmt
    -- an inconsistent entry of the label of `v`
    have : t ≠ (c.nbrs v).map L := fun h => hv (h ▸ ht)
    obtain ⟨i, hi, hne⟩ : ∃ i, ∃ hi : i < (c.nbrs v).length,
        t[i]'(hlen ▸ hi) ≠ L ((c.nbrs v)[i]) := by
      by_contra hcon
      push Not at hcon
      exact this (List.ext_getElem (by simpa using hlen) fun i h₁ h₂ => by
        simpa using hcon i (hlen ▸ h₁))
    set w := (c.nbrs v)[i]
    have hw : w ∈ c.nbrs v := List.getElem_mem hi
    set j : Fin (c.deg w) := ⟨c.port w v, c.port_lt_deg hw⟩
    set b := t[i]'(hlen ▸ hi)
    have hbad : ∀ ω, σ.AcceptsAll c ℓ ω → fpDecide b (fpSend ((ℓ w).headD []) (ω w j)) = true := by
      intro ω hω
      obtain ⟨t', ht', hf⟩ := hacc ω hω
      obtain rfl : t' = t := by rw [ht] at ht'; exact (List.cons_injective ht').symm
      rw [RScheme.received, List.forall₂_map_right_iff, List.forall₂_iff_get] at hf
      have := hf.2 i (hlen ▸ hi) hi
      simp only [List.get_eq_getElem] at this
      rwa [compile_sent ver c ℓ ω hw] at this
    calc σ.accProb c ℓ
        ≤ uprob (fun ω : σ.Coins c ℓ => fpDecide b (fpSend ((ℓ w).headD []) (ω w j)) = true) :=
          uprob_mono hbad
      _ = uprob (fun x : GaloisField 2 (fpBits ((ℓ w).headD []).length) =>
            fpDecide b (fpSend ((ℓ w).headD []) x) = true) := by
          exact EIScheme.uprob_port (compileScheme ver) c ℓ w j
            (fun x => fpDecide b (fpSend ((ℓ w).headD []) x) = true)
      _ < 1 / 3 := by
          have h1 := (lemma_3_3.2.1 ((ℓ w).headD []) b (Ne.symm hne))
          have h2 := uprob_not (fun x : GaloisField 2 (fpBits ((ℓ w).headD []).length) =>
            fpDecide b (fpSend ((ℓ w).headD []) x) = true)
          simp only [Bool.not_eq_true] at h2
          linarith
  · -- bad format: `v` always rejects
    rw [RScheme.accProb_eq_zero σ c ℓ]
    · norm_num
    intro ω hω
    obtain ⟨t, ht, hf⟩ := hacc ω hω
    refine hfmt ⟨t, ht, ?_⟩
    rw [hf.length_eq, RScheme.received, List.length_map]

/-- The compiled scheme is a one-sided RPLS with rejection probability at least `2/3`. -/
theorem compile_isRPLS {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} (hpls : IsPLS ver prover F P) :
    IsRPLS (compileScheme ver).toRScheme (compileProver prover) F P 1 (2 / 3) := by
  refine ⟨fun c hF hP => ?_, fun c hF hP ℓ => ?_⟩
  · exact (((compileScheme ver).toRScheme.accProb_eq_one_iff c (compileProver prover c)).2
      (compile_acceptsAll ver c (prover c) (hpls.1 c hF hP))).symm.le
  · have := compile_sound hpls c hF hP ℓ
    linarith

/-- The certificates of the compiled scheme have `2 · fpBits κ` bits. -/
theorem compile_certBound {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} {κ : Config S → ℕ} (hκ : LabelBound prover F P κ) :
    CertBound (compileScheme ver).toRScheme (compileProver prover) F P
      (fun c => 2 * fpBits (κ c)) := by
  intro c hF hP v ω i hi
  simp only [EIScheme.toRScheme, hi, ↓reduceDIte]
  change (fpSend (prover c v) _).length ≤ _
  refine (fpSend_length (prover c v) _).trans_le ?_
  exact Nat.mul_le_mul_left 2 (Nat.clog_mono_right 2 (by have := hκ c hF hP v; omega))

/-- **Theorem 3.1 of [BFP15].** If `(ver, prover)` is a PLS for `(F, P)` with labels of at most
`κ` bits, then the compiled scheme (`compileScheme ver`, `compileProver prover`) is an RPLS for
`(F, P)` accepting legal configurations with probability `1`, rejecting illegal ones with
probability `≥ 2/3`, with certificates of at most `2 log₂ κ + 6 = O(log κ)` bits. -/
theorem theorem_3_1 {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} {κ : Config S → ℕ} (hpls : IsPLS ver prover F P)
    (hκ : LabelBound prover F P κ) :
    IsRPLS (compileScheme ver).toRScheme (compileProver prover) F P 1 (2 / 3) ∧
    CertBound (compileScheme ver).toRScheme (compileProver prover) F P
      (fun c => 2 * Nat.log 2 (κ c) + 6) := by
  refine ⟨compile_isRPLS hpls, fun c hF hP v ω i hi => ?_⟩
  have h1 : _ ≤ 2 * fpBits (κ c) := compile_certBound (ver := ver) hκ c hF hP v ω i hi
  have h2 := fpBits_le (κ c)
  show _ ≤ 2 * Nat.log 2 (κ c) + 6
  omega

/-- **Theorem 3.1 of [BFP15]**, as stated: a PLS with verification complexity `κ` yields a
one-sided RPLS (edge-independent) with verification complexity `O(log κ)`. -/
theorem theorem_3_1_oneSided {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} {κ : Config S → ℕ} (hpls : IsPLS ver prover F P)
    (hκ : LabelBound prover F P κ) :
    ∃ (e : EIScheme S (List (List Bool))) (prover' : ∀ c : Config S, c.V → List (List Bool)),
      IsOneSided e.toRScheme prover' F P ∧
      CertBound e.toRScheme prover' F P (fun c => 2 * Nat.log 2 (κ c) + 6) := by
  obtain ⟨⟨hc, hs⟩, hb⟩ := theorem_3_1 hpls hκ
  exact ⟨_, _, ⟨hc, fun c hF hP ℓ => le_trans (by norm_num) (hs c hF hP ℓ)⟩, hb⟩

/-- Theorem 3.1 of [BFP15], two-sided form: the compiled scheme is also a two-sided RPLS. -/
theorem theorem_3_1_twoSided {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} {κ : Config S → ℕ} (hpls : IsPLS ver prover F P)
    (hκ : LabelBound prover F P κ) :
    ∃ (e : EIScheme S (List (List Bool))) (prover' : ∀ c : Config S, c.V → List (List Bool)),
      IsTwoSided e.toRScheme prover' F P ∧
      CertBound e.toRScheme prover' F P (fun c => 2 * Nat.log 2 (κ c) + 6) := by
  obtain ⟨⟨hc, hs⟩, hb⟩ := theorem_3_1 hpls hκ
  exact ⟨_, _, ⟨fun c hF hP => le_trans (by norm_num) (hc c hF hP), hs⟩, hb⟩

end Podc.RandomizedPLS
