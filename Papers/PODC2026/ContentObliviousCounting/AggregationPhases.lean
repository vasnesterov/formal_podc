import Papers.PODC2026.ContentObliviousCounting.AggregationProg
import Papers.PODC2026.ContentObliviousCounting.AggregationCluster

/-!
# The phases of the aggregation algorithm (synchronous view)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, proof of Theorem 1.

`phase t = (A t, W t)`: the active set and the (encoded) partial aggregates at the beginning of
phase `t`, computed from the exact result of the simulation of `misAlg` (Theorem 14) on the
virtual ring of `A t`. Invariant (`phase_inv`): the active nodes own clusters partitioning the
ring, each holds the encoding of the aggregate of its cluster, and the leader is active.
While some non-leader is active, the next active set is an MIS of the virtual ring, so it has at
most half as many nodes (`card_phase_succ`); hence after `P ≤ log₂ n` phases only the leader is
active (`numPhases_le_log`), holding the aggregate of all inputs (`phase_final`).
-/

namespace Podc.ContentOblivious.Aggregation

open Podc.ContentOblivious Simulation Finset

variable {n : ℕ} [NeZero n] (op2 : List Bool → List Bool → List Bool) {U : Type}
  (w0 : U → List Bool) (x : ZMod n → ℕ × Bool × U)

/-- The maximal bit length of the IDs (what the λ-preprocessing computes). -/
def lamOf : ℕ := univ.sup fun v => Nat.size (x v).1

/-- Active set and partial aggregates at the beginning of phase `t`. -/
def phase : ℕ → (ZMod n → Bool) × (ZMod n → List Bool)
  | 0 => (fun _ => true, fun v => w0 (x v).2.2)
  | t + 1 =>
    let A := (phase t).1
    let W := (phase t).2
    let st := fun v => stateAt (misAlg op2) A (vnext A) (vprev A)
      (fun u => initSt (lamOf x) (x u).2.1 (x u).1 (W u)) (rounds (lamOf x)) v
    (fun v => A v && (st v).mis, fun v => if A v then (st v).w else W v)

/-- Some non-leader is active in phase `t` (the loneliness test succeeds). -/
def NotDone (t : ℕ) : Prop := ∃ u, (phase op2 w0 x t).1 u = true ∧ (x u).2.1 = false

instance (t : ℕ) : Decidable (NotDone op2 w0 x t) := by unfold NotDone; infer_instance

variable {op2 w0 x}

/-- Hypotheses of Theorem 1 at the level of the encoded aggregates `E X`. -/
structure AggHyp (op2 : List Bool → List Bool → List Bool) (w0 : U → List Bool)
    (x : ZMod n → ℕ × Bool × U) (ℓ : ZMod n) (E : Multiset U → List Bool) : Prop where
  id_inj : Function.Injective fun v => (x v).1
  lead_iff : ∀ v, (x v).2.1 = true ↔ v = ℓ
  w0_eq : ∀ a, w0 a = E {a}
  op2_eq : ∀ X Y, X ≠ 0 → Y ≠ 0 → op2 (E X) (E Y) = E (X + Y)

variable {ℓ : ZMod n} {E : Multiset U → List Bool}

/-- The cluster invariant of phase `t`. -/
def PhaseInv (op2 : List Bool → List Bool → List Bool) (w0 : U → List Bool)
    (x : ZMod n → ℕ × Bool × U) (ℓ : ZMod n) (E : Multiset U → List Bool) (t : ℕ) : Prop :=
  ∃ o : ZMod n → ZMod n, (∀ u, (phase op2 w0 x t).1 (o u) = true) ∧
    (∀ p, (phase op2 w0 x t).1 p = true → o p = p) ∧
    (∀ p, (phase op2 w0 x t).1 p = true →
      (phase op2 w0 x t).2 p = E (clusterVals (fun u => (x u).2.2) o p)) ∧
    (phase op2 w0 x t).1 ℓ = true

lemma ringAx_of {A : ZMod n → Bool} (hℓ : A ℓ = true) {u : ZMod n} (hu : A u = true)
    (huℓ : u ≠ ℓ) : RingAx A (vnext A) (vprev A) where
  nxt_act _ _ := act_vnext hℓ _
  prv_act _ _ := act_vprev hℓ _
  prv_nxt _ hv := vprev_vnext hv
  nxt_prv _ hv := vnext_vprev hv
  nxt_ne _ hv h := huℓ (((vnext_eq_self_iff hv).1 h u hu).trans
    ((vnext_eq_self_iff hv).1 h ℓ hℓ).symm)

lemma lt_two_pow_lamOf (v : ZMod n) : (x v).1 < 2 ^ lamOf x :=
  Nat.size_le.1 (Finset.le_sup (f := fun v => Nat.size (x v).1) (mem_univ v))

variable (op2 w0 x) in
/-- The MIS of phase `t`. -/
abbrev misOf (t : ℕ) : ZMod n → Bool :=
  misAt (vnext (phase op2 w0 x t).1) (vprev (phase op2 w0 x t).1) (lamOf x)
    (fun v => (x v).2.1) (fun v => (x v).1) 8

lemma stateAt_phase (t : ℕ) {v : ZMod n} (hv : (phase op2 w0 x t).1 v = true) :
    stateAt (misAlg op2) (phase op2 w0 x t).1 (vnext (phase op2 w0 x t).1)
      (vprev (phase op2 w0 x t).1)
      (fun u => initSt (lamOf x) (x u).2.1 (x u).1 ((phase op2 w0 x t).2 u)) (rounds (lamOf x)) v =
    runM op2 (vnext (phase op2 w0 x t).1) (vprev (phase op2 w0 x t).1) (lamOf x)
      (fun v => (x v).2.1) (fun v => (x v).1) (phase op2 w0 x t).2 (rounds (lamOf x)) v := by
  simp [stateAt, hv]

lemma phase_succ_act (t : ℕ) (v : ZMod n) :
    (phase op2 w0 x (t + 1)).1 v = ((phase op2 w0 x t).1 v && misOf op2 w0 x t v) := by
  dsimp only [phase]
  by_cases hv : (phase op2 w0 x t).1 v = true
  · rw [stateAt_phase t hv, run_agg]
  · simp at hv; simp [hv]

lemma phase_succ_w (t : ℕ) {v : ZMod n} (hv : (phase op2 w0 x t).1 v = true)
    (hm : misOf op2 w0 x t v = true) :
    (phase op2 w0 x (t + 1)).2 v =
      combine op2 (aggMsg (misOf op2 w0 x t (vprev (phase op2 w0 x t).1 v))
          (misOf op2 w0 x t (vnext (phase op2 w0 x t).1
            (vprev (phase op2 w0 x t).1 v)))
          ((phase op2 w0 x t).2 (vprev (phase op2 w0 x t).1 v))).1
        (aggMsg (misOf op2 w0 x t (vnext (phase op2 w0 x t).1 v))
          (misOf op2 w0 x t (vnext (phase op2 w0 x t).1
            (vnext (phase op2 w0 x t).1 v)))
          ((phase op2 w0 x t).2 (vnext (phase op2 w0 x t).1 v))).2
        ((phase op2 w0 x t).2 v) := by
  dsimp only [phase]
  simp only [hv, ↓reduceIte]
  rw [stateAt_phase t hv, run_agg]
  simp only at hm ⊢
  simp only [hm, ↓reduceIte]

/-- One phase: the invariant is preserved and the active set at least halves. -/
lemma phase_step (h : AggHyp op2 w0 x ℓ E) {t : ℕ} (hinv : PhaseInv op2 w0 x ℓ E t)
    (hnd : NotDone op2 w0 x t) :
    PhaseInv op2 w0 x ℓ E (t + 1) ∧
      2 * (univ.filter fun v => (phase op2 w0 x (t + 1)).1 v = true).card ≤
        (univ.filter fun v => (phase op2 w0 x t).1 v = true).card := by
  obtain ⟨o, ho, hoself, hw, hℓ⟩ := hinv
  obtain ⟨u, hu, hul⟩ := hnd
  set A := (phase op2 w0 x t).1 with hA
  have huℓ : u ≠ ℓ := fun h' => by rw [h', (h.lead_iff ℓ).2 rfl] at hul; cases hul
  have hR := ringAx_of hℓ hu huℓ
  have hid : ∀ u v, A u = true → A v = true → (x u).1 = (x v).1 → u = v :=
    fun u v _ _ he => h.id_inj he
  have hlam : ∀ v, A v = true → (x v).1 < 2 ^ lamOf x := fun v _ => lt_two_pow_lamOf v
  have hlead : ∀ u v, (x u).2.1 = true → (x v).2.1 = true → u = v :=
    fun u v hu hv => ((h.lead_iff u).1 hu).trans ((h.lead_iff v).1 hv).symm
  set M := misOf op2 w0 x t with hM
  have hindep : ∀ v, A v = true → M v = true → M (vnext A v) = false := by
    intro v hv hm
    by_contra hc
    exact misAt_indep hR hid hlam hlead 8 v hv ⟨hm, by simpa using hc⟩
  have hdom : ∀ v, A v = true → M v = false → M (vprev A v) = true ∨ M (vnext A v) = true := by
    intro v hv hm
    rcases misAt_dom (lead := fun v => (x v).2.1) hR hid hlam v hv with h1 | h1 | h1
    · have h1' : M v = true := h1
      rw [h1'] at hm; cases hm
    · exact Or.inl h1
    · exact Or.inr h1
  have hact : ∀ v, (phase op2 w0 x (t + 1)).1 v = (A v && M v) := phase_succ_act t
  refine ⟨⟨fun u => cen M (vnext A) (vprev A) (o u), fun u => ?_, fun p hp => ?_, fun p hp => ?_,
    ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := act_cen hR hdom (ho u)
    rw [hact, h1, h2]; rfl
  · rw [hact] at hp
    simp only [Bool.and_eq_true] at hp
    show cen M (vnext A) (vprev A) (o p) = p
    rw [hoself p hp.1, cen_self hp.2]
  · rw [hact] at hp
    simp only [Bool.and_eq_true] at hp
    rw [phase_succ_w t hp.1 hp.2]
    exact combine_eq hR hindep op2 E h.op2_eq _ ho hoself hw hp.1 hp.2
  · have hMℓ : M ℓ = true :=
      misAt_lead (lead := fun v => (x v).2.1) ℓ ((h.lead_iff ℓ).2 rfl) 8
    rw [hact, hℓ, hMℓ]; rfl
  · have := card_mis_le hR hindep
    simp only [hact, Bool.and_eq_true]
    exact this

lemma phase_inv (h : AggHyp op2 w0 x ℓ E) (t : ℕ) (hnd : ∀ s < t, NotDone op2 w0 x s) :
    PhaseInv op2 w0 x ℓ E t ∧
      2 ^ t * (univ.filter fun v => (phase op2 w0 x t).1 v = true).card ≤ n := by
  induction t with
  | zero =>
    refine ⟨⟨fun u => u, fun _ => rfl, fun p _ => rfl, fun p _ => ?_, rfl⟩, ?_⟩
    · show w0 (x p).2.2 = _
      rw [h.w0_eq]
      congr 1
      simp [clusterVals, Finset.filter_eq']
    · simp [phase]
  | succ t ih =>
    obtain ⟨hinv, hcard⟩ := ih fun s hs => hnd s (by omega)
    obtain ⟨hinv', hcard'⟩ := phase_step h hinv (hnd t (by omega))
    refine ⟨hinv', ?_⟩
    rw [pow_succ]
    calc 2 ^ t * 2 * _ = 2 ^ t * (2 * _) := by ring
      _ ≤ 2 ^ t * _ := Nat.mul_le_mul_left _ hcard'
      _ ≤ n := hcard

lemma card_act_pos (h : PhaseInv op2 w0 x ℓ E t) :
    1 ≤ (univ.filter fun v => (phase op2 w0 x t).1 v = true).card :=
  Finset.card_pos.2 ⟨ℓ, by obtain ⟨-, -, -, -, hℓ⟩ := h; simp [hℓ]⟩

lemma exists_done (h : AggHyp op2 w0 x ℓ E) : ∃ t, ¬ NotDone op2 w0 x t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hinv, hc⟩ := phase_inv h (Nat.log 2 n + 1) fun s _ => hcon s
  have h1 := card_act_pos hinv
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  have : 2 ^ (Nat.log 2 n + 1) ≤ n := le_trans (Nat.le_mul_of_pos_right _ h1) hc
  omega

variable (op2 w0 x) in
/-- The number of phases: the first phase in which the leader is the only active node. -/
noncomputable def numPhases (h : AggHyp op2 w0 x ℓ E) : ℕ := Nat.find (exists_done h)

lemma notDone_of_lt (h : AggHyp op2 w0 x ℓ E) {s : ℕ} (hs : s < numPhases op2 w0 x h) :
    NotDone op2 w0 x s := by
  have := Nat.find_min (exists_done h) hs
  simpa using this

lemma not_notDone (h : AggHyp op2 w0 x ℓ E) : ¬ NotDone op2 w0 x (numPhases op2 w0 x h) :=
  Nat.find_spec (exists_done h)

/-- The number of phases is at most `log₂ n` (an MIS of a ring has at most half of its nodes). -/
lemma numPhases_le_log (h : AggHyp op2 w0 x ℓ E) : numPhases op2 w0 x h ≤ Nat.log 2 n := by
  obtain ⟨hinv, hc⟩ := phase_inv h _ fun s hs => notDone_of_lt h hs
  have h1 := card_act_pos hinv
  exact Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.le_mul_of_pos_right _ h1) hc)

lemma phaseInv_le (h : AggHyp op2 w0 x ℓ E) {t : ℕ} (ht : t ≤ numPhases op2 w0 x h) :
    PhaseInv op2 w0 x ℓ E t :=
  (phase_inv h t fun s hs => notDone_of_lt h (by omega)).1

/-- In the last phase only the leader is active, and it holds the aggregate of all inputs. -/
lemma phase_final (h : AggHyp op2 w0 x ℓ E) :
    (∀ v, (phase op2 w0 x (numPhases op2 w0 x h)).1 v = true ↔ v = ℓ) ∧
    (phase op2 w0 x (numPhases op2 w0 x h)).2 ℓ = E (univ.val.map fun u => (x u).2.2) := by
  obtain ⟨o, ho, -, hw, hℓ⟩ := phaseInv_le h le_rfl
  have hnd := not_notDone h
  have honly : ∀ v, (phase op2 w0 x (numPhases op2 w0 x h)).1 v = true → v = ℓ := by
    intro v hv
    by_contra hne
    exact hnd ⟨v, hv, by
      cases hl : (x v).2.1
      · rfl
      · exact absurd ((h.lead_iff v).1 hl) hne⟩
  refine ⟨fun v => ⟨honly v, fun hv => hv ▸ hℓ⟩, ?_⟩
  rw [hw ℓ hℓ]
  congr 1
  unfold clusterVals
  rw [Finset.filter_true_of_mem fun u _ => honly _ (ho u)]

/-- Every partial aggregate held by an active node has at most `β` bits. -/
lemma phase_len_le (h : AggHyp op2 w0 x ℓ E) {β : ℕ}
    (hβ : ∀ S : Finset (ZMod n), S.Nonempty → (E (S.val.map fun u => (x u).2.2)).length ≤ β)
    {t : ℕ} (ht : t ≤ numPhases op2 w0 x h) {p : ZMod n} (hp : (phase op2 w0 x t).1 p = true) :
    ((phase op2 w0 x t).2 p).length ≤ β := by
  obtain ⟨o, -, hoself, hw, -⟩ := phaseInv_le h ht
  rw [hw p hp]
  exact hβ _ ⟨p, by simp [hoself p hp]⟩

end Podc.ContentOblivious.Aggregation
