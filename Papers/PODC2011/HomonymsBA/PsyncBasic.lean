import Papers.PODC2011.HomonymsBA.PsyncAlg

/-!
# Proposition 5: basic facts about runs of the algorithm

* states (`σ`), received sets (`rcv`) and what correct processes receive;
* monotonicity of the cumulative state components;
* counting identifiers: `BF` (identifiers without Byzantine process), `UCp` (correct processes
  that do not share their identifier), and the quorum lemma (Lemma 7, `lemma7`).
-/

namespace Podc.HomonymsBA.Psync

open Set

variable {P : Type} [Fintype P] {ℓ t : ℕ} {V : Type} (R : Run P ℓ V (Msg ℓ V))

/-- The state of `p` at the beginning of round `r`. -/
noncomputable abbrev σ (R : Run P ℓ V (Msg ℓ V)) (t r : ℕ) (p : P) : St ℓ V :=
  R.st (alg ℓ t V) r p

/-- The set of pairs received by `p` in round `r`. -/
def rcv (R : Run P ℓ V (Msg ℓ V)) (t r : ℕ) (p : P) : Set (Fin ℓ × Msg ℓ V) :=
  {x | x ∈ R.inbox (alg ℓ t V) r p}

lemma σ_succ (r : ℕ) (p : P) : σ R t (r + 1) p = step t (σ R t r p) (rcv R t r p) := rfl

lemma σ_zero (p : P) : σ R t 0 p = initSt (R.id p) (R.inp p) := rfl

@[simp] lemma rnd_σ (r : ℕ) (p : P) : (σ R t r p).rnd = r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [σ_succ]; simp [step, ih]

@[simp] lemma me_σ (r : ℕ) (p : P) : (σ R t r p).me = R.id p := by
  induction r with
  | zero => rfl
  | succ r ih => rw [σ_succ]; simp [step, ih]

lemma mem_rcv {r : ℕ} {p : P} {x : Fin ℓ × Msg ℓ V} : x ∈ rcv R t r p ↔
    (∃ q, q ∉ R.byz ∧ ¬ R.drop r q p ∧ x = (R.id q, out t (σ R t r q))) ∨ x ∈ R.adv r p := by
  classical
  simp only [rcv, Set.mem_ofPred_eq, Run.inbox_eq, Multiset.mem_add, Multiset.mem_sum,
    Finset.mem_filter, Finset.mem_univ, true_and, Run.mem_msgFrom]
  constructor
  · rintro (⟨q, ⟨hq, hd⟩, h1, h2⟩ | h)
    · left
      refine ⟨q, hq, hd, ?_⟩
      obtain ⟨j, m⟩ := x
      simp only [alg, Option.some.injEq] at h1 h2
      subst h1 h2
      rfl
    · exact Or.inr h
  · rintro (⟨q, hq, hd, rfl⟩ | h)
    · left
      exact ⟨q, ⟨hq, hd⟩, rfl, rfl⟩
    · exact Or.inr h

/-- Identifier `j` belongs to no Byzantine process. -/
def BF (j : Fin ℓ) : Prop := ∀ b ∈ R.byz, R.id b ≠ j

/-- `s` is a correct process that does not share its identifier with any other process. -/
def UCp (s : P) : Prop := s ∉ R.byz ∧ ∀ q, R.id q = R.id s → q = s

variable {R}

omit [Fintype P] in
lemma UCp.bf {s : P} (h : UCp R s) : BF R (R.id s) := by
  intro b hb e
  rw [h.2 b e] at hb
  exact h.1 hb

/-- What a correct process receives from an identifier without Byzantine process. -/
lemma rcv_src (hR : R.Valid t) {r : ℕ} {p : P} {j : Fin ℓ} {m : Msg ℓ V}
    (h : (j, m) ∈ rcv R t r p) (hj : BF R j) :
    ∃ q, q ∉ R.byz ∧ R.id q = j ∧ m = out t (σ R t r q) := by
  rcases (mem_rcv R).1 h with ⟨q, hq, -, e⟩ | h
  · simp only [Prod.mk.injEq] at e
    exact ⟨q, hq, e.1.symm, e.2⟩
  · obtain ⟨b, hb, e⟩ := hR.adv_id r p _ h
    exact absurd e (hj b hb)

/-- What a correct process receives from a process with a unique identifier. -/
lemma rcv_src_UCp (hR : R.Valid t) {r : ℕ} {p s : P} {m : Msg ℓ V}
    (h : (R.id s, m) ∈ rcv R t r p) (hs : UCp R s) : m = out t (σ R t r s) := by
  obtain ⟨q, -, e, rfl⟩ := rcv_src hR h hs.bf
  rw [hs.2 q e]

/-- After `gst`, correct processes receive each other's messages. -/
lemma rcv_of_gst (hR : R.Valid t) {r : ℕ} {p q : P} (hr : R.gst ≤ r) (hq : q ∉ R.byz)
    (hp : p ∉ R.byz) : (R.id q, out t (σ R t r q)) ∈ rcv R t r p :=
  (mem_rcv R).2 (Or.inl ⟨q, hq, hR.no_drop r q p hr hq hp, rfl⟩)

/-! ### Monotonicity -/

lemma proper_mono {r r' : ℕ} (h : r ≤ r') (p : P) : (σ R t r p).proper ⊆ (σ R t r' p).proper := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [σ_succ]; exact ih.trans subset_union_left

lemma echoRcv_mono {r r' : ℕ} (h : r ≤ r') (p : P) :
    (σ R t r p).echoRcv ⊆ (σ R t r' p).echoRcv := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [σ_succ]; exact ih.trans subset_union_left

lemma echoing_mono {r r' : ℕ} (h : r ≤ r') (p : P) :
    (σ R t r p).echoing ⊆ (σ R t r' p).echoing := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [σ_succ]; exact ih.trans subset_union_left

lemma dec_mono {r r' : ℕ} (h : r ≤ r') {p : P} {v : V} (hv : (σ R t r p).dec = some v) :
    (σ R t r' p).dec = some v := by
  induction h with
  | refl => exact hv
  | step _ ih => rw [σ_succ]; simp [step, ih]

lemma ncard_mono {Q Q' : Fin ℓ → Prop} (h : ∀ j, Q j → Q' j) :
    {j | Q j}.ncard ≤ {j | Q' j}.ncard :=
  Set.ncard_le_ncard (fun j hj => h j hj) (Set.toFinite _)

lemma Acc_mono {E E' : Set (Fin ℓ × (BMsg V × Fin ℓ))} (h : E ⊆ E') {m : BMsg V} {i : Fin ℓ}
    (hE : Acc t E m i) : Acc t E' m i :=
  hE.trans (ncard_mono fun _ hj => h hj)

lemma Acc_σ_mono {r r' : ℕ} (h : r ≤ r') {p : P} {m : BMsg V} {i : Fin ℓ}
    (hE : Acc t (σ R t r p).echoRcv m i) : Acc t (σ R t r' p).echoRcv m i :=
  Acc_mono (echoRcv_mono h p) hE

/-! ### Counting identifiers -/

lemma ncard_nonBF (hR : R.Valid t) : {j | ¬ BF R j}.ncard ≤ t := by
  have : {j | ¬ BF R j} = R.id '' (R.byz : Set P) := by
    ext j
    simp [BF]
  rw [this]
  exact (Set.ncard_image_le (Set.toFinite _)).trans ((Set.ncard_coe_finset _).le.trans hR.card_byz)

lemma ncard_le_BF (hR : R.Valid t) (Q : Fin ℓ → Prop) :
    {j | Q j}.ncard ≤ {j | Q j ∧ BF R j}.ncard + t := by
  have h : {j | Q j} ⊆ {j | Q j ∧ BF R j} ∪ {j | ¬ BF R j} := by
    intro j hj
    by_cases hb : BF R j
    · exact Or.inl ⟨hj, hb⟩
    · exact Or.inr hb
  exact (Set.ncard_le_ncard h (Set.toFinite _)).trans
    ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ncard_nonBF hR) _))

lemma exists_BF (hR : R.Valid t) {Q : Fin ℓ → Prop} (h : t < {j | Q j}.ncard) :
    ∃ j, Q j ∧ BF R j := by
  have h1 := ncard_le_BF hR Q
  have h2 : 0 < {j | Q j ∧ BF R j}.ncard := by omega
  obtain ⟨j, hj⟩ := (Set.ncard_pos (Set.toFinite _)).1 h2
  exact ⟨j, hj⟩

omit [Fintype P] in
lemma BF_correct (hR : R.Valid t) {j : Fin ℓ} (hj : BF R j) : ∃ q, q ∉ R.byz ∧ R.id q = j := by
  obtain ⟨q, rfl⟩ := hR.surj j
  exact ⟨q, fun hq => hj q hq rfl, rfl⟩

lemma ncard_BF (hR : R.Valid t) : ℓ - t ≤ {j | BF R j}.ncard := by
  have := ncard_le_BF hR (fun _ => True)
  have e : {j : Fin ℓ | True}.ncard = ℓ := by
    rw [Set.ofPred_true, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  simp only [true_and] at this
  omega

/-- If `p` received `Q`-pairs from `ℓ - t` identifiers, from `ℓ - 2t` of them they came from
correct processes. -/
lemma ncard_BF_and (hR : R.Valid t) {Q : Fin ℓ → Prop} (h : ℓ - t ≤ {j | Q j}.ncard) :
    ℓ - 2 * t ≤ {j | Q j ∧ BF R j}.ncard := by
  have := ncard_le_BF hR Q
  omega

lemma le_card (hR : R.Valid t) : ℓ ≤ Fintype.card P := by
  have := Fintype.card_le_of_surjective _ hR.surj
  simpa using this

/-- Identifiers held by at least two processes. -/
def Multi (R : Run P ℓ V (Msg ℓ V)) (j : Fin ℓ) : Prop :=
  ∃ q₁ q₂, q₁ ≠ q₂ ∧ R.id q₁ = j ∧ R.id q₂ = j

/-- At most `n - ℓ` identifiers are held by more than one process. -/
lemma ncard_multi (hR : R.Valid t) : {j | Multi R j}.ncard + ℓ ≤ Fintype.card P := by
  classical
  choose f hf using hR.surj
  have hg : ∀ j : {j // Multi R j}, ∃ q, q ≠ f j.1 ∧ R.id q = j.1 := by
    rintro ⟨j, q₁, q₂, hne, h1, h2⟩
    by_cases h : q₁ = f j
    · exact ⟨q₂, fun e => hne (h.trans e.symm), h2⟩
    · exact ⟨q₁, h, h1⟩
  choose g hg1 hg2 using hg
  let F : {j // Multi R j} ⊕ Fin ℓ → P := Sum.elim g f
  have hF : Function.Injective F := by
    rintro (a | a) (b | b) e <;> simp only [F, Sum.elim_inl, Sum.elim_inr] at e
    · have := congrArg R.id e
      rw [hg2, hg2] at this
      rw [Subtype.ext this]
    · have := congrArg R.id e
      rw [hg2, hf] at this
      subst this
      exact absurd e (hg1 a)
    · have := congrArg R.id e
      rw [hg2, hf] at this
      subst this
      exact absurd e.symm (hg1 b)
    · have := congrArg R.id e
      rw [hf, hf] at this
      rw [this]
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := P), Nat.card_eq_fintype_card (α := Fin ℓ),
    Fintype.card_fin] at this
  have e : Nat.card {j // Multi R j} = {j | Multi R j}.ncard := Nat.card_coe_set_eq _
  omega

omit [Fintype P] in
lemma UCp_of (hR : R.Valid t) {j : Fin ℓ} (hj : BF R j) (hm : ¬ Multi R j) :
    ∃ s, UCp R s ∧ R.id s = j := by
  obtain ⟨s, hs, rfl⟩ := BF_correct hR hj
  refine ⟨s, ⟨hs, fun q hq => ?_⟩, rfl⟩
  by_contra hne
  exact hm ⟨q, s, hne, hq, rfl⟩

lemma ncard_nonUC (hR : R.Valid t) :
    {j | ¬ ∃ s, UCp R s ∧ R.id s = j}.ncard + ℓ ≤ Fintype.card P + t := by
  have h : {j | ¬ ∃ s, UCp R s ∧ R.id s = j} ⊆ {j | ¬ BF R j} ∪ {j | Multi R j} := by
    intro j hj
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hj (UCp_of hR hc.1 hc.2)
  have := (Set.ncard_le_ncard h (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  have := ncard_nonBF hR
  have := ncard_multi hR
  omega

/-- **Lemma 7**: two sets of `ℓ - t` identifiers share the identifier of a correct process that
does not share its identifier. -/
lemma lemma7 (hR : R.Valid t) (hℓ : Fintype.card P + 3 * t < 2 * ℓ) {A B : Fin ℓ → Prop}
    (hA : ℓ - t ≤ {j | A j}.ncard) (hB : ℓ - t ≤ {j | B j}.ncard) :
    ∃ s, UCp R s ∧ A (R.id s) ∧ B (R.id s) := by
  by_contra hc
  push Not at hc
  have h1 := Set.ncard_inter_add_ncard_union {j | A j} {j | B j} (Set.toFinite _) (Set.toFinite _)
  have h2 : ({j | A j} ∪ {j | B j}).ncard ≤ ℓ := by
    have := Set.ncard_le_ncard (Set.subset_univ ({j | A j} ∪ {j | B j})) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h3 : {j | A j} ∩ {j | B j} ⊆ {j | ¬ ∃ s, UCp R s ∧ R.id s = j} := by
    rintro j ⟨ha, hb⟩ ⟨s, hs, rfl⟩
    exact hc s hs ha hb
  have h4 := Set.ncard_le_ncard h3 (Set.toFinite _)
  have h5 := ncard_nonUC hR
  have h6 := le_card hR
  omega

/-- At least `2t + 1` identifiers belong to a single, correct process. -/
lemma ncard_UC (hR : R.Valid t) (hℓ : Fintype.card P + 3 * t < 2 * ℓ) :
    2 * t + 1 ≤ {j | ∃ s, UCp R s ∧ R.id s = j}.ncard := by
  have h1 := Set.ncard_add_ncard_compl {j | ∃ s, UCp R s ∧ R.id s = j} (Set.toFinite _)
    (Set.toFinite _)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := ncard_nonUC hR
  have e : {j | ∃ s, UCp R s ∧ R.id s = j}ᶜ = {j | ¬ ∃ s, UCp R s ∧ R.id s = j} := rfl
  rw [e] at h1
  omega

lemma three_t_lt (hR : R.Valid t) (hℓ : Fintype.card P + 3 * t < 2 * ℓ) : 3 * t < ℓ := by
  have := le_card hR
  omega

end Podc.HomonymsBA.Psync
