import Papers.PODC2026.ContentObliviousEulerian.Merging

/-!
# Theorem 1 at the circuit level

Frei, Gelles, Ghazy, Nolin, PODC 2026, Theorem 1: on an Eulerian network with unique IDs there is
a deterministic uniform content-oblivious leader-election algorithm using `O(|E| · IDmax)` pulses.

We do **not** formalize the pulse-level algorithm (the ring leader-election black box of
Chalopin et al., the simulation of virtual nodes, the OR protocols and the synchronisation between
circuits). We formalize the combinatorial skeleton of its four steps and the pulse arithmetic:

1. Lemma 2: the pairing `(1,2), (3,4), …` (`stdPairing`) induces a circuit decomposition.
2. Lemma 3 (black box): every circuit elects a leader, a node of the circuit (`elect`, hypotheses
   `hE1`, `hE2`); the same node may be elected on several circuits.
3. Lemma 4 at every node: every node elected on several circuits merges them (`Stage3`); afterwards
   distinct circuits have distinct leaders (`stage3_leaderInv`).
4. Lemma 5: merging phases (`PhaseRun`), at most `log₂ n` of them, end with a single Eulerian
   circuit and a single leader (`theorem1_circuit_level`).

The pulse bound `theorem1_pulses` assumes the black-box costs: electing a leader on a circuit `C`
costs at most `c₁ |C| IDmax` pulses, and one merging phase costs at most `c₂ |C| (log₂ IDmax + 1)`
pulses on each circuit `C`; then the total is at most `(c₁ + 4 c₂) |E| (IDmax + 1)`.
-/

namespace Podc.ContentObliviousEulerian

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option linter.unusedSectionVars false

/-! ### Step 3: Lemma 4 at every node -/

/-- Step 3 of the algorithm: the nodes are processed in the order `vs`; a node `v` that was
elected on at least one circuit re-pairs, as in Lemma 4, one of its pairs on each circuit on which
it was elected (`hcover`); these circuits are distinct (`hdist`). Nodes elected nowhere do
nothing. All re-pairings are local to their node. -/
inductive Stage3 (elect : G.Dart → V) : List V → Pairing G → Pairing G → Prop
  | nil (π : Pairing G) : Stage3 elect [] π π
  | skip {v : V} {vs : List V} {π π' : Pairing G} : (∀ d, elect d ≠ v) →
      Stage3 elect vs π π' → Stage3 elect (v :: vs) π π'
  | merge {v : V} {vs : List V} {π π' : Pairing G} (k : ℕ) (a : Fin (k + 1) → G.Dart)
      (hv : ∀ i, (a i).fst = v) (hinj : Function.Injective a) (hab : ∀ i j, a i ≠ π.pair (a j))
      (hel : ∀ i, elect (a i) = v) (hcover : ∀ d, elect d = v → ∃ i, π.Circ (a i) d)
      (hdist : ∀ i j, i ≠ j → ¬ π.Circ (a i) (a j)) :
      Stage3 elect vs (π.repair a hv hinj hab) π' → Stage3 elect (v :: vs) π π'

section stage3

variable {π₀ : Pairing G} {elect : G.Dart → V}
  (hE1 : ∀ d d', π₀.Circ d d' → elect d = elect d')
  (hE2 : ∀ d, ∃ x, π₀.Circ d x ∧ x.fst = elect d)

/-- The invariant of step 3 after processing the nodes satisfying `p`. -/
def Inv3 (π₀ : Pairing G) (elect : G.Dart → V) (p : V → Prop) (π : Pairing G) : Prop :=
  ∀ d d', π.Circ d d' ↔ π₀.Circ d d' ∨ (elect d = elect d' ∧ p (elect d))

include hE1 in
lemma Inv3.elect_eq {p : V → Prop} {π : Pairing G} (h : Inv3 π₀ elect p π) {d d' : G.Dart}
    (hc : π.Circ d d') : elect d = elect d' := by
  rcases (h d d').1 hc with h' | h'
  · exact hE1 _ _ h'
  · exact h'.1

include hE1 in
lemma Inv3.merge {p : V → Prop} {π : Pairing G} (h : Inv3 π₀ elect p π) {v : V} {k : ℕ}
    {a : Fin (k + 1) → G.Dart} (hv : ∀ i, (a i).fst = v) (hinj : Function.Injective a)
    (hab : ∀ i j, a i ≠ π.pair (a j)) (hel : ∀ i, elect (a i) = v)
    (hcover : ∀ d, elect d = v → ∃ i, π.Circ (a i) d)
    (hdist : ∀ i j, i ≠ j → ¬ π.Circ (a i) (a j)) :
    Inv3 π₀ elect (fun u => p u ∨ u = v) (π.repair a hv hinj hab) := by
  have hU : ∀ x, π.U a x ↔ elect x = v := by
    intro x
    constructor
    · rintro ⟨i, hi⟩; rw [← h.elect_eq hE1 hi, hel]
    · exact hcover x
  intro d d'
  rw [π.lemma4 hv hinj hab hdist, h, hU, hU]
  constructor
  · rintro ((h1 | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1.trans h2.symm, Or.inr h1⟩
  · rintro (h1 | ⟨h1, h2 | h2⟩)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1 ▸ h2⟩

include hE1 in
lemma stage3_inv {vs : List V} {π π' : Pairing G} (hs : Stage3 elect vs π π') :
    ∀ p : V → Prop, Inv3 π₀ elect p π →
      Inv3 π₀ elect (fun u => p u ∨ u ∈ vs) π' := by
  induction hs with
  | nil π =>
    intro p h d d'; simp only [List.not_mem_nil, or_false]; exact h d d'
  | @skip v vs π π' hno _ ih =>
    intro p h d d'
    rw [ih p h d d']
    simp only [List.mem_cons]
    constructor
    · rintro (h1 | ⟨h1, h2 | h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact Or.inr ⟨h1, Or.inr (Or.inr h2)⟩
    · rintro (h1 | ⟨h1, h2 | h2 | h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact absurd h2 (hno d)
      · exact Or.inr ⟨h1, Or.inr h2⟩
  | @merge v vs π π' k a hv hinj hab hel hcover hdist _ ih =>
    intro p h d d'
    rw [ih _ (h.merge hE1 hv hinj hab hel hcover hdist) d d']
    simp only [List.mem_cons]
    constructor
    · rintro (h1 | ⟨h1, (h2 | h2) | h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact Or.inr ⟨h1, Or.inr (Or.inl h2)⟩
      · exact Or.inr ⟨h1, Or.inr (Or.inr h2)⟩
    · rintro (h1 | ⟨h1, h2 | h2 | h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, Or.inl (Or.inl h2)⟩
      · exact Or.inr ⟨h1, Or.inl (Or.inr h2)⟩
      · exact Or.inr ⟨h1, Or.inr h2⟩

include hE1 hE2 in
/-- **After step 3 (Lemma 4 at every node), distinct circuits have distinct leaders**, and every
leader is a node of its circuit. -/
theorem stage3_leaderInv {π₁ : Pairing G} (hs : Stage3 elect (univ.toList) π₀ π₁) :
    LeaderInv π₁ elect := by
  have h0 : Inv3 π₀ elect (fun _ => False) π₀ := fun d d' => by simp
  have h1 := stage3_inv hE1 hs _ h0
  refine ⟨fun d d' => ?_, fun d => ?_⟩
  · rw [h1]; simp only [false_or, mem_toList, mem_univ, and_true]
    exact ⟨fun h => h.elim (hE1 _ _) id, Or.inr⟩
  · obtain ⟨x, hx, hxd⟩ := hE2 d
    exact ⟨x, (h1 d x).2 (Or.inl hx), hxd⟩

/-- The circuits of `π` as a finset of darts (the class of `x`). -/
def cls (π : Pairing G) (x : G.Dart) : Finset G.Dart := univ.filter (π.Circ x)

lemma cls_eq_iff (π : Pairing G) {x y : G.Dart} : cls π x = cls π y ↔ π.Circ x y := by
  constructor
  · intro h
    have : y ∈ cls π y := by simp [cls, Pairing.Circ.refl]
    rw [← h] at this; simpa [cls] using this
  · intro h; ext z; simp only [cls, mem_filter, mem_univ, true_and]; exact π.circ_iff_left h

include hE1 hE2 in
/-- Step 3 can always be carried out. -/
theorem exists_stage3 : ∀ (vs : List V), vs.Nodup → ∀ (p : V → Prop) (π : Pairing G),
    Inv3 π₀ elect p π → (∀ v ∈ vs, ¬ p v) → ∃ π', Stage3 elect vs π π' := by
  intro vs
  induction vs with
  | nil => intro _ p π _ _; exact ⟨π, Stage3.nil π⟩
  | cons v vs ih =>
    intro hnd p π h hp
    rw [List.nodup_cons] at hnd
    have hp' : ∀ u ∈ vs, ¬ (p u ∨ u = v) := by
      rintro u hu (h1 | rfl)
      · exact hp u (List.mem_cons_of_mem _ hu) h1
      · exact hnd.1 hu
    by_cases hno : ∀ d, elect d ≠ v
    · obtain ⟨π', h'⟩ := ih hnd.2 p π h (fun u hu => hp u (List.mem_cons_of_mem _ hu))
      exact ⟨π', Stage3.skip hno h'⟩
    push Not at hno
    -- a representative at `v` of every circuit elected at `v`
    have hrep : ∀ d, elect d = v → ∃ x, π.Circ d x ∧ x.fst = v ∧ elect x = v := by
      intro d hd
      obtain ⟨x, hx, hxd⟩ := hE2 d
      exact ⟨x, (h d x).2 (Or.inl hx), hxd.trans hd, (hE1 _ _ hx).symm.trans hd⟩
    let T := univ.filter (fun x : G.Dart => x.fst = v ∧ elect x = v)
    let C := T.image (cls π)
    obtain ⟨d₀, hd₀⟩ := hno
    have hCpos : 0 < C.card := by
      obtain ⟨x, -, hx1, hx2⟩ := hrep d₀ hd₀
      exact card_pos.2 ⟨cls π x, mem_image.2 ⟨x, by simp [T, hx1, hx2], rfl⟩⟩
    obtain ⟨k, hk⟩ : ∃ k, C.card = k + 1 := ⟨C.card - 1, by omega⟩
    let e : Fin (k + 1) ≃ C := (Fin.castOrderIso hk).symm.toEquiv.trans C.equivFin.symm
    have hex : ∀ i, ∃ x ∈ T, cls π x = (e i).1 := fun i => mem_image.1 (e i).2
    choose a ha hacls using hex
    have hT : ∀ i, (a i).fst = v ∧ elect (a i) = v := fun i => by simpa [T] using ha i
    have hdist : ∀ i j, i ≠ j → ¬ π.Circ (a i) (a j) := by
      intro i j hij hc
      apply hij
      apply e.injective
      apply Subtype.ext
      rw [← hacls, ← hacls, cls_eq_iff]; exact hc
    have hcover : ∀ d, elect d = v → ∃ i, π.Circ (a i) d := by
      intro d hd
      obtain ⟨x, hx, hx1, hx2⟩ := hrep d hd
      have hxC : cls π x ∈ C := mem_image.2 ⟨x, by simp [T, hx1, hx2], rfl⟩
      obtain ⟨i, hi⟩ := e.surjective ⟨_, hxC⟩
      refine ⟨i, ?_⟩
      have : cls π (a i) = cls π x := by rw [hacls, hi]
      exact ((cls_eq_iff π).1 this).trans hx.symm
    have hv : ∀ i, (a i).fst = v := fun i => (hT i).1
    have hinj := π.injective_of_dist hdist
    have hab := π.ne_pair_of_dist hdist
    obtain ⟨π', h'⟩ := ih hnd.2 _ _ (h.merge hE1 hv hinj hab (fun i => (hT i).2) hcover hdist) hp'
    exact ⟨π', Stage3.merge k a hv hinj hab (fun i => (hT i).2) hcover hdist h'⟩

end stage3

/-! ### Theorem 1, circuit level -/

/-- **Theorem 1 (circuit level).** Let `G` be a connected network all of whose nodes have even
degree, with injective IDs. Fix the pairing `(1,2), (3,4), …` of Lemma 2, and let `elect` be any
outcome of the per-circuit ring elections of Lemma 3 (constant on each circuit, a node of the
circuit). Then step 3 (Lemma 4 at every node) can be carried out, and after it, for every run of
`T` merging phases (Lemma 5): `T ≤ log₂ n`; a further phase is possible while at least two
circuits remain; and when no phase is possible, a single circuit with a single leader remains, which
is an Eulerian circuit. -/
theorem theorem1_circuit_level (hconn : G.Connected) (port : PortNumbering G)
    (heven : ∀ v, Even (G.degree v)) (ID : V → ℕ) (hID : Function.Injective ID)
    (elect : G.Dart → V)
    (hE1 : ∀ d d', (stdPairing port heven).Circ d d' → elect d = elect d')
    (hE2 : ∀ d, ∃ x, (stdPairing port heven).Circ d x ∧ x.fst = elect d) :
    (∃ π₁, Stage3 elect univ.toList (stdPairing port heven) π₁) ∧
    ∀ π₁, Stage3 elect univ.toList (stdPairing port heven) π₁ →
      LeaderInv π₁ elect ∧
      ∀ T π' lead', PhaseRun ID hID T π₁ elect π' lead' →
        LeaderInv π' lead' ∧ (0 < (leaders lead').card → T ≤ Nat.log 2 (Fintype.card V)) ∧
        (1 < (leaders lead').card → ∃ π'' lead'', PhaseStep ID hID π' lead' π'' lead'') ∧
        ((leaders lead').card = 1 →
          (∀ π'' lead'', ¬ PhaseStep ID hID π' lead' π'' lead'') ∧
          ∀ d : G.Dart, (π'.circuitWalk d).IsCircuit ∧ (π'.circuitWalk d).IsEulerian) := by
  refine ⟨exists_stage3 hE1 hE2 _ (nodup_toList _) (fun _ => False) _ (fun d d' => by simp)
    (fun _ _ h => h), fun π₁ hs => ?_⟩
  have hinv := stage3_leaderInv hE1 hE2 hs
  exact ⟨hinv, lemma5 hconn ID hID hinv⟩

/-- Non-vacuity of the black-box hypotheses: electing, on each circuit, the starting node of
some fixed dart of the circuit satisfies `hE1` and `hE2`. -/
lemma exists_elect (π : Pairing G) :
    ∃ elect : G.Dart → V, (∀ d d', π.Circ d d' → elect d = elect d') ∧
      ∀ d, ∃ x, π.Circ d x ∧ x.fst = elect d := by
  classical
  -- pick the representative via `cls`
  refine ⟨fun d => (Classical.choose (⟨d, rfl⟩ : ∃ x, cls π x = cls π d)).fst, ?_, ?_⟩
  · intro d d' h
    have : cls π d = cls π d' := (cls_eq_iff π).2 h
    simp only [this]
  · intro d
    refine ⟨_, ?_, rfl⟩
    exact ((cls_eq_iff π).1 (Classical.choose_spec (⟨d, rfl⟩ : ∃ x, cls π x = cls π d))).symm

/-! ### The pulse bound -/

/-- The circuits partition the edges, so their sizes add up to `|E|`. -/
lemma sum_card_circuits (π : Pairing G) :
    ∑ C ∈ π.circuits, C.card = G.edgeFinset.card := by
  rw [← card_biUnion]
  · congr 1
    ext e
    simp only [mem_biUnion]
    constructor
    · rintro ⟨C, hC, he⟩
      obtain ⟨d, -, rfl⟩ := mem_image.1 hC
      exact π.circuitEdges_subset_edgeFinset d he
    · intro he
      obtain ⟨C, ⟨hC, heC⟩, -⟩ := π.circuits_partition e (mem_edgeFinset.1 he)
      exact ⟨C, hC, heC⟩
  · intro C hC C' hC' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    apply hne
    obtain ⟨d, -, rfl⟩ := mem_image.1 hC
    obtain ⟨d', -, rfl⟩ := mem_image.1 hC'
    exact π.circuitEdges_eq_of_circ (π.circ_of_mem_circuitEdges he he')

lemma two_mul_add_three_le (L : ℕ) : 2 * L + 3 ≤ 4 * 2 ^ L := by
  induction L with
  | zero => norm_num
  | succ L ih => rw [pow_succ]; nlinarith [Nat.one_le_two_pow (n := L)]

lemma succ_sq_le_four_mul_two_pow (L : ℕ) : (L + 1) ^ 2 ≤ 4 * 2 ^ L := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    have := two_mul_add_three_le L
    calc (L + 1 + 1) ^ 2 = (L + 1) ^ 2 + (2 * L + 3) := by ring
      _ ≤ 4 * 2 ^ L + 4 * 2 ^ L := add_le_add ih this
      _ = 4 * 2 ^ (L + 1) := by ring

/-- `(log₂ m + 1)² ≤ 4 m` for `m ≥ 1`. -/
lemma log_succ_sq_le {m : ℕ} (hm : m ≠ 0) : (Nat.log 2 m + 1) ^ 2 ≤ 4 * m :=
  (succ_sq_le_four_mul_two_pow _).trans (by have := Nat.pow_log_le_self 2 hm; omega)

/-- With unique IDs, `n ≤ IDmax + 1`. -/
lemma card_le_idMax_succ (ID : V → ℕ) (hID : Function.Injective ID) :
    Fintype.card V ≤ univ.sup ID + 1 := by
  have : (univ.image ID) ⊆ range (univ.sup ID + 1) := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := mem_image.1 hx
    exact mem_range.2 (Nat.lt_succ_of_le (le_sup (mem_univ v)))
  have := card_le_card this
  rwa [card_image_of_injective _ hID, card_range, card_univ] at this

/-- **Theorem 1, pulse count.** Assume the black-box costs: the ring elections of Lemma 3 cost at
most `c₁ |C| IDmax` pulses on each circuit `C` of the initial decomposition `σ₀`, and merging phase
`t` costs at most `c₂ |C| (log₂ IDmax + 1)` pulses on each circuit `C` of the decomposition `σ t`
at its start. With at most `log₂ n` phases (Lemma 5), the total is at most
`(c₁ + 4 c₂) |E| (IDmax + 1) = O(|E| · IDmax)`. -/
theorem theorem1_pulses (ID : V → ℕ) (hID : Function.Injective ID) (c₁ c₂ : ℕ)
    (σ₀ : Pairing G) (σ : ℕ → Pairing G) {T : ℕ} (hT : T ≤ Nat.log 2 (Fintype.card V)) :
    (∑ C ∈ σ₀.circuits, c₁ * C.card * univ.sup ID) +
      ∑ t ∈ range T, ∑ C ∈ (σ t).circuits, c₂ * C.card * (Nat.log 2 (univ.sup ID) + 1) ≤
    (c₁ + 4 * c₂) * G.edgeFinset.card * (univ.sup ID + 1) := by
  set X := univ.sup ID
  set E := G.edgeFinset.card
  have h1 : ∑ C ∈ σ₀.circuits, c₁ * C.card * X = c₁ * E * X := by
    rw [show E = ∑ C ∈ σ₀.circuits, C.card from (sum_card_circuits σ₀).symm, mul_sum, sum_mul]
  have h2 : ∀ t, ∑ C ∈ (σ t).circuits, c₂ * C.card * (Nat.log 2 X + 1) =
      c₂ * E * (Nat.log 2 X + 1) := fun t => by
    rw [show E = ∑ C ∈ (σ t).circuits, C.card from (sum_card_circuits (σ t)).symm, mul_sum,
      sum_mul]
  simp only [h1, h2, sum_const, card_range, smul_eq_mul]
  have hn := card_le_idMax_succ ID hID
  have hT' : T ≤ Nat.log 2 (X + 1) := hT.trans (Nat.log_mono_right hn)
  have hlog : Nat.log 2 X ≤ Nat.log 2 (X + 1) := Nat.log_mono_right (Nat.le_succ X)
  have hsq := log_succ_sq_le (Nat.succ_ne_zero X)
  have hkey : T * (Nat.log 2 X + 1) ≤ 4 * (X + 1) := by
    calc T * (Nat.log 2 X + 1) ≤ (Nat.log 2 (X + 1) + 1) * (Nat.log 2 (X + 1) + 1) := by
          apply Nat.mul_le_mul <;> omega
      _ = (Nat.log 2 (X + 1) + 1) ^ 2 := (sq _).symm
      _ ≤ 4 * (X + 1) := hsq
  calc c₁ * E * X + T * (c₂ * E * (Nat.log 2 X + 1))
      = c₁ * E * X + c₂ * E * (T * (Nat.log 2 X + 1)) := by ring
    _ ≤ c₁ * E * (X + 1) + c₂ * E * (4 * (X + 1)) := by
        gcongr
        · omega
    _ = (c₁ + 4 * c₂) * E * (X + 1) := by ring

end Podc.ContentObliviousEulerian
