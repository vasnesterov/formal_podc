import Mathlib

/-!
# Subroutines of the early-stopping Phase King protocol (Section 2 and Lemma 3.4)

Lenzen, Sheikholeslami, *A Recursive Early-Stopping Phase King Protocol*, PODC 2022 [LS22].

* Definitions 2.1, 2.2, 2.5, 2.7 of [LS22] as input/output specifications on the correct nodes
  (`WeakValidatorSpec`, `ElectorsBCSpec`, `WeakAgreement`).
* Algorithm 2 (weak validator / termination check, two broadcast rounds) at the level of one
  instance: `vote` (line 3), `adopt` (lines 6–7), `strongOf` (lines 8–9). Lemmas 2.3, 2.4 and
  Corollary 2.8: `alg2_validity`, `alg2_weakAgreement`, `alg2_spec`.
* Algorithm 3 (king's broadcast) and Lemma 2.6: `kingOut`, `lemma_2_6`.
* Algorithm 5 (electors' broadcast via a black-box consensus on the electors) and the correctness
  part of Lemma 3.4: `alg5Out`, `lemma_3_4`.

An instance is described by the *receptions* of the correct nodes: `r1 i q` is what node `i`
received from `q`. Messages from correct senders arrive as sent (synchronous model); messages from
faulty senders are arbitrary. Throughout, `n = Fintype.card P`, `F` is the set of faulty nodes and
`3 t < n`, `|F| ≤ t` (the paper fixes `t = ⌈n/3⌉ - 1`, the largest such `t`).

"If received at least `x` times `b` for some `b ∈ {0,1}` do `y(b)`, for an arbitrary `b` if both
qualify" (convention (4)) is modelled by a tie-breaking bit `pick`, which may be chosen freely
(the results hold for every choice).
-/

set_option linter.unusedSectionVars false

namespace RecursivePhaseKing

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ### Counting received values -/

/-- The number of senders in `K` from which the value `b` was received. -/
def cntIn (K : Finset P) (m : P → Option Bool) (b : Bool) : ℕ :=
  (K.filter fun q => m q = some b).card

/-- The number of senders from which the value `b` was received. -/
def cnt (m : P → Option Bool) (b : Bool) : ℕ := cntIn univ m b

theorem cntIn_le_card (K : Finset P) (m : P → Option Bool) (b : Bool) : cntIn K m b ≤ K.card :=
  card_le_card (filter_subset _ _)

theorem cntIn_add_le (K : Finset P) (m : P → Option Bool) (b : Bool) :
    cntIn K m b + cntIn K m (!b) ≤ K.card := by
  unfold cntIn
  rw [← card_filter_add_card_filter_not (s := K) (fun q => m q = some b)]
  refine Nat.add_le_add_left (card_le_card fun q hq => ?_) _
  simp only [mem_filter] at hq ⊢
  refine ⟨hq.1, fun h => ?_⟩
  rw [h] at hq; cases b <;> simp at hq

theorem cnt_add_le (m : P → Option Bool) (b : Bool) : cnt m b + cnt m (!b) ≤ Fintype.card P := by
  have := cntIn_add_le univ m b; simpa [cnt] using this

/-- Lower bound: the correct senders in `K` that sent `b`. -/
theorem cntIn_ge_of (K F : Finset P) {m : P → Option Bool} {b : Bool}
    (h : ∀ q ∈ K, q ∉ F → m q = some b) : (K \ F).card ≤ cntIn K m b :=
  card_le_card fun q hq => by
    rw [mem_sdiff] at hq; exact mem_filter.2 ⟨hq.1, h q hq.1 hq.2⟩

theorem cnt_ge_of (F : Finset P) {m : P → Option Bool} {b : Bool}
    (h : ∀ q ∉ F, m q = some b) : Fintype.card P - F.card ≤ cnt m b := by
  have := cntIn_ge_of univ F (m := m) (b := b) (fun q _ hq => h q hq)
  rwa [← compl_eq_univ_sdiff, card_compl] at this

/-- Upper bound: at most `|K ∩ F|` faulty senders plus the correct ones that sent `b`. -/
theorem cntIn_le (K F : Finset P) (m : P → Option Bool) (b : Bool) :
    cntIn K m b ≤ (K ∩ F).card + ((K \ F).filter fun q => m q = some b).card := by
  unfold cntIn
  refine le_trans (card_le_card fun q hq => ?_) (card_union_le _ _)
  simp only [mem_filter, mem_union, mem_inter, mem_sdiff] at hq ⊢
  by_cases hF : q ∈ F
  · exact Or.inl ⟨hq.1, hF⟩
  · exact Or.inr ⟨⟨hq.1, hF⟩, hq.2⟩

theorem cnt_le (F : Finset P) (m : P → Option Bool) (b : Bool) :
    cnt m b ≤ F.card + (Fᶜ.filter fun q => m q = some b).card := by
  have := cntIn_le univ F m b
  simpa [cnt, compl_eq_univ_sdiff] using this

theorem cntIn_congr {K : Finset P} {m m' : P → Option Bool} (h : ∀ q ∈ K, m q = m' q) (b : Bool) :
    cntIn K m b = cntIn K m' b := by
  unfold cntIn; congr 1; exact filter_congr fun q hq => by rw [h q hq]

theorem cnt_congr {m m' : P → Option Bool} (h : ∀ q, m q = m' q) (b : Bool) :
    cnt m b = cnt m' b := cntIn_congr (fun q _ => h q) b

/-! ### Specifications (Definitions 2.2, 2.5, 2.7) -/

/-- Definition 2.2 of [LS22] (weak validator); Definition 2.7 (termination check) is the same
specification with `strong` renamed `term`. `b` are the inputs, `(o, s)` the outputs; only correct
nodes (outside `F`) matter. -/
def WeakValidatorSpec (F : Finset P) (b o s : P → Bool) : Prop :=
  (∀ v, (∀ i ∉ F, b i = v) → ∀ i ∉ F, o i = v ∧ s i = true) ∧
    (∀ i ∉ F, s i = true → ∀ j ∉ F, o j = o i)

/-- The *weak agreement* property of an input `(b, strong)` (as guaranteed by a weak validator):
if a correct node is strong, all correct nodes hold its value. -/
def WeakAgreement (F : Finset P) (b s : P → Bool) : Prop :=
  ∀ i ∉ F, s i = true → ∀ j ∉ F, b j = b i

/-- Definition 2.5 of [LS22] (electors' broadcast with elector set `K`). The precondition of
electors' agreement is the paper's `|V_g ∩ K| > ⌊2|K|/3⌋`. -/
def ElectorsBCSpec (F K : Finset P) (b s o : P → Bool) : Prop :=
  (∀ v, (∀ i ∉ F, b i = v ∧ s i = true) → ∀ i ∉ F, o i = v) ∧
    (2 * K.card / 3 < (K \ F).card → WeakAgreement F b s → ∀ i ∉ F, ∀ j ∉ F, o i = o j)

/-- `|V_g ∩ K| > ⌊2|K|/3⌋` is the same as "fewer than one third of `K` is faulty". -/
theorem good_iff (F K : Finset P) : 2 * K.card / 3 < (K \ F).card ↔ 3 * (K ∩ F).card < K.card := by
  have h := card_sdiff_add_card_inter K F
  omega

theorem WeakValidatorSpec.weakAgreement {F : Finset P} {b o s : P → Bool}
    (h : WeakValidatorSpec F b o s) : WeakAgreement F o s :=
  fun i hi hs j hj => h.2 i hi hs j hj

/-! ### Algorithm 2: the weak validator -/

/-- Line 3 of Algorithm 2: the value (if any) received at least `k` times. For `k = n - t > n/2`
there is at most one such value. -/
def vote (k : ℕ) (m : P → Option Bool) : Option Bool :=
  if k ≤ cnt m true then some true else if k ≤ cnt m false then some false else none

/-- Lines 1, 6–7 of Algorithm 2: adopt a value received at least `t + 1` times in the second
round (`pick` if both qualify), otherwise keep the input `x`. -/
def adopt (t : ℕ) (pick x : Bool) (m : P → Option Bool) : Bool :=
  if t + 1 ≤ cnt m true ∧ t + 1 ≤ cnt m false then pick
  else if t + 1 ≤ cnt m true then true else if t + 1 ≤ cnt m false then false else x

/-- Lines 5, 8–9 of Algorithm 2: `strong` iff some value was received at least `n - t` times in
the second round. -/
def strongOf (t : ℕ) (m : P → Option Bool) : Bool :=
  decide (Fintype.card P - t ≤ cnt m true ∨ Fintype.card P - t ≤ cnt m false)

theorem le_cnt_of_vote {k : ℕ} {m : P → Option Bool} {b : Bool} (h : vote k m = some b) :
    k ≤ cnt m b := by
  unfold vote at h; split_ifs at h with h1 h2 <;> cases h <;> assumption

theorem adopt_eq {t : ℕ} {pick x : Bool} {m : P → Option Bool} {b : Bool}
    (h1 : t + 1 ≤ cnt m b) (h2 : cnt m (!b) < t + 1) : adopt t pick x m = b := by
  unfold adopt; cases b <;> simp at h1 h2 <;> split_ifs <;> first | rfl | omega

variable {F : Finset P} {t : ℕ}

/-- If every correct sender sent `b`, then `b` is the value received `n - t` times. -/
theorem vote_of_all (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) {m : P → Option Bool}
    {b : Bool} (h : ∀ q ∉ F, m q = some b) : vote (Fintype.card P - t) m = some b := by
  have h1 := cnt_ge_of F h
  have h2 := cnt_add_le m b
  unfold vote
  cases b <;> simp only [Bool.not_true, Bool.not_false] at h1 h2 <;> split_ifs <;>
    first | rfl | omega

/-- Second half of Lemma 2.3: if every correct sender sent `b` in the second round, the output
is `(b, 1)`. -/
theorem alg2_out_of_all (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) {m : P → Option Bool}
    {b : Bool} (pick x : Bool) (h : ∀ q ∉ F, m q = some b) :
    adopt t pick x m = b ∧ strongOf t m = true := by
  have h1 := cnt_ge_of F h
  have h2 := cnt_add_le m b
  refine ⟨adopt_eq (by omega) (by omega), ?_⟩
  unfold strongOf; cases b <;> simp at h1 ⊢ <;> omega

/-- If a correct node received `b` at least `n - t` times, it adopts `b` (no other value is
received `t + 1` times). -/
theorem adopt_of_strong (h3 : 3 * t < Fintype.card P) {m : P → Option Bool} {b : Bool}
    (pick x : Bool) (h : Fintype.card P - t ≤ cnt m b) : adopt t pick x m = b := by
  have h2 := cnt_add_le m b
  exact adopt_eq (by omega) (by omega)

theorem strongOf_iff {m : P → Option Bool} :
    strongOf t m = true ↔ ∃ b, Fintype.card P - t ≤ cnt m b := by
  unfold strongOf
  simp only [decide_eq_true_eq]
  constructor
  · rintro (h | h) <;> exact ⟨_, h⟩
  · rintro ⟨b, h⟩; cases b
    · exact Or.inr h
    · exact Or.inl h

/-- The heart of Lemma 2.4: two correct nodes cannot send different values in the second round
of Algorithm 2. -/
theorem vote_unique (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) {x : P → Bool}
    {r1 : P → P → Option Bool} (h1 : ∀ i ∉ F, ∀ q ∉ F, r1 i q = some (x q)) {i j : P}
    (hi : i ∉ F) (hj : j ∉ F) {b : Bool} (hvi : vote (Fintype.card P - t) (r1 i) = some b)
    (hvj : vote (Fintype.card P - t) (r1 j) = some (!b)) : False := by
  have ci := le_trans (le_cnt_of_vote hvi) (cnt_le F (r1 i) b)
  have cj := le_trans (le_cnt_of_vote hvj) (cnt_le F (r1 j) (!b))
  have ei : (Fᶜ.filter fun q => r1 i q = some b) = Fᶜ.filter fun q => x q = b :=
    filter_congr fun q hq => by rw [h1 i hi q (mem_compl.1 hq)]; simp
  have ej : (Fᶜ.filter fun q => r1 j q = some (!b)) = Fᶜ.filter fun q => x q = !b :=
    filter_congr fun q hq => by rw [h1 j hj q (mem_compl.1 hq)]; simp
  rw [ei] at ci; rw [ej] at cj
  have hsum : (Fᶜ.filter fun q => x q = b).card + (Fᶜ.filter fun q => x q = !b).card ≤
      Fᶜ.card := by
    rw [← card_filter_add_card_filter_not (s := Fᶜ) (fun q => x q = b)]
    refine Nat.add_le_add_left (card_le_card fun q hq => ?_) _
    simp only [mem_filter] at hq ⊢
    refine ⟨hq.1, fun h => ?_⟩; rw [h] at hq; cases b <;> simp at hq
  rw [card_compl] at hsum
  omega

/-- Lemma 2.4 (weak agreement of Algorithm 2), in the form: if a correct node received `b` at least
`n - t` times in the second round, every correct node adopts `b`. -/
theorem alg2_weakAgreement_core (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) {x : P → Bool}
    {r1 r2 : P → P → Option Bool} (h1 : ∀ i ∉ F, ∀ q ∉ F, r1 i q = some (x q))
    (h2 : ∀ i ∉ F, ∀ q ∉ F, r2 i q = vote (Fintype.card P - t) (r1 q)) {i : P} (hi : i ∉ F)
    {b : Bool} (hs : Fintype.card P - t ≤ cnt (r2 i) b) {j : P} (hj : j ∉ F) (pick y : Bool) :
    adopt t pick y (r2 j) = b := by
  -- no correct node sends `!b` in the second round
  have hno : ∀ q ∉ F, vote (Fintype.card P - t) (r1 q) ≠ some (!b) := by
    intro q hq hv
    -- some correct node sent `b` in the second round
    have hc := le_trans hs (cnt_le F (r2 i) b)
    obtain ⟨q', hq'⟩ : (Fᶜ.filter fun q => r2 i q = some b).Nonempty := by
      rw [← card_pos]; omega
    rw [mem_filter, mem_compl] at hq'
    rw [h2 i hi q' hq'.1] at hq'
    exact vote_unique h3 hF h1 hq'.1 hq hq'.2 hv
  have hlow : Fintype.card P - t - F.card ≤ cnt (r2 j) b := by
    have hc := le_trans hs (cnt_le F (r2 i) b)
    have : (Fᶜ.filter fun q => r2 i q = some b).card ≤ cnt (r2 j) b := by
      refine card_le_card fun q hq => ?_
      rw [mem_filter, mem_compl] at hq
      rw [h2 i hi q hq.1] at hq
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [h2 j hj q hq.1]; exact hq.2
    omega
  have hhigh : cnt (r2 j) (!b) ≤ F.card := by
    have hc := cnt_le F (r2 j) (!b)
    have : (Fᶜ.filter fun q => r2 j q = some (!b)) = ∅ := by
      refine filter_eq_empty_iff.2 fun q hq => ?_
      rw [h2 j hj q (mem_compl.1 hq)]; exact hno q (mem_compl.1 hq)
    rw [this, card_empty] at hc; omega
  exact adopt_eq (by omega) (by omega)

/-- One instance of Algorithm 2 (weak validator, or termination check), described by the
receptions of the nodes in the two broadcast rounds. -/
structure Alg2Inst (F : Finset P) (t : ℕ) where
  /-- Inputs. -/
  x : P → Bool
  /-- Tie-breaking choices (line 6 when both values qualify). -/
  pick : P → Bool
  /-- `r1 i q`: the first-round message received by `i` from `q`. -/
  r1 : P → P → Option Bool
  /-- `r2 i q`: the second-round message received by `i` from `q`. -/
  r2 : P → P → Option Bool
  h1 : ∀ i ∉ F, ∀ q ∉ F, r1 i q = some (x q)
  h2 : ∀ i ∉ F, ∀ q ∉ F, r2 i q = vote (Fintype.card P - t) (r1 q)

namespace Alg2Inst

variable (I : Alg2Inst F t)

/-- The returned value `o_i`. -/
def o (i : P) : Bool := adopt t (I.pick i) (I.x i) (I.r2 i)

/-- The returned bit `strong_i`. -/
def s (i : P) : Bool := strongOf t (I.r2 i)

/-- Lemma 2.3 of [LS22] (validity of Algorithm 2). -/
theorem lemma_2_3 (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) {v : Bool}
    (hv : ∀ i ∉ F, I.x i = v) : ∀ i ∉ F, I.o i = v ∧ I.s i = true := by
  intro i hi
  have hall : ∀ q ∉ F, I.r2 i q = some v := by
    intro q hq
    rw [I.h2 i hi q hq]
    exact vote_of_all h3 hF fun q' hq' => by rw [I.h1 q hq q' hq', hv q' hq']
  exact alg2_out_of_all h3 hF _ _ hall

/-- Lemma 2.4 of [LS22] (weak agreement of Algorithm 2). -/
theorem lemma_2_4 (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) :
    ∀ i ∉ F, I.s i = true → ∀ j ∉ F, I.o j = I.o i := by
  intro i hi hs j hj
  obtain ⟨b, hb⟩ := strongOf_iff.1 hs
  rw [o, o, alg2_weakAgreement_core h3 hF I.h1 I.h2 hi hb hj, adopt_of_strong h3 _ _ hb]

/-- Lemmas 2.3 and 2.4 of [LS22]: Algorithm 2 implements a weak validator (Definition 2.2). -/
theorem spec (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) : WeakValidatorSpec F I.x I.o I.s :=
  ⟨fun _ hv => I.lemma_2_3 h3 hF hv, I.lemma_2_4 h3 hF⟩

/-- Corollary 2.8 of [LS22]: Algorithm 2 implements the termination check (Definition 2.7),
which is the same specification. -/
theorem corollary_2_8 (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) :
    WeakValidatorSpec F I.x I.o I.s := I.spec h3 hF

end Alg2Inst

/-! ### Algorithm 3: king's broadcast -/

/-- Algorithm 3 at node `i`: keep `b` if strong, otherwise adopt the value `rk` received from the
king (if any). -/
def kingOut (b strong : Bool) (rk : Option Bool) : Bool :=
  if strong then b else rk.getD b

/-- Lemma 2.6 of [LS22]: Algorithm 3 implements electors' broadcast for `K = {k}`. `rk i` is what
`i` received from the king `k`; a correct king sends its input to everybody. -/
theorem lemma_2_6 {F : Finset P} {k : P} {b s : P → Bool} {rk : P → Option Bool}
    (hk : k ∉ F → ∀ i ∉ F, rk i = some (b k)) :
    ElectorsBCSpec F {k} b s (fun i => kingOut (b i) (s i) (rk i)) := by
  refine ⟨fun v hv i hi => ?_, fun hK hwa i hi j hj => ?_⟩
  · simp [kingOut, (hv i hi).2, (hv i hi).1]
  · have hkF : k ∉ F := by
      intro hkF
      have : ({k} \ F : Finset P) = ∅ := by simp [hkF]
      rw [this] at hK; simp at hK
    have key : ∀ i ∉ F, kingOut (b i) (s i) (rk i) = b k := by
      intro i hi
      unfold kingOut
      split_ifs with hs
      · exact (hwa i hi hs k hkF).symm
      · rw [hk hkF i hi]; rfl
    beta_reduce
    rw [key i hi, key j hj]

/-! ### Algorithm 5: electors' broadcast via consensus among the electors -/

/-- The specification of the consensus routine called by the electors `K` (binary consensus,
Definition 2.1, guaranteed only if fewer than a third of `K` is faulty): `c i` is the output of
elector `i` on input `b i`. -/
def ConsensusOn (F K : Finset P) (b c : P → Bool) : Prop :=
  2 * K.card / 3 < (K \ F).card →
    (∀ i ∈ K, i ∉ F → ∀ j ∈ K, j ∉ F → c i = c j) ∧
      ∀ v, (∀ i ∈ K, i ∉ F → b i = v) → ∀ i ∈ K, i ∉ F → c i = v

/-- Majority of the values received from `K` (`pick` on a tie). -/
def majIn (K : Finset P) (pick : Bool) (m : P → Option Bool) : Bool :=
  if cntIn K m false < cntIn K m true then true
  else if cntIn K m true < cntIn K m false then false else pick

/-- Algorithm 5 at node `i` (lines 5–7): keep `b` if strong, otherwise take the majority of the
consensus outputs received from the electors. -/
def alg5Out (K : Finset P) (pick b strong : Bool) (m : P → Option Bool) : Bool :=
  if strong then b else majIn K pick m

/-- Lemma 3.4 of [LS22] (correctness part): Algorithm 5 implements electors' broadcast
(Definition 2.5), given a consensus routine on `K` that is correct when fewer than a third of `K`
is faulty. `m i q` is what `i` receives from the elector `q` in the final broadcast round;
correct electors broadcast their consensus output `c q`. -/
theorem lemma_3_4 {F K : Finset P} {b s c : P → Bool} {pick : P → Bool}
    {m : P → P → Option Bool} (hc : ConsensusOn F K b c)
    (hm : ∀ i ∉ F, ∀ q ∈ K, q ∉ F → m i q = some (c q)) :
    ElectorsBCSpec F K b s (fun i => alg5Out K (pick i) (b i) (s i) (m i)) := by
  refine ⟨fun v hv i hi => ?_, fun hK hwa i hi j hj => ?_⟩
  · simp [alg5Out, (hv i hi).2, (hv i hi).1]
  · obtain ⟨hag, hval⟩ := hc hK
    obtain ⟨e, he⟩ : (K \ F).Nonempty := by rw [← card_pos]; omega
    rw [mem_sdiff] at he
    set w := c e with hw
    have hcw : ∀ q ∈ K, q ∉ F → c q = w := fun q hq hqF => hag q hq hqF e he.1 he.2
    -- the outputs of correct non-strong nodes are `w`
    have hmaj : ∀ i ∉ F, majIn K (pick i) (m i) = w := by
      intro i hi
      have hlo : (K \ F).card ≤ cntIn K (m i) w :=
        cntIn_ge_of K F fun q hq hqF => by rw [hm i hi q hq hqF, hcw q hq hqF]
      have hhi : cntIn K (m i) (!w) ≤ (K ∩ F).card := by
        have h0 := cntIn_le K F (m i) (!w)
        have h1 : ((K \ F).filter fun q => m i q = some (!w)) = ∅ := by
          refine filter_eq_empty_iff.2 fun q hq => ?_
          rw [mem_sdiff] at hq
          rw [hm i hi q hq.1 hq.2, hcw q hq.1 hq.2]; cases w <;> simp
        rw [h1, card_empty] at h0; omega
      have hgood := (good_iff F K).1 hK
      have := card_sdiff_add_card_inter K F
      unfold majIn
      revert hlo hhi
      cases w <;> intro hlo hhi <;> (try simp only [Bool.not_true, Bool.not_false] at hlo hhi) <;>
        split_ifs <;> first | rfl | omega
    -- strong correct nodes also hold `w`
    have key : ∀ i ∉ F, alg5Out K (pick i) (b i) (s i) (m i) = w := by
      intro i hi
      unfold alg5Out
      split_ifs with hs
      · have := hval (b i) fun q _ hqF => hwa i hi hs q hqF
        rw [← this e he.1 he.2]
      · exact hmaj i hi
    beta_reduce
    rw [key i hi, key j hj]

end RecursivePhaseKing
