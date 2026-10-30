import Papers.PODC2015.MSTImpromptuRepair.HPTestOut
import Papers.PODC2015.MSTImpromptuRepair.Isolation
import Papers.PODC2015.MSTImpromptuRepair.Prob

/-!
# `FindAny`: finding an edge leaving a tree (Section 4.1, Lemma 5)

Steps 3–4 of `FindAny(x)` for one hash function `h` (given by its values `hv : U → ℕ` on edge
numbers `num e ∈ U`; edge numbers are XORed as bit vectors `enc : U → N`, `N` of characteristic 2):

* `hvec y i` — node `y`'s bit `h_i(y)`: parity of its incident edges hashing into `[2^i]`;
  `hT i = ⊕_{y ∈ T} h_i(y)`;
* `minIdx I` — `min = min{i ∈ I | h_i(T) = 1}` (`I` is the index range; the paper uses
  `I = {1, …, lg r}`);
* `wT i = ⊕_{y ∈ T} w(y)` with `w(y) = ⊕{e ∈ E(y) | h(e) < 2^i}`;
* `sumEnd z` — step 4's `Sum`: the number of endpoints in `T` of the edge numbered `z`;
* `step` — the result of steps 3–4: the edge numbered `w(T)` if `Sum = 1`, else `∅`.

Results:

* `hT_eq_card_cut`, `wT_eq_sum_cut` — the aggregated values only depend on the cut (the edges inside
  `T` cancel, `sum_incidence_eq_sum_cut`).
* `step_eq_some_of_isolated` — if for some `j ∈ I` exactly one leaving edge `e` hashes into
  `[2^j]` ("Event A"), the step returns `e`; `step_sound` — the step only ever returns leaving
  edges (so `FindAny` never returns a wrong edge).
* `step_success_prob` / `step_success_prob_paperIdx` — with a pairwise independent `h` into
  `[2^ℓ]`, the step succeeds with probability `≥ 3/16` provided `2|W| < 2^ℓ` and `I ⊇ {0, …, ℓ-1}`,
  or `4|W| ≤ 2^ℓ` and the paper's `I = {1, …, ℓ}` (`W` = the leaving edges).
* `lemma5_findAnyC` — **Lemma 5 for `FindAny-C`** (with `r = 2^ℓ > 4 · ∑ deg` instead of
  `r > ∑ deg`): it never returns a non-leaving edge, returns `∅` if no edge leaves, and returns a
  leaving edge with probability `≥ 1/16`.
* `lemma5_findAny` — **Lemma 5 for `FindAny`**: failure probability `≤ δ + (1 - 1/16)^K` for `K`
  repetitions, and `≤ 2ε` with the paper's `K ≥ 16 ln(1/ε)`.

The counterexample for the paper's parameter `r > ∑ deg` is in `FindAnyCounterexample.lean`.
-/

namespace Podc.MSTImpromptuRepair

open Finset Cslib.Probability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (T : Finset V) {U N : Type*} [AddCommGroup N] [DecidableEq N]
  (num : Sym2 V → U) (enc : U → N) (hv : U → ℕ)

/-- Step 3b: the `i`-th bit `h_i(y)` of node `y`: the parity of the set of its incident edges
whose numbers hash into `[2^i]`. -/
def hvec (y : V) (i : ℕ) : ZMod 2 :=
  ∑ e ∈ G.incidenceFinset y, if hv (num e) < 2 ^ i then 1 else 0

/-- Step 3c: `h_i(T) = ⊕_{y ∈ T} h_i(y)`, computed up the tree. -/
def hT (i : ℕ) : ZMod 2 := ∑ y ∈ T, hvec G num hv y i

/-- Step 3c: `min = min{i ∈ I | h_i(T) = 1}` (`none` if there is no such index). -/
def minIdx (I : Finset ℕ) : Option ℕ :=
  if h : (I.filter fun i => hT G T num hv i = 1).Nonempty then
    some ((I.filter fun i => hT G T num hv i = 1).min' h) else none

/-- Step 3d: `w(y) = ⊕{e ∈ E(y) | h(e) < 2^i}` (edge numbers XORed as bit vectors). -/
def wloc (y : V) (i : ℕ) : N :=
  ∑ e ∈ (G.incidenceFinset y).filter (fun e => hv (num e) < 2 ^ i), enc (num e)

/-- Step 3d: `w(T) = ⊕_{y ∈ T} w(y)`. -/
def wT (i : ℕ) : N := ∑ y ∈ T, wloc G num enc hv y i

/-- Step 4: `Sum` = the number of endpoints in `T` incident to the edge (of `G`) whose number
is `z` (`0` if there is no such edge). -/
def sumEnd (z : N) : ℕ :=
  #((T ×ˢ G.edgeFinset).filter fun p => p.1 ∈ p.2 ∧ enc (num p.2) = z)

/-- Steps 3–5 for one hash function: return the edge numbered `w(T)` if `Sum = 1`, else `∅`. -/
noncomputable def step (I : Finset ℕ) : Option (Sym2 V) :=
  match minIdx G T num hv I with
  | none => none
  | some i =>
    if h : ∃ e ∈ G.edgeFinset, enc (num e) = wT G T num enc hv i ∧ sumEnd G T num enc
        (wT G T num enc hv i) = 1 then some h.choose else none

variable {G T num enc hv}

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

/-- `h_i(T)` is the parity of the number of leaving edges hashing into `[2^i]`. -/
theorem hT_eq_card_cut (i : ℕ) :
    hT G T num hv i = (#((cut G T).filter fun e => hv (num e) < 2 ^ i) : ZMod 2) := by
  unfold hT hvec
  rw [sum_incidence_eq_sum_cut G zmod2_add_self T, card_filter]
  push_cast; rfl

variable (h2 : ∀ x : N, x + x = 0)
include h2

/-- `w(T)` is the XOR of the numbers of the leaving edges hashing into `[2^i]`. -/
theorem wT_eq_sum_cut (i : ℕ) :
    wT G T num enc hv i = ∑ e ∈ (cut G T).filter (fun e => hv (num e) < 2 ^ i), enc (num e) := by
  unfold wT wloc
  exact sum_incidence_filter_eq_sum_cut G h2 T _ _

omit h2 in
/-- If edge numbers are distinct, `Sum = 1` for the number of an edge `e` of `G` iff `e` leaves
`T`. -/
theorem sumEnd_eq_one_iff (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet) {e : Sym2 V}
    (he : e ∈ G.edgeSet) : sumEnd G T num enc (enc (num e)) = 1 ↔ crosses T e := by
  have hset : ((T ×ˢ G.edgeFinset).filter fun p => p.1 ∈ p.2 ∧ enc (num p.2) = enc (num e)) =
      (T.filter (· ∈ e)) ×ˢ {e} := by
    ext ⟨v, f⟩
    simp only [mem_filter, mem_product, SimpleGraph.mem_edgeFinset, mem_singleton]
    constructor
    · rintro ⟨⟨hv, hf⟩, hvf, hnum⟩
      have := hinj hf he hnum
      subst this; exact ⟨⟨hv, hvf⟩, rfl⟩
    · rintro ⟨⟨hv, hvf⟩, rfl⟩; exact ⟨⟨hv, he⟩, hvf, rfl⟩
  rw [sumEnd, hset, card_product, card_singleton, mul_one]
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := G.ne_of_adj he
    have : T.filter (· ∈ s(a, b)) = (T.filter (· = a)) ∪ (T.filter (· = b)) := by
      ext v; simp [Sym2.mem_iff, or_and_right, and_or_left]
    rw [this, card_union_of_disjoint (by
      rw [disjoint_filter]; intro v _ h1 h2; exact hab (h1 ▸ h2))]
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> simp [ha, hb, filter_eq']

omit h2 in
/-- The step only ever returns a leaving edge of `G`. -/
theorem step_sound (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet) {I : Finset ℕ}
    {e : Sym2 V} (h : step G T num enc hv I = some e) : e ∈ cut G T := by
  unfold step at h
  split at h
  · simp at h
  · split_ifs at h with hex
    · cases h
      obtain ⟨hE, hnum, hsum⟩ := hex.choose_spec
      rw [← hnum] at hsum
      rw [SimpleGraph.mem_edgeFinset] at hE
      exact (mem_cut G).2 ⟨hE, (sumEnd_eq_one_iff hinj hE).1 hsum⟩

/-- **Correctness of steps 3–4** ("Event A" in the proof of Lemma 5). If for some index `j ∈ I`
exactly one leaving edge `e` hashes into `[2^j]`, then `min ≤ j`, exactly that edge hashes into
`[2^min]`, `w(T)` is its number, `Sum = 1`, and the step returns `e`. -/
theorem step_eq_some_of_isolated (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet)
    {I : Finset ℕ} {j : ℕ} (hj : j ∈ I) {e : Sym2 V}
    (hone : (cut G T).filter (fun e => hv (num e) < 2 ^ j) = {e}) :
    step G T num enc hv I = some e := by
  have heC : e ∈ cut G T := by
    have : e ∈ (cut G T).filter (fun e => hv (num e) < 2 ^ j) := by rw [hone]; simp
    exact (mem_filter.1 this).1
  have hjT : hT G T num hv j = 1 := by rw [hT_eq_card_cut, hone]; simp
  have hne : (I.filter fun i => hT G T num hv i = 1).Nonempty := ⟨j, by simp [hj, hjT]⟩
  set i := (I.filter fun i => hT G T num hv i = 1).min' hne with hi
  have hmin : minIdx G T num hv I = some i := by simp [minIdx, hne, hi]
  have hij : i ≤ j := min'_le _ _ (by simp [hj, hjT])
  have hiT : hT G T num hv i = 1 := (mem_filter.1 (min'_mem _ hne)).2
  -- at `min`, the set of leaving edges hashing into `[2^min]` is `{e}`
  have hsub : (cut G T).filter (fun e => hv (num e) < 2 ^ i) ⊆ {e} := by
    rw [← hone]
    intro f hf
    simp only [mem_filter] at hf ⊢
    exact ⟨hf.1, lt_of_lt_of_le hf.2 (Nat.pow_le_pow_right (by norm_num) hij)⟩
  have hseti : (cut G T).filter (fun e => hv (num e) < 2 ^ i) = {e} := by
    rcases subset_singleton_iff.1 hsub with h0 | h1
    · rw [hT_eq_card_cut, h0] at hiT; simp at hiT
    · exact h1
  have hw : wT G T num enc hv i = enc (num e) := by rw [wT_eq_sum_cut h2, hseti, sum_singleton]
  have heE : e ∈ G.edgeSet := ((mem_cut G).1 heC).1
  have hsum : sumEnd G T num enc (enc (num e)) = 1 :=
    (sumEnd_eq_one_iff hinj heE).2 ((mem_cut G).1 heC).2
  have hex : ∃ f ∈ G.edgeFinset, enc (num f) = wT G T num enc hv i ∧
      sumEnd G T num enc (wT G T num enc hv i) = 1 :=
    ⟨e, by simpa using heE, hw.symm, hw ▸ hsum⟩
  unfold step
  rw [hmin]
  simp only [hex, dite_true, Option.some.injEq]
  obtain ⟨hE, hnum, -⟩ := hex.choose_spec
  exact hinj (by simpa using hE) heE (hnum.trans hw)

/-! ### Probability of success of one round -/

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {K : Finset U} [DecidableEq U]

omit [DecidableEq U] in
private theorem filter_card_one {W : Finset (Sym2 V)} {p : Sym2 V → Prop} [DecidablePred p]
    (h : #(W.filter p) = 1) : ∃ e, W.filter p = {e} := card_eq_one.1 h

/-- With `W` the set of leaving edges, `h : Ω → U → ℕ` pairwise independent into `[2^ℓ]` on a key
set containing the numbers of the leaving edges (numbers distinct), `2|W| < 2^ℓ` and an index
range containing `{0, …, ℓ-1}`, one round of steps 3–4 returns a leaving edge with probability at
least `3/16`. -/
theorem step_success_prob (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet)
    {h : Ω → U → ℕ} {ℓ : ℕ} (hp : IsPairwiseIndep (2 ^ ℓ) K h)
    (hK : ∀ e ∈ cut G T, num e ∈ K) (hW0 : 0 < #(cut G T)) (hWℓ : 2 * #(cut G T) < 2 ^ ℓ)
    {I : Finset ℕ} (hI : ∀ j < ℓ, j ∈ I) :
    3 / 16 ≤ uprob (fun ω => ∃ e ∈ cut G T, step G T num enc (h ω) I = some e) := by
  classical
  set W := (cut G T).image num
  have hinjn : Set.InjOn num (cut G T) := fun a ha b hb hab =>
    hinj ((mem_cut G).1 ha).1 ((mem_cut G).1 hb).1 (by simp [hab])
  have hWc : #W = #(cut G T) := card_image_of_injOn hinjn
  have hWK : W ⊆ K := by intro x hx; obtain ⟨e, he, rfl⟩ := mem_image.1 hx; exact hK e he
  obtain ⟨j, hjℓ, -, hprob⟩ := lemma4_strong hp hWK (by omega) (by omega)
  refine le_trans hprob (uprob_mono fun ω hω => ?_)
  -- transport "exactly one number in `W`" to "exactly one leaving edge"
  have hcard : #((cut G T).filter fun e => h ω (num e) < 2 ^ j) = 1 := by
    rw [← hω, filter_image, card_image_of_injOn (hinjn.mono (coe_subset.2 (filter_subset _ _)))]
  obtain ⟨e, he⟩ := card_eq_one.1 hcard
  have heC : e ∈ cut G T := (mem_filter.1 (he ▸ mem_singleton_self e : e ∈ _)).1
  exact ⟨e, heC, step_eq_some_of_isolated h2 hinj (hI j hjℓ) he⟩

/-- Same with the paper's index range `I = {1, …, ℓ}`, provided `4|W| ≤ 2^ℓ`. -/
theorem step_success_prob_paperIdx (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet)
    {h : Ω → U → ℕ} {ℓ : ℕ} (hp : IsPairwiseIndep (2 ^ ℓ) K h)
    (hK : ∀ e ∈ cut G T, num e ∈ K) (hW0 : 0 < #(cut G T)) (hWℓ : 4 * #(cut G T) ≤ 2 ^ ℓ) :
    3 / 16 ≤ uprob (fun ω => ∃ e ∈ cut G T, step G T num enc (h ω) (Icc 1 ℓ) = some e) := by
  classical
  set W := (cut G T).image num
  have hinjn : Set.InjOn num (cut G T) := fun a ha b hb hab =>
    hinj ((mem_cut G).1 ha).1 ((mem_cut G).1 hb).1 (by simp [hab])
  have hWc : #W = #(cut G T) := card_image_of_injOn hinjn
  have hWK : W ⊆ K := by intro x hx; obtain ⟨e, he, rfl⟩ := mem_image.1 hx; exact hK e he
  obtain ⟨j, hjℓ, hjdef, hprob⟩ := lemma4_strong hp hWK (by omega) (by omega)
  -- `j = ℓ - ⌈lg |W|⌉ - 1 ≥ 1` since `|W| ≤ 2^(ℓ-2)`
  have hj1 : 1 ≤ j := by
    rw [hjdef]
    have hc : Nat.clog 2 #W ≤ ℓ - 2 := by
      rw [Nat.clog_le_iff_le_pow (by norm_num)]
      have hℓ : 2 ≤ ℓ := by
        by_contra hlt; push_neg at hlt
        interval_cases ℓ <;> omega
      have : 2 ^ ℓ = 4 * 2 ^ (ℓ - 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      omega
    have hℓ : 2 ≤ ℓ := by
      by_contra hlt; push_neg at hlt
      interval_cases ℓ <;> omega
    omega
  refine le_trans hprob (uprob_mono fun ω hω => ?_)
  have hcard : #((cut G T).filter fun e => h ω (num e) < 2 ^ j) = 1 := by
    rw [← hω, filter_image, card_image_of_injOn (hinjn.mono (coe_subset.2 (filter_subset _ _)))]
  obtain ⟨e, he⟩ := card_eq_one.1 hcard
  have heC : e ∈ cut G T := (mem_filter.1 (he ▸ mem_singleton_self e : e ∈ _)).1
  exact ⟨e, heC, step_eq_some_of_isolated h2 hinj (by simp; omega) he⟩

/-! ### `FindAny-C` and `FindAny` -/

omit h2 [Nonempty Ω] [DecidableEq U] in
/-- The sum of the degrees of the nodes of `T` bounds the number of leaving edges. -/
theorem card_cut_le_card_Eup :
    #(cut G T) ≤ #(Eup G (fun _ => True) T) := by
  refine card_le_card_of_surjOn (fun d : V × V => s(d.1, d.2)) ?_
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨hab, hc⟩ := (mem_cut G).1 he
    simp only [SimpleGraph.mem_edgeSet, crosses_mk] at hab hc
    by_cases ha : a ∈ T
    · exact ⟨(a, b), by simp [Eup, hab, ha], rfl⟩
    · have hb : b ∈ T := by by_contra hb; exact ha (hc.2 hb)
      exact ⟨(b, a), by simp [Eup, hab.symm, hb], Sym2.eq_swap⟩


variable (G T num enc) in
/-- `FindAny-C(x)`: `HP-TestOut` with random point `α` (dart numbers `dnum`); if it reports a
leaving edge, one round of steps 3–4 with the hash function `hv`; otherwise `∅`. -/
noncomputable def findAnyC {p : ℕ} (dnum : V × V → ℕ) (α : ZMod p) (hv : U → ℕ)
    (I : Finset ℕ) : Option (Sym2 V) :=
  if hpTestOut G (fun _ => True) dnum T α then step G T num enc hv I else none

variable (G T num enc) in
/-- `FindAny(x)`: `HP-TestOut`, then up to `K` rounds of steps 3–5 with fresh hash functions
`hvs 0, …, hvs (K-1)`, returning the first edge found. -/
noncomputable def findAny {p K : ℕ} (dnum : V × V → ℕ) (α : ZMod p) (hvs : Fin K → U → ℕ)
    (I : Finset ℕ) : Option (Sym2 V) :=
  if hpTestOut G (fun _ => True) dnum T α then
    (List.ofFn fun k => step G T num enc (hvs k) I).findSome? id
  else none

omit h2 in
/-- `FindAny-C` never returns an edge that does not leave `T`. -/
theorem findAnyC_sound (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet) {p : ℕ}
    (dnum : V × V → ℕ) (α : ZMod p) (hv : U → ℕ) (I : Finset ℕ) {e : Sym2 V}
    (h : findAnyC G T num enc dnum α hv I = some e) : e ∈ cut G T := by
  unfold findAnyC at h
  split_ifs at h
  exact step_sound hinj h

omit h2 in
/-- `FindAny` never returns an edge that does not leave `T`. -/
theorem findAny_sound (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet) {p K : ℕ}
    (dnum : V × V → ℕ) (α : ZMod p) (hvs : Fin K → U → ℕ) (I : Finset ℕ) {e : Sym2 V}
    (h : findAny G T num enc dnum α hvs I = some e) : e ∈ cut G T := by
  unfold findAny at h
  split_ifs at h
  obtain ⟨o, ho, hoe⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ho
  exact step_sound hinj hoe

omit h2 in
/-- If no edge leaves `T`, `FindAny-C` and `FindAny` return `∅`. -/
theorem findAnyC_findAny_none_of_no_cut (hno : cut G T = ∅) {p K : ℕ} (dnum : V × V → ℕ)
    (α : ZMod p) (hv : U → ℕ) (hvs : Fin K → U → ℕ) (I : Finset ℕ) :
    findAnyC G T num enc dnum α hv I = none ∧ findAny G T num enc dnum α hvs I = none := by
  have : ¬ hpTestOut G (fun _ => True) dnum T α :=
    hpTestOut_false_of_no_cut G _ dnum T (by simp [hno]) α
  simp [findAnyC, findAny, this]

/-- **Lemma 5, `FindAny-C`** (with the hash range `r = 2^ℓ ≥ 4 ∑_{y ∈ T} deg y`; the paper only
asks `r > ∑ deg`, see `FindAnyCounterexample.lean`). The sample space is the random point `α` of
`HP-TestOut` times the seed `ω` of the pairwise independent hash function. If the dart numbers
are distinct modulo the prime `p ≥ 2 ∑ deg`, then, when some edge leaves `T`, `FindAny-C` returns
a leaving edge with probability at least `1/16` (and otherwise `∅`, by `findAnyC_sound`). -/
theorem lemma5_findAnyC {p : ℕ} [Fact p.Prime] (dnum : V × V → ℕ)
    (hdinj : Set.InjOn (fun d => (dnum d : ZMod p)) (darts G))
    (hp2 : 2 * #(Eup G (fun _ => True) T) ≤ p)
    (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet)
    {h : Ω → U → ℕ} {ℓ : ℕ} (hp : IsPairwiseIndep (2 ^ ℓ) K h)
    (hK : ∀ e ∈ cut G T, num e ∈ K) (hr : 4 * #(Eup G (fun _ => True) T) ≤ 2 ^ ℓ)
    (hcut : (cut G T).Nonempty) :
    1 / 16 ≤ uprob (fun x : ZMod p × Ω =>
      ∃ e ∈ cut G T, findAnyC G T num enc dnum x.1 (h x.2) (Icc 1 ℓ) = some e) := by
  classical
  have hW0 : 0 < #(cut G T) := card_pos.2 hcut
  have hle := card_cut_le_card_Eup (G := G) (T := T)
  have hstep := step_success_prob_paperIdx h2 hinj hp hK hW0 (by omega)
  have hcut' : ∃ e ∈ cut G T, (fun _ => True) e := by
    obtain ⟨e, he⟩ := hcut; exact ⟨e, he, trivial⟩
  have hfail := hpTestOut_fail_prob_le (P := fun _ => True) dnum T hdinj hcut'
  have hpp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpass : 1 / 2 ≤ uprob (fun α : ZMod p => hpTestOut G (fun _ => True) dnum T α) := by
    have := uprob_not (fun α : ZMod p => hpTestOut G (fun _ => True) dnum T α)
    have hD : ((#(Eup G (fun _ => True) T) : ℝ) - 1) / p ≤ 1 / 2 := by
      rw [div_le_iff₀ hpp]
      have : (2 : ℝ) * #(Eup G (fun _ => True) T) ≤ p := by exact_mod_cast hp2
      linarith
    linarith
  calc (1 / 16 : ℝ) ≤ 1 / 2 * (3 / 16) := by norm_num
    _ ≤ uprob (fun α : ZMod p => hpTestOut G (fun _ => True) dnum T α) *
        uprob (fun ω => ∃ e ∈ cut G T, step G T num enc (h ω) (Icc 1 ℓ) = some e) :=
        mul_le_mul hpass hstep (by norm_num) (uprob_nonneg _)
    _ = uprob (fun x : ZMod p × Ω => hpTestOut G (fun _ => True) dnum T x.1 ∧
        ∃ e ∈ cut G T, step G T num enc (h x.2) (Icc 1 ℓ) = some e) := (uprob_prod_and _ _).symm
    _ ≤ _ := uprob_mono fun x ⟨hpx, e, he, hse⟩ => ⟨e, he, by simp [findAnyC, hpx, hse]⟩

/-- **Lemma 5, `FindAny`** (with `r = 2^ℓ ≥ 4 ∑ deg`). With `K` independent rounds, if an edge
leaves `T`, `FindAny` fails to return a leaving edge with probability at most
`(D - 1)/p + (1 - 1/16)^K`, where `D = ∑_{y ∈ T} deg y`. -/
theorem lemma5_findAny {p : ℕ} [Fact p.Prime] (dnum : V × V → ℕ)
    (hdinj : Set.InjOn (fun d => (dnum d : ZMod p)) (darts G))
    (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet)
    {h : Ω → U → ℕ} {ℓ : ℕ} (hp : IsPairwiseIndep (2 ^ ℓ) K h)
    (hK : ∀ e ∈ cut G T, num e ∈ K) (hr : 4 * #(Eup G (fun _ => True) T) ≤ 2 ^ ℓ)
    (hcut : (cut G T).Nonempty) (Kr : ℕ) :
    uprob (fun x : ZMod p × (Fin Kr → Ω) =>
      ¬ ∃ e ∈ cut G T, findAny G T num enc dnum x.1 (fun k => h (x.2 k)) (Icc 1 ℓ) = some e) ≤
      ((#(Eup G (fun _ => True) T) : ℝ) - 1) / p + (1 - 1 / 16) ^ Kr := by
  classical
  have hW0 : 0 < #(cut G T) := card_pos.2 hcut
  have hle := card_cut_le_card_Eup (G := G) (T := T)
  have hstep := step_success_prob_paperIdx h2 hinj hp hK hW0 (by omega)
  have hcut' : ∃ e ∈ cut G T, (fun _ => True) e := by
    obtain ⟨e, he⟩ := hcut; exact ⟨e, he, trivial⟩
  have hfail := hpTestOut_fail_prob_le (P := fun _ => True) dnum T hdinj hcut'
  set S : Ω → Prop := fun ω => ∃ e ∈ cut G T, step G T num enc (h ω) (Icc 1 ℓ) = some e
  have hS : uprob (fun ω => ¬ S ω) ≤ 1 - 1 / 16 := by
    rw [uprob_not]; linarith
  -- failure ⊆ (HP-TestOut fails) ∨ (all rounds fail)
  have hsub : ∀ x : ZMod p × (Fin Kr → Ω),
      (¬ ∃ e ∈ cut G T, findAny G T num enc dnum x.1 (fun k => h (x.2 k)) (Icc 1 ℓ) = some e) →
      (¬ hpTestOut G (fun _ => True) dnum T x.1 ∧ True) ∨ (True ∧ ∀ k, ¬ S (x.2 k)) := by
    intro x hx
    by_cases hpx : hpTestOut G (fun _ => True) dnum T x.1
    · right
      refine ⟨trivial, fun k hk => hx ?_⟩
      obtain ⟨e, he, hse⟩ := hk
      have hsome : ((List.ofFn fun k => step G T num enc (h (x.2 k)) (Icc 1 ℓ)).findSome?
          id).isSome := by
        rw [List.findSome?_isSome_iff]
        exact ⟨_, List.mem_ofFn.2 ⟨k, rfl⟩, by simp [hse]⟩
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hsome
      have hres : findAny G T num enc dnum x.1 (fun k => h (x.2 k)) (Icc 1 ℓ) = some e' := by
        simp [findAny, hpx, he']
      exact ⟨e', findAny_sound hinj dnum x.1 _ _ hres, hres⟩
    · left; exact ⟨hpx, trivial⟩
  have hpp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc _ ≤ uprob (fun x : ZMod p × (Fin Kr → Ω) =>
          (¬ hpTestOut G (fun _ => True) dnum T x.1 ∧ True) ∨ (True ∧ ∀ k, ¬ S (x.2 k))) :=
        uprob_mono hsub
    _ ≤ uprob (fun x : ZMod p × (Fin Kr → Ω) => ¬ hpTestOut G (fun _ => True) dnum T x.1 ∧ True)
        + uprob (fun x : ZMod p × (Fin Kr → Ω) => True ∧ ∀ k, ¬ S (x.2 k)) := uprob_or_le _ _
    _ ≤ _ := by
        have e1 := uprob_prod_and (fun α : ZMod p => ¬ hpTestOut G (fun _ => True) dnum T α)
          (fun _ : Fin Kr → Ω => True)
        have e2 := uprob_prod_and (fun _ : ZMod p => True)
          (fun ωs : Fin Kr → Ω => ∀ k, ¬ S (ωs k))
        rw [e1, e2]
        have h1 : uprob (fun _ : Fin Kr → Ω => True) ≤ 1 := uprob_le_one _
        have h1' : uprob (fun _ : ZMod p => True) ≤ 1 := uprob_le_one _
        have hpi : uprob (fun ωs : Fin Kr → Ω => ∀ k, ¬ S (ωs k)) = uprob (fun ω => ¬ S ω) ^ Kr := by
          rw [uprob_pi (α := fun _ : Fin Kr => Ω) (fun _ ω => ¬ S ω), prod_const, card_univ,
            Fintype.card_fin]
        rw [hpi]
        have hA := uprob_nonneg (fun α : ZMod p => ¬ hpTestOut G (fun _ => True) dnum T α)
        have hB : uprob (fun ω => ¬ S ω) ^ Kr ≤ (1 - 1 / 16) ^ Kr :=
          pow_le_pow_left₀ (uprob_nonneg _) hS Kr
        have hB0 : 0 ≤ uprob (fun ω => ¬ S ω) ^ Kr := pow_nonneg (uprob_nonneg _) _
        nlinarith [uprob_nonneg (fun _ : Fin Kr → Ω => True), uprob_nonneg (fun _ : ZMod p => True)]

/-- **Lemma 5, `FindAny`, with the paper's parameters**: `p > D/ε` and `K ≥ 16 ln(1/ε)`
repetitions give failure probability `< 2ε` (the paper: `ε < 1/(2n^c)`, failure `≤ 1/n^c`). -/
theorem lemma5_findAny_whp {p : ℕ} [Fact p.Prime] (dnum : V × V → ℕ)
    (hdinj : Set.InjOn (fun d => (dnum d : ZMod p)) (darts G))
    (hinj : Set.InjOn (fun e => enc (num e)) G.edgeSet)
    {h : Ω → U → ℕ} {ℓ : ℕ} (hp : IsPairwiseIndep (2 ^ ℓ) K h)
    (hK : ∀ e ∈ cut G T, num e ∈ K) (hr : 4 * #(Eup G (fun _ => True) T) ≤ 2 ^ ℓ)
    (hcut : (cut G T).Nonempty) {ε : ℝ} (hε0 : 0 < ε)
    (hε : (#(Eup G (fun _ => True) T) : ℝ) / ε < p) {Kr : ℕ}
    (hKr : 16 * Real.log (1 / ε) ≤ Kr) :
    uprob (fun x : ZMod p × (Fin Kr → Ω) =>
      ¬ ∃ e ∈ cut G T, findAny G T num enc dnum x.1 (fun k => h (x.2 k)) (Icc 1 ℓ) = some e) <
      2 * ε := by
  have h1 := lemma5_findAny h2 dnum hdinj hinj hp hK hr hcut Kr
  have h3 := one_sub_pow_le_of_le_log hε0 hKr
  have hpp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h4 : ((#(Eup G (fun _ => True) T) : ℝ) - 1) / p < ε := by
    rw [div_lt_iff₀ hpp]; rw [div_lt_iff₀ hε0] at hε; nlinarith
  linarith

end Podc.MSTImpromptuRepair
