import Papers.PODC2015.AlgebraicCongestedClique.FourCycle
import Podc.Computability.Distributed.CongestedClique.Routing

/-!
# Theorem 4: 4-cycle detection in `O(1)` rounds (Censor-Hillel et al., PODC 2015)

The algorithm of Section 3.1, as a `Prog` on the congested clique with nodes `Fin n`. Node `v`
starts with its neighbourhood `N(v)`; words are triples of natural numbers `≤ 64 n`
(`O(log n)` bits).

1. every node broadcasts its degree (1 round);
2. every node `x` computes `|P(x,∗,∗)| = ∑_{y ∈ N(x)} deg(y)` and broadcasts whether it is
   `≥ 2n − 1`; if some node does, there is a 4-cycle and all further steps are idle (1 round);
3. (Lemma 12: every node computes the tiles `A(y) × B(y)` from the degrees.) Node `y` sends
   `N_A(y, a)` to every `a ∈ A(y)` (`≤ 8` words per link, 8 rounds);
4. node `a` sends `N_A(y, a)` to every `b ∈ B(y)` for the unique `y` with `(a, b)` in the tile of
   `y` (`≤ 8` words per link, 8 rounds); node `b` now knows `N(y)` for all `y` with `b ∈ B(y)`
   and computes `W(b)`;
5. node `b` sends each walk `(x, y, z) ∈ W(b)` to `x` (Lenzen's routing; every node sends
   `≤ 64 n` walks by Lemma 13 and receives `|P(x,∗,∗)| < 2n` walks; `2 + 128 · 16` rounds by
   `Prog.exists_routedBig`); node `x` now knows `P(x,∗,∗)` and checks whether
   `|P(x,∗,z)| ≥ 2` for some `z ≠ x`;
6. every node broadcasts the result of its check (1 round).
-/

namespace Podc.AlgebraicCongestedClique

open Finset SimpleGraph Cslib.CongestedClique

noncomputable section

/-- Words: triples of natural numbers. -/
abbrev Word := ℕ × ℕ × ℕ

variable {n : ℕ}

/-- Encoding a set of node identifiers. -/
def encIds (s : Finset (Fin n)) : List Word := s.toList.map fun i => (i.val, 0, 0)

/-- Decoding a list of node identifiers. -/
def decIds (l : List Word) : Finset (Fin n) := univ.filter fun i => (i.val, 0, 0) ∈ l

/-- Encoding a set of walks. -/
def encWalks (s : Finset (Fin n × Fin n × Fin n)) : List Word :=
  s.toList.map fun w => (w.1.val, w.2.1.val, w.2.2.val)

/-- Decoding a list of walks. -/
def decWalks (l : List Word) : Finset (Fin n × Fin n × Fin n) :=
  univ.filter fun w => (w.1.val, w.2.1.val, w.2.2.val) ∈ l

lemma decIds_encIds (s : Finset (Fin n)) : decIds (encIds s) = s := by
  ext i; simp [decIds, encIds, Fin.val_inj]

lemma decWalks_encWalks (s : Finset (Fin n × Fin n × Fin n)) : decWalks (encWalks s) = s := by
  ext w
  simp only [decWalks, encWalks, mem_filter, mem_univ, true_and, List.mem_map, mem_toList,
    Prod.mk.injEq]
  constructor
  · rintro ⟨w', hw', h1, h2, h3⟩
    have : w' = w := by
      obtain ⟨a, b, c⟩ := w; obtain ⟨a', b', c'⟩ := w'
      simp only [Prod.mk.injEq]; exact ⟨Fin.ext h1, Fin.ext h2, Fin.ext h3⟩
    exact this ▸ hw'
  · intro hw; exact ⟨w, hw, rfl, rfl, rfl⟩

@[simp] lemma length_encIds (s : Finset (Fin n)) : (encIds s).length = #s := by
  simp [encIds]

@[simp] lemma length_encWalks (s : Finset (Fin n × Fin n × Fin n)) :
    (encWalks s).length = #s := by
  simp [encWalks]

/-- The bound on words. -/
def WordOK (n : ℕ) (w : Word) : Prop := w.1 ≤ 64 * n ∧ w.2.1 ≤ 64 * n ∧ w.2.2 ≤ 64 * n

/-! ### The steps -/

/-- Phase-1 flag of node `x`: `|P(x,∗,∗)| = ∑_{y ∈ N(x)} deg(y) ≥ 2n − 1`. -/
def flag (N : Finset (Fin n)) (d : Fin n → ℕ) : Bool := decide (2 * n - 1 ≤ ∑ y ∈ N, d y)

/-- Step 1: broadcast the degree. -/
def send1 : Fin n → Finset (Fin n) → Fin n → List Word := fun _ N _ => [(#N, 0, 0)]

def recv1 : Fin n → Finset (Fin n) → (Fin n → List Word) → Finset (Fin n) × (Fin n → ℕ) :=
  fun _ N m => (N, fun u => ((m u).head?.map (·.1)).getD 0)

/-- Step 2: broadcast the phase-1 flag. -/
def send2 : Fin n → Finset (Fin n) × (Fin n → ℕ) → Fin n → List Word :=
  fun _ st _ => [(if flag st.1 st.2 then 1 else 0, 0, 0)]

def recv2 : Fin n → Finset (Fin n) × (Fin n → ℕ) → (Fin n → List Word) →
    Finset (Fin n) × (Fin n → ℕ) × Bool :=
  fun _ st m => (st.1, st.2, decide (∃ u, (1, 0, 0) ∈ m u))

/-- Step 3: `y` sends `N_A(y, a)` to `a`. -/
def send3 : Fin n → Finset (Fin n) × (Fin n → ℕ) × Bool → Fin n → List Word :=
  fun y st a => if st.2.2 then [] else encIds (chunk st.1 (tileA n st.2.1 y) a)

def recv3 : Fin n → Finset (Fin n) × (Fin n → ℕ) × Bool → (Fin n → List Word) →
    (Fin n → ℕ) × Bool × (Fin n → Finset (Fin n)) :=
  fun _ st m => (st.2.1, st.2.2, fun y => decIds (m y))

/-- Step 4: `a` forwards `N_A(y, a)` to `b` for the `y` with `(a, b) ∈ A(y) × B(y)`. -/
def send4 : Fin n → (Fin n → ℕ) × Bool × (Fin n → Finset (Fin n)) → Fin n → List Word :=
  fun a st b => if st.2.1 then [] else
    ((univ.filter fun y => a ∈ tileA n st.1 y ∧ b ∈ tileB n st.1 y).toList).flatMap
      fun y => encIds (st.2.2 y)

/-- What `b` knows about `N(y)` after step 4. -/
def knownN (d : Fin n → ℕ) (b : Fin n) (m : Fin n → List Word) (y : Fin n) : Finset (Fin n) :=
  if b ∈ tileB n d y then (tileA n d y).biUnion fun a => decIds (m a) else ∅

/-- `W(b)` as computed by `b` from what it knows. -/
def localW (d : Fin n → ℕ) (b : Fin n) (N : Fin n → Finset (Fin n)) :
    Finset (Fin n × Fin n × Fin n) :=
  univ.filter fun w => w.1 ∈ N w.2.1 ∧ w.2.2 ∈ chunk (N w.2.1) (tileB n d w.2.1) b

def recv4 : Fin n → (Fin n → ℕ) × Bool × (Fin n → Finset (Fin n)) → (Fin n → List Word) →
    Bool × Finset (Fin n × Fin n × Fin n) :=
  fun b st m => (st.2.1, if st.2.1 then ∅ else localW st.1 b (knownN st.1 b m))

/-- Step 5: `b` sends each walk `(x, y, z) ∈ W(b)` to `x` (routed). -/
def send5 : Fin n → Bool × Finset (Fin n × Fin n × Fin n) → Fin n → List Word :=
  fun _ st x => encWalks (st.2.filter fun w => w.1 = x)

/-- The check of node `x` on the set `P` of 2-walks it knows. -/
def check (x : Fin n) (P : Finset (Fin n × Fin n × Fin n)) : Bool :=
  decide (∃ z, x ≠ z ∧ 2 ≤ #(P.filter fun w => w.2.2 = z))

def recv5 : Fin n → Bool × Finset (Fin n × Fin n × Fin n) → (Fin n → List Word) → Bool × Bool :=
  fun x st m => (st.1, check x (univ.biUnion fun b => decWalks (m b)))

/-- Step 6: broadcast the result of the check. -/
def send6 : Fin n → Bool × Bool → Fin n → List Word :=
  fun _ st _ => [(if st.2 then 1 else 0, 0, 0)]

def recv6 : Fin n → Bool × Bool → (Fin n → List Word) → Bool :=
  fun _ st m => st.1 || decide (∃ u, (1, 0, 0) ∈ m u)

/-- The routed step 5, implemented by `Prog.exists_routedBig` with loads `64 n` and `2 n`. -/
def step5 : Prog (Fin n) Word (Bool × Finset (Fin n × Fin n × Fin n)) (Bool × Bool) :=
  Classical.choose (Prog.exists_routedBig 64 2 (fun k => ((k, 0, 0) : Word)) (·.1)
    (fun _ => rfl) (send5 (n := n)) recv5)

lemma step5_spec (s : Fin n → Bool × Finset (Fin n × Fin n × Fin n))
    (h1 : ∀ u, ∑ v, (send5 u (s u) v).length ≤ 64 * n)
    (h2 : ∀ v, ∑ u, (send5 u (s u) v).length ≤ 2 * n) :
    step5.run s = Prog.next send5 recv5 s ∧ step5.rounds s ≤ 2 + 64 * 2 * lenzenRounds ∧
      ∀ ok : Word → Prop, (∀ u v, ∀ w ∈ send5 u (s u) v, ok w) →
        (∀ k ≤ max 64 2 * n, ok (k, 0, 0)) → step5.Valid ok s := by
  have := Classical.choose_spec (Prog.exists_routedBig 64 2 (fun k => ((k, 0, 0) : Word)) (·.1)
    (fun _ => rfl) (send5 (n := n)) recv5) s
  obtain ⟨a, b, c⟩ := this (by simpa using h1) (by simpa using h2)
  exact ⟨a, b, fun ok h h' => c ok h (by simpa using h')⟩

/-- The 4-cycle detection algorithm. -/
def fourCycleProg (n : ℕ) : Prog (Fin n) Word (Finset (Fin n)) Bool :=
  .step .direct send1 recv1 <| .step .direct send2 recv2 <| .step .direct send3 recv3 <|
  .step .direct send4 recv4 <| step5.append <| .step .direct send6 recv6 <| .done Bool

/-! ### The run -/

lemma decIds_nil : decIds ([] : List Word) = (∅ : Finset (Fin n)) := by simp [decIds]

lemma decWalks_nil : decWalks ([] : List Word) = (∅ : Finset (Fin n × Fin n × Fin n)) := by
  simp [decWalks]

lemma decIds_flatMap {α : Type} (L : List α) (f : α → List Word) [DecidableEq α] :
    decIds (n := n) (L.flatMap f) = L.toFinset.biUnion fun y => decIds (f y) := by
  ext i; simp [decIds, List.mem_flatMap]

lemma mem_encIds {s : Finset (Fin n)} {w : Word} (h : w ∈ encIds s) :
    ∃ i ∈ s, w = (i.val, 0, 0) := by
  simp only [encIds, List.mem_map, mem_toList] at h
  obtain ⟨i, hi, rfl⟩ := h; exact ⟨i, hi, rfl⟩

lemma mem_encWalks {s : Finset (Fin n × Fin n × Fin n)} {w : Word} (h : w ∈ encWalks s) :
    ∃ v ∈ s, w = (v.1.val, v.2.1.val, v.2.2.val) := by
  simp only [encWalks, List.mem_map, mem_toList] at h
  obtain ⟨i, hi, rfl⟩ := h; exact ⟨i, hi, rfl⟩

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Whether some node stops in phase 1. -/
def stopG : Bool := decide (∃ u, flag (G.neighborFinset u) (degs G) = true)

lemma run1 : Prog.next send1 recv1 (fun v => G.neighborFinset v) =
    fun v => (G.neighborFinset v, degs G) := by
  funext v; simp [Prog.next, send1, recv1]; rfl

lemma run2 : Prog.next send2 recv2 (fun v => (G.neighborFinset v, degs G)) =
    fun v => (G.neighborFinset v, degs G, stopG G) := by
  funext v
  simp only [Prog.next, send2, recv2, stopG, List.mem_singleton, Prod.mk.injEq, and_true]
  refine ⟨trivial, trivial, ?_⟩
  simp only [decide_eq_decide]
  apply exists_congr; intro u
  split_ifs <;> simp_all

lemma run3 : Prog.next send3 recv3 (fun v => (G.neighborFinset v, degs G, stopG G)) =
    fun a => (degs G, stopG G, fun y =>
      if stopG G then ∅ else chunk (G.neighborFinset y) (tileA n (degs G) y) a) := by
  funext a
  simp only [Prog.next, send3, recv3]
  congr 2; funext y
  split_ifs <;> simp [decIds_nil, decIds_encIds]

lemma phase2_of_not_stop (hpos : 0 < n) (h : stopG G = false) : Phase2 G := by
  refine sum_degree_sq_lt G hpos fun x => ?_
  simp only [stopG, decide_eq_false_iff_not, not_exists, flag, decide_eq_true_eq, not_le] at h
  rw [card_walksFrom_eq_sum_degree]; exact h x

lemma tile_unique (hG : Phase2 G) {a b y y' : Fin n}
    (h : a ∈ tileA n (degs G) y ∧ b ∈ tileB n (degs G) y)
    (h' : a ∈ tileA n (degs G) y' ∧ b ∈ tileB n (degs G) y') : y = y' := by
  by_contra hne
  have : Disjoint (tileA n (degs G) y ×ˢ tileB n (degs G) y)
      (tileA n (degs G) y' ×ˢ tileB n (degs G) y') := tiles_disjoint (degs_lt G) hG hne
  rw [Finset.disjoint_left] at this
  exact this (a := (a, b)) (mem_product.2 h) (mem_product.2 h')

/-- The messages received by `b` in step 4 (when nobody stopped). -/
def msg4 (b a : Fin n) : List Word :=
  ((univ.filter fun y' => a ∈ tileA n (degs G) y' ∧ b ∈ tileB n (degs G) y').toList).flatMap
    fun y' => encIds (chunk (G.neighborFinset y') (tileA n (degs G) y') a)

lemma knownN_eq (hG : Phase2 G) (b y : Fin n) :
    knownN (degs G) b (msg4 G b) y =
      if b ∈ tileB n (degs G) y then G.neighborFinset y else ∅ := by
  unfold knownN
  split_ifs with hb
  · ext x
    simp only [mem_biUnion, msg4, decIds_flatMap, List.mem_toFinset, mem_toList, decIds_encIds,
      mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, y', ⟨ha', hb'⟩, hx⟩
      obtain rfl := tile_unique G hG ⟨ha', hb'⟩ ⟨ha, hb⟩
      exact chunk_subset _ _ _ hx
    · intro hx
      obtain ⟨a, ha, hxa⟩ := exists_mem_chunk (T := tileA n (degs G) y)
        (by rw [card_neighborFinset_eq_degree]; exact degree_le_eight_mul_tileA G hG y) hx
      exact ⟨a, ha, y, ⟨ha, hb⟩, hxa⟩
  · rfl

lemma localW_eq (hG : Phase2 G) (b : Fin n) :
    localW (degs G) b (knownN (degs G) b (msg4 G b)) = Wset G b := by
  ext w
  simp only [localW, Wset, walks2, mem_filter, mem_univ, true_and, knownN_eq G hG]
  by_cases hb : b ∈ tileB n (degs G) w.2.1
  · simp only [hb, ite_true, mem_neighborFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.symm, by simpa using chunk_subset _ _ _ h2⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1.symm, h2⟩
  · simp [hb, chunk]

lemma run4 :
    Prog.next send4 recv4 (fun a => (degs G, stopG G, fun y =>
      if stopG G then ∅ else chunk (G.neighborFinset y) (tileA n (degs G) y) a)) =
    fun b => (stopG G, if stopG G then ∅ else Wset G b) := by
  funext b
  have hpos := b.pos
  simp only [Prog.next, send4, recv4]
  cases hs : stopG G
  · simp only [Bool.false_eq_true, ite_false]
    rw [← localW_eq G (phase2_of_not_stop G hpos hs) b]
    rfl
  · simp

/-- The state after step 4. -/
def S4 (b : Fin n) : Bool × Finset (Fin n × Fin n × Fin n) :=
  (stopG G, if stopG G then ∅ else Wset G b)

lemma biUnion_Wset (hG : Phase2 G) (x : Fin n) :
    univ.biUnion (fun b => (Wset G b).filter fun w => w.1 = x) = walksFrom G x := by
  obtain ⟨h1, h2, -⟩ := lemma_13 G hG
  ext w
  simp only [mem_biUnion, mem_univ, true_and, mem_filter, walksFrom]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨h2 b hb, rfl⟩
  · rintro ⟨hw, rfl⟩; obtain ⟨b, hb, -⟩ := h1 w hw; exact ⟨b, hb, rfl⟩

lemma sum_card_Wset_filter (hG : Phase2 G) (x : Fin n) :
    ∑ b, #((Wset G b).filter fun w => w.1 = x) = #(walksFrom G x) := by
  rw [← biUnion_Wset G hG x, card_biUnion]
  intro b _ b' _ hne
  obtain ⟨h1, -, -⟩ := lemma_13 G hG
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [mem_filter] at hw hw'
  obtain ⟨b0, -, hu⟩ := h1 w (mem_filter.1 hw.1).1
  exact hne ((hu b hw.1).trans (hu b' hw'.1).symm)

lemma load5_send (u : Fin n) :
    ∑ v, (send5 u (S4 G u) v).length ≤ 64 * n := by
  have hpos := u.pos
  simp only [send5, length_encWalks, S4]
  rw [← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)]
  split_ifs with hs
  · simp
  · exact (lemma_13 G (phase2_of_not_stop G hpos (by simpa using hs))).2.2 u

lemma load5_recv (v : Fin n) :
    ∑ u, (send5 u (S4 G u) v).length ≤ 2 * n := by
  have hpos := v.pos
  simp only [send5, length_encWalks, S4]
  split_ifs with hs
  · simp
  · have hs' : stopG G = false := by simpa using hs
    rw [sum_card_Wset_filter G (phase2_of_not_stop G hpos hs')]
    simp only [stopG, decide_eq_false_iff_not, not_exists, flag, decide_eq_true_eq,
      not_le] at hs'
    have := hs' v
    have h2 : #(walksFrom G v) = ∑ y ∈ G.neighborFinset v, degs G y :=
      card_walksFrom_eq_sum_degree G v
    omega

lemma run5 : Prog.next send5 recv5 (S4 G) =
    fun x => (stopG G, check x (if stopG G then ∅ else walksFrom G x)) := by
  funext x
  have hpos := x.pos
  simp only [Prog.next, send5, recv5, decWalks_encWalks, S4]
  split_ifs with hs
  · simp only [filter_empty, Prod.mk.injEq, true_and]
    congr 1; ext w; simp
  · rw [biUnion_Wset G (phase2_of_not_stop G hpos (by simpa using hs))]

lemma card_walksFrom_filter (x z : Fin n) :
    #((walksFrom G x).filter fun w => w.2.2 = z) = #(commonNbrs G x z) := by
  refine card_bij (fun w _ => w.2.1) ?_ ?_ ?_
  · intro w hw
    simp only [walksFrom, walks2, mem_filter, mem_univ, true_and] at hw
    obtain ⟨⟨⟨h1, h2⟩, rfl⟩, rfl⟩ := hw
    simp [commonNbrs, h1, h2]
  · rintro ⟨a, b, c⟩ hw ⟨a', b', c'⟩ hw' h
    simp only [walksFrom, walks2, mem_filter, mem_univ, true_and] at hw hw'
    obtain ⟨⟨-, rfl⟩, rfl⟩ := hw
    obtain ⟨⟨-, rfl⟩, rfl⟩ := hw'
    simp only at h; subst h; rfl
  · intro y hy
    simp only [commonNbrs, mem_filter, mem_univ, true_and] at hy
    exact ⟨(x, y, z), by simp [walksFrom, walks2, hy], rfl⟩

lemma check_walksFrom (x : Fin n) :
    check x (walksFrom G x) = true ↔ ∃ z, x ≠ z ∧ 2 ≤ #(commonNbrs G x z) := by
  simp [check, card_walksFrom_filter]

/-- The state after step 3. -/
def S3 (a : Fin n) : (Fin n → ℕ) × Bool × (Fin n → Finset (Fin n)) :=
  (degs G, stopG G, fun y =>
      if stopG G then ∅ else chunk (G.neighborFinset y) (tileA n (degs G) y) a)

lemma length_send4_le (a b : Fin n) : (send4 a (S3 G a) b).length ≤ 8 := by
  have hpos := a.pos
  simp only [send4, S3]
  split_ifs with hs
  · simp
  · have hG := phase2_of_not_stop G hpos (by simpa using hs)
    rw [List.length_flatMap]
    refine le_trans (List.sum_le_length_nsmul _ 8 ?_) ?_
    · intro k hk
      simp only [List.mem_map, mem_toList] at hk
      obtain ⟨y, -, rfl⟩ := hk
      simp only [length_encIds]
      exact card_chunk_le _ _ _
    · simp only [List.length_map, length_toList, smul_eq_mul]
      refine le_trans (Nat.mul_le_mul_right 8 (?_ : _ ≤ 1)) (by norm_num)
      rw [card_le_one]
      intro y hy y' hy'
      exact tile_unique G hG (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hy').2

lemma width_le_one {σ : Type} (f : Fin n → σ → Fin n → Word)
    (s : Fin n → σ) : Prog.width (fun u x v => [f u x v]) s ≤ 1 :=
  (Prog.width_le_iff _ _ _).2 fun _ _ => by simp

lemma rounds_fourCycleProg :
    (fourCycleProg n).rounds (fun v => G.neighborFinset v) ≤ 2069 := by
  have h5 := (step5_spec (S4 G) (load5_send G) (load5_recv G)).2.1
  simp only [fourCycleProg, Prog.rounds_step_direct, run1, run2, run3, run4, Prog.rounds_append]
  have w1 := width_le_one (fun _ (N : Finset (Fin n)) _ => ((#N, 0, 0) : Word))
    (fun v => G.neighborFinset v)
  have w2 := width_le_one (fun _ (st : Finset (Fin n) × (Fin n → ℕ)) _ =>
    ((if flag st.1 st.2 then 1 else 0, 0, 0) : Word)) (fun v => (G.neighborFinset v, degs G))
  have w3 : Prog.width send3 (fun v => (G.neighborFinset v, degs G, stopG G)) ≤ 8 :=
    (Prog.width_le_iff _ _ _).2 fun y a => by
      simp only [send3]; split_ifs
      · simp
      · rw [length_encIds]; exact card_chunk_le _ _ _
  have w4 : Prog.width send4 (S3 G) ≤ 8 :=
    (Prog.width_le_iff _ _ _).2 fun a b => length_send4_le G a b
  have w6 := width_le_one (fun _ (st : Bool × Bool) _ => ((if st.2 then 1 else 0, 0, 0) : Word))
    (step5.run (S4 G))
  simp only [lenzenRounds] at h5
  change Prog.width (fun u x v => [((#x, 0, 0) : Word)]) _ +
    (Prog.width (fun u (x : Finset (Fin n) × (Fin n → ℕ)) v =>
      [((if flag x.1 x.2 then 1 else 0, 0, 0) : Word)]) _ +
    (Prog.width send3 _ + (Prog.width send4 (S3 G) + (step5.rounds (S4 G) +
      (Prog.width (fun u (x : Bool × Bool) v => [((if x.2 then 1 else 0, 0, 0) : Word)])
        (step5.run (S4 G)) + 0))))) ≤ 2069
  omega

lemma wordOK_id {i : Fin n} : WordOK n (i.val, 0, 0) := by
  refine ⟨?_, by simp, by simp⟩; have := i.isLt; omega

lemma wordOK_bit (k : ℕ) (hk : k ≤ 1) {i : Fin n} : WordOK n ((k, 0, 0) : Word) := by
  refine ⟨?_, by simp, by simp⟩; have := i.isLt; simp only; omega

lemma valid_fourCycleProg :
    (fourCycleProg n).Valid (WordOK n) (fun v => G.neighborFinset v) := by
  have h5 := (step5_spec (S4 G) (load5_send G) (load5_recv G)).2.2
  simp only [fourCycleProg, Prog.Valid, run1, run2, run3, run4, Prog.valid_append, reduceCtorEq,
    IsEmpty.forall_iff, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v w hw
    simp only [send1, List.mem_singleton] at hw; subst hw
    refine ⟨?_, by simp, by simp⟩
    have := card_le_univ (G.neighborFinset u); simp only [Fintype.card_fin] at this; simp only; omega
  · intro u v w hw
    simp only [send2, List.mem_singleton] at hw; subst hw
    exact wordOK_bit _ (by split_ifs <;> simp) (i := u)
  · intro y a w hw
    simp only [send3] at hw
    split_ifs at hw
    · simp at hw
    · obtain ⟨i, -, rfl⟩ := mem_encIds hw; exact wordOK_id
  · intro a b w hw
    simp only [send4] at hw
    split_ifs at hw
    · simp at hw
    · simp only [List.mem_flatMap] at hw
      obtain ⟨y, -, hw⟩ := hw
      obtain ⟨i, -, rfl⟩ := mem_encIds hw; exact wordOK_id
  · refine h5 _ (fun u v w hw => ?_) (fun k hk => ⟨by simpa using hk, by simp, by simp⟩)
    obtain ⟨⟨x, y, z⟩, -, rfl⟩ := mem_encWalks hw
    exact ⟨by have := x.isLt; simp only; omega, by have := y.isLt; simp only; omega,
      by have := z.isLt; simp only; omega⟩
  · refine ⟨fun u v w hw => ?_, trivial⟩
    simp only [send6, List.mem_singleton] at hw; subst hw
    exact wordOK_bit _ (by split_ifs <;> simp) (i := u)

lemma run_fourCycleProg :
    (fourCycleProg n).run (fun v => G.neighborFinset v) = fun _ =>
      stopG G || decide (∃ u, check u (if stopG G then ∅ else walksFrom G u) = true) := by
  have h5 := (step5_spec (S4 G) (load5_send G) (load5_recv G)).1
  simp only [fourCycleProg, Prog.run_step, run1, run2, run3, run4, Prog.run_append]
  change (Prog.done Bool).run (Prog.next send6 recv6 (step5.run (S4 G))) = _
  rw [h5, run5]
  funext v
  simp only [Prog.run_done, Prog.next, send6, recv6, List.mem_singleton, Prod.mk.injEq, and_true]
  congr 2
  apply propext; apply exists_congr; intro u
  split_ifs <;> simp_all

/-- Theorem 4 of [Censor-Hillel, Kaski, Korhonen, Lenzen, Paz, Suomela, PODC 2015]: the
existence of 4-cycles can be detected in `O(1)` rounds on the congested clique. Here: a
deterministic algorithm in which every node starts with its neighbourhood and ends knowing whether
the graph has a 4-cycle, within `2069` rounds (a routed step counting `lenzenRounds = 16`
rounds), with words of three numbers `≤ 64 n` (`O(log n)` bits). -/
theorem theorem_4 (n : ℕ) : ∃ P : Prog (Fin n) Word (Finset (Fin n)) Bool,
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, P.run (fun u => G.neighborFinset u) v = true ↔ HasFourCycle G) ∧
      P.rounds (fun u => G.neighborFinset u) ≤ 2069 ∧
      P.Valid (WordOK n) (fun u => G.neighborFinset u) := by
  refine ⟨fourCycleProg n, fun G _ => ⟨fun v => ?_, ?_, ?_⟩⟩
  · rw [run_fourCycleProg]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    cases hs : stopG G
    · simp only [Bool.false_eq_true, ite_false, false_or, check_walksFrom, hasFourCycle_iff]
    · simp only [true_or, true_iff]
      simp only [stopG, flag, decide_eq_true_eq] at hs
      obtain ⟨u, hu⟩ := hs
      rw [hasFourCycle_iff]
      obtain ⟨z, hz⟩ := exists_of_card_walksFrom G (x := u)
        (by rw [card_walksFrom_eq_sum_degree]; exact hu)
      exact ⟨u, z, hz⟩
  · exact rounds_fourCycleProg G
  · exact valid_fourCycleProg G

end

end Podc.AlgebraicCongestedClique
