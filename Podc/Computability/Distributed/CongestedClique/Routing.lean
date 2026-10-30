import Podc.Computability.Distributed.CongestedClique.Phases

-- CSLib candidate: Cslib/Computability/Distributed/CongestedClique/Routing.lean

/-!
# Routing `O(n)` words per node with Lenzen's algorithm

Lenzen's routing algorithm (a routed step of `Prog`) requires every node to send and to receive at
most `n = |V|` words. Papers on the congested clique routinely use it for instances in which every
node sends at most `a·n` and receives at most `b·n` words, for constants `a, b`, and claim `O(1)`
rounds. `Prog.exists_routedBig` makes this precise: such a step (with arbitrary, state-dependent
lists) can be executed in `2 + a·b·lenzenRounds` rounds, with the same result.

The reduction is deterministic and needs no global knowledge:

1. every node `u` tells every node `v` how many words it has for `v` (1 round);
2. every node `v` computes the offset of each sender in its own receive order
   (`∑_{u' < u} c(u', v)`) and sends it back to `u` (1 round);
3. node `u` numbers its outgoing words consecutively (destination by destination); a word gets
   the *sender class* `⌊(sender index)/n⌋ < a` and the *receiver class*
   `⌊(receiver index)/n⌋ < b`; the `a·b` classes are routed one after the other by Lenzen's
   algorithm, each with loads at most `n`;
4. the receiver concatenates the pieces of each sender in class order, which restores the
   original lists, since both class indices are monotone along a list (`flatMap_sel`).

Counts and offsets are sent as words via an encoding `enc : ℕ → W` with a left inverse `dec`.
-/

namespace Cslib.CongestedClique

open Finset

section ListLemmas

/-- Filtering by a disjunction `p ∨ q` is filtering by `p` and then by `q` if no `q`-element
precedes a `p`-element. -/
lemma List.filter_or_eq_append {β : Type*} (l : List β) (p q : β → Bool)
    (h : l.Pairwise (fun x y => q x → ¬ p y)) (hpq : ∀ x, ¬ (p x ∧ q x)) :
    l.filter (fun x => p x || q x) = l.filter p ++ l.filter q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.pairwise_cons] at h
    have ih := ih h.2
    by_cases hp : p x
    · have hq : q x = false := by simpa [hp] using hpq x
      simp [hp, hq, ih]
    · by_cases hq : q x
      · have : l.filter p = [] := by
          rw [List.filter_eq_nil_iff]; intro y hy; simpa using h.1 y hy hq
        have h2 : l.filter (fun x => p x || q x) = l.filter q := by rw [ih, this]; simp
        simp [hp, hq, h2, this]
      · simp [hp, hq, ih]

/-- The sub-list of `L` at the indices `i` with `k i = c`. -/
def sel {α : Type*} (L : List α) (k : ℕ → ℕ) (c : ℕ) : List α :=
  ((List.finRange L.length).filter (fun i => k i.val = c)).map L.get

lemma sel_sublist {α : Type*} (L : List α) (k : ℕ → ℕ) (c : ℕ) {x : α} (hx : x ∈ sel L k c) :
    x ∈ L := by
  simp only [sel, List.mem_map, List.mem_filter] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact List.get_mem L i

lemma length_filter_finRange {m : ℕ} (p : Fin m → Bool) :
    ((List.finRange m).filter p).length = #(univ.filter (fun i => p i)) := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
  congr 1
  ext i; simp

lemma length_sel {α : Type*} (L : List α) (k : ℕ → ℕ) (c : ℕ) :
    (sel L k c).length = #((range L.length).filter (fun i => k i = c)) := by
  rw [sel, List.length_map, length_filter_finRange]
  refine card_bij (fun i _ => i.val) (by simp) (fun _ _ _ _ h => Fin.ext h) ?_
  intro j hj
  simp only [mem_filter, mem_range] at hj
  exact ⟨⟨j, hj.1⟩, by simpa using hj.2, rfl⟩

/-- Reassembly: if the class `k` is monotone along the indices of `L` and below `N`, then
concatenating the classes `0, …, N-1` restores `L`. -/
lemma flatMap_sel {α : Type*} (L : List α) (k : ℕ → ℕ) (hk : Monotone k) (N : ℕ)
    (hN : ∀ i < L.length, k i < N) :
    (List.range N).flatMap (sel L k) = L := by
  have key : ∀ M, (List.range M).flatMap
      (fun c => (List.finRange L.length).filter (fun i => k i.val = c)) =
      (List.finRange L.length).filter (fun i => decide (k i.val < M)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton]
      rw [← List.filter_or_eq_append]
      · congr 1; funext i; rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
      · refine (List.pairwise_lt_finRange _).imp ?_
        intro x y hxy hx
        simp only [decide_eq_true_eq] at hx ⊢
        have := hk (Fin.le_iff_val_le_val.1 hxy.le)
        omega
      · intro x; simp only [decide_eq_true_eq]; omega
  have h1 : (List.range N).flatMap (sel L k) =
      ((List.range N).flatMap
        (fun c => (List.finRange L.length).filter (fun i => k i.val = c))).map L.get := by
    rw [List.map_flatMap]; rfl
  rw [h1, key, List.filter_eq_self.2 (fun i _ => by simpa using hN i i.isLt), ← List.ofFn_eq_map,
    List.ofFn_get]

end ListLemmas

section Offsets

variable {V : Type} [Fintype V] [LinearOrder V]

/-- `before c v = ∑_{v' < v} c v'`: the offset of `v` when the blocks `c v'` are laid out in
the order of `V`. -/
def before (c : V → ℕ) (v : V) : ℕ := ∑ v' ∈ univ.filter (· < v), c v'

lemma before_add_le_sum (c : V → ℕ) (v : V) : before c v + c v ≤ ∑ x, c x := by
  rw [before, add_comm, ← sum_insert (by simp)]
  exact sum_le_sum_of_subset (subset_univ _)

lemma before_add_le_before (c : V → ℕ) {v v' : V} (h : v < v') :
    before c v + c v ≤ before c v' := by
  rw [before, before, add_comm, ← sum_insert (by simp)]
  refine sum_le_sum_of_subset ?_
  intro x hx
  simp only [mem_insert, mem_filter, mem_univ, true_and] at hx ⊢
  rcases hx with rfl | hx
  · exact h
  · exact hx.trans h

/-- The blocks `[before c v, before c v + c v)` are disjoint, so the number of positions of all
blocks that fall into a set `I` is at most `|I|`. -/
lemma sum_card_filter_before_le (c : V → ℕ) (I : Finset ℕ) :
    ∑ v, #((range (c v)).filter (fun p => before c v + p ∈ I)) ≤ #I := by
  classical
  have hcard : ∀ v, #((range (c v)).filter (fun p => before c v + p ∈ I)) =
      #(((range (c v)).filter (fun p => before c v + p ∈ I)).image (before c v + ·)) :=
    fun v => (card_image_of_injective _ (add_right_injective _)).symm
  simp_rw [hcard]
  rw [← card_biUnion]
  · refine card_le_card ?_
    intro x hx
    simp only [mem_biUnion, mem_image, mem_filter] at hx
    obtain ⟨v, -, p, ⟨-, hp⟩, rfl⟩ := hx
    exact hp
  · intro v _ v' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_image, mem_filter, mem_range] at hx hx'
    obtain ⟨p, ⟨hp, -⟩, rfl⟩ := hx
    obtain ⟨p', ⟨hp', -⟩, he⟩ := hx'
    rcases lt_or_gt_of_ne hne with h | h
    · have := before_add_le_before c h; omega
    · have := before_add_le_before c h; omega

end Offsets

namespace Prog

variable {V W : Type}

/-- Run the steps `(send c, recv c)` for `c` in the list `cs`, in order, all in mode `m`. -/
def loop {σ κ : Type} (m : Mode) (send : κ → V → σ → V → List W)
    (recv : κ → V → σ → (V → List W) → σ) : List κ → Prog V W σ σ
  | [] => done σ
  | c :: cs => step m (send c) (recv c) (loop m send recv cs)

lemma rounds_loop_routed [Fintype V] {σ κ : Type} (send : κ → V → σ → V → List W)
    (recv : κ → V → σ → (V → List W) → σ) (cs : List κ) (s : V → σ) :
    (loop .routed send recv cs).rounds s = cs.length * lenzenRounds := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [loop, rounds_step_routed, ih, List.length_cons]; ring

section Big

variable [Fintype V] [LinearOrder V] {σ τ : Type}

/-- The class of position `p` of the list from `u` to `v`: sender class times `b` plus receiver
class, where `off` is the sender-side offset of the list and `rin` its receiver-side offset. -/
def bkey (n b off rin : ℕ) (p : ℕ) : ℕ := ((off + p) / n) * b + (rin + p) / n

lemma bkey_mono (n b off rin : ℕ) : Monotone (bkey n b off rin) := by
  intro p p' h
  unfold bkey
  have h1 : (off + p) / n ≤ (off + p') / n := Nat.div_le_div_right (by omega)
  have h2 : (rin + p) / n ≤ (rin + p') / n := Nat.div_le_div_right (by omega)
  have := Nat.mul_le_mul_right b h1
  omega

lemma bkey_eq {n b off rin k i : ℕ} (ht : (rin + i) / n < b) (h : bkey n b off rin i = k) :
    (off + i) / n = k / b ∧ (rin + i) / n = k % b := by
  subst h
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) ht
  unfold bkey
  rw [mul_comm, Nat.mul_add_div hb, Nat.mul_add_mod, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht]
  simp

lemma bkey_lt {n a b off rin i : ℕ} (hs : (off + i) / n < a) (ht : (rin + i) / n < b) :
    bkey n b off rin i < a * b := by
  unfold bkey
  have : ((off + i) / n + 1) * b ≤ a * b := Nat.mul_le_mul_right b hs
  rw [Nat.add_one_mul] at this
  omega

lemma mem_Ico_of_div_eq {x n m : ℕ} (hn : 0 < n) (h : x / n = m) : x ∈ Finset.Ico (m * n) (m * n + n) := by
  subst h
  simp only [Finset.mem_Ico]
  exact ⟨Nat.div_mul_le_self x n, Nat.lt_div_mul_add hn⟩

/-- Decoding the first word of a list (`0` if empty). -/
def decHead (dec : W → ℕ) (l : List W) : ℕ := (l.head?.map dec).getD 0

/-- State during the bulk phase: own state, receiver-side offsets of the own lists, and the
pieces received so far from each sender. -/
abbrev BigSt (V W σ : Type) := σ × (V → ℕ) × (V → List (List W))

/-- Step 1 of `bigProg`: send the counts. -/
def bigSend1 (enc : ℕ → W) (send : V → σ → V → List W) : V → σ → V → List W :=
  fun u x v => [enc (send u x v).length]

def bigRecv1 (dec : W → ℕ) : V → σ → (V → List W) → σ × (V → ℕ) :=
  fun _ x m => (x, fun u => decHead dec (m u))

/-- Step 2 of `bigProg`: send back the receiver-side offsets. -/
def bigSend2 (enc : ℕ → W) : V → σ × (V → ℕ) → V → List W :=
  fun _ y w => [enc (before y.2 w)]

def bigRecv2 (dec : W → ℕ) : V → σ × (V → ℕ) → (V → List W) → BigSt V W σ :=
  fun _ y m => (y.1, fun v => decHead dec (m v), fun _ => [])

/-- Bulk step `c` of `bigProg`: route the words of class `c`. -/
def bigSendC (b : ℕ) (send : V → σ → V → List W) (c : ℕ) : V → BigSt V W σ → V → List W :=
  fun u z v => sel (send u z.1 v)
    (bkey (Fintype.card V) b (before (fun v' => (send u z.1 v').length) v) (z.2.1 v)) c

def bigRecvC (_c : ℕ) : V → BigSt V W σ → (V → List W) → BigSt V W σ :=
  fun _ z m => (z.1, z.2.1, fun u => z.2.2 u ++ [m u])

/-- The program of `exists_routedBig`. -/
def bigProg (a b : ℕ) (enc : ℕ → W) (dec : W → ℕ) (send : V → σ → V → List W)
    (recv : V → σ → (V → List W) → τ) : Prog V W σ τ :=
  step .direct (bigSend1 enc send) (bigRecv1 dec) <|
  step .direct (bigSend2 enc) (bigRecv2 dec) <|
  (loop .routed (bigSendC b send) bigRecvC (List.range (a * b))).append <|
  compute fun v z => recv v z.1 (fun u => (z.2.2 u).flatten)

lemma run_loop_bigC (b : ℕ) (send : V → σ → V → List W) (cs : List ℕ) (s : V → BigSt V W σ) :
    (loop .routed (bigSendC b send) bigRecvC cs).run s = fun v =>
      ((s v).1, (s v).2.1, fun u => (s v).2.2 u ++ cs.map fun c => bigSendC b send c u (s u) v) := by
  induction cs generalizing s with
  | nil => simp [loop]
  | cons c cs ih =>
    simp only [loop, run_step, ih]
    funext v
    simp [next, bigRecvC, bigSendC]

lemma valid_loop_bigC (b : ℕ) (send : V → σ → V → List W) (ok : W → Prop) (cs : List ℕ)
    (s : V → BigSt V W σ)
    (h : ∀ c ∈ cs, ∀ s' : V → BigSt V W σ, (∀ v, (s' v).1 = (s v).1 ∧ (s' v).2.1 = (s v).2.1) →
      (∀ u v, ∀ w ∈ bigSendC b send c u (s' u) v, ok w) ∧ LoadOK (bigSendC b send c) s') :
    (loop .routed (bigSendC b send) bigRecvC cs).Valid ok s := by
  induction cs generalizing s with
  | nil => trivial
  | cons c cs ih =>
    refine ⟨(h c (by simp) s fun _ => ⟨rfl, rfl⟩).1, fun _ => (h c (by simp) s fun _ => ⟨rfl, rfl⟩).2,
      ih _ ?_⟩
    intro c' hc' s' hs'
    exact h c' (by simp [hc']) s' (fun v => by simpa [next, bigRecvC] using hs' v)

/-- Routing `O(n)` words per node: a step in which every node sends at most `a·|V|` and receives
at most `b·|V|` words (in arbitrary, state-dependent lists) can be executed in
`2 + a·b·lenzenRounds` rounds, using Lenzen's routing for the bulk and two direct rounds of
counts and offsets (sent as words `enc k`, `k ≤ max a b · |V|`). -/
theorem exists_routedBig (a b : ℕ) (enc : ℕ → W) (dec : W → ℕ) (hdec : ∀ k, dec (enc k) = k)
    (send : V → σ → V → List W) (recv : V → σ → (V → List W) → τ) :
    ∃ Q : Prog V W σ τ, ∀ s : V → σ,
      (∀ u, ∑ v, (send u (s u) v).length ≤ a * Fintype.card V) →
      (∀ v, ∑ u, (send u (s u) v).length ≤ b * Fintype.card V) →
      Q.run s = next send recv s ∧ Q.rounds s ≤ 2 + a * b * lenzenRounds ∧
      ∀ ok : W → Prop, (∀ u v, ∀ w ∈ send u (s u) v, ok w) →
        (∀ k ≤ max a b * Fintype.card V, ok (enc k)) → Q.Valid ok s := by
  classical
  refine ⟨bigProg a b enc dec send recv, fun s hsa hrb => ?_⟩
  set n := Fintype.card V with hn
  -- counts and offsets
  set c : V → V → ℕ := fun u v => (send u (s u) v).length with hc
  have hdh : ∀ k, decHead dec [enc k] = k := fun k => by simp [decHead, hdec]
  have h1 : next (bigSend1 enc send) (bigRecv1 dec) s = fun v => (s v, fun u => c u v) := by
    funext v; simp [next, bigSend1, bigRecv1, hdh, c]
  have h2 : next (bigSend2 enc) (bigRecv2 dec) (fun v => (s v, fun u => c u v)) =
      fun u => (s u, (fun v => before (fun u' => c u' v) u), fun _ => []) := by
    funext u; simp [next, bigSend2, bigRecv2, hdh]
  set rin : V → V → ℕ := fun u v => before (fun u' => c u' v) u with hrin
  -- bounds on the classes
  have hS : ∀ u v i, i < c u v → before (c u) v + i < a * n := fun u v i hi =>
    lt_of_lt_of_le (b := ∑ x, c u x) (by have := before_add_le_sum (c u) v; omega) (hsa u)
  have hR : ∀ u v i, i < c u v → rin u v + i < b * n := fun u v i hi =>
    lt_of_lt_of_le (b := ∑ x, c x v)
      (by have := before_add_le_sum (fun u' => c u' v) u; simp only [hrin]; omega) (hrb v)
  have hn0 : ∀ u v i, i < c u v → 0 < n := fun u v i hi => by
    have := hS u v i hi; rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at this; simp at this
    · exact h
  have hS' : ∀ u v i, i < c u v → (before (c u) v + i) / n < a := fun u v i hi =>
    (Nat.div_lt_iff_lt_mul (hn0 u v i hi)).2 (hS u v i hi)
  have hR' : ∀ u v i, i < c u v → (rin u v + i) / n < b := fun u v i hi =>
    (Nat.div_lt_iff_lt_mul (hn0 u v i hi)).2 (hR u v i hi)
  have hloop := run_loop_bigC b send (List.range (a * b))
    (fun u => (s u, (fun v => before (fun u' => c u' v) u), fun _ => []))
  refine ⟨?_, ?_, ?_⟩
  · -- the run
    simp only [bigProg, run_step, h1, h2, run_append, hloop, run_compute]
    funext v
    simp only [List.nil_append, next]
    congr 1
    funext u
    rw [← List.flatMap_def]
    exact flatMap_sel _ _ (bkey_mono _ _ _ _) _ fun i hi =>
      bkey_lt (hS' u v i hi) (hR' u v i hi)
  · -- the rounds
    simp only [bigProg, rounds_step_direct, h1, h2, rounds_append, rounds_loop_routed,
      rounds_compute, List.length_range]
    have w1 : width (bigSend1 enc send) s ≤ 1 :=
      (width_le_iff _ _ _).2 fun _ _ => by simp [bigSend1]
    have w2 : width (bigSend2 enc) (fun v => (s v, fun u => c u v)) ≤ 1 :=
      (width_le_iff _ _ _).2 fun _ _ => by simp [bigSend2]
    omega
  · intro ok hok henc
    simp only [bigProg, Valid, h1, h2, valid_append, valid_compute, and_true]
    refine ⟨fun u v w hw => ?_, fun h => absurd h (by decide),
      fun u v w hw => ?_, fun h => absurd h (by decide), ?_⟩
    · simp only [bigSend1, List.mem_singleton] at hw
      subst hw
      refine henc _ (le_trans ?_ (Nat.mul_le_mul_right n (le_max_left a b)))
      exact le_trans (Finset.single_le_sum (f := fun v => c u v) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ v)) (hsa u)
    · simp only [bigSend2, List.mem_singleton] at hw
      subst hw
      refine henc _ (le_trans ?_ (Nat.mul_le_mul_right n (le_max_right a b)))
      exact le_trans (b := ∑ x, c x u)
        (by have := before_add_le_sum (fun u' => c u' u) v; omega) (hrb u)
    · refine valid_loop_bigC b send ok _ _ ?_
      intro k _ s' hs'
      have hsel : ∀ u v, bigSendC b send k u (s' u) v =
          sel (send u (s u) v) (bkey n b (before (c u) v) (rin u v)) k := by
        intro u v; simp only [bigSendC, (hs' u).1, (hs' u).2]; rfl
      refine ⟨fun u v w hw => ?_, fun u => ?_, fun v => ?_⟩
      · rw [hsel] at hw; exact hok u v w (sel_sublist _ _ _ hw)
      · simp_rw [hsel, length_sel]
        refine le_trans (Finset.sum_le_sum fun v _ => Finset.card_le_card (s := _)
          (t := (range (c u v)).filter
            (fun p => before (c u) v + p ∈ Finset.Ico (k / b * n) (k / b * n + n))) ?_) ?_
        · intro i hi
          simp only [mem_filter, mem_range] at hi ⊢
          refine ⟨hi.1, mem_Ico_of_div_eq (hn0 u v i hi.1) ?_⟩
          exact (bkey_eq (hR' u v i hi.1) hi.2).1
        · refine le_trans (sum_card_filter_before_le (c u) _) ?_
          simp [hn]
      · simp_rw [hsel, length_sel]
        refine le_trans (Finset.sum_le_sum fun u _ => Finset.card_le_card (s := _)
          (t := (range (c u v)).filter
            (fun p => before (fun u' => c u' v) u + p ∈
              Finset.Ico (k % b * n) (k % b * n + n))) ?_) ?_
        · intro i hi
          simp only [mem_filter, mem_range] at hi ⊢
          refine ⟨hi.1, mem_Ico_of_div_eq (hn0 u v i hi.1) ?_⟩
          exact (bkey_eq (hR' u v i hi.1) hi.2).2
        · refine le_trans (sum_card_filter_before_le (fun u' => c u' v) _) ?_
          simp [hn]

end Big

end Prog

end Cslib.CongestedClique
