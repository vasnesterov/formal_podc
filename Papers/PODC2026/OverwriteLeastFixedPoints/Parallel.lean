import Papers.PODC2026.OverwriteLeastFixedPoints.Interleaving

/-!
# Section 3: non-interleaving parallel rounds (Lemma 3.2, Theorem 3.1)

State space: a product `(k : κ) → β k` of coordinates (the paper: vectors in `{0,…,m}ⁿ`).

**One round** (`RoundExec wr f G S G'`), from the committed state `G`, with the set `S` of active
processes and the committed state `G'` at the end of the round. The paper's real-time description is
captured by two witnesses:
* `read i`: the vector process `i` read; coordinate `k` of it is either the committed value `G k` or
  the value written to `k` in this round by some active process `j`;
* `rank i : ℕ`: the instant at which process `i` finished its reads. Process `i` can read a write of
  `j` only if `rank j < rank i`: `j` computes `f j (read j)` after finishing its reads and its write
  starts before `i`'s read ends. (Any real-time execution of finitely many processes gives such
  ranks; without them, values could come "out of thin air", see `acausal_round_breaks_leastness`.)
* process `j` writes coordinate `k` iff `wr (read j) (f j (read j)) k`: for the
  update-only-on-change model `uooc` iff the computed value differs from the read one
  (Definition 3); for the naive model `naive` always.
* the committed value of `k` is the value of *some* write to `k` (last writer wins, writes in any
  order), or `G k` if nobody writes `k`.

Reads overlapping writes may return the old value or any written value; no memory consistency is
assumed, exactly as in the paper.
-/

namespace Podc.OverwriteLeastFixedPoints

variable {ι κ : Type*} {β : κ → Type*}

/-- A write policy: a process that read `X` and computed `H` writes coordinate `k` iff
`wr X H k`. -/
abbrev WritePolicy (β : κ → Type*) := ((k : κ) → β k) → ((k : κ) → β k) → κ → Prop

/-- Definition 3 (update-only-on-change): write coordinate `k` iff its value changed. -/
def uooc : WritePolicy β := fun X H k => H k ≠ X k

instance [∀ k, DecidableEq (β k)] (X H : (k : κ) → β k) (k : κ) : Decidable (uooc X H k) :=
  inferInstanceAs (Decidable (H k ≠ X k))

/-- The naive read–compute–write rule: every coordinate of the computed vector is written. -/
def naive : WritePolicy β := fun _ _ _ => True

/-- One non-interleaving round from committed state `G` with active set `S` ending in the committed
state `G'` (see the module docstring). -/
structure RoundExec (wr : WritePolicy β) (f : ι → ((k : κ) → β k) → ((k : κ) → β k))
    (G : (k : κ) → β k) (S : Set ι) (G' : (k : κ) → β k) where
  /-- The vector read by process `i`. -/
  read : ι → (k : κ) → β k
  /-- The instant at which process `i` finished reading. -/
  rank : ι → ℕ
  /-- A read returns the committed value or the value of a causally earlier write in this round. -/
  read_spec : ∀ i ∈ S, ∀ k, read i k = G k ∨
    ∃ j ∈ S, rank j < rank i ∧ wr (read j) (f j (read j)) k ∧ read i k = f j (read j) k
  /-- Unwritten coordinates keep their committed value. -/
  commit_unwritten : ∀ k, (∀ j ∈ S, ¬ wr (read j) (f j (read j)) k) → G' k = G k
  /-- A written coordinate ends with the value of one of the writes. -/
  commit_written : ∀ k, (∃ j ∈ S, wr (read j) (f j (read j)) k) →
    ∃ j ∈ S, wr (read j) (f j (read j)) k ∧ G' k = f j (read j) k

/-- `G'` is a possible committed state after a parallel round from `G` with active set `S`. -/
def ParRound (wr : WritePolicy β) (f : ι → ((k : κ) → β k) → ((k : κ) → β k))
    (G : (k : κ) → β k) (S : Set ι) (G' : (k : κ) → β k) : Prop :=
  Nonempty (RoundExec wr f G S G')

/-- Non-vacuity: from every state, every set of active processes has some round (all processes read
the committed state; each written coordinate takes the value of some writer). -/
theorem exists_parRound (wr : WritePolicy β) (f : ι → ((k : κ) → β k) → ((k : κ) → β k))
    (G : (k : κ) → β k) (S : Set ι) : ∃ G', ParRound wr f G S G' := by
  classical
  let G' : (k : κ) → β k := fun k =>
    if h : ∃ j ∈ S, wr G (f j G) k then f h.choose G k else G k
  refine ⟨G', ⟨⟨fun _ => G, fun _ => 0, fun _ _ _ => Or.inl rfl, fun k hk => ?_, fun k hk => ?_⟩⟩⟩
  · have : ¬ ∃ j ∈ S, wr G (f j G) k := fun ⟨j, hj, hw⟩ => hk j hj hw
    simp only [G', dite_eq_right_iff]
    exact fun h => absurd h this
  · refine ⟨hk.choose, hk.choose_spec.1, hk.choose_spec.2, ?_⟩
    simp only [G', dite_eq_left_of_eq_true (eq_true hk)]

/-- An atomic step `G ↦ f i G` is a special case of an update-only-on-change round with
`S = {i}`. -/
theorem parRound_single (f : ι → ((k : κ) → β k) → ((k : κ) → β k)) (G : (k : κ) → β k) (i : ι) :
    ParRound uooc f G {i} (f i G) := by
  refine ⟨⟨fun _ => G, fun _ => 0, fun _ _ _ => Or.inl rfl, fun k hk => ?_, fun k hk => ?_⟩⟩
  · by_contra h
    exact hk i rfl h
  · obtain ⟨j, rfl, hw⟩ := hk
    exact ⟨j, rfl, hw, rfl⟩

section Order

variable [∀ k, PartialOrder (β k)] {f : ι → ((k : κ) → β k) → ((k : κ) → β k)}
  {G G' : (k : κ) → β k} {S : Set ι}

omit [∀ k, PartialOrder (β k)] in
/-- Strong induction on the read instants of a round. -/
theorem RoundExec.induction {wr : WritePolicy β} (e : RoundExec wr f G S G') {P : ι → Prop}
    (h : ∀ i ∈ S, (∀ j ∈ S, e.rank j < e.rank i → P j) → P i) : ∀ i ∈ S, P i := by
  suffices ∀ n, ∀ i ∈ S, e.rank i = n → P i from fun i hi => this _ i hi rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hn
    exact h i hi fun j hj hr => ih _ (hn ▸ hr) j hj rfl

/-- Every read of a round returns at least the committed state (part of Lemma 3.2). -/
theorem RoundExec.le_read (e : RoundExec uooc f G S G') (hinf : ∀ i, Inflationary (f i)) :
    ∀ i ∈ S, G ≤ e.read i := by
  refine e.induction fun i hi ih k => ?_
  rcases e.read_spec i hi k with h | ⟨j, hj, hr, -, h⟩
  · rw [h]
  · rw [h]
    exact (ih j hj hr k).trans (hinf j _ k)

/-- **Lemma 3.2 (1)** of [Garg–Garg, BA]: every write in round `t` writes a value strictly greater
than the committed value `G k` (the full version states `≥`). -/
theorem RoundExec.lt_write (e : RoundExec uooc f G S G') (hinf : ∀ i, Inflationary (f i))
    {j : ι} (hj : j ∈ S) {k : κ} (hw : uooc (e.read j) (f j (e.read j)) k) :
    G k < f j (e.read j) k :=
  lt_of_le_of_lt (e.le_read hinf j hj k) (lt_of_le_of_ne (hinf j _ k) (Ne.symm hw))

/-- **Lemma 3.2 (2)**: the committed state does not decrease. -/
theorem RoundExec.le_commit (e : RoundExec uooc f G S G') (hinf : ∀ i, Inflationary (f i)) :
    G ≤ G' := by
  intro k
  by_cases h : ∃ j ∈ S, uooc (e.read j) (f j (e.read j)) k
  · obtain ⟨j, hj, hw, he⟩ := e.commit_written k h
    rw [he]
    exact (e.lt_write hinf hj hw).le
  · push Not at h
    rw [e.commit_unwritten k h]

/-- **Lemma 3.2 (3)**: a coordinate keeps its committed value iff nobody writes it. -/
theorem RoundExec.commit_eq_iff (e : RoundExec uooc f G S G') (hinf : ∀ i, Inflationary (f i))
    (k : κ) : G' k = G k ↔ ∀ j ∈ S, ¬ uooc (e.read j) (f j (e.read j)) k := by
  constructor
  · intro heq j hj hw
    obtain ⟨j', hj', hw', he⟩ := e.commit_written k ⟨j, hj, hw⟩
    have := e.lt_write hinf hj' hw'
    rw [← he, heq] at this
    exact lt_irrefl _ this
  · exact e.commit_unwritten k

/-- If a round changes nothing, every process read exactly the committed state. -/
theorem RoundExec.read_eq_of_commit_eq (e : RoundExec uooc f G S G')
    (hinf : ∀ i, Inflationary (f i)) (heq : G' = G) : ∀ i ∈ S, e.read i = G := by
  intro i hi
  funext k
  rcases e.read_spec i hi k with h | ⟨j, hj, -, hw, -⟩
  · exact h
  · exact absurd hw ((e.commit_eq_iff hinf k).1 (congrFun heq k) j hj)

/-- A round from below a common fixed point `Y` of monotone functions stays below `Y` (any write
policy). -/
theorem RoundExec.commit_le {wr : WritePolicy β} (e : RoundExec wr f G S G')
    (hm : ∀ i, Monotone (f i)) {Y : (k : κ) → β k} (hY : IsCommonFixed f Y) (hG : G ≤ Y) :
    G' ≤ Y := by
  have hread : ∀ i ∈ S, e.read i ≤ Y := by
    refine e.induction fun i hi ih k => ?_
    rcases e.read_spec i hi k with h | ⟨j, hj, hr, -, h⟩
    · rw [h]; exact hG k
    · rw [h, ← hY j]; exact hm j (ih j hj hr) k
  intro k
  by_cases h : ∃ j ∈ S, wr (e.read j) (f j (e.read j)) k
  · obtain ⟨j, hj, -, he⟩ := e.commit_written k h
    rw [he, ← hY j]
    exact hm j (hread j hj) k
  · push Not at h
    rw [e.commit_unwritten k h]
    exact hG k

/-- Theorem 3.1 from an arbitrary initial state: a fair parallel execution with
update-only-on-change of monotone inflationary functions terminates at the least common fixed
point above `G 0`. -/
theorem parallel_converges_from [WellFoundedGT ((k : κ) → β k)] (hm : ∀ i, Monotone (f i))
    (hinf : ∀ i, Inflationary (f i)) {S : ℕ → Set ι} (hS : FairSets S) {G : ℕ → (k : κ) → β k}
    (hG : ∀ t, ParRound uooc f (G t) (S t) (G (t + 1))) :
    ∃ x, TerminatesAt G x ∧ IsLeast {y | IsCommonFixed f y ∧ G 0 ≤ y} x := by
  have hmono : Monotone G := monotone_nat_of_le_succ fun t => (hG t).some.le_commit hinf
  obtain ⟨T, hT⟩ := exists_terminatesAt_of_monotone hmono
  refine ⟨G T, ⟨T, hT⟩, ⟨?_, hmono (Nat.zero_le _)⟩, ?_⟩
  · intro i
    obtain ⟨t, ht, hti⟩ := hS i T
    let e := (hG t).some
    have heq : G (t + 1) = G t := by rw [hT t ht, hT (t + 1) (by omega)]
    have hread := e.read_eq_of_commit_eq hinf heq i hti
    funext k
    by_contra hne
    have hw : uooc (e.read i) (f i (e.read i)) k := by
      simp only [uooc, hread, hT t ht]
      exact hne
    exact (e.commit_eq_iff hinf k).1 (congrFun heq k) i hti hw
  · rintro y ⟨hy, h0⟩
    have : ∀ t, G t ≤ y := by
      intro t
      induction t with
      | zero => exact h0
      | succ t ih => exact (hG t).some.commit_le hm hy ih
    exact this T

/-- **Theorem 3.1** of [Garg–Garg, BA] (= Theorem 3 of the full version). Let the state space be a
finite product of finite posets with bottom (the paper: `{0,…,m}ⁿ`), and let every `fᵢ` be monotone
and inflationary. A parallel execution with update-only-on-change, non-interleaving rounds and a fair
scheduler, starting from `⊥`, terminates at the least common fixed point. -/
theorem theorem_3_1 [Finite κ] [∀ k, Finite (β k)] [∀ k, OrderBot (β k)]
    (hm : ∀ i, Monotone (f i)) (hinf : ∀ i, Inflationary (f i)) {S : ℕ → Set ι} (hS : FairSets S)
    {G : ℕ → (k : κ) → β k} (h0 : G 0 = ⊥) (hG : ∀ t, ParRound uooc f (G t) (S t) (G (t + 1))) :
    ∃ x, TerminatesAt G x ∧ IsLeast {y | IsCommonFixed f y} x := by
  obtain ⟨x, hx, hl⟩ := parallel_converges_from hm hinf hS hG
  exact ⟨x, hx, hl.1.1, fun y hy => hl.2 ⟨hy, by rw [h0]; exact bot_le⟩⟩

/-- **Corollary 4.2** of [Garg–Garg] (parallel version): for deflationary monotone functions on a
finite product of finite posets with top, a fair update-only-on-change parallel execution starting
from `⊤` terminates at the greatest common fixed point. -/
theorem corollary_4_2_parallel [Finite κ] [∀ k, Finite (β k)] [∀ k, OrderTop (β k)]
    (hm : ∀ i, Monotone (f i)) (hdef : ∀ i, Deflationary (f i)) {S : ℕ → Set ι}
    (hS : FairSets S) {G : ℕ → (k : κ) → β k} (h0 : G 0 = ⊤)
    (hG : ∀ t, ParRound uooc f (G t) (S t) (G (t + 1))) :
    ∃ x, TerminatesAt G x ∧ IsGreatest {y | IsCommonFixed f y} x := by
  have := @theorem_3_1 ι κ (fun k => (β k)ᵒᵈ) (fun k => inferInstance) f
  exact this (fun i _ _ h => hm i h) (fun i x => hdef i x) hS (G := G) h0 hG

end Order

/-! ## Counterexamples and remarks for Section 3 -/

/-- The two functions of the paper's naive-write example on `{0,1}²`:
`f₀ (x₀, x₁) = (1, x₁)` and `f₁ (x₀, x₁) = (x₀, 1)`. -/
def naiveF : Fin 2 → (Fin 2 → Bool) → (Fin 2 → Bool) := fun i x => Function.update x i true

/-- Section 3: with the naive write rule (every process writes every coordinate), a round of both
processes from `(0,0)` can commit `(0,0)` again (each coordinate's last write comes from the process
that did not change it), so the fair execution that stays at `(0,0)` forever is possible, although
`(0,0)` is not a common fixed point. The functions are monotone and inflationary. -/
theorem naive_round_stuck :
    (∀ i, Monotone (naiveF i)) ∧ (∀ i, Inflationary (naiveF i)) ∧
      ParRound naive naiveF ⊥ Set.univ ⊥ ∧ FairSets (fun _ : ℕ => (Set.univ : Set (Fin 2))) ∧
      ¬ IsCommonFixed naiveF ⊥ := by
  refine ⟨?_, ?_, ⟨⟨fun _ => ⊥, fun _ => 0, fun _ _ _ => Or.inl rfl,
      fun k hk => absurd trivial (hk 0 trivial), fun k _ => ?_⟩⟩,
    fun i N => ⟨N, le_rfl, trivial⟩, fun h => absurd (congrFun (h 0) 0) (by decide)⟩
  · intro i x y h k
    by_cases hk : k = i
    · subst hk; simp [naiveF]
    · simp [naiveF, Function.update_of_ne hk, h k]
  · intro i x k
    by_cases hk : k = i
    · subst hk; simp [naiveF]
    · simp [naiveF, Function.update_of_ne hk]
  · refine ⟨1 - k, trivial, trivial, ?_⟩
    fin_cases k <;> rfl

/-- The paper's real-time model forbids a process from reading a value whose computation depends on
its own read. Without that causality constraint (no `rank`), values could appear "out of thin air":
with `f₀ x = (x₀ ∨ x₁, x₁)` and `f₁ x = (x₀, x₀ ∨ x₁)` (monotone, inflationary, `⊥` is a common fixed
point), process 0 reads `(0,1)` justified by process 1's write and process 1 reads `(1,0)` justified
by process 0's write; the round would commit `(1,1)`, above the least common fixed point. With
causality this is impossible (`RoundExec.commit_le`). -/
theorem acausal_round_breaks_leastness :
    let f : Fin 2 → (Fin 2 → Bool) → (Fin 2 → Bool) :=
      fun i x => Function.update x i (x 0 || x 1)
    let X : Fin 2 → Fin 2 → Bool := fun i k => decide (i ≠ k)
    (∀ i, Monotone (f i)) ∧ (∀ i, Inflationary (f i)) ∧ IsCommonFixed f ⊥ ∧
      -- the cyclic reads are each justified by the other process's (changed) write:
      (∀ i k, X i k = false ∨ ∃ j, uooc (X j) (f j (X j)) k ∧ X i k = f j (X j) k) ∧
      -- and committing these writes gives `(1,1)`:
      (fun k => f k (X k) k) = ⊤ ∧
      -- whereas no causal round from `⊥` commits `(1,1)`:
      ¬ ParRound uooc f ⊥ Set.univ ⊤ := by
  intro f X
  have hm : ∀ i, Monotone (f i) := by
    intro i x y h k
    by_cases hk : k = i
    · subst hk
      simp only [f, Function.update_self]
      have h0 := h 0; have h1 := h 1
      exact sup_le_sup h0 h1
    · simp [f, Function.update_of_ne hk, h k]
  have hcf : IsCommonFixed f ⊥ := by
    intro i; funext k; by_cases hk : k = i
    · subst hk; simp [f]
    · simp [f, Function.update_of_ne hk]
  refine ⟨hm, ?_, hcf, by decide, by decide, fun ⟨e⟩ => ?_⟩
  · intro i x k
    by_cases hk : k = i
    · subst hk; simp only [f, Function.update_self]
      cases h0 : x 0 <;> cases h1 : x 1 <;> fin_cases k <;> simp_all
    · simp [f, Function.update_of_ne hk]
  · have := e.commit_le hm hcf le_rfl
    exact absurd (this 0) (by decide)

/-- The brief announcement states Theorem 3.1 for a "finite distributive lattice of vectors", i.e.
possibly a proper sublattice `L` of `{0,…,m}ⁿ` (such as a lattice of consistent cuts). Then the
coordinatewise last-writer-wins commit can leave `L`: in the 5-element distributive sublattice
`L = {000, 010, 110, 021, 121}` of `{0,1,2}³`, the functions `f_A x = x ⊔ 110` and `f_B x = x ⊔ 021`
map `L` to `L` and are monotone and inflationary, but a round of both from `000` (both read `000`;
coordinates 0, 1 last written by `A`, coordinate 2 by `B`) commits `111 ∉ L`. So the theorem needs
the full product (as in the full version's "for simplicity" assumption). -/
theorem sublattice_round_escapes :
    let L : Finset (Fin 3 → Fin 3) := {![0, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 2, 1], ![1, 2, 1]}
    let f : Bool → (Fin 3 → Fin 3) → (Fin 3 → Fin 3) :=
      fun i x => if i then x ⊔ ![0, 2, 1] else x ⊔ ![1, 1, 0]
    (∀ a ∈ L, ∀ b ∈ L, a ⊔ b ∈ L ∧ a ⊓ b ∈ L) ∧ (∀ i, ∀ x ∈ L, f i x ∈ L) ∧
      (∀ i, Monotone (f i)) ∧ (∀ i, Inflationary (f i)) ∧ ⊥ ∈ L ∧
      ParRound uooc f ⊥ Set.univ ![1, 1, 1] ∧ ![1, 1, 1] ∉ L := by
  intro L f
  refine ⟨by decide, by decide, ?_, ?_, by decide, ⟨⟨fun _ => ⊥, fun _ => 0,
    fun _ _ _ => Or.inl rfl, fun k hk => ?_, fun k _ => ?_⟩⟩, by decide⟩
  · intro i x y h
    cases i <;> exact sup_le_sup_right h _
  · intro i x
    cases i <;> exact le_sup_left
  · exfalso
    fin_cases k
    · exact hk false trivial (by decide)
    · exact hk false trivial (by decide)
    · exact hk true trivial (by decide)
  · fin_cases k
    · exact ⟨false, trivial, by decide, by decide⟩
    · exact ⟨false, trivial, by decide, by decide⟩
    · exact ⟨true, trivial, by decide, by decide⟩

end Podc.OverwriteLeastFixedPoints
