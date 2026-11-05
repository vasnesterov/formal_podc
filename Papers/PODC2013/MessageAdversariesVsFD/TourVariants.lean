import Papers.PODC2013.MessageAdversariesVsFD.BlockSim

/-!
# Theorem 6: SOURCE + TOUR, SOURCE_tp + TP and SOURCE_pairs + PAIRS are equivalent

Raynal–Stainer, Appendix A.3. The three synchronous models `SMP_n[adv : SOURCE, TOUR]`,
`SMP_n[adv : SOURCE_tp, TP]` and `SMP_n[adv : SOURCE_pairs, PAIRS]` solve the same tasks
(with the strong semantics `Solvable`: every process outputs). We also obtain the source-free
equivalences of Afek–Gafni (`TOUR`, `TP`, `PAIRS`), with the same proofs.

All simulations are instances of the block simulation `solvable_of_blockPat`:

* Part 1 (`sourceTour_subset_tp`): `SOURCE ∩ TOUR ⊆ SOURCEtp ∩ TP`, so the converse is
  monotonicity.
* Part 2: `2n - 3` rounds of flooding under TP simulate a TOUR round (`blockPat_mem_TOUR_of_TP`,
  by the paper's counting `|K_i| + |K_j| ≥ r + 2`, `tp_journey`); under SOURCE_tp the source's
  message reaches everybody within `n - 1 ≤ 2n - 3` rounds of every late block
  (`blockPat_mem_SOURCE_of_SOURCEtp`).
* Part 3: a block of `C` PAIRS rounds in which every pair occurs simulates a TOUR round
  (`blockPat_mem_TOUR_of_PAIRS`, `blockPat_mem_SOURCE_of_SOURCEpairs`).
* Part 4: one TOUR round simulates one PAIRS round, the receivers discarding the messages not
  exchanged by the pair of the round (`blockPat_mem_PAIRS_of_TOUR`,
  `blockPat_mem_SOURCEpairs_of_SOURCE`).

The PAIRS schedule: the paper's is `paperPair σ` (round `t + 1` is associated with the pair
`σ((t + 1) mod C)`, `σ : Fin C ≃` the unordered pairs of distinct processes, `C = n(n-1)/2`);
the theorems hold for every schedule `pair` with `Covers C pair` (every block `[C R, C R + C)`
contains every pair of distinct processes), and `covers_paperPair` shows that the paper's
schedule has this property.
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.HeardOf (Graph Hears)
open Cslib.DynNet (Journey)
open Relation

variable {P X Y : Type}

/-! ## Forward sets (the paper's `K_i^r`) -/

section Flooding

variable [Fintype P] (p : ℕ → Graph P) (s : ℕ)

open Classical in
/-- The forward set `K_i^r` of the paper: the processes that know the message `p_i` had at time
`s` (the beginning of a block) after `r` rounds of flooding, i.e. reached by a journey from
`(i, s)` to time `s + r`. -/
noncomputable def fwd (i : P) (r : ℕ) : Finset P :=
  Finset.univ.filter fun l => Journey p s i (s + r) l

variable {p s}

theorem mem_fwd {i l : P} {r : ℕ} : l ∈ fwd p s i r ↔ Journey p s i (s + r) l := by
  classical
  simp [fwd]

theorem self_mem_fwd (i : P) (r : ℕ) : i ∈ fwd p s i r :=
  mem_fwd.2 (Journey.self (Nat.le_add_right _ _))

theorem fwd_mono (i : P) (r : ℕ) : fwd p s i r ⊆ fwd p s i (r + 1) := fun _ hl =>
  mem_fwd.2 (by rw [← Nat.add_assoc]; exact (mem_fwd.1 hl).stay)

/-- **Growth of `K_i`.** If in round `s + r` (the round after `r` flooding rounds) a directed path
leads from a process of `K_i^r` to a process outside `K_i^r`, then `K_i` grows strictly (some
edge of the path crosses from `K_i^r` to its complement). -/
theorem card_fwd_lt {i a b : P} {r : ℕ} (ha : a ∈ fwd p s i r) (hb : b ∉ fwd p s i r)
    (hab : ReflTransGen (p (s + r)) a b) : (fwd p s i r).card < (fwd p s i (r + 1)).card := by
  obtain ⟨z, y, hzy, hz, hy⟩ :=
    Cslib.DynNet.exists_edge_cross (S := fun x => x ∉ fwd p s i r) hab (not_not.2 ha) hb
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (fwd_mono i r)).2 ⟨y, ?_, hy⟩)
  rw [mem_fwd, ← Nat.add_assoc]
  exact .step (mem_fwd.1 (not_not.1 hz)) (Or.inr hzy)

/-- **The counting of Part 2 of the proof of Theorem 6.** Under TP, as long as neither of `p_i`,
`p_j` knows the message of the other, `|K_i^r| + |K_j^r| ≥ r + 2`. -/
theorem card_fwd_add_card_fwd (hp : p ∈ TP) (i j : P) :
    ∀ r, j ∉ fwd p s i r → i ∉ fwd p s j r → r + 2 ≤ (fwd p s i r).card + (fwd p s j r).card := by
  intro r
  induction r with
  | zero =>
    intro _ _
    have h1 := Finset.card_pos.2 ⟨i, self_mem_fwd (p := p) (s := s) i 0⟩
    have h2 := Finset.card_pos.2 ⟨j, self_mem_fwd (p := p) (s := s) j 0⟩
    omega
  | succ r ih =>
    intro hj hi
    have hj' : j ∉ fwd p s i r := fun h => hj (fwd_mono i r h)
    have hi' : i ∉ fwd p s j r := fun h => hi (fwd_mono j r h)
    have := ih hj' hi'
    have mi := Finset.card_le_card (fwd_mono (p := p) (s := s) i r)
    have mj := Finset.card_le_card (fwd_mono (p := p) (s := s) j r)
    rcases hp (s + r) i j with h | h
    · have := card_fwd_lt (self_mem_fwd i r) hj' h
      omega
    · have := card_fwd_lt (self_mem_fwd j r) hi' h
      omega

/-- **Part 2 of the proof of Theorem 6 (TOUR from TP).** Under TP, after `2n - 3` rounds of
flooding, for every pair of processes one knows the message of the other.

(The paper concludes from `|K_i ∩ K_j| ≥ n - 1` that `{i, j} ∩ K_i ∩ K_j ≠ ∅`; the missing step
is that `j ∉ K_i` and `i ∉ K_j` give `K_i ∩ K_j ⊆ Π ∖ {i, j}`, of size `n - 2`. Here we argue
directly: `K_i ⊆ Π ∖ {j}` and `K_j ⊆ Π ∖ {i}` give `|K_i| + |K_j| ≤ 2n - 2 < 2n - 1`.) -/
theorem tp_journey (hp : p ∈ TP) (hn : 2 ≤ Fintype.card P) (i j : P) :
    Journey p s i (s + (2 * Fintype.card P - 3)) j ∨
      Journey p s j (s + (2 * Fintype.card P - 3)) i := by
  classical
  by_contra! h
  have hj : j ∉ fwd p s i (2 * Fintype.card P - 3) := fun hm => h.1 (mem_fwd.1 hm)
  have hi : i ∉ fwd p s j (2 * Fintype.card P - 3) := fun hm => h.2 (mem_fwd.1 hm)
  have := card_fwd_add_card_fwd hp i j _ hj hi
  have c1 : (fwd p s i (2 * Fintype.card P - 3)).card ≤ Fintype.card P - 1 := by
    rw [← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ j)]
    exact Finset.card_le_card fun l hl => Finset.mem_erase.2 ⟨fun e => hj (e ▸ hl), by simp⟩
  have c2 : (fwd p s j (2 * Fintype.card P - 3)).card ≤ Fintype.card P - 1 := by
    rw [← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ i)]
    exact Finset.card_le_card fun l hl => Finset.mem_erase.2 ⟨fun e => hi (e ▸ hl), by simp⟩
  omega

/-- **Flooding from a source.** If in each of the rounds `s, …, s + r - 1` process `a` has a
directed path to every process, then `|K_a^r| ≥ min(n, r + 1)`. -/
theorem min_card_le_card_fwd {a : P} :
    ∀ r, (∀ r' < r, ∀ l, ReflTransGen (p (s + r')) a l) →
      min (Fintype.card P) (r + 1) ≤ (fwd p s a r).card := by
  intro r
  induction r with
  | zero =>
    intro _
    have := Finset.card_pos.2 ⟨a, self_mem_fwd (p := p) (s := s) a 0⟩
    omega
  | succ r ih =>
    intro hs
    have := ih fun r' hr' => hs r' (by omega)
    have m := Finset.card_le_card (fwd_mono (p := p) (s := s) a r)
    by_cases hu : ∃ l, l ∉ fwd p s a r
    · obtain ⟨l, hl⟩ := hu
      have := card_fwd_lt (self_mem_fwd a r) hl (hs r (by omega) l)
      omega
    · push Not at hu
      have : (fwd p s a r) = Finset.univ := Finset.eq_univ_of_forall hu
      rw [this, Finset.card_univ] at m
      omega

/-- **Part 2 of the proof of Theorem 6 (SOURCE from SOURCE_tp).** If in each of the rounds
`s, …, s + r - 1` process `a` has a directed path to every process and `n ≤ r + 1`, then the
message of `a` at time `s` reaches every process by time `s + r`. -/
theorem source_journey {a : P} {r : ℕ} (hs : ∀ r' < r, ∀ l, ReflTransGen (p (s + r')) a l)
    (hr : Fintype.card P ≤ r + 1) (l : P) : Journey p s a (s + r) l := by
  classical
  have h := min_card_le_card_fwd r hs
  have : fwd p s a r = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (by omega))
  exact mem_fwd.1 (this ▸ Finset.mem_univ l)

end Flooding

/-! ## The induced patterns -/

/-- The PAIRS schedule `pair` is covered by blocks of length `C > 0`: every block of rounds
`[C R, C R + C)` contains a round associated with each pair of distinct processes. -/
def Covers (C : ℕ) (pair : ℕ → Sym2 P) : Prop :=
  0 < C ∧ ∀ R (i j : P), i ≠ j → ∃ t, C * R ≤ t ∧ t < C * R + C ∧ pair t = s(i, j)

/-- The paper's PAIRS schedule: `σ` is a bijection from `{0, …, C - 1}` onto the unordered
pairs of distinct processes (so `C = n(n-1)/2`), and round `t + 1` is associated with the pair
`σ((t + 1) mod C)`. -/
def paperPair {C : ℕ} [NeZero C] (σ : Fin C ≃ {e : Sym2 P // ¬ e.IsDiag}) (t : ℕ) : Sym2 P :=
  (σ (Fin.ofNat C (t + 1))).1

/-- The paper's schedule is covered by blocks of `C` rounds. -/
theorem covers_paperPair {C : ℕ} [NeZero C] (σ : Fin C ≃ {e : Sym2 P // ¬ e.IsDiag}) :
    Covers C (paperPair σ) := by
  have hC : 0 < C := Nat.pos_of_ne_zero (NeZero.ne C)
  refine ⟨hC, fun R i j hij => ?_⟩
  set a := (σ.symm ⟨s(i, j), by simpa using hij⟩).val with ha
  have haC : a < C := (σ.symm _).isLt
  have key : ∀ t, (t + 1) % C = a → paperPair σ t = s(i, j) := by
    intro t ht
    have : (Fin.ofNat C (t + 1)) = σ.symm ⟨s(i, j), by simpa using hij⟩ := Fin.ext (by simp [ht, ha])
    rw [paperPair, this]; simp
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · refine ⟨C * R + (C - 1), by omega, by omega, key _ ?_⟩
    rw [h0, show C * R + (C - 1) + 1 = C * (R + 1) by rw [Nat.mul_add]; omega]
    exact Nat.mul_mod_right _ _
  · refine ⟨C * R + (a - 1), by omega, by omega, key _ ?_⟩
    rw [show C * R + (a - 1) + 1 = a + C * R by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt haC]

/-- Non-vacuity: for `n ≥ 2` processes, the paper's schedule exists. -/
theorem exists_paperPair [Fintype P] (hn : 2 ≤ Fintype.card P) :
    ∃ C, ∃ _ : NeZero C, Nonempty (Fin C ≃ {e : Sym2 P // ¬ e.IsDiag}) := by
  classical
  refine ⟨Fintype.card {e : Sym2 P // ¬ e.IsDiag}, ⟨?_⟩, ⟨(Fintype.equivFin _).symm⟩⟩
  rw [Sym2.card_subtype_not_diag]
  exact (Nat.choose_pos hn).ne'

/-- Flooding without filtering. -/
abbrev flood (k : ℕ) (p : ℕ → Graph P) : ℕ → Graph P := blockPat k (fun _ _ _ => True) p

section Fin
variable [Fintype P]

/-- **Part 2 of the proof of Theorem 6 (TOUR).** Blocks of `2n - 3` rounds of flooding under TP
induce a TOUR pattern. -/
theorem flood_mem_TOUR_of_TP (hn : 2 ≤ Fintype.card P) {p : ℕ → Graph P} (hp : p ∈ TP) :
    flood (2 * Fintype.card P - 3) p ∈ TOUR := by
  intro R i j _
  rcases tp_journey (s := (2 * Fintype.card P - 3) * R) hp hn i j with h | h
  · exact Or.inl ⟨trivial, h⟩
  · exact Or.inr ⟨trivial, h⟩

/-- **Part 2 of the proof of Theorem 6 (SOURCE).** Blocks of `2n - 3` rounds of flooding under
SOURCE_tp induce a SOURCE pattern: from the first block after `r₀` on, the message of the source
reaches every process within `n - 1 ≤ 2n - 3` rounds. -/
theorem flood_mem_SOURCE_of_SOURCEtp (hn : 2 ≤ Fintype.card P) {p : ℕ → Graph P}
    (hp : p ∈ SOURCEtp) : flood (2 * Fintype.card P - 3) p ∈ SOURCE := by
  obtain ⟨a, r₀, h⟩ := hp
  refine ⟨a, r₀, fun R hR i => Or.inr ⟨trivial, source_journey (fun r' _ l => h _ ?_ l) (by omega) i⟩⟩
  have : R ≤ (2 * Fintype.card P - 3) * R := Nat.le_mul_of_pos_left R (by omega)
  omega

end Fin

/-- **Part 3 of the proof of Theorem 6 (TOUR).** Blocks of `C` PAIRS rounds covering all pairs
induce a TOUR pattern (here with flooding; direct transmission would do as well). -/
theorem flood_mem_TOUR_of_PAIRS {C : ℕ} {pair : ℕ → Sym2 P} (hc : Covers C pair)
    {p : ℕ → Graph P} (hp : p ∈ PAIRS pair) : flood C p ∈ TOUR := by
  intro R i j hij
  obtain ⟨t, h1, h2, ht⟩ := hc.2 R i j hij
  have jr : ∀ {a b : P}, p t a b → Journey p (C * R) a (C * R + C) b := fun hab =>
    ((Journey.single hab).mono_left h1).mono_right (by omega)
  rcases (hp t i j hij).2 ht with h | h
  · exact Or.inl ⟨trivial, jr h⟩
  · exact Or.inr ⟨trivial, jr h⟩

/-- **Part 3 of the proof of Theorem 6 (SOURCE).** Under SOURCE_pairs, from the first block after
`r₀` on, every process receives the message of the source in the round of its pair. -/
theorem flood_mem_SOURCE_of_SOURCEpairs {C : ℕ} {pair : ℕ → Sym2 P} (hc : Covers C pair)
    {p : ℕ → Graph P} (hp : p ∈ SOURCEpairs pair) : flood C p ∈ SOURCE := by
  obtain ⟨a, r₀, h⟩ := hp
  refine ⟨a, r₀, fun R hR i => ?_⟩
  by_cases hai : a = i
  · exact Or.inl hai
  obtain ⟨t, h1, h2, ht⟩ := hc.2 R a i hai
  have : R ≤ C * R := Nat.le_mul_of_pos_left R hc.1
  exact Or.inr ⟨trivial,
    ((Journey.single (h t (by omega) i (Ne.symm hai) ht)).mono_left h1).mono_right (by omega)⟩

/-- The filter of Part 4: in round `R`, only the messages exchanged by the pair `pair R` are
kept. -/
def pairFilter (pair : ℕ → Sym2 P) : ℕ → Graph P := fun R j i => pair R = s(j, i)

theorem journey_one {p : ℕ → Graph P} {R : ℕ} {j i : P} (hji : j ≠ i) :
    Journey p (1 * R) j (1 * R + 1) i ↔ p R j i := by
  rw [Nat.one_mul, Cslib.DynNet.journey_succ_iff le_rfl]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain rfl := hy.same_time
    exact h.resolve_left hji
  · exact fun h => ⟨j, .refl, Or.inr h⟩

/-- **Part 4 of the proof of Theorem 6 (PAIRS).** One TOUR round, where receivers discard the
messages not exchanged by the pair of the round, simulates a PAIRS round. -/
theorem blockPat_mem_PAIRS_of_TOUR (pair : ℕ → Sym2 P) {p : ℕ → Graph P} (hp : p ∈ TOUR) :
    blockPat 1 (pairFilter pair) p ∈ PAIRS pair := by
  intro R i j hij
  simp only [blockPat, pairFilter, journey_one hij, journey_one (Ne.symm hij)]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · exact h.trans Sym2.eq_swap
  · intro h
    rcases hp R i j hij with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h.trans Sym2.eq_swap, h'⟩

/-- **Part 4 of the proof of Theorem 6 (SOURCE_pairs).** The source of SOURCE is a source of
SOURCE_pairs in the simulated PAIRS rounds. -/
theorem blockPat_mem_SOURCEpairs_of_SOURCE (pair : ℕ → Sym2 P) {p : ℕ → Graph P}
    (hp : p ∈ SOURCE) : blockPat 1 (pairFilter pair) p ∈ SOURCEpairs pair := by
  obtain ⟨a, r₀, h⟩ := hp
  refine ⟨a, r₀, fun t ht i hia hpair => ⟨hpair, (journey_one (Ne.symm hia)).2 ?_⟩⟩
  exact (h t ht i).resolve_left (Ne.symm hia)

/-! ## Theorem 6 -/

/-- **Part 1 of the proof of Theorem 6.** SOURCE + TOUR is a weaker adversary than
SOURCE_tp + TP (it produces fewer patterns). -/
theorem sourceTour_subset_tp : (SOURCE ∩ TOUR : Adversary P) ⊆ SOURCEtp ∩ TP := by
  rintro p ⟨⟨a, r₀, hs⟩, ht⟩
  refine ⟨⟨a, r₀, fun t h i => ?_⟩, fun t i j => ?_⟩
  · rcases hs t h i with rfl | h'
    · exact .refl
    · exact .single h'
  · by_cases hij : i = j
    · subst hij; exact Or.inl .refl
    · rcases ht t i j hij with h | h
      · exact Or.inl (.single h)
      · exact Or.inr (.single h)

/-- TOUR is a weaker adversary than TP. -/
theorem tour_subset_tp : (TOUR : Adversary P) ⊆ TP := by
  intro p ht t i j
  by_cases hij : i = j
  · subst hij; exact Or.inl .refl
  · rcases ht t i j hij with h | h
    · exact Or.inl (.single h)
    · exact Or.inr (.single h)

/-- **Theorem 6 of [Raynal–Stainer], first equivalence** (Parts 1 and 2 of its proof): for
`n ≥ 2` processes, a task is solvable in `SMP_n[adv : SOURCE, TOUR]` iff it is solvable in
`SMP_n[adv : SOURCE_tp, TP]`. -/
theorem solvable_sourceTour_iff_tp [Fintype P] (hn : 2 ≤ Fintype.card P) (T : Task P X Y) :
    Solvable (SOURCE ∩ TOUR) T ↔ Solvable (SOURCEtp ∩ TP) T :=
  ⟨solvable_of_blockPat (Target := SOURCE ∩ TOUR) (k := 2 * Fintype.card P - 3) (by omega) _
      fun _ hp => ⟨flood_mem_SOURCE_of_SOURCEtp hn hp.1, flood_mem_TOUR_of_TP hn hp.2⟩,
    Solvable.mono sourceTour_subset_tp⟩

/-- **Theorem 6 of [Raynal–Stainer], second equivalence** (Parts 3 and 4 of its proof), for any
PAIRS schedule covered by blocks of `C` rounds (e.g. the paper's, `covers_paperPair`): a task is
solvable in `SMP_n[adv : SOURCE, TOUR]` iff it is solvable in `SMP_n[adv : SOURCE_pairs, PAIRS]`. -/
theorem solvable_sourceTour_iff_pairs {C : ℕ} {pair : ℕ → Sym2 P} (hc : Covers C pair)
    (T : Task P X Y) :
    Solvable (SOURCE ∩ TOUR) T ↔ Solvable (SOURCEpairs pair ∩ PAIRS pair) T :=
  ⟨solvable_of_blockPat (Target := SOURCE ∩ TOUR) hc.1 _
      fun _ hp => ⟨flood_mem_SOURCE_of_SOURCEpairs hc hp.1, flood_mem_TOUR_of_PAIRS hc hp.2⟩,
    solvable_of_blockPat (Host := SOURCE ∩ TOUR) (Target := SOURCEpairs pair ∩ PAIRS pair)
      Nat.one_pos (pairFilter pair)
      fun _ hp => ⟨blockPat_mem_SOURCEpairs_of_SOURCE pair hp.1,
        blockPat_mem_PAIRS_of_TOUR pair hp.2⟩⟩

/-- **Theorem 6 of [Raynal–Stainer]** (with the paper's PAIRS schedule `σ((t + 1) mod C)`, `σ` a
bijection onto the pairs of distinct processes, `n ≥ 2`): `SMP_n[adv : SOURCE, TOUR]`,
`SMP_n[adv : SOURCE_tp, TP]` and `SMP_n[adv : SOURCE_pairs, PAIRS]` solve the same tasks. -/
theorem theorem6 [Fintype P] (hn : 2 ≤ Fintype.card P) {C : ℕ} [NeZero C]
    (σ : Fin C ≃ {e : Sym2 P // ¬ e.IsDiag}) (T : Task P X Y) :
    (Solvable (SOURCE ∩ TOUR) T ↔ Solvable (SOURCEtp ∩ TP) T) ∧
      (Solvable (SOURCE ∩ TOUR) T ↔
        Solvable (SOURCEpairs (paperPair σ) ∩ PAIRS (paperPair σ)) T) ∧
      (Solvable (SOURCEtp ∩ TP) T ↔
        Solvable (SOURCEpairs (paperPair σ) ∩ PAIRS (paperPair σ)) T) :=
  ⟨solvable_sourceTour_iff_tp hn T, solvable_sourceTour_iff_pairs (covers_paperPair σ) T,
    (solvable_sourceTour_iff_tp hn T).symm.trans
      (solvable_sourceTour_iff_pairs (covers_paperPair σ) T)⟩

/-! ## The source-free equivalences of Afek–Gafni -/

/-- **Afek–Gafni** (recalled in Appendix A.1): for `n ≥ 2`, TOUR and TP solve the same tasks. -/
theorem solvable_tour_iff_tp [Fintype P] (hn : 2 ≤ Fintype.card P) (T : Task P X Y) :
    Solvable TOUR T ↔ Solvable TP T :=
  ⟨solvable_of_blockPat (k := 2 * Fintype.card P - 3) (by omega) _
      fun _ hp => flood_mem_TOUR_of_TP hn hp,
    Solvable.mono tour_subset_tp⟩

/-- **Afek–Gafni** (recalled in Appendix A.1): TOUR and PAIRS (for a schedule covered by blocks
of `C` rounds) solve the same tasks. -/
theorem solvable_tour_iff_pairs {C : ℕ} {pair : ℕ → Sym2 P} (hc : Covers C pair)
    (T : Task P X Y) : Solvable TOUR T ↔ Solvable (PAIRS pair) T :=
  ⟨solvable_of_blockPat hc.1 _ fun _ hp => flood_mem_TOUR_of_PAIRS hc hp,
    solvable_of_blockPat Nat.one_pos (pairFilter pair)
      fun _ hp => blockPat_mem_PAIRS_of_TOUR pair hp⟩

end Podc.MessageAdversariesVsFD
