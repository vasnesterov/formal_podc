import Papers.PODC2026.RankingOpinions.Weights
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Greedy independent sets and the stable braket multiset (Lemma 3.7)

Breitkopf, Dallot, El-Hayek, Schmid, PODC 2026, Section 3.2.

Purely combinatorial part of the correctness proof of Circles: a multiset of brakets in which
every color `c` occurs exactly `x c` times as a bra and `x c` times as a ket, and in which no two
(distinct) members can profitably exchange their kets, is the sum of the circles `f(G_p)` of the
greedy independent sets `G_p = {c | p ≤ x c}`, `p = 1, …, max x`.
-/

namespace RankingOpinions

open Finset

variable {k : ℕ}

/-- Two brakets `e`, `f` can profitably exchange their kets (rule (1) of Circles): exchanging
strictly decreases the minimum of their weights. -/
def Profitable (e f : Braket k) : Prop :=
  min (w k e.1 f.2) (w k f.1 e.2) < min (w k e.1 e.2) (w k f.1 f.2)

instance (e f : Braket k) : Decidable (Profitable e f) := by unfold Profitable; infer_instance

lemma profitable_comm {e f : Braket k} : Profitable e f ↔ Profitable f e := by
  unfold Profitable; rw [min_comm (w k f.1 _), min_comm (w k f.1 _)]

lemma Profitable.ket_ne {e f : Braket k} (h : Profitable e f) : e.2 ≠ f.2 := by
  intro he; unfold Profitable at h; rw [he] at h
  exact lt_irrefl _ h

/-- The greedy independent set `G_p` (Definition 3.1): the colors with at least `p` supporters.
(The paper builds `G_1, G_2, …` greedily; the resulting sets are exactly these.) -/
def greedy (x : Fin k → ℕ) (p : ℕ) : Finset (Fin k) := univ.filter fun c => p ≤ x c

/-- The circle braket set `f(G)` (Definition 3.6): `⟨g|g'⟩` for `g ∈ G` and `g'` its cyclic
successor in `G` (sorted order, wrapping around). -/
noncomputable def circle (G : Finset (Fin k)) : Multiset (Braket k) :=
  G.val.map fun g => (g, nxt G g)

/-- The multiset `⋃_{p=1..q} f(G_p)` of Lemma 3.7, with `q = max_c x c`
(indexing `p = p' + 1` for `p' < q`). -/
noncomputable def layers (x : Fin k → ℕ) : Multiset (Braket k) :=
  ∑ p ∈ range (univ.sup x), circle (greedy x (p + 1))

/-- A multiset of brakets is *stable* if no two of its members can profitably exchange kets. -/
def MStable (M : Multiset (Braket k)) : Prop :=
  ∀ e f, e ::ₘ f ::ₘ 0 ≤ M → ¬ Profitable e f

lemma MStable.mono {M N : Multiset (Braket k)} (h : MStable M) (hNM : N ≤ M) : MStable N :=
  fun e f hef => h e f (hef.trans hNM)

/-- Bra counts and ket counts are both given by `x`. -/
def Counts (M : Multiset (Braket k)) (x : Fin k → ℕ) : Prop :=
  ∀ c, (M.map Prod.fst).count c = x c ∧ (M.map Prod.snd).count c = x c

lemma circle_map_fst (G : Finset (Fin k)) : (circle G).map Prod.fst = G.val := by
  simp [circle, Multiset.map_map]

lemma circle_map_snd (G : Finset (Fin k)) : (circle G).map Prod.snd = G.val := by
  simp only [circle, Multiset.map_map, Function.comp_def]
  have := Finset.image_val_of_injOn (nxt_injOn G)
  rw [nxt_image] at this
  exact this.symm

lemma circle_nodup (G : Finset (Fin k)) : (circle G).Nodup := by
  apply Multiset.Nodup.map_on _ G.nodup
  intro a _ b _ h
  exact (Prod.ext_iff.1 h).1

lemma mem_circle {G : Finset (Fin k)} {e : Braket k} :
    e ∈ circle G ↔ e.1 ∈ G ∧ e.2 = nxt G e.1 := by
  simp only [circle, Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨hg, rfl⟩
  · rintro ⟨h1, h2⟩; exact ⟨e.1, h1, Prod.ext rfl h2.symm⟩

lemma card_eq_zero_of_counts {M : Multiset (Braket k)} {x : Fin k → ℕ} (hM : Counts M x)
    (hx : ∀ c, x c = 0) : M = 0 := by
  by_contra hne
  obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hne
  have : e.1 ∈ M.map Prod.fst := Multiset.mem_map_of_mem _ he
  rw [← Multiset.count_pos, (hM e.1).1, hx] at this
  exact lt_irrefl _ this

/-- Core of the induction step of Lemma 3.7: the circle of the first greedy set is contained in a
stable multiset with the right counts. -/
lemma circle_le {M : Multiset (Braket k)} {x : Fin k → ℕ} (hM : Counts M x) (hS : MStable M) :
    circle (greedy x 1) ≤ M := by
  set G := greedy x 1 with hG
  have memG : ∀ c, c ∈ G ↔ 0 < x c := by
    intro c; simp [G, greedy, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  -- bras/kets occurring in `M` are in `G`
  have bra_mem : ∀ e ∈ M, e.1 ∈ G := by
    intro e he
    rw [memG, ← (hM e.1).1, Multiset.count_pos]; exact Multiset.mem_map_of_mem _ he
  have ket_mem : ∀ e ∈ M, e.2 ∈ G := by
    intro e he
    rw [memG, ← (hM e.2).2, Multiset.count_pos]; exact Multiset.mem_map_of_mem _ he
  rw [Multiset.le_iff_subset (circle_nodup G)]
  intro e he
  rw [mem_circle] at he
  obtain ⟨hg, hh⟩ := he
  obtain ⟨g, h⟩ := e
  simp only at hg hh
  subst hh
  -- an agent with bra `g`
  obtain ⟨e1, he1, hb1⟩ : ∃ e1 ∈ M, e1.1 = g := by
    have : 0 < (M.map Prod.fst).count g := by rw [(hM g).1, ← memG]; exact hg
    simpa using Multiset.count_pos.1 this
  -- an agent with ket `nxt G g`
  obtain ⟨e2, he2, hk2⟩ : ∃ e2 ∈ M, e2.2 = nxt G g := by
    have : 0 < (M.map Prod.snd).count (nxt G g) := by
      rw [(hM _).2, ← memG]; exact nxt_mem hg
    simpa using Multiset.count_pos.1 this
  by_cases hj : e1.2 = nxt G g
  · have : e1 = (g, nxt G g) := Prod.ext hb1 hj
    exact this ▸ he1
  by_cases hi : e2.1 = g
  · have : e2 = (g, nxt G g) := Prod.ext hi hk2
    exact this ▸ he2
  exfalso
  -- the two agents could profitably exchange kets
  have hne : e1 ≠ e2 := fun h => hi (h ▸ hb1)
  have hle : e1 ::ₘ e2 ::ₘ 0 ≤ M := by
    rw [Multiset.le_iff_subset (by simp [hne])]
    intro e he; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    rcases he with rfl | rfl <;> assumption
  apply hS e1 e2 hle
  unfold Profitable
  -- `w g (nxt G g) < w g e1.2` and `w g (nxt G g) < w e2.1 (nxt G g)`
  have a1 : w k g (nxt G g) < w k g e1.2 := nxt_lt hg (ket_mem e1 he1) hj
  have a2 : w k g (nxt G g) < w k e2.1 (nxt G g) := by
    by_cases h2 : e2.1 = nxt G g
    · have hgn : g ≠ nxt G g := by
        intro e
        have hG1 := (nxt_eq_self_iff hg).1 e.symm
        have := bra_mem e2 he2
        rw [hG1, Finset.mem_singleton] at this
        exact hi this
      rw [h2, w_self]; exact w_lt_of_ne hgn
    · exact w_lt_w_of_closer hi (nxt_lt hg (bra_mem e2 he2) h2)
  rw [hb1, hk2]
  calc min (w k g (nxt G g)) (w k e2.1 e1.2) ≤ w k g (nxt G g) := min_le_left _ _
    _ < min (w k g e1.2) (w k e2.1 (nxt G g)) := lt_min a1 a2

lemma counts_sub {M : Multiset (Braket k)} {x : Fin k → ℕ} (hM : Counts M x) (hS : MStable M) :
    Counts (M - circle (greedy x 1)) (fun c => x c - 1) := by
  have hle := circle_le hM hS
  have hsplit : M = circle (greedy x 1) + (M - circle (greedy x 1)) :=
    (add_tsub_cancel_of_le hle).symm
  intro c
  have h1 := (hM c).1; have h2 := (hM c).2
  rw [hsplit, Multiset.map_add, Multiset.count_add] at h1 h2
  rw [circle_map_fst] at h1; rw [circle_map_snd] at h2
  have hc : (greedy x 1).val.count c = if 0 < x c then 1 else 0 := by
    rw [Multiset.count_eq_of_nodup (greedy x 1).nodup]
    simp [greedy, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  rw [hc] at h1 h2
  dsimp only
  constructor <;> split_ifs at h1 h2 <;> omega

lemma greedy_sub (x : Fin k → ℕ) (p : ℕ) :
    greedy (fun c => x c - 1) (p + 1) = greedy x (p + 2) := by
  ext c; simp only [greedy, mem_filter, mem_univ, true_and]; omega

lemma sup_sub (x : Fin k → ℕ) : univ.sup (fun c => x c - 1) = univ.sup x - 1 := by
  apply le_antisymm
  · apply Finset.sup_le; intro c _
    exact Nat.sub_le_sub_right (Finset.le_sup (f := x) (mem_univ c)) 1
  · rcases Nat.eq_zero_or_pos (univ.sup x) with h | h
    · rw [h]; exact Nat.zero_le _
    · obtain ⟨c0, -, -⟩ := Finset.lt_sup_iff.1 h
      obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup univ ⟨c0, mem_univ _⟩ x
      rw [hc]; exact Finset.le_sup (f := fun c => x c - 1) (mem_univ c)

/-- **Lemma 3.7** (multiset form). A stable multiset of brakets in which every color `c` occurs
`x c` times as a bra and `x c` times as a ket equals `⋃_{p=1..q} f(G_p)`. -/
theorem eq_layers_of_stable (x : Fin k → ℕ) (M : Multiset (Braket k)) (hM : Counts M x)
    (hS : MStable M) : M = layers x := by
  induction h : ∑ c, x c using Nat.strong_induction_on generalizing x M with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hx : ∀ c, x c = 0 := fun c => (Finset.sum_eq_zero_iff.1 h) c (mem_univ c)
    rw [card_eq_zero_of_counts hM hx, layers]
    have : univ.sup x = 0 := by
      apply le_antisymm (Finset.sup_le fun c _ => (hx c).le) (Nat.zero_le _)
    rw [this]; simp
  · have hpos : 0 < univ.sup x := by
      by_contra h0; push Not at h0
      have : ∀ c, x c = 0 := fun c => Nat.le_zero.1 (le_trans (Finset.le_sup (mem_univ c)) h0)
      simp [this] at h; omega
    have hle := circle_le hM hS
    have hrest := ih _ ?_ (fun c => x c - 1) (M - circle (greedy x 1)) (counts_sub hM hS)
      (hS.mono (Multiset.sub_le_self _ _)) rfl
    · rw [← add_tsub_cancel_of_le hle, hrest, layers, layers, sup_sub]
      obtain ⟨m, hm⟩ : ∃ m, univ.sup x = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hm, Finset.sum_range_succ', Nat.add_sub_cancel]
      simp only [greedy_sub, zero_add]
      rw [add_comm]
    · -- the total decreases by the number of nonzero colors (at least one)
      have hsum : ∑ c, x c = ∑ c, (x c - 1) + (greedy x 1).card := by
        rw [Finset.card_eq_sum_ones, greedy, Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro c _; split_ifs <;> omega
      have hne : 0 < (greedy x 1).card := by
        rw [Finset.card_pos]
        obtain ⟨c, -, hc⟩ := Finset.lt_sup_iff.1 hpos
        exact ⟨c, by simp [greedy]; omega⟩
      omega

end RankingOpinions

namespace RankingOpinions

open Finset

variable {k : ℕ}

lemma mem_layers {x : Fin k → ℕ} {e : Braket k} :
    e ∈ layers x ↔ ∃ p < univ.sup x, e ∈ circle (greedy x (p + 1)) := by
  simp [layers, Multiset.mem_sum]

/-- **Lemma 3.2** (Majority color), in the form used for Theorem 1.1: the braket `⟨i|i⟩` occurs in
`⋃_p f(G_p)` iff some greedy independent set is `{i}`, iff `i` is the unique color in relative
majority (and is supported by at least one agent). -/
theorem diag_mem_layers_iff (x : Fin k → ℕ) (i : Fin k) :
    (i, i) ∈ layers x ↔ 0 < x i ∧ ∀ c, c ≠ i → x c < x i := by
  rw [mem_layers]
  constructor
  · rintro ⟨p, -, hp⟩
    rw [mem_circle] at hp
    obtain ⟨hi, he⟩ := hp
    have hG := (nxt_eq_self_iff hi).1 he.symm
    simp only [greedy, mem_filter, mem_univ, true_and] at hi
    refine ⟨by omega, fun c hc => ?_⟩
    by_contra hlt; push Not at hlt
    have : c ∈ greedy x (p + 1) := by simp [greedy]; omega
    rw [hG, mem_singleton] at this
    exact hc this
  · rintro ⟨hpos, hmax⟩
    have hG : greedy x (x i - 1 + 1) = {i} := by
      ext c
      simp only [greedy, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hc; by_contra hne; have := hmax c hne; omega
      · rintro rfl; omega
    refine ⟨x i - 1, ?_, ?_⟩
    · have := Finset.le_sup (f := x) (mem_univ i); omega
    · rw [mem_circle, hG]
      exact ⟨mem_singleton_self i, ((nxt_eq_self_iff (mem_singleton_self i)).2 rfl).symm⟩

/-- **Lemma 3.2** (as stated in the paper): if `μ` is the unique color in relative majority, then
the last greedy independent set is `G_q = {μ}`, and no other greedy set is a singleton `{j}`. -/
theorem greedy_majority (x : Fin k → ℕ) (μ : Fin k) (hμ : ∀ c, c ≠ μ → x c < x μ) :
    greedy x (univ.sup x) = {μ} ∧
      ∀ j p, 1 ≤ p → p ≤ univ.sup x → greedy x p = {j} → j = μ := by
  have hsup : univ.sup x = x μ := by
    apply le_antisymm (Finset.sup_le fun c _ => ?_) (Finset.le_sup (mem_univ μ))
    by_cases h : c = μ
    · rw [h]
    · exact (hμ c h).le
  constructor
  · ext c
    simp only [greedy, mem_filter, mem_univ, true_and, mem_singleton, hsup]
    constructor
    · intro hc; by_contra hne; have := hμ c hne; omega
    · rintro rfl; exact le_rfl
  · intro j p hp1 hpq hG
    by_contra hne
    have hμG : μ ∈ greedy x p := by simp [greedy]; omega
    rw [hG, mem_singleton] at hμG
    exact hne hμG.symm

end RankingOpinions

/-! ## The maximal braket (used for tie breaking, Section 4.3) -/

namespace RankingOpinions

open Finset

variable {k : ℕ}

/-- If `g ∉ G` and `g' ∈ G` is the element of `G` closest to `g` counterclockwise, then `g` lies
on the arc from `g'` to its successor in `G`. -/
lemma w_add_of_closest {G : Finset (Fin k)} {g g' : Fin k} (hg : g ∉ G) (hg' : g' ∈ G)
    (hmin : ∀ y ∈ G, w k g' g ≤ w k y g) : w k g' g + w k g (nxt G g') = w k g' (nxt G g') := by
  have hgg' : g ≠ g' := fun e => hg (e ▸ hg')
  have hh' := nxt_mem (G := G) hg'
  have hgh : g ≠ nxt G g' := fun e => hg (e ▸ hh')
  have hm := hmin _ hh'
  have := g.isLt; have := g'.isLt; have := (nxt G g').isLt
  have v1 := Fin.val_ne_of_ne hgg'; have v2 := Fin.val_ne_of_ne hgh
  clear hmin
  rw [w_val, w_val, w_val]
  rw [w_val, w_val] at hm
  split_ifs at hm ⊢ <;> omega

/-- Lexicographic key (weight, bra) of a braket, as a natural number. -/
def key (e : Braket k) : ℕ := w k e.1 e.2 * k + e.1.val

lemma key_lt_of_w_lt {e f : Braket k} (h : w k e.1 e.2 < w k f.1 f.2) : key e < key f := by
  unfold key
  have := e.1.isLt
  have : w k e.1 e.2 * k + k ≤ w k f.1 f.2 * k := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h
  omega

/-- A braket of `⋃_p f(G_p)` whose bra is not a majority color has a strictly smaller key than
some braket of the last circle `f(G_q)`. -/
lemma exists_key_gt (x : Fin k → ℕ) {e : Braket k} (he : e ∈ layers x)
    (hnot : x e.1 < univ.sup x) : ∃ f ∈ layers x, key e < key f := by
  obtain ⟨p, hp, hpe⟩ := mem_layers.1 he
  rw [mem_circle] at hpe
  obtain ⟨hgp, hh⟩ := hpe
  set q := univ.sup x
  have hGq : (greedy x q).Nonempty := by
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup univ ⟨e.1, mem_univ _⟩ x
    exact ⟨c, by simp [greedy, q, hc]⟩
  have hsub : greedy x q ⊆ greedy x (p + 1) := by
    intro c hc; simp only [greedy, mem_filter, mem_univ, true_and] at hc ⊢; omega
  have hgq : e.1 ∉ greedy x q := by
    simp only [greedy, mem_filter, mem_univ, true_and, not_le]; exact hnot
  obtain ⟨g', hg', hmin⟩ := (greedy x q).exists_min_image (fun y => w k y e.1) hGq
  have hadd := w_add_of_closest hgq hg' hmin
  have hle : w k e.1 e.2 ≤ w k e.1 (nxt (greedy x q) g') := by
    rw [hh]; exact nxt_min hgp (hsub (nxt_mem hg'))
  have hpos := w_pos g' e.1
  refine ⟨(g', nxt (greedy x q) g'), ?_, key_lt_of_w_lt (by simp only; omega)⟩
  refine mem_layers.2 ⟨q - 1, ?_, ?_⟩
  · have : 0 < q := by
      obtain ⟨c, hc⟩ := hGq; simp [greedy] at hc
      exact lt_of_lt_of_le (Nat.zero_lt_of_lt hnot) (le_refl _) |>.trans_le le_rfl
    omega
  · have : q - 1 + 1 = q := by
      have : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hnot
      omega
    rw [this, mem_circle]; exact ⟨hg', rfl⟩

end RankingOpinions
