import Papers.PODC2019.FloodingTermination.Termination
import Podc.Graph.Ball

/-!
# Time to termination (Section 3 of Hussak–Trehan)

Definitions 2.3 and 3.1 of the paper:
* `distSet G s j` — the distance set `D_j = {g | d(s, g) = j}` (distances in `ℕ∞`, so unreachable
  nodes lie in no `D_j`);
* `IsEC G s g` — `g` is an *equidistantly-connected* (ec) node: it has a neighbour `g' ∉ {s, g}`
  with `d(s, g) = d(s, g')`;
* `IsFirstIn G s v j` / `IsSecondIn G s v j` — `v¹ ∈ R_j` / `v² ∈ R_j`.

Main results (all for finite connected graphs where the paper needs it):
* `lemma_3_2_i`, `lemma_3_2_ii`, `lemma_3_2_iii`, `lemma_3_3`, `lemma_3_4`, `lemma_3_6`;
* `theorem_3_5` — flooding has terminated after round `e = ecc(s)` iff `G` is bipartite;
  `theorem_3_5'` — in a bipartite graph the termination time is exactly `e`;
* `theorem_3_7` — in a non-bipartite graph the termination time `T` satisfies `e < T ≤ e + d + 1`;
* `terminationTime_le_diam`, `terminationTime_le_two_mul_diam_add_one` — the abstract's bounds
  `d` and `2d + 1`.
-/

namespace FloodingTermination

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (s : V)

/-- The distance set `D_j` (Definition 3.1(i)). -/
def distSet (j : ℕ) : Set V := {g | G.edist s g = j}

/-- Equidistantly-connected node (Definition 3.1(ii)): `g` has a neighbour `g' ∉ {s, g}` at the same
distance from `s`. -/
def IsEC (g : V) : Prop :=
  ∃ g', g' ≠ s ∧ g' ≠ g ∧ G.edist s g = G.edist s g' ∧ G.Adj g g'

/-- `v¹ ∈ R_j` (Definition 2.3): `v` is in `R_j` and in no earlier round-set. -/
def IsFirstIn (v : V) (j : ℕ) : Prop := v ∈ roundSet G s j ∧ ∀ i < j, v ∉ roundSet G s i

/-- `v² ∈ R_j` (Definition 2.3): `v` is in `R_j` and in some earlier round-set. -/
def IsSecondIn (v : V) (j : ℕ) : Prop := v ∈ roundSet G s j ∧ ∃ i < j, v ∈ roundSet G s i

variable {G s}

lemma mem_distSet_iff {g : V} {j : ℕ} :
    g ∈ distSet G s j ↔ G.Reachable s g ∧ G.dist s g = j :=
  edist_eq_natCast_iff

lemma mem_roundSet_dist {g : V} (hr : G.Reachable s g) : g ∈ roundSet G s (G.dist s g) :=
  mem_roundSet_iff.2 hr.isParityDist_dist

lemma dist_le_of_mem_roundSet {g : V} {j : ℕ} (h : g ∈ roundSet G s j) : G.dist s g ≤ j :=
  dist_le_of_isParityDist (mem_roundSet_iff.1 h)

lemma reachable_of_mem_roundSet {g : V} {j : ℕ} (h : g ∈ roundSet G s j) : G.Reachable s g :=
  reachable_of_mem_walkSet (mem_roundSet_iff.1 h).1

/-- **Lemma 3.2(i)** of [Hussak–Trehan, PODC'19]: `D_j ⊆ R_j`, and `R_j ∩ D_i = ∅` for `i > j`. -/
theorem lemma_3_2_i (j : ℕ) :
    distSet G s j ⊆ roundSet G s j ∧ ∀ i, j < i → roundSet G s j ∩ distSet G s i = ∅ := by
  refine ⟨fun g hg => ?_, fun i hij => ?_⟩
  · obtain ⟨hr, rfl⟩ := mem_distSet_iff.1 hg
    exact mem_roundSet_dist hr
  · ext g
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hg hd
    obtain ⟨-, rfl⟩ := mem_distSet_iff.1 hd
    have := dist_le_of_mem_roundSet hg
    omega

/-- The first appearance of a reachable node is at its distance from `s`. -/
lemma isFirstIn_dist {g : V} (hr : G.Reachable s g) : IsFirstIn G s g (G.dist s g) :=
  ⟨mem_roundSet_dist hr, fun i hi h => absurd (dist_le_of_mem_roundSet h) (by omega)⟩

lemma isFirstIn_iff {g : V} {j : ℕ} : IsFirstIn G s g j ↔ G.Reachable s g ∧ G.dist s g = j := by
  constructor
  · rintro ⟨h, hmin⟩
    have hr := reachable_of_mem_roundSet h
    refine ⟨hr, le_antisymm (dist_le_of_mem_roundSet h) ?_⟩
    by_contra hlt
    exact hmin _ (by omega) (mem_roundSet_dist hr)
  · rintro ⟨hr, rfl⟩
    exact isFirstIn_dist hr

/-- **Lemma 3.2(ii)**: nodes in `D_j` send to all their neighbours in `D_{j+1}` in round `j + 1`. -/
theorem lemma_3_2_ii {j : ℕ} {g g' : V} (hg : g ∈ distSet G s j) (hg' : g' ∈ distSet G s (j + 1))
    (hadj : G.Adj g g') : sends G s (j + 1) g g' := by
  obtain ⟨hr, rfl⟩ := mem_distSet_iff.1 hg
  obtain ⟨hr', hd'⟩ := mem_distSet_iff.1 hg'
  rw [sends_succ_iff]
  exact ⟨hadj, hr.isParityDist_dist, hd' ▸ hr'.isParityDist_dist⟩

/-- **Lemma 3.2(iii)**: an ec node `g ∈ D_j` (`j ≥ 1`) receives the message for the second time in
round `j + 1`. -/
theorem lemma_3_2_iii {j : ℕ} (_hj : 1 ≤ j) {g : V} (hg : g ∈ distSet G s j) (hec : IsEC G s g) :
    IsSecondIn G s g (j + 1) := by
  obtain ⟨g', -, -, hd, hadj⟩ := hec
  have hg' : g' ∈ distSet G s j := by simp only [distSet, Set.mem_ofPred_eq] at hg ⊢; rw [← hd, hg]
  obtain ⟨hr, rfl⟩ := mem_distSet_iff.1 hg
  obtain ⟨hr', hd'⟩ := mem_distSet_iff.1 hg'
  refine ⟨mem_roundSet_iff.2 ⟨mem_walkSet_succ_of_adj (hd' ▸ hr'.mem_walkSet_dist) hadj.symm,
    fun t ht hpar hm => ?_⟩, _, Nat.lt_succ_self _, mem_roundSet_dist hr⟩
  have := dist_le_of_mem_walkSet hm
  omega

/-- **Lemma 3.4** of [Hussak–Trehan, PODC'19] (for connected `G`): `G` is bipartite iff it has no
ec nodes. -/
theorem lemma_3_4 (hc : G.Connected) : G.IsBipartite ↔ ∀ g, ¬ IsEC G s g := by
  constructor
  · rintro hb g ⟨g', -, -, hd, hadj⟩
    have hr := hc.preconnected s g
    have hr' := hc.preconnected s g'
    have hdd : G.dist s g = G.dist s g' := by
      have h1 := hr.coe_dist_eq_edist; have h2 := hr'.coe_dist_eq_edist
      rw [hd, ← h2] at h1; exact_mod_cast h1
    have := mod_two_eq_of_colorable hb hr.mem_walkSet_dist
      (mem_walkSet_succ_of_adj hr'.mem_walkSet_dist hadj.symm)
    omega
  · intro hno
    refine ⟨Coloring.mk (fun v => (⟨G.dist s v % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
    intro u v huv heq
    have hru := hc.preconnected s u
    have hrv := hc.preconnected s v
    have h1 := dist_le_of_mem_walkSet (mem_walkSet_succ_of_adj hru.mem_walkSet_dist huv)
    have h2 := dist_le_of_mem_walkSet (mem_walkSet_succ_of_adj hrv.mem_walkSet_dist huv.symm)
    have hmod : G.dist s u % 2 = G.dist s v % 2 := by
      exact congrArg Fin.val heq
    have hdeq : G.dist s u = G.dist s v := by omega
    refine hno u ⟨v, ?_, huv.ne', ?_, huv⟩
    · intro hvs
      have h0 : G.dist s u = 0 := by rw [hdeq, hvs]; simp
      rw [hru.dist_eq_zero_iff] at h0
      exact huv.ne (h0.symm.trans hvs.symm)
    · rw [← hru.coe_dist_eq_edist, ← hrv.coe_dist_eq_edist, hdeq]

/-- In a bipartite graph every node is in exactly one round-set, namely `R_{d(s,v)}` for reachable
`v` (and in none if `v` is unreachable). -/
lemma mem_roundSet_iff_of_colorable (hb : G.IsBipartite) {v : V} {j : ℕ} :
    v ∈ roundSet G s j ↔ G.Reachable s v ∧ G.dist s v = j := by
  rw [← isFirstIn_iff]
  refine ⟨fun h => ?_, fun h => h.1⟩
  rw [isFirstIn_iff]
  have hp := mem_roundSet_iff.1 h
  exact ⟨reachable_of_mem_walkSet hp.1, (hp.eq_dist_of_colorable hb).symm⟩

/-- **Lemma 3.3** of [Hussak–Trehan, PODC'19] (for connected `G`): `G` has no ec nodes iff each
node is contained in exactly one round-set. -/
theorem lemma_3_3 (hc : G.Connected) :
    (∀ g, ¬ IsEC G s g) ↔ ∀ v, ∃! j, v ∈ roundSet G s j := by
  constructor
  · intro hno v
    have hb := (lemma_3_4 hc).2 hno
    refine ⟨G.dist s v, mem_roundSet_dist (hc.preconnected s v), fun j hj => ?_⟩
    exact ((mem_roundSet_iff_of_colorable hb).1 hj).2.symm
  · rintro h g hec
    obtain ⟨g', hg's, -, hd, hadj⟩ := hec
    have hr := hc.preconnected s g
    have hj : 1 ≤ G.dist s g := by
      by_contra h0
      have h0' : G.dist s g = 0 := by omega
      rw [hr.dist_eq_zero_iff] at h0'
      have : G.edist s g' = 0 := by rw [← hd, ← h0']; simp
      exact hg's (edist_eq_zero_iff.1 this).symm
    obtain ⟨h2, i, hi, h1⟩ :=
      lemma_3_2_iii hj (mem_distSet_iff.2 ⟨hr, rfl⟩) ⟨g', hg's, hadj.ne', hd, hadj⟩
    obtain ⟨j, -, hj'⟩ := h g
    have := (hj' _ h2).trans (hj' _ h1).symm
    omega

/-- In a connected non-bipartite graph every node receives the message in some round of each
parity. -/
lemma exists_mem_roundSet_of_not_bipartite (hc : G.Connected) (hb : ¬ G.IsBipartite) (v : V)
    (b : ℕ) : ∃ t, t % 2 = b % 2 ∧ v ∈ roundSet G s t := by
  obtain ⟨t, ht, hm⟩ := exists_mem_walkSet_of_not_colorable hc.preconnected hb s v b
  obtain ⟨t', -, ht', hp⟩ := exists_isParityDist hm
  exact ⟨t', by omega, mem_roundSet_iff.2 hp⟩

/-- In a bipartite graph, flooding has terminated after round `ecc(s)` (any graph whose component
of `s` has finite eccentricity). -/
lemma terminatesAfter_of_bipartite (hb : G.IsBipartite) {e : ℕ} (he : G.eccent s = e) :
    TerminatesAfter G s e := by
  intro t ht
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨-, rfl⟩ := (mem_roundSet_iff_of_colorable hb).1 hv
  exact absurd (dist_le_of_edist_le_natCast (he ▸ edist_le_eccent)) (by omega : ¬ G.dist s v ≤ e)

/-- In a finite graph, `R_e ≠ ∅` where `e = ecc(s)`: the farthest nodes receive the
message in round `e`. -/
lemma roundSet_eccent_nonempty [Finite V] {e : ℕ} (he : G.eccent s = e) :
    (roundSet G s e).Nonempty := by
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite s
  refine ⟨v, (lemma_3_2_i e).1 ?_⟩
  simp only [distSet, Set.mem_ofPred_eq]
  rw [hv, he]

/-- **Theorem 3.5** of [Hussak–Trehan, PODC'19]. Let `G` be a finite connected graph and `s` a node
of eccentricity `e`. Then flooding has terminated after round `e` iff `G` is bipartite. -/
theorem theorem_3_5 [Finite V] (hc : G.Connected) {e : ℕ} (he : G.eccent s = e) :
    TerminatesAfter G s e ↔ G.IsBipartite := by
  refine ⟨fun h => ?_, fun hb => terminatesAfter_of_bipartite hb he⟩
  by_contra hb
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite s
  have hr := hc.preconnected s v
  have hdv : G.dist s v = e := (edist_eq_natCast_iff.1 (hv.trans he)).2
  obtain ⟨t, ht, hm⟩ := exists_mem_roundSet_of_not_bipartite hc hb v (e + 1)
  have hle : e ≤ t := hdv ▸ dist_le_of_mem_roundSet hm
  have hne : t ≠ e := by omega
  rw [h t (by omega)] at hm
  exact hm

/-- Theorem 3.5, as an exact termination time: in a finite connected graph the termination time is
`e = ecc(s)` iff `G` is bipartite. -/
theorem theorem_3_5' [Finite V] (hc : G.Connected) {e : ℕ} (he : G.eccent s = e) :
    IsTerminationTime G s e ↔ G.IsBipartite := by
  rw [← theorem_3_5 hc he]
  exact ⟨fun h => h.2, fun h => ⟨roundSet_eccent_nonempty he, h⟩⟩

/-- **Lemma 3.6** of [Hussak–Trehan, PODC'19]. If `h² ∈ R_j` and `g` is a neighbour of `h`, then
`g² ∈ R_{j-1}`, `g² ∈ R_j` or `g² ∈ R_{j+1}`. -/
theorem lemma_3_6 {h g : V} {j : ℕ} (hh : IsSecondIn G s h j) (hadj : G.Adj h g) :
    IsSecondIn G s g (j - 1) ∨ IsSecondIn G s g j ∨ IsSecondIn G s g (j + 1) := by
  obtain ⟨hj, i, hij, hi⟩ := hh
  have hpj := mem_roundSet_iff.1 hj
  have hpi := mem_roundSet_iff.1 hi
  have hpar : i % 2 ≠ j % 2 := fun hp => by
    have := hpi.eq_of_mod_two_eq hpj hp; omega
  -- `a`: parity distance of `g` of parity `j + 1`; `b`: of parity `j`
  obtain ⟨a, ha, hapar, hpa⟩ := hpj.exists_adj hadj
  obtain ⟨b, hb, hbpar, hpb⟩ := hpi.exists_adj hadj
  have ha' : j ≤ a + 1 := hpj.le_of_mem (mem_walkSet_succ_of_adj hpa.1 hadj.symm) (by omega)
  have hb' : b ≤ j := by omega
  have hab : a ≠ b := by omega
  have hma := mem_roundSet_iff.2 hpa
  have hmb := mem_roundSet_iff.2 hpb
  rcases Nat.lt_or_ge a j with haj | haj
  · -- `a = j - 1`
    have ha1 : a = j - 1 := by omega
    rcases Nat.lt_or_ge b a with hba | hba
    · exact Or.inl ⟨ha1 ▸ hma, b, by omega, hmb⟩
    · have hbj : b = j := by omega
      exact Or.inr (Or.inl ⟨hbj ▸ hmb, a, by omega, hma⟩)
  · -- `a = j + 1`
    have ha1 : a = j + 1 := by omega
    exact Or.inr (Or.inr ⟨ha1 ▸ hma, b, by omega, hmb⟩)

/-- Upper bound behind Theorem 3.7: in a connected non-bipartite graph, every round in which `v`
receives the message is at most `e + d + 1`. (We bound the parity distances directly through an
ec edge, which is the content of the paper's iterated use of Lemma 3.6.) -/
lemma le_of_mem_roundSet_of_not_bipartite [Finite V] (hc : G.Connected) (hb : ¬ G.IsBipartite)
    {e : ℕ} (he : G.eccent s = e) {v : V} {t : ℕ} (hv : v ∈ roundSet G s t) :
    t ≤ e + G.diam + 1 := by
  have hp := mem_roundSet_iff.1 hv
  -- an ec edge `g – g'` with `d(s, g) = d(s, g')`
  have hno : ¬ ∀ g, ¬ IsEC G s g := fun h => hb ((lemma_3_4 hc).2 h)
  push Not at hno
  obtain ⟨g, g', -, -, hd, hadj⟩ := hno
  have hr := hc.preconnected s g
  have hr' := hc.preconnected s g'
  have hdd : G.dist s g = G.dist s g' := by
    have h1 := hr.coe_dist_eq_edist; have h2 := hr'.coe_dist_eq_edist
    rw [hd, ← h2] at h1; exact_mod_cast h1
  have hge : G.dist s g ≤ e := dist_le_of_edist_le_natCast (he ▸ edist_le_eccent)
  have := hc.nonempty
  have hfin : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.1 hc
  have hgv : G.dist g v ≤ G.diam := dist_le_diam hfin
  have hrv := hc.preconnected g v
  -- two walks `s → g → v` of lengths `d(s,g) + d(g,v)` and `d(s,g) + 1 + d(g,v)`
  have w1 := mem_walkSet_add hr.mem_walkSet_dist hrv.mem_walkSet_dist
  have w2 := mem_walkSet_add (mem_walkSet_succ_of_adj (hdd ▸ hr'.mem_walkSet_dist) hadj.symm)
    hrv.mem_walkSet_dist
  rcases Nat.mod_two_eq_zero_or_one (G.dist s g + G.dist g v + t) with h0 | h0
  · have := hp.le_of_mem w1 (by omega); omega
  · have := hp.le_of_mem w2 (by omega); omega

/-- **Theorem 3.7** of [Hussak–Trehan, PODC'19]. Let `G` be a finite connected non-bipartite graph
with diameter `d`, and let `s` have eccentricity `e`. Then flooding terminates after `T` rounds
with `e < T ≤ e + d + 1`. -/
theorem theorem_3_7 [Fintype V] (hc : G.Connected) (hb : ¬ G.IsBipartite) {e : ℕ}
    (he : G.eccent s = e) :
    ∃ T, IsTerminationTime G s T ∧ e < T ∧ T ≤ e + G.diam + 1 := by
  obtain ⟨T, -, hT⟩ := exists_isTerminationTime_lt (G := G) s
  refine ⟨T, hT, ?_, ?_⟩
  · by_contra hle
    exact hb ((theorem_3_5 hc he).1 (hT.2.mono (by omega)))
  · obtain ⟨v, hv⟩ := hT.1
    exact le_of_mem_roundSet_of_not_bipartite hc hb he hv

/-- The abstract's bound for bipartite graphs: termination time `e ≤ d`. -/
theorem terminationTime_le_diam [Finite V] (hc : G.Connected) (hb : G.IsBipartite) {T : ℕ}
    (hT : IsTerminationTime G s T) : T ≤ G.diam := by
  have := hc.nonempty
  have hfin : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.1 hc
  have he : G.eccent s ≠ ⊤ := ne_top_of_le_ne_top hfin eccent_le_ediam
  obtain ⟨e, he'⟩ := WithTop.ne_top_iff_exists.1 he
  have := hT.unique ((theorem_3_5' hc he'.symm).2 hb)
  subst this
  have h1 : G.eccent s ≤ G.diam := by
    rw [natCast_diam_eq_ediam_iff.2 hfin]; exact eccent_le_ediam
  rw [← he'] at h1
  exact ENat.natCast_le_natCast.1 h1

/-- The abstract's bound for non-bipartite graphs: termination time `≤ 2d + 1`. -/
theorem terminationTime_le_two_mul_diam_add_one [Fintype V] (hc : G.Connected)
    (hb : ¬ G.IsBipartite) {T : ℕ} (hT : IsTerminationTime G s T) : T ≤ 2 * G.diam + 1 := by
  have := hc.nonempty
  have hfin : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.1 hc
  have he : G.eccent s ≠ ⊤ := ne_top_of_le_ne_top hfin eccent_le_ediam
  obtain ⟨e, he'⟩ := WithTop.ne_top_iff_exists.1 he
  obtain ⟨T', hT', -, hle⟩ := theorem_3_7 hc hb he'.symm
  have := hT.unique hT'
  subst this
  have h1 : G.eccent s ≤ G.diam := by
    rw [natCast_diam_eq_ediam_iff.2 hfin]; exact eccent_le_ediam
  rw [← he'] at h1
  have : e ≤ G.diam := ENat.natCast_le_natCast.1 h1
  omega

end FloodingTermination
