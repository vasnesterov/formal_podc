import Papers.PODC2026.PLSTradeoff.BallCarving
import Papers.PODC2026.PLSTradeoff.Tradeoff

/-!
# Ball carving with random radii (Section 5.1)

Algorithm `A` of Section 5.1, for a fixed graph `G`, parameter `t ≥ 1` and `K = t ⌈log₂ n⌉`
(the paper's `t log n`). The nodes are processed in increasing identifier order; node `w` has a
radius index `R w` and radius `rad K (R w) = 2K + 2 + 2 R w`. When `w` is processed, the alive set
is `alive w` (the nodes not yet clustered); if some alive node is within distance `2K` of `w`
(`NearAlive`) and the ball of radius `r = rad K (R w)` is not expanding,
`t |B_r(w) ∩ A| ≤ (t+1) |B_{r-2}(w) ∩ A|` (`Ok`), then `w` is *taken* and its cluster is
`B_r(w) ∩ A`.

Rather than simulating the loop, `taken` is defined by well-founded recursion on the identifier
order, and the cluster of `u` is described by its centre `cen u`, the least taken `w` with
`d(w, u) ≤ rad K (R w)` — exactly the paper's `FindMyCluster` (Lemmas 5.8/5.9 become the
characterization `cen_eq_iff`).

Results:
* `isDegenerate_of_allClustered` (Lemma 5.3): if every node is clustered, the clusters form an
  ordered partition with `1/t`-cluster-degeneracy and weak diameter `≤ 2 rad K M`, hence a
  `(16K + 12, 1/t)`-TS partition for radius indices `< M = 3K + 3`.
* `card_bad_le` (Lemma 5.1): at most `K` radius indices make a step fail.
* `card_not_allClustered` (Lemma 5.2, counting version): on a connected graph, at most half of
  all radius assignments `V → Fin (3K+3)` leave some node unclustered.
* `exists_good_family` (Lemma 5.5, Newman's trick): there is a family of `n² + 1` radius
  assignments such that every connected graph on `V` has a good one.

Deviations: radius indices range over `Fin (3K + 3)` (radii `2K+2, …, 8K+6`) instead of the
paper's `{2K+2, …, 8K}`, so that `n = 1` (`K = 0`) is not degenerate; we only need a failure
probability `≤ 1/2` per graph (with `n² + 1` samples) instead of the paper's `1/n` with `n²`
samples.
-/

namespace PLSTradeoff

open SimpleGraph Finset Classical

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The radius with index `x`. -/
def rad (K x : ℕ) : ℕ := 2 * K + 2 + 2 * x

section Process

variable (G : SimpleGraph V) (t K : ℕ) (R : V → ℕ)

/-- `|B_r(w) ∩ A|`. -/
noncomputable def ballCount (A : Set V) (w : V) (r : ℕ) : ℕ :=
  {u | u ∈ A ∧ G.edist w u ≤ r}.ncard

/-- The non-expansion test (Eq. (1)): `|B_r(w) ∩ A| ≤ (1 + 1/t) |B_{r-2}(w) ∩ A|`. -/
def Ok (A : Set V) (w : V) (r : ℕ) : Prop :=
  t * ballCount G A w r ≤ (t + 1) * ballCount G A w (r - 2)

/-- Some node of `A` is within distance `2K` of `w`. -/
def NearAlive (A : Set V) (w : V) : Prop := ∃ u ∈ A, G.edist w u ≤ (2 * K : ℕ)

/-- `taken w`: the cluster of `w` is taken when `w` is processed. -/
noncomputable def taken : V → Prop :=
  wellFounded_lt.fix (fun w rec =>
    NearAlive G K {u | ¬ ∃ w', ∃ h : w' < w, rec w' h ∧ G.edist w' u ≤ rad K (R w')} w ∧
    Ok G t {u | ¬ ∃ w', ∃ h : w' < w, rec w' h ∧ G.edist w' u ≤ rad K (R w')} w (rad K (R w)))

/-- The alive nodes when `w` is processed. -/
def alive (w : V) : Set V :=
  {u | ¬ ∃ w', w' < w ∧ taken G t K R w' ∧ G.edist w' u ≤ rad K (R w')}

lemma taken_iff (w : V) :
    taken G t K R w ↔ NearAlive G K (alive G t K R w) w ∧
      Ok G t (alive G t K R w) w (rad K (R w)) := by
  have h : alive G t K R w =
      {u | ¬ ∃ w', ∃ _ : w' < w, taken G t K R w' ∧ G.edist w' u ≤ rad K (R w')} := by
    ext u; simp only [alive, Set.mem_ofPred_eq, exists_prop]
  rw [h, taken, WellFounded.fix_eq]

/-- `u` belongs to some taken ball. -/
def Clustered (u : V) : Prop := ∃ w, taken G t K R w ∧ G.edist w u ≤ rad K (R w)

/-- Every node is clustered. -/
def AllClustered : Prop := ∀ u, Clustered G t K R u

/-- The centre of the cluster of `u` (`FindMyCluster`): the least taken `w` whose ball contains
`u` (junk value `u` if there is none). -/
noncomputable def cen (u : V) : V :=
  if h : Clustered G t K R u then
    (univ.filter (fun w => taken G t K R w ∧ G.edist w u ≤ rad K (R w))).min'
      (by obtain ⟨w, hw⟩ := h; exact ⟨w, by simpa using hw⟩)
  else u

variable {G t K R}

lemma cen_spec {u : V} (h : Clustered G t K R u) :
    taken G t K R (cen G t K R u) ∧ G.edist (cen G t K R u) u ≤ rad K (R (cen G t K R u)) ∧
      ∀ w, taken G t K R w → G.edist w u ≤ rad K (R w) → cen G t K R u ≤ w := by
  unfold cen
  rw [dite_eq_left h]
  set s := univ.filter (fun w => taken G t K R w ∧ G.edist w u ≤ rad K (R w))
  have hs : s.Nonempty := by obtain ⟨w, hw⟩ := h; exact ⟨w, by simpa [s] using hw⟩
  have hmem := s.min'_mem hs
  simp only [s, mem_filter, mem_univ, true_and] at hmem
  exact ⟨hmem.1, hmem.2, fun w hw hwu => s.min'_le w (by simp [s, hw, hwu])⟩

/-- Lemma 5.9 (characterization of the clusters): for a taken `w`, `u` has centre `w` iff `u`
is alive at `w` and lies in the ball of `w`. -/
lemma cen_eq_iff {w u : V} (hw : taken G t K R w) :
    (Clustered G t K R u ∧ cen G t K R u = w) ↔
      (u ∈ alive G t K R w ∧ G.edist w u ≤ rad K (R w)) := by
  constructor
  · rintro ⟨hc, rfl⟩
    obtain ⟨-, h2, h3⟩ := cen_spec hc
    refine ⟨fun ⟨w', hw'lt, hw't, hw'u⟩ => ?_, h2⟩
    exact absurd (h3 w' hw't hw'u) (not_le.2 hw'lt)
  · rintro ⟨hal, hwu⟩
    have hc : Clustered G t K R u := ⟨w, hw, hwu⟩
    obtain ⟨h1, h2, h3⟩ := cen_spec hc
    refine ⟨hc, le_antisymm (h3 w hw hwu) ?_⟩
    by_contra hlt
    push Not at hlt
    exact hal ⟨_, hlt, h1, h2⟩

/-- A clustered node whose centre is after `w` is alive at `w`. -/
lemma mem_alive_of_lt_cen {w u : V} (hc : Clustered G t K R u) (hlt : w < cen G t K R u) :
    u ∈ alive G t K R w := by
  rintro ⟨w', hw'lt, hw't, hw'u⟩
  exact absurd ((cen_spec hc).2.2 w' hw't hw'u) (not_le.2 (hw'lt.trans hlt))

end Process

/-! ### Lemma 5.3: the output is a TS partition -/

section Partition

variable {G : SimpleGraph V} {t K : ℕ} {R : V → ℕ}

/-- The index of a cluster: the number of identifiers below its centre. -/
noncomputable def cidx (G : SimpleGraph V) (t K : ℕ) (R : V → ℕ) (u : V) : ℕ :=
  (univ.filter (· < cen G t K R u)).card

lemma card_lt_lt {a b : V} (h : a < b) :
    (univ.filter (· < a)).card < (univ.filter (· < b)).card := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact hx.trans h
  · have := hsub (by simp [h] : a ∈ univ.filter (· < b))
    simp at this

lemma cidx_eq_iff {a b : V} : cidx G t K R a = cidx G t K R b ↔ cen G t K R a = cen G t K R b := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd h (card_lt_lt hlt).ne
    · exact absurd h (card_lt_lt hlt).ne'
  · intro h; simp [cidx, h]

lemma cidx_lt_iff {a b : V} : cidx G t K R a < cidx G t K R b ↔ cen G t K R a < cen G t K R b := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · exact absurd h (not_lt.2 (card_lt_lt hlt).le)
    · exact absurd h (by simp [cidx, heq])
  · exact card_lt_lt

/-- **Lemma 5.3** of [Filtser–Fischer, PODC 2026] (degeneracy form): if all nodes are clustered,
the clusters, ordered by centre, have `1/t`-cluster-degeneracy, and radius indices `≤ Mx` give
weak diameter `≤ 2 rad K Mx`. -/
theorem isDegenerate_of_allClustered (ht : 1 ≤ t) (hall : AllClustered G t K R) :
    ClusterDegenerate G (cidx G t K R) (1 / t) := by
  intro i
  by_cases hne : ∃ v₀, cidx G t K R v₀ = i
  swap
  · push Not at hne
    have : {v | cidx G t K R v = i} = ∅ := by ext v; simp [hne v]
    have h2 : {v | cidx G t K R v = i ∧ ∃ u, i < cidx G t K R u ∧ G.edist v u ≤ 2} = ∅ := by
      ext v; simp [hne v]
    rw [this, h2]; simp
  obtain ⟨v₀, rfl⟩ := hne
  set w := cen G t K R v₀
  have hwt : taken G t K R w := (cen_spec (hall v₀)).1
  set A := alive G t K R w
  set r := rad K (R w)
  have hok := ((taken_iff G t K R w).1 hwt).2
  -- the cluster is `B_r(w) ∩ A`
  have hcl : {v | cidx G t K R v = cidx G t K R v₀} = {u | u ∈ A ∧ G.edist w u ≤ r} := by
    ext v
    simp only [Set.mem_ofPred_eq, cidx_eq_iff]
    rw [← cen_eq_iff hwt]
    exact ⟨fun h => ⟨hall v, h⟩, fun h => h.2⟩
  -- close-to-boundary nodes lie in `(B_r \ B_{r-2}) ∩ A`
  have hclose : {v | cidx G t K R v = cidx G t K R v₀ ∧
      ∃ u, cidx G t K R v₀ < cidx G t K R u ∧ G.edist v u ≤ 2} ⊆
      {u | u ∈ A ∧ G.edist w u ≤ r} \ {u | u ∈ A ∧ G.edist w u ≤ (r - 2 : ℕ)} := by
    rintro v ⟨hv, u, hu, hvu⟩
    have hv' : v ∈ {u | u ∈ A ∧ G.edist w u ≤ r} := hcl ▸ hv
    refine ⟨hv', fun ⟨_, hwv⟩ => ?_⟩
    rw [cidx_lt_iff] at hu
    have huA : u ∈ A := mem_alive_of_lt_cen (hall u) hu
    have hr2 : 2 ≤ r := by simp only [r, rad]; omega
    have hwu : G.edist w u ≤ r := by
      have := edist_le_natCast_add hwv hvu
      exact this.trans (by exact_mod_cast (by omega : r - 2 + 2 ≤ r))
    have := ((cen_eq_iff hwt).2 ⟨huA, hwu⟩).2
    exact absurd this hu.ne'
  have hsub : {u | u ∈ A ∧ G.edist w u ≤ (r - 2 : ℕ)} ⊆ {u | u ∈ A ∧ G.edist w u ≤ r} :=
    fun u hu => ⟨hu.1, hu.2.trans (by exact_mod_cast Nat.sub_le r 2)⟩
  have hcard := Set.ncard_le_ncard hclose (Set.toFinite _)
  rw [Set.ncard_sdiff hsub (Set.toFinite _)] at hcard
  rw [hcl]
  have hok' : t * ballCount G A w r ≤ (t + 1) * ballCount G A w (r - 2) := hok
  have hba : ballCount G A w (r - 2) ≤ ballCount G A w r :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  unfold ballCount at hok' hba
  generalize {u | u ∈ A ∧ G.edist w u ≤ r}.ncard = a at *
  generalize {u | u ∈ A ∧ G.edist w u ≤ (r - 2 : ℕ)}.ncard = b at *
  generalize {v | cidx G t K R v = cidx G t K R v₀ ∧
      ∃ u, cidx G t K R v₀ < cidx G t K R u ∧ G.edist v u ≤ 2}.ncard = c at *
  have htc : t * c ≤ a := by
    have e1 : t * a ≤ t * b + b := by rw [add_mul, one_mul] at hok'; exact hok'
    have e2 : t * (a - b) = t * a - t * b := Nat.mul_sub t a b
    have e3 : t * c ≤ t * (a - b) := Nat.mul_le_mul_left _ hcard
    omega
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ htpos]
  have : ((t * c : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast htc
  push_cast at this
  linarith

lemma isWeaklyBounded_of_allClustered {Mx : ℕ} (hR : ∀ w, R w ≤ Mx)
    (hall : AllClustered G t K R) : WeaklyBounded G (cidx G t K R) (2 * rad K Mx) := by
  intro a b hab
  rw [cidx_eq_iff] at hab
  obtain ⟨-, ha, -⟩ := cen_spec (hall a)
  obtain ⟨-, hb, -⟩ := cen_spec (hall b)
  rw [hab] at ha
  have hr : rad K (R (cen G t K R b)) ≤ rad K Mx := by simp only [rad]; have := hR (cen G t K R b); omega
  rw [SimpleGraph.edist_comm] at ha
  have := edist_le_natCast_add ha hb
  exact this.trans (by exact_mod_cast (by omega))

end Partition

/-! ### Lemma 5.1: few bad radii -/

section Lemma51

variable {G : SimpleGraph V} {t K : ℕ}

omit [LinearOrder V] in
lemma ballCount_mono {A : Set V} {w : V} {r r' : ℕ} (h : r ≤ r') :
    ballCount G A w r ≤ ballCount G A w r' :=
  Set.ncard_le_ncard (fun u hu => ⟨hu.1, hu.2.trans (by exact_mod_cast h)⟩) (Set.toFinite _)

omit [LinearOrder V] in
lemma ballCount_le_card {A : Set V} {w : V} {r : ℕ} : ballCount G A w r ≤ Fintype.card V := by
  unfold ballCount
  exact (Set.ncard_le_ncard (Set.subset_univ _)).trans
    (by rw [Set.ncard_univ, Nat.card_eq_fintype_card])

omit [LinearOrder V] in
/-- **Lemma 5.1** of [Filtser–Fischer, PODC 2026]: if some alive node is within distance `2K` of
`w`, at most `K = t ⌈log₂ n⌉` radius indices fail the non-expansion test. -/
theorem card_bad_le (ht : 1 ≤ t) (hK : K = t * Nat.clog 2 (Fintype.card V)) {A : Set V} {w : V}
    (hA : NearAlive G K A w) (M : ℕ) :
    ((range M).filter (fun x => ¬ Ok G t A w (rad K x))).card ≤ K := by
  set n := Fintype.card V
  let g : ℕ → ℕ := fun k => ballCount G A w (2 * K + 2 * k)
  let b : ℕ → ℕ := fun k => ((range k).filter (fun x => ¬ Ok G t A w (rad K x))).card
  have hg0 : 1 ≤ g 0 := by
    obtain ⟨u, hu, hwu⟩ := hA
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    have : {v | v ∈ A ∧ G.edist w v ≤ (2 * K + 2 * 0 : ℕ)}.ncard = 0 := h0
    rw [Set.ncard_eq_zero (Set.toFinite _)] at this
    have hu' : u ∈ {v | v ∈ A ∧ G.edist w v ≤ (2 * K + 2 * 0 : ℕ)} := ⟨hu, by simpa using hwu⟩
    rw [this] at hu'; exact hu'
  have hok_iff : ∀ x, Ok G t A w (rad K x) ↔ t * g (x + 1) ≤ (t + 1) * g x := by
    intro x
    simp only [Ok, g, rad]
    have h1 : 2 * K + 2 + 2 * x = 2 * K + 2 * (x + 1) := by ring
    have h2 : 2 * K + 2 * (x + 1) - 2 = 2 * K + 2 * x := by omega
    rw [h1, h2]
  have key : ∀ k, (t + 1) ^ b k * g 0 ≤ t ^ b k * g k := by
    intro k
    induction k with
    | zero => simp [b]
    | succ k ih =>
      have hmono : g k ≤ g (k + 1) := ballCount_mono (by omega)
      by_cases hk : Ok G t A w (rad K k)
      · have hb : b (k + 1) = b k := by
          simp only [b, range_add_one, filter_insert, hk, not_true_eq_false, ite_false]
        rw [hb]
        exact ih.trans (Nat.mul_le_mul_left _ hmono)
      · have hb : b (k + 1) = b k + 1 := by
          simp only [b, range_add_one, filter_insert, hk, not_false_eq_true, ite_true]
          rw [card_insert_of_notMem (by simp)]
        rw [hb]
        have hk' := (not_congr (hok_iff k)).1 hk
        push Not at hk'
        calc (t + 1) ^ (b k + 1) * g 0 = (t + 1) * ((t + 1) ^ b k * g 0) := by ring
          _ ≤ (t + 1) * (t ^ b k * g k) := Nat.mul_le_mul_left _ ih
          _ = t ^ b k * ((t + 1) * g k) := by ring
          _ ≤ t ^ b k * (t * g (k + 1)) := Nat.mul_le_mul_left _ hk'.le
          _ = t ^ (b k + 1) * g (k + 1) := by ring
  by_contra hcon
  push Not at hcon
  have hbM : K + 1 ≤ b M := hcon
  have hn1 : 1 ≤ n := by obtain ⟨u, -, -⟩ := hA; exact Fintype.card_pos_iff.2 ⟨u⟩
  have hlt := pow_mul_lt_succ_pow ht hn1 (Nat.le_pow_clog (by norm_num) n)
  rw [← hK] at hlt
  have hgM : g M ≤ n := ballCount_le_card
  have h1 := key M
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hbM
  rw [hd] at h1
  have : t ^ (K + 1 + d) * n < (t + 1) ^ (K + 1 + d) := by
    calc t ^ (K + 1 + d) * n = t ^ d * (t ^ (K + 1) * n) := by ring
      _ < t ^ d * (t + 1) ^ (K + 1) := by
        apply Nat.mul_lt_mul_of_pos_left hlt (pow_pos (by omega) d)
      _ ≤ (t + 1) ^ d * (t + 1) ^ (K + 1) := by
        gcongr; omega
      _ = (t + 1) ^ (K + 1 + d) := by ring
  have : (t + 1) ^ (K + 1 + d) ≤ t ^ (K + 1 + d) * n :=
    calc (t + 1) ^ (K + 1 + d) ≤ (t + 1) ^ (K + 1 + d) * g 0 := Nat.le_mul_of_pos_right _ hg0
      _ ≤ t ^ (K + 1 + d) * g M := h1
      _ ≤ t ^ (K + 1 + d) * n := Nat.mul_le_mul_left _ hgM
  omega

end Lemma51

/-! ### Lemma 5.2: most radius assignments cluster every node -/

section Lemma52

variable {G : SimpleGraph V} {t K : ℕ}

/-- `taken w` depends only on the radius indices of the nodes `≤ w`. -/
lemma taken_congr {R R' : V → ℕ} (w : V) (h : ∀ z ≤ w, R z = R' z) :
    taken G t K R w ↔ taken G t K R' w := by
  induction w using WellFoundedLT.induction with
  | _ w ih =>
    have hal : alive G t K R w = alive G t K R' w := by
      ext u
      simp only [alive, Set.mem_ofPred_eq]
      refine not_congr ⟨fun ⟨w', h1, h2, h3⟩ => ⟨w', h1, ?_, ?_⟩,
        fun ⟨w', h1, h2, h3⟩ => ⟨w', h1, ?_, ?_⟩⟩
      · exact (ih w' h1 (fun z hz => h z (hz.trans h1.le))).1 h2
      · rwa [← h w' h1.le]
      · exact (ih w' h1 (fun z hz => h z (hz.trans h1.le))).2 h2
      · rwa [h w' h1.le]
    rw [taken_iff, taken_iff, hal, h w le_rfl]

lemma alive_congr {R R' : V → ℕ} (w : V) (h : ∀ z < w, R z = R' z) :
    alive G t K R w = alive G t K R' w := by
  ext u
  simp only [alive, Set.mem_ofPred_eq]
  refine not_congr ⟨fun ⟨w', h1, h2, h3⟩ => ⟨w', h1, ?_, ?_⟩,
    fun ⟨w', h1, h2, h3⟩ => ⟨w', h1, ?_, ?_⟩⟩
  · exact (taken_congr w' (fun z hz => h z (hz.trans_lt h1))).1 h2
  · rwa [← h w' h1]
  · exact (taken_congr w' (fun z hz => h z (hz.trans_lt h1))).2 h2
  · rwa [h w' h1]

/-- Step `w` fails although an alive node is near `w`. -/
def Bad (G : SimpleGraph V) (t K : ℕ) (R : V → ℕ) (w : V) : Prop :=
  NearAlive G K (alive G t K R w) w ∧ ¬ Ok G t (alive G t K R w) w (rad K (R w))

lemma bad_congr {R R' : V → ℕ} (w : V) (h : ∀ z ≤ w, R z = R' z) :
    Bad G t K R w ↔ Bad G t K R' w := by
  rw [Bad, Bad, alive_congr w (fun z hz => h z hz.le), h w le_rfl]

/-- An unclustered node makes every step `w` with `d(w, u) ≤ 2K` fail. -/
lemma bad_of_not_clustered {R : V → ℕ} {u : V} (hu : ¬ Clustered G t K R u) {w : V}
    (hw : G.edist w u ≤ (2 * K : ℕ)) : Bad G t K R w := by
  have hal : u ∈ alive G t K R w := fun ⟨w', _, h2, h3⟩ => hu ⟨w', h2, h3⟩
  refine ⟨⟨u, hal, hw⟩, fun hok => hu ⟨w, (taken_iff G t K R w).2 ⟨⟨u, hal, hw⟩, hok⟩,
    hw.trans (by simp only [rad]; exact_mod_cast (by omega))⟩⟩

-- CSLib candidate
/-- Fibre counting: if `A` does not depend on coordinate `w`, and for every `R` at most `c`
values of coordinate `w` satisfy `B`, then `M |{A ∧ B}| ≤ c |{A}|`. -/
lemma card_and_le_fiber {M : ℕ} (w : V) (A B : (V → Fin M) → Prop)
    (hA : ∀ R x, A (Function.update R w x) ↔ A R) (c : ℕ)
    (hB : ∀ R, (univ.filter (fun x => B (Function.update R w x))).card ≤ c) :
    M * (univ.filter (fun R => A R ∧ B R)).card ≤ c * (univ.filter A).card := by
  let f : (V → Fin M) → ℕ := fun R => if A R ∧ B R then 1 else 0
  let e : (V → Fin M) × Fin M ≃ (V → Fin M) × Fin M :=
    { toFun := fun p => (Function.update p.1 w p.2, p.1 w)
      invFun := fun p => (Function.update p.1 w p.2, p.1 w)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have h1 : ∑ p : (V → Fin M) × Fin M, f (Function.update p.1 w p.2) =
      M * (univ.filter (fun R => A R ∧ B R)).card := by
    have : ∑ p : (V → Fin M) × Fin M, f (Function.update p.1 w p.2) =
        ∑ p : (V → Fin M) × Fin M, f p.1 := Equiv.sum_comp e (fun p => f p.1)
    rw [this, Fintype.sum_prod_type]
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.card_filter]
  have h2 : ∑ p : (V → Fin M) × Fin M, f (Function.update p.1 w p.2) ≤
      c * (univ.filter A).card := by
    rw [Fintype.sum_prod_type]
    have : ∀ R : V → Fin M, ∑ x : Fin M, f (Function.update R w x) =
        if A R then (univ.filter (fun x => B (Function.update R w x))).card else 0 := by
      intro R
      by_cases hR : A R
      · simp only [f, hA, hR, true_and, ite_true, Finset.card_filter]
      · simp [f, hA, hR]
    simp only [this]
    rw [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro R _
    by_cases hR : A R
    · simp only [hR, ite_true, mul_one]; exact hB R
    · simp [hR]
  omega

-- CSLib candidate
/-- Iterated fibre counting along the identifier order: if each `bad w` depends only on the
coordinates `≤ w` and at most a third of the values of coordinate `w` make it hold, then at most a
`3^{-|S|}` fraction of all `R` make every `bad w`, `w ∈ S`, hold. -/
lemma card_all_bad_le {M : ℕ} (hM : 0 < M) (bad : V → (V → Fin M) → Prop)
    (hdep : ∀ w R R', (∀ z ≤ w, R z = R' z) → (bad w R ↔ bad w R'))
    (hfib : ∀ w R, 3 * (univ.filter (fun x => bad w (Function.update R w x))).card ≤ M)
    (S : Finset V) :
    3 ^ S.card * (univ.filter (fun R : V → Fin M => ∀ w ∈ S, bad w R)).card ≤
      M ^ Fintype.card V := by
  induction S using Finset.induction_on_max with
  | empty =>
    simp only [card_empty, pow_zero, one_mul]
    refine (card_filter_le _ _).trans (by simp)
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has]
    have hA : ∀ R x, (∀ w ∈ s, bad w (Function.update R a x)) ↔ (∀ w ∈ s, bad w R) := by
      intro R x
      refine forall₂_congr fun w hw => hdep w _ _ (fun z hz => ?_)
      rw [Function.update_of_ne (ne_of_lt (hz.trans_lt (hlt w hw)))]
    have hf := card_and_le_fiber a (fun R => ∀ w ∈ s, bad w R) (bad a) hA
      (M / 3) (fun R => by have := hfib a R; omega)
    have heq : univ.filter (fun R : V → Fin M => ∀ w ∈ insert a s, bad w R) =
        univ.filter (fun R => (∀ w ∈ s, bad w R) ∧ bad a R) := by
      ext R; simp [and_comm]
    rw [heq]
    set X := (univ.filter (fun R : V → Fin M => (∀ w ∈ s, bad w R) ∧ bad a R)).card with hX
    set Y := (univ.filter (fun R : V → Fin M => ∀ w ∈ s, bad w R)).card with hY
    have h3 : 3 * (M / 3) ≤ M := Nat.mul_div_le M 3
    have h4 : 3 * X ≤ Y := by
      apply Nat.le_of_mul_le_mul_left _ hM
      have hf' : M * X ≤ M / 3 * Y := by rw [hX, hY]; convert hf
      have e1 := Nat.mul_le_mul_left 3 hf'
      have e2 := Nat.mul_le_mul_right Y h3
      nlinarith
    have h5 := Nat.mul_le_mul_left (3 ^ s.card) h4
    calc 3 ^ (s.card + 1) * X = 3 ^ s.card * (3 * X) := by ring
      _ ≤ 3 ^ s.card * Y := h5
      _ ≤ M ^ Fintype.card V := ih

-- CSLib candidate
omit [LinearOrder V] in
/-- In a connected graph the ball of radius `k` has at least `min(n, k+1)` nodes. -/
lemma card_ball_ge (hG : G.Connected) (u : V) (k : ℕ) :
    min (Fintype.card V) (k + 1) ≤ (univ.filter (fun w => G.edist u w ≤ k)).card := by
  by_cases h : ∀ w, G.edist u w ≤ k
  · rw [filter_true_of_mem (fun w _ => h w), card_univ]; exact min_le_left _ _
  · push Not at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨d, hd⟩ : ∃ d : ℕ, G.edist u w = d :=
      ENat.ne_top_iff_exists.1 (edist_ne_top_iff_reachable.2 (hG.preconnected u w)) |>.imp fun _ h => h.symm
    have hkd : k < d := by exact_mod_cast hd ▸ hw
    have hex : ∀ i ≤ d, ∃ x, G.edist u x = (d - i : ℕ) := by
      intro i hi
      induction i with
      | zero => exact ⟨w, by simpa using hd⟩
      | succ i ih =>
        obtain ⟨x, hx⟩ := ih (by omega)
        have : d - i = (d - (i + 1)) + 1 := by omega
        rw [this] at hx
        obtain ⟨y, hy, -⟩ := exists_adj_of_edist_eq_succ hx
        exact ⟨y, hy⟩
    choose f hf using fun j : Fin (k + 1) => hex (d - j) (by omega)
    have hf' : ∀ j : Fin (k + 1), G.edist u (f j) = j := by
      intro j; rw [hf j]; congr 1; omega
    have hinj : Function.Injective f := by
      intro a b hab
      have := (hf' a).symm.trans (hab ▸ hf' b)
      exact Fin.ext (by exact_mod_cast this)
    have : (univ.image f) ⊆ univ.filter (fun w => G.edist u w ≤ k) := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.1 hx
      simp only [mem_filter, mem_univ, true_and, hf' j]
      exact_mod_cast Nat.lt_succ_iff.1 j.isLt
    calc min (Fintype.card V) (k + 1) ≤ k + 1 := min_le_right _ _
      _ = (univ.image f).card := by rw [card_image_of_injective _ hinj, card_univ,
          Fintype.card_fin]
      _ ≤ _ := card_le_card this

lemma two_mul_le_three_pow (n : ℕ) : 2 * n ≤ 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => have := Nat.one_le_pow n 3 (by norm_num); rw [pow_succ]; omega

/-- **Lemma 5.2** of [Filtser–Fischer, PODC 2026] (counting form): on a connected graph, at most
half of all radius assignments `R : V → Fin (3K+3)` leave some node unclustered. -/
theorem card_not_allClustered (hG : G.Connected) (ht : 1 ≤ t)
    (hK : K = t * Nat.clog 2 (Fintype.card V)) :
    2 * (univ.filter (fun R : V → Fin (3 * K + 3) =>
        ¬ AllClustered G t K (fun v => (R v : ℕ)))).card ≤
      (3 * K + 3) ^ Fintype.card V := by
  set n := Fintype.card V
  set M := 3 * K + 3
  set N := M ^ n
  let bad : V → (V → Fin M) → Prop := fun w R => Bad G t K (fun v => (R v : ℕ)) w
  have hdep : ∀ w R R', (∀ z ≤ w, R z = R' z) → (bad w R ↔ bad w R') :=
    fun w R R' h => bad_congr w (fun z hz => by simp [h z hz])
  have hfib : ∀ w R, 3 * (univ.filter (fun x => bad w (Function.update R w x))).card ≤ M := by
    intro w R
    have hal : ∀ x : Fin M, alive G t K (fun v => (Function.update R w x v : ℕ)) w =
        alive G t K (fun v => (R v : ℕ)) w :=
      fun x => alive_congr w (fun z hz => by simp [Function.update_of_ne hz.ne])
    by_cases hna : NearAlive G K (alive G t K (fun v => (R v : ℕ)) w) w
    · have hsub : (univ.filter (fun x => bad w (Function.update R w x))).map Fin.valEmbedding ⊆
          (range M).filter (fun x => ¬ Ok G t (alive G t K (fun v => (R v : ℕ)) w) w (rad K x)) := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
        simp only [mem_filter, mem_univ, true_and, bad, Bad, hal] at hx
        simp only [mem_filter, mem_range, Fin.valEmbedding_apply, x.isLt, true_and]
        simpa using hx.2
      have := (card_le_card hsub).trans (card_bad_le ht hK hna M)
      rw [card_map] at this
      omega
    · have : univ.filter (fun x => bad w (Function.update R w x)) = ∅ := by
        ext x; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, bad, Bad, hal]
        exact fun h => hna h.1
      rw [this]; simp
  -- per-node bound
  have hnode : ∀ u, 2 * n * (univ.filter (fun R : V → Fin M =>
      ¬ Clustered G t K (fun v => (R v : ℕ)) u)).card ≤ N := by
    intro u
    set S := univ.filter (fun w => G.edist u w ≤ (2 * K : ℕ))
    have hall := card_all_bad_le (by omega) bad hdep hfib S
    have hsub : univ.filter (fun R : V → Fin M => ¬ Clustered G t K (fun v => (R v : ℕ)) u) ⊆
        univ.filter (fun R : V → Fin M => ∀ w ∈ S, bad w R) := by
      intro R hR
      simp only [mem_filter, mem_univ, true_and] at hR ⊢
      intro w hw
      simp only [S, mem_filter, mem_univ, true_and] at hw
      rw [SimpleGraph.edist_comm] at hw
      exact bad_of_not_clustered hR hw
    have hS := card_ball_ge hG u (2 * K)
    have h3 : 2 * n ≤ 3 ^ S.card := by
      rcases le_total n (2 * K + 1) with h | h
      · rw [min_eq_left h] at hS
        exact (two_mul_le_three_pow n).trans (Nat.pow_le_pow_right (by norm_num) hS)
      · rw [min_eq_right h] at hS
        have hL : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
        have hKL : Nat.clog 2 n ≤ K := by rw [hK]; exact Nat.le_mul_of_pos_left _ ht
        calc 2 * n ≤ 2 * 2 ^ Nat.clog 2 n := by omega
          _ ≤ 2 * 2 ^ K := by gcongr
          _ ≤ 3 ^ (2 * K + 1) := by
            rw [pow_succ, pow_mul]
            have : 2 ^ K ≤ 9 ^ K := Nat.pow_le_pow_left (by norm_num) K
            norm_num; omega
          _ ≤ 3 ^ S.card := Nat.pow_le_pow_right (by norm_num) hS
    calc 2 * n * _ ≤ 3 ^ S.card * _ := Nat.mul_le_mul_right _ h3
      _ ≤ 3 ^ S.card * (univ.filter (fun R : V → Fin M => ∀ w ∈ S, bad w R)).card :=
          Nat.mul_le_mul_left _ (card_le_card hsub)
      _ ≤ N := hall
  -- union bound
  have hunion : univ.filter (fun R : V → Fin M => ¬ AllClustered G t K (fun v => (R v : ℕ))) ⊆
      univ.biUnion (fun u => univ.filter (fun R : V → Fin M =>
        ¬ Clustered G t K (fun v => (R v : ℕ)) u)) := by
    intro R hR
    simp only [mem_filter, mem_univ, true_and, AllClustered, not_forall] at hR
    obtain ⟨u, hu⟩ := hR
    exact mem_biUnion.2 ⟨u, mem_univ _, by simpa using hu⟩
  have hsum := (card_le_card hunion).trans card_biUnion_le
  by_cases hn : n = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hn
    have : univ.filter (fun R : V → Fin M => ¬ AllClustered G t K (fun v => (R v : ℕ))) = ∅ := by
      ext R; simp [AllClustered]
    rw [this]; simp
  · have : n * (2 * ∑ u, (univ.filter (fun R : V → Fin M =>
        ¬ Clustered G t K (fun v => (R v : ℕ)) u)).card) ≤ n * N := by
      rw [mul_sum, mul_sum]
      calc ∑ i, n * (2 * _) = ∑ i : V, 2 * n * (univ.filter (fun R : V → Fin M =>
            ¬ Clustered G t K (fun v => (R v : ℕ)) i)).card := by
              apply sum_congr rfl; intro i _; ring
        _ ≤ ∑ _i : V, N := sum_le_sum (fun u _ => hnode u)
        _ = n * N := by simp [n]
    have := Nat.le_of_mul_le_mul_left this (Nat.pos_of_ne_zero hn)
    omega

/-- **Lemma 5.5** of [Filtser–Fischer, PODC 2026] (Newman's trick): there is a family of
`n² + 1` radius assignments such that every connected graph on `V` has a good one (one that
clusters every node). -/
theorem exists_good_family (ht : 1 ≤ t) (hK : K = t * Nat.clog 2 (Fintype.card V)) :
    ∃ F : Fin (Fintype.card V * Fintype.card V + 1) → V → Fin (3 * K + 3),
      ∀ G : SimpleGraph V, G.Connected → ∃ i, AllClustered G t K (fun v => (F i v : ℕ)) := by
  set n := Fintype.card V
  set M := 3 * K + 3
  set m := n * n + 1
  set N := (univ : Finset (V → Fin M)).card
  by_contra hcon
  push Not at hcon
  let Bad' : SimpleGraph V → Finset (V → Fin M) := fun G =>
    univ.filter (fun R => ¬ AllClustered G t K (fun v => (R v : ℕ)))
  have hcover : (univ : Finset (Fin m → V → Fin M)) ⊆
      (univ.filter (fun G : SimpleGraph V => G.Connected)).biUnion
        (fun G => Fintype.piFinset (fun _ : Fin m => Bad' G)) := by
    intro F _
    obtain ⟨G, hG, hbad⟩ := hcon F
    refine mem_biUnion.2 ⟨G, by simp [hG], Fintype.mem_piFinset.2 fun i => ?_⟩
    simp [Bad', hbad i]
  have hcard := (card_le_card hcover).trans card_biUnion_le
  rw [card_univ] at hcard
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin] at hcard
  have hN : N = M ^ n := by simp [N, n]
  -- each term is at most `(N/2)^m`
  have hterm : ∀ G ∈ univ.filter (fun G : SimpleGraph V => G.Connected),
      2 ^ m * (Bad' G).card ^ m ≤ N ^ m := by
    intro G hG
    simp only [mem_filter, mem_univ, true_and] at hG
    rw [← mul_pow]
    apply Nat.pow_le_pow_left
    rw [hN]; exact card_not_allClustered hG ht hK
  have hgraphs : (univ.filter (fun G : SimpleGraph V => G.Connected)).card ≤ 2 ^ (n * n) := by
    refine (card_filter_le _ _).trans ?_
    rw [card_univ]
    have hinj : Function.Injective (fun G : SimpleGraph V => fun a b => decide (G.Adj a b)) := by
      intro G G' h
      ext a b
      have := congrFun (congrFun h a) b
      simpa using this
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool] at this
    rwa [← pow_mul] at this
  have hsum : 2 ^ m * ∑ G ∈ univ.filter (fun G : SimpleGraph V => G.Connected),
      (Bad' G).card ^ m ≤ 2 ^ (n * n) * N ^ m := by
    rw [mul_sum]
    calc ∑ G ∈ _, 2 ^ m * (Bad' G).card ^ m ≤ ∑ _G ∈ univ.filter (fun G : SimpleGraph V =>
          G.Connected), N ^ m := sum_le_sum hterm
      _ = _ * N ^ m := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 ^ (n * n) * N ^ m := Nat.mul_le_mul_right _ hgraphs
  have hpos : 0 < N ^ m := by
    apply pow_pos; rw [hN]; exact pow_pos (by omega) n
  have : 2 ^ m * N ^ m ≤ 2 ^ (n * n) * N ^ m := by
    calc 2 ^ m * N ^ m = 2 ^ m * (M ^ n) ^ m := by rw [hN]
      _ ≤ 2 ^ m * ∑ G ∈ univ.filter (fun G : SimpleGraph V => G.Connected),
          (Bad' G).card ^ m := Nat.mul_le_mul_left _ hcard
      _ ≤ _ := hsum
  have h2 : 2 ^ (n * n) * N ^ m < 2 ^ m * N ^ m := by
    apply Nat.mul_lt_mul_of_pos_right _ hpos
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end Lemma52

end PLSTradeoff
