import Papers.PODC2010.TruncatedGaleShapley.Distributed

/-!
# Theorems 1 and 2: distributed statements

Floréen, Kaski, Polishchuk, Suomela, *Almost Stable Matchings in Constant Time*, arXiv 0812.4893.

* `theorem_1`: a deterministic algorithm in the port-numbering model (§1.2) that, on every simple
  bicoloured port-numbered graph of maximum degree `≤ Δ` whose ports are numbered by the
  preferences, outputs an `ε`-stable matching after `T ≤ 4 + 2Δ²/ε` communication rounds. The
  preferences may have ties (`pref`), as long as the port numbering is compatible with them.
* `theorem_2`: with edge weights as local inputs, a deterministic algorithm that outputs a
  `(2+ε)`-approximation of a maximum-weight matching after `T ≤ 4 + 2Δ/ε` rounds.
-/

namespace Podc.TruncatedGaleShapley

open Finset Cslib.PortNumbering

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The preference graph of a simple port-numbered graph whose ports are numbered by preference:
`v` prefers the neighbour behind port `i` over the one behind port `j` iff `i < j`. -/
noncomputable def portPrefGraph (G : PNGraph V) (hG : G.IsSimple) : PrefGraph V where
  N v := (range (G.deg v)).image (G.nbr v)
  symm := by
    intro u v hv
    simp only [mem_image, mem_range] at hv ⊢
    obtain ⟨i, hi, rfl⟩ := hv
    exact ⟨G.rport u i, G.rport_lt hi, G.nbr_nbr hi⟩
  rank := portOf G
  rank_inj := by
    intro v u u' hu hu' he
    simp only [mem_image, mem_range] at hu hu'
    obtain ⟨i, hi, rfl⟩ := hu
    obtain ⟨j, hj, rfl⟩ := hu'
    rw [portOf_nbr hG hi, portOf_nbr hG hj] at he
    rw [he]

/-- `u` (weakly ranking its neighbours by `pref`, ties allowed) strictly prefers `v` to its
partner `m`. -/
def WPrefers (pref : V → V → ℕ) (u v : V) : Option V → Prop
  | none => True
  | some x => pref u v < pref u x

/-- Unstable edges with respect to preferences with ties: `{u, v}` is an edge, and each endpoint
is unmatched or strictly prefers the other endpoint to its partner. -/
noncomputable def weakUnstableEdges (N : V → Finset V) (pref : V → V → ℕ) (p : V → Option V) :
    Finset (Sym2 V) :=
  open Classical in
  (univ.filter fun x : V × V => x.2 ∈ N x.1 ∧ WPrefers pref x.1 x.2 (p x.1) ∧
    WPrefers pref x.2 x.1 (p x.2)).image fun x => s(x.1, x.2)

/-! ### Theorem 1 -/

/-- The algorithm of Theorem 1: ports are ranked by their numbers, then `gsAlg T`. -/
noncomputable def alg1 (T : ℕ) : Algorithm Bool (Option ℕ) :=
  (Algorithm.ofFun fun _ c => (c, (id : ℕ → ℕ))).seq 0 (gsAlg T)

lemma alg1_eval (T : ℕ) (G : PNGraph V) (red : V → Bool) (v : V) :
    (alg1 T).eval G T red v = (gsAlg T).eval G T (fun u => (red u, (id : ℕ → ℕ))) v := by
  rw [show (alg1 T).eval G T red v = (alg1 T).eval G (0 + T) red v by rw [zero_add], alg1,
    Algorithm.eval_seq]
  rfl

/-- The number of Gale–Shapley rounds used for Theorem 1. -/
noncomputable def rounds1 (Δ : ℕ) (ε : ℝ) : ℕ := max 2 ⌈1 + (Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ) / ε⌉₊

lemma rounds1_bound (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((2 * rounds1 Δ ε : ℕ) : ℝ) ≤ 4 + 2 * (Δ : ℝ) ^ 2 / ε := by
  have ha : (0 : ℝ) ≤ (Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ) / ε := by positivity
  have hD : (Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ) / ε ≤ (Δ : ℝ) ^ 2 / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    rw [sq]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le Δ 1) (Nat.cast_nonneg _)
  have hD2 : 0 ≤ (Δ : ℝ) ^ 2 / ε := by positivity
  have h2 : 2 * (Δ : ℝ) ^ 2 / ε = 2 * ((Δ : ℝ) ^ 2 / ε) := by ring
  rw [h2]
  push_cast
  rcases le_total 2 ⌈1 + (Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ) / ε⌉₊ with hm | hm
  · rw [rounds1, max_eq_right hm]
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 1 + (Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ) / ε)
    linarith
  · rw [rounds1, max_eq_left hm]; push_cast; linarith

lemma le_rounds1 (Δ : ℕ) (ε : ℝ) :
    2 ≤ rounds1 Δ ε ∧ 1 + (Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ) / ε ≤ rounds1 Δ ε :=
  ⟨le_max_left _ _, (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))⟩

lemma card_N_le {G : PNGraph V} {Δ : ℕ} (hΔ : ∀ v, G.deg v ≤ Δ) (v : V) :
    ((range (G.deg v)).image (G.nbr v)).card ≤ Δ :=
  card_image_le.trans ((card_range _).le.trans (hΔ v))

/-- If the port numbering is compatible with the weak preferences `pref`, a strict `pref`-preference
is a strict port preference. -/
lemma prefers_of_wprefers {G : PNGraph V} (hG : G.IsSimple) {pref : V → V → ℕ}
    (hpref : ∀ v i j, i < j → j < G.deg v → pref v (G.nbr v i) ≤ pref v (G.nbr v j)) {u v : V}
    (hv : v ∈ (portPrefGraph G hG).N u) (m : Option V)
    (hm : ∀ x, m = some x → x ∈ (portPrefGraph G hG).N u) (h : WPrefers pref u v m) :
    (portPrefGraph G hG).Prefers u v m := by
  rcases m with _ | x
  · trivial
  · have hx := hm x rfl
    simp only [portPrefGraph, mem_image, mem_range] at hv hx
    obtain ⟨i, hi, rfl⟩ := hv
    obtain ⟨j, hj, rfl⟩ := hx
    change portOf G u (G.nbr u i) < portOf G u (G.nbr u j)
    rw [portOf_nbr hG hi, portOf_nbr hG hj]
    change pref u (G.nbr u i) < pref u (G.nbr u j) at h
    by_contra hij
    rcases (not_lt.1 hij).lt_or_eq with hlt | heq
    · exact absurd (hpref u j i hlt hi) (not_le.2 h)
    · rw [heq] at h; exact lt_irrefl _ h

/-- The algorithm of Theorem 1 (`alg1` run for `2 * rounds1 Δ ε` rounds) is correct, for
preferences with ties compatible with the port numbering. -/
theorem alg1_spec (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) (G : PNGraph V) (hG : G.IsSimple)
    (red : V → Bool) (hred : ∀ v i, i < G.deg v → red (G.nbr v i) ≠ red v)
    (hΔ : ∀ v, G.deg v ≤ Δ) :
    (portPrefGraph G hG).IsMatching
        (fun v => ((alg1 (2 * rounds1 Δ ε)).eval G (2 * rounds1 Δ ε) red v).map (G.nbr v)) ∧
      ∀ pref : V → V → ℕ,
        (∀ v i j, i < j → j < G.deg v → pref v (G.nbr v i) ≤ pref v (G.nbr v j)) →
        ((weakUnstableEdges (portPrefGraph G hG).N pref
            (fun v => ((alg1 (2 * rounds1 Δ ε)).eval G (2 * rounds1 Δ ε) red v).map
              (G.nbr v))).card : ℝ) ≤
          ε * (matchingEdges (fun v => ((alg1 (2 * rounds1 Δ ε)).eval G (2 * rounds1 Δ ε) red v).map
            (G.nbr v))).card := by
  set i := rounds1 Δ ε
  have h : GoodInput G red (fun _ => id) := ⟨hG, hred, fun _ _ _ _ _ e => e⟩
  set I := toBicoloured G red (fun _ => id) h
  have hpart : (fun v => ((alg1 (2 * i)).eval G (2 * i) red v).map (G.nbr v)) = (I.run i).p := by
    funext v; rw [alg1_eval]; exact gsAlg_partner h i v
  rw [hpart]
  have hI : I.toPrefGraph = portPrefGraph G hG := rfl
  rw [← hI]
  refine ⟨Bicoloured.isMatching_run (I := I) i, fun pref hpref => ?_⟩
  have hst := Bicoloured.theorem_1_rounds (I := I) (card_N_le hΔ) hε (le_rounds1 Δ ε).1
    (le_rounds1 Δ ε).2
  refine le_trans ?_ hst
  -- weakly unstable edges are unstable for the port order
  refine Nat.cast_le.2 (card_le_card ?_)
  intro e he
  simp only [weakUnstableEdges, mem_image, mem_filter, mem_univ, true_and] at he
  obtain ⟨⟨u, v⟩, ⟨hv, hu1, hu2⟩, rfl⟩ := he
  simp only [PrefGraph.unstableEdges, mem_image, mem_filter, mem_univ, true_and]
  have hM := Bicoloured.isMatching_run (I := I) i
  refine ⟨(u, v), ⟨hv, ?_, ?_⟩, rfl⟩
  · exact prefers_of_wprefers hG hpref hv _ (hM.mem_N u) hu1
  · exact prefers_of_wprefers hG hpref (I.symm hv) _ (hM.mem_N v) hu2

lemma wprefers_of_prefers {G : PNGraph V} {hG : G.IsSimple} {u v : V} {m : Option V}
    (h : (portPrefGraph G hG).Prefers u v m) : WPrefers (portOf G) u v m := by
  cases m <;> exact h

/-- **Theorem 1** (with ties). For every `Δ` and `ε > 0` there is a deterministic algorithm in the
port-numbering model running for `T ≤ 4 + 2Δ²/ε` synchronous communication rounds such that, on
every simple port-numbered graph of maximum degree `≤ Δ` with a proper red/blue colouring (the
input), the outputs (ports of partners) are consistent and define a matching `M`, and for every
weak preference `pref` (ties allowed) with which the port numbering is compatible, `M` has at most
`ε |M|` unstable edges. -/
theorem theorem_1_ties (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : Algorithm Bool (Option ℕ)) (T : ℕ), (T : ℝ) ≤ 4 + 2 * (Δ : ℝ) ^ 2 / ε ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : PNGraph V) (hG : G.IsSimple) (red : V → Bool),
        (∀ v i, i < G.deg v → red (G.nbr v i) ≠ red v) → (∀ v, G.deg v ≤ Δ) →
        (portPrefGraph G hG).IsMatching (fun v => (A.eval G T red v).map (G.nbr v)) ∧
        ∀ pref : V → V → ℕ,
          (∀ v i j, i < j → j < G.deg v → pref v (G.nbr v i) ≤ pref v (G.nbr v j)) →
          ((weakUnstableEdges (portPrefGraph G hG).N pref
              (fun v => (A.eval G T red v).map (G.nbr v))).card : ℝ) ≤
            ε * (matchingEdges (fun v => (A.eval G T red v).map (G.nbr v))).card :=
  ⟨alg1 (2 * rounds1 Δ ε), 2 * rounds1 Δ ε, rounds1_bound Δ hε,
    fun G hG red hred hΔ => alg1_spec Δ hε G hG red hred hΔ⟩

/-- **Theorem 1.** For every `Δ` and `ε > 0` there is a deterministic distributed algorithm (port-
numbering model; a node knows its colour, its degree and `T`; ports numbered by preference) that
finds an `ε`-stable matching in every bicoloured graph of maximum degree `≤ Δ` in time
`T ≤ 4 + 2Δ²/ε`. -/
theorem theorem_1 (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : Algorithm Bool (Option ℕ)) (T : ℕ), (T : ℝ) ≤ 4 + 2 * (Δ : ℝ) ^ 2 / ε ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : PNGraph V) (hG : G.IsSimple) (red : V → Bool),
        (∀ v i, i < G.deg v → red (G.nbr v i) ≠ red v) → (∀ v, G.deg v ≤ Δ) →
        (portPrefGraph G hG).IsMatching (fun v => (A.eval G T red v).map (G.nbr v)) ∧
        (portPrefGraph G hG).IsEpsStable ε (fun v => (A.eval G T red v).map (G.nbr v)) := by
  obtain ⟨A, T, hT, hA⟩ := theorem_1_ties Δ hε
  refine ⟨A, T, hT, fun G hG red hred hΔ => ⟨(hA G hG red hred hΔ).1, ?_⟩⟩
  have hcompat : ∀ v i j, i < j → j < G.deg v →
      portOf G v (G.nbr v i) ≤ portOf G v (G.nbr v j) := by
    intro v i j hij hj
    rw [portOf_nbr hG (hij.trans hj), portOf_nbr hG hj]; exact hij.le
  refine le_trans ?_ ((hA G hG red hred hΔ).2 (portOf G) hcompat)
  refine Nat.cast_le.2 (card_le_card ?_)
  intro e he
  simp only [PrefGraph.unstableEdges, mem_image, mem_filter, mem_univ, true_and] at he
  obtain ⟨⟨u, v⟩, ⟨hv, hu1, hu2⟩, rfl⟩ := he
  simp only [weakUnstableEdges, mem_image, mem_filter, mem_univ, true_and]
  refine ⟨(u, v), ⟨hv, ?_, ?_⟩, rfl⟩
  · exact wprefers_of_prefers hu1
  · exact wprefers_of_prefers hu2

/-! ### Theorem 2 -/

open Classical in
/-- The local ranking of ports by decreasing weight (ties broken by port number): the number of
ports that beat port `i`. -/
noncomputable def wrank (d : ℕ) (wt : ℕ → ℝ) (i : ℕ) : ℕ :=
  ((range d).filter fun k => wt i < wt k ∨ (wt k = wt i ∧ k < i)).card

/-- `k` beats `i`: heavier, or equally heavy with a smaller port number. -/
def Beats (wt : ℕ → ℝ) (k i : ℕ) : Prop := wt i < wt k ∨ (wt k = wt i ∧ k < i)

lemma beats_trans {wt : ℕ → ℝ} {a b c : ℕ} (h1 : Beats wt a b) (h2 : Beats wt b c) :
    Beats wt a c := by
  unfold Beats at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨h1.trans h2, h1'.trans h2'⟩

lemma not_beats_self (wt : ℕ → ℝ) (a : ℕ) : ¬ Beats wt a a := by
  unfold Beats; rintro (h | ⟨-, h⟩) <;> exact lt_irrefl _ h

lemma wrank_lt_of_beats {d : ℕ} {wt : ℕ → ℝ} {i j : ℕ} (hj : j < d) (h : Beats wt j i) :
    wrank d wt j < wrank d wt i := by
  classical
  unfold wrank
  apply card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, ?_, ?_⟩
    · simp only [mem_filter, mem_range]; exact ⟨hj, h⟩
    · simp only [mem_filter, mem_range, not_and]
      intro _; simp
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    exact ⟨hk.1, beats_trans (wt := wt) hk.2 h⟩

lemma beats_total {wt : ℕ → ℝ} {i j : ℕ} (hij : i ≠ j) : Beats wt i j ∨ Beats wt j i := by
  unfold Beats
  rcases lt_trichotomy (wt i) (wt j) with h | h | h
  · right; left; exact h
  · rcases lt_or_gt_of_ne hij with h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; right; exact ⟨h.symm, h'⟩
  · left; left; exact h

lemma wrank_inj {d : ℕ} {wt : ℕ → ℝ} {i j : ℕ} (hi : i < d) (hj : j < d)
    (h : wrank d wt i = wrank d wt j) : i = j := by
  by_contra hij
  rcases beats_total (wt := wt) hij with hb | hb
  · exact absurd h (wrank_lt_of_beats hi hb).ne
  · exact absurd h (wrank_lt_of_beats hj hb).ne'

/-- The algorithm of Theorem 2: rank the ports by weight, then `gsAlg T`. -/
noncomputable def alg2 (T : ℕ) : Algorithm (Bool × (ℕ → ℝ)) (Option ℕ) :=
  (Algorithm.ofFun fun d x => (x.1, wrank d x.2)).seq 0 (gsAlg T)

lemma alg2_eval (T : ℕ) (G : PNGraph V) (x : V → Bool × (ℕ → ℝ)) (v : V) :
    (alg2 T).eval G T x v =
      (gsAlg T).eval G T (fun u => ((x u).1, wrank (G.deg u) (x u).2)) v := by
  rw [show (alg2 T).eval G T x v = (alg2 T).eval G (0 + T) x v by rw [zero_add], alg2,
    Algorithm.eval_seq]
  rfl

/-- The number of Gale–Shapley rounds used for Theorem 2. -/
noncomputable def rounds2 (Δ : ℕ) (ε : ℝ) : ℕ := max 2 ⌈1 + ((Δ - 1 : ℕ) : ℝ) / ε⌉₊

lemma rounds2_bound (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((2 * rounds2 Δ ε : ℕ) : ℝ) ≤ 4 + 2 * (Δ : ℝ) / ε := by
  have ha : (0 : ℝ) ≤ ((Δ - 1 : ℕ) : ℝ) / ε := by positivity
  have hD : ((Δ - 1 : ℕ) : ℝ) / ε ≤ (Δ : ℝ) / ε :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le Δ 1) hε.le
  have hD2 : 0 ≤ (Δ : ℝ) / ε := by positivity
  have h2 : 2 * (Δ : ℝ) / ε = 2 * ((Δ : ℝ) / ε) := by ring
  rw [h2]
  push_cast
  rcases le_total 2 ⌈1 + ((Δ - 1 : ℕ) : ℝ) / ε⌉₊ with hm | hm
  · rw [rounds2, max_eq_right hm]
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 1 + ((Δ - 1 : ℕ) : ℝ) / ε)
    linarith
  · rw [rounds2, max_eq_left hm]; push_cast; linarith

lemma le_rounds2 (Δ : ℕ) (ε : ℝ) :
    2 ≤ rounds2 Δ ε ∧ 1 + ((Δ - 1 : ℕ) : ℝ) / ε ≤ rounds2 Δ ε :=
  ⟨le_max_left _ _, (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))⟩

/-- The algorithm of Theorem 2 is correct. -/
theorem alg2_spec (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) (G : PNGraph V) (hG : G.IsSimple)
    (red : V → Bool) (hred : ∀ v i, i < G.deg v → red (G.nbr v i) ≠ red v)
    (hΔ : ∀ v, G.deg v ≤ Δ) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (portPrefGraph G hG).IsMatching (fun v => ((alg2 (2 * rounds2 Δ ε)).eval G (2 * rounds2 Δ ε)
        (fun u => (red u, fun i => w (G.edge u i))) v).map (G.nbr v)) ∧
      ∀ q : V → Option V, (portPrefGraph G hG).IsMatching q →
        ∑ e ∈ matchingEdges q, w e ≤ (2 + ε) * ∑ e ∈ matchingEdges (fun v =>
          ((alg2 (2 * rounds2 Δ ε)).eval G (2 * rounds2 Δ ε)
            (fun u => (red u, fun i => w (G.edge u i))) v).map (G.nbr v)), w e := by
  set i := rounds2 Δ ε
  set rk : V → ℕ → ℕ := fun u => wrank (G.deg u) (fun j => w (G.edge u j))
  have h : GoodInput G red rk := ⟨hG, hred, fun v i j hi hj e => wrank_inj hi hj e⟩
  set I := toBicoloured G red rk h
  have hpart : (fun v => ((alg2 (2 * i)).eval G (2 * i)
      (fun u => (red u, fun i => w (G.edge u i))) v).map (G.nbr v)) = (I.run i).p := by
    funext v; rw [alg2_eval]; exact gsAlg_partner h i v
  rw [hpart]
  have hN : ∀ q, (portPrefGraph G hG).IsMatching q → I.IsMatching q :=
    fun q hq => ⟨hq.mem_N, hq.symm⟩
  have hresp : I.RespectsPrefs w := by
    refine ⟨hw, ?_⟩
    intro v x y hx hy hlt
    simp only [I, toBicoloured, mem_image, mem_range] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    change rk v (portOf G v (G.nbr v a)) < rk v (portOf G v (G.nbr v b)) at hlt
    rw [portOf_nbr hG ha, portOf_nbr hG hb] at hlt
    by_contra hcon
    have hb' : Beats (fun j => w (G.edge v j)) b a := Or.inl (by
      simp only [PNGraph.edge]; exact lt_of_not_ge hcon)
    exact absurd hlt (not_lt.2 (wrank_lt_of_beats hb hb').le)
  refine ⟨⟨fun u v huv => (Bicoloured.isMatching_run (I := I) i).mem_N u v huv,
    fun u v huv => (Bicoloured.isMatching_run (I := I) i).symm u v huv⟩, fun q hq => ?_⟩
  exact Bicoloured.theorem_2_rounds hresp (card_N_le hΔ) hε (le_rounds2 Δ ε).1 (le_rounds2 Δ ε).2
    (hN q hq)

/-- **Theorem 2.** For every `Δ` and `ε > 0` there is a deterministic distributed algorithm
(port-numbering model; inputs: the colour and the weights `w ≥ 0` of the incident edges, per port)
that finds a `(2+ε)`-approximation of a maximum-weight matching in every bicoloured graph of
maximum degree `≤ Δ`, in time `T ≤ 4 + 2Δ/ε`: the output is a matching `M` with
`w(M*) ≤ (2+ε) w(M)` for every matching `M*`. -/
theorem theorem_2 (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : Algorithm (Bool × (ℕ → ℝ)) (Option ℕ)) (T : ℕ), (T : ℝ) ≤ 4 + 2 * (Δ : ℝ) / ε ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : PNGraph V) (hG : G.IsSimple) (red : V → Bool)
        (w : Sym2 V → ℝ),
        (∀ v i, i < G.deg v → red (G.nbr v i) ≠ red v) → (∀ v, G.deg v ≤ Δ) → (∀ e, 0 ≤ w e) →
        (portPrefGraph G hG).IsMatching
            (fun v => (A.eval G T (fun u => (red u, fun i => w (G.edge u i))) v).map (G.nbr v)) ∧
        ∀ q : V → Option V, (portPrefGraph G hG).IsMatching q →
          ∑ e ∈ matchingEdges q, w e ≤ (2 + ε) * ∑ e ∈ matchingEdges
            (fun v => (A.eval G T (fun u => (red u, fun i => w (G.edge u i))) v).map (G.nbr v)),
            w e :=
  ⟨alg2 (2 * rounds2 Δ ε), 2 * rounds2 Δ ε, rounds2_bound Δ hε,
    fun G hG red w hred hΔ hw => alg2_spec Δ hε G hG red hred hΔ w hw⟩

end Podc.TruncatedGaleShapley
