import Papers.PODC2013.ByzantineVectorConsensus.Spec
import Cslib.Computability.Distributed.ApproxConsensus.Contraction
import Cslib.Foundations.Algebra.Order.BigOperators.Average
import Cslib.Foundations.Data.Finset.Quorum
import Cslib.Foundations.Data.Real.Logb

/-!
# The iterative approximate BVC algorithm (Section 3.2, Theorem 5; Section 4, Theorem 6)

The paper's asynchronous algorithm runs in asynchronous rounds. In round `r + 1`, every correct
process `i` obtains (by Component #1 of the Abraham–Amit–Dolev algorithm, used as a black box) a
set `B_i[r+1]` of tuples `(p_k, w_k)` with at most one tuple per process (Property 2), with
`w_k = v_k[r]` for correct `p_k` (Property 3), such that any two correct processes share at least
`n - f` identical tuples (Property 1). It then sets `v_i[r+1]` to the average of one
deterministically chosen point of `Γ(Φ(C))` for every `C ⊆ B_i[r+1]` with `|C| = n - f`.

We formalize the algorithm on the level of these round exchanges, exactly as the paper's proof
does: a `RoundExec` records the adversary's choices (faulty set, inputs, the sets `B`, and the values
in the tuples of faulty processes, which may differ between receivers); the states are computed
(`RoundExec.state`). Property 2 is built into the representation (`B` is a set of processes and
the tuple values are a function of the sender), Property 3 into `recvWith` (tuples of correct
senders carry their current state), and Properties 1 and "`|B_i| ≥ n - f`" are the hypotheses
`RoundExec.Valid f s` with subset size `s`. **The implementation of Component #1 (reliable
broadcast + witnesses, [AAD04]) is not formalized**: Theorem 5 is proved for every execution in
which Component #1 delivers sets with Properties 1–3, as in the paper.

The subset size `s` is a parameter: `s = n - f` is the paper's Section 3.2 algorithm; the restricted
round structures of Section 4 are the instances `s = n - f` (synchronous, `B_i` = all processes)
and `s = n - 3f` (asynchronous, `B_i` = the first `n - f` round messages); see
`theorem_6_sync`, `theorem_6_async`.

Main results:
* `RoundExec.state_mem_convexHull` — validity (Part I and Part III of the proof of Theorem 5);
* `RoundExec.contraction` — inequality (12) (Part II and Appendix E), with
  `γ = 1 / (n · C(n, s))` (equation (11) for `s = n - f`);
* `RoundExec.agreement_bound`, `RoundExec.approx_agreement` and `theorem_5`.
-/

open Finset Module Cslib.ApproxConsensus

namespace ByzantineVectorConsensus

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P] {d : ℕ}

/-! ### Auxiliary real-arithmetic lemmas -/

/-- If a point is a convex combination of the points of `F` (at most `n` of them), all with
`l`-th coordinate in `[a, b]`, then some point `u ∈ F` has weight `≥ 1 / n`; hence the
`l`-th coordinate of the point is at most `b - (b - u_l) / n` and at least `a + (u_l - a) / n`.
(The "weight `≥ 1/m`" observation after Definition 1 of the paper.) -/
theorem exists_heavy {F : Finset (Vec d)} {z : Vec d} (hz : z ∈ convexHull ℝ (F : Set (Vec d)))
    {n : ℕ} (hn : F.card ≤ n) (l : Fin d) {a b : ℝ} (hab : ∀ u ∈ F, a ≤ u l ∧ u l ≤ b) :
    ∃ u ∈ F, z l ≤ b - (b - u l) / n ∧ a + (u l - a) / n ≤ z l := by
  obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.1 hz
  have hne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hw1
  have hcard : (0 : ℝ) < F.card := by exact_mod_cast hne.card_pos
  obtain ⟨u, huF, hu⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (1 : ℝ) / F.card) (g := w) (by
      rw [hw1, Finset.sum_const, nsmul_eq_mul]; field_simp; rfl)
  have hun : (1 : ℝ) / n ≤ w u := by
    refine le_trans ?_ hu
    exact one_div_le_one_div_of_le hcard (by exact_mod_cast hn)
  have hzl : (∑ y ∈ F, w y • y) l = ∑ y ∈ F, w y * y l := by
    simp [Finset.sum_apply, smul_eq_mul]
  refine ⟨u, huF, ?_, ?_⟩
  · have h3 : (b - u l) / n ≤ w u * (b - u l) := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hun (by linarith [(hab u huF).2])
    rw [hzl]
    linarith [Finset.sum_mul_le_sub_mul_sub hw0 hw1 (fun y hy => (hab y hy).2) huF]
  · have h3 : (u l - a) / n ≤ w u * (u l - a) := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hun (by linarith [(hab u huF).1])
    rw [hzl]
    linarith [Finset.add_mul_sub_le_sum_mul hw0 hw1 (fun y hy => (hab y hy).1) huF]

/-- Averaging: if all `x_i ≤ b` and `x_{i₀} ≤ b - δ₀`, the average is `≤ b - δ₀ / |S|`. -/
theorem avg_le {ι : Type*} {S : Finset ι} {x : ι → ℝ} {b δ₀ : ℝ} {i₀ : ι} (hi₀ : i₀ ∈ S)
    (hx : ∀ i ∈ S, x i ≤ b) (h0 : x i₀ ≤ b - δ₀) :
    ((S.card : ℝ))⁻¹ * ∑ i ∈ S, x i ≤ b - δ₀ / S.card := by
  rw [inv_mul_eq_div]
  refine (Finset.sum_div_card_le_sub_div hx hi₀ le_rfl).trans ?_
  gcongr
  linarith

/-- Averaging, lower bound version. -/
theorem le_avg {ι : Type*} {S : Finset ι} {x : ι → ℝ} {a δ₀ : ℝ} {i₀ : ι} (hi₀ : i₀ ∈ S)
    (hx : ∀ i ∈ S, a ≤ x i) (h0 : a + δ₀ ≤ x i₀) :
    a + δ₀ / S.card ≤ ((S.card : ℝ))⁻¹ * ∑ i ∈ S, x i := by
  rw [inv_mul_eq_div]
  refine le_trans ?_ (Finset.add_div_le_sum_div_card hx hi₀ le_rfl)
  gcongr
  linarith

/-- The number of rounds after which the paper's algorithm terminates:
`1 + ⌈log_{1/q} (D / ε)⌉` with `q = 1 - γ` and `D = U - ν`, is enough: `q^R · D < ε`. -/
theorem rounds_spec {q D ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hε : 0 < ε) :
    q ^ (1 + ⌈Real.logb (1 / q) (D / ε)⌉₊) * D < ε := by
  set R := 1 + ⌈Real.logb (1 / q) (D / ε)⌉₊
  rcases le_or_gt D 0 with hD | hD
  · nlinarith [pow_nonneg hq0 R]
  rcases hq0.eq_or_lt with hq | hq
  · subst hq; simp [R, hε]
  have h := Real.pow_natCeil_logb_inv_div_mul_le hq hq1 D hε
  rw [← one_div] at h
  rw [pow_add, pow_one, mul_assoc]
  nlinarith

/-! ### Executions of the round-based algorithm -/

/-- The adversary's choices in an execution of the round-based algorithm. -/
structure RoundExec (P : Type*) (d : ℕ) where
  /-- The faulty processes. -/
  faulty : Finset P
  /-- The inputs. -/
  inp : P → Vec d
  /-- `B r i`: the processes whose tuples correct process `i` obtained in round `r + 1`. -/
  B : ℕ → P → Finset P
  /-- `byz r i k`: the value in the tuple of the faulty process `k` obtained by `i` in round
  `r + 1` (may differ between receivers). -/
  byz : ℕ → P → P → Vec d

namespace RoundExec

variable (f s : ℕ) (E : RoundExec P d)

/-- The correct processes. -/
def correct : Finset P := univ.filter fun k => k ∉ E.faulty

/-- The values in the tuples obtained by `i` in round `r + 1`, given the states `v` at the end of
round `r`: correct senders carry their state (Property 3). -/
def recvWith (v : P → Vec d) (r : ℕ) (i k : P) : Vec d :=
  if k ∈ E.faulty then E.byz r i k else v k

/-- Step 2 of the algorithm: the average, over all `C ⊆ B` with `|C| = s`, of the chosen point
of `Γ(Φ(C))` (equation (9)). -/
noncomputable def update (B : Finset P) (w : P → Vec d) : Vec d :=
  (((B.powersetCard s).card : ℝ))⁻¹ • ∑ C ∈ B.powersetCard s, gammaPt f C w

/-- The state `v_i[r]` of every process at the end of round `r` (meaningful for correct `i`). -/
noncomputable def state : ℕ → P → Vec d
  | 0 => E.inp
  | r + 1 => fun i => update f s (E.B r i) (E.recvWith (state r) r i)

/-- The hypotheses on the round exchange (Properties 1–3 of AAD Component #1, Property 2 and 3 being
built into the representation), with subset size `s`. -/
structure Valid : Prop where
  card_faulty : E.faulty.card ≤ f
  /-- every correct process obtains at least `s` tuples -/
  card_B : ∀ r, ∀ i ∉ E.faulty, s ≤ (E.B r i).card
  /-- Property 1: any two correct processes share `s` identical tuples -/
  common : ∀ r, ∀ i ∉ E.faulty, ∀ j ∉ E.faulty, ∃ C ⊆ E.B r i ∩ E.B r j, C.card = s ∧
    ∀ k ∈ C, k ∈ E.faulty → E.byz r i k = E.byz r j k

variable {f s E}

theorem mem_correct {k : P} : k ∈ E.correct ↔ k ∉ E.faulty := by simp [correct]

theorem card_correct (hV : E.Valid f s) : Fintype.card P - f ≤ E.correct.card :=
  card_sub_le_card_filter_notMem hV.card_faulty

/-- **Part I**: every point added to `Z_i` is *valid*, i.e. in the hull of the round-`r` states
of the correct processes. -/
theorem gammaPt_mem_hull (hV : E.Valid f s) (hs : (d + 1) * f < s) (r : ℕ) (i : P) {C : Finset P}
    (hC : C.card = s) :
    gammaPt f C (E.recvWith (E.state f s r) r i) ∈
      convexHull ℝ (E.state f s r '' (E.correct : Set P)) := by
  have hmem := gammaPt_mem (f := f) (C := C) (E.recvWith (E.state f s r) r i)
    (by rw [finrank_fin_fun, hC]; exact hs)
  set T := C.filter fun k => k ∉ E.faulty
  have hT : C.card - f ≤ T.card := by
    have h1 := card_filter_add_card_filter_not (s := C) (fun q => q ∉ E.faulty)
    have h2 : (C.filter fun q => ¬ q ∉ E.faulty).card ≤ f := by
      refine le_trans (card_le_card fun k hk => ?_) hV.card_faulty
      simp only [mem_filter, not_not] at hk; exact hk.2
    simp only [T]; omega
  have := GammaOn_subset_convexHull (filter_subset _ C) hT hmem
  refine convexHull_mono ?_ this
  rintro _ ⟨k, hk, rfl⟩
  simp only [coe_filter, Set.mem_ofPred_eq] at hk
  refine ⟨k, by simpa [mem_correct] using hk.2, ?_⟩
  simp [recvWith, hk.2]

theorem powersetCard_nonempty' (hV : E.Valid f s) (r : ℕ) {i : P} (hi : i ∉ E.faulty) :
    (E.B r i |>.powersetCard s).Nonempty :=
  powersetCard_nonempty.2 (hV.card_B r i hi)

/-- Observation 3 (first half): the new state of a correct process is valid. -/
theorem state_succ_mem_hull (hV : E.Valid f s) (hs : (d + 1) * f < s) (r : ℕ) {i : P}
    (hi : i ∉ E.faulty) :
    E.state f s (r + 1) i ∈ convexHull ℝ (E.state f s r '' (E.correct : Set P)) := by
  simp only [state, update]
  rw [Finset.smul_sum]
  refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_
    fun C hC => gammaPt_mem_hull hV hs r i (mem_powersetCard.1 hC).2
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (0 : ℝ) < ((E.B r i).powersetCard s).card := by
    exact_mod_cast (powersetCard_nonempty' hV r hi).card_pos
  field_simp

/-- **Validity** (Part III of the proof of Theorem 5): the state of every correct process is
always in the convex hull of the inputs of the correct processes. -/
theorem state_mem_convexHull (hV : E.Valid f s) (hs : (d + 1) * f < s) (r : ℕ) {i : P}
    (hi : i ∉ E.faulty) :
    E.state f s r i ∈ convexHull ℝ (E.inp '' (E.correct : Set P)) := by
  have key : ∀ r, convexHull ℝ (E.state f s r '' (E.correct : Set P)) ⊆
      convexHull ℝ (E.inp '' (E.correct : Set P)) := by
    intro r
    induction r with
    | zero => exact le_rfl
    | succ r ih =>
      refine convexHull_min ?_ (convex_convexHull ℝ _)
      rintro _ ⟨k, hk, rfl⟩
      exact ih (state_succ_mem_hull hV hs r (mem_correct.1 hk))
  exact key r (subset_convexHull ℝ _ ⟨i, mem_correct.2 hi, rfl⟩)

/-- Points of the hull of a set whose `l`-th coordinates lie in `[a, b]` have their `l`-th
coordinate in `[a, b]`. -/
theorem coord_mem_of_mem_hull {X : Set (Vec d)} {z : Vec d} (hz : z ∈ convexHull ℝ X) (l : Fin d)
    {a b : ℝ} (hX : ∀ u ∈ X, a ≤ u l ∧ u l ≤ b) : a ≤ z l ∧ z l ≤ b := by
  have hconv : Convex ℝ {w : Vec d | a ≤ w l ∧ w l ≤ b} :=
    (convex_Icc a b).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) l)
  exact convexHull_min (fun u hu => hX u hu) hconv hz

/-- The contraction factor `γ = 1 / (n · C(n, s))` (equation (11) for `s = n - f`). -/
noncomputable def gam (n s : ℕ) : ℝ := 1 / ((n : ℝ) * (n.choose s))

/-- **Inequality (12)** (Part II of the proof of Theorem 5 and Appendix E): if the round-`r`
states of the correct processes have `l`-th coordinates in `[a, b]`, then after round `r + 1` any
two correct processes differ by at most `(1 - γ)(b - a)` in coordinate `l`. -/
theorem contraction (hV : E.Valid f s) (hs : (d + 1) * f < s) (r : ℕ) (l : Fin d) {a b : ℝ}
    (hab : ∀ k ∉ E.faulty, a ≤ E.state f s r k l ∧ E.state f s r k l ≤ b) {i j : P}
    (hi : i ∉ E.faulty) (hj : j ∉ E.faulty) :
    E.state f s (r + 1) i l - E.state f s (r + 1) j l ≤
      (1 - gam (Fintype.card P) s) * (b - a) := by
  set n := Fintype.card P
  set F := E.correct.image (E.state f s r)
  have hFn : F.card ≤ n := card_image_le.trans (card_le_univ _)
  have hF : ∀ u ∈ F, a ≤ u l ∧ u l ≤ b := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hu
    exact hab k (mem_correct.1 hk)
  have hFset : (F : Set (Vec d)) = E.state f s r '' (E.correct : Set P) := by simp [F]
  -- the common point `z_ij`
  obtain ⟨C₀, hC₀, hC₀card, hC₀byz⟩ := hV.common r i hi j hj
  have hz : gammaPt f C₀ (E.recvWith (E.state f s r) r i) =
      gammaPt f C₀ (E.recvWith (E.state f s r) r j) :=
    gammaPt_congr fun k hk => by
      by_cases hkf : k ∈ E.faulty
      · simp [recvWith, hkf, hC₀byz k hk hkf]
      · simp [recvWith, hkf]
  set z := gammaPt f C₀ (E.recvWith (E.state f s r) r i)
  have hzmem : z ∈ convexHull ℝ (F : Set (Vec d)) := by
    rw [hFset]; exact gammaPt_mem_hull hV hs r i hC₀card
  obtain ⟨u, huF, hzu1, hzu2⟩ := exists_heavy hzmem hFn l hF
  have hu := hF u huF
  -- the sizes of `Z_i`, `Z_j`
  have hn0 : (0 : ℝ) < n := by
    have := hV.card_B r i hi
    have := card_le_univ (E.B r i)
    have : 0 < s := by omega
    exact_mod_cast (show 0 < n by omega)
  have hγ : ∀ k ∉ E.faulty, gam n s ≤ 1 / (n * ((E.B r k).powersetCard s).card) := by
    intro k hk
    rw [card_powersetCard]
    have h1 : (0 : ℝ) < (E.B r k).card.choose s := by
      exact_mod_cast Nat.choose_pos (hV.card_B r k hk)
    have h2 : ((E.B r k).card.choose s : ℝ) ≤ n.choose s := by
      exact_mod_cast Nat.choose_le_choose s (card_le_univ _)
    exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hcoord : ∀ k, (E.state f s (r + 1) k) l = (((E.B r k).powersetCard s).card : ℝ)⁻¹ *
      ∑ C ∈ (E.B r k).powersetCard s, (gammaPt f C (E.recvWith (E.state f s r) r k)) l := by
    intro k
    simp [state, update, Finset.sum_apply, smul_eq_mul]
  have hall : ∀ k ∉ E.faulty, ∀ C ∈ (E.B r k).powersetCard s,
      a ≤ (gammaPt f C (E.recvWith (E.state f s r) r k)) l ∧
        (gammaPt f C (E.recvWith (E.state f s r) r k)) l ≤ b := by
    intro k _ C hC
    refine coord_mem_of_mem_hull (gammaPt_mem_hull hV hs r k (mem_powersetCard.1 hC).2) l ?_
    rintro _ ⟨m, hm, rfl⟩
    exact hab m (mem_correct.1 hm)
  have hC₀i : C₀ ∈ (E.B r i).powersetCard s :=
    mem_powersetCard.2 ⟨hC₀.trans inter_subset_left, hC₀card⟩
  have hC₀j : C₀ ∈ (E.B r j).powersetCard s :=
    mem_powersetCard.2 ⟨hC₀.trans inter_subset_right, hC₀card⟩
  -- upper bound for `i`, lower bound for `j`
  set Ni := ((E.B r i).powersetCard s).card
  set Nj := ((E.B r j).powersetCard s).card
  have hNi : (0 : ℝ) < Ni := by exact_mod_cast (powersetCard_nonempty' hV r hi).card_pos
  have hNj : (0 : ℝ) < Nj := by exact_mod_cast (powersetCard_nonempty' hV r hj).card_pos
  have hi' : E.state f s (r + 1) i l ≤ b - gam n s * (b - u l) := by
    rw [hcoord]
    refine (avg_le hC₀i (fun C hC => (hall i hi C hC).2) hzu1).trans ?_
    have := hγ i hi
    have h1 : (b - u l) / n / Ni = 1 / (n * Ni) * (b - u l) := by field_simp
    rw [h1]
    nlinarith [hu.2]
  have hj' : a + gam n s * (u l - a) ≤ E.state f s (r + 1) j l := by
    rw [hcoord]
    refine le_trans ?_ (le_avg hC₀j (fun C hC => (hall j hj C hC).1) (by rw [← hz]; exact hzu2))
    have := hγ j hj
    have h1 : (u l - a) / n / Nj = 1 / (n * Nj) * (u l - a) := by field_simp
    rw [h1]
    nlinarith [hu.1]
  nlinarith

theorem gam_nonneg (n s : ℕ) : 0 ≤ gam n s := by unfold gam; positivity

theorem gam_le_one {n s : ℕ} (hs : s ≤ n) (hs0 : 0 < s) : gam n s ≤ 1 := by
  unfold gam
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h2 : (1 : ℝ) ≤ n.choose s := by exact_mod_cast Nat.choose_pos hs
  rw [div_le_one (by positivity)]
  nlinarith

/-- **Inequality (13)**: the spread of coordinate `l` among correct processes after `r` rounds is
at most `(1 - γ)^r (U - ν)`, if all correct inputs lie in the box `[ν, U]^d`. -/
theorem spread (hV : E.Valid f s) (hs : (d + 1) * f < s) (hsn : s ≤ Fintype.card P) {ν U : ℝ}
    (hin : ∀ k ∉ E.faulty, ∀ l, ν ≤ E.inp k l ∧ E.inp k l ≤ U) (l : Fin d) (r : ℕ) :
    ∃ a b, b - a ≤ (1 - gam (Fintype.card P) s) ^ r * (U - ν) ∧
      ∀ k ∉ E.faulty, a ≤ E.state f s r k l ∧ E.state f s r k l ≤ b := by
  have hγ1 : 0 ≤ 1 - gam (Fintype.card P) s := by
    linarith [gam_le_one hsn (by omega : 0 < s)]
  obtain ⟨a, b, hk, hab⟩ := exists_sub_le_pow_mul_of_step
    (P := fun r a b => ∀ k ∉ E.faulty, a ≤ E.state f s r k l ∧ E.state f s r k l ≤ b) hγ1
    (fun k hk => hin k hk l) (fun r a b hk => by
      obtain ⟨a', b', hab', hk'⟩ := exists_Icc_of_forall_sub_le_of_finite
        (s := {k | k ∉ E.faulty}) (Set.toFinite _) (y := fun k => E.state f s (r + 1) k l)
        fun i hi j hj => contraction hV hs r l hk hi hj
      exact ⟨a', b', hk', hab'⟩) r
  exact ⟨a, b, hab, hk⟩

/-- `ε`-agreement after `r` rounds, coordinate by coordinate. -/
theorem agreement_bound (hV : E.Valid f s) (hs : (d + 1) * f < s) (hsn : s ≤ Fintype.card P)
    {ν U : ℝ} (hin : ∀ k ∉ E.faulty, ∀ l, ν ≤ E.inp k l ∧ E.inp k l ≤ U) (r : ℕ) {i j : P}
    (hi : i ∉ E.faulty) (hj : j ∉ E.faulty) (l : Fin d) :
    |E.state f s r i l - E.state f s r j l| ≤ (1 - gam (Fintype.card P) s) ^ r * (U - ν) := by
  obtain ⟨a, b, hab, hk⟩ := spread hV hs hsn hin l r
  have := hk i hi
  have := hk j hj
  rw [abs_le]; constructor <;> linarith

/-- The number of rounds of Step 3 of the algorithm: `1 + ⌈log_{1/(1-γ)} ((U - ν)/ε)⌉`. -/
noncomputable def rounds (n s : ℕ) (ν U ε : ℝ) : ℕ :=
  1 + ⌈Real.logb (1 / (1 - gam n s)) ((U - ν) / ε)⌉₊

/-- After `rounds` rounds, correct processes agree up to `< ε` in every coordinate. -/
theorem approx_agreement (hV : E.Valid f s) (hs : (d + 1) * f < s) (hsn : s ≤ Fintype.card P)
    {ν U ε : ℝ} (hε : 0 < ε) (hin : ∀ k ∉ E.faulty, ∀ l, ν ≤ E.inp k l ∧ E.inp k l ≤ U)
    {i j : P} (hi : i ∉ E.faulty) (hj : j ∉ E.faulty) (l : Fin d) :
    |E.state f s (rounds (Fintype.card P) s ν U ε) i l -
      E.state f s (rounds (Fintype.card P) s ν U ε) j l| < ε := by
  refine (agreement_bound hV hs hsn hin _ hi hj l).trans_lt ?_
  have hs0 : 0 < s := by omega
  have hn : 0 < Fintype.card P := by omega
  refine rounds_spec (by linarith [gam_le_one hsn hs0]) ?_ hε
  have : 0 < gam (Fintype.card P) s := by
    unfold gam
    have := Nat.choose_pos hsn
    positivity
  linarith

end RoundExec

/-- Correctness of the round-based algorithm with subset size `s`: if `(d + 1) f < s ≤ n` and the
round exchanges are `Valid f s`, then after `rounds n s ν U ε` rounds the correct states are valid
and pairwise `ε`-close in every coordinate. -/
theorem RoundExec.correct_of_valid {f s : ℕ} {E : RoundExec P d} (hV : E.Valid f s)
    (hs : (d + 1) * f < s) (hsn : s ≤ Fintype.card P) {ν U ε : ℝ} (hε : 0 < ε)
    (hin : ∀ k ∉ E.faulty, ∀ l, ν ≤ E.inp k l ∧ E.inp k l ≤ U) :
    let R := RoundExec.rounds (Fintype.card P) s ν U ε
    ∀ i ∉ E.faulty, ∀ j ∉ E.faulty,
      E.state f s R i ∈ convexHull ℝ (E.inp '' (E.correct : Set P)) ∧
      ∀ l, |E.state f s R i l - E.state f s R j l| < ε :=
  fun _ hi _ hj => ⟨RoundExec.state_mem_convexHull hV hs _ hi,
    fun l => RoundExec.approx_agreement hV hs hsn hε hin hi hj l⟩

/-- **Theorem 5** of the paper (sufficiency of `n ≥ (d + 2) f + 1` for approximate BVC in
asynchronous systems), for the algorithm of Section 3.2 on top of AAD Component #1: in every
execution in which the round exchanges satisfy Properties 1–3 (`RoundExec.Valid f (n - f)`) and the
correct inputs lie in `[ν, U]^d`, after `rounds n (n - f) ν U ε` rounds the states of the correct
processes are in the convex hull of the correct inputs (validity) and pairwise `ε`-close in
every coordinate (`ε`-agreement). -/
theorem theorem_5 {f : ℕ} (hn : (d + 2) * f < Fintype.card P) {E : RoundExec P d}
    (hV : E.Valid f (Fintype.card P - f)) {ν U ε : ℝ} (hε : 0 < ε)
    (hin : ∀ k ∉ E.faulty, ∀ l, ν ≤ E.inp k l ∧ E.inp k l ≤ U) :
    let R := RoundExec.rounds (Fintype.card P) (Fintype.card P - f) ν U ε
    ∀ i ∉ E.faulty, ∀ j ∉ E.faulty,
      E.state f (Fintype.card P - f) R i ∈ convexHull ℝ (E.inp '' (E.correct : Set P)) ∧
      ∀ l, |E.state f (Fintype.card P - f) R i l - E.state f (Fintype.card P - f) R j l| < ε := by
  intro R i hi j hj
  have hs : (d + 1) * f < Fintype.card P - f := by
    have : (d + 2) * f = (d + 1) * f + f := by ring
    omega
  exact RoundExec.correct_of_valid hV hs (Nat.sub_le _ _) hε hin i hi j hj

/-! ### Section 4: restricted round structures (sufficiency part of Theorem 6) -/

/-- **Theorem 6, synchronous case, sufficiency.** In the restricted synchronous round structure
every correct process receives a value from every process in every round (`B_i = P`; faulty
processes may send different values to different processes, a missing message is replaced by a
default value, i.e. some value). With Step 2 of Section 3.2 (subsets of size `n - f`), approximate
BVC is achieved if `n ≥ (d + 2) f + 1`. -/
theorem theorem_6_sync {f : ℕ} (hn : (d + 2) * f < Fintype.card P) {E : RoundExec P d}
    (hB : ∀ r i, E.B r i = univ) (hf : E.faulty.card ≤ f) {ν U ε : ℝ} (hε : 0 < ε)
    (hin : ∀ k ∉ E.faulty, ∀ l, ν ≤ E.inp k l ∧ E.inp k l ≤ U) :
    let R := RoundExec.rounds (Fintype.card P) (Fintype.card P - f) ν U ε
    ∀ i ∉ E.faulty, ∀ j ∉ E.faulty,
      E.state f (Fintype.card P - f) R i ∈ convexHull ℝ (E.inp '' (E.correct : Set P)) ∧
      ∀ l, |E.state f (Fintype.card P - f) R i l - E.state f (Fintype.card P - f) R j l| < ε := by
  have hs : (d + 1) * f < Fintype.card P - f := by
    have : (d + 2) * f = (d + 1) * f + f := by ring
    omega
  have hcorr : Fintype.card P - f ≤ E.correct.card := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset P)) (fun q => q ∈ E.faulty)
    have h2 : (univ.filter fun q => q ∈ E.faulty) = E.faulty := by ext; simp
    rw [h2, card_univ] at h1
    simp only [RoundExec.correct]
    omega
  refine RoundExec.correct_of_valid ⟨hf, fun r i _ => by simp [hB], fun r i _ j _ => ?_⟩ hs
    (Nat.sub_le _ _) hε hin
  obtain ⟨C, hC, hCcard⟩ := exists_subset_card_eq hcorr
  refine ⟨C, by simp [hB], hCcard, fun k hk hkf => ?_⟩
  exact absurd hkf (RoundExec.mem_correct.1 (hC hk))

/-- **Theorem 6, asynchronous case, sufficiency.** In the restricted asynchronous round structure
every correct process waits for round-`r` messages from `n - f` processes (itself included), so
`|B_i| ≥ n - f`, and any two correct processes share the (identical) values of at least `n - 3f`
correct processes. The paper says that Step 2 is "analogous to Section 3.2"; with subsets of
size `n - f` the paper's argument does not go through (`B_i` itself has only `n - f` elements, so
`Z_i` is a single point and `Z_i ∩ Z_j` may be empty). With subsets of size `n - 3f` (any size `s`
with `(d + 1) f < s ≤ n - 3f` works) the algorithm achieves approximate BVC if
`n ≥ (d + 4) f + 1`. -/
theorem theorem_6_async {f : ℕ} (hn : (d + 4) * f < Fintype.card P) {E : RoundExec P d}
    (hB : ∀ r, ∀ i ∉ E.faulty, Fintype.card P - f ≤ (E.B r i).card) (hf : E.faulty.card ≤ f)
    {ν U ε : ℝ} (hε : 0 < ε) (hin : ∀ k ∉ E.faulty, ∀ l, ν ≤ E.inp k l ∧ E.inp k l ≤ U) :
    let R := RoundExec.rounds (Fintype.card P) (Fintype.card P - 3 * f) ν U ε
    ∀ i ∉ E.faulty, ∀ j ∉ E.faulty,
      E.state f (Fintype.card P - 3 * f) R i ∈ convexHull ℝ (E.inp '' (E.correct : Set P)) ∧
      ∀ l, |E.state f (Fintype.card P - 3 * f) R i l -
        E.state f (Fintype.card P - 3 * f) R j l| < ε := by
  have hs : (d + 1) * f < Fintype.card P - 3 * f := by
    have : (d + 4) * f = (d + 1) * f + 3 * f := by ring
    omega
  refine RoundExec.correct_of_valid ⟨hf, fun r i hi => (Nat.sub_le_sub_left (by omega) _).trans
    (hB r i hi), fun r i hi j hj => ?_⟩ hs (Nat.sub_le _ _) hε hin
  set I := (E.B r i ∩ E.B r j).filter fun k => k ∉ E.faulty
  have hI : Fintype.card P - 3 * f ≤ I.card := by
    have h1 := card_union_add_card_inter (E.B r i) (E.B r j)
    have h2 := card_le_univ (E.B r i ∪ E.B r j)
    have h3 := card_filter_add_card_filter_not (s := E.B r i ∩ E.B r j) (fun q => q ∉ E.faulty)
    have h4 : ((E.B r i ∩ E.B r j).filter fun q => ¬ q ∉ E.faulty).card ≤ f := by
      refine le_trans (card_le_card fun k hk => ?_) hf
      simp only [mem_filter, not_not] at hk; exact hk.2
    have := hB r i hi
    have := hB r j hj
    simp only [I]
    omega
  obtain ⟨C, hC, hCcard⟩ := exists_subset_card_eq hI
  refine ⟨C, hC.trans (filter_subset _ _), hCcard, fun k hk hkf => ?_⟩
  exact absurd hkf (mem_filter.1 (hC hk)).2

end ByzantineVectorConsensus
