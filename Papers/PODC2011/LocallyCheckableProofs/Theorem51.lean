import Papers.PODC2011.LocallyCheckableProofs.LowerBoundCore

/-!
# Theorem 5.1: `Ω(log n)` lower bounds

* `lowerBound_bound`: packaging of the gluing argument (`lowerBound_core`): if glued `2n`-cycles of
  correct pieces are always no-instances of `F`, then `n ≤ 4 (|L| 2^(s(n)+2))^(12r+12)`.
* `logBound_of_bound`, `not_isLittleO_log`: hence `s(n) ≥ c log n - C` on the relevant `n`, and
  `s ≠ o(log n)`.
* Instances: odd number of nodes (`theorem_5_1_oddNodes`), non-bipartite graphs
  (`theorem_5_1_nonBipartite`), leader election (`theorem_5_1_leader`). Spanning trees and maximum
  matchings: `Theorem51Edges.lean`.

Families. For graph properties the family `F` consists of unlabelled instances (`Plain`) and
contains all cycles with identifiers in `{1, …, n²}` (the paper: "`F` contains (at least) all
cycles", identifiers `poly(n)`). This is the weakest hypothesis on `F` under which the paper's
argument runs, so the lower bounds hold for every such `F` (cycles, connected graphs, all graphs).
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset Filter Asymptotics

variable {L : Type*}

/-- The instance is a cycle (on at least 3 nodes). -/
def Inst.IsCycle (I : Inst L) : Prop :=
  ∃ l : List ℕ, l.Nodup ∧ 3 ≤ l.length ∧ I.V = l.toFinset ∧ I.G = cycGraph l

lemma cyc_isCycle {l : List ℕ} (hl : l.Nodup) (h3 : 3 ≤ l.length) (lab : ℕ → L) (mk : ℕ → Bool) :
    (cyc l lab mk).IsCycle := ⟨l, hl, h3, rfl, rfl⟩

lemma cyc_idBound {l : List ℕ} (hl : l.Nodup) (lab : ℕ → L) (mk : ℕ → Bool)
    (h : ∀ x ∈ l, 1 ≤ x ∧ x ≤ l.length ^ 2) : (cyc l lab mk).IdBound 2 := by
  intro v hv
  rw [cyc_n hl]
  exact h v (by simpa using hv)

lemma Succ.mem_left {l : List ℕ} {x y : ℕ} (h : Succ l x y) : x ∈ l := by
  obtain ⟨i, hi, hx, -⟩ := h; rw [← hx]; exact List.getElem_mem hi

lemma Succ.ne {l : List ℕ} (hl : l.Nodup) (h2 : 2 ≤ l.length) {x y : ℕ} (h : Succ l x y) :
    x ≠ y := by
  obtain ⟨i, hi, hx, hy⟩ := h
  intro he
  rw [← hx, ← hy] at he
  have := (List.Nodup.getElem_inj_iff hl).1 he
  rcases Nat.lt_or_ge (i + 1) l.length with h | h
  · rw [Nat.mod_eq_of_lt h] at this; omega
  · rw [show i + 1 = l.length by omega, Nat.mod_self] at this; omega

lemma cyc_plain {l : List ℕ} {lab : ℕ → L} {mk : ℕ → Bool} (h : ∀ x ∈ l, mk x = false) :
    (cyc l lab mk).Plain := by
  ext x y
  rw [cyc_sadj]
  simp only [bot_adj, iff_false]
  rintro ⟨-, ⟨hs, hm⟩ | ⟨hs, hm⟩⟩
  · rw [h _ hs.mem_left] at hm; exact Bool.false_ne_true hm
  · rw [h _ hs.mem_left] at hm; exact Bool.false_ne_true hm

lemma cyc_marks_false {l : List ℕ} {lab : ℕ → L} {mk : ℕ → Bool} (h2 : 2 ≤ l.length)
    (hl : l.Nodup) (hp : (cyc l lab mk).Plain) : ∀ x ∈ l, mk x = false := by
  intro x hx
  by_contra hm
  have hs : Succ l x (nxt l x) := (succ_iff_nxt hl).2 ⟨hx, rfl⟩
  have hS : (cyc l lab mk).S.Adj x (nxt l x) := by
    rw [cyc_sadj]
    exact ⟨hs.ne hl h2, Or.inl ⟨hs, by simpa using hm⟩⟩
  rw [Inst.Plain] at hp
  rw [hp] at hS
  exact hS

/-! ### The glued instance -/

section Glued

variable {n : ℕ} {lab : Fin n → Fin n → ℕ → L} {mk : Fin n → Fin n → ℕ → Bool} {a₁ a₂ b₁ b₂ : Fin n}

lemma glued_nodup (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) : (lstN n a₁ b₁ ++ lstN n a₂ b₂).Nodup :=
  (goodLists_blk n).nodup_two ha hb

lemma glued_length : (lstN n a₁ b₁ ++ lstN n a₂ b₂).length = 2 * n := by
  simp [lstN_length]; ring

lemma glued_n (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) : (glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂).n = 2 * n := by
  rw [glued, cyc_n (glued_nodup ha hb), glued_length]

lemma glued_isCycle (hn : 2 ≤ n) (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    (glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂).IsCycle :=
  cyc_isCycle (glued_nodup ha hb) (by rw [glued_length]; omega) _ _

lemma glued_idBound (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    (glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂).IdBound 2 := by
  refine cyc_idBound (glued_nodup ha hb) _ _ fun x hx => ?_
  rw [glued_length]
  have : x ∈ lstN n a₁ b₁ ∨ x ∈ lstN n a₂ b₂ := List.mem_append.1 hx
  have hb' : 1 ≤ x ∧ x ≤ n ^ 2 := by
    rcases this with h | h <;> exact mem_lstN_bound h
  refine ⟨hb'.1, hb'.2.trans ?_⟩
  exact Nat.pow_le_pow_left (by omega) 2

/-- The glued instance is plain if the pieces are. -/
lemma glued_plain (hn : 2 ≤ n) (_ha : a₁ ≠ a₂) (_hb : b₁ ≠ b₂)
    (h : ∀ a b, (cyc (lstN n a b) (lab a b) (mk a b)).Plain) :
    (glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂).Plain := by
  have hG := goodLists_blk n
  have hm : ∀ a b, ∀ x ∈ lstN n a b, mk a b x = false := fun a b =>
    cyc_marks_false (by rw [lstN_length]; omega) (hG.nodup_lst a b) (h a b)
  apply cyc_plain
  intro x hx
  by_cases h1 : x ∈ lst (blkA n) (blkB n) a₁ b₁
  · rw [piece_of_mem h1]; exact hm _ _ x h1
  · rw [piece_of_not_mem h1]
    exact hm _ _ x ((List.mem_append.1 hx).resolve_left h1)

end Glued

/-! ### Packaging -/

/-- **The gluing lower bound, quantitative form.** If for every `n` with `good n` the cycles
`C(a,b)` have correct labellings in `F`, and every glued `2n`-cycle of correct pieces is a
no-instance of `F`, then every (weak) scheme of horizon `r` has
`n ≤ 4 (|L| 2^(s(n)+2))^(12r+12)` for all `n ≥ 4r+4` with `good n`. -/
theorem lowerBound_bound [Fintype L] [DecidableEq L] {F P : Set (Inst L)} {s : ℕ → ℕ}
    (good : ℕ → Prop) (hW : AdmitsWeakLCP F P s)
    (hyes : ∀ n, 4 ≤ n → good n → ∀ a b : Fin n, ∃ J ∈ F, J ∈ P ∧ J.V = (lstN n a b).toFinset ∧
      J.G = cycGraph (lstN n a b))
    (hno : ∀ n, 4 ≤ n → good n → ∀ (lab : Fin n → Fin n → ℕ → L) (mk : Fin n → Fin n → ℕ → Bool),
      (∀ a b, cyc (lstN n a b) (lab a b) (mk a b) ∈ F ∧ cyc (lstN n a b) (lab a b) (mk a b) ∈ P) →
      ∀ a₁ a₂ b₁ b₂, a₁ ≠ a₂ → b₁ ≠ b₂ →
        glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂ ∈ F ∧
          glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂ ∉ P) :
    ∃ r : ℕ, ∀ n, 4 * r + 4 ≤ n → good n →
      n ≤ 4 * (Fintype.card L * 2 ^ (s n + 2)) ^ (12 * r + 12) := by
  obtain ⟨r, hr⟩ := lowerBound_core hW
  refine ⟨r, fun n hn hg => ?_⟩
  set K := (Fintype.card L * 2 ^ (s n + 2)) ^ (4 * r + 4) with hK
  have hK3 : K * (K + 1) ^ 2 ≤ 4 * (Fintype.card L * 2 ^ (s n + 2)) ^ (12 * r + 12) := by
    rw [show 12 * r + 12 = (4 * r + 4) * 3 by ring, pow_mul, ← hK]
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · simp [h0]
    · have : (K + 1) ^ 2 ≤ 4 * K ^ 2 := by nlinarith
      calc K * (K + 1) ^ 2 ≤ K * (4 * K ^ 2) := Nat.mul_le_mul_left _ this
        _ = 4 * K ^ 3 := by ring
  by_contra hcon
  have hlt : K * (K + 1) ^ 2 < n := by omega
  obtain ⟨lab, mk, hpieces, a₁, a₂, b₁, b₂, ha, hb, himp⟩ :=
    hr n hn hlt (hyes n (by omega) hg)
  obtain ⟨hF, hP⟩ := hno n (by omega) hg lab mk hpieces a₁ a₂ b₁ b₂ ha hb
  exact hP (himp hF)

/-- From the quantitative bound to `s(n) ≥ c log n - C`. -/
theorem logBound_of_bound {s : ℕ → ℕ} {good : ℕ → Prop} {M r : ℕ} (hM : 1 ≤ M)
    (h : ∀ n, 4 * r + 4 ≤ n → good n → n ≤ 4 * (M * 2 ^ (s n + 2)) ^ (12 * r + 12)) :
    ∃ c > (0 : ℝ), ∃ C : ℝ, ∀ n, good n → c * Real.log n - C ≤ s n := by
  set m : ℝ := 12 * r + 12 with hm
  have hm0 : 0 < m := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  set c : ℝ := 1 / (m * Real.log 2) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, (Real.log 4 + m * Real.log M) / (m * Real.log 2) + 2 +
    c * Real.log (4 * r + 4), fun n hg => ?_⟩
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ (Real.log 4 + m * Real.log M) / (m * Real.log 2) := by positivity
  rcases Nat.lt_or_ge n (4 * r + 4) with hn | hn
  · -- small `n`
    have : c * Real.log n ≤ c * Real.log (4 * r + 4) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · have : (1 : ℝ) ≤ 4 * r + 4 := by have : (0 : ℝ) ≤ r := by positivity
                                         linarith
        simp only [h0, CharP.cast_eq_zero, Real.log_zero, mul_zero]
        exact mul_nonneg hc0.le (Real.log_nonneg this)
      · gcongr
        exact_mod_cast hn.le
    have : (0 : ℝ) ≤ s n := by positivity
    linarith
  · have hb := h n hn hg
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : Real.log n ≤ Real.log 4 + m * (Real.log M + (s n + 2) * Real.log 2) := by
      have hb' : (n : ℝ) ≤ 4 * ((M : ℝ) * 2 ^ (s n + 2)) ^ (12 * r + 12) := by exact_mod_cast hb
      have hMp : (0 : ℝ) < M := by exact_mod_cast hM
      calc Real.log n ≤ Real.log (4 * ((M : ℝ) * 2 ^ (s n + 2)) ^ (12 * r + 12)) :=
            Real.log_le_log hpos hb'
        _ = Real.log 4 + m * (Real.log M + (s n + 2) * Real.log 2) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_mul
              (by positivity) (by positivity), Real.log_pow]
            simp [hm]
    have key : c * Real.log n ≤ (Real.log 4 + m * Real.log M) / (m * Real.log 2) + (s n + 2) := by
      rw [hc, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      rw [add_mul, div_mul_cancel₀ _ (by positivity)]
      nlinarith
    have : 0 ≤ c * Real.log (4 * r + 4) := by
      have : (1 : ℝ) ≤ 4 * r + 4 := by have : (0 : ℝ) ≤ r := by positivity
                                       linarith
      exact mul_nonneg hc0.le (Real.log_nonneg this)
    linarith

/-- A function with `s(n) ≥ c log n - C` on a frequent set of `n` is not `o(log n)`. -/
theorem not_isLittleO_log {s : ℕ → ℕ} {good : ℕ → Prop} {c C : ℝ} (hc : 0 < c)
    (h : ∀ n, good n → c * Real.log n - C ≤ s n) (hfreq : ∃ᶠ n in atTop, good n) :
    ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) := by
  intro ho
  have h1 := ho.bound (show 0 < c / 2 by positivity)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 := hlog.eventually_gt_atTop (2 * C / c)
  have h3 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log n := hlog.eventually_ge_atTop 0
  obtain ⟨n, hg, hb, hgt, hpos⟩ := (hfreq.and_eventually (h1.and (h2.and h3))).exists
  have := h n hg
  simp only [Real.norm_eq_abs, abs_of_nonneg hpos] at hb
  have := le_abs_self (s n : ℝ)
  have : c / 2 * Real.log n ≤ C := by linarith
  have : 2 * C / c < Real.log n := hgt
  rw [div_lt_iff₀ hc] at this
  linarith

/-! ### Theorem 5.1 for graph properties -/

/-- The family hypothesis for graph properties: unlabelled instances, including all cycles with
identifiers in `{1, …, n²}`. -/
structure PlainCycleFamily (F : Set (Inst L)) : Prop where
  plain : ∀ I ∈ F, I.Plain
  cycles : ∀ I : Inst L, I.IsCycle → I.IdBound 2 → I.Plain → I ∈ F

/-- Graphs with an odd number of nodes. -/
def OddNodes : Set (Inst L) := {I | Odd I.n}

/-- Non-bipartite graphs (chromatic number `> 2`). -/
def NonBipartite : Set (Inst L) := {I | ¬ I.G.Colorable 2}

/-- An even cycle is bipartite. -/
lemma cyc_colorable_two {l : List ℕ} (hl : l.Nodup) (he : Even l.length) (lab : ℕ → L)
    (mk : ℕ → Bool) : (cyc l lab mk).G.Colorable 2 := by
  refine ⟨Coloring.mk (fun x => (⟨l.idxOf x % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
  intro x y hxy
  rw [cyc_G, cycGraph, fromRel_adj] at hxy
  obtain ⟨-, h⟩ := hxy
  -- adjacent nodes have consecutive positions modulo the even length
  have key : ∀ u v, Succ l u v → (l.idxOf u % 2) ≠ (l.idxOf v % 2) := by
    rintro u v ⟨i, hi, rfl, rfl⟩
    rw [hl.idxOf_getElem, hl.idxOf_getElem]
    obtain ⟨k, hk⟩ := he
    rcases Nat.lt_or_ge (i + 1) l.length with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]; omega
    · rw [show i + 1 = l.length by omega, Nat.mod_self]; omega
  intro hc
  have hc' : l.idxOf x % 2 = l.idxOf y % 2 := congrArg Fin.val hc
  rcases h with h | h
  · exact key x y h hc'
  · exact key y x h hc'.symm

/-- An odd cycle is not bipartite. -/
lemma cyc_not_colorable_two {l : List ℕ} (hl : l.Nodup) (ho : Odd l.length) (h3 : 3 ≤ l.length)
    (lab : ℕ → L) (mk : ℕ → Bool) : ¬ (cyc l lab mk).G.Colorable 2 := by
  rintro ⟨c⟩
  have hadj : ∀ (i : ℕ) (hi : i + 1 < l.length), (cyc l lab mk).G.Adj l[i] l[i + 1] := by
    intro i hi
    rw [cyc_G, cycGraph, fromRel_adj]
    refine ⟨fun he => ?_, Or.inl ⟨i, by omega, rfl, ?_⟩⟩
    · have := (List.Nodup.getElem_inj_iff hl).1 he; omega
    · simp only [Nat.mod_eq_of_lt hi]
  -- colours alternate along the list
  have alt : ∀ (i : ℕ) (hi : i < l.length),
      (c l[i]).val = ((c (l[0]'(by omega))).val + i) % 2 := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.add_zero, Nat.mod_eq_of_lt (c _).isLt]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := c.valid (hadj i hi)
      have h3' := (c l[i]).isLt
      have h4 := (c l[i + 1]).isLt
      have : (c l[i]).val ≠ (c l[i + 1]).val := fun h => h2 (Fin.ext h)
      omega
  have hlast : (cyc l lab mk).G.Adj (l[l.length - 1]'(by omega)) (l[0]'(by omega)) := by
    rw [cyc_G, cycGraph, fromRel_adj]
    refine ⟨fun he => ?_, Or.inl ⟨l.length - 1, by omega, rfl, ?_⟩⟩
    · have := (List.Nodup.getElem_inj_iff hl).1 he; omega
    · simp only [show l.length - 1 + 1 = l.length by omega, Nat.mod_self]
  have h1 := alt (l.length - 1) (by omega)
  have h2 := c.valid hlast
  obtain ⟨k, hk⟩ := ho
  have h0 := (c (l[0]'(by omega))).isLt
  have : (c (l[l.length - 1]'(by omega))).val = (c (l[0]'(by omega))).val := by
    rw [h1, show l.length - 1 = 2 * k by omega]; omega
  exact h2 (Fin.ext this)

/-- Common setting for graph properties: the yes-instances `C(a,b)` are plain cycles. -/
lemma hyes_plain {F : Set (Inst L)} [Inhabited L] (hF : PlainCycleFamily F) (P : Set (Inst L))
    {n : ℕ} (hn : 3 ≤ n) (hP : ∀ a b : Fin n, cyc (lstN n a b) (fun _ => default) (fun _ => false) ∈ P)
    (a b : Fin n) :
    ∃ J ∈ F, J ∈ P ∧ J.V = (lstN n a b).toFinset ∧ J.G = cycGraph (lstN n a b) := by
  have hnd := (goodLists_blk n).nodup_lst a b
  refine ⟨_, hF.cycles _ (cyc_isCycle hnd (by rw [lstN_length]; omega) _ _)
    (cyc_idBound hnd _ _ fun x hx => by rw [lstN_length]; exact mem_lstN_bound hx)
    (cyc_plain fun _ _ => rfl), hP a b, rfl, rfl⟩

/-- In a plain-cycle family, the glued instance of correct pieces belongs to `F`. -/
lemma glued_mem_plain {F : Set (Inst L)} (hF : PlainCycleFamily F) {n : ℕ} (hn : 4 ≤ n)
    {lab : Fin n → Fin n → ℕ → L} {mk : Fin n → Fin n → ℕ → Bool}
    (hpieces : ∀ a b, cyc (lstN n a b) (lab a b) (mk a b) ∈ F) {a₁ a₂ b₁ b₂ : Fin n}
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) : glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂ ∈ F :=
  hF.cycles _ (glued_isCycle (by omega) ha hb) (glued_idBound ha hb)
    (glued_plain (by omega) ha hb fun a b => hF.plain _ (hpieces a b))

/-- **Theorem 5.1 (odd number of nodes).** On any family of unlabelled graphs containing all
cycles (with identifiers in `{1,…,n²}`), every locally checkable proof for "odd number of nodes" has
size `s(n) ≥ c log n - C` for all odd `n`; in particular `s ≠ o(log n)`. -/
theorem theorem_5_1_oddNodes {F : Set (Inst Unit)} (hF : PlainCycleFamily F) {s : ℕ → ℕ}
    (h : AdmitsWeakLCP F OddNodes s) :
    (∃ c > (0 : ℝ), ∃ C : ℝ, ∀ n : ℕ, Odd n → c * Real.log n - C ≤ s n) ∧
      ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) := by
  obtain ⟨r, hr⟩ := lowerBound_bound (fun n => Odd n) h
    (fun n hn hg a b => hyes_plain hF _ (by omega)
      (fun a b => by
        show Odd (cyc _ _ _).n
        rw [cyc_n ((goodLists_blk n).nodup_lst a b), lstN_length]; exact hg) a b)
    (fun n hn hg lab mk hpieces a₁ a₂ b₁ b₂ ha hb => ⟨glued_mem_plain hF hn
      (fun a b => (hpieces a b).1) ha hb, by
        show ¬ Odd _
        rw [glued_n ha hb]; simp⟩)
  obtain ⟨c, hc, C, hC⟩ := logBound_of_bound (M := 1) le_rfl (by simpa using hr)
  refine ⟨⟨c, hc, C, hC⟩, not_isLittleO_log hc hC ?_⟩
  exact Filter.frequently_atTop.2 fun N => ⟨2 * N + 1, by omega, odd_two_mul_add_one N⟩

/-- **Theorem 5.1 (non-bipartite graphs).** On any family of unlabelled graphs containing all cycles
(identifiers in `{1,…,n²}`), every locally checkable proof for non-bipartiteness has size
`s(n) ≥ c log n - C` for all odd `n`; in particular `s ≠ o(log n)`. -/
theorem theorem_5_1_nonBipartite {F : Set (Inst Unit)} (hF : PlainCycleFamily F) {s : ℕ → ℕ}
    (h : AdmitsWeakLCP F NonBipartite s) :
    (∃ c > (0 : ℝ), ∃ C : ℝ, ∀ n : ℕ, Odd n → c * Real.log n - C ≤ s n) ∧
      ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) := by
  obtain ⟨r, hr⟩ := lowerBound_bound (fun n => Odd n) h
    (fun n hn hg a b => hyes_plain hF _ (by omega)
      (fun a b => cyc_not_colorable_two ((goodLists_blk n).nodup_lst a b)
        (by rw [lstN_length]; exact hg) (by rw [lstN_length]; omega) _ _) a b)
    (fun n hn hg lab mk hpieces a₁ a₂ b₁ b₂ ha hb => ⟨glued_mem_plain hF hn
      (fun a b => (hpieces a b).1) ha hb, fun hP => hP (cyc_colorable_two (glued_nodup ha hb)
        (by rw [glued_length]; simp) _ _)⟩)
  obtain ⟨c, hc, C, hC⟩ := logBound_of_bound (M := 1) le_rfl (by simpa using hr)
  refine ⟨⟨c, hc, C, hC⟩, not_isLittleO_log hc hC ?_⟩
  exact Filter.frequently_atTop.2 fun N => ⟨2 * N + 1, by omega, odd_two_mul_add_one N⟩

end Podc.LocallyCheckableProofs

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset Filter Asymptotics

/-! ### Theorem 5.1 for leader election -/

/-- Leader election: exactly one node is labelled `true`. -/
def LeaderElection : Set (Inst Bool) := {I | (I.V.filter fun v => I.lab v = true).card = 1}

lemma glued_V {L : Type*} {n : ℕ} {lab : Fin n → Fin n → ℕ → L} {mk : Fin n → Fin n → ℕ → Bool}
    {a₁ a₂ b₁ b₂ : Fin n} :
    (glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂).V =
      (lstN n a₁ b₁).toFinset ∪ (lstN n a₂ b₂).toFinset := by
  simp [glued, List.toFinset_append]

lemma glued_disjoint {n : ℕ} {a₁ a₂ b₁ b₂ : Fin n} (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    Disjoint (lstN n a₁ b₁).toFinset (lstN n a₂ b₂).toFinset := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  exact (List.nodup_append.1 (glued_nodup ha hb)).2.2 x (by simpa using h1) x (by simpa using h2) rfl

/-- **Theorem 5.1 (leader election).** On any family of node-labelled graphs without marked edges
containing all cycles (identifiers in `{1,…,n²}`, arbitrary labels), every weak (hence every strong)
proof labelling scheme for leader election has size `s(n) ≥ c log n - C`; in particular
`s ≠ o(log n)`. -/
theorem theorem_5_1_leader {F : Set (Inst Bool)} (hF : PlainCycleFamily F) {s : ℕ → ℕ}
    (h : AdmitsWeakLCP F LeaderElection s) :
    (∃ c > (0 : ℝ), ∃ C : ℝ, ∀ n : ℕ, c * Real.log n - C ≤ s n) ∧
      ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) := by
  classical
  obtain ⟨r, hr⟩ := lowerBound_bound (fun _ => True) h
    (fun n hn _ a b => by
      have hnd := (goodLists_blk n).nodup_lst a b
      have hlen := lstN_length n a b
      let x0 := (lstN n a b)[0]'(by omega)
      refine ⟨cyc (lstN n a b) (fun x => decide (x = x0)) (fun _ => false),
        hF.cycles _ (cyc_isCycle hnd (by unfold lstN at hlen; omega) _ _)
          (cyc_idBound hnd _ _ fun x hx => by rw [hlen]; exact mem_lstN_bound hx)
          (cyc_plain fun _ _ => rfl), ?_, rfl, rfl⟩
      show ((lstN n a b).toFinset.filter fun v => decide (v = x0) = true).card = 1
      rw [Finset.card_eq_one]
      refine ⟨x0, ?_⟩
      ext v
      simp only [decide_eq_true_eq, Finset.mem_filter, List.mem_toFinset, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨List.getElem_mem _, rfl⟩)
    (fun n hn _ lab mk hpieces a₁ a₂ b₁ b₂ ha hb => ⟨glued_mem_plain hF hn
      (fun a b => (hpieces a b).1) ha hb, by
        intro hP
        change (_ : Finset ℕ).card = 1 at hP
        rw [glued_V, Finset.filter_union, Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter (glued_disjoint ha hb))] at hP
        have h1 := (hpieces a₁ b₁).2
        have h2 := (hpieces a₂ b₂).2
        change ((lstN n a₁ b₁).toFinset.filter fun v => lab a₁ b₁ v = true).card = 1 at h1
        change ((lstN n a₂ b₂).toFinset.filter fun v => lab a₂ b₂ v = true).card = 1 at h2
        have e1 : ((lstN n a₁ b₁).toFinset.filter fun v =>
            (glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂).lab v = true) =
            ((lstN n a₁ b₁).toFinset.filter fun v => lab a₁ b₁ v = true) := by
          refine Finset.filter_congr fun v hv => ?_
          simp only [glued, cyc_lab, piece_of_mem (List.mem_toFinset.1 hv)]
        have e2 : ((lstN n a₂ b₂).toFinset.filter fun v =>
            (glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂).lab v = true) =
            ((lstN n a₂ b₂).toFinset.filter fun v => lab a₂ b₂ v = true) := by
          refine Finset.filter_congr fun v hv => ?_
          have : v ∉ lst (blkA n) (blkB n) a₁ b₁ := fun h' =>
            Finset.disjoint_left.1 (glued_disjoint ha hb) (List.mem_toFinset.2 h') hv
          simp only [glued, cyc_lab, piece_of_not_mem this]
        rw [e1, e2, h1, h2] at hP
        omega⟩)
  obtain ⟨c, hc, C, hC⟩ := logBound_of_bound (M := 2) (by norm_num)
    (fun n hn _ => by simpa using hr n hn trivial)
  exact ⟨⟨c, hc, C, fun n => hC n trivial⟩, not_isLittleO_log hc (fun n _ => hC n trivial)
    (Filter.Frequently.of_forall fun _ => trivial)⟩

end Podc.LocallyCheckableProofs
