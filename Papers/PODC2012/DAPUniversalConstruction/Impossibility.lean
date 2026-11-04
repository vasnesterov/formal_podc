import Papers.PODC2012.DAPUniversalConstruction.Instances

/-!
# Theorem 5: no feebly disjoint-access parallel universal construction is wait-free

The proof of Section 4. Fix an implementation `I` of the list (from arbitrary base objects) that
is linearizable, feebly disjoint-access parallel and satisfies the value-obliviousness assumption
for `Append`, and two processes `p ≠ q`. Assume it is wait-free (we only use obstruction-freedom
to build the execution).

* `q` appends `1, 2, 3, …` (`f₀ k = k + 1`): configurations `Cᵢ = cfg f₀ i`; `W k` / `Ac k` are
  the base objects written / accessed by the `k`-th append (paper: `B(k+1)` and
  `A(k+1) ∪ B(k+1)`).
* `p` runs `Search(0)` solo from `Cᵢ` (from `Dc i`). `blen t D` is the length of the longest
  prefix of `p`'s solo run from `D` that neither accesses an object of `W k` nor writes an object
  of `Ac k`, for any `k ≥ t` (paper: `βᵢʲ` with `t = j - 1`).
* `M i = blen (i - 3) (Dc i)` (paper: the length of `βᵢⁱ⁻²`). Lemma 4 becomes
  `blen_stable` and `M_mono`.
* `pending_bad`: after `M i` steps, `p` has not returned (otherwise it would return the same
  response from `Cᵢ` and from `Cᵢⁱ⁻²`, where `0` is in the list), so its next step is "bad".
* `M_lt`: `M i < M (i + 3)` — the paper's contradiction with feeble disjoint-access parallelism
  in the configuration `C_{ℓ-1}^{ℓ-3}`.
* `exec`: the infinite execution `α₁ α₂ α₃ α₄ β₄² α₅ γ₅ α₆ γ₆ ⋯`, in which `p` takes infinitely
  many steps without returning (`theorem_5_list`).
-/

set_option linter.unusedSectionVars false

namespace Podc.DAPUniversalConstruction

open Cslib.SharedMemory Impl

variable {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

/-- The values appended by `q` in the main execution: `1, 2, 3, …`. -/
def f₀ (k : ℕ) : ℤ := k + 1

section Proof

variable (I : Impl listSpec B P L) (p q : P)

/-- Base objects written by the `k`-th append of the main execution (paper: `B(k+1)`). -/
noncomputable abbrev W (k : ℕ) : Set ι := I.written (cfg I q f₀ k) (seg I q f₀ k)

/-- Base objects accessed by the `k`-th append of the main execution (paper: `A(k+1) ∪ B(k+1)`). -/
noncomputable abbrev Ac (k : ℕ) : Set ι := I.accessed (cfg I q f₀ k) (seg I q f₀ k)

/-- `p`'s next step in `E` is forbidden for threshold `t`: it accesses an object written by some
append `k ≥ t`, or writes an object accessed by some append `k ≥ t`. -/
def Bad (t : ℕ) (E : Config listSpec B P L) : Prop :=
  ∃ k, t ≤ k ∧ ∃ b, (b ∈ W I q k ∧ I.SoloAcc p b E) ∨ (b ∈ Ac I q k ∧ I.SoloWr p b E)

/-- `p`'s solo run stops at `E` (for threshold `t`): its next step is forbidden or it has
returned. -/
def Stop (t : ℕ) (E : Config listSpec B P L) : Prop := Bad I p q t E ∨ E.pend p = none

open Classical in
/-- Length of the longest prefix of `p`'s solo run from `D` without forbidden steps (paper: the
length of `β`). -/
noncomputable def blen (t : ℕ) (D : Config listSpec B P L) : ℕ :=
  if h : ∃ m, Stop I p q t ((I.soloStep p)^[m] D) then Nat.find h else 0

/-- `p` has invoked `Search(0)` after the first `n` appends of the main execution. -/
noncomputable abbrev Dc (n : ℕ) : Config listSpec B P L := dcfg I q p f₀ n

/-- Paper: the length of `βᵢⁱ⁻²`. -/
noncomputable def M (i : ℕ) : ℕ := blen I p q (i - 3) (Dc I p q i)

variable {I p q}

lemma blen_spec {t : ℕ} {D : Config listSpec B P L}
    (h : ∃ m, Stop I p q t ((I.soloStep p)^[m] D)) :
    Stop I p q t ((I.soloStep p)^[blen I p q t D] D) ∧
      ∀ m < blen I p q t D, ¬ Stop I p q t ((I.soloStep p)^[m] D) := by
  classical
  simp only [blen, dite_eq_left h]
  exact ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩

lemma blen_eq {t N : ℕ} {D : Config listSpec B P L}
    (h1 : Stop I p q t ((I.soloStep p)^[N] D))
    (h2 : ∀ m < N, ¬ Stop I p q t ((I.soloStep p)^[m] D)) : blen I p q t D = N := by
  classical
  have h : ∃ m, Stop I p q t ((I.soloStep p)^[m] D) := ⟨N, h1⟩
  simp only [blen, dite_eq_left h]
  exact (Nat.find_eq_iff h).2 ⟨h1, h2⟩

lemma exists_stop (hOF : I.ObstructionFree) {D : Config listSpec B P L} (hD : I.Reachable D)
    (t : ℕ) : ∃ m, Stop I p q t ((I.soloStep p)^[m] D) := by
  by_cases hp : D.pend p = none
  · exact ⟨0, Or.inr hp⟩
  · obtain ⟨m, hm⟩ := hOF D p hD hp
    exact ⟨m, Or.inr hm⟩

lemma bad_mono {t t' : ℕ} (htt : t ≤ t') {E : Config listSpec B P L} (h : Bad I p q t' E) :
    Bad I p q t E := by
  obtain ⟨k, hk, hb⟩ := h
  exact ⟨k, by omega, hb⟩

lemma stop_mono {t t' : ℕ} (htt : t ≤ t') {E : Config listSpec B P L} (h : Stop I p q t' E) :
    Stop I p q t E := h.imp (bad_mono htt) id

lemma blen_mono (hOF : I.ObstructionFree) {t t' : ℕ} (htt : t ≤ t') {D : Config listSpec B P L}
    (hD : I.Reachable D) : blen I p q t D ≤ blen I p q t' D := by
  have h' := blen_spec (exists_stop (p := p) (q := q) hOF hD t')
  have h := blen_spec (exists_stop (p := p) (q := q) hOF hD t)
  by_contra hlt
  exact h.2 _ (by omega) (stop_mono htt h'.1)

lemma bad_congr {X : Set ι} {E E' : Config listSpec B P L} (h : AgreeExcept p X E E')
    (t : ℕ) : Bad I p q t E ↔ Bad I p q t E' := by
  simp only [Bad, h.soloAcc_iff, h.soloWr_iff]

lemma stop_congr {X : Set ι} {E E' : Config listSpec B P L} (h : AgreeExcept p X E E')
    (t : ℕ) : Stop I p q t E ↔ Stop I p q t E' := by
  simp only [Stop, bad_congr h, h.pend]

/-- **Agreement along `β`.** Solo runs of `p` from configurations that agree outside objects
written by appends `≥ t` take the same steps up to the end of `β`. -/
lemma agree_run {t : ℕ} {X : Set ι} {D D' : Config listSpec B P L}
    (hD : AgreeExcept p X D D') (hX : ∀ b ∈ X, ∃ k, t ≤ k ∧ b ∈ W I q k)
    (hex : ∃ m, Stop I p q t ((I.soloStep p)^[m] D)) :
    blen I p q t D' = blen I p q t D ∧ ∀ m ≤ blen I p q t D,
      AgreeExcept p X ((I.soloStep p)^[m] D) ((I.soloStep p)^[m] D') ∧
        I.soloLabels p D m = I.soloLabels p D' m := by
  obtain ⟨hs1, hs2⟩ := blen_spec hex
  have key : ∀ m ≤ blen I p q t D,
      AgreeExcept p X ((I.soloStep p)^[m] D) ((I.soloStep p)^[m] D') ∧
        I.soloLabels p D m = I.soloLabels p D' m := by
    intro m hm
    refine hD.iterate_soloStep m (fun k hk b hb hacc => ?_)
    obtain ⟨k', hk', hbk⟩ := hX b hb
    exact hs2 k (by omega) (Or.inl ⟨k', hk', b, Or.inl ⟨hbk, hacc⟩⟩)
  refine ⟨blen_eq ((stop_congr (key _ le_rfl).1 t).1 hs1)
    (fun m hm => fun h => hs2 m hm ((stop_congr (key m hm.le).1 t).2 h)), key⟩

variable (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (hvo : ImplValueOblivious I LOp.append)
include hall hOF hvo

/-- By the value-obliviousness assumption, the `k`-th append writes and accesses the same base
objects whatever the appended values. -/
lemma written_seg (f : ℕ → ℤ) (k : ℕ) :
    I.written (cfg I q f k) (seg I q f k) = W I q k ∧
      I.accessed (cfg I q f k) (seg I q f k) = Ac I q k := by
  obtain ⟨h1, h2⟩ := hvo I.initCfg q ⟨[], rfl⟩ (fun _ => rfl) f f₀ k
  exact ⟨h2, h1⟩

omit hvo in
lemma reachable_Dc (n : ℕ) : I.Reachable (Dc I p q n) := reachable_dcfg (q := q) hall hOF p f₀ n

/-- Configurations of the form `dcfg f n` whose values agree below `j` agree (on `p`) outside
the objects written by the appends `j, …, n - 1`. -/
lemma agree_dcfg (hpq : p ≠ q) {f g : ℕ → ℤ} {j n : ℕ} (hjn : j ≤ n)
    (hfg : ∀ k < j, f k = g k) :
    AgreeExcept p {b | ∃ k, j ≤ k ∧ k < n ∧ b ∈ W I q k} (dcfg I q p f n) (dcfg I q p g n) := by
  obtain ⟨a1, a2, a3⟩ := dcfg_loc_pend (q := q) hall hOF hpq f n
  obtain ⟨b1, b2, b3⟩ := dcfg_loc_pend (q := q) hall hOF hpq g n
  refine ⟨a1.trans b1.symm, a2.trans b2.symm, fun i hi => ?_⟩
  rw [a3, b3]
  have hw : ∀ (h : ℕ → ℤ) k, j ≤ k → k < n → i ∉ I.written (cfg I q h k) (seg I q h k) := by
    intro h k h1 h2 hik
    rw [(written_seg hall hOF hvo h k).1] at hik
    exact hi ⟨k, h1, h2, hik⟩
  rw [mem_cfg_eq hall hOF f hjn (hw f), mem_cfg_eq hall hOF g hjn (hw g), cfg_congr hfg]

omit hvo in
/-- Only the objects written by the `n`-th append differ between `Cₙ` and `Cₙ₊₁`. -/
lemma agree_succ (hpq : p ≠ q) (n : ℕ) :
    AgreeExcept p (W I q n) (Dc I p q n) (Dc I p q (n + 1)) := by
  obtain ⟨a1, a2, a3⟩ := dcfg_loc_pend (q := q) hall hOF hpq f₀ n
  obtain ⟨b1, b2, b3⟩ := dcfg_loc_pend (q := q) hall hOF hpq f₀ (n + 1)
  refine ⟨a1.trans b1.symm, a2.trans b2.symm, fun i hi => ?_⟩
  rw [a3, b3, mem_eq_of_not_written (run_seg (q := q) hall hOF f₀ n).1 hi]

/-- **Lemma 4** (first part, iterated): for `t ≤ n ≤ n'`, `β` has the same length from `Cₙ` and
from `Cₙ'`, with the same steps and the same states of `p` along it. -/
lemma blen_stable (hpq : p ≠ q) {t n n' : ℕ} (htn : t ≤ n) (hnn : n ≤ n') :
    blen I p q t (Dc I p q n') = blen I p q t (Dc I p q n) ∧
      ∀ m ≤ blen I p q t (Dc I p q n),
        AgreeExcept p Set.univ ((I.soloStep p)^[m] (Dc I p q n))
          ((I.soloStep p)^[m] (Dc I p q n')) ∧
        I.soloLabels p (Dc I p q n) m = I.soloLabels p (Dc I p q n') m := by
  induction n', hnn using Nat.le_induction with
  | base => exact ⟨rfl, fun m _ => ⟨⟨rfl, rfl, fun _ h => absurd trivial h⟩, rfl⟩⟩
  | succ n' hnn ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hag := agree_succ (p := p) hall hOF hpq n'
    obtain ⟨h1, h2⟩ := agree_run (t := t) hag
      (fun b hb => ⟨n', by omega, hb⟩) (exists_stop hOF (reachable_Dc hall hOF n') t)
    refine ⟨h1.trans ih1, fun m hm => ?_⟩
    obtain ⟨e1, e2⟩ := ih2 m hm
    obtain ⟨e3, e4⟩ := h2 m (by rw [ih1]; exact hm)
    exact ⟨(e1.trans e3).mono (Set.subset_univ _), e2.trans e4⟩

/-- **Lemma 4** (second part): `β_{i}^{i-2}` is a prefix of `β_{i+1}^{i-1}`. -/
lemma M_mono (hpq : p ≠ q) {i : ℕ} (hi : 3 ≤ i) : M I p q i ≤ M I p q (i + 1) := by
  unfold M
  calc blen I p q (i - 3) (Dc I p q i)
      = blen I p q (i - 3) (Dc I p q (i + 1)) :=
        (blen_stable hall hOF hvo hpq (t := i - 3) (n := i) (n' := i + 1) (by omega)
          (by omega)).1.symm
    _ ≤ blen I p q (i + 1 - 3) (Dc I p q (i + 1)) :=
        blen_mono hOF (by omega) (reachable_Dc hall hOF _)

omit hall hOF hvo in
/-- A process that is pending and becomes idle during its solo run returns in it. -/
lemma exists_ret_of_idle {D : Config listSpec B P L} (hD : D.pend p ≠ none) {m : ℕ}
    (hm : ((I.soloStep p)^[m] D).pend p = none) : ∃ r, .ret p r ∈ I.soloLabels p D m := by
  induction m generalizing D with
  | zero => exact absurd hm hD
  | succ m ih =>
    rw [soloLabels_succ, ite_eq_right hD]
    cases hact : I.act p (D.loc p) with
    | access i o k =>
      have hnl : I.nextLabel D p = .tau p := by simp [nextLabel, hact]
      have hs := step_nextLabel (I := I) hD
      rw [hnl] at hs
      have hp' : (I.soloStep p D).pend p ≠ none := by rw [(step_tau hs).2.1]; exact hD
      rw [Function.iterate_succ_apply] at hm
      obtain ⟨r, hr⟩ := ih hp' hm
      exact ⟨r, List.mem_cons_of_mem _ hr⟩
    | ret r l =>
      have hnl : I.nextLabel D p = .ret p r := by simp [nextLabel, hact]
      exact ⟨r, by rw [hnl]; exact List.mem_cons_self⟩

omit hall hOF hvo in
/-- A process that is still pending after `m` solo steps took only internal steps. -/
lemma eq_tau_of_pending {D : Config listSpec B P L} {m : ℕ}
    (hm : ((I.soloStep p)^[m] D).pend p ≠ none) : ∀ ℓ ∈ I.soloLabels p D m, ℓ = .tau p := by
  induction m generalizing D with
  | zero => simp [soloLabels]
  | succ m ih =>
    by_cases hD : D.pend p = none
    · rw [Function.iterate_succ_apply', iterate_soloStep_of_idle hD, soloStep_of_idle hD] at hm
      exact absurd hD hm
    rw [soloLabels_succ, ite_eq_right hD]
    rw [Function.iterate_succ_apply] at hm
    intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · cases hact : I.act p (D.loc p) with
      | access i o k => simp [nextLabel, hact]
      | ret r l =>
        exfalso
        have hs := step_nextLabel (I := I) hD
        have hnl : I.nextLabel D p = .ret p r := by simp [nextLabel, hact]
        rw [hnl] at hs
        have hidle : (I.soloStep p D).pend p = none := by rw [(step_ret hs).2.1]; simp
        rw [iterate_soloStep_of_idle hidle] at hm
        exact hm hidle
    · exact ih hm ℓ hℓ

omit [DecidableEq P] [DecidableEq ι] hall hOF hvo in
lemma zero_not_mem_vals (n : ℕ) : 0 ∉ vals f₀ n := by
  simp only [vals, f₀, List.mem_map, List.mem_range, not_exists, not_and]
  intro k _ h; omega

/-- After `β_i^{i-2}`, process `p` has not returned (otherwise `Search(0)` would return the same
response from `Cᵢ` and from `Cᵢⁱ⁻²`), so its next step is forbidden. -/
lemma pending_bad (hlin : I.Linearizable) (hpq : p ≠ q) {i : ℕ} (hi : 3 ≤ i) :
    ((I.soloStep p)^[M I p q i] (Dc I p q i)).pend p ≠ none ∧
      Bad I p q (i - 3) ((I.soloStep p)^[M I p q i] (Dc I p q i)) := by
  have hspec := blen_spec (exists_stop (p := p) (q := q) hOF
    (reachable_Dc (p := p) (q := q) hall hOF i) (i - 3))
  have hpend : ((I.soloStep p)^[M I p q i] (Dc I p q i)).pend p ≠ none := by
    intro hidle
    have hD : (Dc I p q i).pend p ≠ none := by
      rw [(dcfg_loc_pend hall hOF hpq f₀ i).2.1]; simp
    obtain ⟨r, hr⟩ := exists_ret_of_idle hD hidle
    set g := Function.update f₀ (i - 3) 0 with hg
    have hag := agree_dcfg hall hOF hvo hpq (f := f₀) (g := g) (j := i - 3) (n := i)
      (by omega) (fun k hk => by rw [hg, Function.update_of_ne (by omega)])
    obtain ⟨-, h2⟩ := agree_run (t := i - 3) hag
      (fun b ⟨k, hk1, hk2, hb⟩ => ⟨k, hk1, hb⟩) (exists_stop hOF (reachable_Dc hall hOF i) _)
    have hr' := hr
    rw [(h2 (M I p q i) le_rfl).2] at hr'
    have e1 := search_resp hall hOF hlin hpq f₀ i _ hr
    have e2 := search_resp hall hOF hlin hpq g i _ hr'
    have hz : (0 : ℤ) ∈ vals g i := by
      simp only [vals, List.mem_map, List.mem_range]
      exact ⟨i - 3, by omega, by rw [hg, Function.update_self]⟩
    rw [e1] at e2
    simp only [hz, decide_true, decide_eq_true_eq] at e2
    exact zero_not_mem_vals i e2
  exact ⟨hpend, hspec.1.resolve_right hpend⟩

omit [DecidableEq P] [DecidableEq ι] hall hOF hvo in
lemma idxOf_le {l : List ℤ} {a : ℤ} {i : ℕ} (hi : i < l.length) (h : l[i] = a) :
    l.idxOf a ≤ i := by
  by_contra hc
  push Not at hc
  have := List.not_of_lt_findIdx (p := (· == a)) (by simpa [List.idxOf] using hc)
  simp [h] at this

omit [DecidableEq P] [DecidableEq ι] hall hOF hvo in
/-- In `C_{k}^{k-2}` (paper: `C_{ℓ-1}^{ℓ-3}` with `ℓ = k + 1`), the list has `k` nodes and its
third-last node holds `0`: `Search(0)` accesses `L.start` and the first `k - 2` nodes,
`Append(k+1)` accesses `L.end`, the last node and the new node. -/
lemma dataSets_disjoint {k : ℕ} (hk : 4 ≤ k) :
    Disjoint (listDataSet (vals (Function.update f₀ (k - 3) 0) k) (.search 0))
      (listDataSet (vals (Function.update f₀ (k - 3) 0) k) (.append (k + 1))) := by
  set h := Function.update f₀ (k - 3) 0 with hh
  have hlen : (vals h k).length = k := by simp [vals]
  have hne : vals h k ≠ [] := by rw [← List.length_pos_iff, hlen]; omega
  have hidx : (vals h k).idxOf 0 ≤ k - 3 :=
    idxOf_le (by rw [hlen]; omega) (by simp [vals, hh])
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [listDataSet, hlen, ite_eq_right hne, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx'
  simp only [listDataSet, Set.mem_insert_iff, Set.mem_ofPred_eq] at hx
  rcases hx with rfl | ⟨j, rfl, -, hj⟩
  · rcases hx' with (h1 | h1) | h1 <;> cases h1
  · rcases hx' with (h1 | h1) | h1
    · cases h1
    · cases h1; omega
    · cases h1; omega

/-- **The core of the proof of Theorem 5**: `γ_{i+1} γ_{i+2} γ_{i+3}` is nonempty, i.e.
`βᵢⁱ⁻² ≠ β_{i+3}^{i+1}`. Otherwise `p`'s next step after `βᵢⁱ⁻²` accesses an object written by
some `Append(ℓ)`, `ℓ ≥ i + 1`, or writes an object it accesses; but from `C_{ℓ-1}^{ℓ-3}` the
solo runs of `Search(0)` and `Append(ℓ)` have disjoint data sets and take these same steps, so
they contend, contradicting feeble disjoint-access parallelism. -/
lemma M_lt (hlin : I.Linearizable) (hdap : FeeblyDAP I listDataSet) (hpq : p ≠ q) {i : ℕ}
    (hi : 4 ≤ i) : M I p q i < M I p q (i + 3) := by
  by_contra hcon
  push Not at hcon
  have hmono : M I p q i ≤ M I p q (i + 3) :=
    (M_mono hall hOF hvo hpq (by omega)).trans ((M_mono hall hOF hvo hpq (by omega)).trans
      (M_mono hall hOF hvo hpq (by omega)))
  have hEq : M I p q (i + 3) = M I p q i := le_antisymm hcon hmono
  obtain ⟨hpend, -⟩ := pending_bad hall hOF hvo hlin hpq (i := i) (by omega)
  have stab := fun n' (h : i ≤ n') =>
    blen_stable hall hOF hvo hpq (t := i - 3) (n := i) (n' := n') (by omega) h
  set Y := (I.soloStep p)^[M I p q i] (Dc I p q i) with hY
  set Y' := (I.soloStep p)^[M I p q i] (Dc I p q (i + 3)) with hY'
  have hYY' : AgreeExcept p Set.univ Y Y' := ((stab (i + 3) (by omega)).2 (M I p q i) le_rfl).1
  -- `p`'s next step in `Y'` is forbidden for threshold `i`
  have hspec := blen_spec (exists_stop (p := p) (q := q) hOF
    (reachable_Dc (p := p) (q := q) hall hOF (i + 3)) i)
  have hM3 : blen I p q i (Dc I p q (i + 3)) = M I p q i := by
    rw [← hEq]; simp only [M, Nat.add_sub_cancel]
  rw [hM3] at hspec
  have hbad : Bad I p q i Y' := hspec.1.resolve_right (by rw [← hYY'.pend]; exact hpend)
  obtain ⟨k, hik, b, hb⟩ := hbad
  -- the configuration `C_{k}^{k-2}`
  set h := Function.update f₀ (k - 3) 0 with hh
  have hagG := agree_dcfg hall hOF hvo hpq (f := f₀) (g := h) (j := k - 3) (n := k) (by omega)
    (fun j hj => by rw [hh, Function.update_of_ne (by omega)])
  obtain ⟨-, hrun2⟩ := agree_run (t := i - 3) hagG
    (fun b ⟨k', hk1, hk2, hb⟩ => ⟨k', by omega, hb⟩)
    (exists_stop hOF (reachable_Dc hall hOF k) _)
  have hMk : M I p q i ≤ blen I p q (i - 3) (dcfg I q p f₀ k) := by
    rw [(stab k (by omega)).1]; rfl
  have hDG : AgreeExcept p Set.univ Y' ((I.soloStep p)^[M I p q i] (dcfg I q p h k)) :=
    ((hYY'.symm.trans ((stab k (by omega)).2 (M I p q i) le_rfl).1).trans
      (hrun2 (M I p q i) hMk).1).mono (Set.subset_univ _)
  -- feeble disjoint-access parallelism in `C_{k}^{k-2}`
  obtain ⟨hr1, hr2, -⟩ := run_pre (q := q) hall hOF h k
  obtain ⟨G₁, hG₁⟩ : ∃ G₁, I.step (cfg I q h k) (.inv q (.append (k + 1))) = some G₁ :=
    ⟨_, step_inv_eq_some (hr2 q) (hall _ _)⟩
  have hseg : soloPrefix I q (.append (k + 1)) (cfg I q h k) (I.soloTime q G₁) = seg I q h k := by
    have hhk : h k = k + 1 := by rw [hh, Function.update_of_ne (by omega)]; simp [f₀]
    simp only [soloPrefix, hG₁, seg, instSeg, soloOp, hhk]
  have hpre : soloPrefix I p (.search 0) (cfg I q h k) (M I p q i + 1) =
      .inv p (.search 0) :: I.soloLabels p (dcfg I q p h k) (M I p q i + 1) := by
    simp only [soloPrefix, step_dcfg (q := q) hall hOF p h k]
  have hacc_p : ∀ c, c ∈ I.accessed (cfg I q h k)
      (soloPrefix I p (.search 0) (cfg I q h k) (M I p q i + 1)) ↔
      ∃ m < M I p q i + 1, I.SoloAcc p c ((I.soloStep p)^[m] (dcfg I q p h k)) := by
    intro c
    rw [hpre, accessed_cons_of_step (step_dcfg hall hOF p h k), Set.mem_union,
      mem_accessed_soloLabels]
    simp [StepAccess]
  have hwr_p : ∀ c, c ∈ I.written (cfg I q h k)
      (soloPrefix I p (.search 0) (cfg I q h k) (M I p q i + 1)) ↔
      ∃ m < M I p q i + 1, I.SoloWr p c ((I.soloStep p)^[m] (dcfg I q p h k)) := by
    intro c
    rw [hpre, written_cons_of_step (step_dcfg hall hOF p h k), Set.mem_union,
      mem_written_soloLabels]
    simp [StepWrite]
  obtain ⟨hw, ha⟩ := written_seg hall hOF hvo (q := q) h k
  refine hdap (pre I q h k) (cfg I q h k) (vals h k) hr1 hr2
    (representsState_pre hall hOF hlin h k) p q (.search 0) (.append (k + 1)) (M I p q i + 1)
    (I.soloTime q G₁) hpq (dataSets_disjoint (by omega)) ⟨b, ?_⟩
  rw [hseg, hw, ha, hacc_p, hwr_p]
  rcases hb with ⟨hbW, hbA⟩ | ⟨hbA, hbW⟩
  · refine ⟨⟨M I p q i, by omega, (hDG.soloAcc_iff b).1 hbA⟩,
      written_subset_accessed _ _ hbW, Or.inr hbW⟩
  · have hw' := (hDG.soloWr_iff b).1 hbW
    exact ⟨⟨M I p q i, by omega, hw'.1, hw'.2.choose, hw'.2.choose_spec.choose,
      hw'.2.choose_spec.choose_spec.1⟩, hbA, Or.inl ⟨M I p q i, by omega, hw'⟩⟩

end Proof

end Podc.DAPUniversalConstruction
