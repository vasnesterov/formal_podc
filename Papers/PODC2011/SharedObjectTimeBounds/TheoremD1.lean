import Papers.PODC2011.SharedObjectTimeBounds.Setup

/-!
# Theorem D.1 of Chapter IV: `(1 - 1/k) u` for last-permuting operation types

Thesis statement: let `OP` be immediately self-commuting, with `k ≥ 2`, a sequence `ρ` and `k`
distinct instances `op_i ∈ OP` such that every `ρ ∘ op_i` is legal and any two legal permutations
`π`, `π'` of the `op_i` with different last elements are not equivalent. Then in a system with
`n ≥ k` processes, `ε`-bounded clocks and delays in `[d - u, d]`, `|OP| ≥ (1 - 1/k) u`.

The proof shifts the run `R₁` (all `op_i` invoked simultaneously by `p_0, …, p_{k-1}`, delays
`d - ((i - j) mod k) u / k`) by `x_i = (-(k-1)/2 + ((z - i) mod k)/k) u` (a typo for
`-(k-1)/(2k)`, as the later text "`p_z` is shifted by `-[(k-1)/2k] u`" shows), where `z` is the last
operation of "the" linearization of `R₁`. Two problems:

* the shifted run has clock skew `(1 - 1/k) u`, so the theorem needs `ε ≥ (1 - 1/k) u` (the
  thesis assumes the optimal skew `ε = (1 - 1/n) u` in the proof);
* Step 1.1 claims a single permutation `π` that determines the results of *every* later sequence
  of operations; correctness does not give this (an algorithm may decide the order lazily). We
  replace the non-equivalence hypothesis by `LastRevealing`: one fixed sequence of later
  invocations `α` whose results determine the last element of the permutation (for a register:
  one read; for a stack: one pop; for a queue: `k` dequeues). For `k = 2` the thesis hypothesis
  implies it (`theorem_D1_two`).

Proof as in the thesis, with the following details: `p_0` first runs `ρ` sequentially (times
`0, g, 2g, …`), the `op_i` start once `ρ` is over, and `α` is run by `p_0` after all `op_i`
responded. The shift is normalised so that `p_0` is not moved (`x' = x - x_{p_0}`; a uniform
shift changes neither delays nor skews), so the `ρ`- and `α`-invocations are the same in `R₁`
and `R₂` and both runs return the same results for `α` (same local histories). All delays of
`R₁` and `R₂` are checked to lie in `[d - u, d]` (`dly1_bounds`, `dly_shift_bounds`); the thesis's
case analysis is correct.
-/

namespace Podc.SharedObjectTimeBounds

open Cslib.TimedMP

variable {P I R M : Type*}

/-- The permutation `σ` of the `k` operations, as a sequence. -/
def permSeq {k : ℕ} (ops : Fin k → I × R) (σ : Equiv.Perm (Fin k)) : List (I × R) :=
  List.ofFn (ops ∘ σ)

/-- Repaired hypothesis of Theorem D.1: a fixed sequence of invocations `α` whose return values
reveal the last operation of the permutation. -/
def LastRevealing (legal : List (I × R) → Prop) {k : ℕ} (hk : 0 < k) (ρ : List (I × R))
    (ops : Fin k → I × R) : Prop :=
  ∃ α : List I, ∀ (σ σ' : Equiv.Perm (Fin k)) (rs : List R), rs.length = α.length →
    legal (ρ ++ permSeq ops σ ++ α.zip rs) → legal (ρ ++ permSeq ops σ' ++ α.zip rs) →
    σ ⟨k - 1, by omega⟩ = σ' ⟨k - 1, by omega⟩

/-! ## Auxiliary lemmas -/

/-- Every arrangement of the `ops` is legal after `ρ'` if each one is (immediate
self-commutativity). -/
theorem legal_map_ops {legal : List (I × R) → Prop} {OP : I → Prop}
    (hsc : ImmSelfCommuting legal OP) {k : ℕ} {ops : Fin k → I × R} (hops : ∀ i, OP (ops i).1) :
    ∀ (l : List (Fin k)) (ρ' : List (I × R)), legal ρ' → (∀ j ∈ l, legal (ρ' ++ [ops j])) →
      legal (ρ' ++ l.map ops)
  | [], ρ', h, _ => by simpa using h
  | i :: l, ρ', h, hl => by
    have hi := hl i List.mem_cons_self
    have := legal_map_ops hsc hops l (ρ' ++ [ops i]) hi (fun j hj => by
      have := (hsc.comm (hops i) (hops j) hi (hl j (List.mem_cons_of_mem _ hj))).1
      simpa using this)
    simpa using this

/-- A duplicate-free list of all indices is a permutation. -/
theorem exists_perm_ofFn {k : ℕ} (l : List (Fin k)) (hnd : l.Nodup) (hlen : l.length = k) :
    ∃ σ : Equiv.Perm (Fin k), List.ofFn σ = l := by
  have hinj : Function.Injective (fun i : Fin k => l.get (Fin.cast hlen.symm i)) := by
    intro a b h
    have := (List.Nodup.get_inj_iff hnd).mp h
    exact Fin.cast_injective _ this
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), ?_⟩
  apply List.ext_getElem (by simp [hlen])
  intro n h1 h2
  simp

theorem permSeq_eq {k : ℕ} (ops : Fin k → I × R) (σ : Equiv.Perm (Fin k)) :
    permSeq ops σ = (List.ofFn σ).map ops := by
  simp [permSeq, List.map_ofFn]

/-- If the elements of `Y` are in order in `L` and after all elements of `X`, then `L` ends
with `Y`. -/
theorem split_last {α : Type*} {X Y L : List α} (hp : L.Perm (X ++ Y)) (hnd : L.Nodup)
    (hY : Y.Pairwise (fun a b => [a, b].Sublist L)) (hxy : ∀ x ∈ X, ∀ y ∈ Y, [x, y].Sublist L) :
    ∃ L', L = L' ++ Y ∧ L'.Perm X := by
  have hp' : L.reverse.Perm (Y.reverse ++ X.reverse) := by
    rw [← List.reverse_append]
    exact (List.reverse_perm L).trans (hp.trans (List.reverse_perm _).symm)
  have hrev : ∀ a b, [a, b].Sublist L → [b, a].Sublist L.reverse := fun a b h => by
    simpa using List.reverse_sublist.mpr h
  obtain ⟨L'', h1, h2⟩ := peel Y.reverse X.reverse L.reverse hp' (List.nodup_reverse.mpr hnd)
    (List.pairwise_reverse.mpr (hY.imp fun h => hrev _ _ h))
    (fun y hy x hx => hrev _ _ (hxy x (List.mem_reverse.mp hx) y (List.mem_reverse.mp hy)))
  refine ⟨L''.reverse, ?_, ?_⟩
  · have := congrArg List.reverse h1
    simpa using this
  · exact (List.reverse_perm _).trans (h2.trans (List.reverse_perm _))

theorem sublist_pair_append_left {α : Type*} {a b : α} {Y : List α} :
    ∀ {X : List α}, [a, b].Sublist (X ++ Y) → b ∉ Y → [a, b].Sublist X
  | [], h, hb => absurd (h.subset (by simp)) hb
  | x :: X, h, hb => by
    rcases List.sublist_cons_iff.mp h with h | ⟨r, h1, h2⟩
    · exact (sublist_pair_append_left h hb).cons x
    · simp only [List.cons.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have : b ∈ X ++ Y := h2.subset (by simp)
      rcases List.mem_append.mp this with h | h
      · exact (List.singleton_sublist.mpr h).cons_cons _
      · exact absurd h hb

/-- A duplicate-free permutation of the images of an injective `f` is the image of an index
list. -/
theorem exists_idx {α : Type*} {k : ℕ} (hk : 0 < k) {f : Fin k → α} (hf : Function.Injective f)
    {L : List α} (hp : L.Perm ((List.finRange k).map f)) (hnd : L.Nodup) :
    ∃ l : List (Fin k), L = l.map f ∧ l.Nodup ∧ l.length = k := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hL : L = (L.map (Function.invFun f)).map f := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id L]
    apply List.map_congr_left
    intro c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp (hp.subset hc)
    simp [Function.leftInverse_invFun hf i]
  refine ⟨_, hL, ?_, ?_⟩
  · rw [hL] at hnd; exact hnd.of_map _
  · simpa using hp.length_eq

theorem last_ne_of_sublist {k : ℕ} (hk : 0 < k) (σ : Equiv.Perm (Fin k)) {a b : Fin k}
    (h : [a, b].Sublist (List.ofFn σ)) : σ ⟨k - 1, by omega⟩ ≠ a := by
  obtain ⟨r₁, r₂, he, ha, hb⟩ := List.cons_sublist_iff.mp h
  have hnd : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  have hne : r₂ ≠ [] := by rintro rfl; simp at hb
  have hne' : List.ofFn σ ≠ [] := by simp; omega
  have hlast : (List.ofFn σ).getLast hne' = σ ⟨k - 1, by omega⟩ := List.getLast_ofFn _
  intro heq
  have hm : (List.ofFn σ).getLast hne' ∈ r₂ := by
    simp_rw [he]; rw [List.getLast_append_of_ne_nil _ hne]; exact List.getLast_mem _
  rw [hlast, heq] at hm
  rw [he] at hnd
  exact (List.nodup_append.mp hnd).2.2 a ha a hm rfl

/-- Shifting preserves well-formedness. -/
theorem wf_shift [Finite P] {A : Algorithm P I R M} {s : Scenario P I}
    {H : P → Set (ℝ × InEv P I M)} (hwf : WF A s H) (x : P → ℝ) : WF A (s.shift x) H := by
  obtain ⟨hnd, hid, htm, hrs⟩ := hwf
  refine ⟨hnd.map (fun c c' h => ?_), ?_, ?_, ?_⟩
  · have h1 := congrArg Call.p h
    have h2 := congrArg Call.k h
    have h3 := congrArg Call.t h
    have h4 := congrArg Call.a h
    simp only at h1 h2 h3 h4
    rw [h1] at h3
    ext <;> first | assumption | linarith
  · simp only [Scenario.shift, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hp hk
    simp only at hp hk
    rw [hid c hc c' hc' hp hk]
  · simp only [Scenario.shift, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hp ht
    simp only at hp ht
    rw [hp] at ht
    rw [htm c hc c' hc' hp (by linarith)]
  · simp only [Scenario.shift, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hp ht
    simp only at hp ht
    rw [hp] at ht
    obtain ⟨σ, r, hr, h1, h2⟩ := hrs c hc c' hc' hp (by linarith)
    refine ⟨σ + x c.p, r, (respAt_shift x c σ r).mpr hr, by simp only; linarith,
      by simp only; rw [hp]; linarith⟩

/-! ## The runs of the proof -/

/-- The operation `op_i`: process `proc i`, id `K + i`, real time `T + y i`. -/
def opCall {k : ℕ} (proc : Fin k → P) (ops : Fin k → I × R) (K : ℕ) (T : ℝ) (y : Fin k → ℝ)
    (i : Fin k) : Call P I :=
  ⟨proc i, K + i, T + y i, (ops i).1⟩

/-- The later invocations `α` at `p₀` (ids `N, N+1, …`, times `N g, (N+1) g, …`). -/
def alphaCalls (p₀ : P) (g : ℝ) (N : ℕ) (α : List I) (r0 : R) : List (Call P I) :=
  rhoCallsFrom p₀ g N (α.map fun a => (a, r0))

/-- Reading off the linearization of a run consisting of the `ρ`-phase, the operations `op_i`
(at times `T + y i`) and the invocations `α` (after all `op_i` responded): `ρ ∘ π ∘ α` with
`π` a permutation of the `op_i` respecting the real-time order. -/
theorem lin_aux [Finite P] (A : Algorithm P I R M) {legal : List (I × R) → Prop}
    (hpc : PrefixClosed legal) (hdet : Deterministic legal)
    {d u ε Bop g B : ℝ} (hcor : Correct A legal d u ε)
    (hBop : TimeBound A d u ε (fun _ => True) Bop) (hg : Bop < g) (hg0 : 0 < g)
    {OP : I → Prop} (hsc : ImmSelfCommuting legal OP) (hB : TimeBound A d u ε OP B)
    {k : ℕ} (hk : 0 < k) (proc : Fin k → P) (ρ : List (I × R)) (ops : Fin k → I × R)
    (hops : ∀ i, OP (ops i).1) (hleg : ∀ i, legal (ρ ++ [ops i]))
    (p₀ : P) (α : List I) (r0 : R) (K N : ℕ) (T : ℝ) (y : Fin k → ℝ)
    (hy1 : ∀ i, ρ.length * g ≤ T + y i) (hy2 : ∀ i, T + y i + B < N * g) (hN : ρ.length ≤ N)
    (s : Scenario P I)
    (hs : s.calls = rhoCalls p₀ g ρ ++
      ((List.finRange k).map (opCall proc ops K T y) ++ alphaCalls p₀ g N α r0))
    (hadm : s.Admissible d u ε) {H : P → Set (ℝ × InEv P I M)} (hH : IsRun A s H)
    (hwf : WF A s H) :
    ∃ ret : Call P I → R, ∃ l : List (Fin k), l.Nodup ∧ l.length = k ∧
      legal (ρ ++ l.map ops ++ α.zip ((alphaCalls p₀ g N α r0).map ret)) ∧
      (∀ c ∈ alphaCalls p₀ g N α r0, ∃ σ, RespAt A s H c σ (ret c)) ∧
      (∀ c ∈ alphaCalls p₀ g N α r0, ∀ σ r, RespAt A s H c σ r → r = ret c) ∧
      ∀ i j, y i + B < y j → [i, j].Sublist l := by
  set αC := alphaCalls p₀ g N α r0 with hαC
  set opC := opCall proc ops K T y with hopC
  have hρ : legal ρ := hpc _ _ (hleg ⟨0, hk⟩)
  have hcont : ∀ c ∈ (List.finRange k).map opC ++ αC, ρ.length * g ≤ c.t := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc; exact hy1 i
    · obtain ⟨-, h1, -, h3⟩ := mem_rhoCallsFrom hc
      rw [h3]
      have : (N : ℝ) ≤ c.k := by exact_mod_cast h1
      have : (ρ.length : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
  obtain ⟨rt, ret, hr, -, L, hLp, hLnd, hLl, hLrt⟩ :=
    contLin A hpc hdet hcor hBop hg hg0 hρ hcont s hs hadm hH hwf
  have hmem : ∀ c ∈ (List.finRange k).map opC ++ αC, c ∈ s.calls := fun c hc => by
    rw [hs]; exact List.mem_append_right _ hc
  have hmemO : ∀ i, opC i ∈ (List.finRange k).map opC ++ αC := fun i =>
    List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  have hdisj : ∀ i, opC i ∉ αC := by
    intro i hi
    have h0 := hs ▸ hwf.1
    have h2 := List.nodup_append.mp (List.nodup_append.mp h0).2.1
    exact h2.2.2 (opC i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩) (opC i) hi rfl
  have hrtO : ∀ i, rt (opC i) ≤ T + y i + B := fun i =>
    hB s H hadm hH hwf (opC i) (hmem _ (hmemO i)) (hops i) _ _ (hr _ (hmem _ (hmemO i))).2.1
  have hαpw : αC.Pairwise (fun a b => [a, b].Sublist L) :=
    (pairwise_rhoCallsFrom N _).imp_of_mem fun {a b} ha hb hab => by
      apply hLrt a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)
      have h1 := hBop s H hadm hH hwf a (hmem a (List.mem_append_right _ ha)) trivial _ _
        (hr a (hmem a (List.mem_append_right _ ha))).2.1
      rw [(mem_rhoCallsFrom ha).2.2.2] at h1
      rw [(mem_rhoCallsFrom hb).2.2.2]
      have : ((a.k + 1 : ℕ) : ℝ) ≤ b.k := by exact_mod_cast hab
      push_cast at this; nlinarith
  have hxy : ∀ x ∈ (List.finRange k).map opC, ∀ y' ∈ αC, [x, y'].Sublist L := by
    intro x hx y' hy'
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    apply hLrt _ (List.mem_append_left _ hx) _ (List.mem_append_right _ hy')
    have h1 := hrtO i
    rw [(mem_rhoCallsFrom hy').2.2.2]
    have : (N : ℝ) ≤ y'.k := by exact_mod_cast (mem_rhoCallsFrom hy').2.1
    have := hy2 i
    nlinarith
  obtain ⟨L', rfl, hL'⟩ := split_last hLp hLnd hαpw hxy
  have hinj : Function.Injective opC := fun i j h => by
    have := congrArg Call.k h
    simp only [opC, opCall] at this
    exact Fin.ext (by omega)
  obtain ⟨l, rfl, hlnd, hllen⟩ := exists_idx hk hinj hL' (List.nodup_append.mp hLnd).1
  refine ⟨ret, l, hlnd, hllen, ?_, ?_, ?_, ?_⟩
  · have hmap : (l.map opC).map (fun c => (c.a, ret c)) = l.map ops := by
      refine det_seq hpc hdet _ _ ρ ?_ (legal_map_ops hsc hops l ρ hρ (fun j _ => hleg j)) ?_
      · rw [List.map_append, ← List.append_assoc] at hLl; exact hpc _ _ hLl
      · simp [List.map_map, opC, opCall, Function.comp_def]
    have hα : αC.map (fun c => (c.a, ret c)) = α.zip (αC.map ret) := by
      rw [← List.zip_map']
      congr 1
      simp only [hαC, alphaCalls]
      rw [map_a_rhoCallsFrom]
      simp [List.map_map, Function.comp_def]
    rw [List.map_append, hmap, hα, ← List.append_assoc] at hLl; exact hLl
  · intro c hc; exact ⟨rt c, (hr c (hmem c (List.mem_append_right _ hc))).2.1⟩
  · intro c hc σ r h; exact ((hr c (hmem c (List.mem_append_right _ hc))).2.2 σ r h).2
  · intro i j hij
    have h := hLrt _ (hmemO i) _ (hmemO j) (by
      have := hrtO i
      show rt (opC i) < T + y j
      linarith)
    have h' := sublist_pair_append_left h (hdisj j)
    obtain ⟨l', hl', he⟩ := List.sublist_map_iff.mp h'
    have : l' = [i, j] := List.map_injective_iff.mpr hinj (by simpa using he.symm)
    rw [this] at hl'
    exact hl'

/-! ## Delays and shifts -/

/-- `(i - j) mod k` for `i, j < k`. -/
def md (k i j : ℕ) : ℕ := if j ≤ i then i - j else i + k - j

theorem md_lt {k i j : ℕ} (hi : i < k) (hj : j < k) : md k i j + 1 ≤ k := by
  unfold md; split_ifs <;> omega

theorem md_key {k i j z : ℕ} (hi : i < k) (hj : j < k) :
    md k i j + md k z i = md k z j ∨ md k i j + md k z i = md k z j + k := by
  unfold md; split_ifs <;> omega

open Classical in
/-- Delays of the run `R₁`: `d - ((i - j) mod k) u / k` from `proc i` to `proc j ≠ proc i`,
`d - u / 2` for all other pairs (`c = u / k`). -/
noncomputable def dly1 {k : ℕ} (proc : Fin k → P) (idx : P → Fin k) (d u c : ℝ) (q r : P) : ℝ :=
  if q ∈ Set.range proc ∧ r ∈ Set.range proc ∧ q ≠ r then d - md k (idx q) (idx r) * c
  else d - u / 2

open Classical in
/-- The shift of the proof: `proc i` by `((z - i) mod k) u / k - (k - 1) u / (2 k)`, other
processes by `0`. -/
noncomputable def shiftX {k : ℕ} (proc : Fin k → P) (idx : P → Fin k) (c : ℝ) (z : Fin k)
    (p : P) : ℝ :=
  if p ∈ Set.range proc then md k z (idx p) * c - (k - 1) * c / 2 else 0

theorem shiftX_proc {k : ℕ} {proc : Fin k → P} {idx : P → Fin k}
    (hidx : ∀ i, idx (proc i) = i) (c : ℝ) (z i : Fin k) :
    shiftX proc idx c z (proc i) = md k z i * c - (k - 1) * c / 2 := by
  simp [shiftX, hidx]

theorem abs_shiftX {k : ℕ} (hk : 0 < k) (proc : Fin k → P) (idx : P → Fin k) {c : ℝ}
    (hc : 0 ≤ c) (z : Fin k) (p : P) : |shiftX proc idx c z p| ≤ (k - 1) * c / 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold shiftX
  split_ifs
  · have h : (md k z (idx p) : ℝ) + 1 ≤ k := by exact_mod_cast md_lt z.isLt (idx p).isLt
    have h1 := mul_le_mul_of_nonneg_right (show (md k z (idx p) : ℝ) ≤ k - 1 by linarith) hc
    have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) (md k z (idx p))) hc
    rw [abs_le]; constructor <;> linarith
  · simp only [abs_zero]
    have := mul_nonneg (show (0 : ℝ) ≤ k - 1 by linarith) hc
    linarith

theorem dly1_bounds {k : ℕ} (hk : 2 ≤ k) (proc : Fin k → P) (idx : P → Fin k) {d u c : ℝ}
    (hd : 0 < d) (hc : 0 ≤ c) (huc : u = k * c) (hud : u ≤ d) (q r : P) :
    d / k ≤ dly1 proc idx d u c q r ∧ d - u ≤ dly1 proc idx d u c q r ∧
      dly1 proc idx d u c q r ≤ d := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set e := d / k with he
  have hde : d = k * e := by rw [he]; field_simp
  have hce : c ≤ e := by
    by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h (show (0 : ℝ) < k by linarith); linarith
  have he0 : 0 < e := div_pos hd (by linarith)
  unfold dly1
  split_ifs
  · have h : (md k (idx q) (idx r) : ℝ) + 1 ≤ k := by
      exact_mod_cast md_lt (idx q).isLt (idx r).isLt
    have h1 := mul_le_mul_of_nonneg_right (show (md k (idx q) (idx r) : ℝ) ≤ k - 1 by linarith) hc
    have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) (md k (idx q) (idx r))) hc
    have h3 := mul_le_mul_of_nonneg_left hce (show (0 : ℝ) ≤ k - 1 by linarith)
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · have hu0 : 0 ≤ u := by rw [huc]; positivity
    refine ⟨by nlinarith, by linarith, by linarith⟩

theorem dly_shift_bounds {k : ℕ} (hk : 2 ≤ k) {proc : Fin k → P}
    {idx : P → Fin k} (hidx : ∀ i, idx (proc i) = i) {d u c : ℝ} (hc : 0 ≤ c)
    (huc : u = k * c) (z : Fin k) (q r : P) :
    d - u ≤ dly1 proc idx d u c q r + shiftX proc idx c z r - shiftX proc idx c z q ∧
      dly1 proc idx d u c q r + shiftX proc idx c z r - shiftX proc idx c z q ≤ d := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < k := by omega
  unfold dly1
  split_ifs with h
  · obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩, hne⟩ := h
    rw [shiftX_proc hidx, shiftX_proc hidx, hidx, hidx]
    rcases md_key (z := z) i.isLt j.isLt with e | e
    · have e' : (md k i j : ℝ) * c + md k z i * c = md k z j * c := by
        rw [← add_mul]; exact_mod_cast congrArg (fun n : ℕ => (n : ℝ) * c) e
      constructor <;> nlinarith
    · have e' : (md k i j : ℝ) * c + md k z i * c = md k z j * c + k * c := by
        rw [← add_mul, ← add_mul]; exact_mod_cast congrArg (fun n : ℕ => (n : ℝ) * c) e
      have : (0 : ℝ) ≤ k * c := by positivity
      constructor <;> linarith
  · have hu0 : 0 ≤ u := by rw [huc]; positivity
    have hb : (k - 1) * c / 2 ≤ u / 2 := by rw [huc]; nlinarith
    by_cases hqr : q = r
    · subst hqr; constructor <;> linarith
    · have : q ∉ Set.range proc ∨ r ∉ Set.range proc := by tauto
      have hq := abs_le.mp (abs_shiftX hk0 proc idx hc z q)
      have hr := abs_le.mp (abs_shiftX hk0 proc idx hc z r)
      rcases this with h' | h'
      · have : shiftX proc idx c z q = 0 := by simp [shiftX, h']
        rw [this]; constructor <;> linarith [hr.1, hr.2]
      · have : shiftX proc idx c z r = 0 := by simp [shiftX, h']
        rw [this]; constructor <;> linarith [hq.1, hq.2]

/-- **Theorem D.1 of Chapter IV** (repaired: `ε ≥ (1 - 1/k) u` and `LastRevealing`). -/
theorem theorem_D1 [Fintype P] [DecidableEq P] (A : Algorithm P I R M)
    {legal : List (I × R) → Prop} (hpc : PrefixClosed legal) (hdet : Deterministic legal)
    {d u ε : ℝ} (hd : 0 < d) (hu : 0 ≤ u) (hud : u ≤ d)
    {k : ℕ} (hk : 2 ≤ k) (hε : (1 - 1 / (k : ℝ)) * u ≤ ε)
    (hcor : Correct A legal d u ε) {Bop : ℝ} (hBop : TimeBound A d u ε (fun _ => True) Bop)
    (proc : Fin k → P) (hproc : Function.Injective proc)
    {OP : I → Prop} (hsc : ImmSelfCommuting legal OP) (ρ : List (I × R))
    (ops : Fin k → I × R) (hops : ∀ i, OP (ops i).1) (hleg : ∀ i, legal (ρ ++ [ops i]))
    (hrev : LastRevealing legal (by omega) ρ ops)
    {B : ℝ} (hB : TimeBound A d u ε OP B) : (1 - 1 / (k : ℝ)) * u ≤ B := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨α, hα⟩ := hrev
  have hk0 : 0 < k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  set c : ℝ := u / k with hc
  have hc0 : 0 ≤ c := div_nonneg hu hkpos.le
  have huc : u = k * c := by rw [hc]; field_simp
  have hεc : (1 - 1 / (k : ℝ)) * u = (k - 1) * c := by rw [huc]; field_simp
  have hBc : B < (k - 1) * c := by linarith
  have hcu : (k - 1) * c ≤ u := by rw [huc]; nlinarith
  have hkc0 : 0 ≤ (k - 1) * c := mul_nonneg (by linarith) hc0
  set g : ℝ := max Bop 0 + 1 with hgdef
  have hg : Bop < g := by have := le_max_left Bop 0; linarith
  have hg0 : 0 < g := by have := le_max_right Bop 0; linarith
  set p₀ := proc ⟨0, hk0⟩ with hp₀
  set Mc := ⌈u / g⌉₊ with hMc
  have hM : u ≤ Mc * g := by
    have := Nat.le_ceil (u / g); rwa [div_le_iff₀ hg0] at this
  set K := ρ.length + Mc with hK
  set N := K + k + 2 * Mc with hN
  set T : ℝ := K * g with hT
  have hKg : (K : ℝ) * g = ρ.length * g + Mc * g := by simp only [hK]; push_cast; ring
  have hNg : (N : ℝ) * g = K * g + k * g + 2 * (Mc * g) := by simp only [hN]; push_cast; ring
  have hkg : 0 < (k : ℝ) * g := mul_pos hkpos hg0
  set r0 : R := (ops ⟨0, hk0⟩).2
  set αC := alphaCalls p₀ g N α r0 with hαC
  have : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  set idx : P → Fin k := Function.invFun proc
  have hidx : ∀ i, idx (proc i) = i := Function.leftInverse_invFun hproc
  -- the run `R₁`
  set s1 : Scenario P I := ⟨fun _ => 0, rhoCalls p₀ g ρ ++
      ((List.finRange k).map (opCall proc ops K T (fun _ => 0)) ++ αC),
      fun q r _ => dly1 proc idx d u c q r⟩ with hs1
  have hγ : s1.MinDelay (d / k) :=
    ⟨div_pos hd hkpos, fun q r _ => (dly1_bounds hk proc idx hd hc0 huc hud q r).1⟩
  have hadm1 : s1.Admissible d u ε :=
    ⟨fun q r _ => (dly1_bounds hk proc idx hd hc0 huc hud q r).2, fun p q => by
      show |(0 : ℝ) - 0| ≤ ε
      simp only [sub_self, abs_zero]; linarith⟩
  have hchar : ∀ c' ∈ s1.calls, (c'.p = p₀ ∧ c'.t = c'.k * g) ∨
      ∃ i : Fin k, i ≠ ⟨0, hk0⟩ ∧ c' = opCall proc ops K T (fun _ => 0) i := by
    intro c' hc'
    simp only [hs1, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hc'
    rcases hc' with h | ⟨i, rfl⟩ | h
    · left; obtain ⟨h1, -, h3⟩ := mem_rhoCalls h; exact ⟨h1, h3⟩
    · by_cases hi : i = ⟨0, hk0⟩
      · left; subst hi; simp [opCall, hT, hp₀]
      · right; exact ⟨i, hi, rfl⟩
    · left; obtain ⟨h1, -, -, h3⟩ := mem_rhoCallsFrom h; exact ⟨h1, h3⟩
  have hids : (s1.calls.map Call.k).Nodup := by
    show ((rhoCalls p₀ g ρ ++ ((List.finRange k).map (opCall proc ops K T (fun _ => 0)) ++
      αC)).map Call.k).Nodup
    rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact List.pairwise_map.mpr ((pairwise_rhoCallsFrom 0 ρ).imp ne_of_lt)
    · rw [List.map_map]
      exact (List.nodup_finRange k).map (fun i j h => Fin.ext (by simpa [opCall] using h))
    · exact List.pairwise_map.mpr ((pairwise_rhoCallsFrom N _).imp ne_of_lt)
    · intro a ha b hb
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp ha
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc'
      obtain ⟨c'', hc'', rfl⟩ := List.mem_map.mp hb
      have := (mem_rhoCallsFrom hc'').2.1
      simp only [opCall]; omega
    · intro a ha b hb
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp ha
      have := (mem_rhoCalls hc').2.1
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨c'', hc'', rfl⟩ := List.mem_map.mp hb
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc''
        simp only [opCall]; omega
      · obtain ⟨c'', hc'', rfl⟩ := List.mem_map.mp hb
        have := (mem_rhoCallsFrom hc'').2.1; omega
  have hnd1 : s1.calls.Nodup := hids.of_map _
  have hid : ∀ c' ∈ s1.calls, ∀ c'' ∈ s1.calls, c'.p = c''.p → c'.k = c''.k → c' = c'' :=
    fun a ha b hb _ hk' => List.inj_on_of_nodup_map hids ha hb hk'
  have hsame : ∀ a ∈ s1.calls, ∀ b ∈ s1.calls, a.p = b.p → a ≠ b →
      a.t = a.k * g ∧ b.t = b.k * g := by
    intro a ha b hb hp hne
    rcases hchar a ha with ⟨h1, h2⟩ | ⟨i, hi, rfl⟩ <;>
      rcases hchar b hb with ⟨h3, h4⟩ | ⟨j, hj, rfl⟩
    · exact ⟨h2, h4⟩
    · exfalso; simp only [opCall] at hp; rw [h1, hp₀] at hp; exact hj (hproc hp).symm
    · exfalso; simp only [opCall] at hp; rw [h3, hp₀] at hp; exact hi (hproc hp)
    · exfalso; simp only [opCall] at hp; exact hne (by rw [hproc hp])
  have htm : ∀ a ∈ s1.calls, ∀ b ∈ s1.calls, a.p = b.p → a.t = b.t → a = b := by
    intro a ha b hb hp ht
    by_contra hne
    obtain ⟨h1, h2⟩ := hsame a ha b hb hp hne
    rw [h1, h2] at ht
    have : (a.k : ℝ) = b.k := mul_right_cancel₀ hg0.ne' ht
    exact hne (hid a ha b hb hp (by exact_mod_cast this))
  have hsp : ∀ a ∈ s1.calls, ∀ b ∈ s1.calls, a.p = b.p → a ≠ b → a.t < b.t → a.t + Bop < b.t := by
    intro a ha b hb hp hne ht
    obtain ⟨h1, h2⟩ := hsame a ha b hb hp hne
    rw [h1, h2] at ht ⊢
    have : (a.k : ℝ) < b.k := lt_of_mul_lt_mul_right ht hg0.le
    have : a.k + 1 ≤ b.k := by exact_mod_cast this
    have : ((a.k + 1 : ℕ) : ℝ) ≤ b.k := by exact_mod_cast this
    push_cast at this
    nlinarith
  obtain ⟨H, hH⟩ := exists_run A s1 hγ
  have hwf1 := wf_of_spaced A hcor hBop s1 hadm1 hγ hnd1 hid hsp htm H hH
  have hρN : ρ.length ≤ N := by omega
  obtain ⟨ret1, l1, hl1nd, hl1len, hleg1, hresp1, -, -⟩ :=
    lin_aux A hpc hdet hcor hBop hg hg0 hsc hB hk0 proc ρ ops hops hleg p₀ α r0 K N T
      (fun _ => 0) (fun _ => by simp only [hT, add_zero]; linarith)
      (fun _ => by simp only [hT, add_zero]; linarith) hρN s1 rfl hadm1 hH hwf1
  obtain ⟨σ1, hσ1⟩ := exists_perm_ofFn l1 hl1nd hl1len
  -- the last operation of the linearization of `R₁`, and the shifted run `R₂`
  set z := σ1 ⟨k - 1, by omega⟩ with hz
  set x' : P → ℝ := fun p => shiftX proc idx c z p - shiftX proc idx c z p₀ with hx'
  have hx0 : x' p₀ = 0 := sub_self _
  have hxb : ∀ p, -((k - 1) * c) ≤ x' p ∧ x' p ≤ (k - 1) * c := by
    intro p
    have h1 := abs_le.mp (abs_shiftX hk0 proc idx hc0 z p)
    have h2 := abs_le.mp (abs_shiftX hk0 proc idx hc0 z p₀)
    simp only [hx']; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  set s2 := s1.shift x' with hs2
  have hfix : ∀ l : List (Call P I), (∀ c' ∈ l, c'.p = p₀) →
      l.map (fun c' => {c' with t := c'.t + x' c'.p}) = l := by
    intro l hl
    conv_rhs => rw [← List.map_id l]
    apply List.map_congr_left
    intro c' hc'
    have h := hl c' hc'
    obtain ⟨cp, ck, ct, ca⟩ := c'
    simp only at h ⊢
    subst h
    rw [hx0, add_zero, id]
  have hcalls2 : s2.calls = rhoCalls p₀ g ρ ++
      ((List.finRange k).map (opCall proc ops K T (fun i => x' (proc i))) ++ αC) := by
    show (rhoCalls p₀ g ρ ++ ((List.finRange k).map (opCall proc ops K T (fun _ => 0)) ++
      αC)).map (fun c' => {c' with t := c'.t + x' c'.p}) = _
    rw [List.map_append, List.map_append, hfix _ (fun c' h => (mem_rhoCalls h).1),
      hfix αC (fun c' h => (mem_rhoCallsFrom h).1), List.map_map]
    congr 2
    apply List.map_congr_left
    intro i _
    simp [opCall]
  have hadm2 : s2.Admissible d u ε := by
    refine ⟨fun q r σ => ?_, fun p q => ?_⟩
    · show d - u ≤ dly1 proc idx d u c q r + x' r - x' q ∧
        dly1 proc idx d u c q r + x' r - x' q ≤ d
      have := dly_shift_bounds hk hidx (d := d) hc0 huc z q r
      simp only [hx']; constructor <;> linarith [this.1, this.2]
    · show |((0 : ℝ) - x' p) - (0 - x' q)| ≤ ε
      have h1 := abs_le.mp (abs_shiftX hk0 proc idx hc0 z p)
      have h2 := abs_le.mp (abs_shiftX hk0 proc idx hc0 z q)
      rw [abs_le]; simp only [hx']; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hH2 : IsRun A s2 H := IsRun.shift A hH x'
  have hwf2 : WF A s2 H := wf_shift hwf1 x'
  obtain ⟨ret2, l2, hl2nd, hl2len, hleg2, -, huniq2, hord2⟩ :=
    lin_aux A hpc hdet hcor hBop hg hg0 hsc hB hk0 proc ρ ops hops hleg p₀ α r0 K N T
      (fun i => x' (proc i)) (fun i => by have := hxb (proc i); simp only [hT]; linarith)
      (fun i => by have := hxb (proc i); simp only [hT]; linarith) hρN s2 hcalls2 hadm2 hH2 hwf2
  obtain ⟨σ2, hσ2⟩ := exists_perm_ofFn l2 hl2nd hl2len
  have hrs : αC.map ret2 = αC.map ret1 := by
    apply List.map_congr_left
    intro c' hc'
    obtain ⟨σ, hσ⟩ := hresp1 c' hc'
    have hp : c'.p = p₀ := (mem_rhoCallsFrom hc').1
    refine (huniq2 c' hc' σ _ ?_).symm
    unfold RespAt at hσ ⊢
    have : s2.off c'.p = s1.off c'.p := by
      show s1.off c'.p - x' c'.p = s1.off c'.p
      rw [hp, hx0, sub_zero]
    rw [this]; exact hσ
  have hlast := hα σ1 σ2 (αC.map ret1)
    (by simp [hαC, alphaCalls, length_rhoCallsFrom])
    (by rw [permSeq_eq, hσ1]; exact hleg1) (by rw [permSeq_eq, hσ2, ← hrs]; exact hleg2)
  -- `op_z` responds before `op_{z+1 mod k}` is invoked in `R₂`
  set w : Fin k := if h : z.val + 1 < k then ⟨z.val + 1, h⟩ else ⟨0, hk0⟩ with hw
  have hmw : md k z w + 1 = k := by
    simp only [hw]; split_ifs with h <;> simp only [md] <;> split_ifs <;> omega
  have hmz : md k z z = 0 := by simp [md]
  have hzw := hord2 z w (by
    simp only [hx', shiftX_proc hidx, hmz]
    have : (md k z w : ℝ) = k - 1 := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hmw; push_cast at this; linarith
    rw [this]; push_cast; linarith)
  rw [← hσ2] at hzw
  exact last_ne_of_sublist hk0 σ2 hzw hlast.symm

/-- For `k = 2` the thesis's hypothesis (the two permutations of `op_0, op_1` are not equivalent
after `ρ`) implies `LastRevealing`: by determinism, the arguments of a distinguishing
continuation reveal the order. -/
theorem lastRevealing_two {legal : List (I × R) → Prop} (hpc : PrefixClosed legal)
    (hdet : Deterministic legal) (ρ : List (I × R)) (ops : Fin 2 → I × R)
    (hne : ¬ Equivalent legal (ρ ++ permSeq ops 1) (ρ ++ permSeq ops (Equiv.swap 0 1))) :
    LastRevealing legal (by norm_num) ρ ops := by
  have hab : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  -- a continuation legal after `a` and illegal after `b`
  have hgen : ∀ a b : Equiv.Perm (Fin 2), a ≠ b → ∀ ρ₃ : List (I × R),
      legal (ρ ++ permSeq ops a ++ ρ₃) → ¬ legal (ρ ++ permSeq ops b ++ ρ₃) →
      LastRevealing legal (by norm_num) ρ ops := by
    intro a b hab' ρ₃ h1 h2
    have hor : ∀ τ : Equiv.Perm (Fin 2), τ = a ∨ τ = b := by
      have : ∀ τ a b : Equiv.Perm (Fin 2), a ≠ b → τ = a ∨ τ = b := by decide
      exact fun τ => this τ a b hab'
    refine ⟨ρ₃.map Prod.fst, fun σ σ' rs hlen hσ hσ' => ?_⟩
    have hz : legal (ρ ++ permSeq ops a ++ (ρ₃.map Prod.fst).zip rs) →
        (ρ₃.map Prod.fst).zip rs = ρ₃ := fun h =>
      det_seq hpc hdet _ _ (ρ ++ permSeq ops a) h h1
        (by rw [List.map_fst_zip (by rw [hlen])])
    by_cases he : σ = σ'
    · rw [he]
    exfalso
    rcases hor σ with rfl | rfl <;> rcases hor σ' with rfl | rfl
    · exact he rfl
    · exact h2 (hz hσ ▸ hσ')
    · exact h2 (hz hσ' ▸ hσ)
    · exact he rfl
  unfold Equivalent LooksLike at hne
  rw [not_and_or] at hne
  rcases hne with h | h <;> push Not at h <;> obtain ⟨ρ₃, h1, h2⟩ := h
  · exact hgen 1 (Equiv.swap 0 1) hab ρ₃ h1 h2
  · exact hgen _ 1 hab.symm ρ₃ h1 h2

/-- **Theorem D.1 for `k = 2`** with the thesis's own hypothesis (the two orders of `op_0`, `op_1`
are not equivalent after `ρ`): `|OP| ≥ u / 2`, provided `ε ≥ u / 2`. -/
theorem theorem_D1_two [Fintype P] [DecidableEq P] (A : Algorithm P I R M)
    {legal : List (I × R) → Prop} (hpc : PrefixClosed legal) (hdet : Deterministic legal)
    {d u ε : ℝ} (hd : 0 < d) (hu : 0 ≤ u) (hud : u ≤ d) (hε : u / 2 ≤ ε)
    (hcor : Correct A legal d u ε) {Bop : ℝ} (hBop : TimeBound A d u ε (fun _ => True) Bop)
    (proc : Fin 2 → P) (hproc : Function.Injective proc)
    {OP : I → Prop} (hsc : ImmSelfCommuting legal OP) (ρ : List (I × R))
    (ops : Fin 2 → I × R) (hops : ∀ i, OP (ops i).1) (hleg : ∀ i, legal (ρ ++ [ops i]))
    (hne : ¬ Equivalent legal (ρ ++ permSeq ops 1) (ρ ++ permSeq ops (Equiv.swap 0 1)))
    {B : ℝ} (hB : TimeBound A d u ε OP B) : u / 2 ≤ B := by
  have := theorem_D1 A hpc hdet hd hu hud le_rfl (by norm_num; linarith) hcor hBop proc hproc
    hsc ρ ops hops hleg (lastRevealing_two hpc hdet ρ ops hne) hB
  norm_num at this
  linarith

end Podc.SharedObjectTimeBounds
