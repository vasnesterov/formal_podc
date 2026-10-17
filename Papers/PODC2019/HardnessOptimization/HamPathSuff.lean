import Papers.PODC2019.HardnessOptimization.HamPathGraph

/-!
# Claim 2.1: `DISJ(x, y) = FALSE` gives a Hamiltonian path in `D_{x,y}`

Given `x(i₀, j₀) = y(i₀, j₀) = 1`, box `c` (bit `h` of layer `ℓ`) chooses the line
`q_c = ¬ ι_ℓ(h)` (`ι_false = i₀`, `ι_true = j₀`), i.e. the line containing the rows whose bit `h`
differs from the one of `i₀` / `j₀`. The path is

`start, [g_c, forward pass of line q_c]_{c = 0..2L-1}, [r_c, backward pass of line ¬q_c]_{c = 2L-1..0},
 s¹₁, a^{i₀}_1, a^{j₀}_2, s²₁, s¹₂, b^{i₀}_1, b^{j₀}_2, s²₂, end`.

In the forward pass, position `d` makes a wheel detour iff `c` is the *first* box (in its layer)
on whose chosen line the wheel row lies (`Detour`), so every row other than the four suffix rows
is visited exactly once. This needs the wheel to be injective on each line, and every row of
layer `layer c` with bit `bit c` equal to `q` to occur on line `q` of box `c`.
-/

namespace HardnessOptimization.HamPath

open HV

/-! ### Segments of paths -/

section Seg

variable {α ι : Type*} {R : α → α → Prop}

/-- `l` is a path (w.r.t. `R`) from `a` to `b`. -/
def Seg (R : α → α → Prop) (l : List α) (a b : α) : Prop :=
  l.IsChain R ∧ l.head? = some a ∧ l.getLast? = some b

lemma seg_singleton (a : α) : Seg R [a] a a := ⟨by simp, rfl, rfl⟩

lemma Seg.append {l₁ l₂ : List α} {a b c d : α} (h1 : Seg R l₁ a b) (h2 : Seg R l₂ c d)
    (h : R b c) : Seg R (l₁ ++ l₂) a d := by
  obtain ⟨c1, h1a, h1b⟩ := h1
  obtain ⟨c2, h2a, h2b⟩ := h2
  refine ⟨List.isChain_append.2 ⟨c1, c2, ?_⟩, ?_, ?_⟩
  · intro u hu v hv
    rw [h1b] at hu; rw [h2a] at hv
    simp only [Option.mem_def, Option.some.injEq] at hu hv
    subst hu hv; exact h
  · simp [List.head?_append, h1a]
  · simp [List.getLast?_append, h2b]

lemma Seg.cons {l : List α} {a b c : α} (h : Seg R l b c) (hab : R a b) : Seg R (a :: l) a c := by
  simpa using (seg_singleton a).append h hab

lemma seg_flatMap (f : ι → List α) (st en : ι → α) :
    ∀ (l : List ι) (hne : l ≠ []), (∀ i ∈ l, Seg R (f i) (st i) (en i)) →
      l.IsChain (fun i j => R (en i) (st j)) →
      Seg R (l.flatMap f) (st (l.head hne)) (en (l.getLast hne))
  | [], hne, _, _ => absurd rfl hne
  | [i], _, hs, _ => by simpa using hs i (by simp)
  | i :: j :: t, _, hs, hc => by
    have ih := seg_flatMap f st en (j :: t) (by simp)
      (fun k hk => hs k (List.mem_cons_of_mem _ hk)) (List.isChain_cons_cons.1 hc).2
    rw [List.flatMap_cons]
    have := (hs i (by simp)).append ih (List.isChain_cons_cons.1 hc).1
    simpa using this

lemma isChain_finRange (n : ℕ) :
    (List.finRange n).IsChain (fun i j : Fin n => j.val = i.val + 1) := by
  rw [List.isChain_iff_getElem]; intro i hi; simp

lemma finRange_ne_nil {n : ℕ} (hn : 0 < n) : List.finRange n ≠ [] := by
  intro h; have := congrArg List.length h; simp at this; omega

lemma head_finRange {n : ℕ} (hn : 0 < n) (h : List.finRange n ≠ []) :
    (List.finRange n).head h = ⟨0, hn⟩ := by
  rw [List.head_eq_getElem]; simp

lemma getLast_finRange {n : ℕ} (hn : 0 < n) (h : List.finRange n ≠ []) :
    (List.finRange n).getLast h = ⟨n - 1, by omega⟩ := by
  rw [List.getLast_eq_getElem]; simp

lemma seg_flatMap_finRange {n : ℕ} (hn : 0 < n) (f : Fin n → List α) (st en : Fin n → α)
    (hs : ∀ i, Seg R (f i) (st i) (en i))
    (hl : ∀ i j : Fin n, j.val = i.val + 1 → R (en i) (st j)) :
    Seg R ((List.finRange n).flatMap f) (st ⟨0, hn⟩) (en ⟨n - 1, by omega⟩) := by
  have := seg_flatMap f st en _ (finRange_ne_nil hn) (fun i _ => hs i)
    ((isChain_finRange n).imp fun i j h => hl i j h)
  simpa only [head_finRange hn, getLast_finRange hn] using this

lemma seg_flatMap_finRange_rev {n : ℕ} (hn : 0 < n) (f : Fin n → List α) (st en : Fin n → α)
    (hs : ∀ i, Seg R (f i) (st i) (en i))
    (hl : ∀ i j : Fin n, j.val = i.val + 1 → R (en j) (st i)) :
    Seg R ((List.finRange n).reverse.flatMap f) (st ⟨n - 1, by omega⟩) (en ⟨0, hn⟩) := by
  have hne : (List.finRange n).reverse ≠ [] := by simpa using finRange_ne_nil hn
  have := seg_flatMap f st en _ hne (fun i _ => hs i)
    (List.isChain_reverse.2 ((isChain_finRange n).imp fun i j h => hl i j h))
  simpa only [List.head_reverse, List.getLast_reverse, head_finRange hn, getLast_finRange hn] using this

end Seg

/-! ### The path -/

section Construction

variable {L : ℕ} (W : Wheel L) (i₀ j₀ : Idx L)

/-- The intersecting index of layer `ℓ`: `i₀` for layer 1, `j₀` for layer 2. -/
def iota (ℓ : Bool) : Idx L := if ℓ then j₀ else i₀

/-- The line chosen in box `c` (traversed forward): the one *not* containing `ι(c)`. -/
def qc (c : Fin (2 * L)) : Bool := !(iota i₀ j₀ (layer c) (bit c))

/-- In the forward pass of box `c`, position `d` makes a wheel detour iff `c` is the first box of
its layer whose chosen line contains the wheel row. -/
def Detour (c : Fin (2 * L)) (d : Fin (2 ^ L)) : Prop :=
  ∀ h : Fin L, h < bit c → (W c (qc i₀ j₀ c) d).2 h = iota i₀ j₀ (layer c) h

instance (c : Fin (2 * L)) (d : Fin (2 ^ L)) : Decidable (Detour W i₀ j₀ c d) := by
  unfold Detour; infer_instance

/-- Forward pass through position `d` of box `c`. -/
def fwdBlock (c : Fin (2 * L)) (d : Fin (2 ^ L)) : List (HV L) :=
  if Detour W i₀ j₀ c d then
    [.la c (qc i₀ j₀ c) d, wrow W c (qc i₀ j₀ c) d, .be c (qc i₀ j₀ c) d, .si c (qc i₀ j₀ c) d]
  else [.la c (qc i₀ j₀ c) d, .si c (qc i₀ j₀ c) d, .be c (qc i₀ j₀ c) d]

/-- Last vertex of `fwdBlock`. -/
def fwdEnd (c : Fin (2 * L)) (d : Fin (2 ^ L)) : HV L :=
  if Detour W i₀ j₀ c d then .si c (qc i₀ j₀ c) d else .be c (qc i₀ j₀ c) d

/-- `g_c` followed by the forward pass of the chosen line of box `c`. -/
def fwdBox (c : Fin (2 * L)) : List (HV L) :=
  .g c :: (List.finRange (2 ^ L)).flatMap (fwdBlock W i₀ j₀ c)

/-- Backward pass through position `d` of the other line of box `c`. -/
def bwdBlock (c : Fin (2 * L)) (d : Fin (2 ^ L)) : List (HV L) :=
  [.la c (!qc i₀ j₀ c) d, .si c (!qc i₀ j₀ c) d, .be c (!qc i₀ j₀ c) d]

/-- `r_c` followed by the backward pass of the other line of box `c`. -/
def bwdBox (c : Fin (2 * L)) : List (HV L) :=
  .r c :: (List.finRange (2 ^ L)).reverse.flatMap (bwdBlock i₀ j₀ c)

/-- The suffix `s¹₁, a^{i₀}_1, a^{j₀}_2, s²₁, s¹₂, b^{i₀}_1, b^{j₀}_2, s²₂, end`. -/
def sufList : List (HV L) :=
  [.sA1, .row false false i₀, .row false true j₀, .sA2, .sB1, .row true false i₀,
    .row true true j₀, .sB2, .stop]

/-- The Hamiltonian path of Claim 2.1. -/
def hamList : List (HV L) :=
  .start :: ((List.finRange (2 * L)).flatMap (fwdBox W i₀ j₀) ++
    ((List.finRange (2 * L)).reverse.flatMap (bwdBox i₀ j₀) ++ sufList i₀ j₀))

variable {W i₀ j₀} {x y : Idx L → Idx L → Bool}

/-! #### The arcs -/

lemma arc_wrow_be (c q d) : Arc W x y (wrow W c q d) (.be c q d) :=
  Or.inl (Or.inr ⟨c, q, d, rfl, rfl⟩)

lemma arc_fwdEnd (c d) {v : HV L} (hv : IsFwd c (qc i₀ j₀ c) d v) :
    Arc W x y (fwdEnd W i₀ j₀ c d) v := by
  unfold fwdEnd; split
  · exact arc_from_si.2 (Or.inr hv)
  · exact arc_from_be.2 (Or.inr (Or.inl hv))

lemma seg_fwdBlock (c d) :
    Seg (Arc W x y) (fwdBlock W i₀ j₀ c d) (.la c (qc i₀ j₀ c) d) (fwdEnd W i₀ j₀ c d) := by
  unfold fwdBlock fwdEnd
  split
  · refine ⟨?_, rfl, rfl⟩
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨arc_from_la.2 (Or.inr rfl), arc_wrow_be c _ d, arc_from_be.2 (Or.inl rfl)⟩
  · refine ⟨?_, rfl, rfl⟩
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨arc_from_la.2 (Or.inl rfl), arc_from_si.2 (Or.inl rfl)⟩

lemma seg_fwdBox (c) :
    Seg (Arc W x y) (fwdBox W i₀ j₀ c) (.g c)
      (fwdEnd W i₀ j₀ c ⟨2 ^ L - 1, by have := Nat.two_pow_pos L; omega⟩) := by
  have hK := Nat.two_pow_pos L
  exact (seg_flatMap_finRange hK (fwdBlock W i₀ j₀ c) (fun d => .la c (qc i₀ j₀ c) d)
    (fwdEnd W i₀ j₀ c) (fun d => seg_fwdBlock c d) (fun d d' h => arc_fwdEnd c d ⟨rfl, rfl, h⟩)).cons
    (arc_from_g.2 ⟨_, _, rfl, rfl⟩)

lemma seg_bwdBlock (c d) :
    Seg (Arc W x y) (bwdBlock i₀ j₀ c d) (.la c (!qc i₀ j₀ c) d) (.be c (!qc i₀ j₀ c) d) := by
  refine ⟨?_, rfl, rfl⟩
  simp only [bwdBlock, List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact ⟨arc_from_la.2 (Or.inl rfl), arc_from_si.2 (Or.inl rfl)⟩

lemma seg_bwdBox (c) :
    Seg (Arc W x y) (bwdBox i₀ j₀ c) (.r c) (.be c (!qc i₀ j₀ c) ⟨0, Nat.two_pow_pos L⟩) := by
  have hK := Nat.two_pow_pos L
  exact (seg_flatMap_finRange_rev hK (bwdBlock i₀ j₀ c) (fun d => .la c (!qc i₀ j₀ c) d)
    (fun d => .be c (!qc i₀ j₀ c) d) (fun d => seg_bwdBlock c d)
    (fun d d' h => arc_from_be.2 (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))).cons
    (arc_from_r.2 ⟨_, _, by simp; omega, rfl⟩)

lemma seg_suf (hx : x i₀ j₀ = true) (hy : y i₀ j₀ = true) :
    Seg (Arc W x y) (sufList i₀ j₀) .sA1 .stop := by
  refine ⟨?_, rfl, rfl⟩
  simp only [sufList, List.isChain_cons_cons, List.isChain_singleton, and_true]
  refine ⟨arc_from_sA1.2 ⟨_, rfl⟩, Or.inr (Or.inl ⟨_, _, rfl, rfl, hx⟩),
    Or.inl (Or.inl ⟨rfl, rfl⟩), arc_from_sA2.2 rfl, arc_from_sB1.2 ⟨_, rfl⟩,
    Or.inr (Or.inr ⟨_, _, rfl, rfl, hy⟩), Or.inl (Or.inl ⟨rfl, rfl⟩), arc_from_sB2.2 rfl⟩

lemma isChain_hamList (hL : 0 < L) (hx : x i₀ j₀ = true) (hy : y i₀ j₀ = true) :
    (hamList W i₀ j₀).IsChain (Arc W x y) := by
  have hK := Nat.two_pow_pos L
  have hm : 0 < 2 * L := by omega
  have hF := seg_flatMap_finRange hm (fwdBox W i₀ j₀) (fun c => .g c)
    (fun c => fwdEnd W i₀ j₀ c ⟨2 ^ L - 1, by omega⟩) (seg_fwdBox (x := x) (y := y))
    (fun c c' h => arc_fwdEnd c _ ⟨by simp; omega, h⟩)
  have hB := seg_flatMap_finRange_rev hm (bwdBox i₀ j₀) (fun c => .r c)
    (fun c => .be c (!qc i₀ j₀ c) ⟨0, hK⟩) (seg_bwdBox (W := W) (x := x) (y := y))
    (fun c c' h => arc_from_be.2 (Or.inr (Or.inr ⟨rfl, h⟩)))
  have hS := seg_suf (W := W) hx hy
  have := (hF.append (hB.append hS (arc_from_be.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    (arc_fwdEnd _ _ ⟨by simp; omega, by simp; omega, rfl⟩)).cons
    (arc_from_start.2 ⟨_, rfl, rfl⟩)
  exact this.1

/-! #### No repetitions, all vertices -/

lemma mem_fwdBlock {c d} {v : HV L} : v ∈ fwdBlock W i₀ j₀ c d ↔
    v = .la c (qc i₀ j₀ c) d ∨ v = .si c (qc i₀ j₀ c) d ∨ v = .be c (qc i₀ j₀ c) d ∨
      (Detour W i₀ j₀ c d ∧ v = wrow W c (qc i₀ j₀ c) d) := by
  unfold fwdBlock; split
  · simp_all; tauto
  · simp_all

lemma mem_F {v : HV L} : v ∈ (List.finRange (2 * L)).flatMap (fwdBox W i₀ j₀) ↔
    ∃ c, v = .g c ∨ ∃ d, v ∈ fwdBlock W i₀ j₀ c d := by
  simp [fwdBox]

lemma mem_B {v : HV L} : v ∈ (List.finRange (2 * L)).reverse.flatMap (bwdBox i₀ j₀) ↔
    ∃ c, v = .r c ∨ ∃ d, v = .la c (!qc i₀ j₀ c) d ∨ v = .si c (!qc i₀ j₀ c) d ∨
      v = .be c (!qc i₀ j₀ c) d := by
  simp [bwdBox, bwdBlock]

variable (hW1 : ∀ c q, Function.Injective (W c q)) (hW2 : ∀ c q d, (W c q d).2 (bit c) = q)
  (hW3 : ∀ c q s (i : Idx L), i (bit c) = q → ∃ d, W c q d = (s, i))

include hW2 in
lemma wheel_ne_iota (c d) : (W c (qc i₀ j₀ c) d).2 ≠ iota i₀ j₀ (layer c) := by
  intro h
  have := hW2 c (qc i₀ j₀ c) d
  rw [h] at this
  simp [qc] at this

include hW2 in
lemma detour_box_eq {c c' d d'} (h : Detour W i₀ j₀ c d) (h' : Detour W i₀ j₀ c' d')
    (he : wrow W c (qc i₀ j₀ c) d = wrow W c' (qc i₀ j₀ c') d') : c = c' := by
  simp only [wrow, HV.row.injEq] at he
  obtain ⟨-, hl, hi⟩ := he
  apply box_ext hl
  have a := hW2 c (qc i₀ j₀ c) d
  have b := hW2 c' (qc i₀ j₀ c') d'
  rcases lt_trichotomy (bit c) (bit c') with hlt | heq | hgt
  · have := h' (bit c) hlt
    rw [← hi, a, ← hl] at this; simp [qc] at this
  · exact heq
  · have := h (bit c') hgt
    rw [hi, b, hl] at this; simp [qc] at this

include hW1 hW2 in
lemma nodup_F : ((List.finRange (2 * L)).flatMap (fwdBox W i₀ j₀)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun c _ => ?_, ?_⟩
  · rw [fwdBox, List.nodup_cons, List.nodup_flatMap]
    refine ⟨?_, fun d _ => ?_, ?_⟩
    · intro hg
      simp only [List.mem_flatMap] at hg
      obtain ⟨d, -, hd⟩ := hg
      rw [mem_fwdBlock] at hd
      simp [wrow] at hd
    · unfold fwdBlock; split <;> simp [wrow]
    · refine (List.nodup_finRange _).pairwise_of_forall_ne fun d _ d' _ hne => ?_
      intro v hv hv'
      rw [mem_fwdBlock] at hv hv'
      apply hne
      rcases hv with rfl | rfl | rfl | ⟨-, rfl⟩ <;> rcases hv' with h | h | h | ⟨-, h⟩
      all_goals first
        | (simp [wrow] at h; done)
        | (simp only [HV.la.injEq, HV.si.injEq, HV.be.injEq] at h; exact h.2.2)
        | (simp only [wrow, HV.row.injEq] at h; exact hW1 c _ (Prod.ext h.1 h.2.2))
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun c _ c' _ hne => ?_
    intro v hv hv'
    simp only [fwdBox, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at hv hv'
    apply hne
    rcases hv with rfl | ⟨d, hd⟩ <;> rcases hv' with h | ⟨d', hd'⟩
    · simpa using h
    · rw [mem_fwdBlock] at hd'; simp [wrow] at hd'
    · subst h; rw [mem_fwdBlock] at hd; simp [wrow] at hd
    · rw [mem_fwdBlock] at hd hd'
      rcases hd with rfl | rfl | rfl | ⟨hdet, rfl⟩ <;> rcases hd' with h | h | h | ⟨hdet', h⟩
      all_goals first
        | exact detour_box_eq hW2 hdet hdet' h
        | (simp [wrow] at h; done)
        | (simp only [HV.la.injEq, HV.si.injEq, HV.be.injEq] at h; exact h.1)

lemma nodup_B : ((List.finRange (2 * L)).reverse.flatMap (bwdBox i₀ j₀)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun c _ => ?_, ?_⟩
  · rw [bwdBox, List.nodup_cons, List.nodup_flatMap]
    refine ⟨?_, fun d _ => ?_, ?_⟩
    · simp [bwdBlock]
    · simp [bwdBlock]
    · refine (List.nodup_reverse.2 (List.nodup_finRange _)).pairwise_of_forall_ne
        fun d _ d' _ hne => ?_
      intro v hv hv'
      simp only [bwdBlock, List.mem_cons, List.not_mem_nil, or_false] at hv hv'
      apply hne
      rcases hv with rfl | rfl | rfl <;> rcases hv' with h | h | h <;> simp_all
  · refine (List.nodup_reverse.2 (List.nodup_finRange _)).pairwise_of_forall_ne
      fun c _ c' _ hne => ?_
    intro v hv hv'
    simp only [bwdBox, bwdBlock, List.mem_cons, List.mem_flatMap, List.mem_reverse,
      List.mem_finRange, true_and, List.not_mem_nil, or_false] at hv hv'
    apply hne
    rcases hv with rfl | ⟨d, rfl | rfl | rfl⟩ <;> rcases hv' with h | ⟨d', h | h | h⟩ <;> simp_all

include hW1 hW2 in
lemma nodup_hamList : (hamList W i₀ j₀).Nodup := by
  have hFB : ∀ v, v ∈ (List.finRange (2 * L)).flatMap (fwdBox W i₀ j₀) →
      v ∉ (List.finRange (2 * L)).reverse.flatMap (bwdBox i₀ j₀) ++ sufList i₀ j₀ := by
    intro v hv hv'
    rw [mem_F] at hv
    rw [List.mem_append, mem_B] at hv'
    obtain ⟨c, rfl | ⟨d, hd⟩⟩ := hv
    · rcases hv' with ⟨c', h | ⟨d', h | h | h⟩⟩ | h <;> simp [sufList] at h
    · rw [mem_fwdBlock] at hd
      rcases hd with rfl | rfl | rfl | ⟨-, rfl⟩
      all_goals rcases hv' with ⟨c', h | ⟨d', h | h | h⟩⟩ | h
      all_goals first
        | (simp [sufList, wrow] at h; done)
        | (simp only [HV.la.injEq, HV.si.injEq, HV.be.injEq] at h
           obtain ⟨rfl, h, -⟩ := h
           simp at h)
        | (have := wheel_ne_iota hW2 (i₀ := i₀) (j₀ := j₀) c d
           simp only [sufList, wrow, List.mem_cons, HV.row.injEq, reduceCtorEq,
             List.not_mem_nil, or_false, false_or] at h
           rcases h with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;>
             simp [iota, h1, h2] at this)
  have hBS : ∀ v, v ∈ (List.finRange (2 * L)).reverse.flatMap (bwdBox i₀ j₀) →
      v ∉ sufList i₀ j₀ := by
    intro v hv hv'
    rw [mem_B] at hv
    obtain ⟨c, rfl | ⟨d, rfl | rfl | rfl⟩⟩ := hv <;> simp [sufList] at hv'
  rw [hamList, List.nodup_cons, List.nodup_append, List.nodup_append]
  refine ⟨?_, nodup_F hW1 hW2, ⟨nodup_B, by simp [sufList], fun a ha b hb hab => ?_⟩,
    fun a ha b hb hab => ?_⟩
  · simp only [List.mem_append, mem_F, mem_B, mem_fwdBlock, not_or, not_exists]
    refine ⟨fun c => ⟨by simp, fun d => by simp [wrow]⟩, fun c => ⟨by simp, fun d => by simp⟩,
      by simp [sufList]⟩
  · subst hab; exact hBS a ha hb
  · subst hab; exact hFB a ha hb

include hW3 in
lemma mem_hamList (v : HV L) : v ∈ hamList W i₀ j₀ := by
  have hK := Nat.two_pow_pos L
  simp only [hamList, List.mem_cons, List.mem_append, mem_F, mem_B]
  cases v
  case start => simp
  case stop => simp [sufList]
  case sA1 => simp [sufList]
  case sA2 => simp [sufList]
  case sB1 => simp [sufList]
  case sB2 => simp [sufList]
  case g c => exact Or.inr (Or.inl ⟨c, Or.inl rfl⟩)
  case r c => exact Or.inr (Or.inr (Or.inl ⟨c, Or.inl rfl⟩))
  case la c q d =>
    by_cases hq : q = qc i₀ j₀ c
    · subst hq; exact Or.inr (Or.inl ⟨c, Or.inr ⟨d, mem_fwdBlock.2 (Or.inl rfl)⟩⟩)
    · have : q = !qc i₀ j₀ c := by cases q <;> simp_all
      subst this; exact Or.inr (Or.inr (Or.inl ⟨c, Or.inr ⟨d, Or.inl rfl⟩⟩))
  case si c q d =>
    by_cases hq : q = qc i₀ j₀ c
    · subst hq; exact Or.inr (Or.inl ⟨c, Or.inr ⟨d, mem_fwdBlock.2 (Or.inr (Or.inl rfl))⟩⟩)
    · have : q = !qc i₀ j₀ c := by cases q <;> simp_all
      subst this; exact Or.inr (Or.inr (Or.inl ⟨c, Or.inr ⟨d, Or.inr (Or.inl rfl)⟩⟩))
  case be c q d =>
    by_cases hq : q = qc i₀ j₀ c
    · subst hq
      exact Or.inr (Or.inl ⟨c, Or.inr ⟨d, mem_fwdBlock.2 (Or.inr (Or.inr (Or.inl rfl)))⟩⟩)
    · have : q = !qc i₀ j₀ c := by cases q <;> simp_all
      subst this; exact Or.inr (Or.inr (Or.inl ⟨c, Or.inr ⟨d, Or.inr (Or.inr rfl)⟩⟩))
  case row s ℓ i =>
    by_cases hi : i = iota i₀ j₀ ℓ
    · subst hi
      refine Or.inr (Or.inr (Or.inr ?_))
      cases s <;> cases ℓ <;> simp [sufList, iota]
    · refine Or.inr (Or.inl ?_)
      classical
      have hS : (Finset.univ.filter (fun h : Fin L => i h ≠ iota i₀ j₀ ℓ h)).Nonempty := by
        by_contra hS
        rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hS
        exact hi (funext fun h => by simpa using hS (Finset.mem_univ h))
      set S := Finset.univ.filter (fun h : Fin L => i h ≠ iota i₀ j₀ ℓ h) with hSdef
      let h := S.min' hS
      have hh : i h ≠ iota i₀ j₀ ℓ h := by
        have := Finset.min'_mem _ hS
        simpa [hSdef] using this
      have hmin : ∀ h', h' < h → i h' = iota i₀ j₀ ℓ h' := by
        intro h' hlt
        by_contra hne
        have := S.min'_le h' (by simpa [hSdef] using hne)
        exact absurd hlt (not_lt.2 this)
      let c := boxOf ℓ h
      have hq : i (bit c) = qc i₀ j₀ c := by
        simp only [c, qc, layer_boxOf, bit_boxOf]
        cases h1 : i h <;> cases h2 : iota i₀ j₀ ℓ h <;> simp_all
      obtain ⟨d, hd⟩ := hW3 c (qc i₀ j₀ c) s i hq
      refine ⟨c, Or.inr ⟨d, mem_fwdBlock.2 (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))⟩⟩
      · intro h' hlt
        rw [hd]
        simp only [c, layer_boxOf, bit_boxOf] at hlt ⊢
        exact hmin h' hlt
      · simp [wrow, hd, c]

/-- **Claim 2.1**: if `DISJ(x, y) = FALSE` (some `x(i, j) = y(i, j) = 1`), then `D_{x,y}` has a
directed Hamiltonian path (for any wheel assignment that is injective on each line and puts on
line `q` of box `c` exactly the rows of layer `layer c` whose bit `bit c` is `q`). -/
theorem claim_2_1 (hL : 0 < L) (hW1 : ∀ c q, Function.Injective (W c q))
    (hW2 : ∀ c q d, (W c q d).2 (bit c) = q)
    (hW3 : ∀ c q s (i : Idx L), i (bit c) = q → ∃ d, W c q d = (s, i))
    (h : ∃ i j, x i j = true ∧ y i j = true) : HasHamPath (Arc W x y) := by
  obtain ⟨i₀, j₀, hx, hy⟩ := h
  exact ⟨hamList W i₀ j₀, nodup_hamList hW1 hW2, mem_hamList hW3,
    isChain_hamList hL hx hy⟩

end Construction

end HardnessOptimization.HamPath
