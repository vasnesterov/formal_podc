import Papers.PODC2011.LocallyCheckableProofs.Cycle

/-!
# The gluing argument of Section 5.3

For index sets `α`, `β` (the paper's `A`, `B`), identifier lists `la a` (length `nA`) and `lb b`
(length `nB`), the yes-instance `C(a,b)` is the cycle `la a ++ reverse (lb b)`: the nodes of `a` in
increasing order followed by the nodes of `b` in decreasing order, so that `a[1]` and `b[1]` are
adjacent (`lst`). A labelling (node labels, marked edges) and a proof accepted by all nodes are
given for every `C(a,b)`.

* `exists_mono_rect`: a monochromatic 4-cycle in an edge colouring of `K_{α,β}` with `t` colours if
  `t (t+1)² < |α|` and `t < |β|` (an elementary replacement for the Bondy–Simonovits theorem; the
  paper only needs `k = 2`).
* `glue_accept`: if the number of possible colours `c(a,b)` (labels, marks and proofs of the
  `2r+2` nodes nearest to the edge `{a[1], b[1]}` on both sides) is small, there are `a₁ ≠ a₂`,
  `b₁ ≠ b₂` such that the `2n`-cycle `C(a₁,b₁) ⊕ C(a₂,b₂)` (with inherited labels, marks and proofs) is
  accepted by all nodes.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset

-- CSLib candidate
/-- If the edges of the complete bipartite graph `K_{α,β}` are coloured with the colours of `T`,
`|T| (|T|+1)² < |α|` and `|T| < |β|`, then there is a monochromatic rectangle (4-cycle). -/
lemma exists_mono_rect {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (T : Finset γ) (c : α → β → γ) (hc : ∀ a b, c a b ∈ T)
    (hA : T.card * (T.card + 1) ^ 2 < Fintype.card α) (hB : T.card < Fintype.card β) :
    ∃ a a' b b', a ≠ a' ∧ b ≠ b' ∧ c a b' = c a b ∧ c a' b = c a b ∧ c a' b' = c a b := by
  classical
  obtain ⟨B0, -, hB0⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset β))
    (n := T.card + 1) (by simpa using hB)
  have hpair : ∀ a, ∃ x ∈ B0, ∃ y ∈ B0, x ≠ y ∧ c a x = c a y := fun a =>
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := T) (by omega) (fun b _ => hc a b)
  choose x hx y hy hxy hcxy using hpair
  let f : α → β × β × γ := fun a => (x a, y a, c a (x a))
  have hf : ∀ a ∈ (Finset.univ : Finset α), f a ∈ B0 ×ˢ B0 ×ˢ T := fun a _ => by
    simp [f, hx a, hy a, hc]
  have hcard : (B0 ×ˢ B0 ×ˢ T).card < (Finset.univ : Finset α).card := by
    simp only [Finset.card_product, hB0, Finset.card_univ]
    calc (T.card + 1) * ((T.card + 1) * T.card) = T.card * (T.card + 1) ^ 2 := by ring
      _ < _ := hA
  obtain ⟨a, -, a', -, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hf
  simp only [f, Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨a, a', x a, y a, hne, hxy a, (hcxy a).symm, ?_, ?_⟩
  · exact (congrArg (c a') h1).trans h3.symm
  · exact ((congrArg (c a') h2).trans (hcxy a').symm).trans h3.symm

variable {L : Type*}

/-- `x ∈ l` decides between two data. -/
def piece {γ : Type*} (l : List ℕ) (f g : ℕ → γ) (x : ℕ) : γ := by
  classical exact if x ∈ l then f x else g x

lemma piece_of_mem {γ : Type*} {l : List ℕ} {f g : ℕ → γ} {x : ℕ} (h : x ∈ l) :
    piece l f g x = f x := by simp [piece, h]

lemma piece_of_not_mem {γ : Type*} {l : List ℕ} {f g : ℕ → γ} {x : ℕ} (h : x ∉ l) :
    piece l f g x = g x := by simp [piece, h]

section Glue

variable {α β : Type*} (la : α → List ℕ) (lb : β → List ℕ)

/-- The node list of the yes-instance `C(a,b)`. -/
def lst (a : α) (b : β) : List ℕ := la a ++ (lb b).reverse

/-- Hypotheses on the identifier lists: duplicate-free, pairwise disjoint. -/
structure GoodLists (nA nB : ℕ) : Prop where
  lenA : ∀ a, (la a).length = nA
  lenB : ∀ b, (lb b).length = nB
  ndA : ∀ a, (la a).Nodup
  ndB : ∀ b, (lb b).Nodup
  dAA : ∀ a a', a ≠ a' → ∀ x ∈ la a, x ∉ la a'
  dBB : ∀ b b', b ≠ b' → ∀ x ∈ lb b, x ∉ lb b'
  dAB : ∀ a b, ∀ x ∈ la a, x ∉ lb b

variable {la lb} {nA nB : ℕ}

lemma GoodLists.nodup_lst (hG : GoodLists la lb nA nB) (a : α) (b : β) : (lst la lb a b).Nodup := by
  simp only [lst, List.nodup_append, List.nodup_reverse, hG.ndA, hG.ndB, List.mem_reverse, true_and]
  intro x hx y hy hxy; subst hxy; exact hG.dAB a b x hx hy

lemma GoodLists.nodup_two (hG : GoodLists la lb nA nB) {a₁ a₂ : α} {b₁ b₂ : β} (ha : a₁ ≠ a₂)
    (hb : b₁ ≠ b₂) : (lst la lb a₁ b₁ ++ lst la lb a₂ b₂).Nodup := by
  rw [List.nodup_append]
  refine ⟨hG.nodup_lst a₁ b₁, hG.nodup_lst a₂ b₂, ?_⟩
  intro x hx y hy hxy; subst hxy
  simp only [lst, List.mem_append, List.mem_reverse] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hG.dAA _ _ ha x hx hy
  · exact hG.dAB _ _ x hx hy
  · exact hG.dAB _ _ x hy hx
  · exact hG.dBB _ _ hb x hx hy

lemma GoodLists.nodup_junction (hG : GoodLists la lb nA nB) {a₁ a₂ : α} {b₁ b₂ : β}
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    ((lb b₁).reverse ++ la a₂ ++ ((lb b₂).reverse ++ la a₁)).Nodup := by
  have := hG.nodup_two ha hb
  refine (List.Perm.nodup_iff ?_).1 this
  simp only [lst, List.append_assoc]
  refine List.perm_append_comm.trans ?_
  simp only [List.append_assoc]
  exact List.Perm.refl _

/-- Acceptance transfers along a shared segment of two labelled cycles. -/
lemma accept_of_segment {A : Verifier L} {r : ℕ} (hA : IsLocal r A) {l w z z' : List ℕ}
    {lab lab' : ℕ → L} {mk mk' : ℕ → Bool} {P P' : Proof}
    (hrot : cyc l lab mk = cyc (w ++ z) lab mk) (h : (w ++ z).Nodup) (h' : (w ++ z').Nodup)
    (hacc : AllAccept A (cyc (w ++ z') lab' mk') P')
    {i : ℕ} (hi1 : r + 1 ≤ i) (hi2 : i + r + 1 < w.length)
    (hag : ∀ (j : ℕ) (hj : j < w.length), i ≤ j + r + 1 → j ≤ i + r →
      lab w[j] = lab' w[j] ∧ mk w[j] = mk' w[j] ∧ P w[j] = P' w[j]) :
    A (cyc l lab mk) P w[i] = true := by
  rw [hrot, hA _ _ _ _ _ (viewEq_cyc_segment h h' hi1 hi2 hag)]
  exact hacc _ (by simp)

variable {A : Verifier L} {r : ℕ} {a₁ a₂ : α} {b₁ b₂ : β}

/-- Nodes of `C(a₁,b₁)` far from the glued edges see the same as in `C(a₁,b₁)`. -/
lemma accept_interior (hA : IsLocal r A) (hG : GoodLists la lb nA nB) (ha : a₁ ≠ a₂)
    (hb : b₁ ≠ b₂) {lab lab' : ℕ → L} {mk mk' : ℕ → Bool} {P P' : Proof}
    (hacc : AllAccept A (cyc (lst la lb a₁ b₁) lab mk) P)
    (h1 : ∀ x ∈ lst la lb a₁ b₁, lab' x = lab x ∧ mk' x = mk x ∧ P' x = P x)
    {i : ℕ} (hi1 : r + 1 ≤ i) (hi2 : i + r + 1 < (lst la lb a₁ b₁).length) :
    A (cyc (lst la lb a₁ b₁ ++ lst la lb a₂ b₂) lab' mk') P' (lst la lb a₁ b₁)[i] = true := by
  refine accept_of_segment (z' := []) hA rfl (hG.nodup_two ha hb) (by simpa using hG.nodup_lst a₁ b₁)
    (by simpa using hacc) hi1 hi2 fun j hj _ _ => ?_
  obtain ⟨e1, e2, e3⟩ := h1 _ (List.getElem_mem hj)
  exact ⟨e1, e2, e3⟩

/-- Nodes near the glued edge `{b₁[1], a₂[1]}` see the same as in `C(a₂,b₁)`, if the labels,
marks and proofs of the `2r+2` nodes nearest to the edge agree. -/
lemma accept_junction (hA : IsLocal r A) (hG : GoodLists la lb nA nB) (ha : a₁ ≠ a₂)
    (hb : b₁ ≠ b₂) (hnA : 2 * r + 2 ≤ nA) (hnB : 2 * r + 2 ≤ nB)
    {labY lab' : ℕ → L} {mkY mk' : ℕ → Bool} {PY P' : Proof}
    (hacc : AllAccept A (cyc (lst la lb a₂ b₁) labY mkY) PY)
    (hB : ∀ (j : ℕ) (hj : j < (lb b₁).length), j ≤ 2 * r + 1 →
      lab' (lb b₁)[j] = labY (lb b₁)[j] ∧ mk' (lb b₁)[j] = mkY (lb b₁)[j] ∧
        P' (lb b₁)[j] = PY (lb b₁)[j])
    (hA' : ∀ (j : ℕ) (hj : j < (la a₂).length), j ≤ 2 * r + 1 →
      lab' (la a₂)[j] = labY (la a₂)[j] ∧ mk' (la a₂)[j] = mkY (la a₂)[j] ∧
        P' (la a₂)[j] = PY (la a₂)[j]) :
    (∀ (j : ℕ) (hj : j < (lb b₁).length), j ≤ r →
      A (cyc (lst la lb a₁ b₁ ++ lst la lb a₂ b₂) lab' mk') P' (lb b₁)[j] = true) ∧
    (∀ (j : ℕ) (hj : j < (la a₂).length), j ≤ r →
      A (cyc (lst la lb a₁ b₁ ++ lst la lb a₂ b₂) lab' mk') P' (la a₂)[j] = true) := by
  set w := (lb b₁).reverse ++ la a₂ with hw
  have hlA := hG.lenA a₂
  have hlB := hG.lenB b₁
  have hwl : w.length = nB + nA := by simp [w, hlA, hlB]
  have hrot : cyc (lst la lb a₁ b₁ ++ lst la lb a₂ b₂) lab' mk' =
      cyc (w ++ ((lb b₂).reverse ++ la a₁)) lab' mk' := by
    rw [show lst la lb a₁ b₁ ++ lst la lb a₂ b₂ =
      la a₁ ++ ((lb b₁).reverse ++ la a₂ ++ (lb b₂).reverse) by simp [lst], cyc_append_comm]
    simp [w]
  have hacc' : AllAccept A (cyc (w ++ []) labY mkY) PY := by
    rw [List.append_nil, hw, ← cyc_append_comm]; exact hacc
  have hnd' : (w ++ []).Nodup := by
    rw [List.append_nil, hw]
    have := hG.nodup_lst a₂ b₁
    rw [lst] at this
    exact List.perm_append_comm.nodup_iff.1 this
  -- the elements of `w`
  have hwB : ∀ (k : ℕ) (hk : k < nB), w[k]'(by omega) = (lb b₁)[nB - 1 - k]'(by omega) := by
    intro k hk
    simp only [w, List.getElem_append_left (show k < (lb b₁).reverse.length by simp; omega),
      List.getElem_reverse, hlB]
  have hwA : ∀ (k : ℕ) (hk : k < nB + nA), nB ≤ k → w[k]'(by omega) = (la a₂)[k - nB]'(by omega) := by
    intro k hk hk'
    simp only [w, List.getElem_append_right (show (lb b₁).reverse.length ≤ k by simp; omega),
      List.length_reverse, hlB]
  -- agreement on the window
  have hagW : ∀ (k : ℕ) (hk : k < w.length), nB ≤ k + 2 * r + 2 → k ≤ nB + 2 * r + 1 →
      lab' w[k] = labY w[k] ∧ mk' w[k] = mkY w[k] ∧ P' w[k] = PY w[k] := by
    intro k hk h1 h2
    by_cases hkB : k < nB
    · rw [hwB k hkB]; exact hB _ _ (by omega)
    · rw [hwA k (by omega) (by omega)]; exact hA' _ _ (by omega)
  constructor
  · intro j hj hjr
    have hv : (lb b₁)[j] = w[nB - 1 - j]'(by omega) := by
      rw [hwB _ (by omega)]; congr 1; omega
    rw [hv]
    exact accept_of_segment hA hrot (by rw [hw]; exact hG.nodup_junction ha hb) hnd' hacc'
      (by omega) (by omega) fun k hk h1 h2 => hagW k hk (by omega) (by omega)
  · intro j hj hjr
    have hv : (la a₂)[j] = w[nB + j]'(by omega) := by
      rw [hwA _ (by omega) (by omega)]; congr 1; omega
    rw [hv]
    exact accept_of_segment hA hrot (by rw [hw]; exact hG.nodup_junction ha hb) hnd' hacc'
      (by omega) (by omega) fun k hk h1 h2 => hagW k hk (by omega) (by omega)

variable (la lb) in
/-- The colour `c(a,b)` of the edge `{a,b}` of `K_{α,β}`: node labels, marks and proof labels of
the `W` nodes of `a` and the `W` nodes of `b` nearest to the edge `{a[1], b[1]}` of `C(a,b)`. -/
def colour (W : ℕ) (lab : α → β → ℕ → L) (mk : α → β → ℕ → Bool) (P : α → β → Proof) (a : α)
    (b : β) : Fin 2 × Fin W → L × Bool × List Bool := fun p =>
  let x := if p.1 = 0 then (la a).getD p.2 0 else (lb b).getD p.2 0
  (lab a b x, mk a b x, P a b x)

variable {W : ℕ} {lab : α → β → ℕ → L} {mk : α → β → ℕ → Bool} {P : α → β → Proof}

lemma colour_B {a a' : α} {b : β} (h : colour la lb W lab mk P a b = colour la lb W lab mk P a' b)
    (j : ℕ) (hj : j < (lb b).length) (hjW : j < W) :
    lab a b (lb b)[j] = lab a' b (lb b)[j] ∧ mk a b (lb b)[j] = mk a' b (lb b)[j] ∧
      P a b (lb b)[j] = P a' b (lb b)[j] := by
  have := congrFun h (1, ⟨j, hjW⟩)
  simpa [colour, List.getElem?_eq_getElem hj] using this

lemma colour_A {a : α} {b b' : β} (h : colour la lb W lab mk P a b = colour la lb W lab mk P a b')
    (j : ℕ) (hj : j < (la a).length) (hjW : j < W) :
    lab a b (la a)[j] = lab a b' (la a)[j] ∧ mk a b (la a)[j] = mk a b' (la a)[j] ∧
      P a b (la a)[j] = P a b' (la a)[j] := by
  have := congrFun h (0, ⟨j, hjW⟩)
  simpa [colour, List.getElem?_eq_getElem hj] using this

variable (la lb) in
/-- The glued `2n`-cycle `C(a₁,b₁) ⊕ C(a₂,b₂)`: the edges `{a₁[1],b₁[1]}`, `{a₂[1],b₂[1]}` are
replaced by `{b₁[1],a₂[1]}`, `{b₂[1],a₁[1]}`; labels and marks are inherited (a new edge inherits the
mark of the removed edge `{a₁[1],b₁[1]}`, resp. `{a₂[1],b₂[1]}`). -/
def glued (lab : α → β → ℕ → L) (mk : α → β → ℕ → Bool) (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β) :
    Inst L :=
  cyc (lst la lb a₁ b₁ ++ lst la lb a₂ b₂) (piece (lst la lb a₁ b₁) (lab a₁ b₁) (lab a₂ b₂))
    (piece (lst la lb a₁ b₁) (mk a₁ b₁) (mk a₂ b₂))

variable (la lb) in
/-- The inherited proof on the glued cycle. -/
def gluedProof (P : α → β → Proof) (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β) : Proof :=
  piece (lst la lb a₁ b₁) (P a₁ b₁) (P a₂ b₂)

/-- **The gluing step of Theorem 5.1.** If every `C(a,b)` (with some labels, marks and proof of
size `≤ s`) is accepted by all nodes of a verifier of horizon `r`, and the number of possible
colours is small (`K (K+1)² < |α|`, `K < |β|` for `K = (|L| 2^(s+2))^(4r+4)`), then some glued
`2n`-cycle `C(a₁,b₁) ⊕ C(a₂,b₂)` with `a₁ ≠ a₂`, `b₁ ≠ b₂` is accepted by all nodes. -/
theorem glue_accept [Fintype α] [Fintype β] [Fintype L] [DecidableEq L] (hA : IsLocal r A)
    (hG : GoodLists la lb nA nB) (hnA : 2 * r + 2 ≤ nA) (hnB : 2 * r + 2 ≤ nB) (s : ℕ)
    (hacc : ∀ a b, AllAccept A (cyc (lst la lb a b) (lab a b) (mk a b)) (P a b))
    (hsize : ∀ a b, SizeLE (cyc (lst la lb a b) (lab a b) (mk a b)) (P a b) s)
    (hK : (Fintype.card L * 2 ^ (s + 2)) ^ (4 * r + 4) *
      ((Fintype.card L * 2 ^ (s + 2)) ^ (4 * r + 4) + 1) ^ 2 < Fintype.card α)
    (hKB : (Fintype.card L * 2 ^ (s + 2)) ^ (4 * r + 4) < Fintype.card β) :
    ∃ a₁ a₂ b₁ b₂, a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      AllAccept A (glued la lb lab mk a₁ b₁ a₂ b₂) (gluedProof la lb P a₁ b₁ a₂ b₂) := by
  classical
  set K := (Fintype.card L * 2 ^ (s + 2)) ^ (4 * r + 4) with hKdef
  let T : Finset (Fin 2 × Fin (2 * r + 2) → L × Bool × List Bool) :=
    Fintype.piFinset fun _ => (Finset.univ : Finset L) ×ˢ (Finset.univ : Finset Bool) ×ˢ
      bitStrings s
  have hT : T.card ≤ K := by
    simp only [T, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Finset.card_product,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    rw [hKdef, show 2 * (2 * r + 2) = 4 * r + 4 by ring]
    gcongr
    calc 2 * (bitStrings s).card ≤ 2 * 2 ^ (s + 1) := by
          gcongr; exact card_bitStrings_le s
      _ = 2 ^ (s + 2) := by ring
  have hc : ∀ a b, colour la lb (2 * r + 2) lab mk P a b ∈ T := by
    intro a b
    simp only [T, Fintype.mem_piFinset, Finset.mem_product, Finset.mem_univ, true_and,
      mem_bitStrings]
    rintro ⟨i, j⟩
    have hj := j.isLt
    fin_cases i
    · simp only [colour, Fin.zero_eta, Fin.isValue, ↓reduceIte]
      rw [List.getD_eq_getElem _ _ (by rw [hG.lenA]; omega)]
      exact hsize a b _ (by simp [lst, List.getElem_mem])
    · simp only [colour, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [List.getD_eq_getElem _ _ (by rw [hG.lenB]; omega)]
      exact hsize a b _ (by simp [lst, List.getElem_mem])
  obtain ⟨a₁, a₂, b₁, b₂, ha, hb, h12, h21, h22⟩ := exists_mono_rect T
    (colour la lb (2 * r + 2) lab mk P) hc
    (lt_of_le_of_lt (by gcongr) hK) (lt_of_le_of_lt hT hKB)
  refine ⟨a₁, a₂, b₁, b₂, ha, hb, ?_⟩
  -- the inherited data
  set lab' := piece (lst la lb a₁ b₁) (lab a₁ b₁) (lab a₂ b₂)
  set mk' := piece (lst la lb a₁ b₁) (mk a₁ b₁) (mk a₂ b₂)
  set P' := piece (lst la lb a₁ b₁) (P a₁ b₁) (P a₂ b₂)
  have hnd := hG.nodup_two ha hb
  have d1 : ∀ x ∈ lst la lb a₁ b₁, lab' x = lab a₁ b₁ x ∧ mk' x = mk a₁ b₁ x ∧ P' x = P a₁ b₁ x :=
    fun x hx => ⟨piece_of_mem hx, piece_of_mem hx, piece_of_mem hx⟩
  have d2 : ∀ x ∈ lst la lb a₂ b₂, lab' x = lab a₂ b₂ x ∧ mk' x = mk a₂ b₂ x ∧ P' x = P a₂ b₂ x := by
    intro x hx
    have hx' : x ∉ lst la lb a₁ b₁ := fun h1 => (List.nodup_append.1 hnd).2.2 x h1 x hx rfl
    exact ⟨piece_of_not_mem hx', piece_of_not_mem hx', piece_of_not_mem hx'⟩
  have hswap : glued la lb lab mk a₁ b₁ a₂ b₂ =
      cyc (lst la lb a₂ b₂ ++ lst la lb a₁ b₁) lab' mk' := cyc_append_comm _ _ _ _
  have hlA := hG.lenA
  have hlB := hG.lenB
  have hlst : ∀ a b, (lst la lb a b).length = nA + nB := fun a b => by simp [lst, hlA, hlB]
  -- the four junction instances
  have J1 := accept_junction (lab' := lab') (mk' := mk') (P' := P') hA hG ha hb hnA hnB
    (hacc a₂ b₁)
    (fun j hj hjr => by
      obtain ⟨e1, e2, e3⟩ := d1 (lb b₁)[j] (by simp [lst, List.getElem_mem])
      obtain ⟨f1, f2, f3⟩ := colour_B h21.symm j hj (by omega)
      exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩)
    (fun j hj hjr => by
      obtain ⟨e1, e2, e3⟩ := d2 (la a₂)[j] (by simp [lst, List.getElem_mem])
      obtain ⟨f1, f2, f3⟩ := colour_A (h22.trans h21.symm) j hj (by omega)
      exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩)
  have J2 := accept_junction (lab' := lab') (mk' := mk') (P' := P') hA hG ha.symm hb.symm hnA hnB
    (hacc a₁ b₂)
    (fun j hj hjr => by
      obtain ⟨e1, e2, e3⟩ := d2 (lb b₂)[j] (by simp [lst, List.getElem_mem])
      obtain ⟨f1, f2, f3⟩ := colour_B (h22.trans h12.symm) j hj (by omega)
      exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩)
    (fun j hj hjr => by
      obtain ⟨e1, e2, e3⟩ := d1 (la a₁)[j] (by simp [lst, List.getElem_mem])
      obtain ⟨f1, f2, f3⟩ := colour_A h12.symm j hj (by omega)
      exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩)
  have I1 := fun i => accept_interior (lab' := lab') (mk' := mk') (P' := P') (i := i) hA hG ha hb
    (hacc a₁ b₁) d1
  have I2 := fun i => accept_interior (lab' := lab') (mk' := mk') (P' := P') (i := i) hA hG ha.symm
    hb.symm (hacc a₂ b₂) d2
  intro v hv
  have hv' : v ∈ la a₁ ∨ v ∈ lb b₁ ∨ v ∈ la a₂ ∨ v ∈ lb b₂ := by
    simpa [glued, lst, or_assoc] using hv
  rcases hv' with h | h | h | h <;> obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  · by_cases hjr : j ≤ r
    · rw [hswap]; exact J2.2 j hj hjr
    · have e : (la a₁)[j] = (lst la lb a₁ b₁)[j]'(by rw [hlst]; have := hlA a₁; omega) := by
        simp [lst, List.getElem_append_left hj]
      rw [e]; exact I1 j (by omega) (by have := hlA a₁; rw [hlst]; omega)
  · by_cases hjr : j ≤ r
    · exact J1.1 j hj hjr
    · have e : (lb b₁)[j] = (lst la lb a₁ b₁)[nA + (nB - 1 - j)]'(by rw [hlst]; have := hlB b₁; omega) := by
        simp only [lst]
        rw [List.getElem_append_right (by rw [hlA]; omega)]
        simp only [List.getElem_reverse, hlA, hlB]
        congr 1; rw [← hlB b₁]; omega
      rw [e]; exact I1 _ (by have := hlB b₁; omega) (by have := hlB b₁; rw [hlst]; omega)
  · by_cases hjr : j ≤ r
    · exact J1.2 j hj hjr
    · have e : (la a₂)[j] = (lst la lb a₂ b₂)[j]'(by rw [hlst]; have := hlA a₂; omega) := by
        simp [lst, List.getElem_append_left hj]
      rw [hswap, e]; exact I2 j (by omega) (by have := hlA a₂; rw [hlst]; omega)
  · by_cases hjr : j ≤ r
    · rw [hswap]; exact J2.1 j hj hjr
    · have e : (lb b₂)[j] = (lst la lb a₂ b₂)[nA + (nB - 1 - j)]'(by rw [hlst]; have := hlB b₂; omega) := by
        simp only [lst]
        rw [List.getElem_append_right (by rw [hlA]; omega)]
        simp only [List.getElem_reverse, hlA, hlB]
        congr 1; rw [← hlB b₂]; omega
      rw [hswap, e]; exact I2 _ (by have := hlB b₂; omega) (by have := hlB b₂; rw [hlst]; omega)

end Glue

end Podc.LocallyCheckableProofs
