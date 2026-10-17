import Papers.PODC2017.StatelessComputation.Basics

/-!
# Proposition 2.3: every function is computable with labels of `n + 1` bits in `2n` rounds

Dolev, Erdmann, Lutz, Schapira, Zair, *Stateless Computation*, PODC 2017, Prop. 2.3 / A.3.

On a strongly connected digraph fix a root, an in-tree `T₂` (parent `p2`, arcs `v → p2 v`) and an
out-tree `T₁` (parent `p1`, arcs `p1 v → v`). Labels are pairs `(z, b) ∈ {0,1}ⁿ × {0,1}`.
Along `T₂` every node sends to its parent its own input (at its own coordinate) OR-ed with the
`z`-vectors received from its `T₂`-children; the root applies `f` to the resulting vector and
sends the result down `T₁` in the `b`-bit; every node outputs the `b`-bit received from its
`T₁`-parent. This is the paper's protocol.

We prove it for arbitrary rank-certified trees (`Trees`) with explicit time bounds, and
construct BFS trees with ranks `≤ n - 1` in strongly connected digraphs.
-/

namespace StatelessComputation
namespace UpperBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V}

/-- An out-tree (`p1`) and an in-tree (`p2`) rooted at `root`, certified by rank functions. -/
structure Trees (G : Digraph V) (root : V) where
  /-- Parent in the out-tree `T₁` (arc `p1 v → v`). -/
  p1 : V → V
  /-- Parent in the in-tree `T₂` (arc `v → p2 v`). -/
  p2 : V → V
  /-- Depth in `T₁`. -/
  r1 : V → ℕ
  /-- Depth in `T₂`. -/
  r2 : V → ℕ
  adj1 : ∀ v, v ≠ root → G.Adj (p1 v) v
  adj2 : ∀ v, v ≠ root → G.Adj v (p2 v)
  rank1 : ∀ v, v ≠ root → r1 (p1 v) + 1 = r1 v
  rank2 : ∀ v, v ≠ root → r2 (p2 v) + 1 = r2 v

variable {root : V} (T : Trees G root)

/-- `Desc T u i`: `i` lies on the `T₂`-path from `u` to the root. -/
inductive Desc (T : Trees G root) : V → V → Prop
  | refl (u : V) : Desc T u u
  | step {u i : V} : u ≠ root → Desc T (T.p2 u) i → Desc T u i

omit [Fintype V] [DecidableEq V] in
lemma Desc.trans {u c i : V} (h1 : Desc T u c) (h2 : Desc T c i) : Desc T u i := by
  induction h1 with
  | refl => exact h2
  | step hu _ ih => exact Desc.step hu (ih h2)

omit [Fintype V] in
lemma desc_root (u : V) : Desc T u root := by
  induction h : T.r2 u using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    by_cases hu : u = root
    · rw [hu]; exact Desc.refl _
    · exact Desc.step hu (ih _ (by have := T.rank2 u hu; omega) _ rfl)

omit [Fintype V] [DecidableEq V] in
lemma desc_iff (u i : V) :
    Desc T u i ↔ u = i ∨ ∃ c, c ≠ root ∧ T.p2 c = i ∧ Desc T u c := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @step u i hu _ ih =>
      rcases ih with h | ⟨c, hc, hpc, hd⟩
      · exact Or.inr ⟨u, hu, h, Desc.refl _⟩
      · exact Or.inr ⟨c, hc, hpc, Desc.step hu hd⟩
  · rintro (rfl | ⟨c, hc, rfl, hd⟩)
    · exact Desc.refl _
    · exact hd.trans _ (Desc.step hc (Desc.refl _))

/-- The label space `{0,1}ⁿ × {0,1}`. -/
abbrev Lbl (V : Type*) := (V → Bool) × Bool

open Classical in
/-- The `z`-vector a node assembles: its own input at its coordinate, OR-ed with the
`z`-vectors from its `T₂`-children. -/
noncomputable def zin (i : V) (inl : InNbr G i → Lbl V) (xi : Bool) : V → Bool := fun u =>
  (decide (u = i) && xi) ||
    decide (∃ c : InNbr G i, c.1 ≠ root ∧ T.p2 c.1 = i ∧ (inl c).1 u = true)

lemma zin_true (i : V) (inl : InNbr G i → Lbl V) (xi : Bool) (u : V) :
    zin T i inl xi u = true ↔
      (u = i ∧ xi = true) ∨ ∃ c : InNbr G i, c.1 ≠ root ∧ T.p2 c.1 = i ∧ (inl c).1 u = true := by
  simp [zin]

/-- The `b`-bit a node holds: `f` of its `z`-vector at the root, the bit from the `T₁`-parent
elsewhere. -/
noncomputable def bval (f : (V → Bool) → Bool) (i : V) (inl : InNbr G i → Lbl V) (xi : Bool) :
    Bool :=
  if h : i = root then f (zin T i inl xi) else (inl ⟨T.p1 i, T.adj1 i h⟩).2

/-- The protocol of Proposition 2.3. -/
noncomputable def proto (f : (V → Bool) → Bool) : Protocol G (Lbl V) Bool Bool :=
  ⟨fun i inl xi =>
    (fun j => (if i ≠ root ∧ j.1 = T.p2 i then zin T i inl xi else fun _ => false,
               if j.1 ≠ root ∧ T.p1 j.1 = i then bval T f i inl xi else false),
     bval T f i inl xi)⟩

variable (f : (V → Bool) → Bool) (x : V → Bool) (ℓ0 : Labeling G (Lbl V))

open Classical in
/-- The correct `z`-vector of node `i`: the inputs of its `T₂`-subtree. -/
noncomputable def Zt (i : V) : V → Bool := fun u => decide (Desc T u i) && x u

omit [Fintype V] [DecidableEq V] in
lemma Zt_true (i u : V) : Zt T x i u = true ↔ Desc T u i ∧ x u = true := by
  simp [Zt]

/-- `H = 1 + max depth in T₂`. -/
def H : ℕ := univ.sup T.r2 + 1

/-- `M = max depth in T₁`. -/
def M : ℕ := univ.sup T.r1

omit [DecidableEq V] in
lemma r2_lt_H (v : V) : T.r2 v < H T := Nat.lt_succ_of_le (le_sup (mem_univ v))

omit [DecidableEq V] in
lemma r1_le_M (v : V) : T.r1 v ≤ M T := le_sup (mem_univ v)

lemma syncRun_succ_apply (t : ℕ) (e : Arc G) :
    (proto T f).syncRun x ℓ0 (t + 1) e =
      (if e.1.1 ≠ root ∧ e.1.2 = T.p2 e.1.1 then
          zin T e.1.1 (inLab ((proto T f).syncRun x ℓ0 t) e.1.1) (x e.1.1) else fun _ => false,
       if e.1.2 ≠ root ∧ T.p1 e.1.2 = e.1.1 then
          bval T f e.1.1 (inLab ((proto T f).syncRun x ℓ0 t) e.1.1) (x e.1.1) else false) := by
  rw [Protocol.syncRun_succ]; rfl

/-- The `z`-labels along `T₂` are correct from time `H - r2 i` on. -/
lemma zlab (t : ℕ) (e : Arc G) (he : e.1.1 ≠ root) (he2 : e.1.2 = T.p2 e.1.1)
    (ht : H T ≤ t + T.r2 e.1.1) : ((proto T f).syncRun x ℓ0 t e).1 = Zt T x e.1.1 := by
  induction t generalizing e with
  | zero => have := r2_lt_H T e.1.1; omega
  | succ t ih =>
    rw [syncRun_succ_apply]; dsimp only; rw [ite_eq_left (show _ ∧ _ from ⟨he, he2⟩)]
    have hch : ∀ c : InNbr G e.1.1, c.1 ≠ root → T.p2 c.1 = e.1.1 →
        (inLab ((proto T f).syncRun x ℓ0 t) e.1.1 c).1 = Zt T x c.1 := by
      intro c hc hpc
      exact ih ⟨(c.1, e.1.1), c.2⟩ hc hpc.symm
        (by show H T ≤ t + T.r2 c.1; have := T.rank2 c.1 hc; rw [hpc] at this; omega)
    funext u
    rw [Bool.eq_iff_iff, zin_true, Zt_true, desc_iff T u e.1.1]
    constructor
    · rintro (⟨rfl, hxu⟩ | ⟨c, hc, hpc, hz⟩)
      · exact ⟨Or.inl rfl, hxu⟩
      · rw [hch c hc hpc, Zt_true] at hz
        exact ⟨Or.inr ⟨c.1, hc, hpc, hz.1⟩, hz.2⟩
    · rintro ⟨hu | ⟨c, hc, hpc, hd⟩, hxu⟩
      · subst hu; exact Or.inl ⟨rfl, hxu⟩
      · right
        have hadj : G.Adj c e.1.1 := hpc ▸ T.adj2 c hc
        refine ⟨⟨c, hadj⟩, hc, hpc, ?_⟩
        rw [hch ⟨c, hadj⟩ hc hpc, Zt_true]
        exact ⟨hd, hxu⟩

/-- From time `H - 1` on, the root assembles the whole input vector. -/
lemma zin_root (t : ℕ) (i : V) (hi : i = root) (ht : H T ≤ t + 1 + T.r2 root) :
    zin T i (inLab ((proto T f).syncRun x ℓ0 t) i) (x i) = x := by
  subst hi
  have hch : ∀ c : InNbr G i, c.1 ≠ i → T.p2 c.1 = i →
      (inLab ((proto T f).syncRun x ℓ0 t) i c).1 = Zt T x c.1 := by
    intro c hc hpc
    exact zlab T f x ℓ0 t ⟨(c.1, i), c.2⟩ hc hpc.symm
      (by show H T ≤ t + T.r2 c.1; have := T.rank2 c.1 hc; rw [hpc] at this; omega)
  funext u
  rw [Bool.eq_iff_iff, zin_true]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨c, hc, hpc, hz⟩)
    · exact h
    · rw [hch c hc hpc, Zt_true] at hz; exact hz.2
  · intro hxu
    rcases (desc_iff T u i).1 (desc_root T u) with rfl | ⟨c, hc, hpc, hd⟩
    · exact Or.inl ⟨rfl, hxu⟩
    · right
      have hadj : G.Adj c i := hpc ▸ T.adj2 c hc
      refine ⟨⟨c, hadj⟩, hc, hpc, ?_⟩
      rw [hch ⟨c, hadj⟩ hc hpc, Zt_true]
      exact ⟨hd, hxu⟩

/-- The `b`-bits along `T₁` are correct from time `H + r1` on. -/
lemma blab (t : ℕ) (e : Arc G) (he : e.1.2 ≠ root) (he1 : T.p1 e.1.2 = e.1.1)
    (ht : H T + T.r1 e.1.1 + T.r2 root ≤ t) : ((proto T f).syncRun x ℓ0 t e).2 = f x := by
  induction t generalizing e with
  | zero =>
    have := r2_lt_H T root; omega
  | succ t ih =>
    rw [syncRun_succ_apply]; dsimp only; rw [ite_eq_left (show _ ∧ _ from ⟨he, he1⟩)]
    unfold bval
    split_ifs with hroot
    · rw [zin_root T f x ℓ0 t _ hroot (by omega)]
    · exact ih ⟨(T.p1 e.1.1, e.1.1), T.adj1 _ hroot⟩ hroot rfl
        (by show H T + T.r1 (T.p1 e.1.1) + T.r2 root ≤ t; have := T.rank1 _ hroot; omega)

/-- Outputs are correct from time `H + M - 1` on. -/
lemma out_eq (t : ℕ) (ht : H T + M T + T.r2 root ≤ t + 1) (i : V) :
    (proto T f).out x ((proto T f).syncRun x ℓ0 t) i = f x := by
  show bval T f i (inLab ((proto T f).syncRun x ℓ0 t) i) (x i) = f x
  unfold bval
  split_ifs with hroot
  · rw [zin_root T f x ℓ0 t _ hroot (by omega)]
  · exact blab T f x ℓ0 t ⟨(T.p1 i, i), T.adj1 _ hroot⟩ hroot rfl
      (by show H T + T.r1 (T.p1 i) + T.r2 root ≤ t
          have := T.rank1 _ hroot; have := r1_le_M T i; omega)

/-- The limit labeling. -/
noncomputable def target : Labeling G (Lbl V) := fun e =>
  (if e.1.1 ≠ root ∧ e.1.2 = T.p2 e.1.1 then Zt T x e.1.1 else fun _ => false,
   if e.1.2 ≠ root ∧ T.p1 e.1.2 = e.1.1 then f x else false)

/-- Labels are stable from time `H + M` on. -/
lemma syncRun_eq_target (t : ℕ) (ht : H T + M T + T.r2 root ≤ t) :
    (proto T f).syncRun x ℓ0 t = target T f x := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := r2_lt_H T root; omega⟩
  funext e
  have h1 : ((proto T f).syncRun x ℓ0 (t + 1) e).1 = (target T f x e).1 := by
    simp only [target]
    split_ifs with hc
    · exact zlab T f x ℓ0 (t + 1) e hc.1 hc.2 (by have := r2_lt_H T root; omega)
    · rw [syncRun_succ_apply]; dsimp only; rw [ite_eq_right hc]
  have h2 : ((proto T f).syncRun x ℓ0 (t + 1) e).2 = (target T f x e).2 := by
    simp only [target]
    split_ifs with hc
    · exact blab T f x ℓ0 (t + 1) e hc.1 hc.2 (by have := r1_le_M T e.1.1; omega)
    · rw [syncRun_succ_apply]; dsimp only; rw [ite_eq_right hc]
  exact Prod.ext h1 h2

/-! ### BFS trees in strongly connected digraphs -/

omit [Fintype V] [DecidableEq V] in
/-- Strong connectivity (`Digraph.StronglyConnected`): every node reaches every node by a directed
walk of some length. -/
lemma stronglyConnected_iff : G.StronglyConnected ↔ ∀ u v, ∃ k, WalkLen G k u v :=
  forall₂_congr fun _ _ =>
    ⟨Relation.ReflTransGen.relatesInSteps, fun ⟨_, h⟩ => h.reflTransGen⟩

-- CSLib candidate: BFS in- and out-trees in strongly connected digraphs.
/-- BFS trees of depth `≤ n - 1` rooted at any node of a strongly connected digraph. -/
lemma exists_trees (hG : G.StronglyConnected) (root : V) :
    ∃ T : Trees G root, (∀ v, T.r1 v ≤ Fintype.card V - 1) ∧
      (∀ v, T.r2 v ≤ Fintype.card V - 1) ∧ T.r2 root = 0 := by
  classical
  replace hG := stronglyConnected_iff.1 hG
  let d1 : V → ℕ := fun v => Nat.find (hG root v)
  let d2 : V → ℕ := fun v => Nat.find (hG v root)
  have hp1 : ∀ v, v ≠ root → ∃ u, G.Adj u v ∧ d1 u + 1 = d1 v := by
    intro v hv
    have hw := Nat.find_spec (hG root v)
    obtain ⟨k, hk⟩ : ∃ k, Nat.find (hG root v) = k + 1 := by
      rcases h : Nat.find (hG root v) with _ | k
      · rw [h] at hw; exact absurd hw.zero.symm hv
      · exact ⟨k, rfl⟩
    rw [hk] at hw
    cases hw with
    | tail u _ _ hku hadj =>
      refine ⟨u, hadj, le_antisymm ?_ ?_⟩
      · have := Nat.find_min' (hG root u) hku
        change Nat.find (hG root u) + 1 ≤ Nat.find (hG root v); omega
      · exact Nat.find_min' (hG root v) (.tail _ _ _ _ (Nat.find_spec (hG root u)) hadj)
  have hp2 : ∀ v, v ≠ root → ∃ w, G.Adj v w ∧ d2 w + 1 = d2 v := by
    intro v hv
    have hw := Nat.find_spec (hG v root)
    obtain ⟨k, hk⟩ : ∃ k, Nat.find (hG v root) = k + 1 := by
      rcases h : Nat.find (hG v root) with _ | k
      · rw [h] at hw; exact absurd hw.zero hv
      · exact ⟨k, rfl⟩
    rw [hk] at hw
    obtain ⟨w, hadj, hkw⟩ := hw.succ'
    refine ⟨w, hadj, le_antisymm ?_ ?_⟩
    · have := Nat.find_min' (hG w root) hkw
      change Nat.find (hG w root) + 1 ≤ Nat.find (hG v root); omega
    · -- prepend the arc `v → w`
      exact Nat.find_min' (hG v root) (.head _ _ _ _ hadj (Nat.find_spec (hG w root)))
  let T : Trees G root :=
    { p1 := fun v => if h : v = root then root else (hp1 v h).choose
      p2 := fun v => if h : v = root then root else (hp2 v h).choose
      r1 := d1
      r2 := d2
      adj1 := fun v h => by simp only [h, dite_false]; exact (hp1 v h).choose_spec.1
      adj2 := fun v h => by simp only [h, dite_false]; exact (hp2 v h).choose_spec.1
      rank1 := fun v h => by simp only [h, dite_false]; exact (hp1 v h).choose_spec.2
      rank2 := fun v h => by simp only [h, dite_false]; exact (hp2 v h).choose_spec.2 }
  refine ⟨T, fun v => ?_, fun v => ?_, ?_⟩
  · obtain ⟨k, hk, hw⟩ := (Nat.find_spec (hG root v)).reflTransGen.relatesWithinSteps_card_sub_one
    exact (Nat.find_min' (hG root v) hw).trans hk
  · obtain ⟨k, hk, hw⟩ := (Nat.find_spec (hG v root)).reflTransGen.relatesWithinSteps_card_sub_one
    exact (Nat.find_min' (hG v root) hw).trans hk
  · exact Nat.eq_zero_of_le_zero (Nat.find_min' (hG root root) (.refl root))

/-- **Proposition 2.3** of [Dolev–Erdmann–Lutz–Schapira–Zair, PODC'17]. On a strongly connected
digraph with `n` nodes every Boolean function `f` is computed by a synchronously
label-stabilizing protocol with label space `{0,1}ⁿ × {0,1}` (label complexity `n + 1`):
all outputs are correct from time `2n - 1` on (computed from `ℓᵗ`, `t ≥ 2n - 2`) and the
labeling is constant from time `2n - 1` on (round complexity `≤ 2n`). -/
theorem prop_2_3 (hG : G.StronglyConnected) (root : V) (f : (V → Bool) → Bool) :
    ∃ P : Protocol G (Lbl V) Bool Bool,
      P.SyncLabelStabilizing ∧ P.SyncComputes f ∧
      (∀ x ℓ0 t, 2 * Fintype.card V ≤ t + 2 → ∀ i, P.out x (P.syncRun x ℓ0 t) i = f x) ∧
      (∀ x ℓ0 t, 2 * Fintype.card V ≤ t + 1 →
        P.syncRun x ℓ0 t = P.syncRun x ℓ0 (2 * Fintype.card V - 1)) := by
  obtain ⟨T, h1, h2, h0⟩ := exists_trees hG root
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨root⟩
  have hH : H T ≤ Fintype.card V := by
    have := Finset.sup_le (s := univ) (f := T.r2) (fun v _ => h2 v); simp only [H]; omega
  have hM : M T ≤ Fintype.card V - 1 := Finset.sup_le fun v _ => h1 v
  have hlab : ∀ x ℓ0 t, 2 * Fintype.card V ≤ t + 1 →
      (proto T f).syncRun x ℓ0 t = target T f x := fun x ℓ0 t ht =>
    syncRun_eq_target T f x ℓ0 t (by omega)
  refine ⟨proto T f, fun x ℓ0 => converges_iff.2 ⟨target T f x, 2 * Fintype.card V,
    fun t ht => hlab x ℓ0 t (by omega)⟩,
    fun x ℓ0 i => ⟨2 * Fintype.card V, fun t ht => out_eq T f x ℓ0 t (by omega) i⟩,
    fun x ℓ0 t ht i => out_eq T f x ℓ0 t (by omega) i, fun x ℓ0 t ht => ?_⟩
  rw [hlab x ℓ0 t ht, hlab x ℓ0 _ (by omega)]

/-- The label space of Proposition 2.3 has `2^(n+1)` elements (label complexity `n + 1`). -/
lemma card_lbl : Fintype.card (Lbl V) = 2 ^ (Fintype.card V + 1) := by
  simp [Lbl, pow_succ]

end UpperBound
end StatelessComputation
