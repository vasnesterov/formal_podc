import Papers.PODC2014.CongestedCliquePower.LowerBoundGraph

/-!
# Cyclic sequences and copies of `C_ℓ` (infrastructure for Section 3.4)

A copy `f` of the cycle `C_ℓ = cycleGraph ℓ` in a graph `G` is described by the `ℓ`-periodic
sequence `t ↦ f (t mod ℓ)` indexed by `ℤ` (`Copy.seq`); such sequences are characterized by
`IsCycSeq`: consecutive terms are adjacent and `x a = x b ↔ a ≡ b [ZMOD ℓ]`. Rotations and
reflections of a cyclic sequence are again cyclic sequences, which lets us normalize a copy of a
cycle before analysing it.

We also express conditions (b), (c) of Definition 10 for a copy of `C_ℓ` in terms of its sequence
(`FitsSeq`), and show that lower bound graphs can be transported along vertex embeddings
(`LowerBoundGraph.map`), e.g. to add isolated vertices or to relabel the vertices by `Fin n`.
-/

namespace Podc.CongestedCliquePower

open SimpleGraph

section Cyc

variable {ℓ : ℕ}

/-- The position `t mod ℓ` of the cycle `Fin ℓ`. -/
def cyc (ℓ : ℕ) [NeZero ℓ] (t : ℤ) : Fin ℓ :=
  ⟨(t % ℓ).toNat, by
    have h0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    have h1 := Int.emod_nonneg t h0.ne'
    have h2 := Int.emod_lt_of_pos t h0
    omega⟩

variable [NeZero ℓ]

lemma ℓ_pos : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)

lemma cyc_val (t : ℤ) : ((cyc ℓ t : ℕ) : ℤ) = t % ℓ := by
  have h1 := Int.emod_nonneg t (ℓ_pos (ℓ := ℓ)).ne'
  simp [cyc, h1]

lemma cyc_eq_iff {a b : ℤ} : cyc ℓ a = cyc ℓ b ↔ a ≡ b [ZMOD ℓ] := by
  rw [Fin.ext_iff, Int.ModEq, ← cyc_val, ← cyc_val]
  exact_mod_cast Iff.rfl

lemma cyc_natCast (k : Fin ℓ) : cyc ℓ (k.val : ℤ) = k := by
  ext
  have := cyc_val (ℓ := ℓ) (k.val : ℤ)
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast k.isLt)] at this
  exact_mod_cast this

lemma cyc_adj (hℓ : 2 ≤ ℓ) (t : ℤ) : (cycleGraph ℓ).Adj (cyc ℓ t) (cyc ℓ (t + 1)) := by
  rw [cycleGraph_adj']
  right
  have h0 : (0 : ℤ) < ℓ := ℓ_pos
  have hv1 := cyc_val (ℓ := ℓ) t
  have hv2 := cyc_val (ℓ := ℓ) (t + 1)
  have hlt := (cyc ℓ t).isLt
  have hlt' := (cyc ℓ (t + 1)).isLt
  rw [Fin.sub_def]
  simp only
  -- `(t + 1) % ℓ` is `t % ℓ + 1` or `0`
  have key : (t + 1) % ℓ = if t % ℓ + 1 < ℓ then t % ℓ + 1 else 0 := by
    rw [Int.add_emod, Int.emod_eq_of_lt (b := (ℓ : ℤ)) (a := 1) (by omega) (by omega)]
    have h1 := Int.emod_nonneg t h0.ne'
    have h2 := Int.emod_lt_of_pos t h0
    split_ifs with h
    · exact Int.emod_eq_of_lt (by omega) h
    · have : t % ℓ + 1 = ℓ := by omega
      rw [this, Int.emod_self]
  rw [← hv1, ← hv2] at key
  split_ifs at key with h
  · have : (cyc ℓ (t + 1) : ℕ) = cyc ℓ t + 1 := by omega
    rw [this, show ℓ - ↑(cyc ℓ t) + (↑(cyc ℓ t) + 1) = ℓ + 1 by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
  · have h1 : (cyc ℓ (t + 1) : ℕ) = 0 := by omega
    have h2 : (cyc ℓ t : ℕ) = ℓ - 1 := by omega
    rw [h1, h2, show ℓ - (ℓ - 1) + 0 = 1 by omega, Nat.mod_eq_of_lt (by omega)]

lemma cyc_val_natCast {n : ℕ} (hn : n < ℓ) : (cyc ℓ (n : ℤ) : ℕ) = n := by
  have := cyc_natCast (ℓ := ℓ) ⟨n, hn⟩
  exact congrArg Fin.val this

lemma cyc_succ_val (t : ℤ) :
    (cyc ℓ (t + 1) : ℕ) = if (cyc ℓ t : ℕ) + 1 < ℓ then (cyc ℓ t : ℕ) + 1 else 0 := by
  have h0 : (0 : ℤ) < ℓ := ℓ_pos
  have hv1 := cyc_val (ℓ := ℓ) t
  have hv2 := cyc_val (ℓ := ℓ) (t + 1)
  have hlt := (cyc ℓ t).isLt
  have h1 := Int.emod_nonneg t h0.ne'
  have h2 := Int.emod_lt_of_pos t h0
  have key : (t + 1) % ℓ = if t % ℓ + 1 < ℓ then t % ℓ + 1 else 0 := by
    rw [Int.add_emod]
    rcases Nat.lt_or_ge 1 ℓ with hℓ | hℓ
    · rw [Int.emod_eq_of_lt (b := (ℓ : ℤ)) (a := 1) (by omega) (by omega)]
      split_ifs with h
      · exact Int.emod_eq_of_lt (by omega) h
      · have : t % ℓ + 1 = ℓ := by omega
        rw [this, Int.emod_self]
    · have : ℓ = 1 := by have := NeZero.ne ℓ; omega
      subst this
      simp
  split_ifs at key ⊢ with h h' h'
  · omega
  · omega
  · omega
  · omega

/-- Every edge of `C_ℓ` joins two consecutive positions. -/
lemma exists_of_cycleGraph_adj {u v : Fin ℓ} (h : (cycleGraph ℓ).Adj u v) :
    cyc ℓ ((u : ℕ) + 1 : ℤ) = v ∨ cyc ℓ ((v : ℕ) + 1 : ℤ) = u := by
  rw [cycleGraph_adj'] at h
  rcases h with h | h
  · right
    rw [← cyc_natCast u, cyc_eq_iff, Int.ModEq]
    rw [Fin.sub_def] at h
    simp only at h
    have hu := u.isLt
    have hv := v.isLt
    have : (ℓ - v + u : ℕ) % ℓ = 1 := h
    rcases Nat.lt_or_ge (v : ℕ) (u : ℕ) with hlt | hge
    · rw [show ℓ - v + u = ℓ + (u - v) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)] at this
      have : (u : ℕ) = v + 1 := by omega
      rw [this]
      push_cast
      rfl
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt'
      · rw [heq, Nat.sub_add_cancel (by omega), Nat.mod_self] at this
        exact absurd this (by norm_num)
      rw [Nat.mod_eq_of_lt (by omega)] at this
      have h1 : (v : ℕ) = ℓ - 1 := by omega
      have h2 : (u : ℕ) = 0 := by omega
      rw [h1, h2]
      have : ((ℓ - 1 : ℕ) : ℤ) + 1 = ℓ := by omega
      push_cast [this]
      simp
  · left
    rw [← cyc_natCast v, cyc_eq_iff, Int.ModEq]
    rw [Fin.sub_def] at h
    simp only at h
    have hu := u.isLt
    have hv := v.isLt
    have : (ℓ - u + v : ℕ) % ℓ = 1 := h
    rcases Nat.lt_or_ge (u : ℕ) (v : ℕ) with hlt | hge
    · rw [show ℓ - u + v = ℓ + (v - u) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)] at this
      have : (v : ℕ) = u + 1 := by omega
      rw [this]
      push_cast
      rfl
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt'
      · rw [heq, Nat.sub_add_cancel (by omega), Nat.mod_self] at this
        exact absurd this (by norm_num)
      rw [Nat.mod_eq_of_lt (by omega)] at this
      have h1 : (u : ℕ) = ℓ - 1 := by omega
      have h2 : (v : ℕ) = 0 := by omega
      rw [h1, h2]
      have : ((ℓ - 1 : ℕ) : ℤ) + 1 = ℓ := by omega
      push_cast [this]
      simp

end Cyc

section Seq

variable {V : Type*} {G : SimpleGraph V} {ℓ : ℕ}

/-- `x : ℤ → V` traverses a cycle of length `ℓ` in `G`: consecutive terms are adjacent and
`x a = x b ↔ a ≡ b [ZMOD ℓ]`. -/
structure IsCycSeq (G : SimpleGraph V) (ℓ : ℕ) (x : ℤ → V) : Prop where
  adj : ∀ t, G.Adj (x t) (x (t + 1))
  eq_iff : ∀ a b, x a = x b ↔ a ≡ b [ZMOD ℓ]

namespace IsCycSeq

variable {x : ℤ → V} (hx : IsCycSeq G ℓ x)
include hx

lemma add_period (t : ℤ) : x (t + ℓ) = x t :=
  (hx.eq_iff _ _).2 (by simp [Int.ModEq])

lemma ne_add {a d : ℤ} (hd : 0 < d) (hdℓ : d < ℓ) : x a ≠ x (a + d) := by
  rw [Ne, hx.eq_iff]
  intro h
  have := h.dvd
  simp only [add_sub_cancel_left] at this
  have := Int.le_of_dvd hd this
  omega

lemma ne_two (hℓ : 3 ≤ ℓ) (a : ℤ) : x (a + 2) ≠ x a :=
  fun h => hx.ne_add (a := a) (d := 2) (by norm_num) (by omega) h.symm

/-- The predecessor of `x t` is `x (t - 1)`. -/
lemma adj_pred (t : ℤ) : G.Adj (x (t - 1)) (x t) := by
  simpa using hx.adj (t - 1)

lemma shift (s : ℤ) : IsCycSeq G ℓ (fun t => x (t + s)) where
  adj t := by simpa [add_right_comm] using hx.adj (t + s)
  eq_iff a b := by
    rw [hx.eq_iff]
    exact ⟨fun h => by simpa using h.add_right (-s), fun h => h.add_right s⟩

lemma neg : IsCycSeq G ℓ (fun t => x (-t)) where
  adj t := by
    have := (hx.adj (-t - 1)).symm
    rw [show -t - 1 + 1 = -t by ring] at this
    rwa [show -(t + 1) = -t - 1 by ring]
  eq_iff a b := by
    rw [hx.eq_iff]
    exact ⟨fun h => by simpa using h.neg, fun h => h.neg⟩

/-- A property of all terms follows from the terms at natural indices. -/
lemma forall_of_forall_nat [NeZero ℓ] {P : V → Prop} (h : ∀ n : ℕ, P (x n)) (t : ℤ) :
    P (x t) := by
  have h1 := Int.emod_nonneg t (ℓ_pos (ℓ := ℓ)).ne'
  have : x t = x ((t % ℓ).toNat : ℕ) := by
    rw [hx.eq_iff, Int.toNat_of_nonneg h1]
    exact (Int.mod_modEq t ℓ).symm
  rw [this]
  exact h _

lemma exists_nat_lt [NeZero ℓ] (t : ℤ) : ∃ n : ℕ, n < ℓ ∧ x t = x n := by
  have h1 := Int.emod_nonneg t (ℓ_pos (ℓ := ℓ)).ne'
  have h2 := Int.emod_lt_of_pos t (ℓ_pos (ℓ := ℓ))
  refine ⟨(t % ℓ).toNat, by omega, ?_⟩
  rw [hx.eq_iff, Int.toNat_of_nonneg h1]
  exact (Int.mod_modEq t ℓ).symm

end IsCycSeq

variable [NeZero ℓ]

/-- The cyclic sequence of a copy of `C_ℓ`. -/
def seq (f : (cycleGraph ℓ).Copy G) (t : ℤ) : V := f (cyc ℓ t)

lemma isCycSeq_seq (hℓ : 2 ≤ ℓ) (f : (cycleGraph ℓ).Copy G) : IsCycSeq G ℓ (seq f) where
  adj t := f.toHom.map_adj (cyc_adj hℓ t)
  eq_iff a b := by
    rw [← cyc_eq_iff]
    exact f.injective.eq_iff

lemma IsCycSeq.cyc_val {x : ℤ → V} (hx : IsCycSeq G ℓ x) (t : ℤ) :
    x ((cyc ℓ t : ℕ) : ℤ) = x t := by
  rw [hx.eq_iff, _root_.Podc.CongestedCliquePower.cyc_val]
  exact Int.mod_modEq t ℓ

/-- The copy of `C_ℓ` traversed by a cyclic sequence. -/
def copyOfSeq {x : ℤ → V} (hx : IsCycSeq G ℓ x) : (cycleGraph ℓ).Copy G where
  toHom := ⟨fun k => x (k.val : ℤ), fun {u v} h => by
    rcases exists_of_cycleGraph_adj h with h' | h'
    · rw [← h', hx.cyc_val]
      exact hx.adj _
    · rw [← h', hx.cyc_val]
      exact (hx.adj _).symm⟩
  injective' u v h := by
    change x _ = x _ at h
    rw [hx.eq_iff, ← cyc_eq_iff, cyc_natCast, cyc_natCast] at h
    exact h

lemma copyOfSeq_apply {x : ℤ → V} (hx : IsCycSeq G ℓ x) (k : Fin ℓ) :
    copyOfSeq hx k = x (k.val : ℤ) := rfl

lemma seq_copyOfSeq {x : ℤ → V} (hx : IsCycSeq G ℓ x) : seq (copyOfSeq hx) = x := by
  funext t
  exact hx.cyc_val t

lemma range_seq (f : (cycleGraph ℓ).Copy G) : Set.range (seq f) = Set.range f := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(k.val : ℤ), by simp [seq, cyc_natCast]⟩

end Seq

section FitsSeq

variable {VF V : Type*} {F : SimpleGraph VF} {G : SimpleGraph V} {ℓ : ℕ}

/-- `{a, b}` is the edge between two consecutive terms of `x`. -/
def SeqEdge (x : ℤ → V) (a b : V) : Prop :=
  ∃ t, (x t = a ∧ x (t + 1) = b) ∨ (x t = b ∧ x (t + 1) = a)

/-- Conditions (b), (c) of Definition 10 for the cycle traversed by `x` and the edge `{u, v}`. -/
def FitsSeq (D : LBData (cycleGraph ℓ) F G) (x : ℤ → V) (u v : VF) : Prop :=
  F.Adj u v ∧ SeqEdge x (D.φA u) (D.φA v) ∧ SeqEdge x (D.φB u) (D.φB v) ∧
    ∀ y, ((∃ t, x t = y) ∧ (y ∈ Set.range D.φA ∨ y ∈ Set.range D.φB)) ↔
      (y = D.φA u ∨ y = D.φA v ∨ y = D.φB u ∨ y = D.φB v)

variable {D : LBData (cycleGraph ℓ) F G} {x : ℤ → V} {u v : VF}

lemma SeqEdge.shift {a b : V} (s : ℤ) (h : SeqEdge (fun t => x (t + s)) a b) : SeqEdge x a b := by
  obtain ⟨t, h⟩ := h
  refine ⟨t + s, ?_⟩
  simpa only [add_right_comm t 1 s] using h

lemma SeqEdge.neg {a b : V} (h : SeqEdge (fun t => x (-t)) a b) : SeqEdge x a b := by
  obtain ⟨t, h⟩ := h
  refine ⟨-t - 1, ?_⟩
  rw [show -t - 1 + 1 = -t by ring, show -t - 1 = -(t + 1) by ring]
  tauto

lemma FitsSeq.shift (s : ℤ) (h : FitsSeq D (fun t => x (t + s)) u v) : FitsSeq D x u v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2.shift s, h3.shift s, fun y => ?_⟩
  rw [← h4]
  exact and_congr_left' ⟨fun ⟨t, ht⟩ => ⟨t - s, by simpa using ht⟩, fun ⟨t, ht⟩ => ⟨t + s, ht⟩⟩

lemma FitsSeq.neg (h : FitsSeq D (fun t => x (-t)) u v) : FitsSeq D x u v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2.neg, h3.neg, fun y => ?_⟩
  rw [← h4]
  exact and_congr_left' ⟨fun ⟨t, ht⟩ => ⟨-t, by simpa using ht⟩, fun ⟨t, ht⟩ => ⟨-t, ht⟩⟩

lemma copyAdj_of_seqEdge [NeZero ℓ] (hℓ : 2 ≤ ℓ) {f : (cycleGraph ℓ).Copy G} {a b : V}
    (h : SeqEdge (seq f) a b) : CopyAdj f a b := by
  obtain ⟨t, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩ := h
  · exact ⟨_, _, cyc_adj hℓ t, ha, hb⟩
  · exact (show CopyAdj f b a from ⟨_, _, cyc_adj hℓ t, hb, ha⟩).symm

lemma fits_of_fitsSeq [NeZero ℓ] (hℓ : 2 ≤ ℓ) {f : (cycleGraph ℓ).Copy G}
    (h : FitsSeq D (seq f) u v) : D.Fits f u v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, copyAdj_of_seqEdge hℓ h2, copyAdj_of_seqEdge hℓ h3, fun y => ?_⟩
  rw [← h4, ← range_seq f]
  rfl

end FitsSeq

section Map

variable {VH VF V W : Type*} {H : SimpleGraph VH} {F : SimpleGraph VF} {G : SimpleGraph V}

/-- The copy of `G` in `G.map e`. -/
abbrev mapCopy (e : V ↪ W) (G : SimpleGraph V) : G.Copy (G.map e) := (Embedding.map e G).toCopy

@[simp] lemma mapCopy_apply (e : V ↪ W) (v : V) : mapCopy e G v = e v := rfl

/-- Transport of the data `φA, φB` along a vertex embedding. -/
def LBData.map (D : LBData H F G) (e : V ↪ W) : LBData H F (G.map e) where
  φA := (mapCopy e G).comp D.φA
  φB := (mapCopy e G).comp D.φB
  disjoint a b h := D.disjoint a b (e.injective (by simpa using h))

@[simp] lemma LBData.map_φA (D : LBData H F G) (e : V ↪ W) (a : VF) :
    (D.map e).φA a = e (D.φA a) := rfl

@[simp] lemma LBData.map_φB (D : LBData H F G) (e : V ↪ W) (a : VF) :
    (D.map e).φB a = e (D.φB a) := rfl

lemma copyAdj_map {e : V ↪ W} {g : H.Copy G} {x y : V} (h : CopyAdj g x y) :
    CopyAdj ((mapCopy e G).comp g) (e x) (e y) := by
  obtain ⟨a, b, hab, rfl, rfl⟩ := h
  exact ⟨a, b, hab, rfl, rfl⟩

lemma LBData.fits_map (D : LBData H F G) (e : V ↪ W) {g : H.Copy G} {u v : VF}
    (h : D.Fits g u v) : (D.map e).Fits ((mapCopy e G).comp g) u v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, copyAdj_map h2, copyAdj_map h3, fun y => ?_⟩
  by_cases hy : ∃ x, e x = y
  · obtain ⟨x, rfl⟩ := hy
    have hx := h4 x
    simp only [Set.mem_range, Copy.coe_comp, Function.comp_apply, mapCopy_apply,
      LBData.map_φA, LBData.map_φB, e.injective.eq_iff] at hx ⊢
    exact hx
  · push Not at hy
    constructor
    · rintro ⟨⟨a, ha⟩, -⟩
      exact absurd ha (hy _)
    · rintro (h | h | h | h) <;> exact absurd h.symm (hy _)

/-- A copy of `H` (without isolated vertices) in `G.map e` comes from a copy in `G`. -/
noncomputable def Copy.pullback (e : V ↪ W) (hH : ∀ a, ∃ b, H.Adj a b)
    (f : H.Copy (G.map e)) : H.Copy G :=
  have mem : ∀ a, ∃ v, e v = f a := fun a => by
    obtain ⟨b, hab⟩ := hH a
    obtain ⟨u', v', -, hu, -⟩ := (map_adj e G _ _).1 (f.toHom.map_adj hab)
    exact ⟨u', hu⟩
  { toHom := ⟨fun a => (mem a).choose, fun {a b} hab => by
      obtain ⟨u', v', huv, hu, hv⟩ := (map_adj e G _ _).1 (f.toHom.map_adj hab)
      have ha : (mem a).choose = u' := e.injective (by rw [(mem a).choose_spec, hu]; rfl)
      have hb : (mem b).choose = v' := e.injective (by rw [(mem b).choose_spec, hv]; rfl)
      change G.Adj (mem a).choose (mem b).choose
      rw [ha, hb]
      exact huv⟩
    injective' := fun a b hab => by
      have := congrArg e hab
      change e (mem a).choose = e (mem b).choose at this
      rw [(mem a).choose_spec, (mem b).choose_spec] at this
      exact f.injective this }

lemma Copy.comp_pullback (e : V ↪ W) (hH : ∀ a, ∃ b, H.Adj a b) (f : H.Copy (G.map e)) :
    (mapCopy e G).comp (Copy.pullback e hH f) = f := by
  ext a
  exact Exists.choose_spec (p := fun v => e v = f a) _

/-- A lower bound graph stays one after relabelling its vertices along an embedding
(e.g. after adding isolated vertices), provided `H` has no isolated vertices. -/
noncomputable def LowerBoundGraph.map (L : LowerBoundGraph H F G) (e : V ↪ W)
    (hH : ∀ a, ∃ b, H.Adj a b) : LowerBoundGraph H F (G.map e) where
  toLBData := L.toLBData.map e
  exists_copy u v h := by
    obtain ⟨f, hf⟩ := L.exists_copy u v h
    exact ⟨_, L.toLBData.fits_map e hf⟩
  fits_of_copy f := by
    obtain ⟨u, v, h⟩ := L.fits_of_copy (Copy.pullback e hH f)
    refine ⟨u, v, ?_⟩
    have := L.toLBData.fits_map e h
    rwa [Copy.comp_pullback] at this

lemma LowerBoundGraph.map_φA (L : LowerBoundGraph H F G) (e : V ↪ W)
    (hH : ∀ a, ∃ b, H.Adj a b) (a : VF) : (L.map e hH).φA a = e (L.φA a) := rfl

/-- Sparsity is preserved by `LowerBoundGraph.map`: the cut does not grow. -/
lemma LowerBoundGraph.isSparse_map [Fintype V] [Fintype W] [DecidableRel G.Adj]
    (L : LowerBoundGraph H F G) (e : V ↪ W) [DecidableRel (G.map e).Adj]
    (hH : ∀ a, ∃ b, H.Adj a b) (inA : V → Bool) (hA : ∀ a, inA (L.φA a) = true)
    (hB : ∀ b, inA (L.φB b) = false) (c : ℕ)
    (hcut : (Finset.univ.filter fun p : V × V =>
      inA p.1 = true ∧ inA p.2 = false ∧ G.Adj p.1 p.2).card ≤ c)
    (δ : ℝ) (hδ : (c : ℝ) ≤ δ * Fintype.card W) : (L.map e hH).IsSparse δ := by
  classical
  let inA' : W → Bool := fun w => if h : ∃ v, e v = w then inA h.choose else true
  have hinA' : ∀ v, inA' (e v) = inA v := by
    intro v
    have h : ∃ v', e v' = e v := ⟨v, rfl⟩
    simp only [inA', h, ↓reduceDIte]
    exact congrArg inA (e.injective h.choose_spec)
  refine ⟨inA', fun a => ?_, fun b => ?_, ?_⟩
  · rw [LowerBoundGraph.map_φA, hinA']
    exact hA a
  · change inA' (e (L.φB b)) = false
    rw [hinA']
    exact hB b
  refine le_trans ?_ hδ
  norm_cast
  refine le_trans ?_ hcut
  rw [← Finset.card_map (e.prodMap e)]
  apply Finset.card_le_card
  intro ⟨w1, w2⟩ hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨h1, h2, hadj⟩ := hw
  obtain ⟨v1, v2, hv, rfl, rfl⟩ := (map_adj e G _ _).1 hadj
  rw [hinA'] at h1 h2
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  exact ⟨v1, v2, ⟨h1, h2, hv⟩, rfl⟩

end Map

end Podc.CongestedCliquePower
