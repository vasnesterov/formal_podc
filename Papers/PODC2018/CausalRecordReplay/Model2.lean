import Papers.PODC2018.CausalRecordReplay.Model

/-!
# Section 6.1: definitions for RnR Model 2 (data races only)

* Definition 6.1: strong write order `SWO(V)` by levels `SWOk`, and `SWO_i(V)` (`SWOi`);
* Definition 6.2: `A_i(V) = (DRO(V_i) ∪ SWO_i(V) ∪ PO|Obs i)⁺` (`Arel`);
* Observation 6.3 (`obs_6_3`): for a write `w` of `i`, `(x, w) ∈ A_i(V) ↔ (x, w) ∈ SWO(V)`;
* Definition 6.4: the relation `C_i(V, o₁, w₂)` by levels (`Ck`, `Crel`), with a flag `d`:
  `d = true` adds the requirement `w₃ ≠ w₄` that the paper's proofs use ("`w³ ≠ w⁴_1`, by
  Definition 6.4", proof of Lemma C.1(a)) but the definition does not state; with `d = false` the
  definition is taken literally (see `Counterexamples.lean`);
* Definition 6.5: `B_i(V)` (`B2`), and the record of Theorem 6.6 (`rec2`):
  `R_i = Â_i(V) \ (SWO_i(V) ∪ PO ∪ B_i(V))`.
-/

namespace Podc.CausalRecordReplay

open Relation

variable {P Op X : Type*} (π : Program P Op X)

namespace Program

/-- Definition 6.1, by levels: `SWOk 0 = ∅` and `(w₁, w₂) ∈ SWOk (k+1)` iff both are writes and
`(w₁, w₂) ∈ (DRO(V_j) ∪ SWOk k ∪ PO|Obs j)⁺` for the process `j` of `w₂`. (`SWOk (k+1)` is the
paper's `SWO^{k+1}`, `SWO^1` being the base case.) -/
def SWOk (V : P → Op → Op → Prop) : ℕ → Op → Op → Prop
  | 0 => fun _ _ => False
  | k + 1 => fun a b => π.IsWrite a ∧ π.IsWrite b ∧
      TransGen (fun x y => π.DRO (V (π.proc b)) x y ∨ SWOk V k x y ∨ π.poOn (π.proc b) x y) a b

/-- Definition 6.1: the strong write order `SWO(V) = ⋃ₖ SWOᵏ(V)`. -/
def SWO (V : P → Op → Op → Prop) (a b : Op) : Prop := ∃ k, π.SWOk V k a b

/-- Definition 6.1: `SWO_i(V)`: the `SWO(V)` pairs whose second write is not by `i`. -/
def SWOi (V : P → Op → Op → Prop) (i : P) (a b : Op) : Prop := π.SWO V a b ∧ π.proc b ≠ i

/-- The generating relation of `A_i(V)`. -/
def Agen (V : P → Op → Op → Prop) (i : P) (a b : Op) : Prop :=
  π.DRO (V i) a b ∨ π.SWOi V i a b ∨ π.poOn i a b

/-- Definition 6.2: `A_i(V) = (DRO(V_i) ∪ SWO_i(V) ∪ PO|Obs i)⁺`. -/
def Arel (V : P → Op → Op → Prop) (i : P) : Op → Op → Prop := TransGen (π.Agen V i)

/-- Definition 6.4, by levels (`Ck … 0` is the paper's `C¹_i`). The flag `d` requires `w₃ ≠ w₄`. -/
def Ck (d : Bool) (V : P → Op → Op → Prop) (i : P) (o₁ w₂ : Op) : ℕ → Op → Op → Prop
  | 0 => fun w₃ w₄ => π.IsWrite w₃ ∧ π.IsWrite w₄ ∧ π.proc w₄ = i ∧ (d → w₃ ≠ w₄) ∧
      ReflGen (π.Arel V i) o₁ w₄ ∧ ReflGen (π.Arel V i) w₃ w₂
  | k + 1 => fun w₃ w₄ => π.IsWrite w₃ ∧ π.IsWrite w₄ ∧ (d → w₃ ≠ w₄) ∧
      ∃ w₅ w₆, Ck d V i o₁ w₂ k w₅ w₆ ∧
        ReflTransGen (fun x y => π.Arel V (π.proc w₄) x y ∨ Ck d V i o₁ w₂ k x y) w₃ w₅ ∧
        ReflGen (π.Arel V (π.proc w₄)) w₆ w₄

/-- Definition 6.4: `C_i(V, o₁, w₂) = ⋃ₖ Cᵏ_i(V, o₁, w₂)`. -/
def Crel (d : Bool) (V : P → Op → Op → Prop) (i : P) (o₁ w₂ : Op) (a b : Op) : Prop :=
  ∃ k, π.Ck d V i o₁ w₂ k a b

/-- A relation has a cycle. -/
def HasCycle (r : Op → Op → Prop) : Prop := ∃ x, TransGen r x x

/-- Definition 6.5: `(o₁, w₂) ∈ B_i(V)`: same variable, `w₂` a write, `(o₁, w₂) ∈ DRO(V_i)`, and for
some process `m`, `A_m(V) ∪ C_i(V, o₁, w₂)` has a cycle (`m ≠ i`), or
`(A_i(V) \ {(o₁, w₂)}) ∪ C_i(V, o₁, w₂)` has a cycle (`m = i`). -/
def B2 (d : Bool) (V : P → Op → Op → Prop) (i : P) (o₁ w₂ : Op) : Prop :=
  π.var o₁ = π.var w₂ ∧ π.IsWrite w₂ ∧ π.DRO (V i) o₁ w₂ ∧
    ∃ m, (m ≠ i ∧ HasCycle (fun x y => π.Arel V m x y ∨ π.Crel d V i o₁ w₂ x y)) ∨
      (m = i ∧ HasCycle (fun x y => (π.Arel V i x y ∧ ¬ (x = o₁ ∧ y = w₂)) ∨
        π.Crel d V i o₁ w₂ x y))

/-- The record of Theorem 6.6: `R_i = Â_i(V) \ (SWO_i(V) ∪ PO ∪ B_i(V))`. -/
def rec2 (d : Bool) (V : P → Op → Op → Prop) (i : P) (a b : Op) : Prop :=
  Cov (π.Arel V i) a b ∧ ¬ π.SWOi V i a b ∧ ¬ π.po a b ∧ ¬ π.B2 d V i a b

/-! ### Basic properties for strongly causal views -/

variable {π}
variable {V : P → Op → Op → Prop}

theorem SWOk_write {k : ℕ} {a b : Op} (h : π.SWOk V k a b) : π.IsWrite a ∧ π.IsWrite b := by
  cases k with
  | zero => exact h.elim
  | succ k => exact ⟨h.1, h.2.1⟩

theorem SWO_write {a b : Op} (h : π.SWO V a b) : π.IsWrite a ∧ π.IsWrite b :=
  let ⟨_, h⟩ := h; SWOk_write h

theorem SWOk_mono {k : ℕ} {a b : Op} (h : π.SWOk V k a b) : π.SWOk V (k + 1) a b := by
  induction k generalizing a b with
  | zero => exact h.elim
  | succ k ih =>
    refine ⟨h.1, h.2.1, ?_⟩
    refine transGen_mono' (fun x y hxy => ?_) h.2.2
    rcases hxy with hxy | hxy | hxy
    · exact Or.inl hxy
    · exact Or.inr (Or.inl (ih hxy))
    · exact Or.inr (Or.inr hxy)

theorem SWOk_mono_le {k l : ℕ} (hkl : k ≤ l) {a b : Op} (h : π.SWOk V k a b) :
    π.SWOk V l a b := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact SWOk_mono ih

/-- The strong write order is contained in the strong causal order. -/
theorem SWO_sub_SCO (hV : π.StronglyCausal V) {a b : Op} (h : π.SWO V a b) : π.SCO V a b := by
  obtain ⟨k, h⟩ := h
  induction k generalizing a b with
  | zero => exact h.elim
  | succ k ih =>
    refine ⟨h.1, h.2.1, ?_⟩
    obtain ⟨-, -, hp⟩ := h
    generalize π.proc b = j at hp
    have hT := hV.total j
    have step : ∀ x y, (π.DRO (V j) x y ∨ π.SWOk V k x y ∨ π.poOn j x y) → V j x y := by
      intro x y hxy
      rcases hxy with hxy | hxy | hxy
      · exact hxy.1
      · exact hV.sco _ (ih hxy)
      · exact hV.po _ hxy.1 hxy.2.1 hxy.2.2
    exact TransGen.trans_induction_on hp (fun h => step _ _ h) (fun _ _ h1 h2 => hT.trans h1 h2)

theorem SWO_view (hV : π.StronglyCausal V) (j : P) {a b : Op} (h : π.SWO V a b) : V j a b :=
  hV.sco j (SWO_sub_SCO hV h)

theorem Agen_view (hV : π.StronglyCausal V) {i : P} {a b : Op} (h : π.Agen V i a b) : V i a b := by
  rcases h with h | h | h
  · exact h.1
  · exact SWO_view hV i h.1
  · exact hV.po i h.1 h.2.1 h.2.2

/-- `A_i(V) ⊆ V_i`. -/
theorem Arel_view (hV : π.StronglyCausal V) {i : P} {a b : Op} (h : π.Arel V i a b) : V i a b := by
  induction h with
  | single h => exact Agen_view hV h
  | tail _ h ih => exact (hV.total i).trans ih (Agen_view hV h)

theorem Arel_strictPO (hV : π.StronglyCausal V) (i : P) : IsStrictPO (π.Arel V i) :=
  ⟨fun a h => (hV.total i).irrefl a (Arel_view hV h), fun h1 h2 => TransGen.trans h1 h2⟩

theorem Arel_trans {i : P} {a b c : Op} (h1 : π.Arel V i a b) (h2 : π.Arel V i b c) :
    π.Arel V i a c := TransGen.trans h1 h2

theorem Arel_obs (hV : π.StronglyCausal V) {i : P} {a b : Op} (h : π.Arel V i a b) :
    π.Obs i a ∧ π.Obs i b := (hV.total i).supp (Arel_view hV h)

theorem Arel_of_dro {i : P} {a b : Op} (h : π.DRO (V i) a b) : π.Arel V i a b :=
  TransGen.single (Or.inl h)

theorem Arel_of_SWOi {i : P} {a b : Op} (h : π.SWOi V i a b) : π.Arel V i a b :=
  TransGen.single (Or.inr (Or.inl h))

theorem Arel_of_po {i : P} {a b : Op} (h : π.po a b) (ha : π.Obs i a) (hb : π.Obs i b) :
    π.Arel V i a b :=
  TransGen.single (Or.inr (Or.inr ⟨h, ha, hb⟩))

/-- Every level of `SWO` is contained in every `A_i`. -/
theorem SWOk_sub_Arel (k : ℕ) : ∀ (i : P) {a b : Op}, π.SWOk V k a b → π.Arel V i a b := by
  induction k with
  | zero => intro i a b h; exact h.elim
  | succ k ih =>
    intro i a b h
    by_cases hb : π.proc b = i
    · have hpath := h.2.2
      rw [hb] at hpath
      refine TransGen.trans_induction_on hpath (fun hxy => ?_) (fun _ _ h1 h2 => TransGen.trans h1 h2)
      rcases hxy with hxy | hxy | hxy
      · exact Arel_of_dro hxy
      · exact ih i hxy
      · exact Arel_of_po hxy.1 hxy.2.1 hxy.2.2
    · exact Arel_of_SWOi ⟨⟨k + 1, h⟩, hb⟩

/-- `SWO(V) ⊆ A_i(V)` for every `i` (remark after Observation 6.3). -/
theorem SWO_sub_Arel (i : P) {a b : Op} (h : π.SWO V a b) : π.Arel V i a b :=
  let ⟨k, h⟩ := h; SWOk_sub_Arel k i h

/-- A path of the generators of `A_i` lies in one level `SWOk` (finite unions). -/
theorem Arel_level {i : P} {a b : Op} (h : π.Arel V i a b) :
    ∃ k, TransGen (fun x y => π.DRO (V i) x y ∨ π.SWOk V k x y ∨ π.poOn i x y) a b := by
  induction h with
  | single hxy =>
    rcases hxy with hxy | hxy | hxy
    · exact ⟨0, TransGen.single (Or.inl hxy)⟩
    · obtain ⟨k, hk⟩ := hxy.1
      exact ⟨k, TransGen.single (Or.inr (Or.inl hk))⟩
    · exact ⟨0, TransGen.single (Or.inr (Or.inr hxy))⟩
  | @tail x y _ hxy ih =>
    obtain ⟨k, hk⟩ := ih
    have lift : ∀ l, k ≤ l → TransGen (fun x y => π.DRO (V i) x y ∨ π.SWOk V k x y ∨
        π.poOn i x y) a x → TransGen (fun x y => π.DRO (V i) x y ∨ π.SWOk V l x y ∨
        π.poOn i x y) a x := fun l hl h =>
      transGen_mono' (fun _ _ h => by
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (SWOk_mono_le hl h))
        · exact Or.inr (Or.inr h)) h
    rcases hxy with hxy | hxy | hxy
    · exact ⟨k, TransGen.tail hk (Or.inl hxy)⟩
    · obtain ⟨l, hl⟩ := hxy.1
      exact ⟨max k l, TransGen.tail (lift _ (le_max_left _ _) hk)
        (Or.inr (Or.inl (SWOk_mono_le (le_max_right _ _) hl)))⟩
    · exact ⟨k, TransGen.tail hk (Or.inr (Or.inr hxy))⟩

/-- **Observation 6.3.** For a write `w₁` and a write `w₂` of `i`:
`(w₁, w₂) ∈ A_i(V) ↔ (w₁, w₂) ∈ SWO(V)`. -/
theorem obs_6_3 {i : P} {a b : Op} (ha : π.IsWrite a) (hb : π.IsWrite b) (hbi : π.proc b = i) :
    π.Arel V i a b ↔ π.SWO V a b := by
  refine ⟨fun h => ?_, SWO_sub_Arel i⟩
  obtain ⟨k, hk⟩ := Arel_level h
  exact ⟨k + 1, ha, hb, hbi ▸ hk⟩

/-- `SWO(V)` is transitive. -/
theorem SWO_trans {a b c : Op} (h1 : π.SWO V a b) (h2 : π.SWO V b c) : π.SWO V a c :=
  (obs_6_3 (SWO_write h1).1 (SWO_write h2).2 rfl).1
    (Arel_trans (SWO_sub_Arel _ h1) (SWO_sub_Arel _ h2))

/-- `SWO(V)` is a strict partial order for strongly causal views. -/
theorem SWO_strictPO (hV : π.StronglyCausal V) : IsStrictPO (π.SWO V) :=
  ⟨fun a h => (hV.total (π.proc a)).irrefl a (SWO_view hV _ h), fun h1 h2 => SWO_trans h1 h2⟩

/-- `A_j(V)` pairs ending at a write of `j` from a write are `SWO(V)` pairs. -/
theorem SWO_of_Arel_write {j : P} {a b : Op} (h : π.Arel V j a b) (ha : π.IsWrite a)
    (hb : π.IsWrite b) (hbj : π.proc b = j) : π.SWO V a b :=
  (obs_6_3 ha hb hbj).1 h

/-- Program order between two writes is in `SWO(V)`. -/
theorem SWO_of_po {a b : Op} (h : π.po a b) (ha : π.IsWrite a)
    (hb : π.IsWrite b) : π.SWO V a b :=
  SWO_of_Arel_write (j := π.proc b) (Arel_of_po h (π.write_obs ha _) (π.write_obs hb _)) ha hb rfl

/-- A cover of `A_i(V)` is a generator. -/
theorem Agen_of_cov {i : P} {a b : Op} (h : Cov (π.Arel V i) a b) : π.Agen V i a b :=
  cov_transGen h

/-- The record of Theorem 6.6 is a Model-2 record: `R_i ⊆ DRO(V_i)`. -/
theorem rec2_isRecord2 (d : Bool) (V : P → Op → Op → Prop) : π.IsRecord2 V (π.rec2 d V) := by
  intro i a b h
  rcases Agen_of_cov h.1 with h' | h' | h'
  · exact h'
  · exact absurd h' h.2.1
  · exact absurd h'.1 h.2.2.1

/-! ### `C` and `B` -/

/-- The levels of `C` are monotone. -/
theorem Ck_mono {d : Bool} {i : P} {o₁ w₂ : Op} {k : ℕ} {a b : Op}
    (h : π.Ck d V i o₁ w₂ k a b) : π.Ck d V i o₁ w₂ (k + 1) a b := by
  refine ⟨?_, ?_, ?_, a, b, h, ReflTransGen.refl, ReflGen.refl⟩
  · cases k <;> exact h.1
  · cases k <;> exact h.2.1
  · cases k
    · exact h.2.2.2.1
    · exact h.2.2.1

theorem Ck_mono_le {d : Bool} {i : P} {o₁ w₂ : Op} {k l : ℕ} (hkl : k ≤ l) {a b : Op}
    (h : π.Ck d V i o₁ w₂ k a b) : π.Ck d V i o₁ w₂ l a b := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact Ck_mono ih

theorem Ck_write {d : Bool} {i : P} {o₁ w₂ : Op} {k : ℕ} {a b : Op}
    (h : π.Ck d V i o₁ w₂ k a b) : π.IsWrite a ∧ π.IsWrite b := by
  cases k <;> exact ⟨h.1, h.2.1⟩

theorem Ck_ne {i : P} {o₁ w₂ : Op} {k : ℕ} {a b : Op}
    (h : π.Ck true V i o₁ w₂ k a b) : a ≠ b := by
  cases k
  · exact h.2.2.2.1 rfl
  · exact h.2.2.1 rfl

/-- A path of `A_j ∪ C` lies in `A_j ∪ Cᵏ` for some level `k`. -/
theorem Crel_path_level {d : Bool} {i j : P} {o₁ w₂ : Op} {a b : Op}
    (h : ReflTransGen (fun x y => π.Arel V j x y ∨ π.Crel d V i o₁ w₂ x y) a b) :
    ∃ k, ReflTransGen (fun x y => π.Arel V j x y ∨ π.Ck d V i o₁ w₂ k x y) a b := by
  induction h with
  | refl => exact ⟨0, ReflTransGen.refl⟩
  | @tail x y _ hxy ih =>
    obtain ⟨k, hk⟩ := ih
    have lift : ∀ l, k ≤ l → ReflTransGen (fun x y => π.Arel V j x y ∨
        π.Ck d V i o₁ w₂ k x y) a x → ReflTransGen (fun x y => π.Arel V j x y ∨
        π.Ck d V i o₁ w₂ l x y) a x := fun l hl h =>
      reflTransGen_mono' (fun _ _ h => by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Ck_mono_le hl h)) h
    rcases hxy with hxy | ⟨l, hl⟩
    · exact ⟨k, ReflTransGen.tail hk (Or.inl hxy)⟩
    · exact ⟨max k l, ReflTransGen.tail (lift _ (le_max_left _ _) hk)
        (Or.inr (Ck_mono_le (le_max_right _ _) hl))⟩

/-- The closure rule of Definition 6.4 for the union `C`: if `w₃ ≤ w₅` in `(A_j ∪ C)⁺`,
`(w₅, w₆) ∈ C` and `w₆ ≤ w₄` in `A_j` with `w₄` a write of `j`, then `(w₃, w₄) ∈ C`. -/
theorem Crel_rule {i : P} {o₁ w₂ : Op} {w₃ w₄ w₅ w₆ : Op} (h3 : π.IsWrite w₃)
    (h4 : π.IsWrite w₄) (hne : w₃ ≠ w₄) (h56 : π.Crel true V i o₁ w₂ w₅ w₆)
    (hp : ReflTransGen (fun x y => π.Arel V (π.proc w₄) x y ∨ π.Crel true V i o₁ w₂ x y) w₃ w₅)
    (h64 : ReflGen (π.Arel V (π.proc w₄)) w₆ w₄) : π.Crel true V i o₁ w₂ w₃ w₄ := by
  obtain ⟨k, hk⟩ := Crel_path_level hp
  obtain ⟨l, hl⟩ := h56
  refine ⟨max k l + 1, h3, h4, fun _ => hne, w₅, w₆, Ck_mono_le (le_max_right _ _) hl, ?_, h64⟩
  exact reflTransGen_mono' (fun _ _ h => by
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Ck_mono_le (le_max_left _ _) h)) hk

/-- The cycle condition of Definition 6.5 needs a nonempty `C`: a nonempty `C` has an element at
level `0`, whose second component is a write `w` of `i` above `o₁` in `A_i`. -/
theorem exists_write_of_Ck {d : Bool} {i : P} {o₁ w₂ : Op} {k : ℕ} {a b : Op}
    (h : π.Ck d V i o₁ w₂ k a b) :
    ∃ w, π.IsWrite w ∧ π.proc w = i ∧ ReflGen (π.Arel V i) o₁ w := by
  induction k generalizing a b with
  | zero => exact ⟨b, h.2.1, h.2.2.1, h.2.2.2.2.1⟩
  | succ k ih =>
    obtain ⟨-, -, -, w₅, w₆, h56, -⟩ := h
    exact ih h56

/-- `B_i(V)` pairs have a nonempty `C`, hence a write of `i` above `o₁` in `A_i(V)`. -/
theorem exists_write_of_B2 (hV : π.StronglyCausal V) {d : Bool} {i : P} {o₁ w₂ : Op}
    (h : π.B2 d V i o₁ w₂) : ∃ w, π.IsWrite w ∧ π.proc w = i ∧ ReflGen (π.Arel V i) o₁ w := by
  obtain ⟨-, -, -, m, hm⟩ := h
  -- if `C` were empty, the cycle would lie in the strict order `A_m`
  by_contra hno
  have hC : ∀ x y, ¬ π.Crel d V i o₁ w₂ x y := fun x y ⟨k, hk⟩ => hno (exists_write_of_Ck hk)
  rcases hm with ⟨-, x, hx⟩ | ⟨-, x, hx⟩
  · have : π.Arel V m x x := of_transGen_of_trans (Arel_strictPO hV m).transitive
      (transGen_mono' (fun _ _ h => h.resolve_right (hC _ _)) hx)
    exact (Arel_strictPO hV m).irrefl x this
  · have : π.Arel V i x x := of_transGen_of_trans (Arel_strictPO hV i).transitive
      (transGen_mono' (fun _ _ h => (h.resolve_right (hC _ _)).1) hx)
    exact (Arel_strictPO hV i).irrefl x this

/-- `u` is the program-order-least write of `i` above `o` in `A_i(V)` (Observation B.1's `wᵢ^min`). -/
def IsWmin (V : P → Op → Op → Prop) (i : P) (o u : Op) : Prop :=
  π.IsWrite u ∧ π.proc u = i ∧ ReflGen (π.Arel V i) o u ∧
    ∀ w, π.IsWrite w → π.proc w = i → ReflGen (π.Arel V i) o w → ReflGen π.po u w

theorem exists_wmin [Finite Op] {i : P} {o : Op}
    (h : ∃ w, π.IsWrite w ∧ π.proc w = i ∧ ReflGen (π.Arel V i) o w) : ∃ u, π.IsWmin V i o u := by
  have hpo : IsStrictPO π.po := ⟨π.po_irrefl, π.po_trans⟩
  obtain ⟨u, ⟨hu1, hu2, hu3⟩, hmin⟩ :=
    hpo.wellFounded.has_min {w | π.IsWrite w ∧ π.proc w = i ∧ ReflGen (π.Arel V i) o w} h
  refine ⟨u, hu1, hu2, hu3, fun w h1 h2 h3 => ?_⟩
  by_cases hwu : u = w
  · exact hwu ▸ ReflGen.refl
  rcases π.po_total (hu2.trans h2.symm) hwu with h | h
  · exact ReflGen.single h
  · exact absurd h (hmin w ⟨h1, h2, h3⟩)

/-- **Observation B.3** (generalized to an arbitrary `o₁`): every second component `t` of a pair of
`C_i(V, o₁, w₂)` is above `wᵢ^min` in `SWO(V)`. -/
theorem wmin_le_Ck_target (hV : π.StronglyCausal V) {d : Bool} {i : P} {o₁ w₂ u : Op}
    (hu : π.IsWmin V i o₁ u) {k : ℕ} {a t : Op} (h : π.Ck d V i o₁ w₂ k a t) :
    ReflGen (π.SWO V) u t := by
  induction k generalizing a t with
  | zero =>
    obtain ⟨-, ht, hti, -, hot, -⟩ := h
    rcases hu.2.2.2 t ht hti hot with _ | hpo
    · exact ReflGen.refl
    · exact ReflGen.single (SWO_of_po hpo hu.1 ht)
  | succ k ih =>
    obtain ⟨-, ht, -, w₅, w₆, h56, -, h6t⟩ := h
    have h6 := ih h56
    rcases h6t with _ | h6t
    · exact h6
    · exact reflGen_trans (SWO_strictPO hV).transitive h6
          (ReflGen.single (SWO_of_Arel_write h6t (Ck_write h56).2 ht rfl))

theorem wmin_le_Crel_target (hV : π.StronglyCausal V) {d : Bool} {i : P} {o₁ w₂ u : Op}
    (hu : π.IsWmin V i o₁ u) {a t : Op} (h : π.Crel d V i o₁ w₂ a t) : ReflGen (π.SWO V) u t :=
  let ⟨_, hk⟩ := h; wmin_le_Ck_target hV hu hk

end Program

end Podc.CausalRecordReplay
