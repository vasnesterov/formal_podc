import Papers.PODC2018.CausalRecordReplay.Offline1

/-!
# Section 5.2: optimal online record for RnR Model 1 under strong causal consistency

In the online setting, process `i` decides whether to record an edge `(o₁, o₂)` of `V_i` at the
moment it observes `o₂`, using only what it knows at that moment. The paper bounds this knowledge:
"if process `i` is aware that `(o₁, o₂) ∈ V_j` (`j ≠ i`) then process `i` must have already observed
some `o₃ ∈ (∗, j, ∗, ∗)` with `o₁ <_{V_j} o₂ ≤_{V_j} o₃`". We give process `i` the *maximal*
knowledge allowed by this bound (`SameKnow`): its own view up to `o₂`, and for every write `w` of
another process `m` that `i` has observed so far, the view `V_m` up to `w`. A record scheme
`Rec : views → record` is *online* (`IsOnline`) if `Rec V i o₁ o₂` depends only on this knowledge
at `o₂`. Maximal knowledge makes the impossibility Theorem 5.6 as strong as possible.

* `rec1on`: `R_i = V̂_i \ (SCO_i(V) ∪ PO)`;
* Theorem 5.5 (`theorem_5_5`): `rec1on` is online and yields good records;
* Theorem 5.6 (`theorem_5_6`): every online scheme that yields good records contains `rec1on`
  (`rec1on_least_online`).

The proof of Theorem 5.6 builds, for an edge `(w₁, w₂) ∈ B_i(V)`, an alternative strongly causal
`W` that is indistinguishable from `V` for process `i` when it observes `w₂` but in which
`(w₁, w₂) ∉ B_i(W)`; Theorem 5.4 applied to `W` then forces the edge into the record.
-/

namespace Podc.CausalRecordReplay

open Relation

section Generic

variable {α : Type*}

/-- `s` agrees with `r` on the `r`-prefix up to `o`: the `r`-predecessors of every `b ≤ᵣ o` are
the same in `r` and `s`. -/
def PrefixAgree (r s : α → α → Prop) (o : α) : Prop := ∀ a b, ReflGen r b o → (r a b ↔ s a b)

/-- Covers ending at `b` are determined by the prefix up to `b`. -/
theorem PrefixAgree.cov {r s : α → α → Prop} {a b : α} (h : PrefixAgree r s b) (hab : Cov r a b) :
    Cov s a b := by
  refine ⟨(h a b ReflGen.refl).1 hab.1, fun c hac hcb => ?_⟩
  have hcb' : r c b := (h c b ReflGen.refl).2 hcb
  exact hab.2 c ((h a c (ReflGen.single hcb')).2 hac) hcb'

theorem PrefixAgree.cov_iff {r s : α → α → Prop} {a b : α} (h : PrefixAgree r s b) :
    Cov r a b ↔ Cov s a b := by
  refine ⟨h.cov, fun hab => ⟨(h a b ReflGen.refl).2 hab.1, fun c hac hcb => ?_⟩⟩
  exact hab.2 c ((h a c (ReflGen.single hcb)).1 hac) ((h c b ReflGen.refl).1 hcb)

/-- Every strict partial order extends to a strict total order (finite or not). -/
theorem strictPO_exists_linearExt {r : α → α → Prop} (hr : IsStrictPO r) :
    ∃ g : α → α → Prop, IsStrictTotalOn (fun _ => True) g ∧ ∀ a b, r a b → g a b := by
  have : IsPartialOrder α (ReflGen r) :=
    { refl := fun _ => ReflGen.refl
      trans := fun _ _ _ => reflGen_trans hr.transitive
      antisymm := fun a b h1 h2 => by
        rcases h1 with _ | h1
        · rfl
        rcases h2 with _ | h2
        · rfl
        exact absurd (hr.trans h1 h2) (hr.irrefl a) }
  obtain ⟨s, hs, hle⟩ := extend_partialOrder (ReflGen r)
  have := hs
  refine ⟨fun a b => s a b ∧ a ≠ b, ⟨fun _ => ⟨trivial, trivial⟩, fun a h => h.2 rfl, ?_, ?_⟩, ?_⟩
  · rintro a b c ⟨hab, nab⟩ ⟨hbc, -⟩
    refine ⟨trans_of s hab hbc, ?_⟩
    rintro rfl
    exact nab (antisymm_of s hab hbc)
  · intro a b _ _ hne
    rcases total_of s a b with h | h
    · exact Or.inl ⟨h, hne⟩
    · exact Or.inr ⟨h, hne.symm⟩
  · intro a b h
    exact ⟨hle _ _ (ReflGen.single h), fun e => hr.irrefl a (e ▸ h)⟩

/-- Concatenation of orders: the elements of `K` first, ordered by `r`, then the rest of `S`,
ordered by `g`. -/
def concatOrd (K S : α → Prop) (r g : α → α → Prop) (a b : α) : Prop :=
  (K a ∧ K b ∧ r a b) ∨ (K a ∧ S b ∧ ¬ K b) ∨ (S a ∧ S b ∧ ¬ K a ∧ ¬ K b ∧ g a b)

theorem concatOrd_total {K S : α → Prop} {r g : α → α → Prop} (hr : IsStrictTotalOn S r)
    (hg : IsStrictTotalOn (fun _ => True) g) (hK : ∀ a, K a → S a) :
    IsStrictTotalOn S (concatOrd K S r g) := by
  refine ⟨fun {a b} h => ?_, fun a h => ?_, fun {a b c} hab hbc => ?_, fun {a b} ha hb hne => ?_⟩
  · rcases h with ⟨ha, hb, -⟩ | ⟨ha, hb, -⟩ | ⟨ha, hb, -⟩
    · exact ⟨hK a ha, hK b hb⟩
    · exact ⟨hK a ha, hb⟩
    · exact ⟨ha, hb⟩
  · rcases h with ⟨-, -, h⟩ | ⟨h1, -, h2⟩ | ⟨-, -, -, -, h⟩
    · exact hr.irrefl a h
    · exact h2 h1
    · exact hg.irrefl a h
  · rcases hab with ⟨ha, hb, hab⟩ | ⟨ha, hb, nb⟩ | ⟨ha, hb, na, nb, hab⟩ <;>
      rcases hbc with ⟨hb', hc, hbc⟩ | ⟨hb', hc, nc⟩ | ⟨hb', hc, nb', nc, hbc⟩
    · exact Or.inl ⟨ha, hc, hr.trans hab hbc⟩
    · exact Or.inr (Or.inl ⟨ha, hc, nc⟩)
    · exact absurd hb nb'
    · exact absurd hb' nb
    · exact absurd hb' nb
    · exact Or.inr (Or.inl ⟨ha, hc, nc⟩)
    · exact absurd hb' nb
    · exact absurd hb' nb
    · exact Or.inr (Or.inr ⟨ha, hc, na, nc, hg.trans hab hbc⟩)
  · by_cases ka : K a <;> by_cases kb : K b
    · rcases hr.total ha hb hne with h | h
      · exact Or.inl (Or.inl ⟨ka, kb, h⟩)
      · exact Or.inr (Or.inl ⟨kb, ka, h⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨ka, hb, kb⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨kb, ha, ka⟩))
    · rcases hg.total trivial trivial hne with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨ha, hb, ka, kb, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hb, ha, kb, ka, h⟩))

/-- Below an element of `K`, the concatenation is `r` restricted to `K`. -/
theorem concatOrd_of_mem {K S : α → Prop} {r g : α → α → Prop} {a b : α} (hb : K b) :
    concatOrd K S r g a b ↔ K a ∧ r a b := by
  constructor
  · rintro (⟨ha, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, -, h, -⟩)
    · exact ⟨ha, h⟩
    · exact absurd hb h
    · exact absurd hb h
  · rintro ⟨ha, h⟩
    exact Or.inl ⟨ha, hb, h⟩

/-- If `K` contains the `r`-prefix up to `o` and is downward closed for `r`, the concatenation
agrees with `r` on that prefix. -/
theorem concatOrd_prefixAgree {K S : α → Prop} {r g : α → α → Prop} {o : α}
    (hK : ∀ b, ReflGen r b o → K b) (hdown : ∀ a b, K b → r a b → K a) :
    PrefixAgree r (concatOrd K S r g) o := by
  intro a b hb
  rw [concatOrd_of_mem (hK b hb)]
  exact ⟨fun h => ⟨hdown a b (hK b hb) h, h⟩, fun h => h.2⟩

/-- Lexicographic order: elements of `D` first, then `r` inside each part. -/
def lexFirst (D : α → Prop) (r : α → α → Prop) (a b : α) : Prop :=
  (D a ∧ ¬ D b) ∨ ((D a ↔ D b) ∧ r a b)

theorem lexFirst_strictPO {D : α → Prop} {r : α → α → Prop} (hr : IsStrictPO r) :
    IsStrictPO (lexFirst D r) := by
  refine ⟨fun a h => ?_, fun {a b c} hab hbc => ?_⟩
  · rcases h with ⟨h1, h2⟩ | ⟨-, h⟩
    · exact h2 h1
    · exact hr.irrefl a h
  · rcases hab with ⟨ha, nb⟩ | ⟨hab, rab⟩ <;> rcases hbc with ⟨hb, nc⟩ | ⟨hbc, rbc⟩
    · exact absurd hb nb
    · exact Or.inl ⟨ha, fun hc => nb (hbc.2 hc)⟩
    · exact Or.inl ⟨hab.2 hb, nc⟩
    · exact Or.inr ⟨hab.trans hbc, hr.trans rab rbc⟩

/-- Closing a strict partial order `z` on a set `Wr` under a strict partial order `p` that agrees
with `z` on `Wr`: `p ∪ (p^= ∘ z ∘ p^=)` is again a strict partial order. -/
def poClose (p z : α → α → Prop) (a b : α) : Prop :=
  p a b ∨ ∃ x y, ReflGen p a x ∧ z x y ∧ ReflGen p y b

theorem poClose_strictPO {p z : α → α → Prop} {Wr : α → Prop} (hp : IsStrictPO p)
    (hz : IsStrictPO z) (hzW : ∀ a b, z a b → Wr a ∧ Wr b)
    (hpz : ∀ a b, p a b → Wr a → Wr b → z a b) : IsStrictPO (poClose p z) := by
  have hpt : TransRel p := fun _ _ _ => hp.trans
  -- a `p`-step between two elements of `Wr` is a `z`-step
  have key : ∀ y x, ReflGen p y x → z x y → False := by
    intro y x hyx hxy
    rcases hyx with _ | hyx
    · exact hz.irrefl _ hxy
    · exact hz.irrefl _ (hz.trans hxy (hpz _ _ hyx (hzW _ _ hxy).2 (hzW _ _ hxy).1))
  refine ⟨fun a h => ?_, fun {a b c} hab hbc => ?_⟩
  · rcases h with h | ⟨x, y, hax, hxy, hya⟩
    · exact hp.irrefl a h
    · exact key y x (reflGen_trans hpt hya hax) hxy
  · rcases hab with hab | ⟨x, y, hax, hxy, hyb⟩ <;> rcases hbc with hbc | ⟨x', y', hbx, hxy', hyc⟩
    · exact Or.inl (hp.trans hab hbc)
    · exact Or.inr ⟨x', y', ReflGen.single (reflGen_trans_right hpt hab hbx), hxy', hyc⟩
    · exact Or.inr ⟨x, y, hax, hxy, ReflGen.single (reflGen_trans_left hpt hyb hbc)⟩
    · refine Or.inr ⟨x, y', hax, ?_, hyc⟩
      have hyx' := reflGen_trans hpt hyb hbx
      rcases hyx' with _ | hyx'
      · exact hz.trans hxy hxy'
      · exact hz.trans (hz.trans hxy (hpz _ _ hyx' (hzW _ _ hxy).2 (hzW _ _ hxy').1)) hxy'

theorem le_poClose_left {p z : α → α → Prop} {a b : α} (h : p a b) : poClose p z a b := Or.inl h

theorem le_poClose_right {p z : α → α → Prop} {a b : α} (h : z a b) : poClose p z a b :=
  Or.inr ⟨a, b, ReflGen.refl, h, ReflGen.refl⟩

end Generic

variable {P Op X : Type*} (π : Program P Op X)

namespace Program

/-- Process `i` has the same knowledge in the views `V` and `W` when it observes `o`: its own view
up to `o`, and for each write `w` of another process `m` observed by `i` up to `o`, the view of `m`
up to `w`. This is the maximal knowledge allowed by Section 5.2 of the paper. -/
def SameKnow (V W : P → Op → Op → Prop) (i : P) (o : Op) : Prop :=
  PrefixAgree (V i) (W i) o ∧
    ∀ w, π.IsWrite w → π.proc w ≠ i → ReflGen (V i) w o →
      PrefixAgree (V (π.proc w)) (W (π.proc w)) w

/-- A record scheme is *online* (Section 5.2) if the decision to record `(o₁, o₂)` at process `i`
(made when `i` observes `o₂`) depends only on the knowledge of `i` at that time: it is the same for
any two strongly causal executions in which `i` has the same knowledge when observing `o₂`. -/
def IsOnline (Rec : (P → Op → Op → Prop) → P → Op → Op → Prop) : Prop :=
  ∀ V W, π.StronglyCausal V → π.StronglyCausal W → ∀ i o₁ o₂, π.SameKnow V W i o₂ →
    (Rec V i o₁ o₂ ↔ Rec W i o₁ o₂)

/-- The online record of Theorem 5.5: `R_i = V̂_i \ (SCO_i(V) ∪ PO)`. -/
def rec1on (V : P → Op → Op → Prop) (i : P) (a b : Op) : Prop :=
  Cov (V i) a b ∧ ¬ π.SCOi V i a b ∧ ¬ π.po a b

variable {π}

/-- Goodness is monotone in the record. -/
theorem Good1.mono {V R R' : P → Op → Op → Prop} (h : π.Good1 V R)
    (hle : ∀ i a b, R i a b → R' i a b) : π.Good1 V R' :=
  fun ex V' hV' hR' => h ex V' hV' fun i a b hab => hR' i a b (hle i a b hab)

theorem rec1_le_rec1on (V : P → Op → Op → Prop) : ∀ i a b, π.rec1 V i a b → π.rec1on V i a b :=
  fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- `SCO_i(V)`-membership of `(o₁, o₂)` is known to `i` when it observes `o₂`. -/
theorem SameKnow.scoi_iff {V W : P → Op → Op → Prop} {i : P} {o₁ o₂ : Op}
    (h : π.SameKnow V W i o₂) : π.SCOi V i o₁ o₂ ↔ π.SCOi W i o₁ o₂ := by
  by_cases hw : π.IsWrite o₂
  · by_cases hp : π.proc o₂ = i
    · exact ⟨fun h' => absurd hp h'.2, fun h' => absurd hp h'.2⟩
    · have := h.2 o₂ hw hp ReflGen.refl o₁ o₂ ReflGen.refl
      exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨h1, h2, this.1 h3⟩, h4⟩,
        fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨h1, h2, this.2 h3⟩, h4⟩⟩
  · exact ⟨fun h' => absurd h'.1.2.1 hw, fun h' => absurd h'.1.2.1 hw⟩

/-- **Theorem 5.5.** The record `R_i = V̂_i \ (SCO_i(V) ∪ PO)` can be recorded online, and for views
`V` explaining a strongly causally consistent execution it is a good record of `V` (RnR Model 1). -/
theorem theorem_5_5 [Finite Op] :
    π.IsOnline π.rec1on ∧
      ∀ (ex : Execution Op) (V : P → Op → Op → Prop), π.SCCExplains ex V →
        IsRecord1 V (π.rec1on V) ∧ π.Good1 V (π.rec1on V) := by
  refine ⟨fun V W _ _ i o₁ o₂ h => ?_, fun ex V hV => ⟨fun _ _ _ h => h.1.1, ?_⟩⟩
  · unfold rec1on
    rw [h.1.cov_iff, h.scoi_iff]
  · exact (theorem_5_3 hV).mono (rec1_le_rec1on V)

/-! ### The indistinguishable execution for Theorem 5.6 -/

section Construction

variable (π) (V : P → Op → Op → Prop) (i : P) (w₁ w₂ : Op)

/-- What process `m` has observed according to the knowledge of `i` at `w₂`: for `m = i` the prefix
of `V_i` up to `w₂`; for `m ≠ i` the prefix of `V_m` up to the last write of `m` observed by `i`. -/
def knownSet (m : P) (a : Op) : Prop :=
  ∃ w, ReflGen (V i) w w₂ ∧ (m = i ∨ (π.IsWrite w ∧ π.proc w = m)) ∧ ReflGen (V m) a w

/-- The writes observed by `i` up to `w₂`. -/
def knownW (a : Op) : Prop := π.IsWrite a ∧ ReflGen (V i) a w₂

/-- An order on writes: known writes first, `SCO(V)` with `(w₂, w₁)` added. -/
def zW (a b : Op) : Prop :=
  π.IsWrite a ∧ π.IsWrite b ∧ lexFirst (π.knownW V i w₂) (addPair (π.SCO V) w₂ w₁) a b

/-- The alternative views: for each `m`, the known part of `V_m` first, the rest ordered by `G`. -/
def altView (G : Op → Op → Prop) (m : P) : Op → Op → Prop :=
  concatOrd (π.knownSet V i w₂ m) (π.Obs m) (V m) G

variable {π V i w₁ w₂}

section
variable (hV : π.StronglyCausal V) (hw₂ : π.IsWrite w₂)
include hV

theorem knownSet_self_iff {a : Op} : π.knownSet V i w₂ i a ↔ ReflGen (V i) a w₂ := by
  constructor
  · rintro ⟨w, h1, -, h3⟩
    exact reflGen_trans (hV.total i).toStrictPO.transitive h3 h1
  · intro h
    exact ⟨w₂, ReflGen.refl, Or.inl rfl, h⟩

include hw₂ in
theorem knownSet_obs {m : P} {a : Op} (h : π.knownSet V i w₂ m a) : π.Obs m a := by
  obtain ⟨w, h1, h2, h3⟩ := h
  rcases h3 with _ | h3
  · rcases h2 with rfl | ⟨hw, -⟩
    · rcases h1 with _ | h1
      · exact π.write_obs hw₂ _
      · exact ((hV.total _).supp h1).1
    · exact π.write_obs hw _
  · exact ((hV.total m).supp h3).1

theorem knownSet_down {m : P} {a b : Op} (hb : π.knownSet V i w₂ m b) (hab : V m a b) :
    π.knownSet V i w₂ m a := by
  obtain ⟨w, h1, h2, h3⟩ := hb
  exact ⟨w, h1, h2, ReflGen.single (reflGen_trans_right (hV.total m).toStrictPO.transitive hab h3)⟩

/-- A known write of any process has been observed by `i`. -/
theorem knownW_of_knownSet {m : P} {a : Op} (ha : π.IsWrite a) (h : π.knownSet V i w₂ m a) :
    π.knownW V i w₂ a := by
  refine ⟨ha, ?_⟩
  obtain ⟨w, h1, h2, h3⟩ := h
  have hti := (hV.total i).toStrictPO.transitive
  rcases h2 with rfl | ⟨hw, rfl⟩
  · exact reflGen_trans hti h3 h1
  · rcases h3 with _ | h3
    · exact h1
    · exact reflGen_trans hti (ReflGen.single (hV.sco i ⟨ha, hw, h3⟩)) h1

omit hV in
theorem knownSet_of_knownW {a : Op} (h : π.knownW V i w₂ a) :
    π.knownSet V i w₂ (π.proc a) a :=
  ⟨a, h.2, Or.inr ⟨h.1, rfl⟩, ReflGen.refl⟩

theorem knownW_down {a b : Op} (hb : π.knownW V i w₂ b) (hab : π.SCO V a b) :
    π.knownW V i w₂ a :=
  ⟨hab.1, ReflGen.single (reflGen_trans_right (hV.total i).toStrictPO.transitive (hV.sco i hab) hb.2)⟩

end

section
variable (hV : π.StronglyCausal V) (hw₁ : π.IsWrite w₁) (hw₂ : π.IsWrite w₂)
  (hp₁ : π.proc w₁ = i) (hp₂ : π.proc w₂ ≠ i) (hcov : Cov (V i) w₁ w₂)
  (hj : V (π.proc w₂) w₂ w₁)
include hV

include hp₁ hp₂ hj in
theorem zW_strictPO : IsStrictPO (π.zW V i w₁ w₂) := by
  have hne : w₂ ≠ w₁ := fun e => hp₂ (e ▸ hp₁)
  have hns : ¬ π.SCO V w₁ w₂ := fun h => (hV.total _).asymm hj h.2.2
  have hlex := lexFirst_strictPO (D := π.knownW V i w₂) (addPair_strictPO hV.sco_strictPO hne hns)
  refine ⟨fun a h => hlex.irrefl a h.2.2, fun {a b c} hab hbc => ⟨hab.1, hbc.2.1, ?_⟩⟩
  exact hlex.trans hab.2.2 hbc.2.2

theorem zW_sco {a b : Op} (h : π.SCO V a b) : π.zW V i w₁ w₂ a b := by
  refine ⟨h.1, h.2.1, ?_⟩
  by_cases ha : π.knownW V i w₂ a
  · by_cases hb : π.knownW V i w₂ b
    · exact Or.inr ⟨iff_of_true ha hb, Or.inl h⟩
    · exact Or.inl ⟨ha, hb⟩
  · have hb : ¬ π.knownW V i w₂ b := fun hb => ha (knownW_down hV hb h)
    exact Or.inr ⟨iff_of_false ha hb, Or.inl h⟩

omit hV in
include hw₁ hw₂ hcov in
theorem zW_21 : π.zW V i w₁ w₂ w₂ w₁ :=
  ⟨hw₂, hw₁, Or.inr ⟨iff_of_true ⟨hw₂, ReflGen.refl⟩ ⟨hw₁, ReflGen.single hcov.1⟩,
    addPair_self _ _⟩⟩

omit hV in
theorem zW_known {a b : Op} (ha : π.knownW V i w₂ a) (hb : π.IsWrite b)
    (hb' : ¬ π.knownW V i w₂ b) : π.zW V i w₁ w₂ a b :=
  ⟨ha.1, hb, Or.inl ⟨ha, hb'⟩⟩

include hp₁ hp₂ hj in
theorem poClose_zW_strictPO : IsStrictPO (poClose π.po (π.zW V i w₁ w₂)) :=
  poClose_strictPO (Wr := π.IsWrite) ⟨π.po_irrefl, π.po_trans⟩ (zW_strictPO hV hp₁ hp₂ hj)
    (fun _ _ h => ⟨h.1, h.2.1⟩)
    (fun _ _ h ha hb => zW_sco hV ⟨ha, hb, hV.po _ h (π.write_obs ha _) (π.write_obs hb _)⟩)

include hw₂ in
/-- The alternative views are strongly causal. -/
theorem altView_stronglyCausal {G : Op → Op → Prop} (hG : IsStrictTotalOn (fun _ => True) G)
    (hGsco : ∀ a b, π.SCO V a b → G a b) (hGpo : ∀ a b, π.po a b → G a b)
    (hGk : ∀ a b, π.knownW V i w₂ a → π.IsWrite b → ¬ π.knownW V i w₂ b → G a b) :
    π.StronglyCausal (π.altView V i w₂ G) := by
  rw [stronglyCausal_iff]
  intro m
  refine ⟨concatOrd_total (hV.total m) hG (fun a => knownSet_obs hV hw₂), ?_, ?_⟩
  · rintro x y ⟨hx, hy, hxy⟩
    unfold altView at hxy ⊢
    by_cases hyD : π.knownW V i w₂ y
    · rw [concatOrd_of_mem (knownSet_of_knownW hyD)] at hxy
      have hs : π.SCO V x y := ⟨hx, hy, hxy.2⟩
      by_cases hKm : π.knownSet V i w₂ m y
      · rw [concatOrd_of_mem hKm]
        exact ⟨knownSet_down hV hKm (hV.sco m hs), hV.sco m hs⟩
      · by_cases hKmx : π.knownSet V i w₂ m x
        · exact Or.inr (Or.inl ⟨hKmx, π.write_obs hy m, hKm⟩)
        · exact Or.inr (Or.inr ⟨π.write_obs hx m, π.write_obs hy m, hKmx, hKm, hGsco _ _ hs⟩)
    · have hKm : ¬ π.knownSet V i w₂ m y := fun h => hyD (knownW_of_knownSet hV hy h)
      by_cases hKmx : π.knownSet V i w₂ m x
      · exact Or.inr (Or.inl ⟨hKmx, π.write_obs hy m, hKm⟩)
      refine Or.inr (Or.inr ⟨π.write_obs hx m, π.write_obs hy m, hKmx, hKm, ?_⟩)
      by_cases hxD : π.knownW V i w₂ x
      · exact hGk _ _ hxD hy hyD
      rcases hxy with ⟨-, hK, -⟩ | ⟨hK, -, -⟩ | ⟨-, -, -, -, h⟩
      · exact absurd (knownW_of_knownSet hV hy hK) hyD
      · exact absurd (knownW_of_knownSet hV hx hK) hxD
      · exact h
  · rintro x y ⟨hpo, hx, hy⟩
    unfold altView
    by_cases hKm : π.knownSet V i w₂ m y
    · rw [concatOrd_of_mem hKm]
      exact ⟨knownSet_down hV hKm (hV.po m hpo hx hy), hV.po m hpo hx hy⟩
    · by_cases hKmx : π.knownSet V i w₂ m x
      · exact Or.inr (Or.inl ⟨hKmx, hy, hKm⟩)
      · exact Or.inr (Or.inr ⟨hx, hy, hKmx, hKm, hGpo _ _ hpo⟩)

/-- Process `i` cannot distinguish the alternative views from `V` when it observes `w₂`. -/
theorem altView_sameKnow (G : Op → Op → Prop) : π.SameKnow V (π.altView V i w₂ G) i w₂ :=
  ⟨concatOrd_prefixAgree (fun _ hb => (knownSet_self_iff hV).2 hb)
      (fun _ _ hb hab => knownSet_down hV hb hab),
    fun w hw _ hw2 => concatOrd_prefixAgree (fun _ hb => ⟨w, hw2, Or.inr ⟨hw, rfl⟩, hb⟩)
      (fun _ _ hb hab => knownSet_down hV hb hab)⟩

include hw₁ hp₁ hcov in
/-- As far as `i` knows when it observes `w₂`, no third process has observed `w₁`. -/
theorem not_knownSet_w₁ {k : P} (hki : k ≠ i) (hkj : k ≠ π.proc w₂) :
    ¬ π.knownSet V i w₂ k w₁ := by
  rintro ⟨w, h1, h2 | ⟨hw, hpw⟩, h3⟩
  · exact hki h2
  have hw1 : w ≠ w₁ := fun e => hki (hpw.symm.trans (e ▸ hp₁))
  have hw2 : w ≠ w₂ := fun e => hkj (hpw.symm.trans (congrArg π.proc e))
  have h3' : V k w₁ w := reflGen_of_ne h3 hw1.symm
  have hsco : π.SCO V w₁ w := ⟨hw₁, hw, by rw [hpw]; exact h3'⟩
  exact hcov.2 w (hV.sco i hsco) (reflGen_of_ne h1 hw2)

include hw₁ hw₂ hp₁ hp₂ hcov hj in
/-- The key construction for Theorem 5.6: for a cover `w₁ ⋖ w₂` of `V_i` with `w₁` a write of `i`,
`w₂` a write of `j ≠ i` and `w₂ <_{V_j} w₁`, there are strongly causal views `W`, indistinguishable
from `V` for `i` when it observes `w₂`, in which `(w₁, w₂)` is still a cover of `W_i` not in
`SCO_i(W)`, but no longer in `B_i(W)`. -/
theorem exists_indistinguishable :
    ∃ W : P → Op → Op → Prop, π.StronglyCausal W ∧ π.SameKnow V W i w₂ ∧ Cov (W i) w₁ w₂ ∧
      ¬ π.SCOi W i w₁ w₂ ∧ ¬ π.B1 W i w₁ w₂ := by
  obtain ⟨G, hG, hGS⟩ := strictPO_exists_linearExt (poClose_zW_strictPO hV hp₁ hp₂ hj)
  have hGz : ∀ a b, π.zW V i w₁ w₂ a b → G a b := fun a b h => hGS a b (le_poClose_right h)
  have hSC := altView_stronglyCausal hV hw₂ hG (fun a b h => hGz a b (zW_sco hV h))
    (fun a b h => hGS a b (le_poClose_left h)) (fun a b ha hb hb' => hGz a b (zW_known ha hb hb'))
  have hSK : π.SameKnow V (π.altView V i w₂ G) i w₂ := altView_sameKnow hV G
  refine ⟨_, hSC, hSK, hSK.1.cov hcov, fun h => ?_, ?_⟩
  · have := (hSK.2 w₂ hw₂ hp₂ ReflGen.refl w₁ w₂ ReflGen.refl).2 h.1.2.2
    exact (hV.total _).asymm hj this
  · rintro ⟨-, -, -, -, -, k, hki, hkj, hk⟩
    rcases hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, h⟩
    · exact not_knownSet_w₁ hV hw₁ hp₁ hcov hki hkj h
    · exact not_knownSet_w₁ hV hw₁ hp₁ hcov hki hkj h
    · exact hG.asymm h (hGz _ _ (zW_21 hw₁ hw₂ hcov))

end

end Construction

/-- **Theorem 5.6.** Let `Rec` be an online record scheme (RnR Model 1) that yields a good record
for every set of views explaining a strongly causally consistent execution. Then for every such
`V`, every process `i` and all `o₁, o₂ ∈ (∗, i, ∗, ∗) ∪ (w, ∗, ∗, ∗)`, every edge
`(o₁, o₂) ∈ V̂_i \ (PO ∪ SCO_i(V))` is in `Rec V i`.

The paper states this per execution ("for any good online record `R` of `V`"); since being online
is a property of how the record depends on the execution, it is stated here for record schemes,
uniformly over executions. -/
theorem theorem_5_6 [Finite Op] {Rec : (P → Op → Op → Prop) → P → Op → Op → Prop}
    (hon : π.IsOnline Rec)
    (hRec : ∀ (ex : Execution Op) (V : P → Op → Op → Prop), π.SCCExplains ex V →
      IsRecord1 V (Rec V) ∧ π.Good1 V (Rec V))
    {ex : Execution Op} {V : P → Op → Op → Prop} (hV : π.SCCExplains ex V) {i : P} {o₁ o₂ : Op}
    (h₁ : π.Obs i o₁) (h₂ : π.Obs i o₂) (hcov : Cov (V i) o₁ o₂) (hpo : ¬ π.po o₁ o₂)
    (hs : ¬ π.SCOi V i o₁ o₂) : Rec V i o₁ o₂ := by
  by_cases hb : π.B1 V i o₁ o₂
  · obtain ⟨hw₁, hw₂, hp₁, hp₂, -, -⟩ := hb
    have hne : o₁ ≠ o₂ := (hV.2.total i).ne hcov.1
    have hj : V (π.proc o₂) o₂ o₁ := (hV.2.total _).of_not (π.write_obs hw₁ _)
      (π.write_obs hw₂ _) hne (fun h => hs ⟨⟨hw₁, hw₂, h⟩, hp₂⟩)
    obtain ⟨W, hW, hSK, hcovW, hsW, hbW⟩ := exists_indistinguishable hV.2 hw₁ hw₂ hp₁ hp₂ hcov hj
    obtain ⟨exW, hexW⟩ := π.exists_explains W hW.total
    have hWE : π.SCCExplains exW W := ⟨hexW, hW⟩
    have hRW := theorem_5_4 hWE (hRec _ _ hWE).1 (hRec _ _ hWE).2 h₁ h₂ hcovW hpo hsW hbW
    exact (hon V W hV.2 hW i o₁ o₂ hSK).2 hRW
  · exact theorem_5_4 hV (hRec _ _ hV).1 (hRec _ _ hV).2 h₁ h₂ hcov hpo hs hb

/-- Theorems 5.5 and 5.6 together: `R_i = V̂_i \ (SCO_i(V) ∪ PO)` is the least online record scheme
yielding good records. -/
theorem rec1on_least_online [Finite Op] :
    (π.IsOnline π.rec1on ∧ ∀ (ex : Execution Op) (V : P → Op → Op → Prop), π.SCCExplains ex V →
        IsRecord1 V (π.rec1on V) ∧ π.Good1 V (π.rec1on V)) ∧
      ∀ Rec : (P → Op → Op → Prop) → P → Op → Op → Prop, π.IsOnline Rec →
        (∀ (ex : Execution Op) (V : P → Op → Op → Prop), π.SCCExplains ex V →
          IsRecord1 V (Rec V) ∧ π.Good1 V (Rec V)) →
        ∀ (ex : Execution Op) (V : P → Op → Op → Prop), π.SCCExplains ex V →
          ∀ i a b, π.rec1on V i a b → Rec V i a b :=
  ⟨theorem_5_5, fun _ hon hRec _ _ hV i _ _ h =>
    theorem_5_6 hon hRec hV ((hV.2.total i).supp h.1.1).1 ((hV.2.total i).supp h.1.1).2 h.1
      h.2.2 h.2.1⟩

end Program

end Podc.CausalRecordReplay
