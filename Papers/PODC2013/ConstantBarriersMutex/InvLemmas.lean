import Papers.PODC2013.ConstantBarriersMutex.InvDefs

/-!
# Consequences of the invariant used in its preservation proof
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-! ### Views depend only on the corresponding field of the base memory -/

section congr
variable {m₁ m₂ : Mem h} (b : List (W h))

lemma view_promQ_congr (he : m₁.promQ = m₂.promQ) : (m₁.view b).promQ = (m₂.view b).promQ := by
  induction b generalizing m₁ m₂ with
  | nil => exact he
  | cons w b ih => exact ih (by cases w <;> simp [Mem.write, he])

lemma view_exits_congr (he : m₁.exits = m₂.exits) : (m₁.view b).exits = (m₂.view b).exits := by
  induction b generalizing m₁ m₂ with
  | nil => exact he
  | cons w b ih => exact ih (by cases w <;> simp [Mem.write, he])

lemma view_lock_congr (he : m₁.lock = m₂.lock) : (m₁.view b).lock = (m₂.view b).lock := by
  induction b generalizing m₁ m₂ with
  | nil => exact he
  | cons w b ih => exact ih (by cases w <;> simp [Mem.write, he])

lemma view_inPromQ_congr {q : Proc h} (he : m₁.inPromQ q = m₂.inPromQ q) :
    (m₁.view b).inPromQ q = (m₂.view b).inPromQ q := by
  induction b generalizing m₁ m₂ with
  | nil => exact he
  | cons w b ih => exact ih (by simp only [write_inPromQ]; cases w <;> simp [he])

lemma view_apply_congr {q : Proc h} (he : m₁.apply q = m₂.apply q) :
    (m₁.view b).apply q = (m₂.view b).apply q := by
  induction b generalizing m₁ m₂ with
  | nil => exact he
  | cons w b ih => exact ih (by simp only [write_apply]; cases w <;> simp [he])

lemma view_signal_congr {q : Proc h} (he : m₁.signal q = m₂.signal q) :
    (m₁.view b).signal q = (m₂.view b).signal q := by
  induction b generalizing m₁ m₂ with
  | nil => exact he
  | cons w b ih => exact ih (by simp only [write_signal]; cases w <;> simp [he])

lemma view_node_congr {i : ℕ} (he : m₁.node i = m₂.node i) :
    (m₁.view b).node i = (m₂.view b).node i := by
  induction b generalizing m₁ m₂ with
  | nil => exact he
  | cons w b ih => exact ih (by simp only [write_node]; cases w <;> simp [he])

end congr

/-! ### Congruence of the local invariant -/

lemma LI_congr {s s' : Cfg h} {q : Proc h} (hm : s'.mem = s.mem) (hb : s'.buf q = s.buf q)
    (hp : s'.pc q = s.pc q) : LI s' q ↔ LI s q := by
  unfold LI; rw [hp]; simp only [XB, DoorLI, hm, hb]

/-! ### The doorway list -/

lemma mem_doorList {q : Proc h} {w : W h} (hw : w ∈ doorList q) :
    w = .signal q false ∨ w = .apply q true ∨ ∃ i, w = .node i q := by
  simp only [doorList, List.mem_cons, List.mem_map, List.mem_reverse, List.mem_range] at hw
  rcases hw with hw | hw | ⟨l, -, rfl⟩
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr ⟨_, rfl⟩)

lemma mem_doorLI {s : Cfg h} {q : Proc h} {k : ℕ} (hd : DoorLI s q k) {w : W h}
    (hw : w ∈ s.buf q) : w = .signal q false ∨ w = .apply q true ∨ ∃ i, w = .node i q := by
  obtain ⟨i, -, hb, -⟩ := hd
  rw [hb] at hw
  exact mem_doorList (List.mem_of_mem_take (List.mem_of_mem_drop hw))

lemma doorList_length (q : Proc h) : (doorList q).length = h + 3 := by
  simp [doorList]

lemma doorList_get0 (q : Proc h) : (doorList q)[0]? = some (.signal q false) := rfl
lemma doorList_get1 (q : Proc h) : (doorList q)[1]? = some (.apply q true) := rfl
lemma doorList_getNode (q : Proc h) {l : ℕ} (hl : l ≤ h) :
    (doorList q)[2 + (h - l)]? = some (.node (anc q l) q) := by
  simp only [doorList]
  rw [show 2 + (h - l) = (h - l) + 1 + 1 by omega]
  simp only [List.getElem?_cons_succ, List.getElem?_map]
  rw [List.getElem?_reverse (by simp)]
  simp only [List.length_range]
  rw [List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.some.injEq, W.node.injEq, and_true]
  congr 1; omega

/-- Issuing the next doorway write. -/
lemma take_succ_doorList (q : Proc h) {k : ℕ} {w : W h} (hk : (doorList q)[k]? = some w) :
    (doorList q).take (k + 1) = (doorList q).take k ++ [w] := by
  rw [List.take_add_one, hk]; rfl

/-! ### Locks, holders, handers -/

section
variable {s : Cfg h} (hI : Inv s)
include hI

lemma Inv.holds_lock {g : Proc h} (hg : Holds s g) : s.mem.lock = some g := by
  have hl := hI.loc g
  unfold Holds at hg; unfold LI at hl
  cases hpc : s.pc g <;> simp only [hpc] at hg hl
  all_goals first | exact hg.elim | exact hl.2.2 | exact hl.1 | skip
  · rcases hl.2 with ⟨B, -, -, hlk⟩ | ⟨hb, -⟩
    · exact hlk
    · simp [hb] at hg
  · rename_i o
    rcases o with _ | nx
    · rcases hl with ⟨B, -, -, hlk⟩ | ⟨hb, -⟩
      · exact hlk
      · simp [hb] at hg
    · rcases hl.2 with ⟨B, -, -, hlk⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
      · exact hlk
      · simp [hb] at hg
      · simp [hb] at hg

lemma Inv.hands_lock {g nx : Proc h} (hg : Hands s g nx) :
    s.mem.lock = some nx ∧ nx ≠ g ∧ s.mem.signal nx = false ∧ s.mem.apply g = false := by
  have hl := hI.loc g
  unfold LI at hl
  rcases hg with ⟨hpc, hb⟩ | ⟨hpc, hb⟩
  · simp only [hpc] at hl
    rcases hl.2 with ⟨B, hB, -, -⟩ | ⟨-, h1, h2, h3⟩
    · simp [hb] at hB
    · exact ⟨h1, hl.1, h3, h2⟩
  · simp only [hpc] at hl
    rcases hl.2 with ⟨B, hB, -, -⟩ | ⟨-, h1, h2, h3⟩ | ⟨hb', -⟩
    · rw [hb] at hB
      have := congrArg List.length hB; simp at this
    · exact ⟨h1, hl.1, h3, h2⟩
    · simp [hb] at hb'

lemma Inv.not_holds_of_hands {g nx : Proc h} (hg : Hands s g nx) : ¬ Holds s g := by
  intro hh
  have h1 := hI.holds_lock hh
  have h2 := hI.hands_lock hg
  rw [h1] at h2; exact h2.2.1 (Option.some_injective _ h2.1).symm

lemma Inv.incsx_iff {g : Proc h} : s.InCSX g ↔ Holds s g ∨ ∃ nx, Hands s g nx := by
  have hl := hI.loc g
  unfold Cfg.InCSX Holds Hands
  unfold LI at hl
  cases hpc : s.pc g <;> simp only [hpc, PC.Exit] at hl ⊢ <;> simp
  · rename_i nx
    rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩
    · left; simp [hB]
    · right; exact hB
  · rename_i o
    rcases o with _ | nx
    · rcases hl with ⟨B, hB, -⟩ | ⟨hB, -⟩
      · simp [hB]
      · simp [hB]
    · rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
      · simp [hB]
      · simp [hB]
      · simp [hB]

lemma Inv.holds_unique {g g' : Proc h} (hg : Holds s g) (hg' : Holds s g') : g = g' := by
  have := hI.holds_lock hg; rw [hI.holds_lock hg'] at this
  exact (Option.some_injective _ this).symm

lemma Inv.lv_of_holds {g : Proc h} (hg : Holds s g) : lv s = s.view g := by
  simp [lv, hI.holds_lock hg, Cfg.view]

end

/-- Writes in a buffer of a process that does not hold the lock. -/
def NHW (q : Proc h) (w : W h) : Prop :=
  w = .signal q false ∨ w = .apply q true ∨ (∃ i, w = .node i q) ∨ ∃ nx, w = .signal nx true

lemma Inv.nonholder_buf {s : Cfg h} (hI : Inv s) {q : Proc h} (hq : ¬ Holds s q) :
    ∀ w ∈ s.buf q, NHW q w := by
  intro w hw
  have hl := hI.loc q
  unfold LI at hl; unfold Holds at hq
  have hd : ∀ k, DoorLI s q k → NHW q w := fun k hd => by
    have := mem_doorLI hd hw; unfold NHW; tauto
  cases hpc : s.pc q <;> simp only [hpc] at hl hq <;> try exact absurd trivial hq
  all_goals first | exact hd _ hl | exact hd _ hl.2 | (rw [hl.1] at hw; simp at hw) | skip
  · rename_i nx
    rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩
    · exact absurd (by simp [hB]) hq
    · simp [hB] at hw
  · rename_i o
    rcases o with _ | nx
    · rcases hl with ⟨B, hB, -⟩ | ⟨hB, -⟩
      · exact absurd (by simp [hB]) hq
      · simp [hB] at hw
    · rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
      · exact absurd (by simp [hB]) hq
      · rw [hB] at hw; simp at hw; subst hw; exact Or.inr (Or.inr (Or.inr ⟨nx, rfl⟩))
      · simp [hB] at hw

lemma NHW.promQ {q : Proc h} {w : W h} (hw : NHW q w) : w.isPromQ = false := by
  rcases hw with rfl | rfl | ⟨i, rfl⟩ | ⟨nx, rfl⟩ <;> rfl
lemma NHW.exits {q : Proc h} {w : W h} (hw : NHW q w) : w.isExits = false := by
  rcases hw with rfl | rfl | ⟨i, rfl⟩ | ⟨nx, rfl⟩ <;> rfl
lemma NHW.lock {q : Proc h} {w : W h} (hw : NHW q w) : w.isLock = false := by
  rcases hw with rfl | rfl | ⟨i, rfl⟩ | ⟨nx, rfl⟩ <;> rfl
lemma NHW.inPromQ {q r : Proc h} {w : W h} (hw : NHW q w) : w.isInPromQ r = false := by
  rcases hw with rfl | rfl | ⟨i, rfl⟩ | ⟨nx, rfl⟩ <;> rfl

/-- If nobody holds the lock, the logical memory agrees with memory on the queue fields. -/
lemma Inv.lv_of_not_holds {s : Cfg h} (hI : Inv s) (hn : ∀ g, ¬ Holds s g) :
    (lv s).promQ = s.mem.promQ ∧ (lv s).exits = s.mem.exits ∧
      ∀ r, (lv s).inPromQ r = s.mem.inPromQ r := by
  unfold lv
  split
  · rename_i g _
    have hb := hI.nonholder_buf (hn g)
    exact ⟨view_promQ_of (fun w hw => (hb w hw).promQ), view_exits_of (fun w hw => (hb w hw).exits),
      fun r => view_inPromQ_of (fun w hw => (hb w hw).inPromQ)⟩
  · exact ⟨rfl, rfl, fun _ => rfl⟩

end Podc.ConstantBarriersMutex

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- The local invariant only depends on `buf q`, `pc q`, `apply[q]`, `lock`, and only on facts
`signal[r] = false`. -/
lemma LI_mono {s s' : Cfg h} {q : Proc h} (hb : s'.buf q = s.buf q) (hp : s'.pc q = s.pc q)
    (ha : s'.mem.apply q = s.mem.apply q) (hl : s'.mem.lock = s.mem.lock)
    (hs : ∀ r, s.mem.signal r = false → s'.mem.signal r = false) (hL : LI s q) : LI s' q := by
  unfold LI at hL ⊢
  rw [hp]
  simp only [XB, DoorLI, hb, ha, hl] at hL ⊢
  cases hpc : s.pc q <;> simp only [hpc] at hL ⊢ <;> try exact hL
  · obtain ⟨i, hi, h1, h2, h3⟩ := hL; exact ⟨i, hi, h1, h2, fun h => hs _ (h3 h)⟩
  · obtain ⟨hl', i, hi, h1, h2, h3⟩ := hL; exact ⟨hl', i, hi, h1, h2, fun h => hs _ (h3 h)⟩
  · obtain ⟨i, hi, h1, h2, h3⟩ := hL; exact ⟨i, hi, h1, h2, fun h => hs _ (h3 h)⟩
  · obtain ⟨h1, h2 | ⟨h2, h3, h4, h5⟩⟩ := hL
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr ⟨h2, h3, h4, hs _ h5⟩⟩
  · rename_i o
    rcases o with _ | nx
    · exact hL
    · obtain ⟨h1, h2 | ⟨h2, h3, h4, h5⟩ | h2⟩ := hL
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h1, Or.inr (Or.inl ⟨h2, h3, h4, hs _ h5⟩)⟩
      · exact ⟨h1, Or.inr (Or.inr h2)⟩

lemma Inv.holder_buf {s : Cfg h} (hI : Inv s) {g : Proc h} (hg : Holds s g) :
    ∀ w ∈ s.buf g, ExitType g w ∨ w.isLock = true ∨ ∃ nx, w = .signal nx true := by
  intro w hw
  have hl := hI.loc g
  unfold LI at hl; unfold Holds at hg
  cases hpc : s.pc g <;> simp only [hpc] at hl hg <;> try exact hg.elim
  all_goals first
    | (rw [hl.1] at hw; simp at hw)
    | (left; exact hl.2.1.1 w hw)
    | (left; exact hl.2.1 w hw)
    | skip
  · rcases hl.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at hw <;> simp at hw
    left; left; exact hw
  · rcases hl.2 with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩
    · rw [hB] at hw; simp at hw
      rcases hw with hw | rfl
      · left; exact hX.1 w hw
      · right; left; rfl
    · simp [hB] at hw
  · rename_i o
    rcases o with _ | nx
    · rcases hl with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩
      · rw [hB] at hw; simp at hw
        rcases hw with hw | rfl
        · left; exact hX.1 w hw
        · right; left; rfl
      · simp [hB] at hw
    · rcases hl.2 with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
      · rw [hB] at hw; simp at hw
        rcases hw with hw | rfl | rfl
        · left; exact hX.1 w hw
        · right; left; rfl
        · right; right; exact ⟨nx, rfl⟩
      · rw [hB] at hw; simp at hw; subst hw; right; right; exact ⟨nx, rfl⟩
      · simp [hB] at hw

lemma Inv.incsx_of_holds {s : Cfg h} (hI : Inv s) {g : Proc h} (hg : Holds s g) : s.InCSX g :=
  hI.incsx_iff.2 (Or.inl hg)

lemma Inv.incsx_of_hands {s : Cfg h} (hI : Inv s) {g nx : Proc h} (hg : Hands s g nx) :
    s.InCSX g := hI.incsx_iff.2 (Or.inr ⟨nx, hg⟩)

end Podc.ConstantBarriersMutex

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-! ### Effects of exit-section writes on memory -/

section
variable {g : Proc h} {w : W h} (hX : ExitType g w) (m : Mem h)
include hX

lemma ExitType.lock : (m.write w).lock = m.lock := by
  rcases hX with rfl | hX | hX | ⟨r', b, rfl⟩ <;> try rfl
  all_goals cases w <;> simp_all [W.isExits, W.isPromQ, Mem.write]

lemma ExitType.signal (r : Proc h) : (m.write w).signal r = m.signal r := by
  rcases hX with rfl | hX | hX | ⟨r', b, rfl⟩ <;> try rfl
  all_goals cases w <;> simp_all [W.isExits, W.isPromQ, Mem.write]

lemma ExitType.apply {r : Proc h} (hr : r ≠ g) : (m.write w).apply r = m.apply r := by
  rcases hX with rfl | hX | hX | ⟨r', b, rfl⟩
  · simp [Mem.write, Function.update_of_ne hr]
  all_goals first | rfl | (cases w <;> simp_all [W.isExits, W.isPromQ, Mem.write])

lemma ExitType.apply_le (hr : (m.write w).apply g = true) : m.apply g = true := by
  rcases hX with rfl | hX | hX | ⟨r', b, rfl⟩
  · simp [Mem.write] at hr
  all_goals first | exact hr | (cases w <;> simp_all [W.isExits, W.isPromQ, Mem.write])

end

/-! ### Frame lemmas for the clauses mentioning `HC` -/

/-- `HC` is preserved by a transition that does not change program counters or the queue fields
of the logical memory, does not lower `apply[c]` except for a lock holder `c`, and does not
make an empty buffer non-empty. -/
lemma HC_frame {s s' : Cfg h} (hI : Inv s) (hpc : s'.pc = s.pc)
    (hlvP : (lv s').promQ = (lv s).promQ) (hlvI : ∀ r, (lv s').inPromQ r = (lv s).inPromQ r)
    (hap : ∀ c, s.mem.apply c = true → s'.mem.apply c = true ∨ Holds s c)
    (hbuf : ∀ q, s'.buf q ≠ [] → s.buf q ≠ []) (q : Proc h) : HC s' q := by
  have hc := hI.hc q
  have hl := hI.loc q
  have hcs : ∀ c, c ≠ q → s.InCSX q → s.mem.apply c = true → s'.mem.apply c = true := by
    intro c hcq hq hc'
    rcases hap c hc' with h1 | h1
    · exact h1
    · exact absurd (hI.uniq _ _ (hI.incsx_of_holds h1) hq) hcq
  have hX : ∀ q, (s.pc q).Exit → s.InCSX q := fun q hq => Or.inr (Or.inl hq)
  unfold HC NxOK at hc ⊢
  unfold LI at hl
  rw [hpc, hlvP]
  simp only [hlvI]
  have hXq : (s.pc q).Exit → s.InCSX q := hX q
  cases hp : s.pc q <;> simp only [hp, PC.Exit, true_imp_iff] at hc hl hXq ⊢ <;> try trivial
  all_goals first
    | exact hc
    | exact ⟨hc.1, hcs _ hl.2.2.2 hXq hc.2⟩
    | exact ⟨hc.1, hcs _ hl.2.2.2 hXq hc.2.1, hc.2.2⟩
    | exact ⟨hc.1, hcs _ hl.2.2 hXq hc.2.1, hc.2.2⟩
    | exact ⟨hc.1, hcs _ hl.1 hXq hc.2.1, hc.2.2⟩
    | skip
  rename_i o
  rcases o with _ | nx
  · exact fun hne => hc (hbuf q hne)
  · intro hne
    have hne' := hbuf q hne
    have h1 := hc hne'
    exact ⟨h1.1, hcs _ hl.1 (Or.inr (Or.inr ⟨⟨_, hp⟩, hne'⟩)) h1.2.1, h1.2.2⟩

end Podc.ConstantBarriersMutex

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

lemma drop_take_cons {l : List (W h)} {k i : ℕ} {w : W h} {b : List (W h)}
    (hd : (l.take k).drop i = w :: b) : i < k ∧ l[i]? = some w ∧ b = (l.take k).drop (i + 1) := by
  have hi : i < (l.take k).length := by
    by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hd; simp at hd
  rw [List.drop_eq_getElem_cons hi] at hd
  simp only [List.cons.injEq] at hd
  refine ⟨by simp at hi; omega, ?_, hd.2.symm⟩
  rw [← hd.1, List.getElem_take]; simp at hi; simp [List.getElem?_eq_getElem hi.2]

lemma doorList_get_signal {q : Proc h} {i : ℕ} {r : Proc h} {b : Bool}
    (hi : (doorList q)[i]? = some (.signal r b)) : i = 0 := by
  rcases i with _ | _ | i
  · rfl
  · simp [doorList_get1] at hi
  · simp only [doorList, List.getElem?_cons_succ] at hi
    have := List.mem_of_getElem? hi; simp at this
lemma doorList_get_apply {q : Proc h} {i : ℕ} {r : Proc h} {b : Bool}
    (hi : (doorList q)[i]? = some (.apply r b)) : i = 1 := by
  rcases i with _ | _ | i
  · simp [doorList_get0] at hi
  · rfl
  · simp only [doorList, List.getElem?_cons_succ] at hi
    have := List.mem_of_getElem? hi; simp at this

/-- Number of doorway writes issued at a doorway program counter. -/
def PC.issued : PC h → ℕ
  | .e18 => 1
  | .e19 l => 2 + (h - l)
  | .e22 => h + 3
  | _ => 0

/-- The local invariant of a process in the doorway. -/
lemma LI_door {s : Cfg h} {q : Proc h} (hL : LI s q)
    (hd : s.pc q = .e18 ∨ (∃ l, s.pc q = .e19 l) ∨ s.pc q = .e22) :
    DoorLI s q (s.pc q).issued := by
  unfold LI at hL
  rcases hd with hd | ⟨l, hd⟩ | hd <;> rw [hd] at hL ⊢
  · exact hL
  · exact hL.2
  · exact hL

lemma LI_of_door {s s' : Cfg h} {q : Proc h} (hL : LI s q) (hp : s'.pc q = s.pc q)
    (hd : s.pc q = .e18 ∨ (∃ l, s.pc q = .e19 l) ∨ s.pc q = .e22)
    (hD : DoorLI s' q (s.pc q).issued) : LI s' q := by
  unfold LI at hL ⊢
  rw [hp]
  rcases hd with hd | ⟨l, hd⟩ | hd <;> rw [hd] at hL hD ⊢
  · exact hD
  · exact ⟨hL.1, hD⟩
  · exact hD

/-- Writes `signal[q] ← false` and `apply[q] ← true` occur only in doorway buffers. -/
lemma Inv.door_of_head {s : Cfg h} (hI : Inv s) {q : Proc h} {w : W h} {b : List (W h)}
    (hb : s.buf q = w :: b) (hw : w = .signal q false ∨ w = .apply q true ∨ ∃ i, w = .node i q) :
    ∃ i, i < (s.pc q).issued ∧ (doorList q)[i]? = some w ∧
      s.buf q = ((doorList q).take (s.pc q).issued).drop i ∧
      (s.mem.apply q = true ↔ 2 ≤ i) ∧ (i = 1 → s.mem.signal q = false) ∧
      (s.pc q = .e18 ∨ (∃ l, s.pc q = .e19 l) ∨ s.pc q = .e22) := by
  have hl := hI.loc q
  have hnh : ¬ Holds s q := by
    intro hh
    rcases hI.holder_buf hh w (by simp [hb]) with h1 | h1 | ⟨nx, h1⟩
    · rcases h1 with h1 | h1 | h1 | ⟨r, b, h1⟩ <;> rcases hw with rfl | rfl | ⟨i, rfl⟩ <;>
        simp_all [W.isExits, W.isPromQ]
    · rcases hw with rfl | rfl | ⟨i, rfl⟩ <;> simp [W.isLock] at h1
    · rcases hw with rfl | rfl | ⟨i, rfl⟩ <;> simp at h1
  have hd : s.pc q = .e18 ∨ (∃ l, s.pc q = .e19 l) ∨ s.pc q = .e22 := by
    unfold LI at hl; unfold Holds at hnh
    cases hp : s.pc q <;> simp only [hp] at hl hnh <;> simp
    all_goals first
      | (rw [hl.1] at hb; simp at hb)
      | exact absurd trivial hnh
      | skip
    · rename_i nx
      rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩
      · exact hnh (by simp [hB])
      · rw [hB] at hb; simp at hb
    · rename_i o
      rcases o with _ | nx
      · rcases hl with ⟨B, hB, -⟩ | ⟨hB, -⟩
        · exact hnh (by simp [hB])
        · rw [hB] at hb; simp at hb
      · rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
        · exact hnh (by simp [hB])
        · rw [hB] at hb; simp at hb; rcases hw with rfl | rfl | ⟨i, rfl⟩ <;> simp_all
        · rw [hB] at hb; simp at hb
  obtain ⟨i, hik, hbk, h1, h2⟩ := LI_door hl hd
  rw [hbk] at hb
  obtain ⟨hlt, hget, -⟩ := drop_take_cons hb
  exact ⟨i, hlt, hget, hbk, h1, h2, hd⟩

lemma Inv.apply_false_of_head_sig {s : Cfg h} (hI : Inv s) {q : Proc h} {b : List (W h)}
    (hb : s.buf q = .signal q false :: b) : s.mem.apply q = false := by
  obtain ⟨i, -, hget, -, h1, -⟩ := hI.door_of_head hb (Or.inl rfl)
  have := doorList_get_signal hget; subst this
  cases ha : s.mem.apply q
  · rfl
  · have := h1.1 ha; omega

lemma Inv.signal_false_of_head_apply {s : Cfg h} (hI : Inv s) {q : Proc h} {b : List (W h)}
    (hb : s.buf q = .apply q true :: b) : s.mem.signal q = false := by
  obtain ⟨i, -, hget, -, -, h2, -⟩ := hI.door_of_head hb (Or.inr (Or.inl rfl))
  exact h2 (doorList_get_apply hget)

lemma Inv.no_exits_early {s : Cfg h} (hI : Inv s) {g : Proc h}
    (hg : s.pc g = .cs ∨ s.pc g = .x31 ∨ s.pc g = .x32) (v : ℕ) : .exits v ∉ s.buf g := by
  have hl := hI.loc g
  unfold LI at hl
  rcases hg with hg | hg | hg <;> rw [hg] at hl
  · rw [hl.1]; simp
  · rw [hl.1]; simp
  · rcases hl.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp

lemma Inv.holds_of_exits_mem {s : Cfg h} (hI : Inv s) {g : Proc h} {v : ℕ}
    (hv : .exits v ∈ s.buf g) : Holds s g := by
  by_contra hn
  have := (hI.nonholder_buf hn _ hv).exits; simp [W.isExits] at this

end Podc.ConstantBarriersMutex

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- The local invariant of a process outside the critical/exit section does not mention `lock`
nor the `signal` of other processes. -/
lemma LI_mono_out {s s' : Cfg h} {q : Proc h} (hI : Inv s) (hout : ¬ s.InCSX q)
    (hb : s'.buf q = s.buf q) (hp : s'.pc q = s.pc q)
    (ha : s'.mem.apply q = s.mem.apply q)
    (hs : s.mem.signal q = false → s'.mem.signal q = false) : LI s' q := by
  have hL := hI.loc q
  unfold Cfg.InCSX at hout
  unfold LI at hL ⊢
  rw [hp]
  simp only [XB, DoorLI, hb, ha] at hL ⊢
  cases hpc : s.pc q <;> simp only [hpc, PC.Exit, not_or] at hL hout ⊢ <;>
    try exact absurd trivial hout.2.1
  all_goals first | exact hL | skip
  · obtain ⟨i, hi, h1, h2, h3⟩ := hL; exact ⟨i, hi, h1, h2, fun h => hs (h3 h)⟩
  · obtain ⟨hl', i, hi, h1, h2, h3⟩ := hL; exact ⟨hl', i, hi, h1, h2, fun h => hs (h3 h)⟩
  · obtain ⟨i, hi, h1, h2, h3⟩ := hL; exact ⟨i, hi, h1, h2, fun h => hs (h3 h)⟩
  · exact absurd trivial hout.1
  · rename_i o
    have hbq : s.buf q = [] := by
      by_contra hne; exact hout.2.2 ⟨⟨o, rfl⟩, hne⟩
    rcases o with _ | nx
    · rcases hL with ⟨B, hB, -⟩ | h1
      · rw [hbq] at hB; simp at hB
      · exact Or.inr h1
    · rcases hL with ⟨h0, ⟨B, hB, -⟩ | ⟨hB, -⟩ | h1⟩
      · rw [hbq] at hB; simp at hB
      · rw [hbq] at hB; simp at hB
      · exact ⟨h0, Or.inr (Or.inr h1)⟩

/-- A process in the entry section whose `apply` write was performed: its local invariant does
not mention `signal`. -/
lemma LI_entry_applied {s s' : Cfg h} {q : Proc h} (hI : Inv s) (hE : (s.pc q).Entry)
    (hap : s.mem.apply q = true)
    (hb : s'.buf q = s.buf q) (hp : s'.pc q = s.pc q)
    (ha : s'.mem.apply q = s.mem.apply q) : LI s' q := by
  have hL := hI.loc q
  unfold LI at hL ⊢
  rw [hp]
  simp only [XB, DoorLI, hb, ha] at hL ⊢
  cases hpc : s.pc q <;> simp only [hpc, PC.Entry] at hL hE ⊢ <;> try exact hE.elim
  all_goals first | exact hL | skip
  · obtain ⟨i, hi, h1, h2, -⟩ := hL
    have := h2.1 hap; exact ⟨i, hi, h1, h2, fun h => by omega⟩
  · obtain ⟨hl', i, hi, h1, h2, -⟩ := hL
    have := h2.1 hap; exact ⟨hl', i, hi, h1, h2, fun h => by omega⟩
  · obtain ⟨i, hi, h1, h2, -⟩ := hL
    have := h2.1 hap; exact ⟨i, hi, h1, h2, fun h => by omega⟩

lemma Inv.not_holds_of_entry {s : Cfg h} {q : Proc h} (hE : (s.pc q).Entry) : ¬ Holds s q := by
  unfold Holds; revert hE; cases s.pc q <;> simp [PC.Entry]

lemma Inv.not_incsx_of_entry {s : Cfg h} {q : Proc h} (hE : (s.pc q).Entry) : ¬ s.InCSX q := by
  unfold Cfg.InCSX; revert hE; cases s.pc q <;> simp [PC.Entry, PC.Exit]

/-- The handed process (the lock value when no process holds the lock) is in the entry
section and has performed its `apply` write. -/
lemma Inv.lock_entry {s : Cfg h} (hI : Inv s) {nx : Proc h} (hl : s.mem.lock = some nx)
    (hnh : ¬ Holds s nx) : (s.pc nx).Entry ∧ s.mem.apply nx = true := by
  rcases hI.lockRole nx hl with h1 | ⟨h1, h2, -⟩
  · exact absurd h1 hnh
  · exact ⟨h1, h2⟩

end Podc.ConstantBarriersMutex

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

lemma ExitType.isLock {g : Proc h} {w : W h} (hX : ExitType g w) : w.isLock = false := by
  rcases hX with rfl | hX | hX | ⟨r', b, rfl⟩ <;> try rfl
  all_goals cases w <;> simp_all [W.isExits, W.isPromQ, W.isLock]

lemma ExitType.ne_signal {g : Proc h} {w : W h} (hX : ExitType g w) (r : Proc h) (b : Bool) :
    w ≠ .signal r b := by
  rintro rfl
  rcases hX with h1 | h1 | h1 | ⟨r', b', h1⟩ <;> simp_all [W.isExits, W.isPromQ]

/-- The shape of a lock holder's store buffer. -/
lemma Inv.holder_shape {s : Cfg h} (hI : Inv s) {g : Proc h} (hg : Holds s g) :
    (∀ w ∈ s.buf g, ExitType g w) ∨
    (∃ B nx, s.pc g = .x48 nx ∧ s.buf g = B ++ [.lock (some nx)] ∧ ∀ w ∈ B, ExitType g w) ∨
    (∃ B, s.pc g = .x50 none ∧ s.buf g = B ++ [.lock none] ∧ ∀ w ∈ B, ExitType g w) ∨
    (∃ B nx, s.pc g = .x50 (some nx) ∧ s.buf g = B ++ [.lock (some nx), .signal nx true] ∧
      ∀ w ∈ B, ExitType g w) := by
  have hl := hI.loc g
  unfold LI at hl; unfold Holds at hg
  cases hp : s.pc g <;> simp only [hp] at hl hg <;> try exact hg.elim
  all_goals first
    | (left; rw [hl.1]; simp)
    | (left; exact hl.2.1.1)
    | (left; exact hl.2.1)
    | skip
  · left; rcases hl.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [ExitType]
  · rename_i nx
    rcases hl.2 with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩
    · exact Or.inr (Or.inl ⟨B, nx, rfl, hB, hX.1⟩)
    · rw [hB] at hg; simp at hg
  · rename_i o
    rcases o with _ | nx
    · rcases hl with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩
      · exact Or.inr (Or.inr (Or.inl ⟨B, rfl, hB, hX.1⟩))
      · rw [hB] at hg; simp at hg
    · rcases hl.2 with ⟨B, hB, hX, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
      · exact Or.inr (Or.inr (Or.inr ⟨B, nx, rfl, hB, hX.1⟩))
      · rw [hB] at hg; simp at hg
      · rw [hB] at hg; simp at hg

/-- A non-holder with `signal[nx] ← true` buffered is the hander of `nx`. -/
lemma Inv.hands_of_head_sig {s : Cfg h} (hI : Inv s) {g nx : Proc h} {b' : List (W h)}
    (hb : s.buf g = .signal nx true :: b') (hg : ¬ Holds s g) :
    s.pc g = .x50 (some nx) ∧ s.buf g = [.signal nx true] := by
  have hl := hI.loc g
  unfold LI at hl; unfold Holds at hg
  cases hp : s.pc g <;> simp only [hp] at hl hg <;> try exact absurd trivial hg
  all_goals first
    | (rw [hl.1] at hb; simp at hb)
    | (have := mem_doorLI hl (show W.signal nx true ∈ s.buf g by simp [hb]); simp at this)
    | (have := mem_doorLI hl.2 (show W.signal nx true ∈ s.buf g by simp [hb]); simp at this)
    | skip
  · rename_i nx'
    rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩
    · exact absurd (by rw [hB]; simp) hg
    · rw [hB] at hb; simp at hb
  · rename_i o'
    rcases o' with _ | nx'
    · rcases hl with ⟨B, hB, -⟩ | ⟨hB, -⟩
      · exact absurd (by rw [hB]; simp) hg
      · rw [hB] at hb; simp at hb
    · rcases hl.2 with ⟨B, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
      · exact absurd (by rw [hB]; simp) hg
      · rw [hB] at hb; simp at hb; obtain ⟨rfl, rfl⟩ := hb; exact ⟨rfl, hB⟩
      · rw [hB] at hb; simp at hb

end Podc.ConstantBarriersMutex

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- Monotonicity of `HC` for one process. -/
lemma HC_mono {s s' : Cfg h} {q : Proc h} (hp : s'.pc q = s.pc q)
    (hEc : ∀ c, (s.pc c).Entry → (s'.pc c).Entry)
    (happ : ∀ c, s.mem.apply c = true → s'.mem.apply c = true)
    (hlvP : (lv s').promQ = (lv s).promQ) (hlvI : ∀ r, (lv s').inPromQ r = (lv s).inPromQ r)
    (hbuf : s'.buf q ≠ [] → s.buf q ≠ []) (hc : HC s q) : HC s' q := by
  unfold HC NxOK at hc ⊢
  rw [hp, hlvP]
  simp only [hlvI]
  cases hpq : s.pc q <;> simp only [hpq] at hc ⊢ <;> try trivial
  all_goals first
    | exact hc
    | exact ⟨hEc _ hc.1, happ _ hc.2⟩
    | exact ⟨hEc _ hc.1, happ _ hc.2.1, hc.2.2⟩
    | skip
  rename_i o
  rcases o with _ | nx
  · exact fun hne => hc (hbuf hne)
  · intro hne
    have h1 := hc (hbuf hne)
    exact ⟨hEc _ h1.1, happ _ h1.2.1, h1.2.2⟩

end Podc.ConstantBarriersMutex
