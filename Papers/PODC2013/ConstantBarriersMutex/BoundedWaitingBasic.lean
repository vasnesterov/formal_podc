import Papers.PODC2013.ConstantBarriersMutex.InvDefs

/-!
# Bounded waiting, part 1: basic facts about single steps

Facts used by the proof of Lemmas 8 and 9 of the paper (bounded waiting): the effect of a step
on the program counters and store buffers of the other processes, how shared memory can change,
the tree arithmetic of `anc`, and consequences of the invariant `Inv` about the contents of the
store buffers.
-/

namespace Podc.ConstantBarriersMutex.BW

open Podc.ConstantBarriersMutex

variable {h : ℕ}

/-! ### Steps of other processes -/

lemma stepProc_pc_ne (s : Cfg h) {g x : Proc h} (hx : x ≠ g) :
    (s.stepProc g).pc x = s.pc x := by
  unfold Cfg.stepProc
  split <;> (try split) <;>
    simp_all [Cfg.goto, Cfg.issue, Cfg.barrier, Cfg.flush, Cfg.cas] <;>
    (try split) <;> (try split) <;> simp_all

lemma stepProc_buf_ne (s : Cfg h) {g x : Proc h} (hx : x ≠ g) :
    (s.stepProc g).buf x = s.buf x := by
  unfold Cfg.stepProc
  split <;> (try split) <;>
    simp_all [Cfg.goto, Cfg.issue, Cfg.barrier, Cfg.flush, Cfg.cas] <;>
    (try split) <;> (try split) <;> simp_all

lemma flush_pc' (s : Cfg h) (g : Proc h) : (s.flush g).pc = s.pc := flush_pc s g

lemma flush_buf_ne (s : Cfg h) {g x : Proc h} (hx : x ≠ g) : (s.flush g).buf x = s.buf x := by
  unfold Cfg.flush; split <;> simp [hx]

lemma next_pc_ne (s : Cfg h) (e : Ev h) {x : Proc h} (hx : e ≠ .step x) :
    (s.next e).pc x = s.pc x := by
  cases e with
  | flush g => simp [Cfg.next]
  | step g =>
    have : x ≠ g := by rintro rfl; exact hx rfl
    simp [Cfg.next, stepProc_pc_ne s this]

/-- Only a step of `x` itself changes the program counter of `x`. -/
lemma eq_step_of_pc_ne (s : Cfg h) (e : Ev h) {x : Proc h} (hx : (s.next e).pc x ≠ s.pc x) :
    e = .step x := by
  by_contra hne; exact hx (next_pc_ne s e hne)

/-! ### The doorway list -/

lemma mem_doorList {q : Proc h} {w : W h} :
    w ∈ doorList q ↔ w = .signal q false ∨ w = .apply q true ∨ ∃ l ≤ h, w = .node (anc q l) q := by
  simp only [doorList, List.mem_cons, List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro (h1 | h1 | ⟨l, hl, rfl⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨l, by omega, rfl⟩)
  · rintro (h1 | h1 | ⟨l, hl, rfl⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨l, by omega, rfl⟩)

lemma mem_of_mem_take_drop {α : Type*} {L : List α} {k i : ℕ} {a : α}
    (ha : a ∈ (L.take k).drop i) : a ∈ L :=
  List.mem_of_mem_take (List.mem_of_mem_drop ha)

/-! ### Store-buffer contents, from the invariant -/

/-- What a store buffer may contain (from the local invariant `LI`). -/
lemma buf_cases {s : Cfg h} (hI : Inv s) {g : Proc h} {w : W h} (hw : w ∈ s.buf g) :
    (w ∈ doorList g ∧ (s.pc g).Entry) ∨ (ExitType g w ∧ s.mem.lock = some g) ∨
    (∃ o, w = .lock o ∧ s.mem.lock = some g ∧
      (s.pc g = .x50 o ∨ ∃ nx, o = some nx ∧ s.pc g = .x48 nx)) ∨
    (∃ nx, w = .signal nx true ∧ s.pc g = .x50 (some nx)) := by
  have hL := hI.loc g
  cases hpc : s.pc g <;> simp only [LI, hpc] at hL
  case rem | e23 | e24 | e25a | e25b | e26 | e27 | cs | x31 =>
    simp [hL.1] at hw
  case e18 | e22 =>
    obtain ⟨i, -, hb, -⟩ := hL; rw [hb] at hw
    exact Or.inl ⟨mem_of_mem_take_drop hw, by simp [PC.Entry]⟩
  case e19 =>
    obtain ⟨-, i, -, hb, -⟩ := hL; rw [hb] at hw
    exact Or.inl ⟨mem_of_mem_take_drop hw, by simp [PC.Entry]⟩
  case x32 =>
    obtain ⟨hl, (⟨hb, -⟩ | ⟨hb, -⟩)⟩ := hL <;> simp [hb] at hw
    exact Or.inr (Or.inl ⟨Or.inl hw, hl⟩)
  case x34 | x35 | x36 | x37 | x38 | x42 | x43 | x45 | x46 | x47 => first
      | exact Or.inr (Or.inl ⟨(hL.2.1 : XB s g _).1 w hw, hL.1⟩)
      | exact Or.inr (Or.inl ⟨hL.2.1 w hw, hL.1⟩)
  case x48 nx =>
    obtain ⟨-, ⟨B, hb, hB, hl⟩ | ⟨hb, -⟩⟩ := hL <;> simp only [hb, List.mem_append,
      List.mem_singleton, List.not_mem_nil] at hw
    rcases hw with hw | rfl
    · exact Or.inr (Or.inl ⟨hB.1 w hw, hl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨_, rfl, hl, Or.inr ⟨nx, rfl, rfl⟩⟩))
  case x50 o =>
    cases o with
    | none =>
      obtain ⟨B, hb, hB, hl⟩ | ⟨hb, -⟩ := hL <;> simp only [hb, List.mem_append,
        List.mem_singleton, List.not_mem_nil] at hw
      rcases hw with hw | rfl
      · exact Or.inr (Or.inl ⟨hB.1 w hw, hl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨_, rfl, hl, Or.inl rfl⟩))
    | some nx =>
      obtain ⟨-, ⟨B, hb, hB, hl⟩ | ⟨hb, -⟩ | ⟨hb, -⟩⟩ := hL <;> simp only [hb, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      · rcases hw with hw | rfl | rfl
        · exact Or.inr (Or.inl ⟨hB.1 w hw, hl⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨_, rfl, hl, Or.inl rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨nx, rfl, rfl⟩))
      · subst hw; exact Or.inr (Or.inr (Or.inr ⟨nx, rfl, rfl⟩))


lemma buf_node {s : Cfg h} (hI : Inv s) {g x : Proc h} {X : ℕ} (hw : W.node X x ∈ s.buf g) :
    x = g ∧ (∃ l ≤ h, X = anc g l) ∧ (s.pc g).Entry := by
  rcases buf_cases hI hw with ⟨hd, hE⟩ | ⟨hX, -⟩ | ⟨o, ho, -⟩ | ⟨nx, hn, -⟩
  · rcases mem_doorList.1 hd with h1 | h1 | ⟨l, hl, h1⟩
    · cases h1
    · cases h1
    · cases h1; exact ⟨rfl, ⟨l, hl, rfl⟩, hE⟩
  · rcases hX with h1 | h1 | h1 | ⟨r, b, h1⟩ <;> simp_all [W.isExits, W.isPromQ]
  · cases ho
  · cases hn

lemma buf_promQ {s : Cfg h} (hI : Inv s) {g : Proc h} {w : W h} (hw : w ∈ s.buf g)
    (hq : w.isPromQ = true) : s.mem.lock = some g := by
  rcases buf_cases hI hw with ⟨hd, hE⟩ | ⟨-, hl⟩ | ⟨o, rfl, -⟩ | ⟨nx, rfl, -⟩
  · rcases mem_doorList.1 hd with rfl | rfl | ⟨l, hl, rfl⟩ <;> simp [W.isPromQ] at hq
  · exact hl
  · simp [W.isPromQ] at hq
  · simp [W.isPromQ] at hq

lemma buf_lock {s : Cfg h} (hI : Inv s) {g : Proc h} {o : Option (Proc h)}
    (hw : W.lock o ∈ s.buf g) :
    s.mem.lock = some g ∧ (s.pc g = .x50 o ∨ ∃ nx, o = some nx ∧ s.pc g = .x48 nx) := by
  rcases buf_cases hI hw with ⟨hd, hE⟩ | ⟨hX, -⟩ | ⟨o', ho, hl, hp⟩ | ⟨nx, hn, -⟩
  · rcases mem_doorList.1 hd with h1 | h1 | ⟨l, hl, h1⟩ <;> cases h1
  · rcases hX with h1 | h1 | h1 | ⟨r, b, h1⟩ <;> simp_all [W.isExits, W.isPromQ]
  · cases ho; exact ⟨hl, hp⟩
  · cases hn

/-- The buffer of a process in the entry section only holds doorway writes. -/
lemma buf_entry {s : Cfg h} (hI : Inv s) {g : Proc h} (hE : (s.pc g).Entry) {w : W h}
    (hw : w ∈ s.buf g) : w ∈ doorList g := by
  have hL := hI.loc g
  cases hpc : s.pc g <;> simp only [LI, hpc] at hL <;> simp only [hpc, PC.Entry] at hE
  case e23 | e24 | e25a | e25b | e26 | e27 => simp [hL.1] at hw
  case e18 | e22 =>
    obtain ⟨i, -, hb, -⟩ := hL; rw [hb] at hw; exact mem_of_mem_take_drop hw
  case e19 =>
    obtain ⟨-, i, -, hb, -⟩ := hL; rw [hb] at hw; exact mem_of_mem_take_drop hw

lemma buf_apply {s : Cfg h} (hI : Inv s) {g x : Proc h} {b : Bool}
    (hw : W.apply x b ∈ s.buf g) : x = g ∧ ((s.pc g).Entry → b = true) := by
  rcases buf_cases hI hw with ⟨hd, hE⟩ | ⟨hX, -⟩ | ⟨o, ho, -⟩ | ⟨nx, hn, -⟩
  · rcases mem_doorList.1 hd with h1 | h1 | ⟨l, hl, h1⟩
    · cases h1
    · cases h1; exact ⟨rfl, fun _ => rfl⟩
    · cases h1
  · rcases hX with h1 | h1 | h1 | ⟨r, b, h1⟩
    · cases h1
      refine ⟨rfl, fun hE => ?_⟩
      rcases mem_doorList.1 (buf_entry hI hE hw) with h1 | h1 | ⟨l, hl, h1⟩ <;> cases h1
    · simp [W.isExits] at h1
    · simp [W.isPromQ] at h1
    · cases h1
  · cases ho
  · cases hn

/-! ### Tree arithmetic -/

lemma anc_bounds (p : Proc h) {l : ℕ} (hl : l ≤ h) : 2 ^ l ≤ anc p l ∧ anc p l < 2 ^ (l + 1) := by
  have hd : 0 < 2 ^ (h - l) := by positivity
  have e1 : 2 ^ h = 2 ^ l * 2 ^ (h - l) := by rw [← pow_add]; congr 1; omega
  have e2 : 2 ^ (l + 1) * 2 ^ (h - l) = 2 * 2 ^ h := by
    rw [← pow_add, ← pow_succ']; congr 1; omega
  have hp := p.isLt
  unfold anc leaf
  constructor
  · rw [Nat.le_div_iff_mul_le hd, ← e1]; omega
  · rw [Nat.div_lt_iff_lt_mul hd, e2]; omega

lemma level_eq {v l l' : ℕ} (h1 : 2 ^ l ≤ v ∧ v < 2 ^ (l + 1)) (h2 : 2 ^ l' ≤ v ∧ v < 2 ^ (l' + 1)) :
    l = l' := by
  rw [← Nat.log_eq_of_pow_le_of_lt_pow h1.1 h1.2, ← Nat.log_eq_of_pow_le_of_lt_pow h2.1 h2.2]

lemma anc_level_inj {p q : Proc h} {l l' : ℕ} (hl : l ≤ h) (hl' : l' ≤ h)
    (he : anc p l = anc q l') : l = l' :=
  level_eq (anc_bounds p hl) (he ▸ anc_bounds q hl')

lemma anc_inj_level {p : Proc h} {l l' : ℕ} (hl : l ≤ h) (hl' : l' ≤ h)
    (he : anc p l = anc p l') : l = l' := anc_level_inj hl hl' he

lemma anc_zero (p : Proc h) : anc p 0 = 1 := by
  have := anc_bounds p (Nat.zero_le h); simp at this; omega

lemma anc_h (p : Proc h) : anc p h = 2 ^ h + p.val := by simp [anc, leaf]

lemma anc_leaf_inj {p q : Proc h} (he : anc p h = anc q h) : p = q := by
  rw [anc_h, anc_h] at he; exact Fin.ext (by omega)

lemma anc_succ_div (p : Proc h) {l : ℕ} (hl : l < h) : anc p (l + 1) / 2 = anc p l := by
  unfold anc
  rw [Nat.div_div_eq_div_mul, ← pow_succ]; congr 2; omega

lemma target_zero (v : ℕ) : target v 0 = v := rfl

lemma anc_child (p : Proc h) {l : ℕ} (hl : l < h) :
    ∃ j, 1 ≤ j ∧ j ≤ 2 ∧ target (anc p l) j = anc p (l + 1) := by
  have h1 := anc_succ_div p hl
  rcases Nat.mod_two_eq_zero_or_one (anc p (l + 1)) with h2 | h2
  · exact ⟨1, le_rfl, by norm_num, by simp [target]; omega⟩
  · exact ⟨2, by norm_num, le_rfl, by simp [target]; omega⟩

lemma target_bounds {v l j : ℕ} (hv : 2 ^ l ≤ v ∧ v < 2 ^ (l + 1)) (hj : j ≠ 0) :
    2 ^ (l + 1) ≤ target v j ∧ target v j < 2 ^ (l + 1 + 1) := by
  rw [pow_succ, pow_succ 2 (l + 1)]
  unfold target; split_ifs <;> omega

/-- A node read at statement 34 at level `l'` (read number `j'`) is at level `l'` (`j' = 0`) or
`l' + 1` (`j' ≠ 0`). -/
lemma target_eq_anc {q p : Proc h} {l' j' m : ℕ} (hl' : l' ≤ h) (hm : m ≤ h)
    (he : target (anc q l') j' = anc p m) : (j' = 0 ∧ l' = m) ∨ (j' ≠ 0 ∧ l' + 1 = m) := by
  by_cases hj : j' = 0
  · subst hj; exact Or.inl ⟨rfl, anc_level_inj hl' hm he⟩
  · exact Or.inr ⟨hj, level_eq (target_bounds (anc_bounds q hl') hj) (he ▸ anc_bounds p hm)⟩


/-! ### How a step changes the configuration -/

lemma cas_of_nil (s : Cfg h) {g : Proc h} (c : PC h) (hb : s.buf g = []) :
    s.cas g c = if s.mem.lock = none then
      { mem := { s.mem with lock := some g }, buf := s.buf, pc := Function.update s.pc g .cs,
        ent := s.ent + 1 } else s.goto g c := by
  have hu : Function.update s.buf g [] = s.buf := by
    rw [← hb]; exact Function.update_eq_self g s.buf
  unfold Cfg.cas; simp only [hb, Mem.view_nil, hu]
  split_ifs <;> rfl

lemma barrier_cases (s : Cfg h) (g : Proc h) (c : PC h) :
    (s.buf g = [] ∧ s.barrier g c = s.goto g c) ∨
    (∃ w b, s.buf g = w :: b ∧ s.barrier g c = s.flush g) := by
  unfold Cfg.barrier
  cases hb : s.buf g with
  | nil => exact Or.inl ⟨rfl, by simp⟩
  | cons w b => exact Or.inr ⟨w, b, rfl, by simp⟩

/-- Every event either performs the oldest write of some store buffer, or leaves the memory
unchanged, or is a successful CAS on `lock` (with an empty store buffer). -/
lemma next_mem_cases {s : Cfg h} (hI : Inv s) (e : Ev h) :
    (∃ g w b, s.buf g = w :: b ∧ s.next e = s.flush g) ∨ (s.next e).mem = s.mem ∨
    (∃ g, s.mem.lock = none ∧ (s.next e).mem = { s.mem with lock := some g }) := by
  cases e with
  | flush g =>
    cases hb : s.buf g with
    | nil => exact Or.inr (Or.inl (by simp [Cfg.next, flush_of_nil s g hb]))
    | cons w b => exact Or.inl ⟨g, w, b, hb, rfl⟩
  | step g =>
    have hL := hI.loc g
    cases hpc : s.pc g <;> simp only [Cfg.next, Cfg.stepProc, hpc] <;>
      simp only [LI, hpc] at hL
    case e22 =>
      rcases barrier_cases s g .e23 with ⟨-, hb⟩ | ⟨w, b, hw, hb⟩
      · exact Or.inr (Or.inl (by simp [hb]))
      · exact Or.inl ⟨g, w, b, hw, hb⟩
    case x50 =>
      rcases barrier_cases s g .rem with ⟨-, hb⟩ | ⟨w, b, hw, hb⟩
      · exact Or.inr (Or.inl (by simp [hb]))
      · exact Or.inl ⟨g, w, b, hw, hb⟩
    case e23 | e26 =>
      rw [cas_of_nil s _ hL.1]; split_ifs with hl
      · exact Or.inr (Or.inr ⟨g, hl, rfl⟩)
      · exact Or.inr (Or.inl rfl)
    case x35 l cands =>
      cases cands <;> exact Or.inr (Or.inl (by simp only; repeat (first | rfl | split)))
    all_goals (refine Or.inr (Or.inl ?_); repeat (first | rfl | split))


lemma view_of_nil {s : Cfg h} {g : Proc h} (hb : s.buf g = []) : s.view g = s.mem := by
  simp [Cfg.view, hb]

/-- How a process enters the critical section: a successful CAS (statements 23, 26) or
statement 27 with `signal[x]` set. -/
lemma enters_cases {s : Cfg h} (hI : Inv s) (e : Ev h) {x : Proc h} (h1 : s.pc x ≠ .cs)
    (h2 : (s.next e).pc x = .cs) :
    e = .step x ∧ (s.pc x).Entry ∧
    (((s.pc x = .e23 ∨ s.pc x = .e26) ∧ s.mem.lock = none ∧
        s.next e = { mem := { s.mem with lock := some x }, buf := s.buf,
                     pc := Function.update s.pc x .cs, ent := s.ent + 1 }) ∨
      (s.pc x = .e27 ∧ s.mem.signal x = true ∧ s.next e = { (s.goto x PC.cs) with ent := s.ent + 1 })) := by
  have he := eq_step_of_pc_ne s e (by rw [h2]; exact Ne.symm h1)
  subst he
  have hL := hI.loc x
  refine ⟨rfl, ?_⟩
  cases hpc : s.pc x <;> simp only [LI, hpc] at hL <;>
    simp only [Cfg.next, Cfg.stepProc, hpc] at h2 ⊢ <;> simp only [PC.Entry, true_and]
  case e23 | e26 =>
    rw [cas_of_nil s _ hL.1] at h2 ⊢
    split_ifs at h2 ⊢ with hl
    · exact Or.inl ⟨by simp, hl, rfl⟩
    · simp at h2
  case e27 =>
    rw [view_of_nil hL.1] at h2 ⊢
    split_ifs at h2 ⊢ with hs
    · first | exact Or.inr ⟨rfl, hs, rfl⟩ | exact Or.inr ⟨hs, rfl⟩
    · exact absurd h2 (by simp [hpc])
  case e22 =>
    rcases barrier_cases s x .e23 with ⟨-, hb⟩ | ⟨w, b, -, hb⟩ <;> rw [hb] at h2 <;> simp [hpc] at h2
  case x50 =>
    rcases barrier_cases s x .rem with ⟨-, hb⟩ | ⟨w, b, -, hb⟩ <;> rw [hb] at h2 <;> simp [hpc] at h2
  case cs => exact absurd hpc h1
  case x35 l cands =>
    cases cands <;> simp only at h2 <;> (repeat' split at h2) <;> simp at h2
  all_goals (repeat' split at h2) <;> simp at h2


/-! ### The exit section reads its nodes in program order -/

/-- `x` is in its critical or exit section and has not yet performed the read number `j` at
level `l` of statement 34. -/
def PreRead (l j : ℕ) : PC h → Prop
  | .cs | .x31 | .x32 => True
  | .x34 l' j' _ => l' < l ∨ (l' = l ∧ j' ≤ j)
  | .x35 l' _ | .x36 l' _ _ | .x37 l' _ _ | .x38 l' _ _ => l' < l
  | _ => False

lemma PreRead.incsx {s : Cfg h} {x : Proc h} {l j : ℕ} (hp : PreRead l j (s.pc x)) : s.InCSX x := by
  unfold Cfg.InCSX
  cases hpc : s.pc x <;> simp_all [PreRead, PC.Exit]

/-- Leaving `PreRead l j` is exactly performing the read number `j` at level `l`. -/
lemma preRead_step (s : Cfg h) (e : Ev h) {x : Proc h} {l j : ℕ} (hl : l < h) (hj : j ≤ 2)
    (h1 : PreRead l j (s.pc x)) (h2 : ¬ PreRead l j ((s.next e).pc x)) :
    e = .step x ∧ ∃ acc, s.pc x = .x34 l j acc := by
  have he : e = .step x := by
    by_contra hne; rw [next_pc_ne s e hne] at h2; exact h2 h1
  subst he
  refine ⟨rfl, ?_⟩
  cases hpc : s.pc x <;> simp only [hpc, PreRead] at h1 <;>
    simp only [Cfg.next, Cfg.stepProc, hpc] at h2
  case cs => simp [PreRead] at h2
  case x31 => simp [PreRead] at h2
  case x32 => simp only [issue_pc, Function.update_self] at h2; split_ifs at h2 <;> simp [PreRead] at h2 <;> omega
  case x34 l' j' acc =>
    simp only [goto_pc, Function.update_self] at h2
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> split_ifs at h2 <;> simp [PreRead] at h2
    all_goals first | omega | exact ⟨acc, by rw [show j' = j by omega]⟩
  case x35 l' cands =>
    exfalso
    cases cands <;> simp only [goto_pc, Function.update_self] at h2 <;> split_ifs at h2 <;>
      simp [PreRead] at h2 <;> omega
  all_goals exfalso; simp only [goto_pc, issue_pc, Function.update_self] at h2
  all_goals (try split_ifs at h2) <;> simp [PreRead] at h2 <;> omega


/-! ### The doorway writes of a waiting process -/

lemma mem_take_drop_iff {α : Type*} {L : List α} (hL : L.Nodup) {j k i : ℕ} {a : α}
    (hj : L[j]? = some a) : a ∈ (L.take k).drop i ↔ i ≤ j ∧ j < k := by
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.1 hj
  constructor
  · intro hm
    obtain ⟨m, hm, he⟩ := List.getElem_of_mem hm
    simp only [List.getElem_drop, List.getElem_take] at he
    simp only [List.length_drop, List.length_take] at hm
    have := (hL.getElem_inj_iff).1 he
    omega
  · rintro ⟨h1, h2⟩
    have hlen : j - i < ((L.take k).drop i).length := by
      simp only [List.length_drop, List.length_take]; omega
    have : ((L.take k).drop i)[j - i] = L[j] := by
      simp only [List.getElem_drop, List.getElem_take]; congr 1; omega
    rw [← this]; exact List.getElem_mem hlen

lemma doorList_node (q : Proc h) {l : ℕ} (hl : l ≤ h) :
    (doorList q)[2 + (h - l)]? = some (.node (anc q l) q) := by
  simp only [doorList]
  rw [show 2 + (h - l) = (h - l) + 1 + 1 by omega]
  simp only [List.getElem?_cons_succ, List.getElem?_map]
  simp [show h - (h - l) = l by omega]

lemma doorList_nodup (q : Proc h) : (doorList q).Nodup := by
  simp only [doorList, List.nodup_cons]
  refine ⟨by simp, by simp, ?_⟩
  refine List.Nodup.map_on ?_ (List.nodup_reverse.2 List.nodup_range)
  intro a ha b hb he
  simp only [List.mem_reverse, List.mem_range] at ha hb
  simp only [W.node.injEq, and_true] at he
  exact anc_inj_level (by omega) (by omega) he

/-- The program counters at which the doorway write to the node at level `l` has been issued. -/
def DoneRegion (l : ℕ) : PC h → Prop
  | .e19 l' => l' < l
  | .e22 | .e23 | .e24 | .e25a _ | .e25b _ | .e26 | .e27 => True
  | _ => False

/-- `p` is in its entry section and its doorway write to the node at level `l` on its path has
been performed (in the current passage). -/
def Done (s : Cfg h) (p : Proc h) (l : ℕ) : Prop :=
  l ≤ h ∧ DoneRegion l (s.pc p) ∧ W.node (anc p l) p ∉ s.buf p

lemma doneRegion_entry {l : ℕ} {c : PC h} (hc : DoneRegion l c) : c.Entry := by
  cases c <;> simp_all [DoneRegion, PC.Entry]

/-- In the doorway, the doorway write at level `l` is no longer buffered iff it was performed:
then all earlier doorway writes were performed. -/
lemma door_idx {s : Cfg h} {p : Proc h} {l : ℕ} (hd : Done s p l) :
    ∀ k i, s.buf p = ((doorList p).take k).drop i → 2 + (h - l) < k → 2 + (h - l) < i := by
  intro k i hb hk
  obtain ⟨hl, -, hn⟩ := hd
  by_contra hi
  apply hn
  rw [hb, mem_take_drop_iff (doorList_nodup p) (doorList_node p hl)]
  exact ⟨by omega, hk⟩

lemma Done.entry_apply {s : Cfg h} (hI : Inv s) {p : Proc h} {l : ℕ} (hd : Done s p l) :
    (s.pc p).Entry ∧ s.mem.apply p = true := by
  refine ⟨doneRegion_entry hd.2.1, ?_⟩
  have hL := hI.loc p
  have hR := hd.2.1
  cases hpc : s.pc p <;> simp only [LI, hpc] at hL <;> simp only [DoneRegion, hpc] at hR
  case e23 | e24 | e25a | e25b | e26 | e27 => exact hL.2
  case e19 l' =>
    obtain ⟨-, i, -, hb, ha, -⟩ := hL
    have := door_idx hd _ i hb (by have := hd.1; omega)
    exact ha.2 (by omega)
  case e22 =>
    obtain ⟨i, -, hb, ha, -⟩ := hL
    have := door_idx hd _ i hb (by have := hd.1; omega)
    exact ha.2 (by omega)

lemma Done.succ {s : Cfg h} (hI : Inv s) {p : Proc h} {l : ℕ} (hd : Done s p l) (hl : l + 1 ≤ h) :
    Done s p (l + 1) := by
  refine ⟨hl, ?_, ?_⟩
  · have hR := hd.2.1
    cases hpc : s.pc p <;> simp only [DoneRegion, hpc] at hR ⊢; all_goals omega
  · have hL := hI.loc p
    have hR := hd.2.1
    have key : ∀ k i, s.buf p = ((doorList p).take k).drop i → 2 + (h - l) < k →
        W.node (anc p (l + 1)) p ∉ s.buf p := by
      intro k i hb hk
      have := door_idx hd k i hb hk
      rw [hb, mem_take_drop_iff (doorList_nodup p) (doorList_node p hl)]
      omega
    cases hpc : s.pc p <;> simp only [LI, hpc] at hL <;> simp only [DoneRegion, hpc] at hR
    case e23 | e24 | e25a | e25b | e26 | e27 => simp [hL.1]
    case e19 l' =>
      obtain ⟨-, i, -, hb, -⟩ := hL; exact key _ i hb (by have := hd.1; omega)
    case e22 =>
      obtain ⟨i, -, hb, -⟩ := hL; exact key _ i hb (by have := hd.1; omega)

lemma Done.of_waiting {s : Cfg h} (hI : Inv s) {p : Proc h} (hw : (s.pc p).Waiting) {l : ℕ}
    (hl : l ≤ h) : Done s p l := by
  have hL := hI.loc p
  cases hpc : s.pc p <;> simp only [LI, hpc] at hL <;> simp only [PC.Waiting, hpc] at hw <;>
    exact ⟨hl, by simp [DoneRegion, hpc], by simp [hL.1]⟩


lemma next_buf_sub (s : Cfg h) (e : Ev h) {p : Proc h} (he : e ≠ .step p) {w : W h}
    (hw : w ∈ (s.next e).buf p) : w ∈ s.buf p := by
  cases e with
  | step g =>
    have : p ≠ g := by rintro rfl; exact he rfl
    simpa [Cfg.next, stepProc_buf_ne s this] using hw
  | flush g =>
    simp only [Cfg.next] at hw
    by_cases hg : p = g
    · subst hg
      unfold Cfg.flush at hw; split at hw
      · exact hw
      · rename_i w' b hb; simp at hw; rw [hb]; exact List.mem_cons_of_mem _ hw
    · rwa [flush_buf_ne s hg] at hw

lemma next_flush_self_node {s : Cfg h} {p : Proc h} {w : W h} {b : List (W h)}
    (hb : s.buf p = w :: b) {X : ℕ} (h1 : W.node X p ∈ s.buf p) (h2 : W.node X p ∉ (s.flush p).buf p) :
    (s.flush p).mem.node X = some p := by
  rw [flush_of_cons s p hb] at h2 ⊢
  simp only [Function.update_self] at h2
  rw [hb] at h1
  rcases List.mem_cons.1 h1 with rfl | h1
  · simp [write_node]
  · exact absurd h1 h2

/-- `Done` persists while `p` stays in its entry section. -/
lemma Done.step {s : Cfg h} (hI : Inv s) {p : Proc h} {l : ℕ} (hd : Done s p l) (e : Ev h)
    (hE : ((s.next e).pc p).Entry) : Done (s.next e) p l := by
  obtain ⟨hl, hR, hn⟩ := hd
  by_cases he : e = .step p
  · subst he
    have hL := hI.loc p
    refine ⟨hl, ?_⟩
    cases hpc : s.pc p <;> simp only [DoneRegion, hpc] at hR <;> simp only [LI, hpc] at hL <;>
      simp only [Cfg.next, Cfg.stepProc, hpc] at hE ⊢
    case e19 l' =>
      refine ⟨?_, ?_⟩
      · split_ifs <;> simp [DoneRegion]; omega
      · simp only [issue_buf, Function.update_self, List.mem_append, List.mem_singleton, not_or]
        refine ⟨hn, fun h' => ?_⟩
        simp only [W.node.injEq, and_true] at h'
        have := anc_inj_level (p := p) (by omega) hL.1 h'; omega
    case e22 =>
      rcases barrier_cases s p .e23 with ⟨-, hb⟩ | ⟨w, b, -, hb⟩ <;> rw [hb] <;> rw [hb] at hE
      · exact ⟨by simp [DoneRegion], by simpa using hn⟩
      · refine ⟨by simp [hpc, DoneRegion], fun h' => hn (next_buf_sub s (.flush p) (by simp) h')⟩
    case e23 | e26 =>
      rw [cas_of_nil s _ hL.1] at hE ⊢
      split_ifs at hE ⊢ <;> simp [PC.Entry] at hE
      simp [DoneRegion, hL.1]
    case e27 =>
      split_ifs at hE ⊢ <;> simp [PC.Entry] at hE
      simp [DoneRegion, hpc, hL.1]
    all_goals (try split_ifs) <;> simp [DoneRegion, hL.1]
  · refine ⟨hl, ?_, fun h' => hn (next_buf_sub s e he h')⟩
    rw [next_pc_ne s e he]; exact hR

/-- The step at which `Done` starts to hold performs the doorway write of `p` to its node. -/
lemma Done.start {s : Cfg h} (hI : Inv s) {p : Proc h} {l : ℕ} (e : Ev h) (hnd : ¬ Done s p l)
    (hd : Done (s.next e) p l) : (s.next e).mem.node (anc p l) = some p := by
  obtain ⟨hl, hR, hn⟩ := hd
  have hL := hI.loc p
  by_cases he : e = .step p
  · subst he
    cases hpc : s.pc p <;> simp only [LI, hpc] at hL <;> simp only [Cfg.next, Cfg.stepProc, hpc] at hR hn ⊢
    case rem | e18 => simp [DoneRegion] at hR; try omega
    case e19 l' =>
      exfalso
      simp only [issue_buf, Function.update_self, List.mem_append, List.mem_singleton, not_or] at hn
      apply hnd
      refine ⟨hl, ?_, hn.1⟩
      simp only [DoneRegion, hpc]
      simp only [issue_pc, Function.update_self] at hR
      by_contra hll
      apply hn.2
      split_ifs at hR with h0 <;> simp [DoneRegion] at hR
      · congr; omega
      · congr; omega
    case e22 =>
      rcases barrier_cases s p .e23 with ⟨-, hb⟩ | ⟨w, b, hb', hb⟩ <;> rw [hb] at hR hn ⊢
      · exfalso; exact hnd ⟨hl, by simp [hpc, DoneRegion], by simpa using hn⟩
      · refine next_flush_self_node hb' ?_ hn
        by_contra hm; exact hnd ⟨hl, by simp [hpc, DoneRegion], hm⟩
    case e23 | e24 | e25a | e25b | e26 | e27 =>
      exfalso; exact hnd ⟨hl, by simp [hpc, DoneRegion], by simp [hL.1]⟩
    case x35 l' cands =>
      exfalso; cases cands <;> simp only at hR <;> split_ifs at hR <;> simp [DoneRegion] at hR
    case x45 =>
      exfalso; split at hR <;> simp [DoneRegion] at hR
    case x50 =>
      exfalso
      rcases barrier_cases s p .rem with ⟨-, hb⟩ | ⟨w, b, -, hb⟩ <;> rw [hb] at hR <;>
        simp [DoneRegion, hpc] at hR
    all_goals exfalso; (try split_ifs at hR) <;> simp [DoneRegion] at hR
  · rw [next_pc_ne s e he] at hR
    have hin : W.node (anc p l) p ∈ s.buf p := by
      by_contra hm; exact hnd ⟨hl, hR, hm⟩
    cases e with
    | step g =>
      have : p ≠ g := by rintro rfl; exact he rfl
      exfalso; apply hn; simpa [Cfg.next, stepProc_buf_ne s this] using hin
    | flush g =>
      by_cases hg : p = g
      · subst hg
        cases hb : s.buf p with
        | nil => simp [hb] at hin
        | cons w b => exact next_flush_self_node hb hin hn
      · exfalso; apply hn; simpa [Cfg.next, flush_buf_ne s hg] using hin


/-! ### Applying processes and node writers -/

lemma take_drop_head {α : Type*} {L : List α} {k i : ℕ} {w : α} {b : List α}
    (hb : (L.take k).drop i = w :: b) : L[i]? = some w := by
  have h1 : ((L.take k).drop i)[0]? = some w := by rw [hb]; rfl
  rw [List.getElem?_drop, List.getElem?_take] at h1
  split_ifs at h1 with hik
  · simpa using h1

/-- A process in the doorway whose oldest buffered write is a node write has performed its
write `apply[g] ← true`. -/
lemma apply_of_head_node {s : Cfg h} (hI : Inv s) {g x : Proc h} {X : ℕ} {b : List (W h)}
    (hb : s.buf g = W.node X x :: b) : s.mem.apply g = true := by
  have hL := hI.loc g
  have key : ∀ k, DoorLI s g k → s.mem.apply g = true := by
    rintro k ⟨i, -, hbi, ha, -⟩
    rw [hb] at hbi
    have := take_drop_head hbi.symm
    apply ha.2
    by_contra hi
    interval_cases i <;> simp [doorList] at this
  cases hpc : s.pc g <;> simp only [LI, hpc] at hL
  case e18 => exact key _ hL
  case e19 => exact key _ hL.2
  case e22 => exact key _ hL
  all_goals exfalso; obtain ⟨-, -, hE⟩ := buf_node hI (hb ▸ List.mem_cons_self ..)
  all_goals simp [hpc, PC.Entry] at hE
  all_goals simp [hL.1] at hb


/-- A process that stays in its entry section keeps `apply = true` (in memory). -/
lemma apply_step {s : Cfg h} (hI : Inv s) (e : Ev h) {r : Proc h} (hE : (s.pc r).Entry)
    (ha : s.mem.apply r = true) : (s.next e).mem.apply r = true := by
  rcases next_mem_cases hI e with ⟨g, w, b, hb, he⟩ | hm | ⟨g, -, hm⟩
  · rw [he, flush_of_cons s g hb]
    simp only [write_apply]
    split
    · rename_i q' b' 
      split_ifs with hq
      · subst hq
        obtain ⟨rfl, hb'⟩ := buf_apply hI (hb ▸ List.mem_cons_self ..)
        exact hb' hE
      · exact ha
    · exact ha
  · rw [hm]; exact ha
  · rw [hm]; exact ha

/-- The step at which a node starts to hold `r` performs a doorway write of `r`; afterwards `r`
is in its entry section with `apply[r] = true`. -/
lemma node_writer {s : Cfg h} (hI : Inv s) (e : Ev h) {X : ℕ} {r : Proc h}
    (h1 : s.mem.node X ≠ some r) (h2 : (s.next e).mem.node X = some r) :
    (∃ l ≤ h, X = anc r l) ∧ ((s.next e).pc r).Entry ∧ (s.next e).mem.apply r = true := by
  rcases next_mem_cases hI e with ⟨g, w, b, hb, he⟩ | hm | ⟨g, -, hm⟩
  · rw [he, flush_of_cons s g hb] at h2 ⊢
    simp only [write_node] at h2
    split at h2
    · rename_i i v
      split_ifs at h2 with hi
      · subst hi; cases h2
        obtain ⟨rfl, hX, hE⟩ := buf_node hI (hb ▸ List.mem_cons_self ..)
        refine ⟨hX, hE, ?_⟩
        simp only [write_apply]
        exact apply_of_head_node hI hb
      · exact absurd h2 h1
    · exact absurd h2 h1
  · rw [hm] at h2; exact absurd h2 h1
  · rw [hm] at h2; exact absurd h2 h1

/-- Nodes never become empty again. -/
lemma node_some_step {s : Cfg h} (hI : Inv s) (e : Ev h) {X : ℕ} {r : Proc h}
    (h1 : s.mem.node X = some r) : ∃ r', (s.next e).mem.node X = some r' := by
  rcases next_mem_cases hI e with ⟨g, w, b, hb, he⟩ | hm | ⟨g, -, hm⟩
  · rw [he, flush_of_cons s g hb]
    simp only [write_node]
    split
    · split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨r, h1⟩
    · exact ⟨r, h1⟩
  · rw [hm]; exact ⟨r, h1⟩
  · rw [hm]; exact ⟨r, h1⟩

/-- Statement 34 reads nodes from memory: the exit section buffers no node writes. -/
lemma view_node_exit {s : Cfg h} (hI : Inv s) {g : Proc h} {l j : ℕ} {acc : List (Proc h)}
    (hpc : s.pc g = .x34 l j acc) (X : ℕ) : (s.view g).node X = s.mem.node X := by
  unfold Cfg.view
  apply view_node_of
  intro w hw
  cases w with
  | node i v =>
    obtain ⟨-, -, hE⟩ := buf_node hI hw; simp [hpc, PC.Entry] at hE
  | _ => rfl

end Podc.ConstantBarriersMutex.BW
