import Papers.PODC2019.RMESubLogBoth.InvDefs

/-!
# Basic lemmas about the invariant
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

@[simp] lemma PC.ovr_l14 (y m : ℕ) : (PC.l14 y m : PC k).ovr = some m := rfl
@[simp] lemma PC.ovr_l49 (y m : ℕ) : (PC.l49 y m : PC k).ovr = some m := rfl

lemma Cfg.vp_def (c : Cfg k) (q : Fin k) : c.vp q = match (c.pc q).ovr with
    | some m => .node m
    | none => match c.node q with
      | some y => c.pred y
      | none => .nil := rfl

lemma Cfg.vp_of_ovr_none {c : Cfg k} {q : Fin k} (h : (c.pc q).ovr = none) {y : ℕ}
    (hn : c.node q = some y) : c.vp q = c.pred y := by
  simp [Cfg.vp, h, hn]

lemma Cfg.vp_of_ovr_some {c : Cfg k} {q : Fin k} {m : ℕ} (h : (c.pc q).ovr = some m) :
    c.vp q = .node m := by
  simp [Cfg.vp, h]

/-- Congruence for `vp`. -/
lemma vp_congr {c c' : Cfg k} {q : Fin k} (ho : (c'.pc q).ovr = (c.pc q).ovr)
    (hn : c'.node q = c.node q) (hp : ∀ y, c.node q = some y → c'.pred y = c.pred y) :
    c'.vp q = c.vp q := by
  unfold Cfg.vp
  rw [ho, hn]
  cases h : (c.pc q).ovr with
  | some m => rfl
  | none =>
    cases h2 : c.node q with
    | none => rfl
    | some y => exact hp y h2

lemma Bh_congr {c c' : Cfg k} (hn : c'.node = c.node) (hv : ∀ q, c'.vp q = c.vp q) :
    c'.Bh = c.Bh := by
  funext y z
  simp only [Cfg.Bh, hn, hv]

lemma Act_congr {c c' : Cfg k} (hn : c'.node = c.node) : c'.Act = c.Act := by
  funext y; simp only [Cfg.Act, hn]

lemma Rel_congr {c c' : Cfg k} (hp : c'.pred = c.pred) (hc : c'.csig = c.csig) :
    c'.Rel = c.Rel := by
  funext z; simp only [Cfg.Rel, hp, hc]

lemma InH_congr {c c' : Cfg k} (hn : c'.node = c.node) (hv : ∀ q, c'.vp q = c.vp q)
    (hp : c'.pred = c.pred) (hc : c'.csig = c.csig) (ht : c'.tail = c.tail) :
    c'.InH = c.InH := by
  funext y
  simp only [Cfg.InH, Act_congr hn, Bh_congr hn hv, Rel_congr hp hc, hp, hc, ht]

/-! ### Simple consequences of the invariant -/

section
variable {c : Cfg k} {own : ℕ → ℕ}

lemma Glob.node_inj (hG : Glob c own) {q q' : Fin k} {a : ℕ} (h : c.node q = some a)
    (h' : c.node q' = some a) : q = q' :=
  Fin.ext ((hG.own q a h).symm.trans (hG.own q' a h'))

lemma Glob.pos_of_bh (hG : Glob c own) {y z : ℕ} (h : c.Bh y z) : 0 < y ∧ y < c.nxt := by
  obtain ⟨q, hq, -⟩ := h; exact hG.nodeLt q y hq

lemma Glob.not_rel_of_act (hG : Glob c own) {y : ℕ} (h : c.Act y) (hc : c.csig y = false) :
    ¬ c.Rel y := by
  rintro ⟨-, h2⟩; simp [hc] at h2

/-- A node with a `Pred` that is a node, `&InCS`, `&Crash` or `NIL` is the node of some port. -/
lemma Glob.act_of_pred (hG : Glob c own) {y : ℕ} (h : c.pred y ≠ .exit) (h0 : c.pred y ≠ .nil) :
    c.Act y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · exact absurd hG.special.1 h
  · by_cases hn : y < c.nxt
    · rcases hG.table y hy hn with h1 | h1
      · exact h1
      · exact absurd h1.1 h
    · exact absurd (hG.fresh y (not_lt.mp hn)).1 h0

lemma Glob.not_rel_of_pred_ne {y : ℕ} (h : c.pred y ≠ .exit) : ¬ c.Rel y := fun h' => h h'.1

lemma rel_special (hG : Glob c own) : c.Rel special := ⟨hG.special.1, hG.special.2.1⟩

/-- Local invariants give the node of a port at its program counter. -/
lemma LI.node_of_pc_l49 {q : Fin k} {y m : ℕ} (hL : LI c own q) (h : c.pc q = .l49 y m) :
    c.node q = some y ∧ c.pred y = .crash := by
  unfold LI at hL; rw [h] at hL; exact ⟨hL.1, hL.2.1⟩

lemma LI.node_of_pc_l14 {q : Fin k} {y m : ℕ} (hL : LI c own q) (h : c.pc q = .l14 y m) :
    c.node q = some y ∧ c.pred y = .nil := by
  unfold LI at hL; rw [h] at hL; exact ⟨hL.1, hL.2.1⟩

/-- `vp` agrees with `Pred` unless the port is at line 14 or 49. -/
lemma vp_cases (hL : ∀ q, LI c own q) (q : Fin k) {y : ℕ} (hn : c.node q = some y) :
    c.vp q = c.pred y ∨ (∃ m, c.pc q = .l14 y m ∧ c.vp q = .node m ∧ c.pred y = .nil) ∨
      (∃ m, c.pc q = .l49 y m ∧ c.vp q = .node m ∧ c.pred y = .crash) := by
  cases h : c.pc q with
  | l14 y' m =>
    have := (hL q).node_of_pc_l14 h
    rw [hn] at this; obtain ⟨hy, hp⟩ := this; cases hy
    exact .inr (.inl ⟨m, rfl, Cfg.vp_of_ovr_some (by simp [h]), hp⟩)
  | l49 y' m =>
    have := (hL q).node_of_pc_l49 h
    rw [hn] at this; obtain ⟨hy, hp⟩ := this; cases hy
    exact .inr (.inr ⟨m, rfl, Cfg.vp_of_ovr_some (by simp [h]), hp⟩)
  | _ => exact .inl (Cfg.vp_of_ovr_none (by simp [h, PC.ovr]) hn)

/-- `Pred = node z` means `Bh`. -/
lemma bh_of_pred (hG : Glob c own) (hL : ∀ q, LI c own q) {y z : ℕ}
    (h : c.pred y = .node z) : c.Bh y z := by
  obtain ⟨q, hq⟩ := hG.act_of_pred (y := y) (by simp [h]) (by simp [h])
  refine ⟨q, hq, ?_⟩
  rcases vp_cases hL q hq with h1 | ⟨m, -, -, h2⟩ | ⟨m, -, -, h2⟩
  · rw [h1, h]
  · rw [h] at h2; cases h2
  · rw [h] at h2; cases h2

/-- `Bh` means `Pred = node z`, or line 14, or line 49. -/
lemma pred_of_bh (hL : ∀ q, LI c own q) {y z : ℕ} (h : c.Bh y z) :
    c.pred y = .node z ∨ (∃ q, c.node q = some y ∧ c.pc q = .l14 y z ∧ c.pred y = .nil) ∨
      (∃ q, c.node q = some y ∧ c.pc q = .l49 y z ∧ c.pred y = .crash) := by
  obtain ⟨q, hq, hv⟩ := h
  rcases vp_cases hL q hq with h1 | ⟨m, h2, h3, h4⟩ | ⟨m, h2, h3, h4⟩
  · exact .inl (h1 ▸ hv)
  · rw [hv] at h3; cases h3; exact .inr (.inl ⟨q, hq, h2, h4⟩)
  · rw [hv] at h3; cases h3; exact .inr (.inr ⟨q, hq, h2, h4⟩)

lemma not_bh_of_rel (hL : ∀ q, LI c own q) {y z : ℕ} (h : c.Rel y) : ¬ c.Bh y z := by
  intro hb
  rcases pred_of_bh hL hb with h1 | ⟨_, _, _, h1⟩ | ⟨_, _, _, h1⟩ <;> rw [h.1] at h1 <;> cases h1

end

/-! ### The initial configuration -/

lemma inv_init : Inv (Cfg.init : Cfg k) := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · refine
      { own := by simp [Cfg.init]
        nodeLt := by simp [Cfg.init]
        fresh := by intro a ha; simp [Cfg.init] at ha ⊢; simp [special]; omega
        special := by simp [Cfg.init]
        nxtPos := by simp [Cfg.init]
        table := by intro a h1 h2; simp [Cfg.init] at h2; omega
        nnPred := by intro a h; simp [Cfg.init] at h ⊢; simp [h]
        csigPred := by intro a h; simp [Cfg.init] at h ⊢; simp [h]
        ioNN := by intro a h; simp [Cfg.init] at h ⊢; split_ifs at h <;> simp_all
        tailLt := by simp [Cfg.init]
        bhLt := by rintro y z ⟨q, hq, -⟩; simp [Cfg.init] at hq
        bhInj := by rintro y y' z ⟨q, hq, -⟩; simp [Cfg.init] at hq
        noBhTail := by rintro y ⟨q, hq, -⟩; simp [Cfg.init] at hq
        hUniq := by rintro y y' ⟨⟨q, hq⟩, -⟩; simp [Cfg.init] at hq
        relTail := by rintro - y ⟨⟨q, hq⟩, -⟩; simp [Cfg.init] at hq
        wf := ⟨fun a => Acc.intro _ (fun b ⟨q, hq, _⟩ => by simp [Cfg.init] at hq)⟩
        holder := by intro q h; simp [Cfg.init, PC.InR] at h }
  · intro q; simp [LI, Cfg.init]

end Podc.RMESubLogBoth
