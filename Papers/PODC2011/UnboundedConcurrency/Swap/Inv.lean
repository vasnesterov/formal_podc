import Papers.PODC2011.UnboundedConcurrency.Swap.Model

/-!
# The inductive invariant of Algorithm 1

`Inv x C` is one inductive invariant of the reachable configurations of Algorithm 1 (inputs `x`).
It contains, as state predicates, the facts the paper proves about executions:

* `l2` is Lemma 2 in "forward" form: a process `j` whose depth is `≥ maxdepth_i` only ever tries
  to capture nodes larger than `cap_i`;
* `blk_right` and `lemma1` are the core of Lemma 1: a node `w` that some process tried to capture
  (or recorded) lies in the right subtree of `v` only if a node `≥ v` of the depth of `v` has been
  recorded in `accessed`; and a returning process that blocked `y` while having captured a node of
  `y`'s right subtree did so only after the capturer of `y` moved past `y`;
* `excl`, `tst_true`, `lost_cap`, `blk_tst`: who set which test-and-set bit.

Lemma 3 (`tryRet_unique`) is derived from the invariant.
-/

namespace Podc.UnboundedConcurrency.Swap

open Cslib.SharedMemory Cslib.SharedMemory.Arrival Cfg' Node

variable {V : Type}

namespace Loc

/-- The depth of a process (`none` before Line 1). -/
def dep : Loc V → Option ℕ
  | .start _ => none
  | .scan _ d _ | .write _ d _ | .tas _ d _ | .upd _ d _ _ => some d
  | .readMax d _ | .retTas d _ _ _ | .readReg d _ _ _ | .done d _ _ _ _ => some d

/-- The node the process currently tries to capture, or has captured (`cap`), from Line 3 on;
`none` while scanning. -/
def sel : Loc V → Option Node
  | .start _ | .scan _ _ _ => none
  | .write _ _ c | .tas _ _ c | .upd _ _ c _ => some c
  | .readMax _ c | .retTas _ c _ _ | .readReg _ c _ _ | .done _ c _ _ _ => some c

/-- The node the process has captured (won its test-and-set at Line 4), if any. -/
def cap : Loc V → Option Node
  | .upd _ _ c w => if w then some c else none
  | .readMax _ c | .retTas _ c _ _ | .readReg _ c _ _ | .done _ c _ _ _ => some c
  | _ => none

/-- `(cap, maxdepth)` of a process that has read `max_depth` in Line 7. -/
def rinfo : Loc V → Option (Node × ℕ)
  | .retTas _ c m _ | .readReg _ c m _ | .done _ c m _ _ => some (c, m)
  | _ => none

/-- The process has *blocked* `y`: it won the test-and-set of `y` in Line 11. -/
def blk : Loc V → Node → Prop
  | .retTas _ c m r, y | .readReg _ c m r, y | .done _ c m (some r) _, y => y.d ≤ m ∧ r < y ∧ y < c
  | .done _ c m none _, y => y.d ≤ m ∧ y < c
  | _, _ => False

/-- The process lost the test-and-set of `y` in Line 11 (and returns `y.reg`). -/
def lost : Loc V → Node → Prop
  | .readReg _ _ _ r, y | .done _ _ _ (some r) _, y => y = r
  | _, _ => False

/-- The process *tries to return from* `y` (applies, or is about to apply, `T&S(y.tst)` in
Line 11). -/
def tryRet (l : Loc V) (y : Node) : Prop :=
  l.blk y ∨ l.lost y ∨ ∃ d c m, l = .retTas d c m y

end Loc

/-- All nodes of the option `o` are `< c`. -/
def Below (o : Option Node) (c : Node) : Prop := ∀ a, o = some a → a < c

/-- The per-process part of the invariant. -/
def LocOK (x : ℕ → V) (C : Config V) (p : ℕ) : Loc V → Prop
  | .start x' => x' = x p
  | .scan x' d pr => x' = x p ∧ S C d = pr ∧ ∀ c, pr = some c → ∃ j, (C.loc j).blk c
  | .write x' d c => x' = x p ∧ c.d = d ∧ Below (S C d) c
  | .tas x' d c => x' = x p ∧ c.d = d ∧ Below (S C d) c ∧ R C c = some (x p)
  | .upd x' d c w => x' = x p ∧ c.d = d ∧ Below (S C d) c ∧ R C c = some (x p) ∧ B C c = true ∧
      (w = false → ∃ j, (C.loc j).blk c)
  | .readMax d c => c.d = d ∧ S C d = some c ∧ R C c = some (x p)
  | .retTas d c m r => c.d = d ∧ S C d = some c ∧ R C c = some (x p) ∧ d < m ∧ r < c ∧ r.d ≤ m
  | .readReg d c m r => c.d = d ∧ S C d = some c ∧ R C c = some (x p) ∧ d < m ∧ r < c ∧ r.d ≤ m
  | .done d c m r o => c.d = d ∧ S C d = some c ∧ R C c = some (x p) ∧ d < m ∧
      (r = none → o = none) ∧
      ∀ r', r = some r' → r' < c ∧ r'.d ≤ m ∧ ∃ q, (C.loc q).cap = some r' ∧ o = some (x q)

/-- The inductive invariant of Algorithm 1. -/
structure Inv (x : ℕ → V) (C : Config V) : Prop where
  one_le : 1 ≤ D C
  dep_lt : ∀ p d, (C.loc p).dep = some d → 1 ≤ d ∧ d < D C
  dep_inj : ∀ p q d, (C.loc p).dep = some d → (C.loc q).dep = some d → p = q
  cell : ∀ e a, S C e = some a → a.d = e ∧ (∃ p, (C.loc p).dep = some e) ∧ B C a = true
  ok : ∀ p, LocOK x C p (C.loc p)
  blk_tst : ∀ j y, (C.loc j).blk y → B C y = true
  tst_true : ∀ y, B C y = true →
    (∃ p, (C.loc p).cap = some y) ∨ ∃ j, (C.loc j).blk y ∨ (C.loc j).lost y
  excl : ∀ p j y, (C.loc p).cap = some y → ¬ (C.loc j).blk y
  lost_cap : ∀ j y, (C.loc j).lost y → ∃ p, (C.loc p).cap = some y
  l2 : ∀ i j c m dj cj, (C.loc i).rinfo = some (c, m) → (C.loc j).dep = some dj → m ≤ dj →
    (C.loc j).sel = some cj → c < cj
  blk_right : ∀ j y c, (C.loc j).blk y → (C.loc j).sel = some c → rightSub y c →
    ∃ a, S C y.d = some a ∧ y < a
  lemma1 : ∀ w, ((∃ p, (C.loc p).sel = some w) ∨ (∃ e, S C e = some w)) →
    ∀ v, rightSub v w → ∃ a, S C v.d = some a ∧ v ≤ a

/-! ### Basic facts about the local-state predicates -/

namespace Loc

lemma blk_spec {l : Loc V} {y : Node} (h : l.blk y) :
    ∃ c m, l.rinfo = some (c, m) ∧ y < c ∧ y.d ≤ m := by
  match l, h with
  | .retTas _ c m r, h => exact ⟨c, m, rfl, h.2.2, h.1⟩
  | .readReg _ c m r, h => exact ⟨c, m, rfl, h.2.2, h.1⟩
  | .done _ c m (some r) _, h => exact ⟨c, m, rfl, h.2.2, h.1⟩
  | .done _ c m none _, h => exact ⟨c, m, rfl, h.2, h.1⟩

lemma rinfo_sel {l : Loc V} {c : Node} {m : ℕ} (h : l.rinfo = some (c, m)) :
    l.sel = some c ∧ l.cap = some c := by
  match l, h with
  | .retTas _ c m r, rfl => exact ⟨rfl, rfl⟩
  | .readReg _ c m r, rfl => exact ⟨rfl, rfl⟩
  | .done _ c m _ _, rfl => exact ⟨rfl, rfl⟩

lemma cap_sel {l : Loc V} {c : Node} (h : l.cap = some c) : l.sel = some c := by
  match l, h with
  | .upd _ _ c w, h => cases w <;> simp_all [cap, sel]
  | .readMax _ c, rfl => rfl
  | .retTas _ c m r, rfl => rfl
  | .readReg _ c m r, rfl => rfl
  | .done _ c m _ _, rfl => rfl

lemma sel_dep {l : Loc V} {c : Node} (h : l.sel = some c) : ∃ d, l.dep = some d := by
  cases l <;> simp_all [sel, dep]

/-- A process trying to return from `y` has blocked every node of depth `≤ maxdepth` strictly
between `y` and its captured node. -/
lemma tryRet_spec {l : Loc V} {y : Node} (h : l.tryRet y) :
    ∃ c m, l.rinfo = some (c, m) ∧ ∀ z : Node, y < z → z < c → z.d ≤ m → l.blk z := by
  rcases h with h | h | ⟨d, c, m, rfl⟩
  · match l, h with
    | .retTas _ c m r, h => exact ⟨c, m, rfl, fun z h1 h2 h3 => ⟨h3, h.2.1.trans h1, h2⟩⟩
    | .readReg _ c m r, h => exact ⟨c, m, rfl, fun z h1 h2 h3 => ⟨h3, h.2.1.trans h1, h2⟩⟩
    | .done _ c m (some r) _, h => exact ⟨c, m, rfl, fun z h1 h2 h3 => ⟨h3, h.2.1.trans h1, h2⟩⟩
    | .done _ c m none _, h => exact ⟨c, m, rfl, fun z h1 h2 h3 => ⟨h3, h2⟩⟩
  · match l, h with
    | .readReg _ c m r, (h : y = r) => subst h; exact ⟨c, m, rfl, fun z h1 h2 h3 => ⟨h3, h1, h2⟩⟩
    | .done _ c m (some r) _, (h : y = r) =>
      subst h; exact ⟨c, m, rfl, fun z h1 h2 h3 => ⟨h3, h1, h2⟩⟩
  · exact ⟨c, m, rfl, fun z h1 h2 h3 => ⟨h3, h1, h2⟩⟩

end Loc

/-! ### Derived facts: Lemmas 2 and 3 -/

section Derived

variable {x : ℕ → V} {C : Config V}

lemma LocOK.rinfo {p : ℕ} {l : Loc V} (h : LocOK x C p l) {c : Node} {m : ℕ}
    (hr : l.rinfo = some (c, m)) :
    ∃ d, l.dep = some d ∧ c.d = d ∧ S C d = some c ∧ R C c = some (x p) ∧ d < m := by
  match l, hr with
  | .retTas d c m r, rfl => exact ⟨d, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | .readReg d c m r, rfl => exact ⟨d, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | .done d c m r o, rfl => exact ⟨d, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

lemma LocOK.sel {p : ℕ} {l : Loc V} (h : LocOK x C p l) {c : Node} (hs : l.sel = some c) :
    l.dep = some c.d := by
  cases l <;> simp_all [Loc.sel, Loc.dep, LocOK]

lemma LocOK.cap {p : ℕ} {l : Loc V} (h : LocOK x C p l) {c : Node} (hc : l.cap = some c) :
    S C c.d = some c ∨ (∃ x' w, l = .upd x' c.d c w) := by
  match l, hc with
  | .upd x' d c w, h' => right; cases w <;> simp_all [Loc.cap, LocOK]
  | .readMax d c, rfl => left; obtain ⟨h1, h2, -⟩ := h; rw [h1]; exact h2
  | .retTas d c m r, rfl => left; obtain ⟨h1, h2, -⟩ := h; rw [h1]; exact h2
  | .readReg d c m r, rfl => left; obtain ⟨h1, h2, -⟩ := h; rw [h1]; exact h2
  | .done d c m r o, rfl => left; obtain ⟨h1, h2, -⟩ := h; rw [h1]; exact h2

/-- A captured node's test-and-set bit is set. -/
lemma Inv.cap_tst (hI : Inv x C) {p : ℕ} {c : Node} (hc : (C.loc p).cap = some c) :
    B C c = true := by
  rcases (hI.ok p).cap hc with h | ⟨x', w, h⟩
  · exact (hI.cell _ _ h).2.2
  · have := hI.ok p; rw [h] at this; exact this.2.2.2.2.1


lemma LocOK.tryRet_lt {p : ℕ} {l : Loc V} (h : LocOK x C p l) {y : Node} (ht : l.tryRet y) :
    ∃ c m, l.rinfo = some (c, m) ∧ y < c := by
  rcases ht with hb | hl | ⟨d, c, m, rfl⟩
  · obtain ⟨c, m, h1, h2, -⟩ := Loc.blk_spec hb; exact ⟨c, m, h1, h2⟩
  · match l, hl with
    | .readReg _ c m r, (hl : y = r) => subst hl; exact ⟨c, m, rfl, h.2.2.2.2.1⟩
    | .done _ c m (some r) _, (hl : y = r) =>
      subst hl; exact ⟨c, m, rfl, (h.2.2.2.2.2 y rfl).1⟩
  · exact ⟨c, m, rfl, h.2.2.2.2.1⟩

/-- **Lemma 2** of [AMW11]: if `cap_i > cap_j` then `maxdepth_i > depth_j` (for a process `i`
that has read `maxdepth_i` in Line 7 and a process `j` that has captured `cap_j`). -/
lemma Inv.lemma2 (hI : Inv x C) {i j : ℕ} {ci cj : Node} {mi dj : ℕ}
    (hi : (C.loc i).rinfo = some (ci, mi)) (hj : (C.loc j).cap = some cj)
    (hdj : (C.loc j).dep = some dj) (h : cj < ci) : dj < mi := by
  by_contra hle
  push Not at hle
  exact absurd (hI.l2 i j ci mi dj cj hi hdj hle (Loc.cap_sel hj)) (not_lt.2 h.le)

/-- **Lemma 3** of [AMW11] (second half): at most one process tries to return from a node. -/
lemma Inv.tryRet_unique (hI : Inv x C) {i j : ℕ} {y : Node} (hi : (C.loc i).tryRet y)
    (hj : (C.loc j).tryRet y) : i = j := by
  have key : ∀ i j : ℕ, (C.loc i).tryRet y → (C.loc j).tryRet y →
      ∀ ci cj mi mj, (C.loc i).rinfo = some (ci, mi) → (C.loc j).rinfo = some (cj, mj) →
      cj < ci → False := by
    intro i j hi hj ci cj mi mj hri hrj hlt
    obtain ⟨ci', mi', hri', hbi⟩ := Loc.tryRet_spec hi
    rw [hri] at hri'; cases hri'
    obtain ⟨cj', mj', hrj', hyj⟩ := (hI.ok j).tryRet_lt hj
    rw [hrj] at hrj'; cases hrj'
    obtain ⟨dj, hdj, hcdj, -, -, -⟩ := (hI.ok j).rinfo hrj
    have hcap := (Loc.rinfo_sel hrj).2
    have hdm := hI.lemma2 hri hcap hdj hlt
    exact hI.excl j i cj hcap (hbi cj hyj hlt (by omega))
  obtain ⟨ci, mi, hri, -⟩ := (hI.ok i).tryRet_lt hi
  obtain ⟨cj, mj, hrj, -⟩ := (hI.ok j).tryRet_lt hj
  rcases lt_trichotomy ci cj with h | h | h
  · exact (key j i hj hi cj ci mj mi hrj hri h).elim
  · subst h
    obtain ⟨di, hdi, hci, -⟩ := (hI.ok i).rinfo hri
    obtain ⟨dj, hdj, hcj, -⟩ := (hI.ok j).rinfo hrj
    exact hI.dep_inj i j di hdi (by rw [hdj, ← hcj, hci])
  · exact (key i j hi hj ci cj mi mj hri hrj h).elim

/-! ### The initial configuration -/

lemma inv_init (x : ℕ → V) : Inv x ((alg V).initCfg x) := by
  have hD : D ((alg V).initCfg x) = 1 := rfl
  have hS : S ((alg V).initCfg x) = fun _ => none := rfl
  have hB : B ((alg V).initCfg x) = fun _ => false := rfl
  have hl : ∀ p, ((alg V).initCfg x).loc p = .start (x p) := fun _ => rfl
  refine ⟨by rw [hD], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hl, hS, hB, Loc.dep, Loc.blk, Loc.cap, Loc.lost, Loc.rinfo, Loc.sel, LocOK]

/-! ### Monotonicity of a step -/

/-- The facts about a local state that persist over steps. -/
structure Mono (l l' : Loc V) : Prop where
  dep : ∀ e, l.dep = some e → l'.dep = some e
  cap : ∀ c, l.cap = some c → l'.cap = some c
  blk : ∀ y, l.blk y → l'.blk y
  lost : ∀ y, l.lost y → l'.lost y
  rinfo : ∀ cm, l.rinfo = some cm → l'.rinfo = some cm

lemma Mono.refl (l : Loc V) : Mono l l := ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
  fun _ h => h⟩

lemma Mono.tryRet {l l' : Loc V} (h : Mono l l') {y : Node} (ht : l.tryRet y) :
    l'.tryRet y ∨ ∃ d c m, l = .retTas d c m y := by
  rcases ht with hb | hl | hr
  · exact Or.inl (Or.inl (h.blk y hb))
  · exact Or.inl (Or.inr (Or.inl (h.lost y hl)))
  · exact Or.inr hr

lemma step_mono (C : Config V) (p q : ℕ) : Mono (C.loc q) ((C.step p).loc q) := by
  by_cases hq : q = p
  swap
  · rw [Cfg.step_loc_other C hq]; exact Mono.refl _
  subst hq
  cases h : C.loc q with
  | start x' =>
    rw [(step_start h).1]
    exact ⟨by simp [Loc.dep], by simp [Loc.cap], by simp [Loc.blk], by simp [Loc.lost],
      by simp [Loc.rinfo]⟩
  | scan x' d pr =>
    rw [(step_scan h).1]
    split <;> exact ⟨by simp [Loc.dep], by simp [Loc.cap], by simp [Loc.blk], by simp [Loc.lost],
      by simp [Loc.rinfo]⟩
  | write x' d c =>
    rw [(step_write h).1]
    exact ⟨by simp [Loc.dep], by simp [Loc.cap], by simp [Loc.blk], by simp [Loc.lost],
      by simp [Loc.rinfo]⟩
  | tas x' d c =>
    rw [(step_tas h).1]
    exact ⟨by simp [Loc.dep], by simp [Loc.cap], by simp [Loc.blk], by simp [Loc.lost],
      by simp [Loc.rinfo]⟩
  | upd x' d c w =>
    rw [(step_upd h).1]
    cases w <;> exact ⟨by simp [Loc.dep], by simp [Loc.cap], by simp [Loc.blk],
      by simp [Loc.lost], by simp [Loc.rinfo]⟩
  | readMax d c =>
    rw [(step_readMax h).1]
    cases prev c (D C) <;> exact ⟨by simp [afterPrev, Loc.dep], by simp [afterPrev, Loc.cap],
      by simp [Loc.blk], by simp [Loc.lost], by simp [Loc.rinfo]⟩
  | retTas d c m r =>
    rw [(step_retTas h).1]
    by_cases hb : B C r = true
    · rw [ite_eq_left hb]
      exact ⟨by simp [Loc.dep], by simp [Loc.cap], fun y hy => hy, by simp [Loc.lost],
        by simp [Loc.rinfo]⟩
    · rw [ite_eq_right hb]
      cases hp : prev r m with
      | none =>
        exact ⟨by simp [afterPrev, Loc.dep], by simp [afterPrev, Loc.cap],
          fun y hy => by simp only [afterPrev, Loc.blk] at hy ⊢; exact ⟨hy.1, hy.2.2⟩,
          by simp [Loc.lost], by simp [afterPrev, Loc.rinfo]⟩
      | some r' =>
        have := (prev_some hp).1
        exact ⟨by simp [afterPrev, Loc.dep], by simp [afterPrev, Loc.cap],
          fun y hy => by
            simp only [afterPrev, Loc.blk] at hy ⊢; exact ⟨hy.1, this.trans hy.2.1, hy.2.2⟩,
          by simp [Loc.lost], by simp [afterPrev, Loc.rinfo]⟩
  | readReg d c m r =>
    rw [(step_readReg h).1]
    exact ⟨by simp [Loc.dep], by simp [Loc.cap], fun y hy => hy, fun y hy => hy,
      by simp [Loc.rinfo]⟩
  | done d c m r o =>
    rw [step_done h, h]; exact Mono.refl _

/-- The per-process invariant is preserved when the memory relevant to the process is unchanged
(and test-and-set bits, blocked nodes and captured nodes only grow). -/
lemma LocOK.transfer {C C' : Config V} {p : ℕ} {l : Loc V} (h : LocOK x C p l)
    (hS : ∀ e, l.dep = some e → S C' e = S C e) (hR : ∀ c, l.sel = some c → R C' c = R C c)
    (hB : ∀ y, B C y = true → B C' y = true) (hm : ∀ j, Mono (C.loc j) (C'.loc j)) :
    LocOK x C' p l := by
  cases l with
  | start x' => exact h
  | scan x' d pr =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, by rw [hS d rfl, h2], fun c hc => ?_⟩
    obtain ⟨j, hj⟩ := h3 c hc; exact ⟨j, (hm j).blk c hj⟩
  | write x' d c =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, h2, by rw [hS d rfl]; exact h3⟩
  | tas x' d c =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, by rw [hS d rfl]; exact h3, by rw [hR c rfl]; exact h4⟩
  | upd x' d c w =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨h1, h2, by rw [hS d rfl]; exact h3, by rw [hR c rfl]; exact h4, hB c h5, fun hw => ?_⟩
    obtain ⟨j, hj⟩ := h6 hw; exact ⟨j, (hm j).blk c hj⟩
  | readMax d c =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by rw [hS d rfl]; exact h2, by rw [hR c rfl]; exact h3⟩
  | retTas d c m r =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, by rw [hS d rfl]; exact h2, by rw [hR c rfl]; exact h3, h4⟩
  | readReg d c m r =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, by rw [hS d rfl]; exact h2, by rw [hR c rfl]; exact h3, h4⟩
  | done d c m r o =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨h1, by rw [hS d rfl]; exact h2, by rw [hR c rfl]; exact h3, h4, h5, fun r' hr' => ?_⟩
    obtain ⟨a1, a2, q, hq, ho⟩ := h6 r' hr'
    exact ⟨a1, a2, q, (hm q).cap r' hq, ho⟩

end Derived

end Podc.UnboundedConcurrency.Swap
