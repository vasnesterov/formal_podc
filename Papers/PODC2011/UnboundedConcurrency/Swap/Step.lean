import Papers.PODC2011.UnboundedConcurrency.Swap.Inv

/-!
# Preservation of the invariant (one lemma per line of Algorithm 1)
-/

namespace Podc.UnboundedConcurrency.Swap

open Cslib.SharedMemory Cslib.SharedMemory.Arrival Cfg' Node

variable {V : Type} {x : ℕ → V} {C : Config V} {p : ℕ}

/-- `tst_true` transfers when bits only grow on already-witnessed nodes. -/
lemma tst_true_transfer (hI : Inv x C) {C' : Config V} (hm : ∀ j, Mono (C.loc j) (C'.loc j))
    (hB : ∀ y, B C' y = true → B C y = true) (y : Node) (hy : B C' y = true) :
    (∃ p, (C'.loc p).cap = some y) ∨ ∃ j, (C'.loc j).blk y ∨ (C'.loc j).lost y := by
  rcases hI.tst_true y (hB y hy) with ⟨q, hq⟩ | ⟨j, hj⟩
  · exact Or.inl ⟨q, (hm q).cap y hq⟩
  · exact Or.inr ⟨j, hj.imp ((hm j).blk y) ((hm j).lost y)⟩

/-! ### Line 1 -/

lemma Inv.stepStart (hI : Inv x C) {x' : V} (h : C.loc p = .start x') : Inv x (C.step p) := by
  obtain ⟨hself, hother, hD, hS, hR, hB⟩ := step_start h
  have hm := step_mono C p
  have hxp : x' = x p := by have := hI.ok p; rw [h] at this; exact this
  constructor
  · rw [hD]; omega
  · intro q d hd
    by_cases hq : q = p
    · subst hq; rw [hself] at hd; simp only [Loc.dep, Option.some.injEq] at hd; subst hd
      rw [hD]; exact ⟨hI.one_le, by omega⟩
    · rw [hother q hq] at hd; have := hI.dep_lt q d hd; rw [hD]; omega
  · intro q q' d hq hq'
    by_cases h1 : q = p <;> by_cases h2 : q' = p
    · rw [h1, h2]
    · subst h1; rw [hself] at hq; simp only [Loc.dep, Option.some.injEq] at hq; subst hq
      rw [hother q' h2] at hq'; exact absurd (hI.dep_lt q' _ hq').2 (lt_irrefl _)
    · subst h2; rw [hself] at hq'; simp only [Loc.dep, Option.some.injEq] at hq'; subst hq'
      rw [hother q h1] at hq; exact absurd (hI.dep_lt q _ hq).2 (lt_irrefl _)
    · rw [hother q h1] at hq; rw [hother q' h2] at hq'; exact hI.dep_inj q q' d hq hq'
  · rw [hS, hB]; intro e a he
    obtain ⟨h1, ⟨q, hq⟩, h3⟩ := hI.cell e a he
    exact ⟨h1, ⟨q, (hm q).dep e hq⟩, h3⟩
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hself]
      refine ⟨hxp, ?_, by simp⟩
      rw [hS]
      by_contra hne
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hne
      obtain ⟨-, ⟨q', hq'⟩, -⟩ := hI.cell _ a ha
      exact absurd (hI.dep_lt q' _ hq').2 (lt_irrefl _)
    · rw [hother q hq]
      exact (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c _ => by rw [hR])
        (fun y hy => by rw [hB]; exact hy) hm
  · intro j y hj
    by_cases hq : j = p
    · subst hq; rw [hself] at hj; simp [Loc.blk] at hj
    · rw [hother j hq] at hj; rw [hB]; exact hI.blk_tst j y hj
  · exact tst_true_transfer hI hm (fun y hy => by rw [hB] at hy; exact hy)
  · intro q j y hq hj
    by_cases h1 : q = p
    · subst h1; rw [hself] at hq; simp [Loc.cap] at hq
    by_cases h2 : j = p
    · subst h2; rw [hself] at hj; simp [Loc.blk] at hj
    rw [hother q h1] at hq; rw [hother j h2] at hj; exact hI.excl q j y hq hj
  · intro j y hj
    by_cases h1 : j = p
    · subst h1; rw [hself] at hj; simp [Loc.lost] at hj
    rw [hother j h1] at hj
    obtain ⟨q, hq⟩ := hI.lost_cap j y hj
    exact ⟨q, (hm q).cap y hq⟩
  · intro i j c m dj cj hi hj hle hs
    by_cases h1 : i = p
    · subst h1; rw [hself] at hi; simp [Loc.rinfo] at hi
    by_cases h2 : j = p
    · subst h2; rw [hself] at hs; simp [Loc.sel] at hs
    rw [hother i h1] at hi; rw [hother j h2] at hj hs
    exact hI.l2 i j c m dj cj hi hj hle hs
  · intro j y c hj hs hr
    by_cases h1 : j = p
    · subst h1; rw [hself] at hj; simp [Loc.blk] at hj
    rw [hother j h1] at hj hs; rw [hS]; exact hI.blk_right j y c hj hs hr
  · intro w hw v hv
    rw [hS] at hw ⊢
    refine hI.lemma1 w ?_ v hv
    rcases hw with ⟨q, hq⟩ | hw
    · by_cases h1 : q = p
      · subst h1; rw [hself] at hq; simp [Loc.sel] at hq
      · rw [hother q h1] at hq; exact Or.inl ⟨q, hq⟩
    · exact Or.inr hw

/-! ### Steps that do not change the "view" of any process -/

/-- If no process changes its depth, selected/captured node, `(cap, maxdepth)`, blocked and lost
nodes, and `max_depth`, `accessed`, the test-and-set bits are unchanged, then the invariant
transfers, provided the per-process part holds. -/
lemma Inv.of_same' (hI : Inv x C) {C' : Config V}
    (hdep : ∀ q, (C'.loc q).dep = (C.loc q).dep) (hsel : ∀ q, (C'.loc q).sel = (C.loc q).sel)
    (hcap : ∀ q, (C'.loc q).cap = (C.loc q).cap)
    (hl2 : ∀ i j c m dj cj, (C'.loc i).rinfo = some (c, m) → (C'.loc j).dep = some dj → m ≤ dj →
      (C'.loc j).sel = some cj → c < cj)
    (hblk : ∀ q y, (C'.loc q).blk y ↔ (C.loc q).blk y)
    (hlost : ∀ q y, (C'.loc q).lost y ↔ (C.loc q).lost y)
    (hD : D C' = D C) (hS : S C' = S C) (hB : B C' = B C)
    (hok : ∀ q, LocOK x C' q (C'.loc q)) : Inv x C' := by
  refine ⟨?_, ?_, ?_, ?_, hok, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hD]; exact hI.one_le
  · intro q d hd; rw [hdep] at hd; rw [hD]; exact hI.dep_lt q d hd
  · intro q q' d hq hq'; rw [hdep] at hq hq'; exact hI.dep_inj q q' d hq hq'
  · intro e a he; rw [hS] at he; rw [hB]
    obtain ⟨h1, ⟨q, hq⟩, h3⟩ := hI.cell e a he
    exact ⟨h1, ⟨q, by rw [hdep]; exact hq⟩, h3⟩
  · intro j y hj; rw [hblk] at hj; rw [hB]; exact hI.blk_tst j y hj
  · intro y hy; rw [hB] at hy
    rcases hI.tst_true y hy with ⟨q, hq⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨q, by rw [hcap]; exact hq⟩
    · exact Or.inr ⟨j, by rw [hblk, hlost]; exact hj⟩
  · intro q j y hq hj; rw [hcap] at hq; rw [hblk] at hj; exact hI.excl q j y hq hj
  · intro j y hj; rw [hlost] at hj
    obtain ⟨q, hq⟩ := hI.lost_cap j y hj; exact ⟨q, by rw [hcap]; exact hq⟩
  · exact hl2
  · intro j y c hj hs hr; rw [hblk] at hj; rw [hsel] at hs; rw [hS]
    exact hI.blk_right j y c hj hs hr
  · intro w hw v hv; rw [hS] at hw ⊢
    refine hI.lemma1 w ?_ v hv
    rcases hw with ⟨q, hq⟩ | hw
    · exact Or.inl ⟨q, by rw [← hsel]; exact hq⟩
    · exact Or.inr hw

lemma Inv.of_same (hI : Inv x C) {C' : Config V}
    (hdep : ∀ q, (C'.loc q).dep = (C.loc q).dep) (hsel : ∀ q, (C'.loc q).sel = (C.loc q).sel)
    (hcap : ∀ q, (C'.loc q).cap = (C.loc q).cap)
    (hrinfo : ∀ q, (C'.loc q).rinfo = (C.loc q).rinfo)
    (hblk : ∀ q y, (C'.loc q).blk y ↔ (C.loc q).blk y)
    (hlost : ∀ q y, (C'.loc q).lost y ↔ (C.loc q).lost y)
    (hD : D C' = D C) (hS : S C' = S C) (hB : B C' = B C)
    (hok : ∀ q, LocOK x C' q (C'.loc q)) : Inv x C' :=
  hI.of_same' hdep hsel hcap (fun i j c m dj cj hi hj hle hs => by
    rw [hrinfo] at hi; rw [hdep] at hj; rw [hsel] at hs; exact hI.l2 i j c m dj cj hi hj hle hs)
    hblk hlost hD hS hB hok

/-- Lift a property of the stepping process to all processes. -/
lemma forall_of_self {C' : Config V} (hother : ∀ q, q ≠ p → C'.loc q = C.loc q)
    {β : Type} (f : Loc V → β) (h : f (C'.loc p) = f (C.loc p)) : ∀ q, f (C'.loc q) = f (C.loc q) := by
  intro q; by_cases hq : q = p
  · subst hq; exact h
  · rw [hother q hq]

lemma forall_iff_of_self {C' : Config V} (hother : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (f : Loc V → Node → Prop) (h : ∀ y, f (C'.loc p) y ↔ f (C.loc p) y) :
    ∀ q y, f (C'.loc q) y ↔ f (C.loc q) y := by
  intro q; by_cases hq : q = p
  · subst hq; exact h
  · rw [hother q hq]; exact fun _ => Iff.rfl

lemma LocOK.cap_reg {q : ℕ} {l : Loc V} (h : LocOK x C q l) {c : Node} (hc : l.cap = some c) :
    R C c = some (x q) := by
  match l, hc with
  | .upd x' d c w, hc => cases w <;> simp [Loc.cap] at hc; subst hc; exact h.2.2.2.1
  | .readMax d c, rfl => exact h.2.2
  | .retTas d c m r, rfl => exact h.2.2.1
  | .readReg d c m r, rfl => exact h.2.2.1
  | .done d c m r o, rfl => exact h.2.2.1

/-- The captured node of a process is at its depth. -/
lemma Inv.cap_dep (hI : Inv x C) {q : ℕ} {c : Node} (hc : (C.loc q).cap = some c) :
    (C.loc q).dep = some c.d := (hI.ok q).sel (Loc.cap_sel hc)

/-! ### Line 3 -/

lemma Inv.stepWrite (hI : Inv x C) {x' : V} {d : ℕ} {c : Node} (h : C.loc p = .write x' d c) :
    Inv x (C.step p) := by
  obtain ⟨hself, hother, hD, hS, hR, hB⟩ := step_write h
  have hm := step_mono C p
  obtain ⟨hxp, hcd, hbel⟩ := (show LocOK x C p (C.loc p) from hI.ok p) |> fun h' => by
    rw [h] at h'; exact h'
  refine hI.of_same (forall_of_self hother _ (by rw [hself, h]; rfl))
    (forall_of_self hother _ (by rw [hself, h]; rfl)) (forall_of_self hother _ (by rw [hself, h]; rfl))
    (forall_of_self hother _ (by rw [hself, h]; rfl))
    (forall_iff_of_self hother _ (by rw [hself, h]; exact fun _ => Iff.rfl))
    (forall_iff_of_self hother _ (by rw [hself, h]; exact fun _ => Iff.rfl)) hD hS hB ?_
  intro q
  by_cases hq : q = p
  · subst hq; rw [hself]
    refine ⟨hxp, hcd, by rw [hS]; exact hbel, by rw [hR, hxp]; simp⟩
  · rw [hother q hq]
    refine (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c' hc' => ?_)
      (fun y hy => by rw [hB]; exact hy) hm
    rw [hR]
    have hne : c' ≠ c := by
      rintro rfl
      have h1 := (hI.ok q).sel hc'
      have h2 : (C.loc p).dep = some c'.d := by rw [h, hcd]; rfl
      exact hq (hI.dep_inj q p _ h1 h2)
    simp [Function.update_of_ne hne]

/-! ### Line 12 -/

lemma Inv.stepReadReg (hI : Inv x C) {d : ℕ} {c : Node} {m : ℕ} {r : Node}
    (h : C.loc p = .readReg d c m r) : Inv x (C.step p) := by
  obtain ⟨hself, hother, hD, hS, hR, hB⟩ := step_readReg h
  have hm := step_mono C p
  have hok := hI.ok p
  rw [h] at hok
  obtain ⟨hcd, hSd, hRc, hdm, hrc, hrm⟩ := hok
  refine hI.of_same (forall_of_self hother _ (by rw [hself, h]; rfl))
    (forall_of_self hother _ (by rw [hself, h]; rfl)) (forall_of_self hother _ (by rw [hself, h]; rfl))
    (forall_of_self hother _ (by rw [hself, h]; rfl))
    (forall_iff_of_self hother _ (by rw [hself, h]; exact fun _ => Iff.rfl))
    (forall_iff_of_self hother _ (by rw [hself, h]; exact fun _ => Iff.rfl)) hD hS hB ?_
  intro q
  by_cases hq : q = p
  · subst hq; rw [hself]
    refine ⟨hcd, by rw [hS]; exact hSd, by rw [hR]; exact hRc, hdm, by simp, fun r' hr' => ?_⟩
    cases hr'
    obtain ⟨q', hq'⟩ := hI.lost_cap q r (by rw [h]; rfl)
    refine ⟨hrc, hrm, q', (hm q').cap r hq', ?_⟩
    exact (hI.ok q').cap_reg hq'
  · rw [hother q hq]
    exact (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c' _ => by rw [hR])
      (fun y hy => by rw [hB]; exact hy) hm


/-! ### Line 2: the core of Lemma 1 -/

/-- The inductive step of **Lemma 1** of [AMW11]: when a process selects (Line 2) a node `c` of the
right subtree of `v`, a node `≥ v` of the depth of `v` has already been recorded in `accessed`.

Paper's argument: let `v_l` be the largest node of `v`'s left subtree at `c`'s depth. Either the
process tried `v_l` and lost it to a returning process `P_j` (then `v_l < cap_j < c`, and `cap_j`
is `v`, in `v`'s right subtree, or in `v_l`'s right subtree — the last case is excluded by
`blk_right`), or it skipped `v_l` because of an accessed node `u` with `v_l < u < c` (same case
analysis on `u`). The case `cap_j = v` (resp. `u = v`), which the paper does not mention, is the
case where `v` itself has been recorded. -/
lemma Inv.sel_new (hI : Inv x C) {x' : V} {d : ℕ} {pr : Option Node} {c : Node}
    (h : C.loc p = .scan x' d pr) (hn : next d (S C) = some c) {v : Node} (hv : rightSub v c) :
    ∃ a, S C v.d = some a ∧ v ≤ a := by
  obtain ⟨hcd, habove, hmin⟩ := next_some hn
  have hok := hI.ok p
  rw [h] at hok
  obtain ⟨-, hSd, hpr⟩ := hok
  have hvl_d : (leftNb v c.d hv.1).d = d := by simp [hcd]
  have hvl_lt_v := leftNb_lt v c.d hv.1
  have hvl_lt_c : leftNb v c.d hv.1 < c := hvl_lt_v.trans hv.lt
  -- the process tried `v_l` and lost it
  have claimA : S C d = some (leftNb v c.d hv.1) → ∃ a, S C v.d = some a ∧ v ≤ a := by
    intro hS
    obtain ⟨j, hj⟩ := hpr _ (by rw [← hSd, hS])
    obtain ⟨cj, mj, hrj, hlt, -⟩ := Loc.blk_spec hj
    obtain ⟨dj, hdj, hcdj, hSj, -, -⟩ := (hI.ok j).rinfo hrj
    have hselj := (Loc.rinfo_sel hrj).1
    have hcjc : cj < c := habove dj cj hSj
    rcases between_left hv hlt hcjc with heq | hr | hr
    · refine ⟨cj, ?_, le_of_eq heq.symm⟩
      rw [← heq, hcdj]; exact hSj
    · exact hI.lemma1 cj (Or.inl ⟨j, hselj⟩) v hr
    · obtain ⟨a', ha', hlt'⟩ := hI.blk_right j _ cj hj hselj hr
      rw [hvl_d, hS] at ha'
      cases ha'
      exact absurd hlt' (lt_irrefl _)
  have hna : ¬ Above (S C) (leftNb v c.d hv.1) := fun habv =>
    absurd (hmin _ hvl_d habv) (not_le.2 hvl_lt_c)
  simp only [Above, not_forall, not_lt] at hna
  obtain ⟨e, a, hea, hvla⟩ := hna
  have hac : a < c := habove e a hea
  obtain ⟨hae, -, -⟩ := hI.cell e a hea
  rcases eq_or_lt_of_le hvla with heq | hlt
  · apply claimA
    rw [← hvl_d, heq, hae]; exact hea
  · rcases between_left hv hlt hac with heq | hr | hr
    · refine ⟨a, ?_, le_of_eq heq.symm⟩
      rw [← heq, hae]; exact hea
    · exact hI.lemma1 a (Or.inr ⟨e, hea⟩) v hr
    · obtain ⟨b, hb, hvlb⟩ := hI.lemma1 a (Or.inr ⟨e, hea⟩) _ hr
      rw [hvl_d] at hb
      rcases eq_or_lt_of_le hvlb with heq | hlt2
      · apply claimA; rw [hb, heq]
      · have hbc : b < c := habove d b hb
        obtain ⟨hbd, -, -⟩ := hI.cell d b hb
        rcases between_left hv hlt2 hbc with heq | hr2 | hr2
        · exfalso
          have := hv.1
          rw [← heq] at this; omega
        · exact hI.lemma1 b (Or.inr ⟨d, hb⟩) v hr2
        · exfalso
          have := hr2.1
          rw [hvl_d] at this; omega

/-! ### Line 2 -/

lemma Inv.stepScan (hI : Inv x C) {x' : V} {d : ℕ} {pr : Option Node}
    (h : C.loc p = .scan x' d pr) : Inv x (C.step p) := by
  obtain ⟨hself, hother, hD, hS, hR, hB⟩ := step_scan h
  have hm := step_mono C p
  cases hn : next d (S C) with
  | none =>
    rw [hn] at hself
    have hall : ∀ q, (C.step p).loc q = C.loc q := by
      intro q; by_cases hq : q = p
      · subst hq; rw [hself, h]
      · exact hother q hq
    refine hI.of_same (fun q => by rw [hall]) (fun q => by rw [hall]) (fun q => by rw [hall])
      (fun q => by rw [hall]) (fun q y => by rw [hall]) (fun q y => by rw [hall]) hD hS hB
      (fun q => ?_)
    rw [hall]
    exact (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c' _ => by rw [hR])
      (fun y hy => by rw [hB]; exact hy) hm
  | some c =>
    rw [hn] at hself
    obtain ⟨hcd, habove, -⟩ := next_some hn
    have hok := hI.ok p
    rw [h] at hok
    obtain ⟨hxp, -, -⟩ := hok
    have hdep := forall_of_self hother Loc.dep (by rw [hself, h]; rfl)
    have hcap := forall_of_self hother Loc.cap (by rw [hself, h]; rfl)
    have hrinfo := forall_of_self hother Loc.rinfo (by rw [hself, h]; rfl)
    have hblk := forall_iff_of_self hother Loc.blk (by rw [hself, h]; exact fun _ => Iff.rfl)
    have hlost := forall_iff_of_self hother Loc.lost (by rw [hself, h]; exact fun _ => Iff.rfl)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hD]; exact hI.one_le
    · intro q d hd; rw [hdep] at hd; rw [hD]; exact hI.dep_lt q d hd
    · intro q q' d hq hq'; rw [hdep] at hq hq'; exact hI.dep_inj q q' d hq hq'
    · intro e a he; rw [hS] at he; rw [hB]
      obtain ⟨h1, ⟨q, hq⟩, h3⟩ := hI.cell e a he
      exact ⟨h1, ⟨q, by rw [hdep]; exact hq⟩, h3⟩
    · intro q
      by_cases hq : q = p
      · subst hq; rw [hself]
        exact ⟨hxp, hcd, fun a ha => by rw [hS] at ha; exact habove d a ha⟩
      · rw [hother q hq]
        exact (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c' _ => by rw [hR])
          (fun y hy => by rw [hB]; exact hy) hm
    · intro j y hj; rw [hblk] at hj; rw [hB]; exact hI.blk_tst j y hj
    · intro y hy; rw [hB] at hy
      rcases hI.tst_true y hy with ⟨q, hq⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨q, by rw [hcap]; exact hq⟩
      · exact Or.inr ⟨j, by rw [hblk, hlost]; exact hj⟩
    · intro q j y hq hj; rw [hcap] at hq; rw [hblk] at hj; exact hI.excl q j y hq hj
    · intro j y hj; rw [hlost] at hj
      obtain ⟨q, hq⟩ := hI.lost_cap j y hj; exact ⟨q, by rw [hcap]; exact hq⟩
    · intro i j ci m dj cj hi hj hle hs
      rw [hrinfo] at hi; rw [hdep] at hj
      by_cases hjp : j = p
      · subst hjp
        rw [hself] at hs; cases hs
        obtain ⟨di, -, hcdi, hSi, -⟩ := (hI.ok i).rinfo hi
        exact habove di ci hSi
      · rw [hother j hjp] at hs; exact hI.l2 i j ci m dj cj hi hj hle hs
    · intro j y c' hj hs hr; rw [hblk] at hj; rw [hS]
      have hjp : j ≠ p := by
        rintro rfl; rw [h] at hj; exact hj
      rw [hother j hjp] at hs
      exact hI.blk_right j y c' hj hs hr
    · intro w hw v hv; rw [hS] at hw ⊢
      rcases hw with ⟨q, hq⟩ | hw
      · by_cases hqp : q = p
        · subst hqp; rw [hself] at hq; cases hq
          exact hI.sel_new h hn hv
        · rw [hother q hqp] at hq; exact hI.lemma1 w (Or.inl ⟨q, hq⟩) v hv
      · exact hI.lemma1 w (Or.inr hw) v hv


/-! ### Line 4 -/

lemma Inv.stepTas (hI : Inv x C) {x' : V} {d : ℕ} {c : Node} (h : C.loc p = .tas x' d c) :
    Inv x (C.step p) := by
  obtain ⟨hself, hother, hD, hS, hR, hB⟩ := step_tas h
  have hm := step_mono C p
  have hok := hI.ok p
  rw [h] at hok
  obtain ⟨hxp, hcd, hbel, hRc⟩ := hok
  have hdep := forall_of_self hother Loc.dep (by rw [hself, h]; rfl)
  have hsel := forall_of_self hother Loc.sel (by rw [hself, h]; rfl)
  have hrinfo := forall_of_self hother Loc.rinfo (by rw [hself, h]; rfl)
  have hblk := forall_iff_of_self hother Loc.blk (by rw [hself, h]; exact fun _ => Iff.rfl)
  have hlost := forall_iff_of_self hother Loc.lost (by rw [hself, h]; exact fun _ => Iff.rfl)
  have hBmono : ∀ y, B C y = true → B (C.step p) y = true := by
    intro y hy; rw [hB]; by_cases hyc : y = c
    · subst hyc; simp
    · simp [Function.update_of_ne hyc, hy]
  -- a process other than `p` that captured `c` cannot exist (depths are unique)
  have hnocap : ∀ q, (C.loc q).cap ≠ some c := by
    intro q hq
    have h1 := hI.cap_dep hq
    have h2 : (C.loc p).dep = some c.d := by rw [h, hcd]; rfl
    have := hI.dep_inj q p _ h1 h2
    subst this; rw [h] at hq; simp [Loc.cap] at hq
  -- the new captured node of `p`
  have hcap' : ∀ q c', ((C.step p).loc q).cap = some c' →
      (C.loc q).cap = some c' ∨ (q = p ∧ c' = c ∧ B C c = false) := by
    intro q c' hq
    by_cases hqp : q = p
    · subst hqp; rw [hself] at hq
      cases hb : B C c <;> simp [hb, Loc.cap] at hq
      exact Or.inr ⟨rfl, hq.symm, rfl⟩
    · rw [hother q hqp] at hq; exact Or.inl hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hD]; exact hI.one_le
  · intro q d hd; rw [hdep] at hd; rw [hD]; exact hI.dep_lt q d hd
  · intro q q' d hq hq'; rw [hdep] at hq hq'; exact hI.dep_inj q q' d hq hq'
  · intro e a he; rw [hS] at he
    obtain ⟨h1, ⟨q, hq⟩, h3⟩ := hI.cell e a he
    exact ⟨h1, ⟨q, by rw [hdep]; exact hq⟩, hBmono a h3⟩
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hself]
      refine ⟨hxp, hcd, by rw [hS]; exact hbel, by rw [hR]; exact hRc, by rw [hB]; simp,
        fun hw => ?_⟩
      have hbc : B C c = true := by simpa using hw
      rcases hI.tst_true c hbc with ⟨q', hq'⟩ | ⟨j, hj | hj⟩
      · exact absurd hq' (hnocap q')
      · exact ⟨j, (hm j).blk c hj⟩
      · obtain ⟨q', hq'⟩ := hI.lost_cap j c hj; exact absurd hq' (hnocap q')
    · rw [hother q hq]
      exact (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c' _ => by rw [hR]) hBmono hm
  · intro j y hj; rw [hblk] at hj; exact hBmono y (hI.blk_tst j y hj)
  · intro y hy
    by_cases hyc : y = c
    · subst hyc
      cases hb : B C y
      · left; refine ⟨p, ?_⟩; rw [hself]; simp [hb, Loc.cap]
      · rcases hI.tst_true y hb with ⟨q, hq⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨q, (hm q).cap y hq⟩
        · exact Or.inr ⟨j, by rw [hblk, hlost]; exact hj⟩
    · rw [hB] at hy; simp only [Function.update_of_ne hyc] at hy
      rcases hI.tst_true y hy with ⟨q, hq⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨q, (hm q).cap y hq⟩
      · exact Or.inr ⟨j, by rw [hblk, hlost]; exact hj⟩
  · intro q j y hq hj; rw [hblk] at hj
    rcases hcap' q y hq with hq | ⟨-, rfl, hb⟩
    · exact hI.excl q j y hq hj
    · have := hI.blk_tst j y hj; rw [hb] at this; exact Bool.false_ne_true this
  · intro j y hj; rw [hlost] at hj
    obtain ⟨q, hq⟩ := hI.lost_cap j y hj; exact ⟨q, (hm q).cap y hq⟩
  · intro i j ci m dj cj hi hj hle hs
    rw [hrinfo] at hi; rw [hdep] at hj; rw [hsel] at hs; exact hI.l2 i j ci m dj cj hi hj hle hs
  · intro j y c' hj hs hr; rw [hblk] at hj; rw [hsel] at hs; rw [hS]
    exact hI.blk_right j y c' hj hs hr
  · intro w hw v hv; rw [hS] at hw ⊢
    refine hI.lemma1 w ?_ v hv
    rcases hw with ⟨q, hq⟩ | hw
    · exact Or.inl ⟨q, by rw [← hsel]; exact hq⟩
    · exact Or.inr hw


/-! ### Line 5 -/

lemma Inv.stepUpd (hI : Inv x C) {x' : V} {d : ℕ} {c : Node} {w : Bool}
    (h : C.loc p = .upd x' d c w) : Inv x (C.step p) := by
  obtain ⟨hself, hother, hD, hS, hR, hB⟩ := step_upd h
  have hm := step_mono C p
  have hok := hI.ok p
  rw [h] at hok
  obtain ⟨hxp, hcd, hbel, hRc, hBc, hlostw⟩ := hok
  have hdep := forall_of_self hother Loc.dep (by rw [hself, h]; cases w <;> rfl)
  have hcap := forall_of_self hother Loc.cap (by rw [hself, h]; cases w <;> rfl)
  have hrinfo := forall_of_self hother Loc.rinfo (by rw [hself, h]; cases w <;> rfl)
  have hblk := forall_iff_of_self hother Loc.blk
    (by rw [hself, h]; cases w <;> exact fun _ => Iff.rfl)
  have hlost := forall_iff_of_self hother Loc.lost
    (by rw [hself, h]; cases w <;> exact fun _ => Iff.rfl)
  have hsel : ∀ q c', ((C.step p).loc q).sel = some c' → (C.loc q).sel = some c' := by
    intro q c' hq
    by_cases hqp : q = p
    · subst hqp; rw [hself] at hq; rw [h]
      cases w <;> simpa [Loc.sel] using hq
    · rwa [hother q hqp] at hq
  have hSmono : ∀ e a, S C e = some a → ∃ a', S (C.step p) e = some a' ∧ a ≤ a' := by
    intro e a he
    by_cases hed : e = d
    · subst hed; exact ⟨c, by rw [hS]; simp, le_of_lt (hbel a he)⟩
    · exact ⟨a, by rw [hS, Function.update_of_ne hed]; exact he, le_rfl⟩
  have hpdep : (C.loc p).dep = some d := by rw [h]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hD]; exact hI.one_le
  · intro q d hd; rw [hdep] at hd; rw [hD]; exact hI.dep_lt q d hd
  · intro q q' d hq hq'; rw [hdep] at hq hq'; exact hI.dep_inj q q' d hq hq'
  · intro e a he; rw [hB]
    by_cases hed : e = d
    · subst hed; rw [hS] at he; simp only [Function.update_self, Option.some.injEq] at he
      subst he
      exact ⟨hcd, ⟨p, by rw [hdep]; exact hpdep⟩, hBc⟩
    · rw [hS, Function.update_of_ne hed] at he
      obtain ⟨h1, ⟨q, hq⟩, h3⟩ := hI.cell e a he
      exact ⟨h1, ⟨q, by rw [hdep]; exact hq⟩, h3⟩
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hself]
      cases w
      · refine ⟨hxp, by rw [hS]; simp, fun c' hc' => ?_⟩
        cases hc'
        obtain ⟨j, hj⟩ := hlostw rfl
        exact ⟨j, (hm j).blk c hj⟩
      · exact ⟨hcd, by rw [hS]; simp, by rw [hR]; exact hRc⟩
    · rw [hother q hq]
      refine (hI.ok q).transfer (fun e he => ?_) (fun c' _ => by rw [hR])
        (fun y hy => by rw [hB]; exact hy) hm
      have hed : e ≠ d := by
        rintro rfl; exact hq (hI.dep_inj q p e he hpdep)
      rw [hS, Function.update_of_ne hed]
  · intro j y hj; rw [hblk] at hj; rw [hB]; exact hI.blk_tst j y hj
  · intro y hy; rw [hB] at hy
    rcases hI.tst_true y hy with ⟨q, hq⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨q, by rw [hcap]; exact hq⟩
    · exact Or.inr ⟨j, by rw [hblk, hlost]; exact hj⟩
  · intro q j y hq hj; rw [hcap] at hq; rw [hblk] at hj; exact hI.excl q j y hq hj
  · intro j y hj; rw [hlost] at hj
    obtain ⟨q, hq⟩ := hI.lost_cap j y hj; exact ⟨q, by rw [hcap]; exact hq⟩
  · intro i j ci m dj cj hi hj hle hs
    rw [hrinfo] at hi; rw [hdep] at hj
    exact hI.l2 i j ci m dj cj hi hj hle (hsel j cj hs)
  · intro j y c' hj hs hr; rw [hblk] at hj
    obtain ⟨a, ha, hya⟩ := hI.blk_right j y c' hj (hsel j c' hs) hr
    obtain ⟨a', ha', haa'⟩ := hSmono _ a ha
    exact ⟨a', ha', lt_of_lt_of_le hya haa'⟩
  · intro w' hw v hv
    have hw' : (∃ q, (C.loc q).sel = some w') ∨ ∃ e, S C e = some w' := by
      rcases hw with ⟨q, hq⟩ | ⟨e, he⟩
      · exact Or.inl ⟨q, hsel q w' hq⟩
      · by_cases hed : e = d
        · subst hed; rw [hS] at he; simp only [Function.update_self, Option.some.injEq] at he
          subst he; exact Or.inl ⟨p, by rw [h]; rfl⟩
        · rw [hS, Function.update_of_ne hed] at he; exact Or.inr ⟨e, he⟩
    obtain ⟨a, ha, hva⟩ := hI.lemma1 w' hw' v hv
    obtain ⟨a', ha', haa'⟩ := hSmono _ a ha
    exact ⟨a', ha', hva.trans haa'⟩


/-! ### Line 7 -/

lemma afterPrev_blk_empty {d : ℕ} {c : Node} {m : ℕ} {y : Node} :
    ¬ (afterPrev (V := V) d c m (prev c m)).blk y := by
  cases hp : prev c m with
  | none =>
    simp only [afterPrev, Loc.blk, not_and]
    exact fun h1 h2 => prev_none hp y h1 h2
  | some r =>
    simp only [afterPrev, Loc.blk, not_and]
    exact fun h1 h2 h3 => absurd ((prev_some hp).2.2 y h1 h3) (not_le.2 h2)

lemma Inv.stepReadMax (hI : Inv x C) {d : ℕ} {c : Node} (h : C.loc p = .readMax d c) :
    Inv x (C.step p) := by
  obtain ⟨hself, hother, hD, hS, hR, hB⟩ := step_readMax h
  have hm := step_mono C p
  have hok := hI.ok p
  rw [h] at hok
  obtain ⟨hcd, hSd, hRc⟩ := hok
  have hpdep : (C.loc p).dep = some d := by rw [h]; rfl
  have hdD : d < D C := (hI.dep_lt p d hpdep).2
  have hdep := forall_of_self hother Loc.dep
    (by rw [hself, h]; cases prev c (D C) <;> rfl)
  have hsel := forall_of_self hother Loc.sel
    (by rw [hself, h]; cases prev c (D C) <;> rfl)
  have hcap := forall_of_self hother Loc.cap
    (by rw [hself, h]; cases prev c (D C) <;> rfl)
  have hblk := forall_iff_of_self hother Loc.blk
    (by rw [hself, h]; exact fun y => ⟨fun h' => absurd h' afterPrev_blk_empty, fun h' => h'.elim⟩)
  have hlost := forall_iff_of_self hother Loc.lost
    (by rw [hself, h]; cases prev c (D C) <;> exact fun _ => ⟨fun h' => h'.elim, fun h' => h'.elim⟩)
  refine hI.of_same' hdep hsel hcap ?_ hblk hlost hD hS hB ?_
  · intro i j ci m dj cj hi hj hle hs
    rw [hdep] at hj
    by_cases hip : i = p
    · subst hip; rw [hself] at hi
      have hmD : m = D C := by
        cases hp : prev c (D C) <;> rw [hp] at hi <;> simp [afterPrev, Loc.rinfo] at hi <;>
          exact hi.2.symm
      have := (hI.dep_lt j dj hj).2
      omega
    · rw [hother i hip] at hi; rw [hsel] at hs; exact hI.l2 i j ci m dj cj hi hj hle hs
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hself]
      cases hp : prev c (D C) with
      | none =>
        exact ⟨hcd, by rw [hS]; exact hSd, by rw [hR]; exact hRc, hdD, fun _ => rfl,
          fun r' hr' => by cases hr'⟩
      | some r =>
        obtain ⟨h1, h2, -⟩ := prev_some hp
        exact ⟨hcd, by rw [hS]; exact hSd, by rw [hR]; exact hRc, hdD, h1, h2⟩
    · rw [hother q hq]
      exact (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c' _ => by rw [hR])
        (fun y hy => by rw [hB]; exact hy) hm


/-! ### Line 11 -/

lemma afterPrev_blk {d : ℕ} {c : Node} {m : ℕ} {r y : Node} (hr : r.d ≤ m) (hrc : r < c) :
    (afterPrev (V := V) d c m (prev r m)).blk y ↔ y = r ∨ (Loc.retTas (V := V) d c m r).blk y := by
  cases hp : prev r m with
  | none =>
    simp only [afterPrev, Loc.blk]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy y r with h3 | h3 | h3
      · exact absurd h3 (prev_none hp y h1)
      · exact Or.inl h3
      · exact Or.inr ⟨h1, h3, h2⟩
    · rintro (rfl | ⟨h1, -, h3⟩)
      · exact ⟨hr, hrc⟩
      · exact ⟨h1, h3⟩
  | some r' =>
    obtain ⟨h1, -, h3⟩ := prev_some hp
    simp only [afterPrev, Loc.blk]
    constructor
    · rintro ⟨h4, h5, h6⟩
      rcases lt_trichotomy y r with h7 | h7 | h7
      · exact absurd (h3 y h4 h7) (not_le.2 h5)
      · exact Or.inl h7
      · exact Or.inr ⟨h4, h7, h6⟩
    · rintro (rfl | ⟨h4, h5, h6⟩)
      · exact ⟨hr, h1, hrc⟩
      · exact ⟨h4, h1.trans h5, h6⟩

lemma Inv.stepRetTas (hI : Inv x C) {d : ℕ} {c : Node} {m : ℕ} {r : Node}
    (h : C.loc p = .retTas d c m r) : Inv x (C.step p) := by
  obtain ⟨hself, hother, hD, hS, hR, hB⟩ := step_retTas h
  have hm := step_mono C p
  have hok := hI.ok p
  rw [h] at hok
  obtain ⟨hcd, hSd, hRc, hdm, hrc, hrm⟩ := hok
  have hBmono : ∀ y, B C y = true → B (C.step p) y = true := by
    intro y hy; rw [hB]; by_cases hyc : y = r
    · subst hyc; simp
    · simp [Function.update_of_ne hyc, hy]
  cases hb : B C r with
  | true =>
    rw [hb, ite_eq_left rfl] at hself
    have hB' : B (C.step p) = B C := by
      rw [hB]; funext y; by_cases hyr : y = r
      · subst hyr; simp [hb]
      · simp [Function.update_of_ne hyr]
    have hdep := forall_of_self hother Loc.dep (by rw [hself, h]; rfl)
    have hsel := forall_of_self hother Loc.sel (by rw [hself, h]; rfl)
    have hcap := forall_of_self hother Loc.cap (by rw [hself, h]; rfl)
    have hrinfo := forall_of_self hother Loc.rinfo (by rw [hself, h]; rfl)
    have hblk := forall_iff_of_self hother Loc.blk (by rw [hself, h]; exact fun _ => Iff.rfl)
    have hlost : ∀ q y, ((C.step p).loc q).lost y → (C.loc q).lost y ∨ (q = p ∧ y = r) := by
      intro q y hq
      by_cases hqp : q = p
      · subst hqp; rw [hself] at hq; exact Or.inr ⟨rfl, hq⟩
      · rw [hother q hqp] at hq; exact Or.inl hq
    -- the capturer of `r` won `r`
    have hcapr : ∃ q, (C.loc q).cap = some r := by
      rcases hI.tst_true r hb with hq | ⟨j, hj⟩
      · exact hq
      · have htj : (C.loc j).tryRet r := by
          rcases hj with hj | hj
          · exact Or.inl hj
          · exact Or.inr (Or.inl hj)
        have htp : (C.loc p).tryRet r := Or.inr (Or.inr ⟨d, c, m, h⟩)
        have := hI.tryRet_unique htj htp
        subst this
        rw [h] at hj
        rcases hj with hj | hj
        · exact absurd hj.2.1 (lt_irrefl _)
        · exact hj.elim
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hD]; exact hI.one_le
    · intro q d hd; rw [hdep] at hd; rw [hD]; exact hI.dep_lt q d hd
    · intro q q' d hq hq'; rw [hdep] at hq hq'; exact hI.dep_inj q q' d hq hq'
    · intro e a he; rw [hS] at he; rw [hB']
      obtain ⟨h1, ⟨q, hq⟩, h3⟩ := hI.cell e a he
      exact ⟨h1, ⟨q, by rw [hdep]; exact hq⟩, h3⟩
    · intro q
      by_cases hq : q = p
      · subst hq; rw [hself]
        exact ⟨hcd, by rw [hS]; exact hSd, by rw [hR]; exact hRc, hdm, hrc, hrm⟩
      · rw [hother q hq]
        exact (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c' _ => by rw [hR]) hBmono hm
    · intro j y hj; rw [hblk] at hj; rw [hB']; exact hI.blk_tst j y hj
    · intro y hy; rw [hB'] at hy
      rcases hI.tst_true y hy with ⟨q, hq⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨q, by rw [hcap]; exact hq⟩
      · exact Or.inr ⟨j, hj.imp ((hm j).blk y) ((hm j).lost y)⟩
    · intro q j y hq hj; rw [hcap] at hq; rw [hblk] at hj; exact hI.excl q j y hq hj
    · intro j y hj
      rcases hlost j y hj with hj | ⟨-, rfl⟩
      · obtain ⟨q, hq⟩ := hI.lost_cap j y hj; exact ⟨q, by rw [hcap]; exact hq⟩
      · obtain ⟨q, hq⟩ := hcapr; exact ⟨q, by rw [hcap]; exact hq⟩
    · intro i j ci m dj cj hi hj hle hs
      rw [hrinfo] at hi; rw [hdep] at hj; rw [hsel] at hs; exact hI.l2 i j ci m dj cj hi hj hle hs
    · intro j y c' hj hs hr; rw [hblk] at hj; rw [hsel] at hs; rw [hS]
      exact hI.blk_right j y c' hj hs hr
    · intro w hw v hv; rw [hS] at hw ⊢
      refine hI.lemma1 w ?_ v hv
      rcases hw with ⟨q, hq⟩ | hw
      · exact Or.inl ⟨q, by rw [← hsel]; exact hq⟩
      · exact Or.inr hw
  | false =>
    rw [hb] at hself
    simp only [Bool.false_eq_true, ite_false] at hself
    have hdep := forall_of_self hother Loc.dep (by rw [hself, h]; cases prev r m <;> rfl)
    have hsel := forall_of_self hother Loc.sel (by rw [hself, h]; cases prev r m <;> rfl)
    have hcap := forall_of_self hother Loc.cap (by rw [hself, h]; cases prev r m <;> rfl)
    have hrinfo := forall_of_self hother Loc.rinfo (by rw [hself, h]; cases prev r m <;> rfl)
    have hlost := forall_iff_of_self hother Loc.lost
      (by rw [hself, h]; cases prev r m <;> exact fun _ => ⟨fun h' => h'.elim, fun h' => h'.elim⟩)
    have hblk : ∀ q y, ((C.step p).loc q).blk y → (C.loc q).blk y ∨ (q = p ∧ y = r) := by
      intro q y hq
      by_cases hqp : q = p
      · subst hqp; rw [hself] at hq; rw [h]
        rcases (afterPrev_blk hrm hrc).1 hq with h' | h'
        · exact Or.inr ⟨rfl, h'⟩
        · exact Or.inl h'
      · rw [hother q hqp] at hq; exact Or.inl hq
    have hpr : ((C.step p).loc p).blk r := by
      rw [hself]; exact (afterPrev_blk hrm hrc).2 (Or.inl rfl)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hD]; exact hI.one_le
    · intro q d hd; rw [hdep] at hd; rw [hD]; exact hI.dep_lt q d hd
    · intro q q' d hq hq'; rw [hdep] at hq hq'; exact hI.dep_inj q q' d hq hq'
    · intro e a he; rw [hS] at he
      obtain ⟨h1, ⟨q, hq⟩, h3⟩ := hI.cell e a he
      exact ⟨h1, ⟨q, by rw [hdep]; exact hq⟩, hBmono a h3⟩
    · intro q
      by_cases hq : q = p
      · subst hq; rw [hself]
        cases hp : prev r m with
        | none =>
          exact ⟨hcd, by rw [hS]; exact hSd, by rw [hR]; exact hRc, hdm, fun _ => rfl,
            fun r' hr' => by cases hr'⟩
        | some r' =>
          obtain ⟨h1, h2, -⟩ := prev_some hp
          exact ⟨hcd, by rw [hS]; exact hSd, by rw [hR]; exact hRc, hdm, h1.trans hrc, h2⟩
      · rw [hother q hq]
        exact (hI.ok q).transfer (fun e _ => by rw [hS]) (fun c' _ => by rw [hR]) hBmono hm
    · intro j y hj
      rcases hblk j y hj with hj | ⟨-, rfl⟩
      · exact hBmono y (hI.blk_tst j y hj)
      · rw [hB]; simp
    · intro y hy
      by_cases hyr : y = r
      · subst hyr; exact Or.inr ⟨p, Or.inl hpr⟩
      · rw [hB, Function.update_of_ne hyr] at hy
        rcases hI.tst_true y hy with ⟨q, hq⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨q, by rw [hcap]; exact hq⟩
        · exact Or.inr ⟨j, hj.imp ((hm j).blk y) ((hm j).lost y)⟩
    · intro q j y hq hj; rw [hcap] at hq
      rcases hblk j y hj with hj | ⟨-, rfl⟩
      · exact hI.excl q j y hq hj
      · have := hI.cap_tst hq; rw [hb] at this; exact Bool.false_ne_true this
    · intro j y hj; rw [hlost] at hj
      obtain ⟨q, hq⟩ := hI.lost_cap j y hj; exact ⟨q, by rw [hcap]; exact hq⟩
    · intro i j ci m dj cj hi hj hle hs
      rw [hrinfo] at hi; rw [hdep] at hj; rw [hsel] at hs; exact hI.l2 i j ci m dj cj hi hj hle hs
    · intro j y c' hj hs hr; rw [hsel] at hs; rw [hS]
      rcases hblk j y hj with hj | ⟨rfl, rfl⟩
      · exact hI.blk_right j y c' hj hs hr
      · obtain ⟨a, ha, hya⟩ := hI.lemma1 c' (Or.inl ⟨j, hs⟩) y hr
        rcases eq_or_lt_of_le hya with heq | hlt
        · subst heq
          have := (hI.cell _ _ ha).2.2; rw [hb] at this; exact absurd this Bool.false_ne_true
        · exact ⟨a, ha, hlt⟩
    · intro w hw v hv; rw [hS] at hw ⊢
      refine hI.lemma1 w ?_ v hv
      rcases hw with ⟨q, hq⟩ | hw
      · exact Or.inl ⟨q, by rw [← hsel]; exact hq⟩
      · exact Or.inr hw

/-! ### The invariant holds in every reachable configuration -/

lemma Inv.step (hI : Inv x C) (p : ℕ) : Inv x (C.step p) := by
  cases h : C.loc p with
  | start x' => exact hI.stepStart h
  | scan x' d pr => exact hI.stepScan h
  | write x' d c => exact hI.stepWrite h
  | tas x' d c => exact hI.stepTas h
  | upd x' d c w => exact hI.stepUpd h
  | readMax d c => exact hI.stepReadMax h
  | retTas d c m r => exact hI.stepRetTas h
  | readReg d c m r => exact hI.stepReadReg h
  | done d c m r o => rw [step_done h]; exact hI

lemma Inv.run (hI : Inv x C) (σ : List ℕ) : Inv x ((alg V).run C σ) := by
  induction σ generalizing C with
  | nil => exact hI
  | cons p σ ih => exact ih (hI.step p)

/-- The invariant holds in every reachable configuration. -/
theorem inv_exec (x : ℕ → V) (σ : List ℕ) : Inv x ((alg V).exec x σ) := (inv_init x).run σ


end Podc.UnboundedConcurrency.Swap
