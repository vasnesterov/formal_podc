import Papers.PODC2011.UnboundedConcurrency.Swap.Step

/-!
# Lemma 1 and wait-freedom of Algorithm 1

* `lemma1`: in every reachable configuration, if a process tries to capture (or has captured) a
  node `w` of the right subtree of `v`, then a node `≥ v` of the depth of `v` has been recorded in
  `accessed` (the state form of Lemma 1; see the docstring for the difference with the paper);
* `next_ne_none`: Lemma 1 implies that `NextUnaccessedNodeAtDepth` always finds a node, so a
  capturing process is never stuck;
* `waitFree`: Algorithm 1 is wait-free in the unbounded concurrency model (every infinite
  schedule; a process that takes infinitely many steps returns). Every process returns after a
  number of its own steps bounded in terms of its `depth` and `maxdepth`: the capture phase visits
  the `2^depth` nodes of its depth in increasing order, the return phase the finitely many nodes of
  depth `≤ maxdepth` below `cap` in decreasing order.
-/

namespace Podc.UnboundedConcurrency.Swap

open Cslib.SharedMemory Cslib.SharedMemory.Arrival Cfg' Node

variable {V : Type} {x : ℕ → V} {C : Config V} {p : ℕ}

/-- **Lemma 1** of [AMW11] (state form): in every reachable configuration, if some process tries
to capture a node `w` (Lines 3–6; `w` is `cap`, also after a successful capture) and `w` lies in
the right subtree of `v`, then `accessed` contains a node `≥ v` of the depth of `v`.

The paper states that `v` *itself* has been recorded; we prove that the process of `v`'s depth
has recorded `v` or moved past it, which is what the wait-freedom argument uses. -/
theorem lemma1 (x : ℕ → V) (σ : List ℕ) {p : ℕ} {w v : Node}
    (hw : ((alg V).exec x σ |>.loc p).sel = some w) (hv : rightSub v w) :
    ∃ a, S ((alg V).exec x σ) v.d = some a ∧ v ≤ a :=
  (inv_exec x σ).lemma1 w (Or.inl ⟨p, hw⟩) v hv

/-- Consequence of Lemma 1: `NextUnaccessedNodeAtDepth` always finds a node (a capturing
process never runs out of nodes at its depth). -/
lemma Inv.next_ne_none (hI : Inv x C) {x' : V} {d : ℕ} {pr : Option Node}
    (h : C.loc p = .scan x' d pr) : next d (S C) ≠ none := by
  intro hn
  have hok := hI.ok p
  rw [h] at hok
  obtain ⟨-, hSd, hpr⟩ := hok
  have claim : S C d ≠ some (rm d) := by
    intro hS
    obtain ⟨j, hj⟩ := hpr (rm d) (by rw [← hSd, hS])
    obtain ⟨cj, mj, hrj, hlt, -⟩ := Loc.blk_spec hj
    have hselj := (Loc.rinfo_sel hrj).1
    obtain ⟨a', ha', hlt'⟩ := hI.blk_right j (rm d) cj hj hselj (rightSub_rm hlt)
    rw [rm_d, hS] at ha'
    cases ha'
    exact lt_irrefl _ hlt'
  obtain ⟨e, a, hea, hla⟩ := next_none hn (rm d) (rm_d d)
  obtain ⟨hae, -, -⟩ := hI.cell e a hea
  rcases eq_or_lt_of_le hla with heq | hlt
  · apply claim
    have hde : d = e := by rw [← hae, ← heq, rm_d]
    rw [heq, hde]; exact hea
  · obtain ⟨b, hb, hrb⟩ := hI.lemma1 a (Or.inr ⟨e, hea⟩) (rm d) (rightSub_rm hlt)
    rw [rm_d] at hb
    have hbd := (hI.cell d b hb).1
    exact claim (by rw [hb, le_antisymm (le_rm hbd) hrb])

/-! ### The progress measure -/

/-- Position of the next candidate node at depth `d` after the previous capture attempt. -/
def pos : Option Node → ℕ
  | none => 0
  | some c => c.k + 1

/-- A lexicographic progress measure: phase (Line 1, capture phase, Line 7, return phase), then
the remaining work in the phase. -/
noncomputable def μ : Loc V → ℕ ×ₗ ℕ
  | .start _ => toLex (3, 0)
  | .scan _ d pr => toLex (2, 4 * (2 ^ d - pos pr) + 4)
  | .write _ d c => toLex (2, 4 * (2 ^ d - c.k) + 3)
  | .tas _ d c => toLex (2, 4 * (2 ^ d - c.k) + 2)
  | .upd _ d c _ => toLex (2, 4 * (2 ^ d - c.k) + 1)
  | .readMax _ _ => toLex (1, 0)
  | .retTas _ _ m r => toLex (0, (below r m).card + 1)
  | .readReg _ _ _ _ => toLex (0, 0)
  | .done _ _ _ _ _ => toLex (0, 0)

/-- `p` has returned. -/
def Loc.Done : Loc V → Prop
  | .done _ _ _ _ _ => True
  | _ => False

/-- Each step of a process that has not returned decreases its measure (or makes it return). -/
lemma Inv.progress (hI : Inv x C) (hnd : ¬ (C.loc p).Done) :
    ((C.step p).loc p).Done ∨ μ ((C.step p).loc p) < μ (C.loc p) := by
  cases h : C.loc p with
  | start x' => right; rw [(step_start h).1]; simp [μ, Prod.Lex.toLex_lt_toLex]
  | scan x' d pr =>
    right
    rw [(step_scan h).1]
    cases hn : next d (S C) with
    | none => exact absurd hn (hI.next_ne_none h)
    | some c =>
      simp only [μ, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, true_and]
      obtain ⟨hcd, habove, -⟩ := next_some hn
      have hok := hI.ok p
      rw [h] at hok
      obtain ⟨-, hSd, -⟩ := hok
      have hpos : pos pr ≤ c.k := by
        cases pr with
        | none => exact Nat.zero_le _
        | some c' =>
          have hlt := habove d c' hSd
          have hc'd := (hI.cell d c' hSd).1
          have := (lt_iff_k_of_d_eq (hc'd.trans hcd.symm)).1 hlt
          simp only [pos]; omega
      have : 2 ^ d - c.k ≤ 2 ^ d - pos pr := Nat.sub_le_sub_left hpos _
      omega
  | write x' d c => right; rw [(step_write h).1]; simp [μ, Prod.Lex.toLex_lt_toLex]
  | tas x' d c => right; rw [(step_tas h).1]; simp [μ, Prod.Lex.toLex_lt_toLex]
  | upd x' d c w =>
    right
    rw [(step_upd h).1]
    cases w
    · show μ (Loc.scan x' d (some c)) < μ (Loc.upd x' d c false)
      simp only [μ, Prod.Lex.toLex_lt_toLex, pos, lt_irrefl, false_or, true_and]
      have hok := hI.ok p
      rw [h] at hok
      have hk := c.hk
      rw [hok.2.1] at hk
      omega
    · simp [μ, Prod.Lex.toLex_lt_toLex]
  | readMax d c =>
    right
    rw [(step_readMax h).1]
    cases prev c (D C) <;> simp [afterPrev, μ, Prod.Lex.toLex_lt_toLex]
  | retTas d c m r =>
    right
    rw [(step_retTas h).1]
    by_cases hb : B C r = true
    · rw [ite_eq_left hb]; simp [μ, Prod.Lex.toLex_lt_toLex]
    · rw [ite_eq_right hb]
      cases hp : prev r m with
      | none => simp [afterPrev, μ, Prod.Lex.toLex_lt_toLex]
      | some r' =>
        have := card_below_lt hp
        simp only [afterPrev, μ, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, true_and]
        omega
  | readReg d c m r =>
    left; rw [(step_readReg h).1]; trivial
  | done d c m r o => rw [h] at hnd; exact absurd trivial hnd

/-! ### Wait-freedom -/

lemma exec_pre_succ (x : ℕ → V) (s : ℕ → ℕ) (t : ℕ) :
    (alg V).exec x (pre s (t + 1)) = ((alg V).exec x (pre s t)).step (s t) := by
  rw [pre_succ, Alg.exec_concat]

lemma loc_const (x : ℕ → V) (s : ℕ → ℕ) (p t : ℕ) :
    ∀ n, (∀ u, t ≤ u → u < t + n → s u ≠ p) →
      ((alg V).exec x (pre s (t + n))).loc p = ((alg V).exec x (pre s t)).loc p := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [← Nat.add_assoc, exec_pre_succ, Cfg.step_loc_other _ (Ne.symm (h (t + n) (by omega)
      (by omega))), ih (fun u h1 h2 => h u h1 (by omega))]

/-- **Wait-freedom** of Algorithm 1 in the unbounded concurrency model: for every infinite
schedule (any number of processes, arriving at any time), every process that takes infinitely
many steps returns. -/
theorem waitFree : WaitFree (alg V) infArrival := by
  intro x s _ p hinf
  classical
  let L : ℕ → Loc V := fun t => ((alg V).exec x (pre s t)).loc p
  suffices H : ∀ a : ℕ ×ₗ ℕ, ∀ t, μ (L t) = a → ∃ t', (L t').Done by
    obtain ⟨t', ht'⟩ := H _ 0 rfl
    refine ⟨t', ?_⟩
    simp only [L] at ht'
    cases hc : ((alg V).exec x (pre s t')).loc p <;> rw [hc] at ht' <;> simp [Loc.Done] at ht'
    rename_i o
    exact ⟨o, by unfold Cfg.Out; rw [hc]; rfl⟩
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
  intro t ht
  by_cases hd : (L t).Done
  · exact ⟨t, hd⟩
  obtain ⟨t1, ht1, hst1⟩ := hinf t
  have hex : ∃ u, t ≤ u ∧ s u = p := ⟨t1, ht1, hst1⟩
  let u := Nat.find hex
  have hu : t ≤ u ∧ s u = p := Nat.find_spec hex
  have hconst : L u = L t := by
    have := loc_const x s p t (u - t) (fun v h1 h2 hv => Nat.find_min hex (by omega) ⟨h1, hv⟩)
    simp only [L]
    rw [← this]; congr 3; omega
  have hI := inv_exec x (pre s u)
  have hstep : L (u + 1) = (((alg V).exec x (pre s u)).step p).loc p := by
    simp only [L]; rw [exec_pre_succ, hu.2]
  have hnd : ¬ (((alg V).exec x (pre s u)).loc p).Done := by
    change ¬ (L u).Done; rw [hconst]; exact hd
  rcases hI.progress hnd with h1 | h1
  · exact ⟨u + 1, by rw [hstep]; exact h1⟩
  · refine ih _ ?_ (u + 1) rfl
    rw [← ht, ← hconst, hstep]; exact h1

end Podc.UnboundedConcurrency.Swap
