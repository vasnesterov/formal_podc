import Papers.PODC2012.IteratedSnapshotFD.Model

/-!
# The consensus algorithm of Figure 5 (Appendix C): definitions and safety

Each process `pᵢ` keeps `⟨estᵢ, r_leaderᵢ, val_ld_seenᵢ, decᵢ⟩` (`Loc`). In each round it reads its
failure-detector output `cur_leaderᵢ` (line 4), resets `val_ld_seenᵢ` and updates `r_leaderᵢ` if the
leader changed (line 5, `wr`), writes its tuple into `IS[r]` and gets a view (line 6), and then
updates its state (lines 7–18, the relation `Upd`).

The choices "∃ v" at lines 12 and 15 are **nondeterministic**: `Upd` allows every witness, so the
safety results below hold for every way of resolving them.

* `validity` (Lemma 1): every estimate, hence every decision, is a proposed value.
* `inv` (Claim C1 of Lemma 3, strengthened): in every round, the tuples with
  `val_ld_seen = true, dec = false` carry the same estimate and the same leader `ℓ`, **and the tuple
  written by `ℓ` itself (if `ℓ` has not decided) carries that estimate too**. The second half is
  the missing ingredient of the paper's proof.
* `agreement` (Lemma 3).

These results do not need any property of the leader outputs: they hold for arbitrary
failure-detector outputs, crashes and IIS schedules.
-/

set_option linter.unusedSectionVars false

namespace Podc.IteratedSnapshotFD

variable {P V : Type}

/-- Local state `⟨est, r_leader, val_ld_seen, dec⟩` of a process; `r_leader = none` is `⊥`. -/
structure Loc (P V : Type) where
  est : V
  rl : Option P
  vls : Bool
  dec : Bool

/-- Initial state (line 1). -/
def Loc.init (v : V) : Loc P V := ⟨v, none, false, false⟩

variable [DecidableEq P]

/-- Lines 4–5: the tuple written in the round, after reading the leader `l`. -/
def wr (s : Loc P V) (l : P) : Loc P V :=
  if s.rl = some l then s else { s with rl := some l, vls := false }

@[simp] theorem wr_est (s : Loc P V) (l : P) : (wr s l).est = s.est := by
  unfold wr; split_ifs <;> rfl

@[simp] theorem wr_dec (s : Loc P V) (l : P) : (wr s l).dec = s.dec := by
  unfold wr; split_ifs <;> rfl

@[simp] theorem wr_rl (s : Loc P V) (l : P) : (wr s l).rl = some l := by
  unfold wr; split_ifs with h
  · exact h
  · rfl

theorem vls_of_wr {s : Loc P V} {l : P} (h : (wr s l).vls = true) : s.vls = true := by
  unfold wr at h; split_ifs at h
  exact h

theorem wr_eq_of_vls {s : Loc P V} {l : P} (h : (wr s l).vls = true) : wr s l = s := by
  unfold wr at h ⊢; split_ifs at h ⊢
  rfl

/-- Line 12: `v` is a candidate estimate in view `vw` for the round leader `l`: either the estimate
of `p_l` (first disjunct) or the estimate of a tuple with `val_ld_seen = true` (second disjunct). -/
def Cand (w : P → Loc P V) (vw : Finset P) (l : Option P) (v : V) : Prop :=
  (∃ j ∈ vw, some j = l ∧ (w j).est = v) ∨ (∃ j ∈ vw, (w j).vls = true ∧ (w j).est = v)

/-- Line 9: all tuples of the view have `val_ld_seen = true` and estimate `v`. -/
def Unanim (w : P → Loc P V) (vw : Finset P) (v : V) : Prop :=
  ∀ j ∈ vw, (w j).vls = true ∧ (w j).est = v

/-- Lines 7–18 of Figure 5: process `i`, having written the tuples `w` (of all processes) and
obtained the view `vw`, moves to the state `t`. -/
inductive Upd (w : P → Loc P V) (vw : Finset P) (i : P) : Loc P V → Prop
  /-- line 7: already decided. -/
  | done (h : (w i).dec = true) : Upd w vw i (w i)
  /-- line 8: a decided value is seen. -/
  | seeDec (h0 : (w i).dec = false) (j : P) (hj : j ∈ vw) (hd : (w j).dec = true) :
      Upd w vw i { w i with est := (w j).est, dec := true }
  /-- line 9. -/
  | unanim (h0 : (w i).dec = false) (hnd : ∀ j ∈ vw, (w j).dec = false) (v : V)
      (hv : Unanim w vw v) : Upd w vw i { w i with est := v, dec := true }
  /-- lines 11–13. -/
  | adopt (h0 : (w i).dec = false) (hnd : ∀ j ∈ vw, (w j).dec = false)
      (hnu : ∀ v, ¬ Unanim w vw v) (l : Option P) (hl : ∀ j ∈ vw, (w j).rl = l) (v : V)
      (hv : Cand w vw l v) : Upd w vw i { w i with est := v, vls := true }
  /-- lines 11–12 with a false predicate at line 12. -/
  | keep (h0 : (w i).dec = false) (hnd : ∀ j ∈ vw, (w j).dec = false)
      (hnu : ∀ v, ¬ Unanim w vw v) (l : Option P) (hl : ∀ j ∈ vw, (w j).rl = l)
      (hc : ∀ v, ¬ Cand w vw l v) : Upd w vw i (w i)
  /-- line 15, a tuple with `val_ld_seen = true` is seen. -/
  | mixAdopt (h0 : (w i).dec = false) (hnd : ∀ j ∈ vw, (w j).dec = false)
      (hnu : ∀ v, ¬ Unanim w vw v) (hnl : ∀ l : Option P, ¬ ∀ j ∈ vw, (w j).rl = l) (j : P)
      (hj : j ∈ vw) (hv : (w j).vls = true) :
      Upd w vw i { w i with est := (w j).est, vls := false }
  /-- line 15, no such tuple. -/
  | mixKeep (h0 : (w i).dec = false) (hnd : ∀ j ∈ vw, (w j).dec = false)
      (hnu : ∀ v, ¬ Unanim w vw v) (hnl : ∀ l : Option P, ¬ ∀ j ∈ vw, (w j).rl = l)
      (hnv : ∀ j ∈ vw, (w j).vls = false) : Upd w vw i { w i with vls := false }

/-- An execution of Figure 5 in `IIS_n` on the schedule `σ`, with inputs `input`, leader outputs
`ld r i` (the value of `Ω*.read()` at line 4 of round `r`) and states `st r i` at the beginning of
round `r`. Crashed processes keep their state. -/
structure Exec (σ : Schedule P) (input : P → V) where
  /-- Output of the leader oracle read by `i` at the beginning of round `r`. -/
  ld : ℕ → P → P
  /-- State of `i` at the beginning of round `r`. -/
  st : ℕ → P → Loc P V
  init : ∀ i, st 0 i = Loc.init (input i)
  step : ∀ r i, i ∈ (σ.rd r).part →
    Upd (fun j => wr (st r j) (ld r j)) ((σ.rd r).view i) i (st (r + 1) i)
  frozen : ∀ r i, i ∉ (σ.rd r).part → st (r + 1) i = st r i

namespace Exec

variable {σ : Schedule P} {input : P → V} (E : Exec σ input)

/-- The tuple written by `j` into `IS[r]`. -/
def W (r : ℕ) (j : P) : Loc P V := wr (E.st r j) (E.ld r j)

theorem step' (r : ℕ) (i : P) (hi : i ∈ (σ.rd r).part) :
    Upd (E.W r) ((σ.rd r).view i) i (E.st (r + 1) i) := E.step r i hi

/-- The decision of `i` (if any) by the beginning of round `r`: `decᵢ = true`, decided value `estᵢ`. -/
def Decided (r : ℕ) (i : P) : Prop := (E.st r i).dec = true

/-! ### Generic facts about `Upd` -/

/-- The new estimate is the old one or an estimate read in the view. -/
theorem _root_.Podc.IteratedSnapshotFD.Upd.est_mem {w : P → Loc P V} {vw : Finset P} {i : P} {t : Loc P V}
    (h : Upd w vw i t) (hi : i ∈ vw) : t.est = (w i).est ∨ ∃ j ∈ vw, t.est = (w j).est := by
  cases h with
  | done => exact Or.inl rfl
  | seeDec _ j hj => exact Or.inr ⟨j, hj, rfl⟩
  | unanim _ _ v hv => exact Or.inl (hv i hi).2.symm
  | adopt _ _ _ l hl v hv =>
    rcases hv with ⟨j, hj, -, rfl⟩ | ⟨j, hj, -, rfl⟩ <;> exact Or.inr ⟨j, hj, rfl⟩
  | keep => exact Or.inl rfl
  | mixAdopt _ _ _ _ j hj => exact Or.inr ⟨j, hj, rfl⟩
  | mixKeep => exact Or.inl rfl

/-- `i` decides `v` (line 10) at some round. -/
def Decides (i : P) (v : V) : Prop := ∃ r, (E.st r i).dec = true ∧ (E.st r i).est = v

/-! ### Validity (Lemma 1) -/

theorem est_input (r : ℕ) (i : P) : ∃ j, (E.st r i).est = input j := by
  induction r generalizing i with
  | zero => exact ⟨i, by rw [E.init]; rfl⟩
  | succ r ih =>
    by_cases hi : i ∈ (σ.rd r).part
    · rcases (E.step' r i hi).est_mem ((σ.rd r).self_mem i hi) with h | ⟨j, -, h⟩
      · rw [h, W, wr_est]; exact ih i
      · rw [h, W, wr_est]; exact ih j
    · rw [E.frozen r i hi]; exact ih i

/-- **Lemma 1 (validity).** Every decided value is a proposed value. -/
theorem validity {i : P} {v : V} (h : E.Decides i v) : ∃ j, v = input j := by
  obtain ⟨r, -, rfl⟩ := h
  obtain ⟨j, hj⟩ := E.est_input r i
  exact ⟨j, hj⟩

end Exec

/-! ### Claim C1, strengthened -/

/-- The invariant of a round with written tuples `w` and participants `S`: (C1) all tuples with
`val_ld_seen = true` and `dec = false` carry the same estimate and the same leader; (L) if such a
tuple names `ℓ` as leader, then `ℓ`'s own tuple carries the same estimate (unless `ℓ` decided). -/
def Inv (w : P → Loc P V) (S : Finset P) : Prop :=
  (∀ j ∈ S, ∀ k ∈ S, (w j).vls = true → (w j).dec = false → (w k).vls = true →
      (w k).dec = false → (w j).est = (w k).est ∧ (w j).rl = (w k).rl) ∧
  (∀ j ∈ S, ∀ l ∈ S, (w j).vls = true → (w j).dec = false → (w j).rl = some l →
      (w l).dec = false → (w l).est = (w j).est)

/-- Two candidate values (line 12) for the same leader in two views without decided tuples are
equal. -/
theorem cand_eq {w : P → Loc P V} {S vw₁ vw₂ : Finset P} (hI : Inv w S) (h₁ : vw₁ ⊆ S)
    (h₂ : vw₂ ⊆ S) (hd₁ : ∀ j ∈ vw₁, (w j).dec = false) (hd₂ : ∀ j ∈ vw₂, (w j).dec = false)
    {l : Option P} (hl₁ : ∀ j ∈ vw₁, (w j).rl = l) (hl₂ : ∀ j ∈ vw₂, (w j).rl = l) {v₁ v₂ : V}
    (hv₁ : Cand w vw₁ l v₁) (hv₂ : Cand w vw₂ l v₂) : v₁ = v₂ := by
  rcases hv₁ with ⟨j₁, hj₁, hl1, rfl⟩ | ⟨k₁, hk₁, hvk₁, rfl⟩ <;>
  rcases hv₂ with ⟨j₂, hj₂, hl2, rfl⟩ | ⟨k₂, hk₂, hvk₂, rfl⟩
  · rw [← hl2] at hl1; cases hl1; rfl
  · exact hI.2 k₂ (h₂ hk₂) j₁ (h₁ hj₁) hvk₂ (hd₂ k₂ hk₂) (by rw [hl₂ k₂ hk₂, hl1]) (hd₁ j₁ hj₁)
  · exact (hI.2 k₁ (h₁ hk₁) j₂ (h₂ hj₂) hvk₁ (hd₁ k₁ hk₁) (by rw [hl₁ k₁ hk₁, hl2])
      (hd₂ j₂ hj₂)).symm
  · exact (hI.1 k₁ (h₁ hk₁) k₂ (h₂ hk₂) hvk₁ (hd₁ k₁ hk₁) hvk₂ (hd₂ k₂ hk₂)).1

/-- A state with `val_ld_seen = true, dec = false` after a round comes from line 13. -/
theorem Upd.vls_true {w : P → Loc P V} {vw : Finset P} {i : P} {t : Loc P V}
    (h : Upd w vw i t) (hi : i ∈ vw) (hv : t.vls = true) (hd : t.dec = false) :
    (∀ j ∈ vw, (w j).dec = false) ∧ (∀ j ∈ vw, (w j).rl = (w i).rl) ∧
      Cand w vw (w i).rl t.est ∧ t.rl = (w i).rl := by
  cases h with
  | done h => simp [h] at hd
  | seeDec => simp at hd
  | unanim => simp at hd
  | adopt _ hnd _ l hl v hcand =>
    have := hl i hi
    subst this
    exact ⟨hnd, hl, hcand, rfl⟩
  | keep _ _ _ l hl hc => exact absurd (Or.inr ⟨i, hi, hv, rfl⟩) (hc _)
  | mixAdopt => simp at hv
  | mixKeep => simp at hv

namespace Exec

variable {σ : Schedule P} {input : P → V} (E : Exec σ input)

theorem W_zero_vls (j : P) : (E.W 0 j).vls = false := by
  simp [W, E.init, wr, Loc.init]

theorem W_succ_of_vls {r : ℕ} {j : P} (h : (E.W (r + 1) j).vls = true) :
    E.W (r + 1) j = E.st (r + 1) j := wr_eq_of_vls h

/-- The invariant is preserved from round `r` to round `r + 1`. -/
theorem inv_succ (r : ℕ) (hI : Inv (E.W r) (σ.rd r).part) :
    Inv (E.W (r + 1)) (σ.rd (r + 1)).part := by
  set R := σ.rd r with hR
  -- facts about a process whose round-(r+1) tuple has vls = true, dec = false
  have key : ∀ j ∈ (σ.rd (r + 1)).part, (E.W (r + 1) j).vls = true →
      (E.W (r + 1) j).dec = false →
      j ∈ R.part ∧ (∀ k ∈ R.view j, (E.W r k).dec = false) ∧
      (∀ k ∈ R.view j, (E.W r k).rl = (E.W r j).rl) ∧
      Cand (E.W r) (R.view j) (E.W r j).rl (E.W (r + 1) j).est ∧
      (E.W (r + 1) j).rl = (E.W r j).rl := by
    intro j hj hv hd
    have hjR : j ∈ R.part := σ.mono r hj
    have heq := E.W_succ_of_vls hv
    rw [heq] at hv hd ⊢
    exact ⟨hjR, (E.step' r j hjR).vls_true (R.self_mem j hjR) hv hd⟩
  refine ⟨fun j hj k hk hvj hdj hvk hdk => ?_, fun j hj l hl hvj hdj hrl hdl => ?_⟩
  · obtain ⟨hjR, hndj, hlj, hcj, hrj⟩ := key j hj hvj hdj
    obtain ⟨hkR, hndk, hlk, hck, hrk⟩ := key k hk hvk hdk
    have hsame : (E.W r j).rl = (E.W r k).rl := by
      rcases R.contain j hjR k hkR with h | h
      · exact hlk j (h (R.self_mem j hjR))
      · exact (hlj k (h (R.self_mem k hkR))).symm
    rw [hsame] at hlj hcj
    refine ⟨cand_eq hI (R.view_sub j hjR) (R.view_sub k hkR) hndj hndk hlj hlk hcj hck, ?_⟩
    rw [hrj, hrk, hsame]
  · obtain ⟨hjR, hndj, hlj, hcj, hrj⟩ := key j hj hvj hdj
    have hlR : l ∈ R.part := σ.mono r hl
    have hjl : (E.W r j).rl = some l := by rw [← hrj]; exact hrl
    rw [hjl] at hlj hcj
    -- the new state of `l`
    have hU := E.step' r l hlR
    have hdl' : (E.st (r + 1) l).dec = false := by simpa [W] using hdl
    have hest : (E.W (r + 1) l).est = (E.st (r + 1) l).est := by simp [W]
    rw [hest]
    generalize E.st (r + 1) l = t at hU hdl'
    -- Case A: the view of `l` is inside the view of `j`
    have caseA : R.view l ⊆ R.view j → t.est = (E.W (r + 1) j).est := by
      intro hsub
      have hlv : l ∈ R.view l := R.self_mem l hlR
      have hlrl : (E.W r l).rl = some l := hlj l (hsub hlv)
      cases hU with
      | done h => exact absurd h (by rw [hndj l (hsub hlv)]; simp)
      | seeDec _ k hk hd => exact absurd hd (by rw [hndj k (hsub hk)]; simp)
      | unanim => simp at hdl'
      | adopt _ hnd _ l' hl' v hv =>
        have : l' = some l := by rw [← hl' l hlv, hlrl]
        subst this
        exact cand_eq hI (R.view_sub l hlR) (R.view_sub j hjR) hnd hndj hl' hlj hv hcj
      | keep _ _ _ l' hl' hc =>
        have : l' = some l := by rw [← hl' l hlv, hlrl]
        subst this
        exact absurd (Or.inl ⟨l, hlv, rfl, rfl⟩) (hc _)
      | mixAdopt _ _ _ hnl => exact absurd (fun k hk => hlj k (hsub hk)) (hnl _)
      | mixKeep _ _ _ hnl => exact absurd (fun k hk => hlj k (hsub hk)) (hnl _)
    by_cases hlj' : l ∈ R.view j
    · exact caseA (R.immed l hlR j hjR hlj')
    rcases R.contain l hlR j hjR with hsub | hsub
    · exact caseA hsub
    -- Case B: the view of `j` is inside the view of `l`, and `l` is not in the view of `j`
    obtain ⟨k, hk, hvk, hek⟩ : ∃ k ∈ R.view j, (E.W r k).vls = true ∧
        (E.W r k).est = (E.W (r + 1) j).est := by
      rcases hcj with ⟨j₁, hj₁, h₁, -⟩ | h
      · cases h₁; exact absurd hj₁ hlj'
      · exact h
    cases hU with
    | done h => simp [h] at hdl'
    | seeDec => simp at hdl'
    | unanim => simp at hdl'
    | adopt _ hnd _ l' hl' v hv =>
      have : l' = some l := by rw [← hl' j (hsub (R.self_mem j hjR)), hlj j (R.self_mem j hjR)]
      subst this
      exact cand_eq hI (R.view_sub l hlR) (R.view_sub j hjR) hnd hndj hl' hlj hv hcj
    | keep _ _ _ l' hl' hc => exact absurd (Or.inr ⟨k, hsub hk, hvk, rfl⟩) (hc _)
    | mixAdopt _ hnd _ _ k' hk' hvk' =>
      show (E.W r k').est = _
      rw [← hek]
      exact (hI.1 k' (R.view_sub l hlR hk') k (R.view_sub j hjR hk) hvk' (hnd k' hk') hvk
        (hndj k hk)).1
    | mixKeep _ _ _ _ hnv => exact absurd (hnv k (hsub hk)) (by rw [hvk]; simp)

/-- **Claim C1** (strengthened), in every round. -/
theorem inv (r : ℕ) : Inv (E.W r) (σ.rd r).part := by
  induction r with
  | zero =>
    exact ⟨fun j _ _ _ h => by simp [E.W_zero_vls] at h,
      fun j _ _ _ h => by simp [E.W_zero_vls] at h⟩
  | succ r ih => exact E.inv_succ r ih

/-! ### Agreement (Lemma 3) -/

/-- After the first decision round, all participants hold the decided value `v`, and so do all
decided processes. -/
def Settled (r : ℕ) (v : V) : Prop :=
  (∀ i ∈ (σ.rd r).part, (E.st r i).est = v) ∧ (∀ i, (E.st r i).dec = true → (E.st r i).est = v)

theorem settled_succ {r : ℕ} {v : V} (h : E.Settled r v) : E.Settled (r + 1) v := by
  have hpart : ∀ i ∈ (σ.rd r).part, (E.st (r + 1) i).est = v := by
    intro i hi
    rcases (E.step' r i hi).est_mem ((σ.rd r).self_mem i hi) with h' | ⟨j, hj, h'⟩
    · rw [h', W, wr_est]; exact h.1 i hi
    · rw [h', W, wr_est]; exact h.1 j ((σ.rd r).view_sub i hi hj)
  refine ⟨fun i hi => hpart i (σ.mono r hi), fun i hd => ?_⟩
  by_cases hi : i ∈ (σ.rd r).part
  · exact hpart i hi
  · rw [E.frozen r i hi] at hd ⊢; exact h.2 i hd

theorem settled_le {r r' : ℕ} {v : V} (h : E.Settled r v) (hr : r ≤ r') : E.Settled r' v := by
  induction hr with
  | refl => exact h
  | step _ ih => exact E.settled_succ ih

/-- The first decisions (round `r₀`) are taken at line 9 with a common value, and at the end of
round `r₀` every participant holds it. -/
theorem settled_first {r₀ : ℕ} (hno : ∀ i, (E.st r₀ i).dec = false) {d : P}
    (hd : (E.st (r₀ + 1) d).dec = true) : E.Settled (r₀ + 1) (E.st (r₀ + 1) d).est := by
  set R := σ.rd r₀ with hR
  have hWno : ∀ j, (E.W r₀ j).dec = false := fun j => by simp [W, hno j]
  have frozen_nd : ∀ i, i ∉ R.part → (E.st (r₀ + 1) i).dec = false := fun i hi => by
    rw [E.frozen r₀ i hi]; exact hno i
  have hdR : d ∈ R.part := by
    by_contra h; rw [frozen_nd d h] at hd; simp at hd
  have hU := E.step' r₀ d hdR
  generalize E.st (r₀ + 1) d = t at hU hd ⊢
  -- `d` decided at line 9
  obtain ⟨v, hv, rfl⟩ : ∃ v, Unanim (E.W r₀) (R.view d) v ∧ t.est = v := by
    cases hU with
    | done h => simp [hWno] at h
    | seeDec _ j _ h => simp [hWno] at h
    | unanim _ _ v hv => exact ⟨v, hv, rfl⟩
    | adopt => simp [hWno] at hd
    | keep => simp [hWno] at hd
    | mixAdopt => simp [hWno] at hd
    | mixKeep => simp [hWno] at hd
  have hI := E.inv r₀
  have hdv := R.self_mem d hdR
  have hpart : ∀ i ∈ R.part, (E.st (r₀ + 1) i).est = t.est := by
    intro i hi
    have hUi := E.step' r₀ i hi
    have hiv := R.self_mem i hi
    generalize E.st (r₀ + 1) i = u at hUi
    rcases R.contain i hi d hdR with hsub | hsub
    · cases hUi with
      | done h => simp [hWno] at h
      | seeDec _ j _ h => simp [hWno] at h
      | unanim _ _ v' hv' => exact ((hv' i hiv).2.symm.trans (hv i (hsub hiv)).2)
      | adopt _ _ hnu => exact absurd (fun j hj => hv j (hsub hj)) (hnu _)
      | keep _ _ hnu => exact absurd (fun j hj => hv j (hsub hj)) (hnu _)
      | mixAdopt _ _ hnu => exact absurd (fun j hj => hv j (hsub hj)) (hnu _)
      | mixKeep _ _ hnu => exact absurd (fun j hj => hv j (hsub hj)) (hnu _)
    · have hdi := hsub hdv
      cases hUi with
      | done h => simp [hWno] at h
      | seeDec _ j _ h => simp [hWno] at h
      | unanim _ _ v' hv' => exact ((hv' d hdi).2.symm.trans (hv d hdv).2)
      | adopt _ _ _ l hl v' hc =>
        show v' = _
        rcases hc with ⟨j₁, hj₁, h₁, rfl⟩ | ⟨k, hk, hvk, rfl⟩
        · rw [← (hv d hdv).2]
          exact hI.2 d hdR j₁ (R.view_sub i hi hj₁) (hv d hdv).1 (hWno d)
            (by rw [hl d hdi, h₁]) (hWno j₁)
        · rw [← (hv d hdv).2]
          exact (hI.1 k (R.view_sub i hi hk) d hdR hvk (hWno k) (hv d hdv).1 (hWno d)).1
      | keep _ _ _ l hl hc => exact absurd (Or.inr ⟨d, hdi, (hv d hdv).1, rfl⟩) (hc _)
      | mixAdopt _ _ _ _ k hk hvk =>
        show (E.W r₀ k).est = _
        rw [← (hv d hdv).2]
        exact (hI.1 k (R.view_sub i hi hk) d hdR hvk (hWno k) (hv d hdv).1 (hWno d)).1
      | mixKeep _ _ _ _ hnv => exact absurd (hnv d hdi) (by rw [(hv d hdv).1]; simp)
  refine ⟨fun i hi => hpart i (σ.mono r₀ hi), fun i hi => ?_⟩
  by_cases hiR : i ∈ R.part
  · exact hpart i hiR
  · rw [frozen_nd i hiR] at hi; simp at hi

/-- **Lemma 3 (agreement).** No two processes decide different values — for every IIS schedule,
every crash pattern, every sequence of leader outputs and every resolution of the choices at
lines 12 and 15. -/
theorem agreement {i j : P} {v v' : V} (hi : E.Decides i v) (hj : E.Decides j v') : v = v' := by
  classical
  obtain ⟨r, hdr, rfl⟩ := hi
  obtain ⟨r', hdr', rfl⟩ := hj
  have hex : ∃ r, ∃ i, (E.st r i).dec = true := ⟨r, i, hdr⟩
  set r₁ := Nat.find hex with hr₁
  obtain ⟨d, hd⟩ := Nat.find_spec hex
  have hr₁0 : r₁ ≠ 0 := by
    intro h; rw [← hr₁, h, E.init] at hd; simp [Loc.init] at hd
  obtain ⟨r₀, hr₀⟩ := Nat.exists_eq_succ_of_ne_zero hr₁0
  have hno : ∀ i, (E.st r₀ i).dec = false := by
    intro i
    have := Nat.find_min hex (show r₀ < r₁ by omega)
    push Not at this
    simpa using this i
  rw [← hr₁, hr₀] at hd
  have hS := E.settled_first hno hd
  have m1 : r₁ ≤ r := Nat.find_min' hex ⟨i, hdr⟩
  have m2 : r₁ ≤ r' := Nat.find_min' hex ⟨j, hdr'⟩
  have h1 := (E.settled_le hS (show r₀ + 1 ≤ r by omega)).2 i hdr
  have h2 := (E.settled_le hS (show r₀ + 1 ≤ r' by omega)).2 j hdr'
  rw [h1, h2]

end Exec

end Podc.IteratedSnapshotFD
