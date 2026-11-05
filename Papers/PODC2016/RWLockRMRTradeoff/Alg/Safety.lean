import Papers.PODC2016.RWLockRMRTradeoff.Alg.Model
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Mutual exclusion of the repaired algorithm `A_f`

For the repaired algorithm (`W[i]` read before `C[i]` in line 51, `op'` tested in line 47) we
prove Mutual Exclusion (Lemmas 8 and 9 of the paper) for any number of readers, any static
partition into groups, one writer, and unboundedly many passages.

The proof is by an inductive invariant `Inv`, in three layers:

* `InvA` — bookkeeping: `RSIG` as a function of the writer's program counter; `C[g]`, `W[g]`
  count the group-`g` readers in lines 32–40 resp. 36–37 (incl. `HelpWCS` called from line 35);
  sequence numbers held by readers are `≤ WSEQ`, and equal to `WSEQ` only if the writer is past
  line 11 (`seq'`) resp. line 18 (`seq`, `hseq`); `WSIG[g]` for the current passage only holds
  the tags the writer's position allows.
* `InvB` — Lemma 11: once the writer has passed group `g` in the loop of lines 12–17, no group-`g`
  reader waits (lines 34–37) for an old passage; at line 18 no reader waits at all.
* `InvC` — Lemma 8: in lines 19–24, `WSIG[g] = <WSEQ, CS>` implies that no group-`g` reader is
  in the CS; all groups already passed in the loop of lines 19–23 have no reader in the CS; a
  helper about to CAS in line 52 for the current passage has seen `W[g] = C[g]` (so no group-`g`
  reader is in the CS), and a helper between the two reads of line 51 holds a value `≤ W[g]`
  (`W[g]` does not decrease while the writer is in lines 19–24).
-/

-- The case-splitting macros `wsplit` / `rsplit` run one finishing tactic on all cases; parts of
-- it are unused in some cases.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace Podc.RWLockRMRTradeoff.Alg

open Finset

variable {n G : ℕ}

/-! ### Auxiliary predicates -/

/-- The writer is in lines 19–24 (after writing `<WSEQ, WAIT>` to `RSIG`, before line 25). -/
def WPc.ph20 : WPc G → Prop
  | .l20 _ | .l21 _ | .cs => True
  | _ => False

/-- The writer is in lines 12–24 (after writing `<WSEQ, PREENTRY>` to `RSIG`, before line 25). -/
def WPc.ph13 : WPc G → Prop
  | .l13 _ | .l14 _ | .l16 _ | .l18 | .l20 _ | .l21 _ | .cs => True
  | _ => False

/-- The value of `RSIG` determined by the writer's position. -/
def rsigOf (w : WLocal G) : ℕ × ROp :=
  match w.pc with
  | .rem | .l8 _ | .l11 => (w.wseq, .nop)
  | .l13 _ | .l14 _ | .l16 _ | .l18 => (w.wseq, .preentry)
  | .l20 _ | .l21 _ | .cs => (w.wseq, .wait)
  | .l26 => (w.wseq - 1, .wait)

/-- Tags `WSIG[g]` may hold with the current sequence number, given the writer's position. -/
def allowed : WPc G → Fin G → WTag → Prop
  | .rem, _, t | .l8 _, _, t | .l11, _, t => t = .bot
  | .l13 i, g, t | .l14 i, g, t | .l16 i, g, t =>
      if g < i then t = .wait else t = .bot ∨ t = .proceed
  | .l18, _, t => t = .wait
  | .l20 _, _, t | .l21 _, _, t | .cs, _, t => t = .wait ∨ t = .cs
  | .l26, _, _ => False

/-- `pc` is inside `HelpWCS`. -/
def RPc.help : RPc → Bool
  | .l51a | .l51b | .l52 => true
  | _ => false

/-- The reader is counted by `C[g]` (lines 32–40). -/
def RLocal.inC (l : RLocal) : Bool :=
  match l.pc with
  | .l32 | .l34 | .l36 | .l37 | .cs => true
  | .l51a | .l51b | .l52 => l.ret36
  | _ => false

/-- The reader is counted by `W[g]` (lines 35–37). -/
def RLocal.inW (l : RLocal) : Bool :=
  match l.pc with
  | .l36 | .l37 => true
  | .l51a | .l51b | .l52 => l.ret36
  | _ => false

/-- The reader is *waiting* (Definition 4, lines 34–36) or about to leave the waiting loop
(line 37). -/
def RLocal.ew (l : RLocal) : Bool :=
  match l.pc with
  | .l34 | .l36 | .l37 => true
  | .l51a | .l51b | .l52 => l.ret36
  | _ => false

/-- Number of group-`g` readers satisfying `P`. -/
def cnt (grp : Fin n → Fin G) (P : RLocal → Bool) (r : Fin n → RLocal) (g : Fin G) : ℕ :=
  ∑ q, if grp q = g ∧ P (r q) = true then 1 else 0

/-- No group-`g` reader is in the critical section. -/
def Clear (grp : Fin n → Fin G) (r : Fin n → RLocal) (g : Fin G) : Prop :=
  ∀ q, grp q = g → (r q).pc ≠ .cs

/-- Constraint on a waiting reader of group `g` that read sequence number `seq` (Lemma 11). -/
def ewOK (w : WLocal G) (wsig : Fin G → ℕ × WTag) (g : Fin G) (seq : ℕ) : Prop :=
  match w.pc with
  | .l13 i => i ≤ g ∧ wsig g ≠ (w.wseq, .proceed)
  | .l14 i => i ≤ g ∧ wsig g ≠ (w.wseq, .proceed)
  | .l16 i => i < g ∧ wsig g ≠ (w.wseq, .proceed)
  | .l18 => False
  | .l20 _ | .l21 _ | .cs => seq = w.wseq
  | _ => True

/-! ### Counting lemmas -/

lemma cnt_update (grp : Fin n → Fin G) (P : RLocal → Bool) (r : Fin n → RLocal) (p : Fin n)
    (x : RLocal) (g : Fin G) :
    cnt grp P (Function.update r p x) g + (if grp p = g ∧ P (r p) = true then 1 else 0) =
      cnt grp P r g + (if grp p = g ∧ P x = true then 1 else 0) := by
  unfold cnt
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  have : ∀ q ∈ (univ : Finset (Fin n)).erase p,
      (if grp q = g ∧ P (Function.update r p x q) = true then 1 else 0) =
        (if grp q = g ∧ P (r q) = true then 1 else 0) := by
    intro q hq
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  rw [Finset.sum_congr rfl this]
  simp only [Function.update_self]
  omega

lemma cnt_update_same (grp : Fin n → Fin G) (P : RLocal → Bool) (r : Fin n → RLocal) (p : Fin n)
    (x : RLocal) (h : P x = P (r p)) (g : Fin G) :
    cnt grp P (Function.update r p x) g = cnt grp P r g := by
  have := cnt_update grp P r p x g
  rw [h] at this
  omega

lemma cnt_le_of_imp (grp : Fin n → Fin G) {P Q : RLocal → Bool} (r : Fin n → RLocal)
    (h : ∀ l, P l = true → Q l = true) (g : Fin G) : cnt grp P r g ≤ cnt grp Q r g := by
  unfold cnt
  apply Finset.sum_le_sum
  intro q _
  by_cases h1 : grp q = g ∧ P (r q) = true
  · simp [h1, h _ h1.2]
  · simp [h1]

lemma cnt_eq_imp (grp : Fin n → Fin G) {P Q : RLocal → Bool} (r : Fin n → RLocal)
    (h : ∀ l, P l = true → Q l = true) (g : Fin G) (he : cnt grp Q r g ≤ cnt grp P r g)
    (q : Fin n) (hq : grp q = g) (hQ : Q (r q) = true) : P (r q) = true := by
  unfold cnt at he
  have hle : ∀ q ∈ (univ : Finset (Fin n)),
      (if grp q = g ∧ P (r q) = true then 1 else 0) ≤
        (if grp q = g ∧ Q (r q) = true then 1 else 0) := by
    intro q _
    by_cases h1 : grp q = g ∧ P (r q) = true
    · simp [h1, h _ h1.2]
    · simp [h1]
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (le_antisymm (Finset.sum_le_sum hle) he) q
    (Finset.mem_univ q)
  by_contra hP
  simp [hq, hQ, hP] at heq

lemma cnt_eq_zero (grp : Fin n → Fin G) (P : RLocal → Bool) (r : Fin n → RLocal) (g : Fin G)
    (h : cnt grp P r g = 0) (q : Fin n) (hq : grp q = g) : P (r q) = false := by
  unfold cnt at h
  rw [Finset.sum_eq_zero_iff] at h
  have := h q (Finset.mem_univ q)
  by_contra hP
  simp [hq, hP] at this

lemma inW_imp_inC (l : RLocal) (h : l.inW = true) : l.inC = true := by
  unfold RLocal.inW at h; unfold RLocal.inC; split at h <;> simp_all

lemma ew_imp_inC (l : RLocal) (h : l.ew = true) : l.inC = true := by
  unfold RLocal.ew at h; unfold RLocal.inC; split at h <;> simp_all

/-! ### Loop indices -/

lemma firstIdx_some {j : Fin G} (h : firstIdx G = some j) : j.val = 0 := by
  unfold firstIdx at h; split at h <;> simp_all; rw [← h]

lemma firstIdx_none (h : firstIdx G = none) (g : Fin G) : False := by
  unfold firstIdx at h
  split at h
  · simp at h
  · exact absurd g.pos (by assumption)

lemma nextIdx_some {i j : Fin G} (h : nextIdx i = some j) : j.val = i.val + 1 := by
  unfold nextIdx at h; split at h <;> simp_all; rw [← h]

lemma nextIdx_none {i : Fin G} (h : nextIdx i = none) (g : Fin G) : g ≤ i := by
  unfold nextIdx at h; split at h <;> simp_all
  rw [Fin.le_def]; omega

/-! ### Frame lemmas -/

lemma wstep_r (s : State n G) : (wstep s).r = s.r := by
  unfold wstep; dsimp only; split <;> (try split) <;> rfl

lemma wstep_C (s : State n G) : (wstep s).C = s.C := by
  unfold wstep; dsimp only; split <;> (try split) <;> rfl

lemma wstep_W (s : State n G) : (wstep s).W = s.W := by
  unfold wstep; dsimp only; split <;> (try split) <;> rfl

lemma rstep_w (cfg : Cfg n G) (p : Fin n) (s : State n G) : (rstep cfg p s).w = s.w := by
  unfold rstep; dsimp only; split <;> (try split) <;> rfl

lemma rstep_rsig (cfg : Cfg n G) (p : Fin n) (s : State n G) :
    (rstep cfg p s).rsig = s.rsig := by
  unfold rstep; dsimp only; split <;> (try split) <;> rfl

/-! ### Layer A: bookkeeping -/

/-- Layer A of the invariant (bookkeeping). -/
structure InvA (cfg : Cfg n G) (s : State n G) : Prop where
  rsig : s.rsig = rsigOf s.w
  l26 : s.w.pc = .l26 → 0 < s.w.wseq
  cntC : ∀ g, s.C g = cnt cfg.grp RLocal.inC s.r g
  cntW : ∀ g, s.W g = cnt cfg.grp RLocal.inW s.r g
  wsig_le : ∀ g, (s.wsig g).1 ≤ s.w.wseq
  wsig_ok : ∀ g, (s.wsig g).1 = s.w.wseq → allowed s.w.pc g (s.wsig g).2
  seqA : ∀ p, (s.r p).ew = true →
    (s.r p).seq ≤ s.w.wseq ∧ ((s.r p).seq = s.w.wseq → s.w.pc.ph20)
  seqB : ∀ p, (s.r p).pc.help = true →
    (s.r p).hseq ≤ s.w.wseq ∧ ((s.r p).hseq = s.w.wseq → s.w.pc.ph20)
  seqC : ∀ p, ((s.r p).pc = .l43 ∨ (s.r p).pc = .l44) →
    (s.r p).seq' ≤ s.w.wseq ∧ ((s.r p).seq' = s.w.wseq → s.w.pc.ph13)
  r37 : ∀ p, (s.r p).pc = .l37 → s.rsig ≠ ((s.r p).seq, .wait)

lemma invA_init (cfg : Cfg n G) : InvA cfg init := by
  refine ⟨rfl, by simp [init], fun g => ?_, fun g => ?_, by simp [init], ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [init, cnt, RLocal.init, RLocal.inC, RLocal.inW, RLocal.ew, RPc.help, allowed]

set_option hygiene false in
/-- Split a writer step into its concrete cases, then run `tac` on each. -/
macro "wsplit" tac:tactic : tactic => `(tactic| (
  cases hpc : s.w.pc with
  | rem => (rcases hk : firstIdx G with _ | j <;> simp only [wstep, hpc, hk, loopTo]) <;>
      (try have hk1 := firstIdx_some hk) <;> (try have hk2 := firstIdx_none hk) <;> $tac
  | l8 i => (rcases hk : nextIdx i with _ | j <;> simp only [wstep, hpc, hk, loopTo]) <;> (try have hk1 := nextIdx_some hk) <;> (try have hk2 := nextIdx_none hk) <;> $tac
  | l11 => (rcases hk : firstIdx G with _ | j <;> simp only [wstep, hpc, hk, loopTo]) <;>
      (try have hk1 := firstIdx_some hk) <;> (try have hk2 := firstIdx_none hk) <;> $tac
  | l13 i => (by_cases hc : 0 < s.C i <;> simp only [wstep, hpc, hc, ↓reduceIte]) <;> $tac
  | l14 i => (by_cases hc : s.wsig i = (s.w.wseq, .proceed) <;>
      simp only [wstep, hpc, hc, ↓reduceIte]) <;> $tac
  | l16 i => (rcases hk : nextIdx i with _ | j <;> simp only [wstep, hpc, hk, loopTo]) <;> (try have hk1 := nextIdx_some hk) <;> (try have hk2 := nextIdx_none hk) <;> $tac
  | l18 => (rcases hk : firstIdx G with _ | j <;> simp only [wstep, hpc, hk, loopTo]) <;>
      (try have hk1 := firstIdx_some hk) <;> (try have hk2 := firstIdx_none hk) <;> $tac
  | l20 i => (by_cases hc : 0 < s.C i <;> rcases hk : nextIdx i with _ | j <;>
      simp only [wstep, hpc, hk, hc, loopTo, ↓reduceIte]) <;> (try have hk1 := nextIdx_some hk) <;> (try have hk2 := nextIdx_none hk) <;> $tac
  | l21 i => (by_cases hc : s.wsig i = (s.w.wseq, .cs) <;> rcases hk : nextIdx i with _ | j <;>
      simp only [wstep, hpc, hk, hc, loopTo, ↓reduceIte]) <;> (try have hk1 := nextIdx_some hk) <;> (try have hk2 := nextIdx_none hk) <;> $tac
  | cs => simp only [wstep, hpc] <;> $tac
  | l26 => simp only [wstep, hpc] <;> $tac))

lemma wstep_rsig (s : State n G) (h : s.rsig = rsigOf s.w) :
    (wstep s).rsig = rsigOf (wstep s).w := by
  wsplit (simp_all [rsigOf])

lemma wstep_l26 (s : State n G) (h : s.w.pc = .l26 → 0 < s.w.wseq) :
    (wstep s).w.pc = .l26 → 0 < (wstep s).w.wseq := by
  wsplit (try simp_all)

lemma wstep_wsig_le (s : State n G) (hle : ∀ g, (s.wsig g).1 ≤ s.w.wseq) :
    ∀ g, ((wstep s).wsig g).1 ≤ (wstep s).w.wseq := by
  wsplit (intro g; have := hle g; clear hle; (try simp only [Function.update_apply]); (try split_ifs) <;> simp_all <;> omega)

lemma wstep_wsig_ok (s : State n G) (hle : ∀ g, (s.wsig g).1 ≤ s.w.wseq)
    (hok : ∀ g, (s.wsig g).1 = s.w.wseq → allowed s.w.pc g (s.wsig g).2) :
    ∀ g, ((wstep s).wsig g).1 = (wstep s).w.wseq → allowed (wstep s).w.pc g ((wstep s).wsig g).2 := by
  wsplit (
    intro g hg
    have h1 := hok g
    have h2 := hle g
    try simp only [Function.update_apply] at *
    try have h3 := hk2 g
    (try split_ifs at hg ⊢) <;> (try split_ifs at h1) <;>
      (try simp_all [allowed]) <;>
      first
      | (rw [Fin.le_def]; omega)
      | (rw [Fin.lt_def]; omega)
      | (have h4 := hok g hg; simp only [lt_of_le_of_ne (hk2 g) ‹_›, ↓reduceIte] at h4; exact h4)
      | (have h4 := hok g hg
         have hne : g.val ≠ i.val := fun h => ‹¬g = i› (Fin.ext h)
         by_cases ha : g < i <;> by_cases hb : g < j <;>
           simp only [ha, hb, ↓reduceIte] at h4 ⊢ <;> (try exact h4) <;>
           (rw [Fin.lt_def] at ha hb; omega)))

lemma wstep_seqA (s : State n G) (hA : ∀ p, (s.r p).ew = true →
    (s.r p).seq ≤ s.w.wseq ∧ ((s.r p).seq = s.w.wseq → s.w.pc.ph20)) :
    ∀ p, ((wstep s).r p).ew = true →
      ((wstep s).r p).seq ≤ (wstep s).w.wseq ∧
        (((wstep s).r p).seq = (wstep s).w.wseq → (wstep s).w.pc.ph20) := by
  rw [wstep_r]
  wsplit (intro p hp; have h1 := hA p hp; clear hA; simp_all [WPc.ph20] <;> omega)

lemma wstep_seqB (s : State n G) (hB : ∀ p, (s.r p).pc.help = true →
    (s.r p).hseq ≤ s.w.wseq ∧ ((s.r p).hseq = s.w.wseq → s.w.pc.ph20)) :
    ∀ p, ((wstep s).r p).pc.help = true →
      ((wstep s).r p).hseq ≤ (wstep s).w.wseq ∧
        (((wstep s).r p).hseq = (wstep s).w.wseq → (wstep s).w.pc.ph20) := by
  rw [wstep_r]
  wsplit (intro p hp; have h1 := hB p hp; clear hB; simp_all [WPc.ph20] <;> omega)

lemma wstep_seqC (s : State n G) (hCc : ∀ p, ((s.r p).pc = .l43 ∨ (s.r p).pc = .l44) →
    (s.r p).seq' ≤ s.w.wseq ∧ ((s.r p).seq' = s.w.wseq → s.w.pc.ph13)) :
    ∀ p, (((wstep s).r p).pc = .l43 ∨ ((wstep s).r p).pc = .l44) →
      ((wstep s).r p).seq' ≤ (wstep s).w.wseq ∧
        (((wstep s).r p).seq' = (wstep s).w.wseq → (wstep s).w.pc.ph13) := by
  rw [wstep_r]
  wsplit (intro p hp; have h1 := hCc p hp; clear hCc; simp_all [WPc.ph13] <;> omega)

lemma wstep_r37 (s : State n G) (hA : ∀ p, (s.r p).ew = true →
    (s.r p).seq ≤ s.w.wseq ∧ ((s.r p).seq = s.w.wseq → s.w.pc.ph20))
    (h37 : ∀ p, (s.r p).pc = .l37 → s.rsig ≠ ((s.r p).seq, .wait)) :
    ∀ p, ((wstep s).r p).pc = .l37 → (wstep s).rsig ≠ (((wstep s).r p).seq, .wait) := by
  rw [wstep_r]
  wsplit (
    intro p hp
    have h1 := h37 p hp
    have h2 := hA p (by simp [RLocal.ew, hp])
    clear hA h37
    simp_all [WPc.ph20] <;> omega)

lemma invA_wstep (cfg : Cfg n G) (s : State n G) (h : InvA cfg s) : InvA cfg (wstep s) where
  rsig := wstep_rsig s h.rsig
  l26 := wstep_l26 s h.l26
  cntC := by rw [wstep_C, wstep_r]; exact h.cntC
  cntW := by rw [wstep_W, wstep_r]; exact h.cntW
  wsig_le := wstep_wsig_le s h.wsig_le
  wsig_ok := wstep_wsig_ok s h.wsig_le h.wsig_ok
  seqA := wstep_seqA s h.seqA
  seqB := wstep_seqB s h.seqB
  seqC := wstep_seqC s h.seqC
  r37 := wstep_r37 s h.seqA h.r37

/-! #### Reader steps -/

lemma rsigOf_wait (w : WLocal G) (h26 : w.pc = .l26 → 0 < w.wseq) (h : (rsigOf w).2 = .wait) :
    (rsigOf w).1 ≤ w.wseq ∧ ((rsigOf w).1 = w.wseq → w.pc.ph20) := by
  rcases w with ⟨pc, ws⟩
  cases pc <;> simp_all [rsigOf, WPc.ph20] <;> omega

lemma rsigOf_pre (w : WLocal G) (h : (rsigOf w).2 = .preentry) :
    (rsigOf w).1 = w.wseq ∧ w.pc.ph13 := by
  rcases w with ⟨pc, ws⟩
  cases pc <;> simp_all [rsigOf, WPc.ph13]

lemma rsigOf_ph20 (w : WLocal G) (h : w.pc.ph20) : rsigOf w = (w.wseq, .wait) := by
  rcases w with ⟨pc, ws⟩
  cases pc <;> simp_all [rsigOf, WPc.ph20]

lemma rsigOf_ph13 (w : WLocal G) (h : w.pc.ph13) (h' : ¬ w.pc.ph20) :
    rsigOf w = (w.wseq, .preentry) := by
  rcases w with ⟨pc, ws⟩
  cases pc <;> simp_all [rsigOf, WPc.ph20, WPc.ph13]

lemma allowed_cs (pc : WPc G) (g : Fin G) (h : pc.ph20) : allowed pc g .cs := by
  cases pc <;> simp_all [allowed, WPc.ph20]

lemma allowed_proceed (pc : WPc G) (g : Fin G) (h : allowed pc g .bot) (h' : pc.ph13) :
    allowed pc g .proceed := by
  cases pc <;> simp_all [allowed, WPc.ph13] <;> split_ifs at h ⊢ <;> simp_all

lemma cas_fst {α : Type} [DecidableEq α] {β : Type} [DecidableEq β] (x : α × β) (a b : β) :
    (cas x (x.1, a) (x.1, b)).1 = x.1 := by
  unfold cas; split_ifs <;> rfl

set_option hygiene false in
/-- Split a step of reader `p` into its concrete cases, then run `tac` on each. -/
macro "rsplit" tac:tactic : tactic => `(tactic| (
  cases hpc : (s.r p).pc with
  | rem => simp only [rstep, hpc] <;> $tac
  | l31 => simp only [rstep, hpc] <;> $tac
  | l32 => (by_cases hc : s.rsig.2 = .wait <;> simp only [rstep, hpc, hc, ↓reduceIte]) <;> $tac
  | l34 => simp only [rstep, hpc] <;> $tac
  | l51a => simp only [rstep, hpc] <;> $tac
  | l51b => (by_cases hc : cfg.order.second (s.C (cfg.grp p)) (s.W (cfg.grp p)) = (s.r p).tmp <;>
      by_cases hr : (s.r p).ret36 = true <;>
      simp only [rstep, hpc, hc, hr, ↓reduceIte, Bool.not_eq_true, Bool.false_eq_true]) <;> $tac
  | l52 => (by_cases hr : (s.r p).ret36 = true <;>
      simp only [rstep, hpc, hr, ↓reduceIte, Bool.not_eq_true, Bool.false_eq_true]) <;> $tac
  | l36 => (by_cases hc : s.rsig = ((s.r p).seq, .wait) <;>
      simp only [rstep, hpc, hc, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]) <;> $tac
  | l37 => simp only [rstep, hpc] <;> $tac
  | cs => simp only [rstep, hpc] <;> $tac
  | l41 => (by_cases hc : s.rsig.2 = .preentry <;>
      by_cases hh : cfg.l47.tested (s.r p).op s.rsig.2 = .wait <;>
      simp only [rstep, hpc, hc, hh, ↓reduceIte]) <;> $tac
  | l43 => (by_cases hc : s.C (cfg.grp p) = 0 <;> simp only [rstep, hpc, hc, ↓reduceIte]) <;> $tac
  | l44 => simp only [rstep, hpc] <;> $tac))

lemma cnt_pos (grp : Fin n → Fin G) (P : RLocal → Bool) (r : Fin n → RLocal) (p : Fin n)
    (hP : P (r p) = true) : 0 < cnt grp P r (grp p) := by
  unfold cnt
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨p, Finset.mem_univ _, by simp [hP]⟩

lemma cnt_step (grp : Fin n → Fin G) (P : RLocal → Bool) {C C' : Fin G → ℕ}
    {r : Fin n → RLocal} {p : Fin n} {l' : RLocal} (hC : ∀ g, C g = cnt grp P r g)
    (h : ∀ g, C' g + (if grp p = g ∧ P (r p) = true then 1 else 0) =
      C g + (if grp p = g ∧ P l' = true then 1 else 0)) :
    ∀ g, C' g = cnt grp P (Function.update r p l') g := by
  intro g
  have h1 := cnt_update grp P r p l' g
  have h2 := h g
  rw [hC g] at h2
  omega

lemma rstep_cntC (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (hC : ∀ g, s.C g = cnt cfg.grp RLocal.inC s.r g) :
    ∀ g, (rstep cfg p s).C g = cnt cfg.grp RLocal.inC (rstep cfg p s).r g := by
  have hpos := cnt_pos cfg.grp RLocal.inC s.r p
  rw [← hC] at hpos
  rsplit (first
    | exact hC
    | (apply cnt_step cfg.grp _ hC
       intro g
       by_cases hg : cfg.grp p = g
       · subst hg; simp_all [RLocal.inC, Function.update_apply]; try omega
       · simp [hg, Function.update_apply, Ne.symm hg]))

lemma rstep_cntW (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (hW : ∀ g, s.W g = cnt cfg.grp RLocal.inW s.r g) :
    ∀ g, (rstep cfg p s).W g = cnt cfg.grp RLocal.inW (rstep cfg p s).r g := by
  have hpos := cnt_pos cfg.grp RLocal.inW s.r p
  rw [← hW] at hpos
  rsplit (first
    | exact hW
    | (apply cnt_step cfg.grp _ hW
       intro g
       by_cases hg : cfg.grp p = g
       · subst hg; simp_all [RLocal.inW, Function.update_apply]; try omega
       · simp [hg, Function.update_apply, Ne.symm hg]))

lemma rstep_wsig_le (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (hle : ∀ g, (s.wsig g).1 ≤ s.w.wseq) :
    ∀ g, ((rstep cfg p s).wsig g).1 ≤ (rstep cfg p s).w.wseq := by
  rsplit (
    intro g
    have h1 := hle g
    try simp only [Function.update_apply]
    try split_ifs
    all_goals (try subst_vars) <;> (try simp only [cas]) <;> (try split_ifs) <;> simp_all)

lemma rstep_wsig_ok (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (hok : ∀ g, (s.wsig g).1 = s.w.wseq → allowed s.w.pc g (s.wsig g).2)
    (hB : ∀ p, (s.r p).pc.help = true →
      (s.r p).hseq ≤ s.w.wseq ∧ ((s.r p).hseq = s.w.wseq → s.w.pc.ph20))
    (hCc : ∀ p, ((s.r p).pc = .l43 ∨ (s.r p).pc = .l44) →
      (s.r p).seq' ≤ s.w.wseq ∧ ((s.r p).seq' = s.w.wseq → s.w.pc.ph13)) :
    ∀ g, ((rstep cfg p s).wsig g).1 = (rstep cfg p s).w.wseq →
      allowed (rstep cfg p s).w.pc g ((rstep cfg p s).wsig g).2 := by
  rsplit (
    intro g hg
    have h1 := hok g
    try simp only [Function.update_apply] at hg ⊢
    try split_ifs at hg ⊢
    all_goals (try exact h1 hg)
    all_goals (
      subst_vars
      unfold cas at hg ⊢
      split_ifs at hg ⊢ with hx
      · rw [hx] at h1
        simp only at hg h1 ⊢
        first
        | exact allowed_cs _ _ ((hB p (by simp [hpc, RPc.help])).2 hg)
        | exact allowed_proceed _ _ (h1 hg) ((hCc p (by simp [hpc])).2 hg)
      · exact h1 hg))

lemma rstep_seqA (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (hrs : s.rsig = rsigOf s.w) (h26 : s.w.pc = .l26 → 0 < s.w.wseq)
    (hA : ∀ p, (s.r p).ew = true →
      (s.r p).seq ≤ s.w.wseq ∧ ((s.r p).seq = s.w.wseq → s.w.pc.ph20)) :
    ∀ q, ((rstep cfg p s).r q).ew = true →
      ((rstep cfg p s).r q).seq ≤ (rstep cfg p s).w.wseq ∧
        (((rstep cfg p s).r q).seq = (rstep cfg p s).w.wseq → (rstep cfg p s).w.pc.ph20) := by
  rsplit (
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      try simp only [Function.update_self] at hq ⊢
      first
      | exact hA q hq
      | exact hA q (by simp_all [RLocal.ew])
      | (rw [hrs] at hc ⊢; exact rsigOf_wait _ h26 hc)
      | simp_all [RLocal.ew]
    · try rw [Function.update_of_ne hqp] at hq ⊢
      exact hA q hq)

lemma rstep_seqB (cfg : Cfg n G) (hcfg : cfg.l47 = .op') (s : State n G) (p : Fin n)
    (hrs : s.rsig = rsigOf s.w) (h26 : s.w.pc = .l26 → 0 < s.w.wseq)
    (hA : ∀ p, (s.r p).ew = true →
      (s.r p).seq ≤ s.w.wseq ∧ ((s.r p).seq = s.w.wseq → s.w.pc.ph20))
    (hB : ∀ p, (s.r p).pc.help = true →
      (s.r p).hseq ≤ s.w.wseq ∧ ((s.r p).hseq = s.w.wseq → s.w.pc.ph20)) :
    ∀ q, ((rstep cfg p s).r q).pc.help = true →
      ((rstep cfg p s).r q).hseq ≤ (rstep cfg p s).w.wseq ∧
        (((rstep cfg p s).r q).hseq = (rstep cfg p s).w.wseq → (rstep cfg p s).w.pc.ph20) := by
  rsplit (
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      try simp only [Function.update_self] at hq ⊢
      first
      | exact hB q hq
      | exact hB q (by simp_all [RPc.help])
      | exact hA q (by simp_all [RLocal.ew])
      | (rw [hcfg] at hh; simp only [Line47.tested] at hh; rw [hrs] at hh ⊢
         exact rsigOf_wait _ h26 hh)
      | simp_all [RPc.help]
    · try rw [Function.update_of_ne hqp] at hq ⊢
      exact hB q hq)

lemma rstep_seqC (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (hrs : s.rsig = rsigOf s.w)
    (hCc : ∀ p, ((s.r p).pc = .l43 ∨ (s.r p).pc = .l44) →
      (s.r p).seq' ≤ s.w.wseq ∧ ((s.r p).seq' = s.w.wseq → s.w.pc.ph13)) :
    ∀ q, (((rstep cfg p s).r q).pc = .l43 ∨ ((rstep cfg p s).r q).pc = .l44) →
      ((rstep cfg p s).r q).seq' ≤ (rstep cfg p s).w.wseq ∧
        (((rstep cfg p s).r q).seq' = (rstep cfg p s).w.wseq → (rstep cfg p s).w.pc.ph13) := by
  rsplit (
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      try simp only [Function.update_self] at hq ⊢
      first
      | exact hCc q hq
      | exact hCc q (by simp_all)
      | (rw [hrs] at hc ⊢
         have := rsigOf_pre _ hc
         exact ⟨this.1.le, fun _ => this.2⟩)
      | simp_all
    · try rw [Function.update_of_ne hqp] at hq ⊢
      exact hCc q hq)

lemma rstep_r37 (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (h37 : ∀ p, (s.r p).pc = .l37 → s.rsig ≠ ((s.r p).seq, .wait)) :
    ∀ q, ((rstep cfg p s).r q).pc = .l37 →
      (rstep cfg p s).rsig ≠ (((rstep cfg p s).r q).seq, .wait) := by
  rsplit (
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      try simp only [Function.update_self] at hq ⊢
      first
      | exact h37 q hq
      | exact hc
      | simp_all
    · try rw [Function.update_of_ne hqp] at hq ⊢
      first
      | exact h37 q hq
      | (rw [← hc]; exact h37 q hq))

lemma invA_rstep (cfg : Cfg n G) (hcfg : cfg.l47 = .op') (s : State n G) (p : Fin n)
    (h : InvA cfg s) : InvA cfg (rstep cfg p s) where
  rsig := by rw [rstep_rsig, rstep_w]; exact h.rsig
  l26 := by rw [rstep_w]; exact h.l26
  cntC := rstep_cntC cfg s p h.cntC
  cntW := rstep_cntW cfg s p h.cntW
  wsig_le := rstep_wsig_le cfg s p h.wsig_le
  wsig_ok := rstep_wsig_ok cfg s p h.wsig_ok h.seqB h.seqC
  seqA := rstep_seqA cfg s p h.rsig h.l26 h.seqA
  seqB := rstep_seqB cfg hcfg s p h.rsig h.l26 h.seqA h.seqB
  seqC := rstep_seqC cfg s p h.rsig h.seqC
  r37 := rstep_r37 cfg s p h.r37

lemma invA_step (cfg : Cfg n G) (hcfg : cfg.l47 = .op') (s : State n G) (who : Who n)
    (h : InvA cfg s) : InvA cfg (step cfg who s) := by
  cases who with
  | writer => exact invA_wstep cfg s h
  | reader p => exact invA_rstep cfg hcfg s p h

/-! ### Layer B: Lemma 11 -/

/-- Layer B of the invariant (Lemma 11 of the paper and its supporting facts). -/
structure InvB (cfg : Cfg n G) (s : State n G) : Prop where
  ew : ∀ p, (s.r p).ew = true → ewOK s.w s.wsig (cfg.grp p) (s.r p).seq
  r44 : ∀ p, (s.r p).pc = .l44 → (s.r p).seq' = s.w.wseq →
    s.wsig (cfg.grp p) = (s.w.wseq, .bot) → ∀ q, cfg.grp q = cfg.grp p → (s.r q).ew = false

lemma invB_init (cfg : Cfg n G) : InvB cfg init := by
  constructor <;> simp [init, RLocal.init, RLocal.ew]

lemma ew_pos (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s) (p : Fin n)
    (hp : (s.r p).ew = true) : 0 < s.C (cfg.grp p) := by
  rw [hA.cntC]; exact cnt_pos _ _ _ _ (ew_imp_inC _ hp)

lemma wstep_ew (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s)
    (hew : ∀ p, (s.r p).ew = true → ewOK s.w s.wsig (cfg.grp p) (s.r p).seq) :
    ∀ p, ((wstep s).r p).ew = true →
      ewOK (wstep s).w (wstep s).wsig (cfg.grp p) ((wstep s).r p).seq := by
  rw [wstep_r]
  have hpos := ew_pos cfg s hA
  have hok := hA.wsig_ok
  wsplit (
    intro p hp
    have h1 := hew p hp
    have h2 := hpos p hp
    (try simp only [ewOK, hpc, Function.update_apply] at h1 ⊢) <;>
    first
    | exact h1
    | trivial
    | exact (hk2 (cfg.grp p)).elim
    | exact absurd (lt_of_lt_of_le h1.1 (hk2 (cfg.grp p))) (lt_irrefl _)
    | exact ⟨by rw [Fin.le_def]; omega, fun h => by
        have := hok _ (by rw [h])
        simp [hpc, allowed, h] at this⟩
    | exact ⟨lt_of_le_of_ne h1.1 (fun h => hc (h ▸ h2)), h1.2⟩
    | exact ⟨lt_of_le_of_ne h1.1 (fun h => h1.2 (h ▸ hc)), h1.2⟩
    | (refine ⟨?_, ?_⟩
       · have := h1.1; rw [Fin.lt_def] at this; rw [Fin.le_def]; omega
       · simp only [ne_of_gt h1.1, ↓reduceIte]; exact h1.2))

lemma wstep_r44 (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s)
    (hr44 : ∀ p, (s.r p).pc = .l44 → (s.r p).seq' = s.w.wseq →
      s.wsig (cfg.grp p) = (s.w.wseq, .bot) → ∀ q, cfg.grp q = cfg.grp p → (s.r q).ew = false) :
    ∀ p, ((wstep s).r p).pc = .l44 → ((wstep s).r p).seq' = (wstep s).w.wseq →
      (wstep s).wsig (cfg.grp p) = ((wstep s).w.wseq, .bot) →
        ∀ q, cfg.grp q = cfg.grp p → ((wstep s).r q).ew = false := by
  rw [wstep_r]
  have hCc := hA.seqC
  wsplit (
    intro p hp hs hw q hq
    have hC := hCc p (Or.inr hp)
    have h1 := hr44 p hp
    (try simp only [Function.update_apply] at hw)
    (try split_ifs at hw)
    all_goals first
      | exact h1 hs hw q hq
      | (simp only [hpc, WPc.ph13] at hC; exact absurd (hC.2 hs) id)
      | simp_all
      | omega)

lemma invB_wstep (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s) (hB : InvB cfg s) :
    InvB cfg (wstep s) :=
  ⟨wstep_ew cfg s hA hB.ew, wstep_r44 cfg s hA hB.r44⟩

lemma ewOK_upd (w : WLocal G) (wsig wsig' : Fin G → ℕ × WTag) (g : Fin G) (seq : ℕ)
    (h : ewOK w wsig g seq) (h' : wsig' g = (w.wseq, .proceed) → wsig g = (w.wseq, .proceed)) :
    ewOK w wsig' g seq := by
  rcases w with ⟨pc, ws⟩
  cases pc <;> simp_all [ewOK] <;> exact fun h2 => h.2 (h' h2)

lemma ewOK_of_wait (w : WLocal G) (wsig : Fin G → ℕ × WTag) (g : Fin G)
    (h : (rsigOf w).2 = .wait) : ewOK w wsig g (rsigOf w).1 := by
  rcases w with ⟨pc, ws⟩
  cases pc <;> simp_all [ewOK, rsigOf]

lemma rstep_ew (cfg : Cfg n G) (s : State n G) (p : Fin n) (hA : InvA cfg s)
    (hew : ∀ p, (s.r p).ew = true → ewOK s.w s.wsig (cfg.grp p) (s.r p).seq)
    (hr44 : ∀ p, (s.r p).pc = .l44 → (s.r p).seq' = s.w.wseq →
      s.wsig (cfg.grp p) = (s.w.wseq, .bot) → ∀ q, cfg.grp q = cfg.grp p → (s.r q).ew = false) :
    ∀ q, ((rstep cfg p s).r q).ew = true →
      ewOK (rstep cfg p s).w (rstep cfg p s).wsig (cfg.grp q) ((rstep cfg p s).r q).seq := by
  have hrs := hA.rsig
  rsplit (
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      try simp only [Function.update_self] at hq ⊢
      first
      | exact hew q hq
      | (rw [hrs] at hc ⊢; exact ewOK_of_wait _ _ _ hc)
      | exact hew q (by simp_all [RLocal.ew])
      | (simp_all [RLocal.ew]; done)
      | (apply ewOK_upd _ _ _ _ _ (hew q (by simp_all [RLocal.ew]))
         intro h
         simp only [Function.update_apply, cas] at h ⊢
         split_ifs at h ⊢ <;> simp_all; done)
    · try rw [Function.update_of_ne hqp] at hq ⊢
      first
      | exact hew q hq
      | (apply ewOK_upd _ _ _ _ _ (hew q hq)
         intro h
         simp only [Function.update_apply, cas] at h ⊢
         split_ifs at h ⊢ with h3 h4
         · simp only [Prod.mk.injEq] at h
           first
           | exact absurd h.2 (by decide)
           | (have := hr44 p hpc h.1 (by rw [h4, h.1]) q h3; simp_all)
         all_goals simp_all))

lemma ew_false_of_C_zero (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s) (g : Fin G)
    (h : s.C g = 0) (q : Fin n) (hq : cfg.grp q = g) : (s.r q).ew = false := by
  have h1 := cnt_eq_zero _ _ _ _ (hA.cntC g ▸ h) q hq
  cases he : (s.r q).ew
  · rfl
  · have := ew_imp_inC _ he; simp_all

lemma no_wait_of_r44 (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s) (q0 : Fin n)
    (hq0 : (s.r q0).pc = .l44) (hs : (s.r q0).seq' = s.w.wseq)
    (hw : s.wsig (cfg.grp q0) = (s.w.wseq, .bot)) : s.rsig.2 ≠ .wait := by
  have h13 := (hA.seqC q0 (Or.inr hq0)).2 hs
  have hok := hA.wsig_ok (cfg.grp q0) (by rw [hw])
  rw [hw] at hok
  rw [hA.rsig]
  rcases hw' : s.w with ⟨pc, ws⟩
  rw [hw'] at h13 hok
  cases pc <;> simp_all [rsigOf, WPc.ph13, allowed]

lemma rstep_r44 (cfg : Cfg n G) (s : State n G) (p : Fin n) (hA : InvA cfg s)
    (hr44 : ∀ p, (s.r p).pc = .l44 → (s.r p).seq' = s.w.wseq →
      s.wsig (cfg.grp p) = (s.w.wseq, .bot) → ∀ q, cfg.grp q = cfg.grp p → (s.r q).ew = false) :
    ∀ q0, ((rstep cfg p s).r q0).pc = .l44 → ((rstep cfg p s).r q0).seq' = (rstep cfg p s).w.wseq →
      (rstep cfg p s).wsig (cfg.grp q0) = ((rstep cfg p s).w.wseq, .bot) →
        ∀ q, cfg.grp q = cfg.grp q0 → ((rstep cfg p s).r q).ew = false := by
  have hC0 := ew_false_of_C_zero cfg s hA
  have hnw := no_wait_of_r44 cfg s hA
  rsplit (
    intro q0 hq0 hs hw q hq
    by_cases h0 : q0 = p
    · subst h0
      try simp only [Function.update_self] at hq0 hs
      first
      | exact hr44 q0 hq0 hs hw q hq
      | (by_cases hqq : q = q0
         · subst hqq; simp [Function.update_self, RLocal.ew]
         · rw [Function.update_of_ne hqq]; exact hC0 _ hc q hq)
      | (simp_all; done)
    · try rw [Function.update_of_ne h0] at hq0 hs
      have hw' : s.wsig (cfg.grp q0) = (s.w.wseq, .bot) := by
        first
        | exact hw
        | (simp only [Function.update_apply, cas] at hw; split_ifs at hw <;> simp_all)
      have hold := hr44 q0 hq0 hs hw'
      by_cases hqp : q = p
      · subst hqp
        try simp only [Function.update_self]
        first
        | exact hold q hq
        | (simp only [RLocal.ew]; done)
        | exact absurd hc (hnw q0 hq0 hs hw')
        | (have := hold q hq; simp_all [RLocal.ew]; done)
      · try rw [Function.update_of_ne hqp]
        exact hold q hq)

lemma invB_rstep (cfg : Cfg n G) (s : State n G) (p : Fin n) (hA : InvA cfg s) (hB : InvB cfg s) :
    InvB cfg (rstep cfg p s) :=
  ⟨rstep_ew cfg s p hA hB.ew hB.r44, rstep_r44 cfg s p hA hB.r44⟩

lemma invB_step (cfg : Cfg n G) (s : State n G) (who : Who n) (hA : InvA cfg s)
    (hB : InvB cfg s) : InvB cfg (step cfg who s) := by
  cases who with
  | writer => exact invB_wstep cfg s hA hB
  | reader p => exact invB_rstep cfg s p hA hB

/-! ### Layer C: Lemma 8 -/

/-- Layer C of the invariant (Lemma 8 of the paper). -/
structure InvC (cfg : Cfg n G) (s : State n G) : Prop where
  sigcs : s.w.pc.ph20 → ∀ g, s.wsig g = (s.w.wseq, .cs) → Clear cfg.grp s.r g
  loop : ∀ i g, (s.w.pc = .l20 i ∨ s.w.pc = .l21 i) → g < i → Clear cfg.grp s.r g
  csAll : s.w.pc = .cs → ∀ g, Clear cfg.grp s.r g
  r52 : ∀ p, (s.r p).pc = .l52 → (s.r p).hseq = s.w.wseq → s.w.pc.ph20 →
    Clear cfg.grp s.r (cfg.grp p)
  r51b : ∀ p, (s.r p).pc = .l51b → (s.r p).hseq = s.w.wseq → s.w.pc.ph20 →
    (s.r p).tmp ≤ s.W (cfg.grp p)

lemma invC_init (cfg : Cfg n G) : InvC cfg init := by
  constructor <;> simp [init, WPc.ph20, RLocal.init]

/-- While the writer is in lines 19–24, no reader is at line 37. -/
lemma no_l37_ph20 (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s) (hB : InvB cfg s)
    (h20 : s.w.pc.ph20) (q : Fin n) : (s.r q).pc ≠ .l37 := by
  intro hq
  have h1 := hA.r37 q hq
  have h2 := hB.ew q (by simp [RLocal.ew, hq])
  rw [hA.rsig, rsigOf_ph20 _ h20] at h1
  rcases hw : s.w with ⟨pc, ws⟩
  rw [hw] at h20 h1 h2
  cases pc <;> simp_all [ewOK, WPc.ph20]

/-- While the writer is in lines 19–24, no reader enters the CS. -/
lemma rstep_cs_ph20 (cfg : Cfg n G) (s : State n G) (p : Fin n) (hA : InvA cfg s)
    (hB : InvB cfg s) (h20 : s.w.pc.ph20) :
    ∀ q, ((rstep cfg p s).r q).pc = .cs → (s.r q).pc = .cs := by
  have h37 := no_l37_ph20 cfg s hA hB h20
  have hrs : s.rsig = (s.w.wseq, .wait) := by rw [hA.rsig, rsigOf_ph20 _ h20]
  rsplit (
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      try simp only [Function.update_self] at hq
      first
      | exact hq
      | (simp_all; done)
      | exact absurd hpc (h37 q)
    · try rw [Function.update_of_ne hqp] at hq
      exact hq)

lemma clear_rstep_ph20 (cfg : Cfg n G) (s : State n G) (p : Fin n) (hA : InvA cfg s)
    (hB : InvB cfg s) (h20 : s.w.pc.ph20) (g : Fin G) (h : Clear cfg.grp s.r g) :
    Clear cfg.grp (rstep cfg p s).r g :=
  fun q hq hcs => h q hq (rstep_cs_ph20 cfg s p hA hB h20 q hcs)

/-- While the writer is in lines 19–24, `W[g]` does not decrease. -/
lemma rstep_W_ph20 (cfg : Cfg n G) (s : State n G) (p : Fin n) (hA : InvA cfg s)
    (hB : InvB cfg s) (h20 : s.w.pc.ph20) (g : Fin G) : s.W g ≤ (rstep cfg p s).W g := by
  have h37 := no_l37_ph20 cfg s hA hB h20 p
  rsplit (first
    | exact le_rfl
    | exact absurd hpc h37
    | (simp only [Function.update_apply]; split_ifs <;> simp_all))

lemma clear_of_C_zero (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s) (g : Fin G)
    (h : s.C g = 0) : Clear cfg.grp s.r g := by
  intro q hq hcs
  have := cnt_eq_zero _ _ _ _ (hA.cntC g ▸ h) q hq
  simp [RLocal.inC, hcs] at this

lemma clear_of_C_le_W (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s) (g : Fin G)
    (h : s.C g ≤ s.W g) : Clear cfg.grp s.r g := by
  intro q hq hcs
  rw [hA.cntC, hA.cntW] at h
  have := cnt_eq_imp cfg.grp s.r inW_imp_inC g h q hq (by simp [RLocal.inC, hcs])
  simp [RLocal.inW, hcs] at this

lemma invC_wstep (cfg : Cfg n G) (s : State n G) (hA : InvA cfg s) (hC : InvC cfg s) :
    InvC cfg (wstep s) := by
  have hok := hA.wsig_ok
  have hz := clear_of_C_zero cfg s hA
  have hsB := hA.seqB
  have hsig := hC.sigcs
  have hloop := hC.loop
  have h52 := hC.r52
  have h51 := hC.r51b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [wstep_r]
    wsplit (
      intro h20 g hg
      first
      | (simp [WPc.ph20] at h20; done)
      | (refine hsig ?_ g hg; simp [hpc, WPc.ph20]; done)
      | (have := hok g (by rw [hg]); simp [hpc, hg, allowed] at this; done))
  · rw [wstep_r]
    wsplit (
      intro i' g hi hgi
      (rcases hi with hi | hi) <;>
        (try simp only [WPc.l20.injEq, WPc.l21.injEq, reduceCtorEq] at hi) <;>
        (try subst hi) <;>
      first
      | (simp at hi; done)
      | (refine hloop _ g ?_ hgi; simp [hpc]; done)
      | (rw [Fin.lt_def, hk1] at hgi; omega)
      | (by_cases hgi' : g < i
         · refine hloop i g ?_ hgi'; simp [hpc]
         · have : g = i := Fin.ext (by
             have := nextIdx_some hk; rw [Fin.lt_def] at hgi hgi'; omega)
           subst this
           first | (refine hz _ ?_; omega) | (refine hsig ?_ _ hc; simp [hpc, WPc.ph20]; done)))
  · rw [wstep_r]
    wsplit (
      intro hcs g
      first
      | (simp at hcs; done)
      | exact (hk2 g).elim
      | (by_cases hgi' : g < i
         · refine hloop i g ?_ hgi'; simp [hpc]
         · have : g = i := le_antisymm (hk2 g) (not_lt.1 hgi')
           subst this
           first | (refine hz _ ?_; omega) | (refine hsig ?_ _ hc; simp [hpc, WPc.ph20]; done)))
  · rw [wstep_r]
    wsplit (
      intro p hp hs h20
      first
      | (simp [WPc.ph20] at h20; done)
      | (refine h52 p hp hs ?_; simp [hpc, WPc.ph20]; done)
      | (have := (hsB p (by simp [hp, RPc.help])).2 hs; simp [hpc, WPc.ph20] at this; done))
  · rw [wstep_r, wstep_W]
    wsplit (
      intro p hp hs h20
      first
      | (simp [WPc.ph20] at h20; done)
      | (refine h51 p hp hs ?_; simp [hpc, WPc.ph20]; done)
      | (have := (hsB p (by simp [hp, RPc.help])).2 hs; simp [hpc, WPc.ph20] at this; done))

lemma rstep_wsig_cs (cfg : Cfg n G) (s : State n G) (p : Fin n) (g : Fin G) (x : ℕ)
    (h : (rstep cfg p s).wsig g = (x, .cs)) (h' : s.wsig g ≠ (x, .cs)) :
    (s.r p).pc = .l52 ∧ (s.r p).hseq = x ∧ cfg.grp p = g := by
  revert h h'
  rsplit (
    intro h h'
    first
    | exact absurd h h'
    | (simp only [Function.update_apply, cas] at h
       split_ifs at h with h1 h2 <;> simp_all))

lemma rstep_to_l52 (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (h : ((rstep cfg p s).r p).pc = .l52) :
    (s.r p).pc = .l51b ∧ cfg.order.second (s.C (cfg.grp p)) (s.W (cfg.grp p)) = (s.r p).tmp ∧
      ((rstep cfg p s).r p).hseq = (s.r p).hseq := by
  revert h
  rsplit (intro h; simp_all)

lemma rstep_to_l51b (cfg : Cfg n G) (s : State n G) (p : Fin n)
    (h : ((rstep cfg p s).r p).pc = .l51b) :
    (s.r p).pc = .l51a ∧ ((rstep cfg p s).r p).tmp = cfg.order.first (s.C (cfg.grp p)) (s.W (cfg.grp p)) ∧
      ((rstep cfg p s).r p).hseq = (s.r p).hseq ∧ (rstep cfg p s).W = s.W := by
  revert h
  rsplit (intro h; simp_all)

lemma rstep_r_ne (cfg : Cfg n G) (s : State n G) (p q : Fin n) (h : q ≠ p) :
    (rstep cfg p s).r q = s.r q := by
  rsplit (first | rfl | exact Function.update_of_ne h _ _)

lemma invC_rstep (cfg : Cfg n G) (hcfg : cfg.order = .wc) (s : State n G) (p : Fin n)
    (hA : InvA cfg s) (hB : InvB cfg s) (hC : InvC cfg s) : InvC cfg (rstep cfg p s) := by
  have hcl := clear_rstep_ph20 cfg s p hA hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h20 g hg
    rw [rstep_w] at h20 hg
    apply hcl h20
    by_cases hold : s.wsig g = (s.w.wseq, .cs)
    · exact hC.sigcs h20 g hold
    · obtain ⟨h1, h2, h3⟩ := rstep_wsig_cs cfg s p g _ hg hold
      rw [← h3]
      exact hC.r52 p h1 h2 h20
  · intro i g hi hgi
    rw [rstep_w] at hi
    have h20 : s.w.pc.ph20 := by rcases hi with hi | hi <;> simp [hi, WPc.ph20]
    exact hcl h20 g (hC.loop i g hi hgi)
  · intro hcs g
    rw [rstep_w] at hcs
    have h20 : s.w.pc.ph20 := by simp [hcs, WPc.ph20]
    exact hcl h20 g (hC.csAll hcs g)
  · intro q hq hs h20
    rw [rstep_w] at hs h20
    apply hcl h20
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨h1, h2, h3⟩ := rstep_to_l52 cfg s q hq
      rw [h3] at hs
      have h4 := hC.r51b q h1 hs h20
      rw [hcfg] at h2
      simp only [ReadOrder.second] at h2
      exact clear_of_C_le_W cfg s hA _ (h2 ▸ h4)
    · rw [rstep_r_ne cfg s p q hqp] at hq hs
      exact hC.r52 q hq hs h20
  · intro q hq hs h20
    rw [rstep_w] at hs h20
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨_, h2, _, h4⟩ := rstep_to_l51b cfg s q hq
      rw [h2, h4, hcfg]
      exact le_rfl
    · rw [rstep_r_ne cfg s p q hqp] at hq hs ⊢
      exact (hC.r51b q hq hs h20).trans (rstep_W_ph20 cfg s p hA hB h20 _)

/-! ### Main results -/

/-- The full inductive invariant. -/
def Inv (cfg : Cfg n G) (s : State n G) : Prop := InvA cfg s ∧ InvB cfg s ∧ InvC cfg s

/-- The invariant holds in every reachable configuration of the repaired algorithm. -/
theorem inv_reachable (cfg : Cfg n G) (h1 : cfg.order = .wc) (h2 : cfg.l47 = .op')
    (s : State n G) (hs : Reachable cfg s) : Inv cfg s := by
  induction hs with
  | init => exact ⟨invA_init cfg, invB_init cfg, invC_init cfg⟩
  | step who _ ih =>
    obtain ⟨hA, hB, hC⟩ := ih
    refine ⟨invA_step cfg h2 _ who hA, invB_step cfg _ who hA hB, ?_⟩
    cases who with
    | writer => exact invC_wstep cfg _ hA hC
    | reader p => exact invC_rstep cfg h1 _ p hA hB hC

/-- **Lemma 8 / Lemma 9 of the paper (Mutual Exclusion), for the repaired algorithm.** If in
line 51 `W[i]` is read before `C[i]` and line 47 tests `op'`, then for any number `n` of readers,
any static partition `grp` of the readers into `G` groups and a single writer, no reachable
configuration has the writer and a reader in the critical section at the same time. -/
theorem mutualExclusion_repaired (grp : Fin n → Fin G) :
    MutualExclusion (⟨.wc, .op', grp⟩ : Cfg n G) := by
  intro s hs hw p hp
  exact (inv_reachable _ rfl rfl s hs).2.2.csAll hw (grp p) p rfl hp

/-- **Lemma 11 of the paper, for the repaired algorithm.** When the writer is about to execute
line 18, no reader is waiting (lines 34–36, including `HelpWCS` called from line 35) or about to
leave the waiting loop (line 37). -/
theorem lemma11_repaired (grp : Fin n → Fin G) (s : State n G)
    (hs : Reachable (⟨.wc, .op', grp⟩ : Cfg n G) s) (hw : s.w.pc = .l18) (p : Fin n) :
    (s.r p).ew = false := by
  have hB := (inv_reachable _ rfl rfl s hs).2.1
  cases he : (s.r p).ew
  · rfl
  · have := hB.ew p he
    simp [ewOK, hw] at this

end Podc.RWLockRMRTradeoff.Alg
