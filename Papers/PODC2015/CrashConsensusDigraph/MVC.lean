import Papers.PODC2015.CrashConsensusDigraph.MinMax

/-!
# Algorithm MVC (multi-valued consensus): Theorem 4

Algorithm MVC of Section 2.3 for inputs in `[0, K]`. Every node keeps a tentative value `tᵢ`
(initially its input) and a bit `vᵢ`. OUTER-LOOP `l = 0, …, K`:
* STEP I: `vᵢ := 0` if `tᵢ = l`, else `vᵢ := 1`;
* STEP II (INNER-LOOP = Min-Max with `2f + 2` phases of `D` rounds): broadcast `(vᵢ, tᵢ)`; with
  `Bᵢ` the received tuples (including one's own), set `vᵢ` to the max (odd phases) or min (even
  phases) of the first components, and if some received second component exceeds `l`, set `tᵢ`
  to the least such component;
* STEP III: if `vᵢ = 0`, exit the OUTER-LOOP and output `l`.
If the loop is never exited, output `K`.

Encoding (`mvc f D K`): rounds are grouped into blocks of `blk f D = (2f + 2)·D + 1` rounds.
Round `blk·l` is a *local* round (messages ignored): it performs STEP III of iteration `l − 1`
(for `l ≥ 1`; at `l = K + 1` the output `K` after the loop) and STEP I of iteration `l`. Rounds
`blk·l + 1 + j`, `j < (2f + 2)·D`, are the INNER-LOOP rounds of iteration `l`. `false` encodes
`vᵢ = 0`. The first output is the decision; afterwards a node keeps running, which is harmless.

**Theorem 4** (`theorem4`): MVC solves crash consensus for inputs in `[0, K]` in every graph with
`f` CT node connectivity (and every `D` bounding the fault-tolerant diameter).

The proof follows Appendix A: Claim 2 (all non-crashed nodes have the same `v` at the end of each
INNER-LOOP) is `minmax_core`; Lemma 3 (`vᵢ = 1 ⇒ tᵢ > l` during iteration `l`) is
`inv_iteration`; Claim 5 (`tᵢ` is always an input) is `t_input`; Claim 6 (exit at `l` ⇒ some node
had `tⱼ = l` at the start of the iteration) is the first case of the validity proof. The paper's
Lemma 4 case "no node exits the OUTER-LOOP" (output `K`) is shown to be impossible: by Lemma 3,
all non-crashed nodes would have `tᵢ > K`, but `tᵢ` is an input `≤ K`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open AsyncApproxBCDirected

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V}

/-- State of Algorithm MVC: round counter, tentative value `t`, bit `v` (`false` = 0), decision. -/
structure MState where
  r : ℕ
  t : ℕ
  v : Bool
  dec : Option ℕ

/-- Block length: one local round plus the `(2f + 2)·D` INNER-LOOP rounds. -/
def blk (f D : ℕ) : ℕ := (2 * f + 2) * D + 1

theorem blk_pos (f D : ℕ) : 0 < blk f D := Nat.succ_pos _

/-- The decision taken in the local round of block `l`: STEP III of iteration `l − 1` (exit with
output `l − 1` if `v = 0`), or the output `K` after OUTER-LOOP iteration `K`. -/
def decAt (K l : ℕ) (v : Bool) : Option ℕ :=
  if 1 ≤ l ∧ v = false then some (l - 1) else if l = K + 1 then some K else none

/-- The local round of block `l`: STEP III of iteration `l − 1`, then STEP I of iteration `l`. -/
def mvcLocal (K l : ℕ) (s : MState) : MState where
  r := s.r + 1
  t := s.t
  v := !decide (s.t = l)
  dec := s.dec.or (decAt K l s.v)

/-- One INNER-LOOP round (inner index `j`) of iteration `l`, steps 2–4. -/
def mvcInner (D l j : ℕ) (s : MState) (ib : V → Option (Bool × ℕ)) : MState where
  r := s.r + 1
  t :=
    let bigs := ((recvd (s.v, s.t) ib).image Prod.snd).filter (l < ·)
    if h : bigs.Nonempty then bigs.min' h else s.t
  v := mmUpdate (phaseVal D 0 j) s.v (fun u => (ib u).map Prod.fst)
  dec := s.dec

/-- **Algorithm MVC** for inputs in `[0, K]`. -/
def mvc (f D K : ℕ) : Algorithm V ℕ (Bool × ℕ) MState ℕ where
  init _ x := ⟨0, x, true, none⟩
  send _ s _ := some (s.v, s.t)
  trans _ s ib :=
    if s.r % blk f D = 0 then mvcLocal K (s.r / blk f D) s
    else mvcInner D (s.r / blk f D) (s.r % blk f D - 1) s ib
  out _ s := s.dec

section Run

variable {f D K : ℕ} {adv : Adversary V} {inp : V → ℕ}

local notation "st" => state G (mvc f D K) adv inp

theorem mvc_trans (u : V) (s : MState) (ib : V → Option (Bool × ℕ)) :
    (mvc f D K).trans u s ib = if s.r % blk f D = 0 then mvcLocal K (s.r / blk f D) s
      else mvcInner D (s.r / blk f D) (s.r % blk f D - 1) s ib := rfl

theorem mvc_counter (r : ℕ) (u : V) : (st r u).r = r := by
  induction r generalizing u with
  | zero => rfl
  | succ r ih =>
    rw [state_succ, mvc_trans]
    split_ifs <;> simp [mvcLocal, mvcInner, ih]

theorem mvc_succ (r : ℕ) (w : V) : st (r + 1) w =
    if r % blk f D = 0 then mvcLocal K (r / blk f D) (st r w)
    else mvcInner D (r / blk f D) (r % blk f D - 1) (st r w)
      (inbox G (mvc f D K) adv (st r) r w) := by
  rw [state_succ, mvc_trans, mvc_counter]

theorem mvc_succ_local {r : ℕ} (w : V) (h : r % blk f D = 0) :
    st (r + 1) w = mvcLocal K (r / blk f D) (st r w) := by
  rw [mvc_succ, ite_eq_left_of_eq_true _ _ (eq_true h)]

theorem mvc_succ_inner {r : ℕ} (w : V) (h : r % blk f D ≠ 0) :
    st (r + 1) w = mvcInner D (r / blk f D) (r % blk f D - 1) (st r w)
      (inbox G (mvc f D K) adv (st r) r w) := by
  rw [mvc_succ, ite_eq_right_of_eq_false _ _ (eq_false h)]

open Classical in
theorem mvc_inbox (r : ℕ) (w u : V) : inbox G (mvc f D K) adv (st r) r w u =
    if Delivers G adv r u w then some ((st r u).v, (st r u).t) else none := rfl

/-! ### Arithmetic of blocks -/

theorem mod_blk {l j : ℕ} (hj : j < blk f D) : (blk f D * l + j) % blk f D = j := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem div_blk {l j : ℕ} (hj : j < blk f D) : (blk f D * l + j) / blk f D = l := by
  rw [Nat.mul_add_div (blk_pos f D), Nat.div_eq_of_lt hj, Nat.add_zero]

/-! ### Claim 5: `t` is always an input -/

theorem t_input (r : ℕ) (w : V) : ∃ u, (st r w).t = inp u := by
  induction r generalizing w with
  | zero => exact ⟨w, rfl⟩
  | succ r ih =>
    by_cases h : r % blk f D = 0
    · rw [mvc_succ_local w h]; exact ih w
    · rw [mvc_succ_inner w h]
      simp only [mvcInner]
      split_ifs with hne
      · have hm := min'_mem _ hne
        simp only [mem_filter, mem_image, mem_recvd, mvc_inbox] at hm
        obtain ⟨⟨⟨b, t⟩, hp, rfl⟩, -⟩ := hm
        rcases hp with hp | ⟨u, hu⟩
        · simp only [Prod.mk.injEq] at hp; rw [hp.2]; exact ih w
        · split_ifs at hu
          simp only [Option.some.injEq, Prod.mk.injEq] at hu
          rw [← hu.2]; exact ih u
      · exact ih w

/-! ### The `v`-trajectory follows Min-Max -/

theorem v_absStep {r : ℕ} (h : r % blk f D ≠ 0) :
    AbsStep G adv (fun r u => (st r u).v) r (phaseVal D 0 (r % blk f D - 1)) := by
  classical
  refine absStep_of_mmUpdate fun w => ?_
  rw [mvc_succ_inner w h]
  simp only [mvcInner]
  congr 1
  funext u
  rw [mvc_inbox]
  split_ifs <;> rfl

/-- **Claim 2**: at the end of every INNER-LOOP, all nodes that have not crashed hold the same
`v`. -/
theorem claim2 (hG : CTConn G f) (hD : FTDiamLE G f D) (hadm : adv.Admissible f) (l : ℕ) :
    ∃ c, ∀ u, adv.Alive (blk f D * (l + 1)) u → (st (blk f D * (l + 1)) u).v = c := by
  have hE : blk f D * (l + 1) = (blk f D * l + 1) + (2 * f + 2) * D := by
    simp only [blk]; ring
  rw [hE]
  apply minmax_core (x := fun r u => (st r u).v) hG hD hadm
  intro r h1 h2
  obtain ⟨j, rfl⟩ : ∃ j, r = blk f D * l + 1 + j := ⟨r - (blk f D * l + 1), by omega⟩
  have hj : 1 + j < blk f D := by simp only [blk]; omega
  have hmod : (blk f D * l + 1 + j) % blk f D = 1 + j := by rw [Nat.add_assoc]; exact mod_blk hj
  have := v_absStep (f := f) (D := D) (K := K) (adv := adv) (inp := inp) (G := G)
    (r := blk f D * l + 1 + j) (by omega)
  rw [hmod] at this
  simpa [phaseVal] using this

/-- Unanimity inside one INNER-LOOP. -/
theorem inner_unanimity (l : ℕ) {c : Bool}
    (h : ∀ u, adv.Alive (blk f D * l + 1) u → (st (blk f D * l + 1) u).v = c) :
    ∀ u, adv.Alive (blk f D * (l + 1)) u → (st (blk f D * (l + 1)) u).v = c := by
  have hE : blk f D * (l + 1) = blk f D * l + 1 + (2 * f + 2) * D := by simp only [blk]; ring
  intro u hu
  refine unanimity (G := G) (x := fun r u => (st r u).v) (r₁ := blk f D * l + 1)
    (r₂ := blk f D * (l + 1)) (fun r h1 h2 => ?_) h _ (by rw [hE]; omega) le_rfl u hu
  obtain ⟨j, rfl⟩ : ∃ j, r = blk f D * l + 1 + j := ⟨r - (blk f D * l + 1), by omega⟩
  have hj : 1 + j < blk f D := by rw [hE] at h2; simp only [blk] at h2 ⊢; omega
  have hmod : (blk f D * l + 1 + j) % blk f D = 1 + j := by rw [Nat.add_assoc]; exact mod_blk hj
  exact ⟨_, v_absStep (by omega)⟩

/-! ### Lemma 3: `v = 1 ⇒ t > l` during iteration `l` -/

/-- **Lemma 3** (for one iteration): if at the start of iteration `l` every node alive has
`t ≥ l`, then during the iteration every alive node with `v = 1` has `t > l`. -/
theorem inv_iteration (l : ℕ) (hP : ∀ u, adv.Alive (blk f D * l) u → l ≤ (st (blk f D * l) u).t) :
    ∀ j, j ≤ (2 * f + 2) * D → ∀ u, adv.Alive (blk f D * l + 1 + j) u →
      (st (blk f D * l + 1 + j) u).v = true → l < (st (blk f D * l + 1 + j) u).t := by
  intro j
  induction j with
  | zero =>
    intro _ u hu hv
    have hl : (blk f D * l + 0) % blk f D = 0 := mod_blk (blk_pos f D)
    rw [Nat.add_zero] at hl ⊢
    rw [mvc_succ_local u hl] at hv ⊢
    simp only [mvcLocal, Bool.not_eq_true', decide_eq_false_iff_not] at hv ⊢
    rw [Nat.mul_div_cancel_left _ (blk_pos f D)] at hv
    have := hP u (hu.mono (by omega))
    omega
  | succ j ih =>
    intro hj u hu hv
    have hjb : 1 + j < blk f D := by simp only [blk]; omega
    have hmod : (blk f D * l + 1 + j) % blk f D = 1 + j := by
      rw [Nat.add_assoc]; exact mod_blk hjb
    have hdiv : (blk f D * l + 1 + j) / blk f D = l := by rw [Nat.add_assoc]; exact div_blk hjb
    rw [show blk f D * l + 1 + (j + 1) = blk f D * l + 1 + j + 1 by ring] at hu hv ⊢
    rw [mvc_succ_inner u (by omega)] at hv ⊢
    simp only [mvcInner, hdiv] at hv ⊢
    have ih' := ih (by omega)
    -- some received tuple `(true, b)` with `b > l`
    have hex : ∃ p ∈ recvd ((st (blk f D * l + 1 + j) u).v, (st (blk f D * l + 1 + j) u).t)
        (inbox G (mvc f D K) adv (st (blk f D * l + 1 + j)) (blk f D * l + 1 + j) u), l < p.2 := by
      have hown : (st (blk f D * l + 1 + j) u).v = true →
          l < (st (blk f D * l + 1 + j) u).t := ih' u hu.of_succ
      cases ha : phaseVal D 0 ((blk f D * l + 1 + j) % blk f D - 1)
      · rw [ha] at hv
        have hv' := hv
        rw [← Bool.not_eq_false, mmUpdate_eq_iff] at hv'
        push Not at hv'
        have : (st (blk f D * l + 1 + j) u).v = true := by simpa using hv'.1
        exact ⟨_, mem_recvd.mpr (Or.inl rfl), hown this⟩
      · rw [ha] at hv
        rw [mmUpdate_eq_iff] at hv
        rcases hv with hv | ⟨w, hw⟩
        · exact ⟨_, mem_recvd.mpr (Or.inl rfl), hown hv⟩
        · simp only [mvc_inbox, Option.map_eq_some_iff] at hw
          obtain ⟨⟨b, t⟩, hw, hb⟩ := hw
          split_ifs at hw with hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          refine ⟨(b, t), mem_recvd.mpr (Or.inr ⟨w, by rw [mvc_inbox]; simp [hd, hw.1, hw.2]⟩), ?_⟩
          rw [← hw.2]
          exact ih' w hd.alive (by rw [hw.1]; exact hb)
    obtain ⟨p, hp, hlt⟩ := hex
    have hne : (((recvd ((st (blk f D * l + 1 + j) u).v, (st (blk f D * l + 1 + j) u).t)
        (inbox G (mvc f D K) adv (st (blk f D * l + 1 + j)) (blk f D * l + 1 + j) u)).image Prod.snd).filter
          (l < ·)).Nonempty := ⟨p.2, mem_filter.mpr ⟨mem_image_of_mem _ hp, hlt⟩⟩
    simp only [hne, ↓reduceDIte]
    exact (mem_filter.mp (min'_mem _ hne)).2

/-- Iterating Lemma 3: if all iterations before `m` ended with `v = 1` at the alive nodes, every
node alive at the start of iteration `m` has `t ≥ m`. -/
theorem t_ge_iter (m : ℕ)
    (hv : ∀ i < m, ∀ u, adv.Alive (blk f D * (i + 1)) u → (st (blk f D * (i + 1)) u).v = true) :
    ∀ u, adv.Alive (blk f D * m) u → m ≤ (st (blk f D * m) u).t := by
  induction m with
  | zero => intro _ _; omega
  | succ m ih =>
    intro u hu
    have hP := ih fun i hi => hv i (by omega)
    have hE : blk f D * (m + 1) = blk f D * m + 1 + (2 * f + 2) * D := by simp only [blk]; ring
    have := inv_iteration m hP ((2 * f + 2) * D) le_rfl u (by rw [← hE]; exact hu)
      (by rw [← hE]; exact hv m (by omega) u hu)
    rw [← hE] at this
    omega

/-! ### Decisions -/

theorem dec_succ_inner {r : ℕ} (w : V) (h : r % blk f D ≠ 0) : (st (r + 1) w).dec = (st r w).dec := by
  rw [mvc_succ_inner w h]; rfl

theorem dec_succ_local {r : ℕ} (w : V) (h : r % blk f D = 0) :
    (st (r + 1) w).dec = (st r w).dec.or (decAt K (r / blk f D) (st r w).v) := by
  rw [mvc_succ_local w h]; rfl

theorem dec_mono {r r' : ℕ} {w : V} {o : ℕ} (h : (st r w).dec = some o) (hr : r ≤ r') :
    (st r' w).dec = some o := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ r' _ ih =>
    by_cases hm : r' % blk f D = 0
    · rw [dec_succ_local w hm, ih]; rfl
    · rw [dec_succ_inner w hm, ih]

theorem decides_iff_dec {w : V} {o : ℕ} :
    Decides G (mvc f D K) adv inp w o ↔ ∃ r, (st r w).dec = some o := by
  constructor
  · rintro ⟨r, hr, -⟩; exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    obtain ⟨o', ho'⟩ := decides_of_out (alg := mvc f D K) (G := G) (adv := adv) (inp := inp) hr
    have ho'' := ho'
    obtain ⟨r', hr', -⟩ := ho''
    have h1 := dec_mono hr (le_max_left r r')
    have h2 := dec_mono (K := K) hr' (le_max_right r r')
    have : o = o' := Option.some_injective _ (h1.symm.trans h2)
    subst this
    exact ho'

/-- Everybody has decided after the local round of block `K + 1`. -/
theorem dec_isSome (w : V) : ∃ o, (st (blk f D * (K + 1) + 1) w).dec = some o := by
  have h0 : (blk f D * (K + 1) + 0) % blk f D = 0 := mod_blk (blk_pos f D)
  have hd : (blk f D * (K + 1) + 0) / blk f D = K + 1 := div_blk (blk_pos f D)
  simp only [Nat.add_zero] at h0 hd
  rw [dec_succ_local w h0, hd]
  cases (st (blk f D * (K + 1)) w).dec with
  | some o => exact ⟨o, rfl⟩
  | none =>
    simp only [decAt, Option.none_or]
    split_ifs <;> exact ⟨_, rfl⟩

/-- Where a decision comes from: the local round of some block `l ∈ [1, K + 1]`. -/
theorem dec_origin {r : ℕ} {w : V} {o : ℕ} (h : (st r w).dec = some o) :
    ∃ l, 1 ≤ l ∧ l ≤ K + 1 ∧ (st (blk f D * l) w).dec = none ∧
      decAt K l (st (blk f D * l) w).v = some o := by
  induction r with
  | zero => simp [state_zero, mvc] at h
  | succ r ih =>
    by_cases hprev : (st r w).dec = some o
    · exact ih hprev
    by_cases hm : r % blk f D = 0
    · rw [dec_succ_local w hm] at h
      have hnone : (st r w).dec = none := by
        cases hd : (st r w).dec with
        | none => rfl
        | some o' => rw [hd] at h; simp at h; exact absurd (h ▸ hd) hprev
      rw [hnone, Option.none_or] at h
      obtain ⟨l, hl⟩ : ∃ l, r = blk f D * l := ⟨r / blk f D, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)).symm⟩
      subst hl
      rw [Nat.mul_div_cancel_left _ (blk_pos f D)] at h
      have hl1 : 1 ≤ l := by
        by_contra hl; simp only [decAt] at h; split_ifs at h <;> omega
      have hlK : l ≤ K + 1 := by
        by_contra hlK
        obtain ⟨o', ho'⟩ := dec_isSome (K := K) (G := G) (adv := adv) (inp := inp) (f := f) (D := D) w
        have := dec_mono ho' (show blk f D * (K + 1) + 1 ≤ blk f D * l by
          have := Nat.mul_le_mul_left (blk f D) (show K + 2 ≤ l by omega)
          have := blk_pos f D
          nlinarith)
        rw [hnone] at this; simp at this
      exact ⟨l, hl1, hlK, hnone, h⟩
    · rw [dec_succ_inner w hm] at h; exact absurd h hprev

end Run

/-- **Theorem 4.** Algorithm MVC solves crash consensus for inputs in `[0, K]` in every graph
satisfying `f` CT node connectivity (with phases of `D ≥ d` rounds). -/
theorem theorem4 {f D K : ℕ} (hG : CTConn G f) (hD : FTDiamLE G f D) :
    SolvesOn G f {x | x ≤ K} (mvc f D K) := by
  intro adv hadm inp hinp
  set B := blk f D
  -- agreement of the `v`s of correct nodes at all block boundaries
  have hagrv : ∀ u w, adv.crash u = none → adv.crash w = none → ∀ l, 1 ≤ l →
      (state G (mvc f D K) adv inp (B * l) u).v = (state G (mvc f D K) adv inp (B * l) w).v := by
    intro u w hu hw l hl
    obtain ⟨c, hc⟩ := claim2 (K := K) (inp := inp) hG hD hadm (l - 1)
    rw [show l - 1 + 1 = l by omega] at hc
    exact (hc u (Adversary.alive_of_correct hu _)).trans (hc w (Adversary.alive_of_correct hw _)).symm
  refine ⟨fun u _ => ?_, fun u w o o' hu hw ho ho' => ?_, fun u o hu ho => ?_⟩
  · -- termination
    obtain ⟨o, ho⟩ := dec_isSome (G := G) (adv := adv) (inp := inp) (f := f) (D := D) (K := K) u
    exact ⟨o, decides_iff_dec.mpr ⟨_, ho⟩⟩
  · -- agreement
    have hdec : ∀ r, (state G (mvc f D K) adv inp r u).dec =
        (state G (mvc f D K) adv inp r w).dec := by
      intro r
      induction r with
      | zero => rfl
      | succ r ih =>
        by_cases hm : r % B = 0
        · rw [dec_succ_local u hm, dec_succ_local w hm, ih]
          obtain ⟨l, rfl⟩ : ∃ l, r = B * l :=
            ⟨r / B, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)).symm⟩
          by_cases hl : 1 ≤ l
          · rw [hagrv u w hu hw l hl]
          · obtain rfl : l = 0 := by omega
            simp [decAt]
        · rw [dec_succ_inner u hm, dec_succ_inner w hm, ih]
    obtain ⟨r, hr⟩ := decides_iff_dec.mp ho
    obtain ⟨r', hr'⟩ := decides_iff_dec.mp ho'
    have h1 := dec_mono hr (le_max_left r r')
    have h2 := dec_mono hr' (le_max_right r r')
    rw [hdec] at h1
    exact Option.some_injective _ (h1.symm.trans h2)
  · -- validity
    obtain ⟨r, hr⟩ := decides_iff_dec.mp ho
    obtain ⟨l, hl1, hlK, hnone, hdl⟩ := dec_origin hr
    set m := l - 1 with hm
    have hlm : l = m + 1 := by omega
    -- all earlier iterations ended with `v = 1` at `u`, hence at every alive node
    have hprev : ∀ i < m, ∀ w, adv.Alive (B * (i + 1)) w →
        (state G (mvc f D K) adv inp (B * (i + 1)) w).v = true := by
      intro i hi w hw
      have hd : (state G (mvc f D K) adv inp (B * (i + 1) + 1) u).dec = none := by
        cases hd : (state G (mvc f D K) adv inp (B * (i + 1) + 1) u).dec with
        | none => rfl
        | some o' =>
          have := dec_mono hd (show B * (i + 1) + 1 ≤ B * l by
            have := Nat.mul_le_mul_left B (show i + 2 ≤ l by omega)
            have hB : 0 < B := blk_pos f D
            have : B * (i + 2) = B * (i + 1) + B := by ring
            omega)
          rw [hnone] at this; simp at this
      have h0 : (B * (i + 1) + 0) % B = 0 := mod_blk (blk_pos f D)
      have hdv : (B * (i + 1) + 0) / B = i + 1 := div_blk (blk_pos f D)
      simp only [Nat.add_zero] at h0 hdv
      rw [dec_succ_local u h0, hdv] at hd
      have huv : (state G (mvc f D K) adv inp (B * (i + 1)) u).v = true := by
        by_contra hv
        simp only [Bool.not_eq_true] at hv
        simp [decAt, hv] at hd
      obtain ⟨c, hc⟩ := claim2 (K := K) (inp := inp) hG hD hadm i
      rw [hc w hw, ← hc u (Adversary.alive_of_correct hu _)]
      exact huv
    simp only [decAt] at hdl
    split_ifs at hdl with h1 h2
    · -- STEP III exit at iteration `m`: Claim 6
      have ho : o = m := by simp only [Option.some.injEq] at hdl; omega
      have hex : ∃ w, adv.Alive (B * m + 1) w ∧
          (state G (mvc f D K) adv inp (B * m + 1) w).v = false := by
        by_contra hno
        push Not at hno
        have := inner_unanimity (G := G) (K := K) (inp := inp) m (c := true)
          (fun w hw => by simpa using hno w hw) u (Adversary.alive_of_correct hu _)
        rw [← hlm, h1.2] at this
        simp at this
      obtain ⟨w, -, hwv⟩ := hex
      have h0 : (B * m + 0) % B = 0 := mod_blk (blk_pos f D)
      have hdv : (B * m + 0) / B = m := div_blk (blk_pos f D)
      simp only [Nat.add_zero] at h0 hdv
      rw [mvc_succ_local w h0, hdv] at hwv
      simp only [mvcLocal, Bool.not_eq_false', decide_eq_true_eq] at hwv
      obtain ⟨w', hw'⟩ := t_input (G := G) (adv := adv) (f := f) (D := D) (K := K) (inp := inp)
        (B * m) w
      exact ⟨w', by rw [← hw', hwv, ho]⟩
    · -- output `K` after the OUTER-LOOP: impossible
      exfalso
      have hvK : (state G (mvc f D K) adv inp (B * l) u).v = true := by
        by_contra hv
        simp only [Bool.not_eq_true] at hv
        exact h1 ⟨hl1, hv⟩
      have hall : ∀ i < l, ∀ w, adv.Alive (B * (i + 1)) w →
          (state G (mvc f D K) adv inp (B * (i + 1)) w).v = true := by
        intro i hi w hw
        by_cases him : i < m
        · exact hprev i him w hw
        · have hil : i + 1 = l := by omega
          obtain ⟨c, hc⟩ := claim2 (K := K) (inp := inp) hG hD hadm i
          rw [hc w hw, ← hc u (Adversary.alive_of_correct hu _), hil]
          exact hvK
      have hge := t_ge_iter (G := G) (K := K) (inp := inp) l hall u (Adversary.alive_of_correct hu _)
      obtain ⟨w', hw'⟩ := t_input (G := G) (adv := adv) (f := f) (D := D) (K := K) (inp := inp)
        (B * l) u
      have h3 : l ≤ inp w' := hge.trans_eq hw'
      have h4 : inp w' ≤ K := hinp w'
      omega

end CrashConsensusDigraph

namespace CrashConsensusDigraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V}

/-- **Tight condition for multi-valued consensus** (Theorems 1 and 4): for inputs in `[0, K]`
with `K ≥ 1`, crash consensus with at most `f` crashes is solvable on `G` iff `G` satisfies `f`
CT node connectivity. -/
theorem consensus_iff {f K : ℕ} (hK : 1 ≤ K) :
    (∃ (M S : Type) (alg : Algorithm V ℕ M S ℕ), SolvesOn G f {x | x ≤ K} alg) ↔ CTConn G f := by
  constructor
  · rintro ⟨M, S, alg, h⟩
    exact theorem1 (a := 0) (b := 1) (by simp) (by simpa using hK) (by simp) h
  · intro h
    exact ⟨Bool × ℕ, MState, mvc f (ftDiam G f) K, theorem4 h (ftDiamLE_ftDiam f)⟩

end CrashConsensusDigraph
