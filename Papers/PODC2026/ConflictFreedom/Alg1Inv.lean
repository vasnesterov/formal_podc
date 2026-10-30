import Papers.PODC2026.ConflictFreedom.Alg1Step
import Papers.PODC2026.ConflictFreedom.GCAProof

/-!
# Algorithm 1: structural invariants and the GCA simulation

* `Alg1.LInv C i`: local structure of process `i` (phase vs. pending operation, rounds of the
  ghost history, relation between the round and the register `S[i]`);
* `Alg1.Inv1 C`: `LInv` for all processes, and every per-round GCA state `gst C r` is a reachable
  state of Algorithm 2 (`GCA.Reach`), so it satisfies the GCA properties (Theorem 5.1).
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

namespace Alg1

variable {A : ObjSpec} {n : ℕ}

/-- Local invariant of process `i`. -/
structure LInv (C : Cfg A n) (i : Fin n) : Prop where
  pend_iff : C.pend i = none ↔ (C.loc i).phase = .idle
  readS_lt : ∀ j best, (C.loc i).phase = .readS j best → j < n
  hist_le : ∀ r, (C.loc i).hist r ≠ none → 1 ≤ r ∧ r ≤ (C.loc i).r
  hist_pc : ∀ r g, (C.loc i).hist r = some g → g.pc = 4
  gca : ∀ g, (C.loc i).phase = .gca g →
    1 ≤ (C.loc i).r ∧ (C.loc i).hist (C.loc i).r = none ∧ g.pc < 4
  sreg_idle : (C.loc i).phase = .idle → (C.mem (.S i)).1 = (C.loc i).r
  sreg_readS : ∀ j best, (C.loc i).phase = .readS j best → (C.mem (.S i)).1 = (C.loc i).r
  sreg_done : (C.loc i).phase = .done → (C.mem (.S i)).1 = (C.loc i).r
  sreg_gca : ∀ g, (C.loc i).phase = .gca g → (C.mem (.S i)).1 < (C.loc i).r
  sreg_writeS : (C.loc i).phase = .writeS → (C.mem (.S i)).1 < (C.loc i).r
  readS_best : ∀ j best, (C.loc i).phase = .readS j best → i.val < j → (C.loc i).r ≤ best.1

/-- Structural invariant: local invariants and reachability of every per-round GCA state. -/
structure Inv1 (C : Cfg A n) : Prop where
  loc : ∀ i, LInv C i
  reach : ∀ r, GCA.Reach (gst C r)

lemma LInv.congr {C C' : Cfg A n} {i : Fin n} (h : LInv C i) (hl : C'.loc i = C.loc i)
    (hp : C'.pend i = C.pend i) (hs : C'.mem (.S i) = C.mem (.S i)) : LInv C' i := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  rw [← hl, ← hp, ← hs] at *
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

@[simp] lemma locAt_of_not_gca {l : Loc A n} (h : ∀ g, l.phase ≠ .gca g) (r : ℕ) :
    locAt l r = l.hist r := by
  unfold locAt; split
  · rename_i g hg; exact absurd hg (h g)
  · rfl

lemma locAt_gca {l : Loc A n} {g : GCA.Loc n (Tr A n)} (h : l.phase = .gca g) (r : ℕ) :
    locAt l r = if r = l.r then some g else l.hist r := by
  unfold locAt; rw [h]

/-- `gst` only depends on the snapshot objects and on `locAt`. -/
lemma gst_eq_of {C C' : Cfg A n} {r : ℕ} (hA : C'.mem (.A r) = C.mem (.A r))
    (hB : C'.mem (.B r) = C.mem (.B r)) (hl : ∀ i, locAt (C'.loc i) r = locAt (C.loc i) r) :
    gst C' r = gst C r := by
  simp only [gst, hA, hB, GCA.State.mk.injEq, true_and]
  funext i; exact hl i

lemma gst_loc (C : Cfg A n) (r : ℕ) (i : Fin n) : (gst C r).loc i = locAt (C.loc i) r := rfl
lemma gst_A (C : Cfg A n) (r : ℕ) : (gst C r).A = C.mem (.A r) := rfl
lemma gst_B (C : Cfg A n) (r : ℕ) : (gst C r).B = C.mem (.B r) := rfl

variable [Inhabited A.Resp] [Inhabited A.Op] [NeZero n]

/-- Response steps: only from phase `done`. -/
lemma step_ret_cases {C C' : Cfg A n} {p : Fin n} {r : A.Resp}
    (h : (impl (A := A) (n := n)).step C (.ret p r) = some C') (hL : LInv C p) :
    (C.loc p).phase = .done ∧ r = retT (C.loc p).s (C.loc p).cmd ∧
      C' = { C with pend := Function.update C.pend p none,
                    loc := Function.update C.loc p { C.loc p with phase := .idle } } := by
  obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  change act p (C.loc p) = _ at hact
  have hC' : C' = { C with pend := C'.pend, loc := C'.loc } := by
    cases C'; simp only [Config.mk.injEq, and_true, true_and]; exact hmem
  unfold act at hact
  split at hact
  · rename_i hph; exact absurd (hL.pend_iff.2 hph) hp
  · rename_i j best hph
    split at hact
    · cases hact
    · rename_i hj; exact absurd (hL.readS_lt j best hph) hj
  · split at hact <;> cases hact
  · cases hact
  · rename_i hph
    cases hact
    exact ⟨hph, rfl, by rw [hC', hpend, hloc]⟩

lemma linv_init (i : Fin n) : LInv (impl (A := A) (n := n)).initCfg i := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Impl.initCfg, impl]

lemma gst_init (r : ℕ) : gst (impl (A := A) (n := n)).initCfg r = GCA.State.init := by
  simp only [gst, Impl.initCfg, impl, GCA.State.init, GCA.State.mk.injEq]
  refine ⟨trivial, trivial, ?_⟩
  funext i; simp [locAt]

theorem inv1_init : Inv1 (impl (A := A) (n := n)).initCfg :=
  ⟨linv_init, fun r => by rw [gst_init]; exact GCA.Reach.init⟩

theorem Inv1.step_inv {C C' : Cfg A n} (hI : Inv1 C) {p : Fin n} {o : A.Op}
    (h : (impl (A := A) (n := n)).step C (.inv p o) = some C') : Inv1 C' := by
  obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  have hL := hI.loc p
  have hidle : (C.loc p).phase = .idle := hL.pend_iff.1 hp
  have hlp : C'.loc p = invoke p (C.loc p) o := by rw [hloc]; simp; rfl
  have hlo : ∀ i, i ≠ p → C'.loc i = C.loc i := fun i hi => by rw [hloc]; simp [hi]
  constructor
  · intro i
    by_cases hi : i = p
    · subst hi
      have hS : C'.mem (.S i) = C.mem (.S i) := by rw [hmem]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hlp, hpend, invoke]
      · intro j best hj; simp only [hlp, invoke, Phase.readS.injEq] at hj
        rw [← hj.1]; exact Nat.pos_of_neZero n
      · simpa [hlp, invoke] using hL.hist_le
      · simpa [hlp, invoke] using hL.hist_pc
      · intro g hg; simp [hlp, invoke] at hg
      · intro hg; simp [hlp, invoke] at hg
      · intro j best _; rw [hS, hlp]; exact hL.sreg_idle hidle
      · intro hg; simp [hlp, invoke] at hg
      · intro g hg; simp [hlp, invoke] at hg
      · intro hg; simp [hlp, invoke] at hg
      · intro j best hj hij; simp only [hlp, invoke, Phase.readS.injEq] at hj
        omega
    · exact (hI.loc i).congr (hlo i hi) (by rw [hpend]; simp [hi]) (by rw [hmem])
  · intro r
    have hg : gst C' r = gst C r := gst_eq_of (by rw [hmem]) (by rw [hmem]) (fun i => by
      by_cases hi : i = p
      · subst hi; rw [hlp]; unfold locAt; simp [invoke, hidle]
      · rw [hlo i hi])
    rw [hg]; exact hI.reach r

theorem Inv1.step_ret {C C' : Cfg A n} (hI : Inv1 C) {p : Fin n} {r : A.Resp}
    (h : (impl (A := A) (n := n)).step C (.ret p r) = some C') : Inv1 C' := by
  have hL := hI.loc p
  obtain ⟨hdone, -, hC'⟩ := step_ret_cases h hL
  have hl : C'.loc = Function.update C.loc p { C.loc p with phase := .idle } := by rw [hC']
  have hpd : C'.pend = Function.update C.pend p none := by rw [hC']
  have hm : C'.mem = C.mem := by rw [hC']
  clear hC'
  constructor
  · intro i
    by_cases hi : i = p
    · subst hi
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hl, hpd, hm]
      · simpa using hL.hist_le
      · simpa using hL.hist_pc
      · exact hL.sreg_done hdone
    · exact (hI.loc i).congr (by simp [hl, hi]) (by simp [hpd, hi]) (by rw [hm])
  · intro r
    have hg : gst C' r = gst C r :=
      gst_eq_of (by rw [hm]) (by rw [hm]) (fun i => by
        by_cases hi : i = p
        · subst hi; rw [hl]; unfold locAt; simp [hdone]
        · simp [hl, hi])
    rw [hg]; exact hI.reach r

@[simp] lemma setLoc_loc (C : Cfg A n) (p : Fin n) (l : Loc A n) :
    (setLoc C p l).loc = Function.update C.loc p l := rfl
@[simp] lemma setLoc_mem (C : Cfg A n) (p : Fin n) (l : Loc A n) : (setLoc C p l).mem = C.mem :=
  rfl
@[simp] lemma setLoc_pend (C : Cfg A n) (p : Fin n) (l : Loc A n) :
    (setLoc C p l).pend = C.pend := rfl
@[simp] lemma setMemLoc_loc (C : Cfg A n) (o : Obj n) (v : (base A n o).State) (p : Fin n)
    (l : Loc A n) : (setMemLoc C o v p l).loc = Function.update C.loc p l := rfl
@[simp] lemma setMemLoc_mem (C : Cfg A n) (o : Obj n) (v : (base A n o).State) (p : Fin n)
    (l : Loc A n) : (setMemLoc C o v p l).mem = Function.update C.mem o v := rfl
@[simp] lemma setMemLoc_pend (C : Cfg A n) (o : Obj n) (v : (base A n o).State) (p : Fin n)
    (l : Loc A n) : (setMemLoc C o v p l).pend = C.pend := rfl

/-- Local invariants of the processes that do not move. -/
lemma linv_other {C C' : Cfg A n} (hI : Inv1 C) {p : Fin n}
    (hl : C'.loc = Function.update C.loc p (C'.loc p)) (hp : C'.pend = C.pend)
    (hS : ∀ i, i ≠ p → C'.mem (.S i) = C.mem (.S i)) (i : Fin n) (hi : i ≠ p) : LInv C' i :=
  (hI.loc i).congr (by rw [hl]; simp [hi]) (by rw [hp]) (hS i hi)

lemma better_left (best v : ℕ × Tr A n) : best.1 ≤ (better best v).1 := by
  unfold better; split <;> omega

lemma better_right (best v : ℕ × Tr A n) : v.1 ≤ (better best v).1 := by
  unfold better; split <;> omega

lemma better_cases (best v : ℕ × Tr A n) : better best v = best ∨ better best v = v := by
  unfold better; split <;> simp

/-- After reading `S[j]` in phase `readS j best`, the round of `p` is at most the best round. -/
lemma LInv.r_le_better {C : Cfg A n} {p : Fin n} (hL : LInv C p) {j : ℕ} {best : ℕ × Tr A n}
    (hph : (C.loc p).phase = .readS j best) (hj : j < n) (hpj : p.val ≤ j) :
    (C.loc p).r ≤ (better best (C.mem (.S ⟨j, hj⟩))).1 := by
  rcases Nat.lt_or_eq_of_le hpj with h | h
  · exact (hL.readS_best j best hph h).trans (better_left _ _)
  · have : (⟨j, hj⟩ : Fin n) = p := Fin.ext h.symm
    rw [this]
    exact (hL.sreg_readS j best hph).symm.le.trans (better_right _ _)

lemma reach_invoke {g g' : GCA.State n (Tr A n)} (h : GCA.Reach g) (i : Fin n)
    (s : Tr A n) (hi : g.loc i = none)
    (e : g' = { g with loc := Function.update g.loc i (some (GCA.Loc.init s)) }) :
    GCA.Reach g' := e ▸ GCA.Reach.invoke i s h hi

lemma reach_step {g g' : GCA.State n (Tr A n)} (h : GCA.Reach g) (i : Fin n)
    (l : GCA.Loc n (Tr A n)) (hi : g.loc i = some l) (hpc : l.pc < 4) (e : g' = g.step i l) :
    GCA.Reach g' := e ▸ GCA.Reach.step i l h hi hpc

lemma locAt_eq_hist_of_ne {l : Loc A n} {r : ℕ} (h : r ≠ l.r) : locAt l r = l.hist r := by
  unfold locAt; split
  · simp [h]
  · rfl

theorem Inv1.tau_readS {C : Cfg A n} (hI : Inv1 C) {p : Fin n} (j : ℕ) (best : ℕ × Tr A n)
    (hj : j < n) (hph : (C.loc p).phase = .readS j best) (hlt : j + 1 < n)
    (hpn : C.pend p ≠ none) :
    Inv1 (setLoc C p
      { C.loc p with phase := .readS (j + 1) (better best (C.mem (.S ⟨j, hj⟩))) }) := by
  have hL := hI.loc p
  constructor
  · intro i
    by_cases hi : i = p
    · subst hi
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [setLoc_loc,
        setLoc_pend, setLoc_mem, Function.update_self, reduceCtorEq, Phase.readS.injEq]
      · simpa [hph] using hL.pend_iff
      · rintro j' b' ⟨rfl, -⟩; exact hlt
      · exact hL.hist_le
      · exact hL.hist_pc
      · intro g hg; cases hg
      · intro hg; cases hg
      · intro _ _ _; exact hL.sreg_readS j best hph
      · intro hg; cases hg
      · intro g hg; cases hg
      · intro hg; cases hg
      · rintro j' b' ⟨rfl, rfl⟩ hij
        exact hL.r_le_better hph hj (by omega)
    · exact linv_other (C' := setLoc C p _) hI (by simp) rfl (fun _ _ => rfl) i hi
  · intro r
    have hg : gst (setLoc C p
        { C.loc p with phase := .readS (j + 1) (better best (C.mem (.S ⟨j, hj⟩))) }) r =
        gst C r := gst_eq_of rfl rfl (fun i => by
      by_cases hi : i = p
      · subst hi; simp only [setLoc_loc, Function.update_self]; unfold locAt; simp [hph]
      · simp [hi])
    rw [hg]; exact hI.reach r

theorem Inv1.tau_readLast {C : Cfg A n} (hI : Inv1 C) {p : Fin n} (j : ℕ) (best : ℕ × Tr A n)
    (hj : j < n) (hph : (C.loc p).phase = .readS j best) (hlt : ¬ j + 1 < n)
    (hpn : C.pend p ≠ none) :
    Inv1 (setLoc C p ((C.loc p).afterRead (better best (C.mem (.S ⟨j, hj⟩))))) := by
  have hL := hI.loc p
  set b := better best (C.mem (.S ⟨j, hj⟩)) with hb
  have hrb : (C.loc p).r ≤ b.1 := hL.r_le_better hph hj (by omega)
  constructor
  · intro i
    by_cases hi : i = p
    · subst hi
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [setLoc_loc,
        setLoc_pend, setLoc_mem, Function.update_self, Loc.afterRead, Loc.startRound,
        reduceCtorEq, Phase.gca.injEq]
      · simpa [hph] using hL.pend_iff
      · intro _ _ h; cases h
      · intro r hr; have := hL.hist_le r hr; omega
      · exact hL.hist_pc
      · rintro g rfl
        refine ⟨by omega, ?_, by simp [GCA.Loc.init]⟩
        by_contra hc; have := hL.hist_le _ hc; omega
      · intro hg; cases hg
      · intro _ _ h; cases h
      · intro hg; cases hg
      · intro _ _; have := hL.sreg_readS j best hph; omega
      · intro hg; cases hg
      · intro _ _ h; cases h
    · exact linv_other (C' := setLoc C p _) hI (by simp) rfl (fun _ _ => rfl) i hi
  · intro r
    by_cases hr : r = b.1 + 1
    · subst hr
      refine reach_invoke (hI.reach (b.1 + 1)) p (b.2.snoc (C.loc p).cmd) ?_ ?_
      · rw [gst_loc, locAt_of_not_gca (by simp [hph])]
        by_contra hc; have := hL.hist_le _ hc; omega
      · simp only [gst, setLoc_mem, setLoc_loc, GCA.State.mk.injEq, true_and]
        funext i
        by_cases hi : i = p
        · subst hi; simp [locAt, Loc.afterRead, Loc.startRound]
        · simp [hi]
    · have hg : gst (setLoc C p ((C.loc p).afterRead b)) r = gst C r := gst_eq_of rfl rfl
        (fun i => by
          by_cases hi : i = p
          · subst hi; simp only [setLoc_loc, Function.update_self]
            rw [locAt_eq_hist_of_ne (by simpa [Loc.afterRead, Loc.startRound] using hr),
              locAt_of_not_gca (by simp [hph])]
            rfl
          · simp [hi])
      rw [hg]; exact hI.reach r

/-- A GCA step of `p` in its current round (phases `gca` before and after, same round and
history) changes the local GCA state of round `(C.loc p).r` only. -/
lemma locAt_gca_step {l l' : Loc A n} {g g' : GCA.Loc n (Tr A n)} (hph : l.phase = .gca g)
    (hph' : l'.phase = .gca g') (hr : l'.r = l.r) (hh : l'.hist = l.hist) (r : ℕ) :
    locAt l' r = if r = l.r then some g' else locAt l r := by
  rw [locAt_gca hph', locAt_gca hph, hr, hh]; split <;> rfl

theorem Inv1.tau_gca012 {C C' : Cfg A n} (hI : Inv1 C) {p : Fin n} {g g' : GCA.Loc n (Tr A n)}
    (hph : (C.loc p).phase = .gca g) (hpn : C.pend p ≠ none)
    (hloc : C'.loc = Function.update C.loc p { C.loc p with phase := .gca g' })
    (hpend : C'.pend = C.pend) (hS : ∀ i, C'.mem (.S i) = C.mem (.S i))
    (hpc' : g'.pc < 4)
    (hgst : gst C' (C.loc p).r = (gst C (C.loc p).r).step p g)
    (hother : ∀ r, r ≠ (C.loc p).r → C'.mem (.A r) = C.mem (.A r) ∧
      C'.mem (.B r) = C.mem (.B r)) : Inv1 C' := by
  have hL := hI.loc p
  obtain ⟨hr1, hrn, hpc⟩ := hL.gca g hph
  have hlp : C'.loc p = { C.loc p with phase := .gca g' } := by rw [hloc]; simp
  constructor
  · intro i
    by_cases hi : i = p
    · subst hi
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hlp, hpend, hS,
        reduceCtorEq, Phase.gca.injEq]
      · simpa [hph] using hL.pend_iff
      · intro _ _ h; cases h
      · exact hL.hist_le
      · exact hL.hist_pc
      · rintro _ rfl; exact ⟨hr1, hrn, hpc'⟩
      · intro hg; cases hg
      · intro _ _ h; cases h
      · intro hg; cases hg
      · intro _ _; exact hL.sreg_gca g hph
      · intro hg; cases hg
      · intro _ _ h; cases h
    · exact linv_other hI (by rw [hloc]; simp) hpend (fun i _ => hS i) i hi
  · intro r
    by_cases hr : r = (C.loc p).r
    · subst hr
      refine reach_step (hI.reach _) p g (by rw [gst_loc, locAt_gca hph]; simp) hpc hgst
    · have hg : gst C' r = gst C r := gst_eq_of (hother r hr).1 (hother r hr).2 (fun i => by
        by_cases hi : i = p
        · subst hi
          rw [hlp, locAt_gca_step (l' := { C.loc i with phase := .gca g' }) hph rfl rfl rfl]
          simp [hr]
        · rw [hloc]; simp [hi])
      rw [hg]; exact hI.reach r

theorem Inv1.tau_gca3 {C : Cfg A n} (hI : Inv1 C) {p : Fin n} {g : GCA.Loc n (Tr A n)}
    (hph : (C.loc p).phase = .gca g) (hpc3 : g.pc ≠ 0 ∧ g.pc ≠ 1 ∧ g.pc ≠ 2)
    (hpn : C.pend p ≠ none) :
    Inv1 (setLoc C p ((C.loc p).afterGCA { g with pc := 4, bv := C.mem (.B (C.loc p).r) })) := by
  have hL := hI.loc p
  obtain ⟨hr1, hrn, hpc⟩ := hL.gca g hph
  have hpc' : g.pc = 3 := by omega
  set g4 : GCA.Loc n (Tr A n) := { g with pc := 4, bv := C.mem (.B (C.loc p).r) } with hg4
  have hstep : (gst C (C.loc p).r).step p g =
      ⟨C.mem (.A (C.loc p).r), C.mem (.B (C.loc p).r),
        Function.update (gst C (C.loc p).r).loc p (some g4)⟩ := GCA.step_eq_three hpc'
  have hreach := reach_step (hI.reach (C.loc p).r) p g
    (by rw [gst_loc, locAt_gca hph]; simp) hpc rfl
  rw [hstep] at hreach
  by_cases hex : g4.output.2 = true ∧ (C.loc p).cmd ∈ g4.output.1.supp
  · have hl' : (C.loc p).afterGCA g4 = { C.loc p with
        hist := Function.update (C.loc p).hist (C.loc p).r (some g4), s := g4.output.1,
        phase := .writeS, cr := Function.update (C.loc p).cr (C.loc p).seq (C.loc p).r } := by
      simp [Loc.afterGCA, hex]
    rw [hl']
    constructor
    · intro i
      by_cases hi : i = p
      · subst hi
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [setLoc_loc,
          setLoc_pend, setLoc_mem, Function.update_self, reduceCtorEq]
        · simpa [hph] using hL.pend_iff
        · intro _ _ h; cases h
        · intro r hr
          by_cases hrr : r = (C.loc i).r
          · omega
          · simp only [ne_eq, Function.update_of_ne hrr] at hr; exact hL.hist_le r hr
        · intro r g' hr
          by_cases hrr : r = (C.loc i).r
          · subst hrr; simp only [Function.update_self, Option.some.injEq] at hr; rw [← hr]
          · rw [Function.update_of_ne hrr] at hr; exact hL.hist_pc r g' hr
        · intro _ h; cases h
        · intro h; cases h
        · intro _ _ h; cases h
        · intro h; cases h
        · intro _ h; cases h
        · intro _; exact hL.sreg_gca g hph
        · intro _ _ h; cases h
      · exact linv_other (C' := setLoc C p _) hI (by simp) rfl (fun _ _ => rfl) i hi
    · intro r
      by_cases hr : r = (C.loc p).r
      · subst hr
        convert hreach using 1
        simp only [gst, setLoc_mem, setLoc_loc, GCA.State.mk.injEq, true_and]
        funext i
        by_cases hi : i = p
        · subst hi; simp [locAt]
        · simp [hi]
      · have hg : gst (setLoc C p { C.loc p with
            hist := Function.update (C.loc p).hist (C.loc p).r (some g4), s := g4.output.1,
            phase := .writeS, cr := Function.update (C.loc p).cr (C.loc p).seq (C.loc p).r }) r =
            gst C r := gst_eq_of rfl rfl (fun i => by
          by_cases hi : i = p
          · subst hi; simp only [setLoc_loc, Function.update_self]
            rw [locAt_of_not_gca (by simp), locAt_gca hph]; simp [hr]
          · simp [hi])
        rw [hg]; exact hI.reach r
  · have hl' : (C.loc p).afterGCA g4 = { (C.loc p).startRound (C.loc p).r g4.output.1 with
        hist := Function.update (C.loc p).hist (C.loc p).r (some g4) } := by
      simp only [Loc.afterGCA, hex, if_false]
    rw [hl']
    constructor
    · intro i
      by_cases hi : i = p
      · subst hi
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [setLoc_loc,
          setLoc_pend, setLoc_mem, Function.update_self, Loc.startRound, reduceCtorEq,
          Phase.gca.injEq]
        · simpa [hph] using hL.pend_iff
        · intro _ _ h; cases h
        · intro r hr
          by_cases hrr : r = (C.loc i).r
          · omega
          · simp only [ne_eq, Function.update_of_ne hrr] at hr; have := hL.hist_le r hr; omega
        · intro r g' hr
          by_cases hrr : r = (C.loc i).r
          · subst hrr; simp only [Function.update_self, Option.some.injEq] at hr; rw [← hr]
          · rw [Function.update_of_ne hrr] at hr; exact hL.hist_pc r g' hr
        · rintro _ rfl
          refine ⟨by omega, ?_, by simp [GCA.Loc.init]⟩
          rw [Function.update_of_ne (by omega)]
          by_contra hc; have := hL.hist_le _ hc; omega
        · intro h; cases h
        · intro _ _ h; cases h
        · intro h; cases h
        · intro _ _; have := hL.sreg_gca g hph; omega
        · intro h; cases h
        · intro _ _ h; cases h
      · exact linv_other (C' := setLoc C p _) hI (by simp) rfl (fun _ _ => rfl) i hi
    · intro r
      by_cases hr : r = (C.loc p).r
      · subst hr
        convert hreach using 1
        simp only [gst, setLoc_mem, setLoc_loc, GCA.State.mk.injEq, true_and]
        funext i
        by_cases hi : i = p
        · subst hi; simp [locAt, Loc.startRound]
        · simp [hi]
      · by_cases hr' : r = (C.loc p).r + 1
        · subst hr'
          refine reach_invoke (hI.reach ((C.loc p).r + 1)) p (g4.output.1.snoc (C.loc p).cmd) ?_ ?_
          · rw [gst_loc, locAt_gca hph]; simp only [Nat.succ_ne_self, if_false]
            by_contra hc; have := hL.hist_le _ hc; omega
          · simp only [gst, setLoc_mem, setLoc_loc, GCA.State.mk.injEq, true_and]
            funext i
            by_cases hi : i = p
            · subst hi; simp [locAt, Loc.startRound]
            · simp [hi]
        · have hg : gst (setLoc C p { (C.loc p).startRound (C.loc p).r g4.output.1 with
              hist := Function.update (C.loc p).hist (C.loc p).r (some g4) }) r = gst C r :=
            gst_eq_of rfl rfl (fun i => by
              by_cases hi : i = p
              · subst hi; simp only [setLoc_loc, Function.update_self]
                rw [locAt_gca rfl, locAt_gca hph]; simp [hr, hr', Loc.startRound]
              · simp [hi])
          rw [hg]; exact hI.reach r

theorem Inv1.tau_writeS {C : Cfg A n} (hI : Inv1 C) {p : Fin n}
    (hph : (C.loc p).phase = .writeS) (hpn : C.pend p ≠ none) :
    Inv1 (setMemLoc C (.S p) ((C.loc p).r, (C.loc p).s) p { C.loc p with phase := .done }) := by
  have hL := hI.loc p
  constructor
  · intro i
    by_cases hi : i = p
    · subst hi
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [setMemLoc_loc,
        setMemLoc_pend, setMemLoc_mem, Function.update_self, reduceCtorEq]
      · simpa [hph] using hL.pend_iff
      · intro _ _ h; cases h
      · exact hL.hist_le
      · exact hL.hist_pc
      · intro _ h; cases h
      · intro h; cases h
      · intro _ _ h; cases h
      · intro _; trivial
      · intro _ h; cases h
      · intro h; cases h
      · intro _ _ h; cases h
    · exact linv_other (C' := setMemLoc C _ _ p _) hI (by simp) rfl
        (fun i hi => by simp [Function.update_of_ne (show Obj.S i ≠ Obj.S p by simpa using hi)])
        i hi
  · intro r
    have hg : gst (setMemLoc C (.S p) ((C.loc p).r, (C.loc p).s) p
        { C.loc p with phase := .done }) r = gst C r :=
      gst_eq_of (by simp [Function.update_of_ne (show Obj.A r ≠ Obj.S p by simp)])
        (by simp [Function.update_of_ne (show Obj.B r ≠ Obj.S p by simp)]) (fun i => by
          by_cases hi : i = p
          · subst hi; simp only [setMemLoc_loc, Function.update_self]
            rw [locAt_of_not_gca (by simp), locAt_of_not_gca (by simp [hph])]
          · simp [hi])
    rw [hg]; exact hI.reach r

theorem Inv1.step {C C' : Cfg A n} (hI : Inv1 C) {ℓ : Label (Fin n) A}
    (h : (impl (A := A) (n := n)).step C ℓ = some C') : Inv1 C' := by
  cases ℓ with
  | inv p o => exact hI.step_inv h
  | ret p r => exact hI.step_ret h
  | tau p =>
    obtain ⟨hpn, hpend, hT⟩ := step_tau_cases h
    cases hT with
    | readS j best hj hph hlt => exact hI.tau_readS j best hj hph hlt hpn
    | readLast j best hj hph hlt => exact hI.tau_readLast j best hj hph hlt hpn
    | gca0 g hph hpc =>
      refine hI.tau_gca012 (g' := { g with pc := 1 }) hph hpn (by simp) rfl
        (fun i => by simp [Function.update_of_ne (show Obj.S i ≠ Obj.A (C.loc p).r by simp)])
        (by simp) ?_ (fun r hr => by
          simp [Function.update_of_ne (show Obj.A r ≠ Obj.A (C.loc p).r by simpa using hr),
            Function.update_of_ne (show Obj.B r ≠ Obj.A (C.loc p).r by simp)])
      rw [GCA.step_eq_zero hpc]
      simp only [gst, setMemLoc_mem, setMemLoc_loc, Function.update_self, GCA.State.mk.injEq]
      refine ⟨trivial, by simp [Function.update_of_ne (show Obj.B (C.loc p).r ≠ Obj.A (C.loc p).r
        by simp)], ?_⟩
      funext i
      by_cases hi : i = p
      · subst hi; simp [locAt]
      · simp [hi]
    | gca1 g hph hpc =>
      refine hI.tau_gca012 (g' := { g with pc := 2, av := C.mem (.A (C.loc p).r) }) hph hpn
        (by simp) rfl (fun i => rfl) (by simp) ?_ (fun r _ => ⟨rfl, rfl⟩)
      rw [GCA.step_eq_one hpc]
      simp only [gst, setLoc_mem, setLoc_loc, GCA.State.mk.injEq, true_and]
      funext i
      by_cases hi : i = p
      · subst hi; simp [locAt]
      · simp [hi]
    | gca2 g hph hpc =>
      refine hI.tau_gca012 (g' := { g with pc := 3 }) hph hpn (by simp) rfl
        (fun i => by simp [Function.update_of_ne (show Obj.S i ≠ Obj.B (C.loc p).r by simp)])
        (by simp) ?_ (fun r hr => by
          simp [Function.update_of_ne (show Obj.B r ≠ Obj.B (C.loc p).r by simpa using hr),
            Function.update_of_ne (show Obj.A r ≠ Obj.B (C.loc p).r by simp)])
      rw [GCA.step_eq_two hpc]
      simp only [gst, setMemLoc_mem, setMemLoc_loc, Function.update_self, GCA.State.mk.injEq]
      refine ⟨by simp [Function.update_of_ne (show Obj.A (C.loc p).r ≠ Obj.B (C.loc p).r
        by simp)], trivial, ?_⟩
      funext i
      by_cases hi : i = p
      · subst hi; simp [locAt]
      · simp [hi]
    | gca3 g hph hpc => exact hI.tau_gca3 hph hpc hpn
    | writeS hph => exact hI.tau_writeS hph hpn

/-- `Inv1` holds in every reachable configuration. -/
theorem inv1_of_run {α : List (Label (Fin n) A)} {C : Cfg A n}
    (h : (impl (A := A) (n := n)).run α = some C) : Inv1 C :=
  Impl.invariant_of_run inv1_init (fun _ _ _ hI hs => hI.step hs) h

end Alg1

end Podc.ConflictFreedom
