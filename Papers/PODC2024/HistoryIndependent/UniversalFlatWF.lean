import Papers.PODC2024.HistoryIndependent.UniversalFlat

/-!
# Theorem 32: wait-freedom of the flattened implementation

The atomic potential `mu p` of `UniversalWF` measures the progress of process `p`'s operation
at the level of Algorithm 5. In the flattened implementation a step of `p` may be a *stutter*
(a `Read`, a failed `CAS`, or a `Load` of a right-hand side of `∥` that does not end it), which
does not change `mu p`. Every failed `CAS` of `p` on a CAS object `X` is caused by a change of `X`
by another process since `p`'s last `Read`; the paper's Lemmas 29–31, 41 and Claim 33 bound the
number of such changes. We replace them by explicit potentials:

* `G2`: the sum over processes of their atomic potentials (plus a bonus for a linearized
  operation that can still complete). It never increases at steps that are not *transitions*
  (successful `SC`s on `head`), and strictly decreases at every change of the memory that is not
  a transition (Lemmas 29/31: without mode transitions only finitely many context changes
  happen).
* `Sj j`: the "stragglers" of `announce[j]` (processes about to `LL(announce[j])` after reading
  an old `head`) and its context; together with `G2` it bounds the changes of `announce[j]` that
  do not reset its context (Lemma 41).
* `psi`: the local progress of `p` inside an Algorithm 6 operation.

The final potential `Pi p = K · mu p + V p` never increases and strictly decreases at every step
of `p` (while `p`'s operation is pending), which gives wait-freedom.
-/

namespace Cslib.SharedMemory

namespace Universal

open List Finset

variable {A : ObjSpec} {n : ℕ} [DecidablePred A.ReadOnly]

/-- A *transition* (a mode change, the paper's transitions `A_{i-1} → B_i` and `B_i → A_i`): a
successful `SC` on `head` (lines 14, 21, 26). -/
def IsTrans (q : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : Prop :=
  q ∈ hc D.mem ∧ ((∃ j o, (D.loc q).pc = .scApply j o) ∨ (D.loc q).pc = .scHead ∨
    ∃ r, (D.loc q).pc = .clear r)

/-- A transition by `q ≠ p` while `p`'s operation is announced but not cleared strictly
decreases `p`'s atomic potential (in phase 1 it applies an operation or switches back to mode
`A`; phase 2 admits no transition). -/
theorem mu_lt_trans {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {q p : Fin n}
    (hI : InvC L cur C.pend C.mem C.loc) (hqp : q ≠ p)
    (h : (alg5 A n).step C (.tau q) = some C') (ht : IsTrans q C)
    (hact' : (C.loc p).pc.inLoop = true ∧ isOp (av C.mem p) = true) : mu p C' < mu p C := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := fun r hr => by
    rw [hloc]; exact Function.update_of_ne hr _ _
  have hlp := hlr p (Ne.symm hqp)
  have hQ := hI.proc q
  obtain ⟨hin, ⟨j, o', hpc⟩ | hpc | ⟨r, hpc⟩⟩ := ht
  · simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    simp [hin] at hmem hloc
    have hhd := (hQ.ch hin).1
    rw [hhd] at hmem
    have hvn : (hv C.mem).2 = none := by rw [← hhd]; exact hl.1
    have hph : phase p C = 1 := by
      rw [phase_of_loop hact'.1, hact'.2, hvn]; simp [ownerIs]
    apply mu_lt_of_G
    rw [G_of_one hph]
    by_cases hjp : j = p
    · have hph' : phase p C' = 2 := by
        rw [phase_of_loop (by rw [hlp]; exact hact'.1), hmem]; simp [hact'.2, hjp, ownerIs]
      rw [G_of_two hph']; omega
    · have hph' : phase p C' = 1 := by
        rw [phase_of_loop (by rw [hlp]; exact hact'.1), hmem]
        simp [hact'.2, ownerIs, hjp]
      rw [G_of_one hph']
      have hmb : modeBit C' = 1 := by simp [modeBit, hmem]
      have hmb0 : modeBit C = 0 := by simp [modeBit, hvn]
      have hPhi : Phi p C' < Phi p C := by
        refine Phi_lt_all hlr (fun r _ h' => by rw [hmem] at h'; simp at h') ?_
        have hns : ¬ Stale p C' q := fun ⟨_, h2, _⟩ => by rw [hmem] at h2; simp at h2
        have hprio' : (C'.loc q).prio = nextP (C.loc q).prio := by rw [hloc]; simp
        unfold phi; simp only [hns, ↓reduceIte, hprio']
        split_ifs with hs
        · exact dist_lt _ _
        · have hpr : (C.loc q).prio ≠ p := by
            intro e
            rcases hl.2 with e' | e'
            · exact hjp (e'.trans e)
            · exact hs ⟨hqp, hin, e, Or.inr ⟨o', by rw [hpc, e']⟩⟩
          have := dist_nextP p _ hpr; omega
      omega
  · simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    simp [hin] at hmem hloc
    have hhd := (hQ.ch hin).1
    rw [hhd] at hmem
    have hvj : (hv C.mem).2 = some (rsp, (C.loc q).aj) := by rw [← hhd, hrsp]
    have hnotinl : ∀ o, av C.mem (C.loc q).aj ≠ some (.inl o) := by
      by_cases hac : q ∈ ac C.mem (C.loc q).aj
      · rw [hQ.ca1 _ hac rfl]; intro o e
        exact hQ.k4 hpc (by rw [e]; rfl) hac
      · exact hQ.k3 hin (by rw [hpc]; rfl) hac
    have hjp : (C.loc q).aj ≠ p := by
      intro e; obtain ⟨o', ho'⟩ := (isOp_iff _).1 hact'.2
      rw [← e] at ho'; exact hnotinl o' ho'
    have hph : phase p C = 1 := by
      rw [phase_of_loop hact'.1, hact'.2, hvj]; simp [ownerIs, hjp]
    have hph' : phase p C' = 1 := by
      rw [phase_of_loop (by rw [hlp]; exact hact'.1), hmem]; simp [hact'.2, ownerIs]
    exact mu_lt_BA hph hph' (by simp [modeBit, hvj]) (by simp [modeBit, hmem])
      (phi_le_all hlr (fun r _ h' => by rw [hmem] at h'; simp at h')
        (phi_le_of (by rw [hloc]; simp) (fun hs => by
          obtain ⟨-, h2, -⟩ := hs; rw [hmem] at h2; simp at h2)))
  · simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    simp [hin] at hmem hloc
    have hhd := (hQ.ch hin).1
    rw [hhd] at hmem
    have hvj : (hv C.mem).2 = some (rsp, q) := by rw [← hhd, hrsp]
    have hph : phase p C = 1 := by
      rw [phase_of_loop hact'.1, hact'.2, hvj]; simp [ownerIs, hqp]
    have hph' : phase p C' = 1 := by
      rw [phase_of_loop (by rw [hlp]; exact hact'.1), hmem]; simp [hact'.2, ownerIs]
    exact mu_lt_BA hph hph' (by simp [modeBit, hvj]) (by simp [modeBit, hmem])
      (phi_le_all hlr (fun r _ h' => by rw [hmem] at h'; simp at h')
        (phi_le_of (by rw [hloc]; simp) (fun hs => by
          obtain ⟨-, h2, -⟩ := hs; rw [hmem] at h2; simp at h2)))

/-- Jumps (ends of right-hand sides of `∥`) decrease the jumping process's potential. -/
theorem mu_jump_self {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {D : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} {l' : Loc A n}
    (hI : InvC L cur D.pend D.mem D.loc) (hJ : Jump p D l') :
    mu p { D with loc := Function.update D.loc p l' } < mu p D := by
  have hP := hI.proc p
  rcases hJ with ⟨hpc, hr, rfl⟩ | ⟨hpc, hr, rsp, j, hj, rfl⟩ | ⟨r, hpc, hown, rfl⟩
  · have hop : isOp (av D.mem p) = false := by
      obtain ⟨r, hr⟩ := (isResp_iff _).1 hr; rw [hr]; rfl
    have h3 : phase p D = 3 := by
      rw [phase_of_loop (by rw [hpc]; rfl), hop]; rfl
    have h3' : phase p { D with loc := Function.update D.loc p { D.loc p with pc := .resp } } = 3 := by
      unfold phase; simp
    apply mu_lt_three h3 h3'; simp [hpc, pl3, dLoop]
  · have hop : isOp (av D.mem p) = false := by
      obtain ⟨r, hr⟩ := (isResp_iff _).1 hr; rw [hr]; rfl
    have h3 : phase p D = 3 := by
      rw [phase_of_loop (by rw [hpc]; rfl), hop]; rfl
    have h3' : phase p { D with loc := Function.update D.loc p { D.loc p with pc := .rl18 j } } = 3 := by
      unfold phase; simp
    apply mu_lt_three h3 h3'; simp [hpc, pl3, dLoop]
  · have h3 : phase p D = 3 := by unfold phase; rw [hpc]
    have h3' : phase p { D with loc := Function.update D.loc p { D.loc p with pc := .rlHead r } } = 3 := by
      unfold phase; simp
    apply mu_lt_three h3 h3'; simp [hpc, pl3]

omit [DecidablePred A.ReadOnly] in
/-- Jumps of other processes do not increase `p`'s potential. -/
theorem mu_jump_other {D : Config A (B A n) (Fin n) (Loc A n)} {p q : Fin n} {l' : Loc A n}
    (hqp : q ≠ p) (hJ : Jump q D l') :
    mu p { D with loc := Function.update D.loc q l' } ≤ mu p D := by
  have hlr : ∀ r, r ≠ q → (Function.update D.loc q l') r = D.loc r := fun r hr =>
    Function.update_of_ne hr _ _
  refine mu_le_same (C' := { D with loc := Function.update D.loc q l' }) (hlr p (Ne.symm hqp))
    rfl rfl Iff.rfl (fun _ => phi_le_all hlr (fun r _ h' => h') (phi_le_of ?_ ?_))
  · rcases hJ with ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;> simp
  · rcases hJ with ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;>
      rintro ⟨-, -, -, h4⟩ <;> simp at h4

/-! ## The global budget `G2` -/

/-- Process `q`'s operation is linearized (for a process inside a state-changing operation). -/
def linB (q : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : Bool :=
  match (D.loc q).pc with
  | .resp | .llHead2 _ | .clear _ | .rlHead _ | .storeBot _ | .retSC _ | .rl18 _ => true
  | _ => isResp (av D.mem q) || (isOp (av D.mem q) && ownerIs q (hv D.mem).2)

/-- Program counters outside a state-changing operation. -/
def PC.outSC : PC A n → Bool
  | .idle | .ro _ | .roRet _ => true
  | _ => false

omit [DecidablePred A.ReadOnly] in
lemma linB_iff {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {D : Config A (B A n) (Fin n) (Loc A n)} (hI : InvC L cur D.pend D.mem D.loc) (q : Fin n)
    (hq : (D.loc q).pc.outSC = false) :
    linB q D = true ↔ specResp L (cur q) ≠ none := by
  have hP := hI.proc q
  have pinv := hP.pinv
  by_cases hl : (D.loc q).pc.inLoop
  · rw [PInv_loop hl] at pinv
    obtain ⟨o, -, -, ⟨h1, h2⟩ | ⟨r, h1, h2⟩⟩ := pinv
    · have hlin : linB q D = ownerIs q (hv D.mem).2 := by
        unfold linB; rw [h1]
        cases hpc : (D.loc q).pc <;> rw [hpc] at hl <;> simp_all [PC.inLoop, isResp, isOp]
      rw [hlin]
      constructor
      · intro ho e
        revert ho
        rcases hh : (hv D.mem).2 with _ | ⟨rsp, j⟩
        · simp [ownerIs]
        · simp only [ownerIs, decide_eq_true_eq]; rintro rfl
          rw [(hP.h2 rsp hh).1] at e; cases e
      · intro hne
        obtain ⟨rsp, e⟩ := h2 hne
        rw [e]; simp [ownerIs]
    · have : linB q D = true := by
        unfold linB; rw [h1]
        cases hpc : (D.loc q).pc <;> rw [hpc] at hl <;> simp_all [PC.inLoop, isResp]
      rw [this, h2]; simp
  · cases hpc : (D.loc q).pc with
    | idle | ro _ | roRet _ => simp [hpc, PC.outSC] at hq
    | ann o =>
      rw [hpc] at pinv; simp only [linB, hpc, PInv] at pinv ⊢
      rw [pinv.2.2.1, pinv.2.2.2]; simp [isResp, isOp]
    | resp | rl18 _ =>
      rw [hpc] at pinv; obtain ⟨-, r, -, h⟩ := pinv; simp [linB, hpc, h]
    | llHead2 _ | clear _ | rlHead _ | storeBot _ | retSC _ =>
      rw [hpc] at pinv; obtain ⟨-, -, h⟩ := pinv; simp [linB, hpc, h]
    | _ => simp [hpc, PC.inLoop] at hl

/-- The constant bounding the atomic potential. -/
def K0 (n : ℕ) : ℕ := 32 * (2 * n * n + 4) + 21

omit [DecidablePred A.ReadOnly] in
lemma mu_lt_K0 (p : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : mu p D < K0 n := by
  have h1 := pl_le p D
  have h2 : G p D ≤ 2 * n * n + 4 := by
    unfold G
    split
    · exact le_rfl
    · have := Phi_le (p := p) (C := D)
      have : modeBit D ≤ 1 := by unfold modeBit; split <;> omega
      have : 2 * Phi p D ≤ 2 * (n * n) := Nat.mul_le_mul_left 2 ‹_›
      rw [Nat.mul_assoc]; omega
    all_goals omega
  unfold mu K0; omega

/-- The rank of process `q`: its atomic potential, plus `K0` if its operation is linearized (it
may still complete and start a new operation). -/
noncomputable def rank (q : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : ℕ :=
  if (D.loc q).pc.outSC then K0 n else mu q D + (if linB q D then K0 n else 0)

/-- The global budget: the sum of the ranks. -/
noncomputable def G2 (D : Config A (B A n) (Fin n) (Loc A n)) : ℕ := ∑ q, rank q D

omit [DecidablePred A.ReadOnly] in
lemma rank_le (q : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : rank q D ≤ 2 * K0 n := by
  have := mu_lt_K0 q D
  unfold rank; split_ifs <;> omega

omit [DecidablePred A.ReadOnly] in
lemma G2_le (D : Config A (B A n) (Fin n) (Loc A n)) : G2 D ≤ n * (2 * K0 n) := by
  unfold G2
  calc ∑ q, rank q D ≤ ∑ _q : Fin n, 2 * K0 n := Finset.sum_le_sum fun q _ => rank_le q D
    _ = n * (2 * K0 n) := by simp

omit [DecidablePred A.ReadOnly] in
/-- Under the invariant, a process is inside a state-changing operation iff its pending
operation is state-changing. -/
lemma outSC_iff {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {D : Config A (B A n) (Fin n) (Loc A n)} (hI : InvC L cur D.pend D.mem D.loc) (q : Fin n) :
    (D.loc q).pc.outSC = false ↔ ∃ o, D.pend q = some o ∧ ¬ A.ReadOnly o := by
  have pinv := (hI.proc q).pinv
  by_cases hl : (D.loc q).pc.inLoop
  · rw [PInv_loop hl] at pinv
    obtain ⟨o, h1, h2, -⟩ := pinv
    refine ⟨fun _ => ⟨o, h1, h2⟩, fun _ => ?_⟩
    cases hpc : (D.loc q).pc <;> rw [hpc] at hl <;> simp_all [PC.inLoop, PC.outSC]
  · cases hpc : (D.loc q).pc <;> rw [hpc] at pinv <;> simp only [PInv] at pinv <;>
      simp only [PC.outSC, Bool.true_eq_false, false_iff, true_iff, not_exists, not_and]
    all_goals first
      | (simp [hpc, PC.inLoop] at hl; done)
      | (intro o ho; rw [pinv.1] at ho; cases ho; exact fun h => h pinv.2.1; done)
      | (intro o ho; rw [pinv.1] at ho; cases ho; done)
      | (obtain ⟨⟨o', h1, h2⟩, -⟩ := pinv; intro o ho; rw [h1] at ho; cases ho; exact fun h => h h2; done)
      | (obtain ⟨o', h1, h2, -⟩ := pinv; exact ⟨o', h1, h2⟩)
      | (obtain ⟨⟨o', h1, h2⟩, -⟩ := pinv; exact ⟨o', h1, h2⟩)
      | exact ⟨_, pinv.1, pinv.2.1⟩

/-- Non-transition steps do not increase `G2`, and strictly decrease it at steps of processes
inside state-changing operations (in particular at every change of the memory). -/
theorem G2_tau {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    (hcur : ∀ q, (cur q).1 = q) {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.tau q) = some C')
    (hnt : ¬ IsTrans q C) :
    G2 C' ≤ G2 C ∧ ((C.loc q).pc.outSC = false → G2 C' < G2 C) := by
  have hI' := hI.tau hcur h
  obtain ⟨hp, hpend, -⟩ := Impl.step_tau h
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := fun r hr => by
    obtain ⟨-, -, i, o, k, -, -, hloc⟩ := Impl.step_tau h
    rw [hloc]; exact Function.update_of_ne hr _ _
  have cur_ne : ∀ {a b : Fin n}, a ≠ b → cur a ≠ cur b :=
    fun hq e => hq (by have := congrArg Prod.fst e; rwa [hcur, hcur] at this)
  -- the contribution of the step is at most a read-only operation of `q`
  have hM : contribT cur C q = [] ∨ ∃ o, contribT cur C q = [(cur q, o)] ∧ (C.loc q).pc = .ro o := by
    unfold contribT
    split
    · rename_i o hpc; exact Or.inr ⟨o, rfl, hpc⟩
    · rename_i j o hpc
      split_ifs with hin
      · exact absurd ⟨hin, Or.inl ⟨j, o, hpc⟩⟩ hnt
      · exact Or.inl rfl
    · exact Or.inl rfl
  have hspec : ∀ r, ((C.loc q).pc.outSC = false ∨ r ≠ q) →
      specResp (L ++ contribT cur C q) (cur r) = specResp L (cur r) := by
    intro r hr
    apply specRespFrom_append_of_not_mem
    rcases hM with hM | ⟨o, hM, hpc⟩
    · simp [hM]
    · rw [hM]
      rcases hr with hr | hr
      · simp [hpc, PC.outSC] at hr
      · simpa using cur_ne hr
  have hlin : ∀ r, ((C.loc q).pc.outSC = false ∨ r ≠ q) → (C.loc r).pc.outSC = false →
      (C'.loc r).pc.outSC = false → linB r C' = linB r C := by
    intro r hr h1 h2
    have e1 := linB_iff hI' r h2
    have e2 := linB_iff hI r h1
    rw [hspec r hr] at e1
    cases h3 : linB r C' <;> cases h4 : linB r C <;> simp_all
  have hrank : ∀ r, r ≠ q → rank r C' ≤ rank r C := by
    intro r hr
    unfold rank
    rw [hlr r hr]
    by_cases ho : (C.loc r).pc.outSC = true
    · simp [ho]
    · have := mu_tau_other r hI (Ne.symm hr) h
      have hl := hlin r (Or.inr hr) (by simpa using ho) (by rw [hlr r hr]; simpa using ho)
      simp only [ho, Bool.false_eq_true, ↓reduceIte, hl]; omega
  have hq' : (C.loc q).pc.outSC = false → (C'.loc q).pc.outSC = false := by
    intro ho
    rw [outSC_iff hI q] at ho
    rw [outSC_iff hI' q, hpend]; exact ho
  have hrankq : rank q C' ≤ rank q C ∧ ((C.loc q).pc.outSC = false → rank q C' < rank q C) := by
    by_cases ho : (C.loc q).pc.outSC = false
    · have ho' := hq' ho
      have := mu_tau_self q hI h
      have hl := hlin q (Or.inl ho) ho ho'
      unfold rank
      simp only [ho, ho', Bool.false_eq_true, ↓reduceIte, hl]
      exact ⟨by omega, fun _ => by omega⟩
    · have ho1 : (C.loc q).pc.outSC = true := by simpa using ho
      have ho2 : (C'.loc q).pc.outSC = true := by
        by_contra hc
        have := (outSC_iff hI' q).1 (by simpa using hc)
        rw [hpend] at this
        exact ho ((outSC_iff hI q).2 this)
      unfold rank
      rw [if_pos ho1, if_pos ho2]
      exact ⟨le_rfl, fun h => absurd h ho⟩
  unfold G2
  constructor
  · refine Finset.sum_le_sum fun r _ => ?_
    by_cases hr : r = q
    · subst hr; exact hrankq.1
    · exact hrank r hr
  · intro ho
    refine Finset.sum_lt_sum (fun r _ => ?_) ⟨q, Finset.mem_univ _, hrankq.2 ho⟩
    by_cases hr : r = q
    · subst hr; exact hrankq.1
    · exact hrank r hr

omit [DecidablePred A.ReadOnly] in
lemma rank_other {D D' : Config A (B A n) (Fin n) (Loc A n)} {r : Fin n}
    (hl : D'.loc r = D.loc r) (hm : D'.mem = D.mem) (hmu : mu r D' ≤ mu r D) :
    rank r D' ≤ rank r D := by
  have hlin : linB r D' = linB r D := by unfold linB; rw [hl, hm]
  unfold rank; rw [hl, hlin]; split_ifs <;> omega

/-- Jumps do not increase `G2`. -/
theorem G2_jump {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {D : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} {l' : Loc A n}
    (hI : InvC L cur D.pend D.mem D.loc) (hJ : Jump q D l') :
    G2 { D with loc := Function.update D.loc q l' } ≤ G2 D := by
  unfold G2
  refine Finset.sum_le_sum fun r _ => ?_
  by_cases hr : r = q
  · subst hr
    have hmu := mu_jump_self hI hJ
    unfold rank linB
    rcases hJ with ⟨hpc, hres, rfl⟩ | ⟨hpc, hres, rsp, j, hj, rfl⟩ | ⟨r', hpc, hown, rfl⟩ <;>
      simp_all [PC.outSC] <;> omega
  · exact rank_other (by simp [Function.update_of_ne hr]) rfl (mu_jump_other (Ne.symm hr) hJ)

/-- Invocations do not increase `G2`. -/
theorem G2_inv {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} {o : A.Op}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.inv q o) = some C') :
    G2 C' ≤ G2 C := by
  obtain ⟨hp, -, -, hloc, hmem⟩ := Impl.step_inv h
  unfold G2
  refine Finset.sum_le_sum fun r _ => ?_
  by_cases hr : r = q
  · subst hr
    have pinv := (hI.proc r).pinv
    have hidle : (C.loc r).pc = .idle := by
      revert pinv; cases (C.loc r).pc <;> simp_all [PInv]
    rw [hidle] at pinv
    have := mu_lt_K0 r C'
    unfold rank linB
    rw [hloc, hmem, hidle]
    simp only [Function.update_self, alg5, PC.outSC, ↓reduceIte]
    have hav : av C.mem r = none := pinv.2
    by_cases hro : A.ReadOnly o
    · simp [hro]
    · simp only [hro, ↓reduceIte, hav]; simp [isResp, isOp]; omega
  · exact rank_other (by rw [hloc]; exact Function.update_of_ne hr _ _) hmem (mu_inv_other r (Ne.symm hr) h)

/-- Responses do not increase `G2`. -/
theorem G2_ret {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} {r : A.Resp}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.ret q r) = some C') :
    G2 C' ≤ G2 C := by
  obtain ⟨hp, -, hmem, l, hact, hloc⟩ := Impl.step_ret h
  unfold G2
  refine Finset.sum_le_sum fun r' _ => ?_
  by_cases hr : r' = q
  · subst hr
    have hl : (C'.loc r').pc = .idle ∧ ((C.loc r').pc.outSC = true ∨ linB r' C = true) := by
      rw [hloc]; simp only [Function.update_self]
      simp only [alg5, act] at hact
      split at hact <;> (try split at hact) <;> cases hact <;> simp [PC.outSC, linB, *]
    unfold rank
    have hi : (PC.idle : PC A n).outSC = true := rfl
    rw [hl.1, if_pos hi]
    rcases hl.2 with h1 | h1
    · rw [if_pos h1]
    · split_ifs with h2 h3 <;> first | omega | exact absurd h1 h3
  · exact rank_other (by rw [hloc]; exact Function.update_of_ne hr _ _) hmem (mu_ret_other r' (Ne.symm hr) h)

/-! ## Stragglers of `announce[j]` -/

/-- `l` is about to perform `LL(announce[j])` (line 18L). -/
def strag (j : Fin n) (l : Loc A n) : Bool :=
  match l.pc, l.hd.2 with
  | .llAnn, some (_, k) => decide (k = j)
  | _, _ => false

/-- The straggler budget of `announce[j]`: twice the number of processes about to
`LL(announce[j])`, plus the size of its context. -/
def Sj (j : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : ℕ :=
  ∑ r, (2 * (if strag j (D.loc r) then 1 else 0) + (if r ∈ ac D.mem j then 1 else 0))

omit [DecidablePred A.ReadOnly] in
lemma Sj_le (j : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : Sj j D ≤ n * 3 := by
  unfold Sj
  calc ∑ r, (2 * (if strag j (D.loc r) then 1 else 0) + (if r ∈ ac D.mem j then 1 else 0))
      ≤ ∑ _r : Fin n, 3 := Finset.sum_le_sum fun r _ => by split_ifs <;> omega
    _ = n * 3 := by simp

omit [DecidablePred A.ReadOnly] in
/-- Comparing `Sj` when only process `q`'s term may change. -/
lemma Sj_cmp {D D' : Config A (B A n) (Fin n) (Loc A n)} {j q : Fin n}
    (hl : ∀ r, r ≠ q → D'.loc r = D.loc r) (hm : ∀ r, r ≠ q → (r ∈ ac D'.mem j ↔ r ∈ ac D.mem j))
    (hq : 2 * (if strag j (D'.loc q) then 1 else 0) + (if q ∈ ac D'.mem j then 1 else 0) ≤
      2 * (if strag j (D.loc q) then 1 else 0) + (if q ∈ ac D.mem j then 1 else 0)) :
    Sj j D' ≤ Sj j D ∧
    (2 * (if strag j (D'.loc q) then 1 else 0) + (if q ∈ ac D'.mem j then 1 else 0) <
      2 * (if strag j (D.loc q) then 1 else 0) + (if q ∈ ac D.mem j then 1 else 0) →
      Sj j D' < Sj j D) := by
  have hle : ∀ r ∈ (Finset.univ : Finset (Fin n)),
      2 * (if strag j (D'.loc r) then 1 else 0) + (if r ∈ ac D'.mem j then 1 else 0) ≤
      2 * (if strag j (D.loc r) then 1 else 0) + (if r ∈ ac D.mem j then 1 else 0) := by
    intro r _
    by_cases hr : r = q
    · subst hr; exact hq
    · rw [hl r hr]; simp only [hm r hr]; exact le_rfl
  exact ⟨Finset.sum_le_sum hle, fun h => Finset.sum_lt_sum hle ⟨q, Finset.mem_univ _, h⟩⟩

omit [DecidablePred A.ReadOnly] in
lemma Sj_untouched {D D' : Config A (B A n) (Fin n) (Loc A n)} {j q : Fin n}
    (hl : ∀ r, r ≠ q → D'.loc r = D.loc r) (hm : D'.mem (.ann j) = D.mem (.ann j))
    (hs : strag j (D'.loc q) = false) :
    ac D'.mem j = ∅ ∨ (av D'.mem j = av D.mem j ∧ Sj j D' ≤ Sj j D ∧
      (ac D'.mem j ≠ ac D.mem j → Sj j D' < Sj j D)) := by
  have ha : av D'.mem j = av D.mem j := by simp only [av, hm]
  have hc : ac D'.mem j = ac D.mem j := by simp only [ac, hm]
  refine Or.inr ⟨ha, (Sj_cmp hl (fun r _ => by rw [hc]) ?_).1, fun h => absurd hc h⟩
  rw [hs, hc]; simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> omega

/-- `Sj` under non-transition steps while `head` is not owned by `j`: either the context of
`announce[j]` is reset, or its value is unchanged, `Sj` does not increase, and it strictly
decreases when the context changes. -/
theorem Sj_tau {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.tau q) = some C')
    (hnt : ¬ IsTrans q C) (j : Fin n) (hown : ownerIs j (hv C.mem).2 = false) :
    ac C'.mem j = ∅ ∨ (av C'.mem j = av C.mem j ∧ Sj j C' ≤ Sj j C ∧
      (ac C'.mem j ≠ ac C.mem j → Sj j C' < Sj j C)) := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := fun r hr => by
    rw [hloc]; exact Function.update_of_ne hr _ _
  have hQ := hI.proc q
  cases hpc : (C.loc q).pc with
  | idle => have := hQ.pinv; rw [hpc] at this; exact absurd this.1 hp
  | roRet r => simp only [alg5, act, hpc] at hact; cases hact
  | retSC r => simp only [alg5, act, hpc] at hact; cases hact
  | ro o' =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp [strag])
  | loop =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp; split <;> simp [strag])
  | help =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp; split <;> simp [strag])
  | own =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp; split <;> simp [strag])
  | resp =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp; split <;> simp [strag, hpc])
  | vl =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp; split <;> split_ifs <;> simp [strag])
  | ann o' =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    by_cases hj : j = q
    · subst hj; left; rw [hmem]; simp
    · exact Sj_untouched hlr (by rw [hmem]; simp [Function.update_of_ne (show Obj.ann j ≠ .ann q by simpa using hj)])
        (by rw [hloc]; simp [strag])
  | storeBot r =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    by_cases hj : j = q
    · subst hj; left; rw [hmem]; simp
    · exact Sj_untouched hlr (by rw [hmem]; simp [Function.update_of_ne (show Obj.ann j ≠ .ann q by simpa using hj)])
        (by rw [hloc]; simp [strag])
  | llHead =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    refine Sj_untouched hlr (by rw [hmem]; simp) ?_
    rw [hloc]; simp only [Function.update_self]
    split_ifs with hn
    · simp [strag]
    · simp only [strag]
      rcases e : (hv C.mem).2 with _ | ⟨rsp, k'⟩
      · simp
      · simp only [decide_eq_false_iff_not]
        rintro rfl; rw [e] at hown; simp [ownerIs] at hown
  | scApply j' o' =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hin : q ∉ hc C.mem := fun hin => hnt ⟨hin, Or.inl ⟨j', o', hpc⟩⟩
    simp [hin] at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp [strag])
  | scHead =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hin : q ∉ hc C.mem := fun hin => hnt ⟨hin, Or.inr (Or.inl hpc)⟩
    simp [hin] at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp; split_ifs <;> simp [strag])
  | clear r =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hin : q ∉ hc C.mem := fun hin => hnt ⟨hin, Or.inr (Or.inr ⟨r, hpc⟩)⟩
    simp [hin] at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp [strag])
  | llHead2 r =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    refine Sj_untouched hlr (by rw [hmem]; simp) ?_
    rw [hloc]; simp only [Function.update_self]
    by_cases hcl : ownerIs q (hv C.mem).2 = true <;> simp [hcl, strag]
  | rlHead r =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    exact Sj_untouched hlr (by rw [hmem]; simp) (by rw [hloc]; simp [strag])
  | llAnn =>
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, k'⟩, hk⟩ := Option.isSome_iff_exists.1 hl
    simp only [alg5, act, hpc, hk] at hact; cases hact; simp at hmem hloc
    by_cases hj : k' = j
    · subst hj
      right
      refine ⟨by rw [hmem]; simp, ?_⟩
      have hs : strag k' (C.loc q) = true := by simp [strag, hpc, hk]
      have := Sj_cmp (j := k') (q := q) hlr (fun r hr => by rw [hmem]; simp [hr])
        (by rw [hloc, hmem, hs]; simp [strag]; split_ifs <;> omega)
      refine ⟨this.1, fun _ => this.2 ?_⟩
      rw [hloc, hmem, hs]; simp [strag]; split_ifs <;> omega
    · exact Sj_untouched hlr (by rw [hmem]; simp [Function.update_of_ne (show Obj.ann j ≠ .ann k' by simpa using Ne.symm hj)])
        (by rw [hloc]; simp [strag])
  | scAnn =>
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, hrsp⟩, hop⟩ := hl
    simp only [alg5, act, hpc, hrsp] at hact; cases hact
    by_cases hin : q ∈ ac C.mem (C.loc q).aj
    · simp [hin] at hmem hloc
      by_cases hj : (C.loc q).aj = j
      · left; rw [hmem, ← hj]; simp
      · exact Sj_untouched hlr (by rw [hmem]; simp [Function.update_of_ne (show Obj.ann j ≠ .ann (C.loc q).aj by simpa using Ne.symm hj)])
          (by rw [hloc]; simp [strag])
    · simp [hin] at hmem hloc
      exact Sj_untouched hlr (by rw [hmem]) (by rw [hloc]; simp [strag])
  | rlAnn =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    by_cases hj : (C.loc q).aj = j
    · right
      refine ⟨by rw [hmem, ← hj]; simp, ?_⟩
      have hs : strag j (C'.loc q) = false := by rw [hloc]; simp [strag]
      have hs0 : strag j (C.loc q) = false := by simp [strag, hpc]
      have := Sj_cmp (j := j) (q := q) hlr (fun r hr => by rw [hmem, ← hj]; simp [hr])
        (by rw [hs, hs0, hmem, ← hj]; simp)
      refine ⟨this.1, fun hne => this.2 ?_⟩
      have hq : q ∈ ac C.mem j := by
        by_contra hq; apply hne; rw [hmem, ← hj]; simp [Finset.erase_eq_of_notMem (hj ▸ hq)]
      rw [hs, hs0, hmem, ← hj]; simp [hj ▸ hq]
    · exact Sj_untouched hlr (by rw [hmem]; simp [Function.update_of_ne (show Obj.ann j ≠ .ann (C.loc q).aj by simpa using Ne.symm hj)])
        (by rw [hloc]; simp [strag])
  | rl18 j' =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    by_cases hj : j' = j
    · subst hj
      right
      refine ⟨by rw [hmem]; simp, ?_⟩
      have hs : strag j' (C'.loc q) = false := by rw [hloc]; simp [strag]
      have hs0 : strag j' (C.loc q) = false := by simp [strag, hpc]
      have := Sj_cmp (j := j') (q := q) hlr (fun r hr => by rw [hmem]; simp [hr])
        (by rw [hs, hs0, hmem]; simp)
      refine ⟨this.1, fun hne => this.2 ?_⟩
      have hq : q ∈ ac C.mem j' := by
        by_contra hq; apply hne; rw [hmem]; simp [Finset.erase_eq_of_notMem hq]
      rw [hs, hs0, hmem]; simp [hq]
    · exact Sj_untouched hlr (by rw [hmem]; simp [Function.update_of_ne (show Obj.ann j ≠ .ann j' by simpa using Ne.symm hj)])
        (by rw [hloc]; simp [strag])

omit [DecidablePred A.ReadOnly] in
lemma Sj_le_of {D D' : Config A (B A n) (Fin n) (Loc A n)} {j q : Fin n}
    (hl : ∀ r, r ≠ q → D'.loc r = D.loc r) (hm : D'.mem (.ann j) = D.mem (.ann j))
    (hs : strag j (D'.loc q) = false) : Sj j D' ≤ Sj j D := by
  have hc : ac D'.mem j = ac D.mem j := by simp only [ac, hm]
  refine (Sj_cmp hl (fun r _ => by rw [hc]) ?_).1
  rw [hs, hc]; simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> omega

/-- Transitions do not change `announce[j]` and create no stragglers. -/
theorem Sj_trans {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} (j : Fin n)
    (h : (alg5 A n).step C (.tau q) = some C') (ht : IsTrans q C) : Sj j C' ≤ Sj j C := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := fun r hr => by
    rw [hloc]; exact Function.update_of_ne hr _ _
  obtain ⟨hin, ⟨j', o', hpc⟩ | hpc | ⟨r, hpc⟩⟩ := ht
  · simp only [alg5, act, hpc] at hact; cases hact; simp [hin] at hmem hloc
    exact Sj_le_of hlr (by rw [hmem]; simp) (by rw [hloc]; simp [strag])
  · simp only [alg5, act, hpc] at hact; cases hact; simp [hin] at hmem hloc
    exact Sj_le_of hlr (by rw [hmem]; simp) (by rw [hloc]; simp; split_ifs <;> simp [strag])
  · simp only [alg5, act, hpc] at hact; cases hact; simp [hin] at hmem hloc
    exact Sj_le_of hlr (by rw [hmem]; simp) (by rw [hloc]; simp [strag])

omit [DecidablePred A.ReadOnly] in
theorem Sj_jump {D : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} {l' : Loc A n} (j : Fin n)
    (hJ : Jump q D l') : Sj j { D with loc := Function.update D.loc q l' } ≤ Sj j D :=
  Sj_le_of (fun r hr => Function.update_of_ne hr _ _) rfl (by
    simp only [Function.update_self]
    rcases hJ with ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;> simp [strag])

theorem Sj_inv {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} {o : A.Op} (j : Fin n)
    (h : (alg5 A n).step C (.inv q o) = some C') : Sj j C' ≤ Sj j C := by
  obtain ⟨-, -, -, hloc, hmem⟩ := Impl.step_inv h
  exact Sj_le_of (fun r hr => by rw [hloc]; exact Function.update_of_ne hr _ _) (by rw [hmem])
    (by rw [hloc]; simp only [Function.update_self, alg5]; split_ifs <;> simp [strag])

theorem Sj_ret {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} {r : A.Resp} (j : Fin n)
    (h : (alg5 A n).step C (.ret q r) = some C') : Sj j C' ≤ Sj j C := by
  obtain ⟨-, -, hmem, l, hact, hloc⟩ := Impl.step_ret h
  refine Sj_le_of (fun r hr => by rw [hloc]; exact Function.update_of_ne hr _ _) (by rw [hmem]) ?_
  rw [hloc]; simp only [Function.update_self]
  simp only [alg5, act] at hact
  split at hact <;> (try split at hact) <;> cases hact <;> simp [strag]

/-! ## Local progress inside an Algorithm 6 operation -/

section Local

variable {V : Type}

/-- Algorithm 6's guard before the `CAS` of `op` (the loop condition `cur.context[i] = 1` of
`SC` and `RL`; always true for `LL`). -/
def grd : RLLSCOp (Fin n) V → V × Finset (Fin n) → Prop
  | .sc q _, cur => q ∈ cur.2
  | .rl q, cur => q ∈ cur.2
  | _, _ => True

instance (o : RLLSCOp (Fin n) V) (c : V × Finset (Fin n)) : Decidable (grd o c) := by
  cases o <;> simp only [grd] <;> infer_instance

/-- `o` is an `LL`. -/
def isLL : RLLSCOp (Fin n) V → Bool
  | .ll _ => true
  | _ => false

open Classical in
/-- Local potential of an Algorithm 6 operation `o` whose CAS object currently holds `s`:
a pending `CAS` with an up-to-date `cur` (`1`, it succeeds), a pending `Read` (`2`), a pending
`CAS` with an outdated `cur` (`3`, it fails); plus the turn of `∥`. -/
noncomputable def psiOp (o : RLLSCOp (Fin n) V) (st turn : Bool) (cur s : V × Finset (Fin n)) :
    ℕ :=
  2 * (if st ∧ grd o cur then (if s = cur then 1 else 3) else 2) + (if turn then 1 else 0)

lemma psiOp_le (o : RLLSCOp (Fin n) V) (st turn : Bool) (cur s : V × Finset (Fin n)) :
    psiOp o st turn cur s ≤ 7 := by
  unfold psiOp; split_ifs <;> omega

lemma psiOp_change (o : RLLSCOp (Fin n) V) (st turn : Bool) (cur s s' : V × Finset (Fin n)) :
    psiOp o st turn cur s' ≤ psiOp o st turn cur s + 4 := by
  unfold psiOp; split_ifs <;> omega

set_option hygiene false in
/-- Proof of the stutter lemmas (shared by `head` and `announce[j]`). -/
local macro "stutter_tac" getC:ident : tactic => `(tactic| (
  intro fl'
  cases o with
  | load => exact absurd (by simp [stepOp]) hne
  | store v => exact absurd (by simp [stepOp]) hne
  | vl q => exact absurd (by simp [stepOp]) hne
  | ll q =>
    have ht := hturn rfl
    by_cases hs : fl.st = true
    · by_cases he : s = $getC fl
      · exact absurd (by subst he; simp [stepOp, hs]) hne
      · simp only [fl', stepOp, hs, ↓reduceIte, he]
        simp [psiOp, grd, hs, he, ht, setCurH, setCurA, getCH, getCA]
    · simp only [fl', stepOp, hs, Bool.false_eq_true, ↓reduceIte]
      simp [psiOp, grd, hs, ht, setCurH, setCurA, getCH, getCA]
  | sc q v =>
    by_cases hs : fl.st = true ∧ q ∈ ($getC fl).2
    · by_cases he : s = $getC fl
      · exact absurd (by subst he; simp [stepOp, hs]) hne
      · simp only [fl', stepOp, hs, and_self, ↓reduceIte, he]
        simp [psiOp, grd, hs, he, setCurH, setCurA, getCH, getCA, isLL]
    · by_cases hq : q ∈ s.2
      · simp only [fl', stepOp, hs, ↓reduceIte, hq]
        simp only [psiOp, grd, setCurH, setCurA, getCH, getCA] at hs ⊢
        simp only [hq, hs]
        by_cases ht : fl.turn = true <;> simp [ht, isLL]
      · exact absurd (by simp [stepOp, hs, hq]) hne
  | rl q =>
    by_cases hs : fl.st = true ∧ q ∈ ($getC fl).2
    · by_cases he : s = $getC fl
      · exact absurd (by subst he; simp [stepOp, hs]) hne
      · simp only [fl', stepOp, hs, and_self, ↓reduceIte, he]
        simp [psiOp, grd, hs, he, setCurH, setCurA, getCH, getCA, isLL]
    · by_cases hq : q ∈ s.2
      · simp only [fl', stepOp, hs, ↓reduceIte, hq]
        simp only [psiOp, grd, setCurH, setCurA, getCH, getCA] at hs ⊢
        simp only [hq, hs]
        by_cases ht : fl.turn = true <;> simp [ht, isLL]
      · exact absurd (by simp [stepOp, hs, hq, Finset.erase_eq_of_notMem hq]) hne))

/-- `cur` of `head`. -/
abbrev getCH (fl : FLoc A n) : HeadVal A n × Finset (Fin n) := fl.curH
/-- `cur` of `announce`. -/
abbrev getCA (fl : FLoc A n) : AnnVal A × Finset (Fin n) := fl.curA

set_option hygiene false in
/-- Statement of the stutter lemmas. -/
local macro "stutter_stmt" V:term "," getC:ident "," setC:ident : term => `(
  ∀ (o : RLLSCOp (Fin n) $V) (k : $V ⊕ Bool → Loc A n) (fl : FLoc A n),
    (isLL o = true → fl.turn = false) → ∀ (v₀ s : $V × Finset (Fin n)) (w₀ : $V),
    ¬ (((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).1 =
        ((rllsc (Fin n) $V w₀).δ s o).1 ∧
      ((stepOp o k fl ($getC fl) $setC).2
        ((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).2).l5 =
        k ((rllsc (Fin n) $V w₀).δ s o).2) →
    let fl' := (stepOp o k fl ($getC fl) $setC).2
        ((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).2
    ((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).1 = s ∧
      fl'.l5 = fl.l5 ∧
      psiOp o fl'.st fl'.turn ($getC fl') s < psiOp o fl.st fl.turn ($getC fl) s ∧
      (fl'.st = true → grd o ($getC fl')) ∧
      (fl.st = true ∧ grd o ($getC fl) → fl'.st = false) ∧
      (isLL o = true → fl'.turn = true) ∧
      (fl'.st = true → $getC fl' = s) ∧
      (¬ (fl.st = true ∧ grd o ($getC fl)) → fl'.st = true))

set_option hygiene false in
/-- Effective or stutter (statement). -/
local macro "cases_stmt" V:term "," getC:ident "," setC:ident : term => `(
  ∀ (o : RLLSCOp (Fin n) $V) (k : $V ⊕ Bool → Loc A n) (fl : FLoc A n),
    (isLL o = true → fl.turn = false) → ∀ (v₀ s : $V × Finset (Fin n)) (w₀ : $V),
    (((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).1 =
        ((rllsc (Fin n) $V w₀).δ s o).1 ∧
      ((stepOp o k fl ($getC fl) $setC).2
        ((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).2).l5 =
        k ((rllsc (Fin n) $V w₀).δ s o).2) ∨
    (¬ (((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).1 =
        ((rllsc (Fin n) $V w₀).δ s o).1 ∧
      ((stepOp o k fl ($getC fl) $setC).2
        ((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).2).l5 =
        k ((rllsc (Fin n) $V w₀).δ s o).2) ∧
    let fl' := (stepOp o k fl ($getC fl) $setC).2
        ((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).2
    ((casC ($V × Finset (Fin n)) v₀).δ s (stepOp o k fl ($getC fl) $setC).1).1 = s ∧
      fl'.l5 = fl.l5 ∧
      psiOp o fl'.st fl'.turn ($getC fl') s < psiOp o fl.st fl.turn ($getC fl) s ∧
      (fl'.st = true → grd o ($getC fl')) ∧
      (fl.st = true ∧ grd o ($getC fl) → fl'.st = false) ∧
      (isLL o = true → fl'.turn = true) ∧
      (fl'.st = true → $getC fl' = s) ∧
      (¬ (fl.st = true ∧ grd o ($getC fl)) → fl'.st = true)))

/-- **Stutter steps of Algorithm 6** on `head`: a step that is not the linearization point of
the operation is a `Read` (followed by a `CAS` with up-to-date `cur`) or a failed `CAS`
(followed by a `Read`); in both cases the local potential decreases. -/
lemma stepOp_stutterH : stutter_stmt (HeadVal A n), getCH, setCurH := by
  intro o k fl hturn v₀ s w₀ hne
  stutter_tac getCH

/-- **Stutter steps of Algorithm 6** on `announce[j]`. -/
lemma stepOp_stutterA : stutter_stmt (AnnVal A), getCA, setCurA := by
  intro o k fl hturn v₀ s w₀ hne
  stutter_tac getCA

lemma stepOp_casesH : cases_stmt (HeadVal A n), getCH, setCurH := by
  intro o k fl hturn v₀ s w₀
  by_cases h : ((casC (HeadVal A n × Finset (Fin n)) v₀).δ s (stepOp o k fl (getCH fl) setCurH).1).1 =
        ((rllsc (Fin n) (HeadVal A n) w₀).δ s o).1 ∧
      ((stepOp o k fl (getCH fl) setCurH).2
        ((casC (HeadVal A n × Finset (Fin n)) v₀).δ s (stepOp o k fl (getCH fl) setCurH).1).2).l5 =
        k ((rllsc (Fin n) (HeadVal A n) w₀).δ s o).2
  · exact Or.inl h
  · exact Or.inr ⟨h, stepOp_stutterH o k fl hturn v₀ s w₀ h⟩

lemma stepOp_casesA : cases_stmt (AnnVal A), getCA, setCurA := by
  intro o k fl hturn v₀ s w₀
  by_cases h : ((casC (AnnVal A × Finset (Fin n)) v₀).δ s (stepOp o k fl (getCA fl) setCurA).1).1 =
        ((rllsc (Fin n) (AnnVal A) w₀).δ s o).1 ∧
      ((stepOp o k fl (getCA fl) setCurA).2
        ((casC (AnnVal A × Finset (Fin n)) v₀).δ s (stepOp o k fl (getCA fl) setCurA).1).2).l5 =
        k ((rllsc (Fin n) (AnnVal A) w₀).δ s o).2
  · exact Or.inl h
  · exact Or.inr ⟨h, stepOp_stutterA o k fl hturn v₀ s w₀ h⟩

end Local

/-! ## Effects of a step on the shared objects -/

/-- What a step of `q` can do to the memory. -/
structure StepFacts (q : Fin n) (C C' : Config A (B A n) (Fin n) (Loc A n)) : Prop where
  hvSame : ¬ IsTrans q C → hv C'.mem = hv C.mem
  hcSub : ∀ r, r ≠ q → r ∈ hc C'.mem → r ∈ hc C.mem
  hcSup : ¬ IsTrans q C → ∀ r, r ≠ q → r ∈ hc C.mem → r ∈ hc C'.mem
  acSub : ∀ r, r ≠ q → ∀ j, r ∈ ac C'.mem j → r ∈ ac C.mem j
  avOp : ∀ r, r ≠ q → isOp (av C'.mem r) = true → isOp (av C.mem r) = true
  memRO : C'.mem ≠ C.mem → (C.loc q).pc.outSC = false
  transAnn : IsTrans q C → ∀ j, C'.mem (.ann j) = C.mem (.ann j)
  transHc : IsTrans q C → hc C'.mem = ∅
  transOwner : IsTrans q C → ∀ j,
    (ownerIs j (hv C'.mem).2 = true → ownerIs j (hv C.mem).2 = false ∧ isOp (av C.mem j) = true) ∧
    (ownerIs j (hv C.mem).2 = true → ownerIs j (hv C'.mem).2 = false ∧ isOp (av C.mem j) = false)

omit [DecidablePred A.ReadOnly] in
lemma StepFacts.of_same {q : Fin n} {C C' : Config A (B A n) (Fin n) (Loc A n)}
    (hm : C'.mem = C.mem) (hnt : ¬ IsTrans q C) : StepFacts q C C' where
  hvSame _ := by rw [hm]
  hcSub _ _ h := by rwa [hm] at h
  hcSup _ _ _ h := by rwa [hm]
  acSub _ _ _ h := by rwa [hm] at h
  avOp _ _ h := by rwa [hm] at h
  memRO h := absurd hm h
  transAnn h := absurd h hnt
  transHc h := absurd h hnt
  transOwner h := absurd h hnt

theorem stepFacts {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.tau q) = some C') :
    StepFacts q C C' := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  have hQ := hI.proc q
  have notT : ∀ pc : PC A n, (C.loc q).pc = pc → (∀ j o, pc ≠ .scApply j o) → pc ≠ .scHead →
      (∀ r, pc ≠ .clear r) → ¬ IsTrans q C := by
    rintro pc hpc h1 h2 h3 ⟨-, ⟨j, o, e⟩ | e | ⟨r, e⟩⟩ <;> rw [hpc] at e
    · exact h1 j o e
    · exact h2 e
    · exact h3 r e
  cases hpc : (C.loc q).pc with
  | idle => have := hQ.pinv; rw [hpc] at this; exact absurd this.1 hp
  | roRet r => simp only [alg5, act, hpc] at hact; cases hact
  | retSC r => simp only [alg5, act, hpc] at hact; cases hact
  | ro o' =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem
    exact StepFacts.of_same hmem (notT _ hpc (by simp) (by simp) (by simp))
  | loop | help | own | resp | vl =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem
    exact StepFacts.of_same hmem (notT _ hpc (by simp) (by simp) (by simp))
  | llHead | llHead2 _ | rlHead _ =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem
    have hnt := notT _ hpc (by simp) (by simp) (by simp)
    exact ⟨fun _ => by rw [hmem]; simp, fun r hr h' => by rw [hmem] at h'; simpa [hr] using h',
      fun _ r hr h' => by rw [hmem]; simp [hr, h'], fun r _ j h' => by rwa [hmem] at h',
      fun r _ h' => by rwa [hmem] at h', fun _ => by rw [hpc]; rfl,
      fun h => absurd h hnt, fun h => absurd h hnt, fun h => absurd h hnt⟩
  | ann o' | storeBot _ =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem
    have hnt := notT _ hpc (by simp) (by simp) (by simp)
    exact ⟨fun _ => by rw [hmem]; simp, fun r hr h' => by rwa [hmem] at h',
      fun _ r hr h' => by rwa [hmem], fun r _ j h' => by
        rw [hmem, ac_update_ann] at h'; split_ifs at h' <;> simp_all,
      fun r hr h' => by rwa [hmem, av_update_ann_ne _ hr] at h', fun _ => by rw [hpc]; rfl,
      fun h => absurd h hnt, fun h => absurd h hnt, fun h => absurd h hnt⟩
  | rlAnn =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem
    have hnt := notT _ hpc (by simp) (by simp) (by simp)
    exact ⟨fun _ => by rw [hmem]; simp, fun r hr h' => by rwa [hmem] at h',
      fun _ r hr h' => by rwa [hmem], fun r hr j h' => by
        rw [hmem, ac_update_ann] at h'; split_ifs at h' with e
        · subst e; simp at h'; exact h'.2
        · exact h',
      fun r hr h' => by rw [hmem] at h'; simpa using h', fun _ => by rw [hpc]; rfl,
      fun h => absurd h hnt, fun h => absurd h hnt, fun h => absurd h hnt⟩
  | rl18 j' =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem
    have hnt := notT _ hpc (by simp) (by simp) (by simp)
    exact ⟨fun _ => by rw [hmem]; simp, fun r hr h' => by rwa [hmem] at h',
      fun _ r hr h' => by rwa [hmem], fun r hr j h' => by
        rw [hmem, ac_update_ann] at h'; split_ifs at h' with e
        · subst e; simp at h'; exact h'.2
        · exact h',
      fun r hr h' => by rw [hmem] at h'; simpa using h', fun _ => by rw [hpc]; rfl,
      fun h => absurd h hnt, fun h => absurd h hnt, fun h => absurd h hnt⟩
  | llAnn =>
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, k'⟩, hk⟩ := Option.isSome_iff_exists.1 hl
    simp only [alg5, act, hpc, hk] at hact; cases hact; simp at hmem
    have hnt := notT _ hpc (by simp) (by simp) (by simp)
    exact ⟨fun _ => by rw [hmem]; simp, fun r hr h' => by rwa [hmem] at h',
      fun _ r hr h' => by rwa [hmem], fun r hr j h' => by
        rw [hmem, ac_update_ann] at h'; split_ifs at h' with e
        · subst e; simpa [hr] using h'
        · exact h',
      fun r hr h' => by rw [hmem] at h'; simpa using h', fun _ => by rw [hpc]; rfl,
      fun h => absurd h hnt, fun h => absurd h hnt, fun h => absurd h hnt⟩
  | scAnn =>
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, hrsp⟩, hop⟩ := hl
    simp only [alg5, act, hpc, hrsp] at hact; cases hact
    have hnt := notT _ hpc (by simp) (by simp) (by simp)
    by_cases hin : q ∈ ac C.mem (C.loc q).aj
    · simp [hin] at hmem
      exact ⟨fun _ => by rw [hmem]; simp, fun r hr h' => by rwa [hmem] at h',
        fun _ r hr h' => by rwa [hmem], fun r hr j h' => by
          rw [hmem, ac_update_ann] at h'; split_ifs at h' <;> simp_all,
        fun r hr h' => by
          rw [hmem, av_update_ann] at h'; split_ifs at h' with e
          · simp [isOp] at h'
          · exact h',
        fun _ => by rw [hpc]; rfl,
        fun h => absurd h hnt, fun h => absurd h hnt, fun h => absurd h hnt⟩
    · simp [hin] at hmem
      exact StepFacts.of_same hmem hnt
  | scApply j' o' =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    by_cases hin : q ∈ hc C.mem
    · simp [hin] at hmem
      have hhd := (hQ.ch hin).1
      rw [hhd] at hmem
      have hvn : (hv C.mem).2 = none := by rw [← hhd]; exact hl.1
      have hav : av C.mem j' = some (.inl o') := hQ.k6 j' o' hpc hin
      have ht : IsTrans q C := ⟨hin, Or.inl ⟨j', o', hpc⟩⟩
      refine ⟨fun h => absurd ht h, fun r hr h' => by rw [hmem] at h'; simp at h',
        fun h => absurd ht h, fun r _ j h' => by rwa [hmem] at h', fun r _ h' => by rwa [hmem] at h',
        fun _ => by rw [hpc]; rfl, fun _ j => by rw [hmem]; simp, fun _ => by rw [hmem]; simp,
        fun _ j => ⟨fun ho => ?_, fun ho => ?_⟩⟩
      · rw [hmem] at ho; simp [ownerIs] at ho; subst ho
        refine ⟨by rw [hvn]; rfl, by rw [hav]; rfl⟩
      · rw [hvn] at ho; simp [ownerIs] at ho
    · simp [hin] at hmem
      exact StepFacts.of_same hmem (fun ⟨h1, _⟩ => hin h1)
  | scHead =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    by_cases hin : q ∈ hc C.mem
    · simp [hin] at hmem
      have hhd := (hQ.ch hin).1
      rw [hhd] at hmem
      have hvj : (hv C.mem).2 = some (rsp, (C.loc q).aj) := by rw [← hhd, hrsp]
      have hnotinl : ∀ o, av C.mem (C.loc q).aj ≠ some (.inl o) := by
        by_cases hac : q ∈ ac C.mem (C.loc q).aj
        · rw [hQ.ca1 _ hac rfl]; intro o e
          exact hQ.k4 hpc (by rw [e]; rfl) hac
        · exact hQ.k3 hin (by rw [hpc]; rfl) hac
      have ht : IsTrans q C := ⟨hin, Or.inr (Or.inl hpc)⟩
      refine ⟨fun h => absurd ht h, fun r hr h' => by rw [hmem] at h'; simp at h',
        fun h => absurd ht h, fun r _ j h' => by rwa [hmem] at h', fun r _ h' => by rwa [hmem] at h',
        fun _ => by rw [hpc]; rfl, fun _ j => by rw [hmem]; simp, fun _ => by rw [hmem]; simp,
        fun _ j => ⟨fun ho => by rw [hmem] at ho; simp [ownerIs] at ho, fun ho => ?_⟩⟩
      rw [hvj] at ho; simp [ownerIs] at ho; subst ho
      refine ⟨by rw [hmem]; rfl, ?_⟩
      rcases e : av C.mem (C.loc q).aj with _ | v
      · rfl
      · cases v with
        | inl o => exact absurd e (hnotinl o)
        | inr _ => rfl
    · simp [hin] at hmem
      exact StepFacts.of_same hmem (fun ⟨h1, _⟩ => hin h1)
  | clear r =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    by_cases hin : q ∈ hc C.mem
    · simp [hin] at hmem
      have hhd := (hQ.ch hin).1
      rw [hhd] at hmem
      have hvj : (hv C.mem).2 = some (rsp, q) := by rw [← hhd, hrsp]
      have hav : ∃ x, av C.mem q = some (.inr x) := by
        have := hQ.pinv; rw [hpc] at this; exact ⟨r, this.2.1⟩
      have ht : IsTrans q C := ⟨hin, Or.inr (Or.inr ⟨r, hpc⟩)⟩
      refine ⟨fun h => absurd ht h, fun r hr h' => by rw [hmem] at h'; simp at h',
        fun h => absurd ht h, fun r _ j h' => by rwa [hmem] at h', fun r _ h' => by rwa [hmem] at h',
        fun _ => by rw [hpc]; rfl, fun _ j => by rw [hmem]; simp, fun _ => by rw [hmem]; simp,
        fun _ j => ⟨fun ho => by rw [hmem] at ho; simp [ownerIs] at ho, fun ho => ?_⟩⟩
      rw [hvj] at ho; simp [ownerIs] at ho; subst ho
      obtain ⟨x, hx⟩ := hav
      exact ⟨by rw [hmem]; rfl, by rw [hx]; rfl⟩
    · simp [hin] at hmem
      exact StepFacts.of_same hmem (fun ⟨h1, _⟩ => hin h1)

/-! ## The budget of `announce[j]` -/

/-- `G2 ≤ G2max`. -/
def G2max (n : ℕ) : ℕ := n * (2 * K0 n)
/-- Tier constants. -/
def T1 (n : ℕ) : ℕ := n * 3 + 1
/-- Tier constants. -/
def T2 (n : ℕ) : ℕ := T1 n * (G2max n + 1) + 1

/-- The budget for changes of `announce[j]` that do not reset its context: while `head` is owned
by `j` (mode `B` for `p_j`'s operation) no transition other than the end of this mode is possible
and `G2` bounds all changes; otherwise only stragglers can change it (`Sj`), and if `p_j`'s
operation is announced but not yet applied, a future mode `B` for it is accounted for by `T2`. -/
noncomputable def Wann (j : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : ℕ :=
  if ownerIs j (hv D.mem).2 then T1 n * (G2 D + 1)
  else if isOp (av D.mem j) then T2 n + Sj j D else Sj j D

omit [DecidablePred A.ReadOnly] in
lemma Wann_le (j : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) : Wann j D ≤ T2 n + n * 3 := by
  have h1 := G2_le D
  have h2 := Sj_le j D
  have h3 : T1 n * (G2 D + 1) ≤ T1 n * (G2max n + 1) :=
    Nat.mul_le_mul_left _ (by unfold G2max; omega)
  unfold Wann T2
  split_ifs <;> omega

/-- Transitions do not increase `Wann`. -/
theorem Wann_trans {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} (j : Fin n)
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.tau q) = some C')
    (ht : IsTrans q C) : Wann j C' ≤ Wann j C := by
  have F := stepFacts hI h
  have hS := Sj_trans j h ht
  have hav : av C'.mem j = av C.mem j := by simp only [av, F.transAnn ht j]
  have hG := G2_le C'
  have hT : T1 n * (G2 C' + 1) ≤ T1 n * (G2max n + 1) :=
    Nat.mul_le_mul_left _ (by unfold G2max at *; omega)
  have hSle := Sj_le j C'
  obtain ⟨h1, h2⟩ := F.transOwner ht j
  unfold Wann
  rw [hav]
  by_cases ho : ownerIs j (hv C.mem).2 = true
  · obtain ⟨h3, h4⟩ := h2 ho
    simp only [ho, h3, h4, ↓reduceIte, Bool.false_eq_true]
    have : 1 ≤ G2 C + 1 := by omega
    have := Nat.mul_le_mul_left (T1 n) this
    unfold T1 at *; omega
  · by_cases ho' : ownerIs j (hv C'.mem).2 = true
    · obtain ⟨h3, h4⟩ := h1 ho'
      simp only [ho', h3, h4, ↓reduceIte, Bool.false_eq_true]
      unfold T2; omega
    · simp only [ho, ho', Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega

/-- Non-transition steps that do not reset the context of `announce[j]` do not increase
`Wann`, and strictly decrease it if they change `announce[j]`. -/
theorem Wann_tau {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    (hcur : ∀ q, (cur q).1 = q) {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n}
    (j : Fin n) (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.tau q) = some C')
    (hnt : ¬ IsTrans q C) (hne : ac C'.mem j ≠ ∅) :
    Wann j C' ≤ Wann j C ∧ (C'.mem (.ann j) ≠ C.mem (.ann j) → Wann j C' < Wann j C) := by
  have F := stepFacts hI h
  have hG := G2_tau hcur hI h hnt
  have hhv := F.hvSame hnt
  unfold Wann
  rw [hhv]
  by_cases ho : ownerIs j (hv C.mem).2 = true
  · simp only [ho, ↓reduceIte]
    refine ⟨Nat.mul_le_mul_left _ (by omega), fun hch => ?_⟩
    have hm : C'.mem ≠ C.mem := fun e => hch (by rw [e])
    have := hG.2 (F.memRO hm)
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by unfold T1; omega)
  · rcases Sj_tau hI h hnt j (by simpa using ho) with h0 | ⟨hav, hle, hlt⟩
    · exact absurd h0 hne
    · simp only [ho, Bool.false_eq_true, ↓reduceIte, hav]
      refine ⟨by split_ifs <;> omega, fun hch => ?_⟩
      have : ac C'.mem j ≠ ac C.mem j := by
        intro e; apply hch
        have e1 : (C'.mem (.ann j)).1 = (C.mem (.ann j)).1 := hav
        have e2 : (C'.mem (.ann j)).2 = (C.mem (.ann j)).2 := e
        exact Prod.ext e1 e2
      have := hlt this
      split_ifs <;> omega

omit [DecidablePred A.ReadOnly] in
/-- `Wann` under steps that do not change the memory, given that `G2` and `Sj` do not increase. -/
lemma Wann_same_mem {D D' : Config A (B A n) (Fin n) (Loc A n)} (j : Fin n)
    (hm : D'.mem = D.mem) (hG : G2 D' ≤ G2 D) (hS : Sj j D' ≤ Sj j D) : Wann j D' ≤ Wann j D := by
  unfold Wann; rw [hm]
  split_ifs
  · exact Nat.mul_le_mul_left _ (by omega)
  all_goals omega

/-! ## The local potential of `p` and the final potential -/

/-- The local progress of `p` inside its current Algorithm 6 operation. -/
noncomputable def psiV (p : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) (l : FLoc A n) : ℕ :=
  match act p l.l5 with
  | .access .head o _ => psiOp o l.st l.turn l.curH (D.mem .head)
  | .access (.ann j) o _ => psiOp o l.st l.turn l.curA (D.mem (.ann j))
  | .ret _ _ => 0

omit [DecidablePred A.ReadOnly] in
lemma psiV_le (p : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) (l : FLoc A n) :
    psiV p D l ≤ 7 := by
  unfold psiV; split
  · exact psiOp_le _ _ _ _ _
  · exact psiOp_le _ _ _ _ _
  · omega

omit [DecidablePred A.ReadOnly] in
lemma psiV_change (p : Fin n) (D D' : Config A (B A n) (Fin n) (Loc A n)) (l : FLoc A n) :
    psiV p D' l ≤ psiV p D l + 4 := by
  unfold psiV; split
  · exact psiOp_change _ _ _ _ _ _
  · exact psiOp_change _ _ _ _ _ _
  · omega

omit [DecidablePred A.ReadOnly] in
lemma psiV_same (p : Fin n) (D D' : Config A (B A n) (Fin n) (Loc A n)) (l : FLoc A n)
    (hh : D'.mem .head = D.mem .head) (ha : ∀ j, D'.mem (.ann j) = D.mem (.ann j)) :
    psiV p D' l = psiV p D l := by
  unfold psiV; split
  · rw [hh]
  · rw [ha]
  · rfl

/-- The local potential of `p` (see the module docstring). -/
noncomputable def Vf (p : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) (l : FLoc A n) : ℕ :=
  match l.l5.pc with
  | .llHead | .llAnn =>
    if phase p D = 1 ∨ phase p D = 2 then 5 * (G2 D + 1) + psiV p D l
    else if l.turn then 0 else 1
  | .llHead2 _ =>
    if ownerIs p (hv D.mem).2 then 5 * (G2 D + 1) + psiV p D l
    else if l.turn then 0 else 1
  | .scApply _ _ | .scHead | .clear _ | .rlHead _ =>
    if p ∈ hc D.mem then 5 * (G2 D + 1) + psiV p D l
    else if l.st then 1 else 0
  | .scAnn | .rlAnn =>
    if p ∈ ac D.mem l.l5.aj then 5 * (Wann l.l5.aj D + 1) + psiV p D l
    else if l.st then 1 else 0
  | .rl18 j =>
    if p ∈ ac D.mem j then 5 * (Wann j D + 1) + psiV p D l
    else if l.st then 1 else 0
  | _ => 0

/-- Bound on `Vf`. -/
def Vmax (n : ℕ) : ℕ := 5 * (T2 n + n * 3 + 1) + 7

omit [DecidablePred A.ReadOnly] in
lemma Vf_le (p : Fin n) (D : Config A (B A n) (Fin n) (Loc A n)) (l : FLoc A n) :
    Vf p D l ≤ Vmax n := by
  have h1 := psiV_le p D l
  have h2 : G2 D ≤ G2max n := G2_le D
  have h4 : G2 D ≤ T2 n := by
    have : G2max n + 1 ≤ T1 n * (G2max n + 1) := Nat.le_mul_of_pos_left _ (by unfold T1; omega)
    unfold T2; omega
  have hG : 5 * (G2 D + 1) + psiV p D l ≤ Vmax n := by unfold Vmax; omega
  have hW : ∀ j, 5 * (Wann j D + 1) + psiV p D l ≤ Vmax n := fun j => by
    have := Wann_le j D; unfold Vmax; omega
  have h0 : 1 ≤ Vmax n := by unfold Vmax; omega
  unfold Vf
  split <;> (try split_ifs) <;> first | exact hG | exact hW _ | omega

omit [DecidablePred A.ReadOnly] in
lemma psiV_eq {p : Fin n} {D D' : Config A (B A n) (Fin n) (Loc A n)} {l : FLoc A n}
    (h : ∀ i o k, act p l.l5 = .access i o k → D'.mem i = D.mem i) :
    psiV p D' l = psiV p D l := by
  unfold psiV
  split
  · rename_i o k hA; rw [h _ _ _ hA]
  · rename_i j o k hA; rw [h _ _ _ hA]
  · rfl

omit [DecidablePred A.ReadOnly] in
/-- The object accessed by `p` at the `announce` operations of lines 20, 22, 18R.2. -/
lemma act_cell_ann {p : Fin n} {l : Loc A n} (hloc : LocInv p l) {j : Fin n}
    (hj : (l.pc = .scAnn ∨ l.pc = .rlAnn) ∧ l.aj = j ∨ l.pc = .rl18 j) :
    ∀ i o k, act p l = .access i o k → i = .ann j := by
  intro i o k hA
  rcases hj with ⟨hpc | hpc, rfl⟩ | hpc
  · simp only [LocInv, hpc] at hloc
    obtain ⟨⟨rsp, hrsp⟩, -⟩ := hloc
    simp only [act, hpc, hrsp] at hA
    injection hA with h1; exact h1.symm
  · simp only [act, hpc] at hA
    injection hA with h1; exact h1.symm
  · simp only [act, hpc] at hA
    injection hA with h1; exact h1.symm

omit [DecidablePred A.ReadOnly] in
lemma phase12_iff {p : Fin n} {D : Config A (B A n) (Fin n) (Loc A n)}
    (hl : (D.loc p).pc.inLoop = true) :
    (phase p D = 1 ∨ phase p D = 2) ↔ isOp (av D.mem p) = true := by
  rw [phase_of_loop hl]
  split_ifs <;> simp_all

/-- The potential of process `p` in a configuration of the flattened implementation. -/
noncomputable def PiF (p : Fin n) (C : Config A (BF A n) (Fin n) (FLoc A n)) : ℕ :=
  (Vmax n + 1) * mu p (absC C) + Vf p (absC C) (C.loc p)

/-- **Steps of other processes do not increase `p`'s local potential** (unless they decrease
its atomic potential). -/
theorem Vf_tau_other {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    (hcur : ∀ q, (cur q).1 = q) {D D' : Config A (B A n) (Fin n) (Loc A n)} {p q : Fin n}
    {l : FLoc A n} (hI : InvC L cur D.pend D.mem D.loc) (hqp : q ≠ p)
    (h : (alg5 A n).step D (.tau q) = some D') (hmu : mu p D' = mu p D) (hl : l.l5 = D.loc p) :
    Vf p D' l ≤ Vf p D l := by
  have F := stepFacts hI h
  obtain ⟨-, -, i, o, k, -, -, hloc⟩ := Impl.step_tau h
  have hlp : D'.loc p = D.loc p := by rw [hloc]; exact Function.update_of_ne (Ne.symm hqp) _ _
  have hP := hI.proc p
  have hLI : LocInv p l.l5 := by rw [hl]; exact hP.loc
  have bigG : ¬ IsTrans q D → 5 * (G2 D' + 1) + psiV p D' l ≤ 5 * (G2 D + 1) + psiV p D l := by
    intro hnt
    have hG := G2_tau hcur hI h hnt
    by_cases hm : D'.mem = D.mem
    · rw [psiV_eq (D := D) (D' := D') (fun i _ _ _ => by rw [hm])]; omega
    · have := hG.2 (F.memRO hm); have := psiV_change p D D' l; omega
  have bigW : ∀ j, (∀ i o k, act p l.l5 = .access i o k → i = .ann j) → p ∈ ac D'.mem j →
      5 * (Wann j D' + 1) + psiV p D' l ≤ 5 * (Wann j D + 1) + psiV p D l := by
    intro j hcell hin'
    by_cases ht : IsTrans q D
    · rw [psiV_eq (D := D) (D' := D') (fun i _ _ hA => by rw [hcell _ _ _ hA]; exact F.transAnn ht j)]
      have := Wann_trans j hI h ht; omega
    · have hW := Wann_tau hcur j hI h ht (fun e => by rw [e] at hin'; simp at hin')
      by_cases hm : D'.mem (.ann j) = D.mem (.ann j)
      · rw [psiV_eq (D := D) (D' := D') (fun i _ _ hA => by rw [hcell _ _ _ hA]; exact hm)]; omega
      · have := hW.2 hm; have := psiV_change p D D' l; omega
  have hloop : ∀ pc : PC A n, l.l5.pc = pc → pc.inLoop = true →
      (D.loc p).pc.inLoop = true ∧ (D'.loc p).pc.inLoop = true := by
    intro pc hpc hin; rw [hlp, ← hl, hpc]; exact ⟨hin, hin⟩
  unfold Vf
  cases hpc : l.l5.pc with
  | llHead | llAnn =>
    dsimp only
    obtain ⟨h1, h1'⟩ := hloop _ hpc rfl
    by_cases h12 : phase p D = 1 ∨ phase p D = 2
    · have hop := (phase12_iff h1).1 h12
      have hnt : ¬ IsTrans q D := fun ht => by have := mu_lt_trans hI hqp h ht ⟨h1, hop⟩; omega
      rw [if_pos h12]
      by_cases h12' : phase p D' = 1 ∨ phase p D' = 2
      · rw [if_pos h12']; exact bigG hnt
      · rw [if_neg h12']; split_ifs <;> omega
    · rw [if_neg h12]
      have h12' : ¬ (phase p D' = 1 ∨ phase p D' = 2) := fun h' =>
        h12 ((phase12_iff h1).2 (F.avOp p (Ne.symm hqp) ((phase12_iff h1').1 h')))
      rw [if_neg h12']
  | llHead2 r =>
    dsimp only
    have hpost : isOp (av D.mem p) = false := by
      have := hP.pinv; rw [← hl, hpc] at this; rw [this.2.1]; rfl
    by_cases ho : ownerIs p (hv D.mem).2 = true
    · rw [if_pos ho]
      by_cases ht : IsTrans q D
      · rw [if_neg (by simp [((F.transOwner ht p).2 ho).1])]; split_ifs <;> omega
      · rw [F.hvSame ht, if_pos ho]; exact bigG ht
    · rw [if_neg ho]
      have ho' : ¬ ownerIs p (hv D'.mem).2 = true := by
        intro ho'
        by_cases ht : IsTrans q D
        · rw [((F.transOwner ht p).1 ho').2] at hpost; cases hpost
        · rw [F.hvSame ht] at ho'; exact ho ho'
      rw [if_neg ho']
  | scApply _ _ | scHead | clear _ | rlHead _ =>
    dsimp only
    by_cases hin : p ∈ hc D.mem
    · rw [if_pos hin]
      by_cases ht : IsTrans q D
      · rw [if_neg (by rw [F.transHc ht]; simp)]; split_ifs <;> omega
      · rw [if_pos (F.hcSup ht p (Ne.symm hqp) hin)]; exact bigG ht
    · rw [if_neg hin, if_neg (fun h' => hin (F.hcSub p (Ne.symm hqp) h'))]
  | scAnn | rlAnn =>
    dsimp only
    by_cases hin : p ∈ ac D.mem l.l5.aj
    · rw [if_pos hin]
      by_cases hin' : p ∈ ac D'.mem l.l5.aj
      · rw [if_pos hin']
        exact bigW _ (act_cell_ann hLI (Or.inl ⟨by simp [hpc], rfl⟩)) hin'
      · rw [if_neg hin']; split_ifs <;> omega
    · rw [if_neg hin, if_neg (fun h' => hin (F.acSub p (Ne.symm hqp) _ h'))]
  | rl18 j =>
    dsimp only
    by_cases hin : p ∈ ac D.mem j
    · rw [if_pos hin]
      by_cases hin' : p ∈ ac D'.mem j
      · rw [if_pos hin']
        exact bigW _ (act_cell_ann hLI (Or.inr hpc)) hin'
      · rw [if_neg hin']; split_ifs <;> omega
    · rw [if_neg hin, if_neg (fun h' => hin (F.acSub p (Ne.symm hqp) _ h'))]
  | _ => exact le_rfl

omit [DecidablePred A.ReadOnly] in
/-- Steps of other processes that do not change the memory (jumps, invocations, responses). -/
theorem Vf_same_mem {D D' : Config A (B A n) (Fin n) (Loc A n)} {p : Fin n} {l : FLoc A n}
    (hm : D'.mem = D.mem) (hlp : D'.loc p = D.loc p) (hG : G2 D' ≤ G2 D)
    (hS : ∀ j, Sj j D' ≤ Sj j D) : Vf p D' l ≤ Vf p D l := by
  have hph : phase p D' = phase p D := phase_eq hlp (by rw [hm]) (by rw [hm])
  have hpsi : psiV p D' l = psiV p D l := psiV_eq (D := D) (D' := D') (fun i _ _ _ => by rw [hm])
  have hW : ∀ j, Wann j D' ≤ Wann j D := fun j => Wann_same_mem j hm hG (hS j)
  unfold Vf
  rw [hph, hpsi, hm]
  split
  all_goals first
    | exact le_rfl
    | (split_ifs <;> omega)
    | (split_ifs <;> (try have := hW ‹_›) <;> omega)
    | (split_ifs with h1 h2 <;> (try have := hW l.l5.aj) <;> omega)

/-! ## Steps of `p` -/

omit [DecidablePred A.ReadOnly] in
lemma act_isLL_head {p : Fin n} {l : Loc A n} {o : (B A n .head).Op} {k : (B A n .head).Resp → Loc A n}
    (h : act p l = .access .head o k) (hll : isLL o = true) :
    l.pc = .llHead ∨ ∃ r, l.pc = .llHead2 r := by
  cases hpc : l.pc <;> simp only [act, hpc] at h
  all_goals first
    | (cases h; done)
    | (left; rfl)
    | (right; exact ⟨_, rfl⟩)
    | (cases h; simp [isLL] at hll)
    | (split at h <;> cases h <;> simp [isLL] at hll)
    | (injection h with h1; cases h1)
    | (split at h <;> (injection h with h1; cases h1))

omit [DecidablePred A.ReadOnly] in
lemma act_isLL_ann {p j : Fin n} {l : Loc A n} {o : (B A n (.ann j)).Op}
    {k : (B A n (.ann j)).Resp → Loc A n}
    (h : act p l = .access (.ann j) o k) (hll : isLL o = true) : l.pc = .llAnn := by
  cases hpc : l.pc <;> simp only [act, hpc] at h
  all_goals first
    | (cases h; done)
    | rfl
    | (cases h; simp [isLL] at hll)
    | (split at h <;> cases h <;> simp [isLL] at hll)
    | (injection h with h1; cases h1)
    | (split at h <;> first | (injection h with h1; cases h1) | (cases h; simp [isLL] at hll))

lemma E_of_eff {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n} {i : Obj n}
    {o : (B A n i).Op} {k : (B A n i).Resp → Loc A n} (hp : C.pend p ≠ none)
    (hA : act p (C.loc p).l5 = .access i o k) (hpend : C'.pend = C.pend)
    (hlr : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (hm : C'.mem = Function.update C.mem i ((B A n i).δ (C.mem i) o).1)
    (hl5 : (C'.loc p).l5 = k ((B A n i).δ (C.mem i) o).2) :
    (alg5 A n).step (absC C) (.tau p) = some (absC C') := by
  rw [alg5_step_tau_of_act (D := absC C) hp hA]
  congr 1
  exact (absC_eq_of hpend hlr hl5 hm).symm

omit [DecidablePred A.ReadOnly] in
lemma PiF_lt_of_mu {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n}
    (h : mu p (absC C') < mu p (absC C)) : PiF p C' < PiF p C := by
  have h1 := Vf_le p (absC C') (C'.loc p)
  have h2 : (Vmax n + 1) * (mu p (absC C') + 1) ≤ (Vmax n + 1) * mu p (absC C) :=
    Nat.mul_le_mul_left _ h
  rw [Nat.mul_succ] at h2
  unfold PiF; omega

omit [DecidablePred A.ReadOnly] in
lemma PiF_lt_of_V {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n}
    (h : absC C' = absC C) (hV : Vf p (absC C) (C'.loc p) < Vf p (absC C) (C.loc p)) :
    PiF p C' < PiF p C := by
  unfold PiF; rw [h]; omega

omit [DecidablePred A.ReadOnly] in
lemma PiF_le_of {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n}
    (hmu : mu p (absC C') ≤ mu p (absC C))
    (hV : mu p (absC C') = mu p (absC C) → Vf p (absC C') (C'.loc p) ≤ Vf p (absC C) (C.loc p)) :
    PiF p C' ≤ PiF p C := by
  rcases Nat.lt_or_eq_of_le hmu with h | h
  · exact (PiF_lt_of_mu h).le
  · unfold PiF; rw [h]; have := hV h; omega

omit [DecidablePred A.ReadOnly] in
lemma act_access {p : Fin n} {l : Loc A n} (h1 : ∀ r, l.pc ≠ .roRet r)
    (h2 : ∀ r, l.pc ≠ .retSC r) : ∃ i o k, act p l = .access i o k := by
  cases hpc : l.pc <;> simp only [act, hpc]
  all_goals first
    | exact absurd hpc (h1 _)
    | exact absurd hpc (h2 _)
    | exact ⟨_, _, _, rfl⟩
    | (split <;> exact ⟨_, _, _, rfl⟩)

omit [DecidablePred A.ReadOnly] in
lemma psiV_turn {p : Fin n} {D : Config A (B A n) (Fin n) (Loc A n)} {l : FLoc A n}
    (ht : l.turn = true) {i : Obj n} {o : (B A n i).Op} {k : (B A n i).Resp → Loc A n}
    (hA : act p l.l5 = .access i o k) :
    psiV p D { l with turn := false } + 1 = psiV p D l := by
  have hA' : act p ({ l with turn := false } : FLoc A n).l5 = .access i o k := hA
  unfold psiV
  rw [hA']
  cases i <;> simp [psiOp, ht] <;> split_ifs <;> omega

/-- **Every step of `p` decreases its potential.** -/
theorem PiF_self {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n}
    (hI : InvC L cur (absC C).pend (absC C).mem (absC C).loc)
    (h : (flat A n).step C (.tau p) = some C') : PiF p C' < PiF p C := by
  obtain ⟨hp, hpend, i, o', k', hact, hmem, hloc⟩ := Impl.step_tau h
  have hlr : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
    rw [hloc]; exact Function.update_of_ne hq _ _
  have hlp : C'.loc p = k' ((BF A n i).δ (C.mem i) o').2 := by rw [hloc]; simp
  have hP := hI.proc p
  have absEq : C'.mem = C.mem → (C'.loc p).l5 = (C.loc p).l5 → absC C' = absC C := fun hm hl => by
    rw [absC_eq_of (p := p) (l := (C.loc p).l5) hpend hlr hl hm]; simp [absC]
  have viaJ : C'.mem = C.mem → Jump p (absC C) (C'.loc p).l5 → PiF p C' < PiF p C := fun hm hJ => by
    apply PiF_lt_of_mu
    rw [absC_eq_of (p := p) (l := (C'.loc p).l5) hpend hlr rfl hm]
    exact mu_jump_self hI hJ
  have viaE : (alg5 A n).step (absC C) (.tau p) = some (absC C') → PiF p C' < PiF p C :=
    fun hE => PiF_lt_of_mu (mu_tau_self p hI hE)
  -- `p`'s operation is in the loop: announce holds `inl` or `inr`
  have loopAv : (C.loc p).l5.pc.inLoop = true →
      isResp (av C.mem p) = false → isOp (av C.mem p) = true := by
    intro hl hr
    have pinv := hP.pinv
    change PInv L (cur p) (C.pend p) C.mem p (C.loc p).l5.pc at pinv
    rw [PInv_loop hl] at pinv
    obtain ⟨o, -, -, ⟨h1, -⟩ | ⟨r, h1, -⟩⟩ := pinv
    · rw [h1]; rfl
    · rw [h1] at hr; cases hr
  have leftCase : leftAct p (C.loc p) = .access i o' k' →
      (¬ ((C.loc p).l5.pc = .llHead ∨ (C.loc p).l5.pc = .llAnn ∨ ∃ r, (C.loc p).l5.pc = .llHead2 r) ∨
        (C.loc p).turn = false) → PiF p C' < PiF p C := by
    intro hL hturn0
    rcases hA : act p (C.loc p).l5 with ⟨i₀, o, k⟩ | ⟨r, l⟩
    · cases i₀ with
      | head =>
        rw [leftAct_head hA] at hL; cases hL
        have hturn : isLL o = true → (C.loc p).turn = false := fun hll => by
          rcases hturn0 with h0 | h0
          · rcases act_isLL_head hA hll with e | ⟨r, e⟩
            · exact absurd (Or.inl e) h0
            · exact absurd (Or.inr (Or.inr ⟨r, e⟩)) h0
          · exact h0
        rcases stepOp_casesH o k (C.loc p) hturn (B A n .head).init (C.mem .head) (A.init, none) with
          eff | ⟨hne, h1, h2, h3, h4, h5, h6, h7, h8⟩
        · exact viaE (E_of_eff hp hA hpend hlr (by rw [hmem]; erw [eff.1]) (by rw [hlp]; exact eff.2))
        · have hm : C'.mem = C.mem := by rw [hmem]; erw [h1]; simp
          have hl5 : (C'.loc p).l5 = (C.loc p).l5 := by rw [hlp]; exact h2
          apply PiF_lt_of_V (absEq hm hl5)
          have hpsi : psiV p (absC C) (C'.loc p) < psiV p (absC C) (C.loc p) := by
            have e1 : act p (C'.loc p).l5 = .access .head o k := by rw [hl5]; exact hA
            unfold psiV; rw [e1, hA]; rw [hlp]; exact h3
          have hst' : (C'.loc p).st = true → grd o (C'.loc p).curH ∧ (C'.loc p).curH = C.mem .head :=
            fun h => by rw [hlp] at h ⊢; exact ⟨h4 h, h7 h⟩
          have hst : ¬ ((C.loc p).st = true ∧ grd o (C.loc p).curH) → (C'.loc p).st = true :=
            fun h => by rw [hlp]; exact h8 h
          have htu : isLL o = true → (C'.loc p).turn = true := fun h => by rw [hlp]; exact h6 h
          unfold Vf; rw [hl5]
          cases hpc : (C.loc p).l5.pc with
          | llHead | llHead2 _ =>
            simp only [act, hpc] at hA; cases hA
            have t0 := hturn rfl; have t1 := htu rfl
            dsimp only
            split_ifs <;> simp_all
            all_goals omega
          | scApply _ _ | scHead | clear _ | rlHead _ =>
            simp only [act, hpc] at hA; cases hA
            dsimp only
            by_cases hin : p ∈ hc (absC C).mem
            · rw [if_pos hin, if_pos hin]; omega
            · rw [if_neg hin, if_neg hin]
              have e1 : (C'.loc p).st = false := by
                cases e : (C'.loc p).st
                · rfl
                · exfalso; obtain ⟨g, gc⟩ := hst' e; rw [gc] at g; exact hin g
              have e2 : (C.loc p).st = true := by
                by_contra e; have := hst (fun h => e h.1); rw [e1] at this; cases this
              rw [e1, e2]; simp
          | _ =>
            simp only [act, hpc] at hA
            first
              | (cases hA; done)
              | (cases hA; exact absurd (by simp [stepOp]) hne)
              | (split at hA <;> cases hA <;> exact absurd (by simp [stepOp]) hne)
              | (injection hA with e; cases e)
              | (split at hA <;> (injection hA with e; cases e))
      | ann j =>
        rw [leftAct_ann hA] at hL; cases hL
        have hturn : isLL o = true → (C.loc p).turn = false := fun hll => by
          rcases hturn0 with h0 | h0
          · exact absurd (Or.inr (Or.inl (act_isLL_ann hA hll))) h0
          · exact h0
        rcases stepOp_casesA o k (C.loc p) hturn (B A n (.ann j)).init (C.mem (.ann j)) none with
          eff | ⟨hne, h1, h2, h3, h4, h5, h6, h7, h8⟩
        · exact viaE (E_of_eff hp hA hpend hlr (by rw [hmem]; erw [eff.1]) (by rw [hlp]; exact eff.2))
        · have hm : C'.mem = C.mem := by rw [hmem]; erw [h1]; simp
          have hl5 : (C'.loc p).l5 = (C.loc p).l5 := by rw [hlp]; exact h2
          apply PiF_lt_of_V (absEq hm hl5)
          have hpsi : psiV p (absC C) (C'.loc p) < psiV p (absC C) (C.loc p) := by
            have e1 : act p (C'.loc p).l5 = .access (.ann j) o k := by rw [hl5]; exact hA
            unfold psiV; rw [e1, hA]; rw [hlp]; exact h3
          have hst' : (C'.loc p).st = true → grd o (C'.loc p).curA ∧ (C'.loc p).curA = C.mem (.ann j) :=
            fun h => by rw [hlp] at h ⊢; exact ⟨h4 h, h7 h⟩
          have hst : ¬ ((C.loc p).st = true ∧ grd o (C.loc p).curA) → (C'.loc p).st = true :=
            fun h => by rw [hlp]; exact h8 h
          have htu : isLL o = true → (C'.loc p).turn = true := fun h => by rw [hlp]; exact h6 h
          have hLI : LocInv p (C.loc p).l5 := hP.loc
          unfold Vf; rw [hl5]
          cases hpc : (C.loc p).l5.pc with
          | llAnn =>
            have hl5' := hLI; simp only [LocInv, hpc] at hl5'
            obtain ⟨⟨rsp, j'⟩, hj⟩ := Option.isSome_iff_exists.1 hl5'
            simp only [act, hpc, hj] at hA; cases hA
            have t0 := hturn rfl; have t1 := htu rfl
            dsimp only
            split_ifs <;> simp_all
            all_goals omega
          | scAnn =>
            have hl5' := hLI; simp only [LocInv, hpc] at hl5'
            obtain ⟨⟨rsp, hrsp⟩, -⟩ := hl5'
            simp only [act, hpc, hrsp] at hA; cases hA
            dsimp only
            by_cases hin : p ∈ ac (absC C).mem (C.loc p).l5.aj
            · rw [if_pos hin, if_pos hin]; omega
            · rw [if_neg hin, if_neg hin]
              have e1 : (C'.loc p).st = false := by
                cases e : (C'.loc p).st
                · rfl
                · exfalso; obtain ⟨g, gc⟩ := hst' e; rw [gc] at g; exact hin g
              have e2 : (C.loc p).st = true := by
                by_contra e; have := hst (fun h => e h.1); rw [e1] at this; cases this
              rw [e1, e2]; simp
          | rlAnn =>
            simp only [act, hpc] at hA; cases hA
            dsimp only
            by_cases hin : p ∈ ac (absC C).mem (C.loc p).l5.aj
            · rw [if_pos hin, if_pos hin]; omega
            · rw [if_neg hin, if_neg hin]
              have e1 : (C'.loc p).st = false := by
                cases e : (C'.loc p).st
                · rfl
                · exfalso; obtain ⟨g, gc⟩ := hst' e; rw [gc] at g; exact hin g
              have e2 : (C.loc p).st = true := by
                by_contra e; have := hst (fun h => e h.1); rw [e1] at this; cases this
              rw [e1, e2]; simp
          | rl18 j' =>
            simp only [act, hpc] at hA; cases hA
            dsimp only
            by_cases hin : p ∈ ac (absC C).mem j
            · rw [if_pos hin, if_pos hin]; omega
            · rw [if_neg hin, if_neg hin]
              have e1 : (C'.loc p).st = false := by
                cases e : (C'.loc p).st
                · rfl
                · exfalso; obtain ⟨g, gc⟩ := hst' e; rw [gc] at g; exact hin g
              have e2 : (C.loc p).st = true := by
                by_contra e; have := hst (fun h => e h.1); rw [e1] at this; cases this
              rw [e1, e2]; simp
          | _ =>
            simp only [act, hpc] at hA
            first
              | (cases hA; done)
              | (cases hA; exact absurd (by simp [stepOp]) hne)
              | (split at hA <;> cases hA <;> exact absurd (by simp [stepOp]) hne)
              | (injection hA with e; cases e)
              | (split at hA <;> (injection hA with e; cases e))
              | (split at hA <;> first | (injection hA with e; cases e) | (cases hA; exact absurd (by simp [stepOp]) hne))
    · simp only [leftAct, hA] at hL; cases hL
  simp only [flat, fact] at hact
  by_cases ht : (C.loc p).turn = true
  · rw [if_pos ht] at hact
    cases hpc : (C.loc p).l5.pc with
    | llHead =>
      simp only [hpc, right6] at hact; cases hact
      have hm : C'.mem = C.mem := by rw [hmem]; simp
      by_cases hr : isResp (av C.mem p) = true
      · exact viaJ hm (Or.inl ⟨hpc, hr, by rw [hlp]; simp [hr, absC]⟩)
      · have hl' : C'.loc p = { C.loc p with turn := false } := by rw [hlp]; simp [hr]
        apply PiF_lt_of_V (absEq hm (by rw [hl']))
        have hloop : (C.loc p).l5.pc.inLoop = true := by rw [hpc]; rfl
        have hop := loopAv hloop (by simpa using hr)
        have h12 := (phase12_iff (D := absC C) hloop).2 hop
        obtain ⟨i₁, o₁, k₁, hA⟩ := act_access (p := p) (l := (C.loc p).l5) (by simp [hpc]) (by simp [hpc])
        have := psiV_turn (D := absC C) ht hA
        unfold Vf; rw [hl']; simp only [hpc]
        rw [if_pos h12, if_pos h12]; omega
    | llAnn =>
      simp only [hpc, right18] at hact; cases hact
      have hm : C'.mem = C.mem := by rw [hmem]; simp
      have hl5 := hP.loc; change LocInv p (C.loc p).l5 at hl5; simp only [LocInv, hpc] at hl5
      obtain ⟨⟨rsp, j⟩, hj⟩ := Option.isSome_iff_exists.1 hl5
      by_cases hr : isResp (av C.mem p) = true
      · exact viaJ hm (Or.inr (Or.inl ⟨hpc, hr, rsp, j, hj, by rw [hlp]; simp [hr, absC, hj]⟩))
      · have hl' : C'.loc p = { C.loc p with turn := false } := by rw [hlp]; simp [hr]
        apply PiF_lt_of_V (absEq hm (by rw [hl']))
        have hloop : (C.loc p).l5.pc.inLoop = true := by rw [hpc]; rfl
        have hop := loopAv hloop (by simpa using hr)
        have h12 := (phase12_iff (D := absC C) hloop).2 hop
        obtain ⟨i₁, o₁, k₁, hA⟩ := act_access (p := p) (l := (C.loc p).l5) (by simp [hpc]) (by simp [hpc])
        have := psiV_turn (D := absC C) ht hA
        unfold Vf; rw [hl']; simp only [hpc]
        rw [if_pos h12, if_pos h12]; omega
    | llHead2 r =>
      simp only [hpc, right25] at hact; cases hact
      have hm : C'.mem = C.mem := by rw [hmem]; simp
      by_cases hr : ownerIs p (hv C.mem).2 = true
      · have hl' : C'.loc p = { C.loc p with turn := false } := by rw [hlp]; simp [hr]
        apply PiF_lt_of_V (absEq hm (by rw [hl']))
        obtain ⟨i₁, o₁, k₁, hA⟩ := act_access (p := p) (l := (C.loc p).l5) (by simp [hpc]) (by simp [hpc])
        have := psiV_turn (D := absC C) ht hA
        unfold Vf; rw [hl']; simp only [hpc]
        rw [if_pos (show ownerIs p (hv (absC C).mem).2 = true from hr),
          if_pos (show ownerIs p (hv (absC C).mem).2 = true from hr)]; omega
      · exact viaJ hm (Or.inr (Or.inr ⟨r, hpc, (by simpa using hr : ownerIs p (hv C.mem).2 = false),
          by rw [hlp]; simp [hr, absC]⟩))
    | _ => simp only [hpc] at hact; exact leftCase hact (Or.inl (by simp [hpc]))
  · rw [if_neg ht] at hact; exact leftCase hact (Or.inr (by simpa using ht))

/-! ## Steps of other processes and wait-freedom -/

/-- **Steps of other processes do not increase `p`'s potential.** -/
theorem PiF_other {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    (hcur : ∀ q, (cur q).1 = q) {C C' : Config A (BF A n) (Fin n) (FLoc A n)} {p : Fin n}
    {ℓ : Label (Fin n) A} (hI : InvC L cur (absC C).pend (absC C).mem (absC C).loc)
    (h : (flat A n).step C ℓ = some C') (hq : ℓ.proc ≠ p) : PiF p C' ≤ PiF p C := by
  cases ℓ with
  | tau q =>
    have hqp : q ≠ p := hq
    have hloc5 : LocInv q (C.loc q).l5 := (hI.proc q).loc
    obtain ⟨hpend, hlr, hS | hE | hJ⟩ := flat_tau hloc5 h
    · have : absC C' = absC C := by
        rw [absC_eq_of (p := q) (l := (C.loc q).l5) hpend hlr hS.2 hS.1]; simp [absC]
      unfold PiF; rw [this, hlr p (Ne.symm hqp)]
    · have hlp := hlr p (Ne.symm hqp)
      refine PiF_le_of (mu_tau_other p hI hqp hE) fun hmu => ?_
      rw [hlp]
      exact Vf_tau_other hcur hI hqp hE hmu rfl
    · have hlp := hlr p (Ne.symm hqp)
      have e : absC C' = { absC C with loc := Function.update (absC C).loc q (C'.loc q).l5 } := by
        rw [absC_eq_of (p := q) (l := (C'.loc q).l5) hpend hlr rfl hJ.1]; rfl
      refine PiF_le_of (by rw [e]; exact mu_jump_other hqp hJ.2) fun _ => ?_
      rw [hlp, e]
      exact Vf_same_mem rfl (Function.update_of_ne (Ne.symm hqp) _ _) (G2_jump hI hJ.2)
        (fun j => Sj_jump j hJ.2)
  | inv q o =>
    have hqp : q ≠ p := hq
    have hA := flat_inv h
    obtain ⟨-, -, -, hloc, hmem⟩ := Impl.step_inv h
    have hlp : C'.loc p = C.loc p := by rw [hloc]; exact Function.update_of_ne (Ne.symm hqp) _ _
    refine PiF_le_of (mu_inv_other p hqp hA) fun _ => ?_
    rw [hlp]
    exact Vf_same_mem hmem (by simp [absC, hlp]) (G2_inv hI hA) (fun j => Sj_inv j hA)
  | ret q r =>
    have hqp : q ≠ p := hq
    have hA := flat_ret h
    obtain ⟨-, -, hmem, l, -, hloc⟩ := Impl.step_ret h
    have hlp : C'.loc p = C.loc p := by rw [hloc]; exact Function.update_of_ne (Ne.symm hqp) _ _
    refine PiF_le_of (mu_ret_other p hqp hA) fun _ => ?_
    rw [hlp]
    exact Vf_same_mem hmem (by simp [absC, hlp]) (G2_ret hI hA) (fun j => Sj_ret j hA)

/-- **Theorem 32** (wait-freedom): the flattened implementation (Algorithm 5 over
Algorithm 6, with the strict-alternation schedule for `∥`) is wait-free. -/
theorem flat_waitFree : (flat A n).WaitFree := by
  intro e p n0 hpend
  have hinv : ∀ m, InvC (hlinF A n ((List.range m).map e.lbl)) (curOf ((List.range m).map e.lbl))
      (absC (e.cfg m)).pend (absC (e.cfg m)).mem (absC (e.cfg m)).loc :=
    fun m => (flat_invL (e.run_eq m)).invC
  have hcur : ∀ m q, (curOf ((List.range m).map e.lbl) q).1 = q := fun _ _ => rfl
  have hstep : ∀ m ≥ n0, PiF p (e.cfg (m + 1)) ≤ PiF p (e.cfg m) ∧
      (e.lbl m = .tau p → PiF p (e.cfg (m + 1)) < PiF p (e.cfg m)) := by
    intro m hm
    have hs := e.step_eq m
    rcases hl : e.lbl m with ⟨q, o⟩ | ⟨q, r⟩ | q
    · rw [hl] at hs
      by_cases hq : q = p
      · subst hq; exact absurd (Impl.step_inv hs).1 (hpend m hm)
      · exact ⟨PiF_other (hcur m) (hinv m) hs hq, fun h => by cases h⟩
    · rw [hl] at hs
      by_cases hq : q = p
      · subst hq
        have := (Impl.step_ret hs).2.1
        exact absurd (by rw [this]; simp) (hpend (m + 1) (by omega))
      · exact ⟨PiF_other (hcur m) (hinv m) hs hq, fun h => by cases h⟩
    · rw [hl] at hs
      by_cases hq : q = p
      · subst hq
        have := PiF_self (hinv m) hs
        exact ⟨this.le, fun _ => this⟩
      · exact ⟨PiF_other (hcur m) (hinv m) hs hq, fun h => by cases h; exact absurd rfl hq⟩
  have hmono : ∀ d m, n0 ≤ m → PiF p (e.cfg (m + d)) ≤ PiF p (e.cfg m) := by
    intro d; induction d with
    | zero => intro m _; exact le_rfl
    | succ d ih =>
      intro m hm
      exact (hstep (m + d) (by omega)).1.trans (ih m hm)
  by_contra hcon
  push Not at hcon
  have key : ∀ k, ∃ m ≥ n0, PiF p (e.cfg m) + k ≤ PiF p (e.cfg n0) := by
    intro k; induction k with
    | zero => exact ⟨n0, le_rfl, by simp⟩
    | succ k ih =>
      obtain ⟨m, hm, hk⟩ := ih
      obtain ⟨m', hm', hl⟩ := hcon m
      have h1 := (hstep m' (by omega)).2 hl
      have h2 := hmono (m' - m) m hm
      rw [show m + (m' - m) = m' by omega] at h2
      exact ⟨m' + 1, by omega, by omega⟩
  obtain ⟨m, -, hk⟩ := key (PiF p (e.cfg n0) + 1)
  omega

end Universal

end Cslib.SharedMemory

namespace Cslib.SharedMemory

namespace Universal

variable {A : ObjSpec} {n : ℕ} [DecidablePred A.ReadOnly]

/-- **Theorem 32** of Attiya, Bender, Farach-Colton, Oshman, Schiller (PODC 2024): Algorithm 5,
with its R-LLSC objects implemented by Algorithm 6 (flattened into one implementation from `n + 1`
atomic CAS objects, with the strict-alternation schedule for `∥`), is a linearizable, wait-free,
state-quiescent history-independent implementation of the arbitrary object `A`. -/
theorem theorem32 : (flat A n).Linearizable ∧ (flat A n).WaitFree ∧ (flat A n).StateQuiescentHI :=
  ⟨⟨_, flat_isLinFun⟩, flat_waitFree, flat_stateQuiescentHI⟩

end Universal

end Cslib.SharedMemory
