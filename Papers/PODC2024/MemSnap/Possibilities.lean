import Papers.PODC2024.MemSnap.Forwarding

/-!
# The Possibilities Invariant `I₂` (Figure 2, Lemma 7.2)

* `pstar C` — the base possibility `p*`: `(val, snap) = (A, B.val)`, and a process is linearized
  iff it is at a return statement (lines 2, 5, 8), with the response it is about to return.
* `QSet fixed C G` — the set `Q` of Figure 2. With `fixed = false` it is the set *as printed*;
  with `fixed = true` the third disjunct (a process `μ` about to perform a successful CAS at
  line 12 with value `a_μ`) additionally requires `x_μ = X`, i.e. that the CAS will make
  `B[j].seq` equal to `X`, as the text before Lemma 7.2 says ("a successful CAS at Line 12 that
  will cause `B[j].seq` to become equal to `X`").
* `lemma_7_2_fixed` — **Lemma 7.2, corrected**: `Q ⊆ P ∧ Q ≠ ∅` is an invariant of Algorithm 2
  for the corrected `Q`. (For `Q` as printed the lemma is false, see `Counterexample.lean`.)
-/

set_option linter.unusedSectionVars false

namespace Podc.MemSnap

open Cslib.SharedMemory

variable {W : ObjSpec} {K : Type} [DecidableEq K] {v₀ : K → W.State}
variable {P : Type} [DecidableEq P] {σ : P}

/-! ## Linearizing sequences of updates -/

section LinSeq

variable {ops : P → Option (COp W K)}

/-- All processes of `l` have pending updates. -/
def AllUpd (ops : P → Option (COp W K)) (l : List P) : Prop :=
  ∀ π ∈ l, ∃ i o, ops π = some (.update i o)

/-- No process of `l` has a pending update on component `j`. -/
def AvoidComp (ops : P → Option (COp W K)) (l : List P) (j : K) : Prop :=
  ∀ π ∈ l, ∀ i o, ops π = some (.update i o) → i ≠ j

@[simp] lemma lin_update_st_val (p : CPoss W K v₀ P) (π : P) (i : K) (o : W.Op) :
    (p.lin π (.update i o)).st.val = Function.update p.st.val i (W.δ (p.st.val i) o).1 := rfl

@[simp] lemma lin_update_st_snap (p : CPoss W K v₀ P) (π : P) (i : K) (o : W.Op) :
    (p.lin π (.update i o)).st.snap = p.st.snap := rfl

@[simp] lemma lin_update_fl (p : CPoss W K v₀ P) (π : P) (i : K) (o : W.Op) :
    (p.lin π (.update i o)).fl = Function.update p.fl π (some (.upd (W.δ (p.st.val i) o).2)) :=
  rfl

lemma linSeq_cons_upd (p : CPoss W K v₀ P) {π : P} {i : K} {o : W.Op}
    (h : ops π = some (.update i o)) (l : List P) :
    p.linSeq ops (π :: l) = (p.lin π (.update i o)).linSeq ops l := Poss.linSeq_cons_some p h l

/-- (S3) Flags of processes outside `l` are unchanged. -/
lemma linSeq_fl_not_mem (p : CPoss W K v₀ P) {l : List P} {π : P} (h : π ∉ l) :
    (p.linSeq ops l).fl π = p.fl π := by
  induction l generalizing p with
  | nil => rfl
  | cons π' l ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [Poss.linSeq]
    rw [ih _ h.2]
    split <;> simp [Poss.lin, Function.update_of_ne h.1]

/-- (S2) Components that no update of `l` touches keep their value. -/
lemma linSeq_val_of_avoid (p : CPoss W K v₀ P) {l : List P} {j : K}
    (hU : AllUpd ops l) (hA : AvoidComp ops l j) :
    (p.linSeq ops l).st.val j = p.st.val j := by
  induction l generalizing p with
  | nil => rfl
  | cons π l ih =>
    obtain ⟨i, o, ho⟩ := hU π (by simp)
    rw [linSeq_cons_upd p ho, ih _ (fun π' h => hU π' (by simp [h]))
      (fun π' h => hA π' (by simp [h]))]
    simp [Function.update_of_ne (hA π (by simp) i o ho).symm]

/-- (S4) The values and flags after linearizing updates depend only on the values and flags. -/
lemma linSeq_congr {p p' : CPoss W K v₀ P} {l : List P} (hU : AllUpd ops l)
    (hv : p.st.val = p'.st.val) (hf : p.fl = p'.fl) :
    (p.linSeq ops l).st.val = (p'.linSeq ops l).st.val ∧
      (p.linSeq ops l).fl = (p'.linSeq ops l).fl := by
  induction l generalizing p p' with
  | nil => exact ⟨hv, hf⟩
  | cons π l ih =>
    obtain ⟨i, o, ho⟩ := hU π (by simp)
    rw [linSeq_cons_upd p ho, linSeq_cons_upd p' ho]
    exact ih (fun π' h => hU π' (by simp [h])) (by simp [hv]) (by simp [hf, hv])

/-- (S7) Changing the flag of a process outside `l` commutes with linearizing `l`. -/
lemma linSeq_set_fl {st : CState W K} {fl : P → Option (CResp W)} {l : List P} {π : P}
    (h : π ∉ l) (v : Option (CResp W)) :
    (⟨st, Function.update fl π v⟩ : CPoss W K v₀ P).linSeq ops l =
      ⟨((⟨st, fl⟩ : CPoss W K v₀ P).linSeq ops l).st,
        Function.update ((⟨st, fl⟩ : CPoss W K v₀ P).linSeq ops l).fl π v⟩ := by
  induction l generalizing st fl with
  | nil => rfl
  | cons π' l ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [Poss.linSeq]
    split
    · simp only [Poss.lin]
      rw [Function.update_comm h.1]
      exact ih h.2
    · exact ih h.2

/-- (S6) Only the operations of the processes in `l` matter. -/
lemma linSeq_ops_congr {ops' : P → Option (COp W K)} (p : CPoss W K v₀ P) {l : List P}
    (h : ∀ π ∈ l, ops π = ops' π) : p.linSeq ops l = p.linSeq ops' l := by
  induction l generalizing p with
  | nil => rfl
  | cons π l ih =>
    simp only [Poss.linSeq]
    rw [h π (by simp)]
    exact ih _ (fun π' h' => h π' (by simp [h']))

/-- (S5) An update on component `i` commutes with updates of `l` on other components. -/
lemma linSeq_lin_comm (p : CPoss W K v₀ P) {l : List P} {π : P} {i : K} {o : W.Op}
    (hπ : π ∉ l) (hU : AllUpd ops l) (hA : AvoidComp ops l i) :
    (p.lin π (.update i o)).linSeq ops l = (p.linSeq ops l).lin π (.update i o) := by
  induction l generalizing p with
  | nil => rfl
  | cons π' l ih =>
    simp only [List.mem_cons, not_or] at hπ
    obtain ⟨i', o', ho⟩ := hU π' (by simp)
    have hii : i' ≠ i := hA π' (by simp) i' o' ho
    rw [linSeq_cons_upd _ ho, linSeq_cons_upd _ ho]
    rw [← ih _ hπ.2 (fun π'' h => hU π'' (by simp [h])) (fun π'' h => hA π'' (by simp [h]))]
    congr 1
    ext1
    · ext1
      · simp only [lin_update_st_val]
        rw [Function.update_of_ne hii, Function.update_of_ne hii.symm,
          Function.update_comm hii]
      · rfl
    · simp only [lin_update_fl, lin_update_st_val, Function.update_of_ne hii,
        Function.update_of_ne hii.symm]
      exact Function.update_comm hπ.1 _ _ _

end LinSeq

/-! ## The set `Q` of Figure 2 -/

/-- The flag of a process in the base possibility `p*`: `ack` at line 2, `r_π` at lines 5, 8. -/
def Loc.flag : Loc W K → Option (CResp W)
  | .c2 => some .ack
  | .o5 v => some (.obs v)
  | .u8 r => some (.upd r)
  | _ => none

/-- The component `i_π` of the current operation (where the local state records it). -/
def Loc.comp : Loc W K → Option K
  | .f9 i _ _ => some i
  | .f10 i _ _ _ => some i
  | .f11 i _ _ _ _ => some i
  | .f12 i _ _ _ _ _ => some i
  | .o4 i => some i
  | .u7 i _ => some i
  | _ => none

/-- The base possibility `p*` of Figure 2: `(val, snap) = (A, B.val)`, flags `ack` at line 2,
`r_π` at lines 5 and 8, `⊥` otherwise. -/
def pstar (C : Cfg W K v₀ P) : CPoss W K v₀ P :=
  ⟨⟨fun j => C.A j, fun j => (C.B j).1⟩, fun π => (C.loc π).flag⟩

variable (σ) in
/-- `UnLin(p*) ∩ {π ∈ Π | x̂_π < X}`: updaters with an ongoing update that started before the
latest click. -/
def Cand (C : Cfg W K v₀ P) (G : Ghost W K v₀ P) (π : P) : Prop :=
  π ∈ UnLin σ C (pstar C) ∧ G.xh π < C.X

/-- The three disjuncts of Figure 2 for component `j`, for the sequence `l` (the permutation `α`
of `S`). With `fixed = true` the third disjunct also requires `x_μ = X`. -/
def SnapCase (fixed : Bool) (C : Cfg W K v₀ P) (l : List P) (p : CPoss W K v₀ P) (j : K) :
    Prop :=
  ((C.B j).2 = C.X ∧ (∀ π ∈ l, (C.loc π).comp ≠ some j) ∧ p.st.snap j = (C.B j).1) ∨
  ((C.B j).2 ≠ C.X ∧ p.st.snap j = p.st.val j) ∨
  ((C.B j).2 ≠ C.X ∧ (∀ π ∈ l, (C.loc π).comp ≠ some j) ∧
    ∃ μ u k b x a, C.loc μ = .f12 j u k b x a ∧ b = C.B j ∧ (fixed = true → x = C.X) ∧
      p.st.snap j = a)

variable (σ) in
/-- The set `Q` of Figure 2 (`fixed = false`: as printed; `fixed = true`: corrected). -/
def QSet (fixed : Bool) (C : Cfg W K v₀ P) (G : Ghost W K v₀ P) : Set (CPoss W K v₀ P) :=
  {p | ∃ l : List P, l.Nodup ∧ (∀ π ∈ l, Cand σ C G π) ∧ ∃ q, TransOK C (pstar C) l q ∧
    p.st.val = q.st.val ∧ (∀ π, p.fl π = q.fl π) ∧ ∀ j, SnapCase fixed C l p j}

variable (σ) in
/-- Membership in `Q` with a fixed sequence `l`, with `TransitionsOK` unfolded. -/
def QMem (fixed : Bool) (C : Cfg W K v₀ P) (G : Ghost W K v₀ P) (l : List P)
    (p : CPoss W K v₀ P) : Prop :=
  l.Nodup ∧ (∀ π ∈ l, Cand σ C G π) ∧ p.st.val = ((pstar C).linSeq C.pend l).st.val ∧
    p.fl = ((pstar C).linSeq C.pend l).fl ∧ ∀ j, SnapCase fixed C l p j

section QBasics

variable {C : Cfg W K v₀ P} {G : Ghost W K v₀ P}

lemma cand_loc (hI : FInv σ C G) {π : P} (h : Cand σ C G π) :
    ∃ i o, C.pend π = some (.update i o) ∧ (C.loc π).comp = some i ∧ (C.loc π).flag = none ∧
      π ≠ σ := by
  obtain ⟨⟨hσ, hU, hfl⟩, -⟩ := h
  have hsh := hI.shape π
  change (C.loc π).flag = none at hfl
  cases hl : C.loc π with
  | f9 i u k | f10 i u k _ | f11 i u k _ _ | f12 i u k _ _ _ =>
    rw [hl] at hsh hU
    cases u with
    | none => simp [Loc.IsUpd] at hU
    | some o => exact ⟨i, o, hsh.2, rfl, rfl, hσ⟩
  | u7 i o => rw [hl] at hsh; exact ⟨i, o, hsh.2, rfl, rfl, hσ⟩
  | u8 r => rw [hl] at hfl; simp [Loc.flag] at hfl
  | _ => rw [hl] at hU; simp [Loc.IsUpd] at hU

lemma allUpd_of_cand (hI : FInv σ C G) {l : List P} (h : ∀ π ∈ l, Cand σ C G π) :
    AllUpd C.pend l := fun π hπ => by
  obtain ⟨i, o, ho, -⟩ := cand_loc hI (h π hπ); exact ⟨i, o, ho⟩

lemma avoid_of_cand (hI : FInv σ C G) {l : List P} (h : ∀ π ∈ l, Cand σ C G π) {j : K}
    (hj : ∀ π ∈ l, (C.loc π).comp ≠ some j) : AvoidComp C.pend l j := by
  intro π hπ i o ho
  obtain ⟨i', o', ho', hc, -⟩ := cand_loc hI (h π hπ)
  rw [ho] at ho'; cases ho'
  intro hij; subst hij; exact hj π hπ hc

lemma mem_QSet_iff (hI : FInv σ C G) {fixed : Bool} {p : CPoss W K v₀ P} :
    p ∈ QSet σ fixed C G ↔ ∃ l, QMem σ fixed C G l p := by
  constructor
  · rintro ⟨l, hnd, hc, q, ⟨-, -, rfl⟩, hv, hf, hs⟩
    exact ⟨l, hnd, hc, hv, funext hf, hs⟩
  · rintro ⟨l, hnd, hc, hv, hf, hs⟩
    refine ⟨l, hnd, hc, _, ⟨hnd, fun π hπ => ?_, rfl⟩, hv, fun π => by rw [hf], hs⟩
    obtain ⟨i, o, ho, -, hfl, -⟩ := cand_loc hI (hc π hπ)
    exact ⟨by rw [ho]; simp, hfl⟩

open Classical in
/-- The canonical element of `Q`: `S = ∅`, and for each component the first or second disjunct. -/
noncomputable def qcanon (C : Cfg W K v₀ P) : CPoss W K v₀ P :=
  ⟨⟨fun j => C.A j, fun j => if (C.B j).2 = C.X then (C.B j).1 else C.A j⟩,
    fun π => (C.loc π).flag⟩

lemma qcanon_mem (fixed : Bool) : QMem σ fixed C G [] (qcanon C) := by
  refine ⟨by simp, by simp, rfl, rfl, fun j => ?_⟩
  by_cases h : (C.B j).2 = C.X
  · left; simp [qcanon, h]
  · right; left; simp [qcanon, h]

/-- `Q ≠ ∅`. -/
lemma QSet_nonempty (hI : FInv σ C G) (fixed : Bool) : (QSet σ fixed C G).Nonempty :=
  ⟨qcanon C, (mem_QSet_iff hI).2 ⟨[], qcanon_mem fixed⟩⟩

end QBasics

/-! ## Transfer lemmas -/

section Transfer

variable {C C' : Cfg W K v₀ P} {G G' : Ghost W K v₀ P}

lemma pstar_val (C : Cfg W K v₀ P) : (pstar C).st.val = fun j => C.A j := rfl
lemma pstar_snap (C : Cfg W K v₀ P) : (pstar C).st.snap = fun j => (C.B j).1 := rfl
lemma pstar_fl (C : Cfg W K v₀ P) : (pstar C).fl = fun π => (C.loc π).flag := rfl

/-- The value of an avoided component in a member of `Q` is `A[j]`. -/
lemma QMem.val_of_avoid (hI : FInv σ C G) {fixed : Bool} {l : List P} {p : CPoss W K v₀ P}
    (hm : QMem σ fixed C G l p) {j : K} (hj : ∀ π ∈ l, (C.loc π).comp ≠ some j) :
    p.st.val j = C.A j := by
  rw [hm.2.2.1, linSeq_val_of_avoid _ (allUpd_of_cand hI hm.2.1) (avoid_of_cand hI hm.2.1 hj)]
  rfl

/-- Generic transfer of membership in `Q` from `C'` back to `C` with the same sequence `l`. -/
lemma qmem_transfer (hI : FInv σ C G) {l : List P} {p : CPoss W K v₀ P}
    (hm : QMem σ true C' G' l p) (hcand : ∀ π ∈ l, Cand σ C G π)
    (hpend : ∀ π ∈ l, C'.pend π = C.pend π)
    (hval : (pstar C').st.val = (pstar C).st.val) (hfl : (pstar C').fl = (pstar C).fl)
    (hsnap : ∀ j, SnapCase true C' l p j → SnapCase true C l p j) : QMem σ true C G l p := by
  obtain ⟨hnd, -, hv, hf, hs⟩ := hm
  have hU := allUpd_of_cand hI hcand
  rw [linSeq_ops_congr _ hpend] at hv hf
  have := linSeq_congr (ops := C.pend) (p := pstar C') (p' := pstar C) hU hval hfl
  exact ⟨hnd, hcand, hv.trans this.1, hf.trans this.2, fun j => hsnap j (hs j)⟩

/-- Transfer for a step of `π` that changes neither memory nor the base possibility, and in
which `π` reaches line 12 only with `a = A[i]`. -/
lemma qmem_local (hI : FInv σ C G) {l : List P} {p : CPoss W K v₀ P}
    (hm : QMem σ true C' G' l p) {π : P} (l' : Loc W K)
    (hmem : C'.mem = C.mem) (hloc : C'.loc = Function.update C.loc π l')
    (hpend : ∀ π' ∈ l, C'.pend π' = C.pend π') (hxh : ∀ π' ∈ l, G'.xh π' = G.xh π')
    (hU : π ∈ l → l'.IsUpd → (C.loc π).IsUpd) (hcomp : π ∈ l → l'.comp = (C.loc π).comp)
    (hflag : l'.flag = (C.loc π).flag)
    (hw : ∀ j u k b x a, l' = .f12 j u k b x a → C.loc π = .f12 j u k b x a ∨ a = C.A j) :
    QMem σ true C G l p := by
  have hX : C'.X = C.X := by simp [Cfg.X, hmem]
  have hB : ∀ j, C'.B j = C.B j := by simp [Cfg.B, hmem]
  have hA : ∀ j, C'.A j = C.A j := by simp [Cfg.A, hmem]
  have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by
    rw [hloc, Function.update_of_ne h]
  have hlocπ : C'.loc π = l' := by rw [hloc]; simp
  have hfl : (pstar C').fl = (pstar C).fl := by
    funext ν; simp only [pstar_fl]
    by_cases hν : ν = π
    · subst hν; rw [hlocπ, hflag]
    · rw [hlocν ν hν]
  have hcomp' : ∀ ν ∈ l, (C'.loc ν).comp = (C.loc ν).comp := fun ν hν => by
    by_cases h : ν = π
    · subst h; rw [hlocπ]; exact hcomp hν
    · rw [hlocν ν h]
  have hcand : ∀ ν ∈ l, Cand σ C G ν := by
    intro ν hν
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hm.2.1 ν hν
    refine ⟨⟨h1, ?_, ?_⟩, ?_⟩
    · by_cases h : ν = π
      · subst h; rw [hlocπ] at h2; exact hU hν h2
      · rwa [hlocν ν h] at h2
    · rw [← hfl]; exact h3
    · rw [← hxh ν hν, ← hX]; exact h4
  have hv0 : p.st.val = ((pstar C).linSeq C.pend l).st.val := by
    rw [hm.2.2.1, linSeq_ops_congr _ hpend]
    exact (linSeq_congr (allUpd_of_cand hI hcand) (by funext j; simp [pstar_val, hA]) hfl).1
  refine qmem_transfer hI hm hcand hpend (by funext j; simp [pstar_val, hA]) hfl (fun j h => ?_)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, μ, u, k, b, x, a, h3, h4, h5, h6⟩
  · left; rw [hB, hX] at *
    exact ⟨h1, fun ν hν => (hcomp' ν hν) ▸ h2 ν hν, h3⟩
  · right; left; rw [hB, hX] at h1; exact ⟨h1, h2⟩
  · have h2' : ∀ ν ∈ l, (C.loc ν).comp ≠ some j := fun ν hν => (hcomp' ν hν) ▸ h2 ν hν
    simp only [hB, hX] at h1 h4 h5
    by_cases hμ : μ = π
    · subst hμ; rw [hlocπ] at h3
      rcases hw _ _ _ _ _ _ h3 with h3' | ha
      · right; right; exact ⟨h1, h2', μ, u, k, b, x, a, h3', h4, fun _ => h5 trivial, h6⟩
      · right; left
        refine ⟨h1, ?_⟩
        rw [h6, ha, hv0,
          linSeq_val_of_avoid _ (allUpd_of_cand hI hcand) (avoid_of_cand hI hcand h2')]
        rfl
    · rw [hlocν μ hμ] at h3
      right; right; exact ⟨h1, h2', μ, u, k, b, x, a, h3, h4, fun _ => h5 trivial, h6⟩

end Transfer

/-! ## Lemma 7.2 (corrected) -/

section Step

variable {C C' : Cfg W K v₀ P} {G G' : Ghost W K v₀ P}

/-- Snapshot cases transfer along a step of `π ∉ l` that keeps `X`, `B[j]`, the other local
states, and in which `π` is not at line 12 afterwards. -/
lemma snap_frame {π : P} {l l0 : List P} {p p0 : CPoss W K v₀ P} {j : K}
    (hX : C'.X = C.X) (hB : C'.B j = C.B j) (hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν)
    (hπ12 : ∀ u k b x a, C'.loc π ≠ .f12 j u k b x a) (hπl : π ∉ l)
    (hl0 : ∀ ν ∈ l0, ν ∈ l ∨ (ν ∉ l ∧ (C.loc ν).comp ≠ some j))
    (hs0 : p0.st.snap j = p.st.snap j) (hv0 : p0.st.val j = p.st.val j)
    (h : SnapCase true C' l p j) : SnapCase true C l0 p0 j := by
  have hc : ∀ ν ∈ l0, (∀ ν ∈ l, (C'.loc ν).comp ≠ some j) → (C.loc ν).comp ≠ some j := by
    intro ν hν h2
    rcases hl0 ν hν with h1 | ⟨-, h1⟩
    · have := h2 ν h1
      rwa [hlocν ν (fun he => hπl (he ▸ h1))] at this
    · exact h1
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, μ, u, k, b, x, a, h3, h4, h5, h6⟩
  · left; rw [hB, hX] at h1; rw [hB] at h3
    exact ⟨h1, fun ν hν => hc ν hν h2, hs0.trans h3⟩
  · right; left; rw [hB, hX] at h1; exact ⟨h1, by rw [hs0, hv0, h2]⟩
  · right; right
    have hμ : μ ≠ π := by rintro rfl; exact hπ12 u k b x a h3
    rw [hlocν μ hμ] at h3
    simp only [hB, hX] at h1 h4 h5
    exact ⟨h1, fun ν hν => hc ν hν h2, μ, u, k, b, x, a, h3, h4, fun _ => h5 trivial, hs0.trans h6⟩

lemma cand_frame {π ν : P} (hνπ : ν ≠ π) (hX : C'.X = C.X)
    (hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν) (hxh : G'.xh ν = G.xh ν)
    (h : Cand σ C' G' ν) : Cand σ C G ν := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  change (C'.loc ν).flag = none at h3
  rw [hlocν ν hνπ] at h2 h3
  exact ⟨⟨h1, h2, h3⟩, by rw [← hxh, ← hX]; exact h4⟩

lemma not_mem_of_flag {fixed : Bool} {l : List P} {p : CPoss W K v₀ P}
    (hm : QMem σ fixed C G l p) {π : P} (h : (C.loc π).flag ≠ none) : π ∉ l :=
  fun hπ => h (hm.2.1 π hπ).1.2.2

lemma not_mem_of_not_upd {fixed : Bool} {l : List P} {p : CPoss W K v₀ P}
    (hm : QMem σ fixed C G l p) {π : P} (h : ¬ (C.loc π).IsUpd) : π ∉ l :=
  fun hπ => h (hm.2.1 π hπ).1.2.1

/-- Lemma 7.2 for the step at line 1 (the write `X ← X + 1`). -/
lemma QSub.c1w (hI : FInv σ C G) (hQ : QSet σ true C G ⊆ G.PP) {π : P} {x : ℕ}
    (hl : C.loc π = .c1w x) (hst : (memSnap W K v₀ σ).step C (.tau π) = some C')
    {l : List P} {p : CPoss W K v₀ P} (hm : QMem σ true C' (augStep σ C (.tau π) G) l p) :
    p ∈ (augStep σ C (.tau π) G).PP := by
  obtain ⟨hp, hX, hA, hB, hloc⟩ := tau_c1w hst hl
  have hσ : π = σ := (hl ▸ hI.shape π).1
  have hx := hI.c1w_x π x hl
  have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by rw [hloc, Function.update_of_ne h]
  have hlocπ : C'.loc π = .c2 := by rw [hloc]; simp
  simp only [augStep, hl]
  refine ⟨qcanon C, hQ ((mem_QSet_iff hI).2 ⟨[], qcanon_mem true⟩), l, ?_, ?_⟩
  · intro ν hν
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := hm.2.1 ν hν
    have hνπ : ν ≠ π := hσ ▸ h1
    change (C'.loc ν).flag = none at h3
    rw [hlocν ν hνπ] at h2 h3
    exact ⟨h1, h2, h3⟩
  have hπl : π ∉ l := not_mem_of_flag hm (by rw [hlocπ]; simp [Loc.flag])
  have hU : AllUpd C.pend l := fun ν hν => by
    obtain ⟨i, o, ho, -⟩ := cand_loc (hI.step hst) (hm.2.1 ν hν); exact ⟨i, o, hp ▸ ho⟩
  have hpendπ : C.pend π = some .click := (hl ▸ hI.shape π).2
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_append]; exact ⟨hm.1, by simp, by simp; exact fun a ha he => hπl (he ▸ ha)⟩
  · intro ν hν
    rcases List.mem_append.1 hν with hν | hν
    · obtain ⟨i, o, ho, -, hfl, -⟩ := cand_loc (hI.step hst) (hm.2.1 ν hν)
      have hνπ : ν ≠ π := fun h => hπl (h ▸ hν)
      refine ⟨by rw [← hp, ho]; simp, ?_⟩
      change (C.loc ν).flag = none; rw [← hlocν ν hνπ]; exact hfl
    · simp only [List.mem_singleton] at hν; subst hν
      exact ⟨by rw [hpendπ]; simp, by change (C.loc ν).flag = none; rw [hl]; rfl⟩
  · -- the main equation
    rw [Poss.linSeq_append, Poss.linSeq_cons_some _ hpendπ, Poss.linSeq_nil]
    have hps : pstar C' = ⟨⟨fun j => C.A j, fun j => (C.B j).1⟩,
        Function.update (pstar C).fl π (some .ack)⟩ := by
      ext1
      · ext1 <;> funext j <;> simp [pstar, hA, hB]
      · funext ν; simp only [pstar_fl]
        by_cases hν : ν = π
        · subst hν; rw [hlocπ]; simp [Loc.flag]
        · rw [hlocν ν hν, Function.update_of_ne hν]
    have hv := hm.2.2.1; have hf := hm.2.2.2.1
    rw [hps, linSeq_ops_congr _ (fun ν _ => by rw [hp]), linSeq_set_fl hπl] at hv hf
    have hc := linSeq_congr (ops := C.pend) (p := ⟨⟨fun j => C.A j, fun j => (C.B j).1⟩,
      (pstar C).fl⟩) (p' := qcanon C) hU rfl rfl
    rw [hc.1] at hv; rw [hc.2] at hf
    have hsnap : p.st.snap = p.st.val := by
      funext j
      rcases hm.2.2.2.2 j with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, -, μ, u, k, b, y, a, h3, -, h5, -⟩
      · rw [hB, hX, hx] at h1; have := hI.seq_le j; omega
      · exact h2
      · have hμ : μ ≠ π := by rintro rfl; rw [hlocπ] at h3; cases h3
        rw [hlocν μ hμ] at h3
        have := (hI.poised μ j b y (by rw [h3]; rfl)).2.1
        rw [h5 rfl, hX, hx] at this; omega
    ext1
    · ext1
      · exact hv
      · rw [hsnap, hv]; rfl
    · rw [hf]; rfl

/-- A step that changes only the local state and flag of `π ∉ l` (and possibly its pending
operation), not the memory: membership in `Q` transfers, with the flag of `π` replaced. -/
lemma qmem_flag_frame {π : P} {l : List P} {p : CPoss W K v₀ P}
    (hm : QMem σ true C' G' l p) (hπl : π ∉ l) (hmem : C'.mem = C.mem)
    (hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν) (hpend : ∀ ν, ν ≠ π → C'.pend ν = C.pend ν)
    (hxh : ∀ ν, ν ≠ π → G'.xh ν = G.xh ν)
    (hπ12 : ∀ j u k b x a, C'.loc π ≠ .f12 j u k b x a) :
    QMem σ true C G l ⟨p.st, Function.update p.fl π (C.loc π).flag⟩ := by
  have hX : C'.X = C.X := by simp [Cfg.X, hmem]
  have hB : ∀ j, C'.B j = C.B j := by simp [Cfg.B, hmem]
  have hA : ∀ j, C'.A j = C.A j := by simp [Cfg.A, hmem]
  have hne : ∀ ν ∈ l, ν ≠ π := fun ν hν h => hπl (h ▸ hν)
  have hcand : ∀ ν ∈ l, Cand σ C G ν := fun ν hν =>
    cand_frame (hne ν hν) hX hlocν (hxh ν (hne ν hν)) (hm.2.1 ν hν)
  have hps : pstar C = ⟨(pstar C').st, Function.update (pstar C').fl π (C.loc π).flag⟩ := by
    ext1
    · ext1 <;> funext j <;> simp [pstar, hA, hB]
    · funext ν; simp only [pstar_fl]
      by_cases hν : ν = π
      · subst hν; simp
      · rw [Function.update_of_ne hν, hlocν ν hν]
  have hops : ∀ ν ∈ l, C.pend ν = C'.pend ν := fun ν hν => (hpend ν (hne ν hν)).symm
  refine ⟨hm.1, hcand, ?_, ?_, fun j => ?_⟩
  · rw [hps, linSeq_ops_congr _ hops, linSeq_set_fl hπl]; exact hm.2.2.1
  · rw [hps, linSeq_ops_congr _ hops, linSeq_set_fl hπl]; simp only; rw [hm.2.2.2.1]
  · exact snap_frame hX (hB j) hlocν (fun u k b x a => hπ12 j u k b x a) hπl
      (fun ν hν => Or.inl hν) rfl rfl (hm.2.2.2.2 j)

/-- Lemma 7.2 for the step at line 4. -/
lemma QSub.o4 (hI : FInv σ C G) (hQ : QSet σ true C G ⊆ G.PP) {π : P} {i : K}
    (hl : C.loc π = .o4 i) (hst : (memSnap W K v₀ σ).step C (.tau π) = some C')
    {l : List P} {p : CPoss W K v₀ P} (hm : QMem σ true C' (augStep σ C (.tau π) G) l p) :
    p ∈ (augStep σ C (.tau π) G).PP := by
  obtain ⟨hp, hmem, hloc⟩ := tau_o4 hst hl
  have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by rw [hloc, Function.update_of_ne h]
  have hlocπ : C'.loc π = .o5 (C.B i).1 := by rw [hloc]; simp
  have hπl : π ∉ l := not_mem_of_flag hm (by rw [hlocπ]; simp [Loc.flag])
  have hm0 := qmem_flag_frame (G := G) hm hπl hmem hlocν (fun ν _ => by rw [hp])
    (fun ν _ => by rw [augStep_tau_xh]) (by rw [hlocπ]; simp)
  rw [hl] at hm0
  have hpendπ : C.pend π = some (.observe i) := (hl ▸ hI.shape π).2
  simp only [augStep, hl]
  refine ⟨_, hQ ((mem_QSet_iff hI).2 ⟨l, hm0⟩), by simp [Loc.flag], List.nodup_singleton π,
    fun ν hν => ?_, ?_⟩
  · simp only [List.mem_singleton] at hν; subst hν
    exact ⟨by rw [hpendπ]; simp, by simp [Loc.flag]⟩
  · rw [Poss.linSeq_cons_some _ hpendπ, Poss.linSeq_nil]
    have hflπ : p.fl π = some (.obs (C.B i).1) := by
      rw [hm.2.2.2.1, linSeq_fl_not_mem _ hπl, pstar_fl]; simp only [hlocπ, Loc.flag]
    have hsn : p.st.snap i = (C.B i).1 := by
      have h8 := hI.o4 π i hl
      have hX : C'.X = C.X := by simp [Cfg.X, hmem]
      have hB : C'.B i = C.B i := by simp [Cfg.B, hmem]
      rcases hm.2.2.2.2 i with ⟨-, -, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h3, hB]
      · rw [hB, hX] at h1; exact absurd h8 h1
      · rw [hB, hX] at h1; exact absurd h8 h1
    ext1
    · rfl
    · simp only [Poss.lin, Function.update_idem]
      rw [hsn, ← hflπ]; simp

/-- Lemma 7.2 for return steps (the filter rule at lines 2, 5, 8). -/
lemma QSub.ret (hI : FInv σ C G) (hQ : QSet σ true C G ⊆ G.PP) {π : P} {r : CResp W}
    (hst : (memSnap W K v₀ σ).step C (.ret π r) = some C')
    {l : List P} {p : CPoss W K v₀ P} (hm : QMem σ true C' (augStep σ C (.ret π r) G) l p) :
    p ∈ (augStep σ C (.ret π r) G).PP := by
  obtain ⟨hpn, hmem, hpend, hloc, hcases⟩ := ret_eq hst
  have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by rw [hloc, Function.update_of_ne h]
  have hlocπ : C'.loc π = .idle := by rw [hloc]; simp
  have hπl : π ∉ l := not_mem_of_not_upd hm (by rw [hlocπ]; simp [Loc.IsUpd])
  have hm0 := qmem_flag_frame (G := G) hm hπl hmem hlocν
    (fun ν h => by rw [hpend, Function.update_of_ne h]) (fun ν _ => rfl) (by rw [hlocπ]; simp)
  have hflag : (C.loc π).flag = some r := by
    rcases hcases with h | ⟨h, rfl⟩ | ⟨v, h, rfl⟩ | ⟨r', h, rfl⟩
    · have := hI.shape π; rw [h] at this; exact absurd this hpn
    all_goals rw [h]; rfl
  rw [hflag] at hm0
  refine ⟨_, hQ ((mem_QSet_iff hI).2 ⟨l, hm0⟩), by simp, ?_⟩
  have hflπ : p.fl π = none := by
    rw [hm.2.2.2.1, linSeq_fl_not_mem _ hπl, pstar_fl]; simp only [hlocπ, Loc.flag]
  ext1
  · rfl
  · simp only [Poss.clear, Function.update_idem]
    rw [← hflπ]; simp

/-- Lemma 7.2 for the step at line 7 (the explicit execution of an update). -/
lemma QSub.u7 (hI : FInv σ C G) (hQ : QSet σ true C G ⊆ G.PP) {π : P} {i : K} {o : W.Op}
    (hl : C.loc π = .u7 i o) (hst : (memSnap W K v₀ σ).step C (.tau π) = some C')
    {l : List P} {p : CPoss W K v₀ P} (hm : QMem σ true C' (augStep σ C (.tau π) G) l p) :
    p ∈ (augStep σ C (.tau π) G).PP := by
  obtain ⟨hp, hX, hA, hB, hloc⟩ := tau_u7 hst hl
  have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by rw [hloc, Function.update_of_ne h]
  have hlocπ : C'.loc π = .u8 (W.δ (C.A i) o).2 := by rw [hloc]; simp
  have hπl : π ∉ l := not_mem_of_flag hm (by rw [hlocπ]; simp [Loc.flag])
  have hsh : π ≠ σ ∧ C.pend π = some (.update i o) := by
    have := hI.shape π; rw [hl] at this; exact this
  have hne : ∀ ν ∈ l, ν ≠ π := fun ν hν h => hπl (h ▸ hν)
  have hcandC : ∀ ν ∈ l, Cand σ C G ν := fun ν hν =>
    cand_frame (hne ν hν) hX hlocν (by rw [augStep_tau_xh]) (hm.2.1 ν hν)
  have hU : AllUpd C.pend l := allUpd_of_cand hI hcandC
  have hops : ∀ ν ∈ l, C'.pend ν = C.pend ν := fun ν _ => by rw [hp]
  have hps : pstar C' = (pstar C).lin π (.update i o) := by
    ext1
    · ext1
      · funext j; simp only [pstar_val, lin_update_st_val, hA, Function.update_apply]
      · funext j; simp [pstar, hB]
    · funext ν; simp only [pstar_fl, lin_update_fl]
      by_cases hν : ν = π
      · subst hν; rw [hlocπ]; simp [Loc.flag, pstar]
      · rw [hlocν ν hν, Function.update_of_ne hν]
  have hv := hm.2.2.1
  have hf := hm.2.2.2.1
  rw [hps, linSeq_ops_congr _ hops] at hv hf
  have hcomp : ∀ ν ∈ l, (C'.loc ν).comp = (C.loc ν).comp := fun ν hν => by rw [hlocν ν (hne ν hν)]
  simp only [augStep, hl]
  -- the route via `trans(p, π)`: used when no process of `S` updates component `i`
  have key : (∀ ν ∈ l, (C'.loc ν).comp ≠ some i) →
      SnapCase true C l ⟨⟨((pstar C).linSeq C.pend l).st.val, p.st.snap⟩,
        ((pstar C).linSeq C.pend l).fl⟩ i →
      p ∈ G.PP ∪ {p' | ∃ p ∈ G.PP, p.fl π = none ∧ TransOK C p [π] p'} := by
    intro hav hsc
    have havoid : AvoidComp C.pend l i :=
      avoid_of_cand hI hcandC (fun ν hν => (hcomp ν hν) ▸ hav ν hν)
    rw [linSeq_lin_comm _ hπl hU havoid] at hv hf
    set q := (pstar C).linSeq C.pend l with hq
    right
    refine ⟨⟨⟨q.st.val, p.st.snap⟩, q.fl⟩, hQ ((mem_QSet_iff hI).2 ⟨l, hm.1, hcandC, rfl, rfl,
      fun j => ?_⟩), ?_, List.nodup_singleton π, fun ν hν => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; exact hsc
      · refine snap_frame (p := p) hX (hB j) hlocν (by rw [hlocπ]; simp) hπl
          (fun ν hν => Or.inl hν) rfl ?_ (hm.2.2.2.2 j)
        rw [hv]; simp [Function.update_of_ne hj]
    · show q.fl π = none
      rw [hq, linSeq_fl_not_mem _ hπl, pstar_fl]; simp only [hl, Loc.flag]
    · simp only [List.mem_singleton] at hν; subst hν
      refine ⟨by rw [hsh.2]; simp, ?_⟩
      show q.fl ν = none
      rw [hq, linSeq_fl_not_mem _ hπl, pstar_fl]; simp only [hl, Loc.flag]
    · rw [Poss.linSeq_cons_some _ hsh.2, Poss.linSeq_nil]
      ext1
      · ext1
        · rw [hv]; rfl
        · rfl
      · rw [hf]; rfl
  rcases hm.2.2.2.2 i with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, μ, u, k, b, x, a, h3, h4, h5, h6⟩
  · refine key h2 (Or.inl ⟨by rw [← hB, ← hX]; exact h1, fun ν hν => (hcomp ν hν) ▸ h2 ν hν,
      by rw [h3, hB]⟩)
  · -- the route `S ∪ {π}`: `π` linearizes just before the latest click
    left
    rw [hB, hX] at h1
    have hxπ : G.xh π < C.X :=
      lt_of_le_of_ne ((hI.u7 π i o hl).trans (hI.seq_le i)) (fun h => h1 (le_antisymm
        (hI.seq_le i) (h ▸ hI.u7 π i o hl)))
    refine hQ ((mem_QSet_iff hI).2 ⟨π :: l, List.nodup_cons.2 ⟨hπl, hm.1⟩, ?_, ?_, ?_,
      fun j => ?_⟩)
    · intro ν hν
      rcases List.mem_cons.1 hν with rfl | hν
      · exact ⟨⟨hsh.1, by rw [hl]; trivial, by rw [pstar_fl]; simp only [hl, Loc.flag]⟩, hxπ⟩
      · exact hcandC ν hν
    · rw [Poss.linSeq_cons_some _ hsh.2]; exact hv
    · rw [Poss.linSeq_cons_some _ hsh.2]; exact hf
    · by_cases hj : j = i
      · subst hj; right; left; exact ⟨h1, h2⟩
      · refine snap_frame hX (hB j) hlocν (by rw [hlocπ]; simp) hπl (fun ν hν => ?_) rfl rfl
          (hm.2.2.2.2 j)
        rcases List.mem_cons.1 hν with rfl | hν
        · right; exact ⟨hπl, by rw [hl]; simp [Loc.comp, Ne.symm hj]⟩
        · left; exact hν
  · have hμ : μ ≠ π := by rintro rfl; rw [hlocπ] at h3; cases h3
    rw [hlocν μ hμ] at h3
    simp only [hB, hX] at h1 h4 h5
    exact key h2 (Or.inr (Or.inr ⟨h1, fun ν hν => (hcomp ν hν) ▸ h2 ν hν, μ, u, k, b, x, a, h3,
      h4, fun _ => h5 trivial, h6⟩))

/-- Lemma 7.2 for a successful CAS at line 12. -/
lemma QSub.cas_succ (hI : FInv σ C G) (hQ : QSet σ true C G ⊆ G.PP) {π : P} {i : K}
    {u : Option W.Op} {k : Bool} {b : W.State × ℕ} {x : ℕ} {a : W.State}
    (hl : C.loc π = .f12 i u k b x a) (hb : C.B i = b)
    (hst : (memSnap W K v₀ σ).step C (.tau π) = some C')
    {l : List P} {p : CPoss W K v₀ P} (hm : QMem σ true C' (augStep σ C (.tau π) G) l p) :
    p ∈ (augStep σ C (.tau π) G).PP := by
  obtain ⟨hp, hX, hA, hB, hloc⟩ := tau_f12_succ hst hl hb
  have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by rw [hloc, Function.update_of_ne h]
  have hlocπ : C'.loc π = fcont i u := by rw [hloc]; simp
  have hpo := hI.poised π i b x (by rw [hl]; rfl)
  have hcomp : ∀ ν, (C'.loc ν).comp = (C.loc ν).comp := fun ν => by
    by_cases hν : ν = π
    · subst hν; rw [hlocπ, hl]; cases u <;> rfl
    · rw [hlocν ν hν]
  simp only [augStep, hl]
  have hfl : (pstar C').fl = (pstar C).fl := by
    funext ν; simp only [pstar_fl]
    by_cases hν : ν = π
    · subst hν; rw [hlocπ, hl]; cases u <;> rfl
    · rw [hlocν ν hν]
  have hcand : ∀ ν ∈ l, Cand σ C G ν := by
    intro ν hν
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hm.2.1 ν hν
    refine ⟨⟨h1, ?_, by rw [← hfl]; exact h3⟩, by rw [augStep_tau_xh] at h4; rw [← hX]; exact h4⟩
    by_cases h : ν = π
    · subst h; rw [hlocπ] at h2; rw [hl]; cases u <;> simp_all [fcont, Loc.IsUpd]
    · rwa [hlocν ν h] at h2
  refine hQ ((mem_QSet_iff hI).2 ⟨l, qmem_transfer hI hm hcand (fun ν _ => by rw [hp])
    (by funext j; simp [pstar_val, hA]) hfl (fun j h => ?_)⟩)
  have hc : (∀ ν ∈ l, (C'.loc ν).comp ≠ some j) → ∀ ν ∈ l, (C.loc ν).comp ≠ some j :=
    fun h ν hν => (hcomp ν) ▸ h ν hν
  by_cases hj : j = i
  · subst hj
    have hBi : C'.B j = (a, x) := by rw [hB j]; simp
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, μ, u', k', b', x', a', h3, h4, h5, h6⟩
    · -- `B[j].seq` became `X`: the third disjunct before, with witness `π`
      rw [hBi, hX] at h1; rw [hBi] at h3
      right; right
      refine ⟨by rw [hb]; simp only at h1; omega, hc h2, π, u, k, b, x, a, hl, hb.symm,
        fun _ => h1, h3⟩
    · right; left
      refine ⟨by rw [hb]; omega, h2⟩
    · exfalso
      have hμ : μ ≠ π := by rintro rfl; rw [hlocπ] at h3; cases u <;> simp [fcont] at h3
      rw [hlocν μ hμ] at h3
      rw [hBi] at h4
      have hrd : (C.loc μ).rd = some (j, k', b') := by rw [h3]; rfl
      by_cases hne : C.B j = b'
      · rw [hb, h4] at hne; rw [hne] at hpo; simp at hpo
      · have := hI.rd_lt μ j k' b' hrd hne; rw [hb, h4] at this; simp at this; omega
  · have hBj : C'.B j = C.B j := by rw [hB j]; simp [hj]
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, μ, u', k', b', x', a', h3, h4, h5, h6⟩
    · left; rw [hBj, hX] at h1; rw [hBj] at h3; exact ⟨h1, hc h2, h3⟩
    · right; left; rw [hBj, hX] at h1; exact ⟨h1, h2⟩
    · right; right
      have hμ : μ ≠ π := by rintro rfl; rw [hlocπ] at h3; cases u <;> simp [fcont] at h3
      rw [hlocν μ hμ] at h3
      simp only [hBj, hX] at h1 h4 h5
      exact ⟨h1, hc h2, μ, u', k', b', x', a', h3, h4, fun _ => h5 trivial, h6⟩

/-- One step of the induction for (corrected) Lemma 7.2. -/
theorem QSub.step (hI : FInv σ C G) (hQ : QSet σ true C G ⊆ G.PP) {ℓ : CLabel W K v₀ P}
    (hst : (memSnap W K v₀ σ).step C ℓ = some C') :
    QSet σ true C' (augStep σ C ℓ G) ⊆ (augStep σ C ℓ G).PP := by
  have hI' := hI.step hst
  intro p hp
  obtain ⟨l, hm⟩ := (mem_QSet_iff hI').1 hp
  have back : ∀ {l : List P} {p : CPoss W K v₀ P}, QMem σ true C G l p → p ∈ G.PP :=
    fun h => hQ ((mem_QSet_iff hI).2 ⟨_, h⟩)
  cases ℓ with
  | inv π o =>
    obtain ⟨hp0, hall, hmem, hpend, hloc⟩ := inv_eq hst
    have hidle := shape_none (hp0 ▸ hI.shape π)
    have hπl : π ∉ l := by
      intro hπ
      obtain ⟨⟨h1, h2, -⟩, h4⟩ := hm.2.1 π hπ
      rw [hloc] at h2; simp only [Function.update_self] at h2
      cases o with
      | update i o' =>
        simp only [augStep, Function.update_self] at h4
        have : C'.X = C.X := by simp [Cfg.X, hmem]
        omega
      | click => exact h1 hall
      | observe i => exact h1 hall
    have hPP : (augStep σ C (.inv π o) G).PP = G.PP := by cases o <;> rfl
    rw [hPP]
    refine back (qmem_local hI hm (invoke W K o) hmem hloc
      (fun ν hν => by rw [hpend, Function.update_of_ne (show ν ≠ π from fun h => hπl (h ▸ hν))])
      (fun ν hν => by
        cases o <;> simp [augStep, Function.update_of_ne (show ν ≠ π from fun h => hπl (h ▸ hν))])
      (fun h => absurd h hπl) (fun h => absurd h hπl) ?_ ?_)
    · rw [hidle]; cases o <;> rfl
    · intro j u k b x a h; cases o <;> simp [invoke] at h
  | tau π =>
    obtain ⟨hn1, hn2, hn3, hn4⟩ := tau_ret_none hst
    cases hl : C.loc π with
    | idle => exact absurd hl hn1
    | c2 => exact absurd hl hn2
    | o5 v => exact absurd hl (hn3 v)
    | u8 r => exact absurd hl (hn4 r)
    | c1w x => exact QSub.c1w hI hQ hl hst hm
    | o4 i => exact QSub.o4 hI hQ hl hst hm
    | u7 i o => exact QSub.u7 hI hQ hl hst hm
    | c1 =>
      obtain ⟨hp, hmem, hloc⟩ := tau_c1 hst hl
      simp only [augStep, hl]
      exact back (qmem_local hI hm _ hmem hloc (fun ν _ => by rw [hp]) (fun _ _ => by rw [augStep_tau_xh])
        (by rw [hl]; simp [Loc.IsUpd]) (by rw [hl]; simp [Loc.comp]) (by rw [hl]; rfl)
        (by simp))
    | f9 i u k =>
      obtain ⟨hp, hmem, hloc⟩ := tau_f9 hst hl
      simp only [augStep, hl]
      exact back (qmem_local hI hm _ hmem hloc (fun ν _ => by rw [hp]) (fun _ _ => by rw [augStep_tau_xh])
        (fun _ h => by rw [hl]; cases u <;> simp_all [Loc.IsUpd]) (fun _ => by rw [hl]; rfl)
        (by rw [hl]; rfl) (by simp))
    | f10 i u k b =>
      obtain ⟨hp, hmem, hloc⟩ := tau_f10 hst hl
      simp only [augStep, hl]
      refine back (qmem_local hI hm _ hmem hloc (fun ν _ => by rw [hp]) (fun _ _ => by rw [augStep_tau_xh])
        (fun _ h => ?_) (fun _ => ?_) ?_ ?_) <;> rw [hl] <;> split_ifs at * <;>
        cases u <;> simp_all [Loc.IsUpd, fcont, Loc.comp, Loc.flag]
    | f11 i u k b x =>
      obtain ⟨hp, hmem, hloc⟩ := tau_f11 hst hl
      simp only [augStep, hl]
      refine back (qmem_local hI hm _ hmem hloc (fun ν _ => by rw [hp]) (fun _ _ => by rw [augStep_tau_xh])
        (fun _ h => ?_) (fun _ => by rw [hl]; rfl) (by rw [hl]; rfl) ?_)
      · rw [hl]; cases u <;> simp_all [Loc.IsUpd]
      · rintro j u' k' b' x' a' h
        simp only [Loc.f12.injEq] at h
        right; rw [← h.2.2.2.2.2, h.1]
    | f12 i u k b x a =>
      by_cases hb : C.B i = b
      · exact QSub.cas_succ hI hQ hl hb hst hm
      · obtain ⟨hp, hmem, hloc⟩ := tau_f12_fail hst hl hb
        simp only [augStep, hl]
        refine back (qmem_local hI hm _ hmem hloc (fun ν _ => by rw [hp]) (fun _ _ => by rw [augStep_tau_xh])
          (fun _ h => ?_) (fun _ => ?_) ?_ ?_) <;> rw [hl] <;> cases k <;>
          cases u <;> simp_all [Loc.IsUpd, fcont, Loc.comp, Loc.flag]
  | ret π r => exact QSub.ret hI hQ hst hm

end Step

/-- **Lemma 7.2 of [MemSnap], corrected** (with `x_μ = X` in the third disjunct of `Q`):
`Q ⊆ P ∧ Q ≠ ∅` is an invariant of Algorithm 2. -/
theorem lemma_7_2_fixed {α : List (CLabel W K v₀ P)} {C : Cfg W K v₀ P} {G : Ghost W K v₀ P}
    (h : arun σ α = some (C, G)) : QSet σ true C G ⊆ G.PP ∧ (QSet σ true C G).Nonempty := by
  have key : FInv σ C G ∧ QSet σ true C G ⊆ G.PP := by
    refine arun_induction (Q := fun _ C G => FInv σ C G ∧ QSet σ true C G ⊆ G.PP) ?_ ?_ h
    · refine ⟨FInv.init, fun p hp => ?_⟩
      obtain ⟨l, hnd, hc, hv, hf, hs⟩ := (mem_QSet_iff FInv.init).1 hp
      cases l with
      | cons π l =>
        obtain ⟨-, h4⟩ := hc π (by simp)
        simp [memSnap, Impl.initCfg, Cfg.X, ginit] at h4
      | nil =>
        show p ∈ ({Poss.init} : Set _)
        rw [Set.mem_singleton_iff]
        ext1
        · ext1
          · exact hv
          · funext j
            rcases hs j with ⟨-, -, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
            · exact h3
            · simp [memSnap, Impl.initCfg, Cfg.X, Cfg.B] at h1
            · simp [memSnap, Impl.initCfg, Cfg.X, Cfg.B] at h1
        · rw [hf]; funext π; rfl
    · intro α C G ℓ C' _ ⟨hI, hQ⟩ hst
      exact ⟨hI.step hst, QSub.step hI hQ hst⟩
  exact ⟨key.2, QSet_nonempty key.1 true⟩





end Podc.MemSnap
