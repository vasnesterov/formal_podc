import Papers.PODC2014.WritableObjects.HighLow
import Papers.PODC2014.WritableObjects.ListAux
import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Lemma 4.5: the template is linearizable under condition (C)

Main result: `lemma_4_5`. Given a transcript that follows the template of Figure 4.4 and
satisfies condition (C), and in which the history of every base object `A[i]` is admissible for a
sequentially writable object, the high-level history is linearizable.

## The linearization

As in the paper, every *matured* call `M` gets a timestamp `TS(M)` (here `keyPos`, the number of
writes to `Ptr` before the chosen point of `M`). All calls with timestamp `ℓ` operate on the same
base object `A[i_ℓ]` (the index written by the `ℓ`-th write to `Ptr`). Let `L_i` be a
linearization of the history of `A[i]` (it exists, since no `SWrite` overlaps another operation on
`A[i]`, `IsCtrl.writesIsolated`). The linearization of `WT` lists the blocks `ℓ = 0, 1, 2, …`,
block `ℓ` being the operations of `L_{i_ℓ}` with timestamp `ℓ`, in the order of `L_{i_ℓ}`,
replaced by their calls (`block`, `linWT`).

The paper obtains the order inside a block from a linearization of the *sub-history* `Λ_ℓ` of the
calls with timestamp `ℓ`, claiming that sequential writability applies to it. That inference is
not valid as stated (a sub-history of a linearizable history need not be linearizable; see
`Counterexample.lean`). We instead restrict the linearization `L_i` of the whole history of
`A[i]` and prove that, on each `A[i]`, timestamps are sorted along `L_i`
(`IsCtrl.ret_before_of_keyPos_lt`, which uses that `A[f]` is not in use when `A[f].SWrite` is
invoked), so each block is a contiguous segment of `L_i` starting with its `SWrite`.
-/

set_option linter.unusedSectionVars false

namespace Podc.WritableObjects

open Cslib.SharedMemory List

variable {P ι : Type} {T : ObjSpec} [DecidableEq P] [DecidableEq ι]

section Construction

variable (W : Writable T) (α : List (Ev P ι T))

open Classical in
/-- A chosen linearization of the history of `A[i]` (if any). -/
noncomputable def Lsel (i : ι) : List (OpId P × T.Op) :=
  if h : ∃ L, IsLinearization (lowH W i α) L then h.choose else []

open Classical in
/-- The position of the invocation of the instance `y` of `A[i]`. -/
noncomputable def lposOf (i : ι) (y : OpId P) : ℕ :=
  if h : ∃ a, IsInv (Ev.toLow W i) α y a then h.choose else 0

/-- The timestamp of the call of the instance `y` of `A[i]`. -/
noncomputable def keyL (i : ι) (y : OpId P) : WithTop ℕ := keyPos α (lposOf W α i y)

/-- The high-level call of the instance `y` of `A[i]`. -/
noncomputable def hidOf (i : ι) (y : OpId P) : OpId P := hidAt W α y.1 (lposOf W α i y)

/-- The index written by the `ℓ`-th write to `Ptr` (`i_ℓ`). -/
def iOf (ℓ : ℕ) : Option ι := (α.filterMap Ev.ptrVal)[ℓ - 1]?

open Classical in
/-- Block `ℓ` of the linearization: the calls with timestamp `ℓ`, in the order of `L_{i_ℓ}`. -/
noncomputable def block (ℓ : ℕ) : List (OpId P × T.Op) :=
  match iOf α ℓ with
  | none => []
  | some i => ((Lsel W α i).filter (fun z => decide (keyL W α i z.1 = ℓ))).map
      (fun z => (hidOf W α i z.1, z.2))

/-- The linearization of the high-level history (`S` in (4.5) of the paper). -/
noncomputable def linWT : List (OpId P × T.Op) :=
  (List.range ((α.filterMap Ev.ptrVal).length + 1)).flatMap (block W α)

end Construction

/-! ## General lemmas -/

lemma seqOK_map {h₁ h₂ : List (Label P T)} (g : OpId P → OpId P) {q : T.State}
    {L : List (OpId P × T.Op)} (hL : SeqOK h₁ q L)
    (hr : ∀ z ∈ L, ∀ r, respOf h₂ (g z.1) = some r → respOf h₁ z.1 = some r) :
    SeqOK h₂ q (L.map (fun z => (g z.1, z.2))) := by
  induction L generalizing q with
  | nil => trivial
  | cons z L ih =>
    obtain ⟨x, o⟩ := z
    obtain ⟨h1, h2⟩ := hL
    refine ⟨fun r hr' => h1 r (hr _ (by simp) r hr'), ih h2 (fun z hz => hr z (by simp [hz]))⟩

lemma seqOK_flatMap {h : List (Label P T)} {f : ℕ → List (OpId P × T.Op)}
    (hf : ∀ ℓ q, SeqOK h q (f ℓ)) (l : List ℕ) (q : T.State) : SeqOK h q (l.flatMap f) := by
  induction l generalizing q with
  | nil => trivial
  | cons c l ih =>
    rw [List.flatMap_cons, seqOK_append]
    exact ⟨hf c q, ih _⟩

variable {W : Writable T} {owner : ι → P} {α : List (Ev P ι T)} {σ : P → ℕ → PSt ι T}

lemma isInv_lposOf {i : ι} {y : OpId P} (hy : ∃ a, IsInv (Ev.toLow W i) α y a) :
    IsInv (Ev.toLow W i) α y (lposOf W α i y) := by
  classical
  rw [lposOf, dif_pos hy]
  exact hy.choose_spec

lemma lposOf_eq {i : ι} {y : OpId P} {a : ℕ} (hy : IsInv (Ev.toLow W i) α y a) :
    lposOf W α i y = a :=
  (isInv_lposOf ⟨a, hy⟩).unique hy

lemma isInv_of_mem_lin {i : ι} {L : List (OpId P × T.Op)} (hL : IsLinearization (lowH W i α) L)
    {z : OpId P × T.Op} (hz : z ∈ L) : IsInv (Ev.toLow W i) α z.1 (lposOf W α i z.1) := by
  have := hL.op_eq z hz
  unfold lowH at this
  obtain ⟨a, ha, h1, h2⟩ := (opOf_iff _ α _ _).1 this
  exact isInv_lposOf ⟨a, ha, _, h1, h2⟩

/-- Timestamps of calls on `A[i]` determine `i` (all calls with timestamp `ℓ` use `i_ℓ`). -/
lemma IsCtrl.iOf_of_keyPos (h : IsCtrl W owner α σ) (hC : CondC α) {i : ι} {p : P} {a ℓ : ℕ}
    (ha : LowInvAt α i p a) (hk : keyPos α a = ℓ) :
    iOf α ℓ = some i ∧ ℓ < (α.filterMap Ev.ptrVal).length + 1 := by
  have key : ∃ t, ptrAt α t = some i ∧ nptr α t = ℓ := by
    rcases ha with ⟨v, ha⟩ | ⟨o, ha⟩
    · have hne : keyPos α a ≠ ⊤ := by rw [hk]; exact WithTop.coe_ne_top
      obtain ⟨w, hw⟩ := h.keyPos_ne_top_iff_anchor ha hne
      rw [keyPos_anchor hw] at hk
      obtain ⟨p', i', v', ha', hw', -⟩ := hw
      rw [ha] at ha'
      simp only [Option.some.injEq, Ev.swinv.injEq] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := ha'
      exact ⟨w + 1, (nptr_succ_of_ptr hw').2, WithTop.coe_inj.1 hk⟩
    · rw [keyPos_opinv ha] at hk
      have hcpt := cpt_tsOf (h.exists_cpt hC ha)
      obtain ⟨-, -, hptr, -⟩ := hcpt.facts ha
      exact ⟨tsOf α a, hptr, WithTop.coe_inj.1 hk⟩
  obtain ⟨t, hpt, hn⟩ := key
  obtain ⟨h1, h2⟩ := ptrAt_eq_some hpt
  rw [hn] at h1 h2
  refine ⟨h2, ?_⟩
  have := (List.getElem?_eq_some_iff.1 h2).1
  omega

/-- There is at most one `SWrite` with a given (finite) timestamp. -/
lemma IsCtrl.swinv_eq_of_keyPos_eq (h : IsCtrl W owner α σ) {a a' : ℕ} {p p' : P} {i i' : ι}
    {v v' : T.State} (ha : α[a]? = some (.swinv p i v)) (ha' : α[a']? = some (.swinv p' i' v'))
    (hk : keyPos α a = keyPos α a') (hne : keyPos α a ≠ ⊤) : a = a' := by
  obtain ⟨w, hw⟩ := h.keyPos_ne_top_iff_anchor ha hne
  obtain ⟨w', hw'⟩ := h.keyPos_ne_top_iff_anchor ha' (hk ▸ hne)
  rw [keyPos_anchor hw, keyPos_anchor hw'] at hk
  have hn := WithTop.coe_inj.1 hk
  obtain ⟨_, _, _, -, hpw, -⟩ := id hw
  obtain ⟨_, _, _, -, hpw', -⟩ := id hw'
  have hww := eq_of_nptr_eq hpw hpw' hn
  subst hww
  exact hw.unique_left hw'

lemma mem_block_iff' {ℓ : ℕ} {z : OpId P × T.Op} :
    z ∈ block W α ℓ ↔ ∃ i, iOf α ℓ = some i ∧ ∃ y ∈ Lsel W α i, keyL W α i y.1 = ℓ ∧
      z = (hidOf W α i y.1, y.2) := by
  classical
  unfold block
  split
  · rename_i heq; simp [heq]
  · rename_i i heq
    simp only [heq, Option.some.injEq, exists_eq_left', List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨y, ⟨hy, hk⟩, rfl⟩; exact ⟨y, hy, hk, rfl⟩
    · rintro ⟨y, hy, hk, rfl⟩; exact ⟨y, ⟨hy, hk⟩, rfl⟩

namespace IsCtrl

variable (h : IsCtrl W owner α σ) (hN : NotInUse α) (hC : CondC α)
include h hN hC

lemma lsel_isLin (hSW : ∀ i, SeqWritable W (lowH W i α)) (i : ι) :
    IsLinearization (lowH W i α) (Lsel W α i) := by
  classical
  have hex := hSW i (h.writesIsolated hC i)
  rw [Lsel, dif_pos hex]
  exact hex.choose_spec

/-- On each base object, timestamps are sorted along the linearization `L_i`. -/
lemma lsel_sorted (hSW : ∀ i, SeqWritable W (lowH W i α)) (i : ι) :
    (Lsel W α i).Pairwise (fun z z' => keyL W α i z.1 ≤ keyL W α i z'.1) := by
  have hL := h.lsel_isLin hN hC hSW i
  rw [List.pairwise_iff_forall_sublist]
  intro z z' hzz
  by_contra hlt
  rw [not_le] at hlt
  have hz := isInv_of_mem_lin hL (hzz.subset (show z ∈ [z, z'] by simp))
  have hz' := isInv_of_mem_lin hL (hzz.subset (show z' ∈ [z, z'] by simp))
  obtain ⟨r, hr, hret⟩ := h.ret_before_of_keyPos_lt hN hC hz' (lowInvAt_of_isInv hz) hlt
  have hprec : Precedes (lowH W i α) z'.1 z.1 :=
    precedes_of_lt hret (fun e he => (he.unique hz) ▸ hr)
  have h1 := hL.realtime _ _ hprec (List.mem_map_of_mem (hzz.subset (show z ∈ [z, z'] by simp)))
  have h2 : [z.1, z'.1] <+ (Lsel W α i).map Prod.fst := hzz.map Prod.fst
  exact not_sublist_pair_both hL.nodup h2 h1

/-- Every `Exec` with timestamp `ℓ` comes after the `SWrite` with timestamp `ℓ` (on the same
object) in real time. -/
lemma head_precedes {i : ι} {a a_s : ℕ} {p q : P} {v : T.State} {o : T.Op}
    (has : α[a_s]? = some (.swinv p i v)) (ha : α[a]? = some (.opinv q i o))
    (hk : keyPos α a_s = keyPos α a) (hne : keyPos α a_s ≠ ⊤) :
    ∃ b < a, IsRet (Ev.toLow W i) α (lidAt W α i p a_s) b := by
  obtain ⟨a₀, p₀, v₀, b₀, ha₀, hk₀, hab, hba, ⟨r, hb⟩, hq⟩ := h.head_of_opinv hC ha
  have := h.swinv_eq_of_keyPos_eq has ha₀ (hk.trans hk₀.symm) hne
  subst this
  rw [has] at ha₀
  simp only [Option.some.injEq, Ev.swinv.injEq] at ha₀
  obtain ⟨rfl, -, rfl⟩ := ha₀
  obtain ⟨hbl, hbp⟩ := proc_of_getElem? hb
  exact ⟨b₀, hba, h.isRet_of_quiet (Or.inl ⟨v, has⟩) hbl hab hbp hq⟩

/-- Each block is legal from any state: it starts with its `Write`, followed by `Exec`s in the
order of `L_{i_ℓ}`. -/
lemma seqOK_block (hSW : ∀ i, SeqWritable W (lowH W i α)) (ℓ : ℕ) (q : T.State) :
    SeqOK (highH W α) q (block W α ℓ) := by
  classical
  unfold block
  split
  · trivial
  rename_i i hiℓ
  have hL := h.lsel_isLin hN hC hSW i
  set F := (Lsel W α i).filter (fun z => decide (keyL W α i z.1 = ℓ)) with hF
  by_cases hFne : F = []
  · rw [hFne]; trivial
  obtain ⟨z₀, hz₀⟩ := List.exists_mem_of_ne_nil F hFne
  have hz₀L : z₀ ∈ Lsel W α i := (List.mem_filter.1 hz₀).1
  have hz₀k : keyL W α i z₀.1 = ℓ := by simpa using (List.mem_filter.1 hz₀).2
  have hz₀i := isInv_of_mem_lin hL hz₀L
  -- the head `SWrite` with timestamp `ℓ`
  obtain ⟨as, p, v, has, hask⟩ : ∃ as p v, α[as]? = some (.swinv p i v) ∧ keyPos α as = ℓ := by
    rcases lowInvAt_of_isInv hz₀i with ⟨v, hv⟩ | ⟨o, ho⟩
    · exact ⟨_, _, v, hv, hz₀k⟩
    · obtain ⟨a₀, p₀, v₀, -, ha₀, hk₀, -⟩ := h.head_of_opinv hC ho
      exact ⟨a₀, p₀, v₀, ha₀, hk₀.trans hz₀k⟩
  have hne : keyPos α as ≠ ⊤ := by rw [hask]; exact WithTop.coe_ne_top
  set hs := lidAt W α i p as
  have hsInv : IsInv (Ev.toLow W i) α hs as := isInv_lidAt (Or.inl ⟨v, has⟩)
  have hsp : hs.1 = p := rfl
  -- the head is completed, hence in `L_i`
  obtain ⟨w, hw⟩ := h.keyPos_ne_top_iff_anchor has hne
  have hsRet : ∃ b, IsRet (Ev.toLow W i) α hs b := by
    obtain ⟨p', i', v', ha', -, b, hab, -, ⟨r, hb⟩, hq, -⟩ := hw
    rw [has] at ha'
    simp only [Option.some.injEq, Ev.swinv.injEq] at ha'
    obtain ⟨rfl, rfl, rfl⟩ := ha'
    obtain ⟨hbl, hbp⟩ := proc_of_getElem? hb
    exact ⟨b, h.isRet_of_quiet (Or.inl ⟨v, has⟩) hbl hab hbp hq⟩
  have hsMem : hs ∈ (Lsel W α i).map Prod.fst := by
    apply hL.complete
    unfold lowH
    exact (completed_iff _ α hs).2 hsRet
  obtain ⟨⟨hs', os⟩, hsL, hs'eq⟩ := List.mem_map.1 hsMem
  simp only at hs'eq
  subst hs'eq
  have hos : os = W.wr v := by
    have := hL.op_eq _ hsL
    unfold lowH at this
    obtain ⟨a', ha', h1, h2⟩ := (opOf_iff _ α _ _).1 this
    have : a' = as := (IsInv.unique ⟨ha', _, h1, h2⟩ hsInv)
    subst this
    obtain ⟨_, hev⟩ := getElem_of_getElem? has
    simp [hev, Ev.toLow] at h1
    exact h1.2.symm
  subst hos
  have hsF : (hs, W.wr v) ∈ F := by
    refine List.mem_filter.2 ⟨hsL, ?_⟩
    simp only [keyL, lposOf_eq hsInv, hask, decide_true]
  have hnodupL : (Lsel W α i).Nodup := List.Nodup.of_map _ hL.nodup
  have hnodupF : F.Nodup := hnodupL.filter _
  -- every other element of the block is an `Exec` that the head precedes
  have hother : ∀ z ∈ F, z ≠ (hs, W.wr v) →
      (∃ o, α[lposOf W α i z.1]? = some (.opinv z.1.1 i o)) ∧ [(hs, W.wr v), z] <+ F := by
    intro z hz hzne
    have hzL : z ∈ Lsel W α i := (List.mem_filter.1 hz).1
    have hzk : keyL W α i z.1 = ℓ := by simpa using (List.mem_filter.1 hz).2
    have hzi := isInv_of_mem_lin hL hzL
    have hz1 : z.1 ≠ hs := by
      intro h1
      apply hzne
      have := hL.op_eq _ hzL
      have h2 := hL.op_eq _ hsL
      rw [h1, h2] at this
      exact Prod.ext h1 (Option.some.inj this).symm
    rcases lowInvAt_of_isInv hzi with ⟨v', hv'⟩ | ⟨o, ho⟩
    · exfalso
      have := h.swinv_eq_of_keyPos_eq has hv' (hask.trans hzk.symm) hne
      exact hz1 (hzi.inj (this ▸ hsInv))
    · refine ⟨⟨o, ho⟩, ?_⟩
      obtain ⟨b, hb, hret⟩ := h.head_precedes hN hC has ho (hask.trans hzk.symm) hne
      have hprec : Precedes (lowH W i α) hs z.1 :=
        precedes_of_lt hret (fun e he => (he.unique hzi) ▸ hb)
      have h1 := hL.realtime _ _ hprec (List.mem_map_of_mem hzL)
      have h2 := sublist_pair_of_fst hL.nodup hsL hzL h1
      have h3 := h2.filter (fun z => decide (keyL W α i z.1 = ℓ))
      rw [List.filter_cons_of_pos (by simpa using (List.mem_filter.1 hsF).2),
        List.filter_cons_of_pos (by simpa using (List.mem_filter.1 hz).2),
        List.filter_nil] at h3
      exact h3
  obtain ⟨rest, hrest⟩ := eq_cons_of_first hnodupF hsF (fun z hz hzne => (hother z hz hzne).2)
  -- `F` is a contiguous segment of `L_i`
  obtain ⟨A, B, hAB, -, -⟩ := exists_filter_infix (fun z : OpId P × T.Op => keyL W α i z.1)
    (ℓ : WithTop ℕ) (h.lsel_sorted hN hC hSW i)
  have hseqL := hL.seq
  rw [hAB, seqOK_append, seqOK_append] at hseqL
  have hseqF := hseqL.1.2
  rw [← hF, hrest] at hseqF
  obtain ⟨-, hseqR⟩ := hseqF
  rw [W.δ_wr] at hseqR
  -- the high-level block
  rw [hrest, List.map_cons]
  refine ⟨fun r hr => ?_, ?_⟩
  · rw [W.δ_wr]
    unfold highH at hr
    obtain ⟨rpos, hrl, hr1, hr2⟩ := (respOf_iff _ α _ _).1 hr
    obtain ⟨i', a'', c, hlow, hid, -, -, -, -, hsw, -⟩ :=
      h.completed_high (x := hidOf W α i hs) ⟨hrl, r, hr1, hr2⟩
    have hid' : hidAt W α (hidOf W α i hs).1 a'' = hidAt W α p as := by
      rw [hid]; simp only [hidOf, lposOf_eq hsInv]; rfl
    have := h.eq_of_hidAt_eq hlow (Or.inl ⟨v, has⟩) hid'
    subst this
    have hp' : (hidOf W α i hs).1 = p := rfl
    rw [hp'] at hsw hlow
    obtain ⟨v'', hv''⟩ | ⟨o, ho⟩ := hlow
    · rw [has] at hv''
      simp only [Option.some.injEq, Ev.swinv.injEq] at hv''
      obtain ⟨-, rfl, rfl⟩ := hv''
      exact (hsw v r has (by unfold highH; exact hr)).symm
    · rw [has] at ho; simp at ho
  · have hseqR' : SeqOK (lowH W i α) v rest := hseqR
    show SeqOK _ (T.δ q (W.wr v)).1 _
    rw [W.δ_wr]
    refine seqOK_map (hidOf W α i) hseqR' (fun z hz r hr => ?_)
    have hzF : z ∈ F := by rw [hrest]; exact List.mem_cons_of_mem _ hz
    have hzne : z ≠ (hs, W.wr v) := by
      rintro rfl
      rw [hrest] at hnodupF
      exact (List.nodup_cons.1 hnodupF).1 hz
    obtain ⟨⟨o, ho⟩, -⟩ := hother z hzF hzne
    have hzi := isInv_of_mem_lin hL (List.mem_filter.1 hzF).1
    unfold highH at hr
    obtain ⟨rpos, hrl, hr1, hr2⟩ := (respOf_iff _ α _ _).1 hr
    obtain ⟨i', a'', c, hlow, hid, -, -, -, -, -, hex⟩ :=
      h.completed_high (x := hidOf W α i z.1) ⟨hrl, r, hr1, hr2⟩
    have := h.eq_of_hidAt_eq hlow (lowInvAt_of_isInv hzi) (by rw [hid]; rfl)
    subst this
    have hii : i' = i := by
      rcases hlow with ⟨v', hv'⟩ | ⟨o', ho'⟩
      · rw [ho] at hv'; simp at hv'
      · rw [ho] at ho'
        simp only [Option.some.injEq, Ev.opinv.injEq] at ho'
        exact ho'.2.1.symm
    subst hii
    have hp' : (hidOf W α i' z.1).1 = z.1.1 := rfl
    have := hex o r (by rw [hp']; exact ho) (by unfold highH; exact hr)
    rw [hp', lidAt_eq_of_isInv hzi] at this
    unfold lowH at this
    exact this

/-- Distinct elements of the linearizations `L_i` belong to distinct calls. -/
lemma hidOf_inj (hSW : ∀ i, SeqWritable W (lowH W i α)) {i i' : ι} {y y' : OpId P × T.Op}
    (hy : y ∈ Lsel W α i) (hy' : y' ∈ Lsel W α i') (heq : hidOf W α i y.1 = hidOf W α i' y'.1) :
    i = i' ∧ y = y' := by
  have hL := h.lsel_isLin hN hC hSW i
  have hL' := h.lsel_isLin hN hC hSW i'
  have hi := isInv_of_mem_lin hL hy
  have hi' := isInv_of_mem_lin hL' hy'
  have ha := h.eq_of_hidAt_eq (lowInvAt_of_isInv hi) (lowInvAt_of_isInv hi') heq
  rw [ha] at hi
  have hii : i = i' := by
    obtain ⟨hl, o, h1, -⟩ := hi
    obtain ⟨hl', o', h1', -⟩ := hi'
    rcases Ev.toLow_eq_inv h1 with ⟨v, h2, -⟩ | h2 <;>
      rcases Ev.toLow_eq_inv h1' with ⟨v', h2', -⟩ | h2' <;> rw [h2] at h2' <;>
      simp only [Ev.swinv.injEq, Ev.opinv.injEq, reduceCtorEq] at h2' <;> exact h2'.2.1
  subst hii
  have h1 := hi.inj hi'
  refine ⟨rfl, Prod.ext h1 ?_⟩
  have := hL.op_eq _ hy
  rw [h1, hL.op_eq _ hy'] at this
  exact (Option.some.inj this).symm

/-- **Lemma 4.5** (with the explicit linearization `linWT`). -/
theorem isLinearization_linWT (hSW : ∀ i, SeqWritable W (lowH W i α)) :
    IsLinearization (highH W α) (linWT W α) := by
  classical
  have hmem : ∀ z, z ∈ linWT W α ↔ ∃ ℓ < (α.filterMap Ev.ptrVal).length + 1,
      z ∈ block W α ℓ := by
    intro z; simp [linWT, List.mem_flatMap]
  have hrange : (List.range ((α.filterMap Ev.ptrVal).length + 1)).Pairwise (· < ·) :=
    List.pairwise_lt_range
  -- every completed call is in some block
  have hcomp : ∀ x r, IsRet (Ev.toHigh W) α x r → ∃ ℓ < (α.filterMap Ev.ptrVal).length + 1,
      ∃ i, iOf α ℓ = some i ∧ ∃ y ∈ Lsel W α i, keyL W α i y.1 = ℓ ∧ hidOf W α i y.1 = x ∧
        ∃ c < r, IsRet (Ev.toLow W i) α y.1 c ∧ (ℓ : WithTop ℕ) ≤ nptr α r := by
    intro x r hr
    obtain ⟨i, a, c, hlow, hid, -, hcr, hret, hkey, -⟩ := h.completed_high hr
    obtain ⟨ℓ, hℓ⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hkey)
    obtain ⟨hiℓ, hℓN⟩ := h.iOf_of_keyPos hC hlow hℓ.symm
    have hL := h.lsel_isLin hN hC hSW i
    have hlidm : lidAt W α i x.1 a ∈ (Lsel W α i).map Prod.fst := by
      apply hL.complete
      unfold lowH
      exact (completed_iff _ α _).2 ⟨c, hret⟩
    obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hlidm
    have hpos : lposOf W α i y.1 = a := by rw [hy1]; exact lposOf_eq (isInv_lidAt hlow)
    refine ⟨ℓ, hℓN, i, hiℓ, y, hy, ?_, ?_, c, hcr, hy1 ▸ hret, hℓ ▸ hkey⟩
    · simp only [keyL, hpos, hℓ]
    · simp only [hidOf, hpos]
      rw [hy1]
      exact hid
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- no duplicates
    rw [linWT, List.map_flatMap, List.nodup_flatMap]
    refine ⟨fun ℓ _ => ?_, hrange.imp_of_mem (fun {ℓ ℓ'} _ _ hlt => ?_)⟩
    · refine List.Nodup.map_on (fun z hz z' hz' heq => ?_) ?_
      · obtain ⟨i, hi, y, hy, -, rfl⟩ := (mem_block_iff' (W := W)).1 hz
        obtain ⟨i', hi', y', hy', -, rfl⟩ := (mem_block_iff' (W := W)).1 hz'
        obtain ⟨rfl, rfl⟩ := h.hidOf_inj hN hC hSW hy hy' heq
        rfl
      · unfold block
        split
        · exact List.nodup_nil
        · rename_i i _
          have hL := h.lsel_isLin hN hC hSW i
          refine List.Nodup.map_on (fun y hy y' hy' heq => ?_)
            ((List.Nodup.of_map _ hL.nodup).filter _)
          have := congrArg Prod.fst heq
          exact (h.hidOf_inj hN hC hSW (List.mem_filter.1 hy).1 (List.mem_filter.1 hy').1
            this).2
    · intro x hx hx'
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      obtain ⟨z', hz', heq⟩ := List.mem_map.1 hx'
      obtain ⟨i, hi, y, hy, hk, rfl⟩ := (mem_block_iff' (W := W)).1 hz
      obtain ⟨i', hi', y', hy', hk', rfl⟩ := (mem_block_iff' (W := W)).1 hz'
      obtain ⟨rfl, rfl⟩ := h.hidOf_inj hN hC hSW hy hy' heq.symm
      rw [hk] at hk'
      exact absurd (WithTop.coe_inj.1 hk') (by omega)
  · -- operations
    intro z hz
    obtain ⟨ℓ, -, hzb⟩ := (hmem z).1 hz
    obtain ⟨i, -, y, hy, -, rfl⟩ := (mem_block_iff' (W := W)).1 hzb
    have hL := h.lsel_isLin hN hC hSW i
    have hyi := isInv_of_mem_lin hL hy
    obtain ⟨e, -, -, hinv, ha', he', o, hlo, hhi⟩ := h.high_inv (lowInvAt_of_isInv hyi)
    have hop := hL.op_eq _ hy
    unfold lowH at hop
    obtain ⟨a', ha'', h1, h2⟩ := (opOf_iff _ α _ _).1 hop
    have := IsInv.unique ⟨ha'', _, h1, h2⟩ hyi
    subst this
    rw [h1] at hlo
    simp only [Option.some.injEq, Label.inv.injEq] at hlo
    obtain ⟨-, rfl⟩ := hlo
    obtain ⟨-, -, -, hcnt⟩ := hinv
    unfold highH
    exact (opOf_iff _ α _ _).2 ⟨e, he', hhi, hcnt⟩
  · -- completed calls
    intro x hx
    unfold highH at hx
    obtain ⟨r, hr⟩ := (completed_iff _ α x).1 hx
    obtain ⟨ℓ, hℓN, i, hi, y, hy, hk, hid, -⟩ := hcomp x r hr
    refine List.mem_map.2 ⟨(hidOf W α i y.1, y.2), (hmem _).2 ⟨ℓ, hℓN, ?_⟩, by simp [hid]⟩
    exact (mem_block_iff' (W := W)).2 ⟨i, hi, y, hy, hk, rfl⟩
  · -- real time
    intro x x' hprec hx'
    have hxc := hprec.completed
    unfold highH at hxc hprec
    obtain ⟨r, hr⟩ := (completed_iff _ α x).1 hxc
    obtain ⟨ℓ, hℓN, i, hi, y, hy, hk, hid, c, hcr, hret, hℓr⟩ := hcomp x r hr
    obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hx'
    obtain ⟨ℓ', hℓN', hzb'⟩ := (hmem z').1 hz'
    obtain ⟨i', hi', y', hy', hk', rfl⟩ := (mem_block_iff' (W := W)).1 hzb'
    have hL' := h.lsel_isLin hN hC hSW i'
    have hyi' := isInv_of_mem_lin hL' hy'
    obtain ⟨e, hea, -, hinv, -⟩ := h.high_inv (lowInvAt_of_isInv hyi')
    have hre : r < e := lt_of_precedes hprec hr hinv
    have hke := h.nptr_le_keyPos hC (lowInvAt_of_isInv hyi') hinv
    have hle : ℓ ≤ ℓ' := by
      have h1 : (ℓ : WithTop ℕ) ≤ ℓ' := by
        refine hℓr.trans ((WithTop.coe_le_coe.2 (nptr_mono hre.le)).trans ?_)
        rw [← hk']; exact hke
      exact WithTop.coe_le_coe.1 h1
    have hxb : (x, y.2) ∈ block W α ℓ :=
      (mem_block_iff' (W := W)).2 ⟨i, hi, y, hy, hk, by rw [hid]⟩
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · have := sublist_flatMap_of_lt hrange (block W α) (List.mem_range.2 hℓN)
        (List.mem_range.2 hℓN') hlt hxb hzb'
      exact this.map Prod.fst
    · rw [hi] at hi'
      cases hi'
      have hL := h.lsel_isLin hN hC hSW i
      have hlow : Precedes (lowH W i α) y.1 y'.1 :=
        precedes_of_lt hret (fun e' he' => (he'.unique hyi') ▸ (by omega))
      have h1 := hL.realtime _ _ hlow (List.mem_map_of_mem hy')
      have h2 := sublist_pair_of_fst hL.nodup hy hy' h1
      have h3 := h2.filter (fun z => decide (keyL W α i z.1 = ℓ))
      rw [List.filter_cons_of_pos (by simpa using hk), List.filter_cons_of_pos (by simpa using hk'),
        List.filter_nil] at h3
      have h4 := h3.map (fun z => (hidOf W α i z.1, z.2))
      have h5 : [(hidOf W α i y.1, y.2), (hidOf W α i y'.1, y'.2)] <+ block W α ℓ := by
        unfold block
        rw [hi]
        exact h4
      have h6 := h5.trans (sublist_flatMap_of_mem (block W α) (List.mem_range.2 hℓN))
      have h7 := h6.map Prod.fst
      simp only [List.map_cons, List.map_nil] at h7
      rw [hid] at h7
      exact h7
  · -- legality
    exact seqOK_flatMap (fun ℓ q => h.seqOK_block hN hC hSW ℓ q) _ _

end IsCtrl

/-- **Lemma 4.5** of [AGW14] (thesis numbering). An implementation of `Write()` and `Exec()`
following the template of Figure 4.4 is linearizable if it guarantees condition (C): for every
transcript `α` that follows the template, satisfies (C), and in which each base object `A[i]`
behaves as a sequentially writable object (its history is linearizable whenever no `SWrite`
overlaps another operation on it), the high-level history of `α` is linearizable. -/
theorem lemma_4_5 (W : Writable T) (owner : ι → P) (α : List (Ev P ι T))
    (hT : Template W owner α) (hC : CondC α) (hSW : ∀ i, SeqWritable W (lowH W i α)) :
    ∃ L, IsLinearization (highH W α) L := by
  obtain ⟨σ, hσ⟩ := hT.ctrl
  exact ⟨linWT W α, IsCtrl.isLinearization_linWT (W := W) (owner := owner) hσ hT.notInUse hC hSW⟩

/-- The template's requirement in the paper's form: the write-index `f` of a `Write` call is not
in use at the invocation of the call. -/
def NotInUseAtWriteInv (α : List (Ev P ι T)) : Prop :=
  ∀ e t p f v v', α[e]? = some (.winv p v') → α[t]? = some (.swinv p f v) → e < t →
    Quiet α p e t → ptrAt α e ≠ some f

/-- The paper's form of the "not in use" requirement implies the one used here (`NotInUse`, at
the invocation of the `SWrite`). -/
lemma notInUse_of_atWriteInv (h : IsCtrl W owner α σ) (hw : NotInUseAtWriteInv α) :
    NotInUse α := by
  intro t p f v ht hpt
  obtain ⟨-, -, -, e, het, he, hq⟩ := h.swinv_facts ht
  have hne := hw e t p f v v he ht het hq
  obtain ⟨w, p', h1, h2, hw'⟩ := exists_ptr_of_ne (α := α) het.le hne hpt
  have hown := h.owner_of_ptr hw'
  rw [(h.swinv_facts ht).1] at hown
  subst hown
  obtain ⟨hwl, hwp⟩ := proc_of_getElem? hw'
  rcases Nat.lt_or_eq_of_le h1 with h1 | rfl
  · exact hq w hwl h1 h2 hwp
  · rw [he] at hw'; simp at hw'

end Podc.WritableObjects
