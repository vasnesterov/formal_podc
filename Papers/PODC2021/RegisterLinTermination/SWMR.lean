import Podc.Computability.Distributed.SharedMemory.WriteStrongLin
import Cslib.Computability.Distributed.SharedMemory.Atomic
import Mathlib.Tactic.FinCases

/-!
# Linearizable SWMR registers are write strongly-linearizable (Theorem 14)

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Section 6
and Appendix E.

**Theorem 14.** Any linearizable implementation of a SWMR register is write strongly-linearizable.

We prove it for an arbitrary set `E` of histories in which only one process `w` invokes writes and
each history has a linearization (`swmr_writeStrongLin`): this covers shared-memory,
message-passing and hybrid implementations alike, as claimed by the paper. The corollary for
CSLib's shared-memory implementations is `Impl.writeStronglyLinearizable_of_swmr`.

## The construction

Our write strong-linearization function differs from the paper's (see below): for each history
`α` it picks a linearization with the **least number of operations of the writer `w`**. In any
linearization the operations of `w` are `w`'s first `m` operations in program order, where `m`
is the number of completed operations of `w` or that number plus one (the pending operation).
If `α` is a prefix of `β`, restricting a linearization of `β` to the operations invoked in `α`
gives a linearization of `α` (`IsLinearization.restrict`) with at most as many `w`-operations;
hence the minimal count does not decrease along prefixes, and the write sequences are prefixes
of each other.

## The paper's construction fails (`lemma67_construction_fails`)

The paper (Lemma 67) starts from an *arbitrary* linearization function `f` and removes the last
operation of `f(H)` if it is an incomplete write. Claim 67.1 asserts that an incomplete write that
is not the last operation of `f(H)` is read by some read of `H`; but the operation after it may be
a *pending* read (Definition 2 allows pending operations with responses added). We exhibit a
linearization function `f` of the atomic SWMR register for which the modified function `f*`
violates property (P): in `G` the writer has completed `write 1` and invoked `write 2`, and a
reader has invoked a read; `f(G) = write 1, write 2, read` (the read is pending, its response
`2` is "added"). In the extension `H` the read returns `1`, and `f(H) = write 1, read`. Then
`f*(G) = f(G)` and `f*(H) = f(H)`, and the write sequence `write 1, write 2` of `f*(G)` is not a
prefix of the write sequence `write 1` of `f*(H)`.
-/

namespace Podc.RegisterLinTermination

open Cslib.SharedMemory List

variable {P : Type} [DecidableEq P] {V : Type} {v₀ : V}

local notation "Reg" => register V v₀

/-! ## The writer's entries of a linearization -/

/-- The first `m` operations of `w` in `α`, as entries of a sequential history. -/
def wList (α : List (Label P Reg)) (w : P) (m : ℕ) : List (OpId P × RWOp V) :=
  zip ((range m).map (fun j => (w, j))) ((opsOf α w).take m)

/-- The number of entries of `w` in `S`. -/
def wCount (S : List (OpId P × RWOp V)) (w : P) : ℕ :=
  ((S.map Prod.fst).filter (fun x => decide (x.1 = w))).length

lemma filter_writer_eq {α : List (Label P Reg)} {S : List (OpId P × RWOp V)}
    (hα : WellFormed α) (hS : IsLinearization α S) (w : P) :
    S.filter (fun y => decide (y.1.1 = w)) = wList α w (wCount S w) := by
  have h1 : (S.filter (fun y => decide (y.1.1 = w))).map Prod.fst =
      (range (wCount S w)).map (fun j => (w, j)) := by
    have h := hS.procIds_eq hα w
    unfold IsLinearization.procIds at h
    rw [wCount, ← h, filter_map]; rfl
  have h2 : (S.filter (fun y => decide (y.1.1 = w))).map Prod.snd =
      (opsOf α w).take (wCount S w) := by
    exact hS.map_snd_filter_eq hα w S [] (by simp)
  rw [wList, ← h1, ← h2, ← unzip_fst, ← unzip_snd, zip_unzip]

lemma wList_eq_of_prefix {α β : List (Label P Reg)} (h : α <+: β) (w : P) {m : ℕ}
    (hm : m ≤ (opsOf α w).length) : wList α w m = wList β w m := by
  obtain ⟨γ, rfl⟩ := h
  simp only [wList, opsOf_append, take_append_of_le_length hm]

lemma wList_prefix (α : List (Label P Reg)) (w : P) {m m' : ℕ} (h : m ≤ m') :
    wList α w m <+: wList α w m' := by
  have : wList α w m = (wList α w m').take m := by
    simp only [wList, zip, take_zipWith, ← map_take, take_range, take_take, Nat.min_eq_left h]
  rw [this]; exact take_prefix _ _

lemma wCount_le {α : List (Label P Reg)} {S : List (OpId P × RWOp V)}
    (hα : WellFormed α) (hS : IsLinearization α S) (w : P) :
    wCount S w ≤ (opsOf α w).length := (hS.procIds_length hα w).2

lemma wCount_filter_le (S : List (OpId P × RWOp V)) (q : OpId P × RWOp V → Bool) (w : P) :
    wCount (S.filter q) w ≤ wCount S w := by
  unfold wCount
  apply Sublist.length_le
  apply Sublist.filter
  exact (filter_sublist).map _

/-- If only `w` writes, the writes of a linearization are the writes among `w`'s entries. -/
lemma opsFor_eq_of_writer {α : List (Label P Reg)} {S : List (OpId P × RWOp V)}
    (hS : IsLinearization α S) {w : P}
    (hw : ∀ p, ∀ o ∈ opsOf α p, o.isWrite = true → p = w) :
    opsFor (RWOp.isWrite (V := V)) S = opsFor (RWOp.isWrite (V := V)) (S.filter (fun y => decide (y.1.1 = w))) := by
  simp only [opsFor, filter_filter]
  apply filter_congr
  intro y hy
  by_cases h : y.2.isWrite = true
  · simp [h, hw _ _ (hS.op_mem hy) h]
  · simp [h]

/-! ## Theorem 14 -/

/-- The set of histories `E` is a set of SWMR histories with writer `w`: well formed, only `w`
invokes writes, and linearizable. -/
structure SWMRLinHistories (E : List (Label P Reg) → Prop) (w : P) : Prop where
  wellFormed : ∀ α, E α → WellFormed α
  writer : ∀ α, E α → ∀ p, ∀ o ∈ opsOf α p, o.isWrite = true → p = w
  linearizable : ∀ α, E α → ∃ S, IsLinearization α S

open Classical in
/-- The least number of writer entries of a linearization of `α` (`0` if there is none). -/
noncomputable def minCount (α : List (Label P Reg)) (w : P) : ℕ :=
  if h : ∃ m, ∃ S, IsLinearization α S ∧ wCount S w = m then Nat.find h else 0

open Classical in
/-- A linearization of `α` with the least number of writer entries. -/
noncomputable def minLin (α : List (Label P Reg)) (w : P) : List (OpId P × RWOp V) :=
  if h : ∃ S, IsLinearization α S ∧ wCount S w = minCount α w then h.choose else []

lemma minLin_spec {α : List (Label P Reg)} {w : P} (h : ∃ S, IsLinearization α S) :
    IsLinearization α (minLin α w) ∧ wCount (minLin α w) w = minCount α w ∧
      ∀ S, IsLinearization α S → minCount α w ≤ wCount S w := by
  classical
  have hex : ∃ m, ∃ S, IsLinearization α S ∧ wCount S w = m := by
    obtain ⟨S, hS⟩ := h; exact ⟨_, S, hS, rfl⟩
  have hmc : minCount α w = Nat.find hex := by rw [minCount, dite_eq_left_of_eq_true (eq_true hex)]
  have hex' : ∃ S, IsLinearization α S ∧ wCount S w = minCount α w := by
    rw [hmc]; exact Nat.find_spec hex
  have hml : minLin α w = hex'.choose := by rw [minLin, dite_eq_left_of_eq_true (eq_true hex')]
  rw [hml]
  refine ⟨hex'.choose_spec.1, hex'.choose_spec.2, fun S hS => ?_⟩
  rw [hmc]; exact Nat.find_min' hex ⟨S, hS, rfl⟩

/-- **Theorem 14** (Hadzilacos–Hu–Toueg, PODC 2021), for an arbitrary set of SWMR histories:
there is a write strong-linearization function, i.e. a function mapping every history of `E` to a
linearization of it such that, whenever `α` is a prefix of `β` (both in `E`), the sequence of
writes of the linearization of `α` is a prefix of that of `β`. -/
theorem swmr_writeStrongLin {E : List (Label P Reg) → Prop} {w : P}
    (hE : SWMRLinHistories E w) :
    ∃ f : List (Label P Reg) → List (OpId P × RWOp V),
      (∀ α, E α → IsLinearization α (f α)) ∧
      ∀ α β, E α → E β → α <+: β → opsFor (RWOp.isWrite (V := V)) (f α) <+: opsFor (RWOp.isWrite (V := V)) (f β) := by
  refine ⟨fun α => minLin α w, fun α hα => (minLin_spec (hE.linearizable α hα)).1, ?_⟩
  intro α β hα hβ hαβ
  obtain ⟨hLα, hcα, -⟩ := minLin_spec (w := w) (hE.linearizable α hα)
  obtain ⟨hLβ, hcβ, -⟩ := minLin_spec (w := w) (hE.linearizable β hβ)
  have hwfα := hE.wellFormed α hα
  have hwfβ := hE.wellFormed β hβ
  -- the minimal count does not decrease along prefixes
  have hle : minCount α w ≤ minCount β w := by
    obtain ⟨γ, rfl⟩ := hαβ
    have hR := hLβ.restrict (γ := γ) hwfα
    rw [← hcβ]
    exact ((minLin_spec (w := w) (hE.linearizable _ hα)).2.2 _ hR).trans
      (wCount_filter_le _ _ w)
  rw [opsFor_eq_of_writer hLα (hE.writer α hα), opsFor_eq_of_writer hLβ (hE.writer β hβ),
    filter_writer_eq hwfα hLα, filter_writer_eq hwfβ hLβ, hcα, hcβ,
    wList_eq_of_prefix hαβ w (hcα ▸ wCount_le hwfα hLα w)]
  exact opsFor_prefix (wList_prefix β w hle)

/-- **Theorem 14** for shared-memory implementations: a linearizable implementation of a register
in which only process `w` may invoke writes is write strongly-linearizable. -/
theorem _root_.Cslib.SharedMemory.Impl.writeStronglyLinearizable_of_swmr {ι L : Type}
    [DecidableEq ι] {B : ι → ObjSpec} {I : Impl Reg B P L} {w : P}
    (hw : ∀ p v, I.allowed p (.write v) → p = w) (hI : I.Linearizable) :
    I.WriteStronglyLinearizable := by
  obtain ⟨g, hg⟩ := hI
  have hE : SWMRLinHistories I.Valid w := by
    refine ⟨fun α hα => hα.wellFormed, fun α hα p o ho hwr => ?_, fun α hα => ⟨g α, hg α hα⟩⟩
    cases o with
    | read => simp at hwr
    | write v => exact hw p v (I.allowed_of_mem_opsOf hα ho)
  obtain ⟨f, hf, hpre⟩ := swmr_writeStrongLin hE
  exact ⟨f, hf, fun α β hβ hαβ => hpre α β (I.valid_of_prefix hβ hαβ) hβ hαβ⟩

/-! ## The construction of Lemma 67 fails -/

section Lemma67

/-- The modification `f*` of a linearization function `f` used in the proof of Lemma 67: if the
last operation of `f(H)` is a write that is incomplete in `H`, remove it. -/
noncomputable def paperStar (f : List (Label P Reg) → List (OpId P × RWOp V))
    (α : List (Label P Reg)) : List (OpId P × RWOp V) :=
  match (f α).getLast? with
  | some (x, .write _) => if Completed α x then f α else (f α).dropLast
  | _ => f α

/-- The atomic SWMR register over `ℕ` (initially `0`) for two processes: the atomic
implementation in which only process `0` may write. -/
def atomicSWMR : Impl (register ℕ 0) (fun _ : Unit => register ℕ 0) (Fin 2)
    (AtomicLoc (register ℕ 0)) :=
  { atomicImpl (register ℕ 0) 0 (Fin 2) with allowed := fun p o => o.isWrite = true → p = 0 }

instance (p : Fin 2) (o : RWOp ℕ) : Decidable (atomicSWMR.allowed p o) :=
  inferInstanceAs (Decidable (o.isWrite = true → p = 0))

/-- Only process `0` writes. -/
lemma atomicSWMR_swmr (p : Fin 2) (v : ℕ) (h : atomicSWMR.allowed p (.write v)) : p = 0 := h rfl

lemma atomicSWMR_step {C C' : Config (register ℕ 0) (fun _ : Unit => register ℕ 0) (Fin 2)
    (AtomicLoc (register ℕ 0))} {ℓ : Label (Fin 2) (register ℕ 0)}
    (h : atomicSWMR.step C ℓ = some C') :
    (atomicImpl (register ℕ 0) 0 (Fin 2)).step C ℓ = some C' := by
  cases ℓ with
  | inv p o =>
    obtain ⟨h1, -, h3, h4, h5⟩ := Impl.step_inv h
    rw [Impl.step_inv_eq_some h1 trivial]
    cases C'; simp only at h3 h4 h5; subst h3 h4 h5; rfl
  | tau p => exact h
  | ret p r => exact h

lemma atomicSWMR_runFrom (C : Config (register ℕ 0) (fun _ : Unit => register ℕ 0) (Fin 2)
    (AtomicLoc (register ℕ 0))) (α : List (Label (Fin 2) (register ℕ 0))) {C'}
    (h : atomicSWMR.runFrom C α = some C') :
    (atomicImpl (register ℕ 0) 0 (Fin 2)).runFrom C α = some C' := by
  induction α generalizing C with
  | nil => exact h
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h ⊢
    cases hs : atomicSWMR.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      rw [hs, Option.bind_some] at h
      rw [atomicSWMR_step hs, Option.bind_some]
      exact ih C₁ h

lemma atomicSWMR_linearizable : atomicSWMR.Linearizable := by
  obtain ⟨g, hg⟩ := Atomic.exists_linFun (A := register ℕ 0) (P := Fin 2) (r₀ := 0)
  exact ⟨g, fun α ⟨C, hC⟩ => (hg α C (atomicSWMR_runFrom _ _ hC)).lin⟩

/-- Non-vacuity of Theorem 14: the atomic SWMR register satisfies its hypotheses (and hence is
write strongly-linearizable). -/
theorem atomicSWMR_writeStronglyLinearizable : atomicSWMR.WriteStronglyLinearizable :=
  Impl.writeStronglyLinearizable_of_swmr atomicSWMR_swmr atomicSWMR_linearizable

/-- `G`: the writer completes `write 1`, then invokes `write 2`; the reader invokes a read. -/
def histG : List (Label (Fin 2) (register ℕ 0)) :=
  [.inv 0 (.write 1), .tau 0, .ret 0 1, .inv 0 (.write 2), .inv 1 .read]

/-- `H`: the read of `G` returns `1`. -/
def histH : List (Label (Fin 2) (register ℕ 0)) := histG ++ [.tau 1, .ret 1 1]

/-- `f(G)`: both writes, then the pending read (with added response `2`). -/
def linG : List (OpId (Fin 2) × RWOp ℕ) := [((0, 0), .write 1), ((0, 1), .write 2), ((1, 0), .read)]

/-- `f(H)`: the first write, then the read (which returns `1`). -/
def linH : List (OpId (Fin 2) × RWOp ℕ) := [((0, 0), .write 1), ((1, 0), .read)]

lemma valid_histH : atomicSWMR.Valid histH := by
  apply Impl.valid_of_crun; decide +kernel

lemma respsOf_histG_0 : respsOf histG 0 = [1] := by decide
lemma respsOf_histG_1 : respsOf histG 1 = [] := by decide
lemma respsOf_histH_0 : respsOf histH 0 = [1] := by decide
lemma respsOf_histH_1 : respsOf histH 1 = [1] := by decide

lemma len_histG : ∀ p : Fin 2, (respsOf histG p).length = if p = 0 then 1 else 0 := by decide
lemma len_histH : ∀ p : Fin 2, (respsOf histH p).length = 1 := by decide

lemma completed_histG {p : Fin 2} {k : ℕ} : Completed histG (p, k) ↔ p = 0 ∧ k = 0 := by
  rw [Completed, len_histG]; split_ifs with h <;> simp_all

lemma completed_histH {p : Fin 2} {k : ℕ} : Completed histH (p, k) ↔ k = 0 := by
  rw [Completed, len_histH]; omega

lemma isLinearization_linG : IsLinearization histG linG := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · rintro ⟨p, k⟩ h
    obtain ⟨rfl, rfl⟩ := completed_histG.1 h
    decide
  · rintro ⟨p, k⟩ ⟨q, l⟩ hpre hb
    have hb' : (q, l) ∈ [((0 : Fin 2), 0), (0, 1), (1, 0)] := by simpa [linG] using hb
    obtain ⟨rfl, rfl⟩ := completed_histG.1 hpre.completed
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
      at hb'
    rcases hb' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hpre (by decide)
    · decide
    · decide
  · simp [SeqOK, linG, respOf, respsOf_histG_0, respsOf_histG_1]

lemma isLinearization_linH : IsLinearization histH linH := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · rintro ⟨p, k⟩ h
    obtain rfl := completed_histH.1 h
    revert p; decide
  · rintro ⟨p, k⟩ ⟨q, l⟩ hpre hb
    have hb' : (q, l) ∈ [((0 : Fin 2), 0), (1, 0)] := by simpa [linH] using hb
    obtain rfl := completed_histH.1 hpre.completed
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
      at hb'
    revert hpre
    rcases hb' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert p <;> decide
  · simp [SeqOK, linH, respOf, respsOf_histH_0, respsOf_histH_1]

open Classical in
/-- A linearization function of the atomic SWMR register with `f(G) = linG`, `f(H) = linH`. -/
noncomputable def badLinFun : List (Label (Fin 2) (register ℕ 0)) → List (OpId (Fin 2) × RWOp ℕ) :=
  fun α => if α = histG then linG else if α = histH then linH else
    atomicSWMR_linearizable.choose α

lemma badLinFun_isLinFun : atomicSWMR.IsLinFun badLinFun := by
  intro α hα
  unfold badLinFun
  split_ifs with h1 h2
  · subst h1; exact isLinearization_linG
  · subst h2; exact isLinearization_linH
  · exact atomicSWMR_linearizable.choose_spec α hα

/-- **The construction in the proof of Lemma 67 is wrong.** For the linearization function
`badLinFun` of the atomic SWMR register, the modified function `f*` of the paper
(`paperStar`) violates property (P) of Definition 4: `G` is a prefix of the history `H`, but the
write sequence of `f*(G)` (`write 1, write 2`) is not a prefix of that of `f*(H)` (`write 1`).
(Theorem 14 itself holds: `swmr_writeStrongLin`.) -/
theorem lemma67_construction_fails :
    atomicSWMR.IsLinFun badLinFun ∧ atomicSWMR.Valid histH ∧ histG <+: histH ∧
      ¬ opsFor RWOp.isWrite (paperStar badLinFun histG) <+:
        opsFor RWOp.isWrite (paperStar badLinFun histH) := by
  refine ⟨badLinFun_isLinFun, valid_histH, prefix_append _ _, ?_⟩
  have hG : badLinFun histG = linG := by simp [badLinFun]
  have hH : badLinFun histH = linH := by simp [badLinFun, histH, histG]
  have h1 : paperStar badLinFun histG = linG := by
    simp [paperStar, hG, linG]
  have h2 : paperStar badLinFun histH = linH := by
    simp [paperStar, hH, linH]
  rw [h1, h2]
  decide

end Lemma67

end Podc.RegisterLinTermination
