import Papers.PODC2024.HistoryIndependent.Alg4

/-!
# Algorithm 4: abstract state with ghost variables

`St K` is the state of Algorithm 4 (memory, writer's and reader's local state) together with
*ghost* variables, and `sstep` its (total) transition function on labels. The ghost state of an
execution `α` is `sOf v₀ α = α.foldl sstep init`, a function of the execution. The simulation
lemma `rel_run` shows that the concrete part of `sOf v₀ α` is the configuration reached by `α`.

Ghost variables (writes are numbered `1, 2, …` in invocation order, `0` is the initial value):

* `wv` — the values of the invoked writes; `n = wv.length`;
* `tagA j` / `tagB j` — number of the write that last wrote `1` to `A[j]` / `B[j]`;
* `sN1` — `n` when the current `Read` executed Line 1; `sT` — `nA` (number of writes that
  executed Line 16) when the current `TryRead` started;
* `lo` — number of completed writes when the current `Read` was invoked;
* `rf` — the *reads-from* candidate of the current `Read`: when the reader sets `val ← j`
  after reading `A[j] = 1` it records `tagA j`; after reading `B[j] = 1` it records
  `tagB j - 1` (the write *preceding* the one that wrote `B[j]`, whose value is `last-val`);
* `fl` — reads-from value of the last completed `Read`; `pis` — reads-from values of all
  completed `Read`s.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Alg4

variable {K : ℕ} [NeZero K]

/-- Abstract state with ghost variables. -/
structure St (K : ℕ) where
  A : Fin K → Bool
  Bm : Fin K → Bool
  f1 : Bool
  f2 : Bool
  last : Fin K
  wpc : WPC K
  rpc : RPC K
  wv : List (Fin K)
  tagA : Fin K → ℕ
  tagB : Fin K → ℕ
  sN1 : ℕ
  sT : ℕ
  lo : ℕ
  rf : ℕ
  fl : ℕ
  pis : List ℕ

/-- The writer is before Line 16 of a `Write`. -/
def WPC.preA : WPC K → Bool
  | .scanB .. | .rdF1 _ | .setB _ | .rdF2 _ | .rdF1' _ | .clrB _ | .setA _ => true
  | _ => false

/-- The writer is after Line 16 of a `Write`. -/
def WPC.postA : WPC K → Bool
  | .down .. | .up .. | .done _ => true
  | _ => false

namespace St

/-- Number of invoked writes. -/
def n (s : St K) : ℕ := s.wv.length

/-- Number of writes that executed Line 16. -/
def nA (s : St K) : ℕ := if s.wpc.preA then s.n - 1 else s.n

/-- Number of completed writes. -/
def c (s : St K) : ℕ := if s.wpc = .idle then s.n else s.n - 1

/-- Value of write number `m` (`0`: initial value). -/
def vals (v₀ : Fin K) (s : St K) (m : ℕ) : Fin K := (v₀ :: s.wv).getD m v₀

end St

/-- Initial abstract state. -/
def St.init (v₀ : Fin K) : St K where
  A j := decide (j = v₀)
  Bm _ := false
  f1 := false
  f2 := false
  last := v₀
  wpc := .idle
  rpc := .idle
  wv := []
  tagA _ := 0
  tagB _ := 0
  sN1 := 0
  sT := 0
  lo := 0
  rf := 0
  fl := 0
  pis := []

/-- Writer's internal step. -/
def stepW (s : St K) : St K :=
  match s.wpc with
  | .scanB v j => { s with wpc := WPC.scanNext v j (s.Bm j) }
  | .rdF1 v => { s with wpc := if s.f1 then .setB v else .setA v }
  | .setB v => { s with Bm := Function.update s.Bm s.last true,
                        tagB := Function.update s.tagB s.last s.n, wpc := .rdF2 v }
  | .rdF2 v => { s with wpc := if s.f2 then .clrB v else .rdF1' v }
  | .rdF1' v => { s with wpc := if s.f1 then .setA v else .clrB v }
  | .clrB v => { s with Bm := Function.update s.Bm s.last false, wpc := .setA v }
  | .setA v => { s with A := Function.update s.A v true, tagA := Function.update s.tagA v s.n,
                        wpc := WPC.afterSetA v }
  | .down v j => { s with A := Function.update s.A j false, wpc := WPC.downNext v j }
  | .up v j => { s with A := Function.update s.A j false, wpc := WPC.upNext v j }
  | _ => s

/-- Reader's internal step. -/
def stepR (s : St K) : St K :=
  match s.rpc with
  | .start => { s with f1 := true, rpc := .up false 0, sN1 := s.n, sT := s.nA }
  | .up snd j => { s with rpc := if s.A j then RPC.found j else RPC.upNext snd j,
                          rf := if s.A j then s.tagA j else s.rf,
                          sT := if s.A j = false ∧ snd = false ∧ ¬ (j.val + 1 < K) then s.nA
                            else s.sT }
  | .down val j => { s with rpc := RPC.downNext val j (s.A j),
                            rf := if s.A j then s.tagA j else s.rf }
  | .bscan j val => { s with rpc := RPC.bscanNext j val (s.Bm j),
                             rf := if s.Bm j then s.tagB j - 1 else s.rf }
  | .setF2 val => { s with f2 := true, rpc := .clr 0 val }
  | .clr j val => { s with Bm := Function.update s.Bm j false, rpc := RPC.clrNext j val }
  | .resF1 val => { s with f1 := false, rpc := .resF2 val }
  | .resF2 val => { s with f2 := false, rpc := .done val }
  | _ => s

variable (v₀ : Fin K)

/-- The abstract transition function. -/
def sstep (s : St K) : Lbl v₀ → St K
  | .inv .w (.write v) => { s with wpc := .scanB v 0, wv := s.wv ++ [v] }
  | .inv .r .read => { s with rpc := .start, lo := s.c }
  | .inv _ _ => s
  | .tau .w => stepW s
  | .tau .r => stepR s
  | .ret .w _ =>
    match s.wpc with
    | .done v => { s with last := v, wpc := .idle }
    | _ => s
  | .ret .r _ =>
    match s.rpc with
    | .done _ => { s with rpc := .idle, pis := s.pis ++ [s.rf], fl := s.rf }
    | _ => s

/-- The abstract state (with ghost variables) at the end of an execution. -/
def sOf (α : List (Lbl v₀)) : St K := α.foldl (sstep v₀) (St.init v₀)

/-- Which labels are enabled in an abstract state. -/
def Enabled (s : St K) : Lbl v₀ → Prop
  | .inv .w o => s.wpc = .idle ∧ ∃ v, o = .write v
  | .inv .r o => s.rpc = .idle ∧ o = .read
  | .tau .w => s.wpc ≠ .idle ∧ ∀ v, s.wpc ≠ .done v
  | .tau .r => s.rpc ≠ .idle ∧ ∀ val, s.rpc ≠ .done val
  | .ret .w x => s.wpc = .done x
  | .ret .r x => ∃ val, s.rpc = .done val ∧ x = val.getD v₀

/-- The concrete configuration corresponds to the abstract state. -/
structure Rel (C : Cfg v₀) (s : St K) : Prop where
  memA : ∀ j, C.mem (.a j) = s.A j
  memB : ∀ j, C.mem (.b j) = s.Bm j
  memF1 : C.mem .f1 = s.f1
  memF2 : C.mem .f2 = s.f2
  last : (C.loc .w).last = s.last
  wpc : (C.loc .w).wpc = s.wpc
  rpc : (C.loc .r).rpc = s.rpc
  pendW : C.pend .w = none ↔ s.wpc = .idle
  pendR : C.pend .r = none ↔ s.rpc = .idle

lemma rel_init : Rel v₀ (alg4 v₀).initCfg (St.init v₀) where
  memA j := rfl
  memB j := rfl
  memF1 := rfl
  memF2 := rfl
  last := rfl
  wpc := rfl
  rpc := rfl
  pendW := by simp [Impl.initCfg, St.init]
  pendR := by simp [Impl.initCfg, St.init]

/-! ### Simulation -/

@[simp] lemma RPC.found_ne_idle (j : Fin K) : RPC.found j ≠ .idle := by
  unfold RPC.found; split <;> simp
@[simp] lemma RPC.upNext_ne_idle (b : Bool) (j : Fin K) : RPC.upNext b j ≠ .idle := by
  unfold RPC.upNext; split <;> [simp; split <;> simp]
@[simp] lemma RPC.downNext_ne_idle (val j : Fin K) (x : Bool) : RPC.downNext val j x ≠ .idle := by
  unfold RPC.downNext; split <;> simp
@[simp] lemma RPC.bscanNext_ne_idle (j : Fin K) (val) (x : Bool) :
    RPC.bscanNext j val x ≠ .idle := by
  unfold RPC.bscanNext; split <;> simp
@[simp] lemma RPC.clrNext_ne_idle (j : Fin K) (val) : RPC.clrNext j val ≠ .idle := by
  unfold RPC.clrNext; split <;> simp
@[simp] lemma WPC.scanNext_ne_idle (v j : Fin K) (x : Bool) : WPC.scanNext v j x ≠ .idle := by
  unfold WPC.scanNext; split <;> [simp; split <;> simp]
@[simp] lemma WPC.upFrom_ne_idle (v : Fin K) (j : ℕ) : WPC.upFrom v j ≠ .idle := by
  unfold WPC.upFrom; split <;> simp
@[simp] lemma WPC.afterSetA_ne_idle (v : Fin K) : WPC.afterSetA v ≠ .idle := by
  unfold WPC.afterSetA; split <;> simp
@[simp] lemma WPC.downNext_ne_idle (v j : Fin K) : WPC.downNext v j ≠ .idle := by
  unfold WPC.downNext; split <;> simp
@[simp] lemma WPC.upNext_ne_idle (v j : Fin K) : WPC.upNext v j ≠ .idle := by
  unfold WPC.upNext; simp

lemma rel_step {C C' : Cfg v₀} {s : St K} {ℓ : Lbl v₀} (hR : Rel v₀ C s)
    (h : (alg4 v₀).step C ℓ = some C') : Enabled v₀ s ℓ ∧ Rel v₀ C' (sstep v₀ s ℓ) := by
  cases ℓ with
  | inv p o =>
    obtain ⟨hp, hal, hpend, hloc, hmem⟩ := Impl.step_inv h
    rcases hal with ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩
    · have hw := hR.pendW.1 hp
      refine ⟨⟨hw, v, rfl⟩, ?_⟩
      constructor <;> simp [sstep, hmem, hloc, hpend, hR.memA, hR.memB, hR.memF1, hR.memF2,
        hR.last, hR.rpc, hR.pendR, alg4, invoke]
    · have hr := hR.pendR.1 hp
      refine ⟨⟨hr, rfl⟩, ?_⟩
      constructor <;> simp [sstep, hmem, hloc, hpend, hR.memA, hR.memB, hR.memF1, hR.memF2,
        hR.last, hR.wpc, hR.pendW, alg4, invoke]
  | tau p =>
    obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
    cases p with
    | w =>
      have hw : s.wpc ≠ .idle := fun h' => hp (hR.pendW.2 h')
      simp only [alg4, act, actW, hR.wpc] at hact
      cases hs : s.wpc <;> simp only [hs] at hact <;> cases hact
      all_goals refine ⟨⟨hw, by simp [hs]⟩, ?_⟩
      all_goals constructor <;> simp [sstep, stepW, hs, hmem, hloc, hpend, hR.memA, hR.memB,
        hR.memF1, hR.memF2, hR.last, hR.rpc, hR.pendR, hR.pendW, Function.update_apply] <;>
        split <;> simp
    | r =>
      have hr : s.rpc ≠ .idle := fun h' => hp (hR.pendR.2 h')
      simp only [alg4, act, actR, hR.rpc] at hact
      cases hs : s.rpc <;> simp only [hs] at hact <;> cases hact
      all_goals refine ⟨⟨hr, by simp [hs]⟩, ?_⟩
      all_goals constructor <;> simp [sstep, stepR, hs, hmem, hloc, hpend, hR.memA, hR.memB,
        hR.memF1, hR.memF2, hR.last, hR.wpc, hR.pendR, hR.pendW, Function.update_apply] <;>
        split <;> simp
  | ret p x =>
    obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    cases p with
    | w =>
      simp only [alg4, act, actW, hR.wpc] at hact
      cases hs : s.wpc
      · exact absurd (hR.pendW.2 hs) hp
      all_goals simp only [hs] at hact; cases hact
      refine ⟨hs, ?_⟩
      constructor <;> simp [sstep, hs, hmem, hloc, hpend, hR.memA, hR.memB,
        hR.memF1, hR.memF2, hR.rpc, hR.pendR]
    | r =>
      simp only [alg4, act, actR, hR.rpc] at hact
      cases hs : s.rpc
      · exact absurd (hR.pendR.2 hs) hp
      all_goals simp only [hs] at hact; cases hact
      refine ⟨⟨_, hs, rfl⟩, ?_⟩
      constructor <;> simp [sstep, hs, hmem, hloc, hpend, hR.memA, hR.memB,
        hR.memF1, hR.memF2, hR.last, hR.wpc, hR.pendW]

/-- The abstract state of an execution corresponds to its final configuration, and every step
of a valid execution is enabled in the abstract state before it. -/
lemma rel_runFrom {C C' : Cfg v₀} {s : St K} (hR : Rel v₀ C s) {α : List (Lbl v₀)}
    (h : (alg4 v₀).runFrom C α = some C') : Rel v₀ C' (α.foldl (sstep v₀) s) := by
  induction α generalizing C s with
  | nil => simp at h; subst h; exact hR
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg4 v₀).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      exact ih (rel_step v₀ hR hs).2 h

lemma rel_run {C : Cfg v₀} {α : List (Lbl v₀)} (h : (alg4 v₀).run α = some C) :
    Rel v₀ C (sOf v₀ α) := rel_runFrom v₀ (rel_init v₀) h

lemma sOf_append (α β : List (Lbl v₀)) :
    sOf v₀ (α ++ β) = β.foldl (sstep v₀) (sOf v₀ α) := by
  simp [sOf, List.foldl_append]

lemma sOf_snoc (α : List (Lbl v₀)) (ℓ : Lbl v₀) :
    sOf v₀ (α ++ [ℓ]) = sstep v₀ (sOf v₀ α) ℓ := by
  simp [sOf, List.foldl_append]

/-- Every step of a valid execution is enabled in the abstract state. -/
lemma enabled_of_valid {α : List (Lbl v₀)} {ℓ : Lbl v₀} (h : (alg4 v₀).Valid (α ++ [ℓ])) :
    Enabled v₀ (sOf v₀ α) ℓ := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C₁, h1, h2⟩ := (alg4 v₀).runFrom_eq_some_of_append hC
  rw [Impl.runFrom_singleton] at h2
  exact (rel_step v₀ (rel_run v₀ h1) h2).1

end Alg4

end Cslib.SharedMemory
