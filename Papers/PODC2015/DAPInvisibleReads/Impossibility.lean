import Papers.PODC2015.DAPInvisibleReads.Scenario

/-!
# Theorems 1 and 2: no WDAP TM with wait-free read-only transactions ensures real-time order

Peluso, Palmieri, Romano, Ravindran, Quaglia. *Disjoint-Access Parallelism: Impossibility,
Possibility, and Cost of Transactional Memory Implementations.* PODC 2015, Section 3.

Processes `a` (running `T₄`), `b` (running `T₂`) and `c` (running `T₃`), transactional objects
`x ≠ y`. The execution `E` of Figure 1 is

  `E = R₄(y) · W₃(y) c₃ · W₂(x) c₂ · R₄(x) c₄`,

each block run solo. The reads of `T₄` complete and `T₄` commits by WFRO; `T₃` and `T₂` commit by
obstruction-freedom (Theorem 1) or, for Theorem 2, because they commit in the execution without
`T₄`, which they cannot distinguish from `E` since `T₄`'s first read is invisible.

The core of the argument (`core`) is an indistinguishability argument: by WDAP, the steps of `T₂`
commute with those of `T₃` and with `T₄`'s first read (at the time of these steps the transactions
are disjoint-access), so `E' = W₂(x) c₂ · R₄(y) · W₃(y) c₃ · R₄(x) c₄` is an execution in which
`R₄(x)` returns the same value `w` as in `E`. By `LegalReads`, `w` is the initial value or `T₂`'s
value. If it is `T₂`'s value, `E`'s history is `H_WRTO` and violates RTO; if it is the initial
value, `E'` violates WRTO (and RTO), since `T₂` committed before `T₄` began.

## Main results

* `theorem_1`: no WDAP TM with obstruction-free write transactions and wait-free read-only
  transactions ensures RTO.
* `theorem_2`: no WDAP TM with weakly progressive write transactions (`IsolatedWritesCommit`)
  and wait-free invisible read-only transactions ensures RTO.
* `theorem_1_wrto`, `theorem_2_wrto`: if such a TM ensures WRTO, it produces the history
  `H_WRTO` of Figure 1 (which satisfies WRTO but not RTO): this is the statement actually proved in
  the paper ("the TM cannot reject `H_WRTO`"); it contains the instance of Lemma 3 used there.
-/

namespace Podc.DAPInvisibleReads

open Cslib.SharedMemory

variable {X V P : Type} [DecidableEq P] [DecidableEq X]
variable {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι]
variable {I : Impl (tmSpec X V) B P L}

/-! ### Solo blocks -/

omit [DecidableEq X] in
lemma runFrom_taus_pend {q : P} {β : List (Lbl P X V)} (hβ : Taus q β)
    {C C' : Config (tmSpec X V) B P L} (h : I.runFrom C β = some C') : C'.pend = C.pend := by
  induction β generalizing C with
  | nil => simp at h; rw [h]
  | cons ℓ β ih =>
    rw [hβ ℓ (by simp)] at h
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C (.tau q) with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      rw [ih (fun ℓ' h' => hβ ℓ' (by simp [h'])) h, (Impl.step_tau hs).2.1]

omit [DecidableEq X] in
/-- Unfolding a completed solo block. -/
lemma blk_spec {C C' : Config (tmSpec X V) B P L} {p : P} {o : TOp X V}
    {β : List (Lbl P X V)} {r : Option V} (hβ : Taus p β)
    (h : I.runFrom C (Blk p o β r) = some C') :
    ∃ C₁, I.runFrom C (.inv p o :: β) = some C₁ ∧ C₁.pend p = some o ∧
      (∃ l, I.act p (C₁.loc p) = .ret r l) ∧ I.step C₁ (.ret p r) = some C' ∧
      C'.pend p = none := by
  have h' : I.runFrom C ((.inv p o :: β) ++ [.ret p r]) = some C' := by simpa [Blk] using h
  obtain ⟨C₁, h1, h2⟩ := I.runFrom_eq_some_of_append h'
  rw [Impl.runFrom_singleton] at h2
  obtain ⟨-, hp, -, l, hl, -⟩ := Impl.step_ret h2
  refine ⟨C₁, h1, ?_, ⟨l, hl⟩, h2, by simp [hp]⟩
  simp only [Impl.runFrom_cons] at h1
  cases hs : I.step C (.inv p o) with
  | none => simp [hs] at h1
  | some C₀ =>
    simp only [hs, Option.bind_some] at h1
    rw [runFrom_taus_pend hβ h1, (Impl.step_inv hs).2.2.1]; simp

omit [DecidableEq X] in
/-- A solo completion gives a block. -/
lemma blk_of_solo {C : Config (tmSpec X V) B P L} {p : P} {o : TOp X V} {v : V}
    (h : SoloCompletes I C p o v) :
    ∃ β, Taus p β ∧ ∃ C', I.runFrom C (Blk p o β (some v)) = some C' := by
  obtain ⟨β, hβ, hs⟩ := h
  obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨β, hβ, C', by simpa [Blk] using hC'⟩

omit [DecidableEq P] [DecidableEq X] [DecidableEq ι] in
lemma mem_blk_inv {p q : P} {o o' : TOp X V} {β : List (Lbl P X V)} {r : Option V}
    (hβ : Taus p β) (h : Label.inv q o' ∈ Blk p o β r) : q = p ∧ o' = o := by
  simp only [Blk, List.cons_append, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at h
  rcases h with h | h | h
  · simp only [Label.inv.injEq] at h; exact h
  · exact absurd (hβ _ h) (by simp)
  · simp at h

omit [DecidableEq X] in
lemma run_initCfg : I.run ([] : List (Lbl P X V)) = some I.initCfg := rfl

/-! ### The core argument -/

section Core

variable (v₀ : X → V) {a b c : P} {x y : X} {v₁ r₁ r₂ s₁ s₂ : V}
  {βa₁ βc₁ βc₂ βb₁ βb₂ : List (Lbl P X V)}

omit [DecidableEq P] [DecidableEq X] [DecidableEq ι] in
/-- The objects accessed by the blocks. -/
lemma inv_mem_scenario {ℓ : Lbl P X V} {q : P} {o : TOp X V}
    (ha₁ : Taus a βa₁) (hc₁ : Taus c βc₁) (hc₂ : Taus c βc₂) (hb₁ : Taus b βb₁)
    (hb₂ : Taus b βb₂) (hℓ : ℓ = .inv q o) :
    (ℓ ∈ bA v₀ a y βa₁ → q = a ∧ o = .read y) ∧
    (ℓ ∈ bC c y v₁ r₁ r₂ βc₁ βc₂ → q = c ∧ (o = .write y v₁ ∨ o = .tryC)) ∧
    (ℓ ∈ bB b x v₁ s₁ s₂ βb₁ βb₂ → q = b ∧ (o = .write x v₁ ∨ o = .tryC)) := by
  subst hℓ
  refine ⟨fun h => mem_blk_inv ha₁ h, fun h => ?_, fun h => ?_⟩
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨h1, h2⟩ := mem_blk_inv hc₁ h; exact ⟨h1, Or.inl h2⟩
    · obtain ⟨h1, h2⟩ := mem_blk_inv hc₂ h; exact ⟨h1, Or.inr h2⟩
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨h1, h2⟩ := mem_blk_inv hb₁ h; exact ⟨h1, Or.inl h2⟩
    · obtain ⟨h1, h2⟩ := mem_blk_inv hb₂ h; exact ⟨h1, Or.inr h2⟩

variable (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y)
  (ha₁ : Taus a βa₁) (hc₁ : Taus c βc₁) (hc₂ : Taus c βc₂) (hb₁ : Taus b βb₁) (hb₂ : Taus b βb₂)

/-- The two sides of the partition used with WDAP: `b` (accessing `x`) and the others
(accessing `y`). -/
def side (b : P) (p : P) : Bool := decide (p = b)

/-- The objects of the two sides. -/
def sideObj (x y : X) : Bool → Set X := fun s => if s then {x} else {y}

include hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ in
/-- **The commutation step** (the paper's Lemmas 1–3, as used in Theorems 1 and 2): under WDAP,
`R₄(y) · T₃ · T₂` and `T₂ · R₄(y) · T₃` lead to the same configuration. -/
lemma commute_scenario (hW : WDAP I) {D : Config (tmSpec X V) B P L}
    (hrun : I.runFrom I.initCfg (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂) = some D) :
    I.runFrom I.initCfg (bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bA v₀ a y βa₁ ++
      bC c y v₁ r₁ r₂ βc₁ βc₂) = some D := by
  set α := bA v₀ a y βa₁
  set γ := bC c y v₁ r₁ r₂ βc₁ βc₂
  set β := bB b x v₁ s₁ s₂ βb₁ βb₂
  have pA : ∀ ℓ ∈ α, ℓ.proc = a := proc_blk ha₁
  have pB : ∀ ℓ ∈ β, ℓ.proc = b := proc_append (proc_blk hb₁) (proc_blk hb₂)
  have pC : ∀ ℓ ∈ γ, ℓ.proc = c := proc_append (proc_blk hc₁) (proc_blk hc₂)
  have hS : Disjoint (sideObj x y true) (sideObj x y false) := by simp [sideObj, hxy]
  have hfab : ∀ q, q ≠ b → side b q ≠ side b b := by intro q hq; simp [side, hq]
  have key := fun {ℓ : Lbl P X V} {q : P} {o : TOp X V} (h : ℓ = .inv q o) =>
    inv_mem_scenario (v₁ := v₁) (r₁ := r₁) (r₂ := r₂) (s₁ := s₁) (s₂ := s₂) (x := x) (y := y) v₀ ha₁
    hc₁ hc₂ hb₁ hb₂ h
  have hrun' : I.runFrom I.initCfg (α ++ (γ ++ β)) = some D := by
    rw [← List.append_assoc]; exact hrun
  obtain ⟨Cα, h1, h2⟩ := I.runFrom_eq_some_of_append hrun'
  -- `T₃` and `T₂` commute after `R₄(y)`
  have hα : I.run α = some Cα := h1
  have hnc₁ := noContendFrom_of_wdap hW hα (fun ℓ => ℓ ∈ γ ∨ ℓ ∈ β) (side b) (sideObj x y) hS
    (by
      intro p z hz
      obtain ⟨o, ho, hz⟩ := hz
      obtain ⟨ℓ, hℓ, hinv⟩ := List.mem_filterMap.1 ho
      obtain ⟨rfl, rfl⟩ := (key (Label.eq_inv_of_invOf_eq_some hinv)).1 hℓ
      simp only [TOp.obj, Option.some.injEq] at hz; subst hz
      simp [side, sideObj, hab])
    (by
      intro ℓ hℓ q o z hq hz
      rcases hℓ with hℓ | hℓ
      · obtain ⟨rfl, ho⟩ := (key hq).2.1 hℓ
        rcases ho with rfl | rfl <;> simp only [TOp.obj, Option.some.injEq, reduceCtorEq] at hz
        subst hz; simp [side, sideObj, Ne.symm hbc]
      · obtain ⟨rfl, ho⟩ := (key hq).2.2 hℓ
        rcases ho with rfl | rfl <;> simp only [TOp.obj, Option.some.injEq, reduceCtorEq] at hz
        subst hz; simp [side, sideObj])
    (Ne.symm hbc) (hfab c (Ne.symm hbc))
  have h3 := commute (Ne.symm hbc) _ β γ Cα D (fun ℓ h => ⟨pC ℓ h, Or.inl h⟩)
    (fun ℓ h => ⟨pB ℓ h, Or.inr h⟩) hnc₁ h2
  obtain ⟨Cαβ, h4, h5⟩ := I.runFrom_eq_some_of_append h3
  have h6 : I.runFrom I.initCfg (α ++ β) = some Cαβ := by
    rw [Impl.runFrom_append_of_eq I h1]; exact h4
  -- `R₄(y)` and `T₂` commute from the initial configuration
  have hnc₂ := noContendFrom_of_wdap hW run_initCfg (fun ℓ => ℓ ∈ α ∨ ℓ ∈ β) (side b)
    (sideObj x y) hS (by intro p z hz; obtain ⟨o, ho, -⟩ := hz; simp at ho)
    (by
      intro ℓ hℓ q o z hq hz
      rcases hℓ with hℓ | hℓ
      · obtain ⟨rfl, rfl⟩ := (key hq).1 hℓ
        simp only [TOp.obj, Option.some.injEq] at hz; subst hz; simp [side, sideObj, hab]
      · obtain ⟨rfl, ho⟩ := (key hq).2.2 hℓ
        rcases ho with rfl | rfl <;> simp only [TOp.obj, Option.some.injEq, reduceCtorEq] at hz
        subst hz; simp [side, sideObj])
    hab (hfab a hab)
  have h7 := commute hab _ β α I.initCfg Cαβ (fun ℓ h => ⟨pA ℓ h, Or.inl h⟩)
    (fun ℓ h => ⟨pB ℓ h, Or.inr h⟩) hnc₂ h6
  rw [Impl.runFrom_append_of_eq I h7]
  exact h5

omit [DecidableEq X] [DecidableEq ι] in
include hab hac ha₁ hc₁ hc₂ hb₁ hb₂ in
/-- The bookkeeping of `T₄` after `R₄(y) · T₃ · T₂`. -/
lemma pstate_a_before (w : V) {βa₂ : List (Lbl P X V)} (ha₂ : Taus a βa₂) :
    pstate (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++ bB b x v₁ s₁ s₂ βb₁ βb₂) a =
      ⟨[], ⟨[(.read y, some (v₀ y))], none⟩⟩ ∧
    pstate ((bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++ bB b x v₁ s₁ s₂ βb₁ βb₂) ++
      Blk a (.read x) βa₂ (some w)) a =
      ⟨[], ⟨[(.read y, some (v₀ y)), (.read x, some w)], none⟩⟩ := by
  constructor <;>
  simp [pstate_eq_foldl, bA, bC, bB, projP_append, foldl_projP_blk ha₁, foldl_projP_blk ha₂,
    foldl_projP_blk hc₁, foldl_projP_blk hc₂, foldl_projP_blk hb₁, foldl_projP_blk hb₂,
    Ne.symm hab, Ne.symm hac, PState.step, PState.init, endsTx, TxRec.empty]

include hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ in
/-- **Core of Theorems 1 and 2.** Under WDAP, WFRO and legal reads, if `R₄(y) · T₃ · T₂` is an
execution (with both write transactions committed), then the TM produces a history that does not
preserve RTO; and if it ensures WRTO, the execution `E` of Figure 1 exists with `R₄(x)` returning
`T₂`'s value (so its history is `H_WRTO`). -/
theorem core (hW : WDAP I) (hWF : WaitFreeReadOnly I) (hL : LegalReads I v₀)
    {D : Config (tmSpec X V) B P L}
    (hrun : I.runFrom I.initCfg (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂) = some D) :
    ∃ w u βa₂ βa₃, Taus a βa₂ ∧ Taus a βa₃ ∧ (w = v₀ x ∨ w = v₁) ∧
      I.Valid (execE v₀ a b c x y v₁ w r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
      I.Valid (execE' v₀ a b c x y v₁ w r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) := by
  set E₀ := bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++ bB b x v₁ s₁ s₂ βb₁ βb₂ with hE₀
  have pA : ∀ ℓ ∈ bA v₀ a y βa₁, ℓ.proc = a := proc_blk ha₁
  have pB : ∀ ℓ ∈ bB b x v₁ s₁ s₂ βb₁ βb₂, ℓ.proc = b :=
    proc_append (proc_blk hb₁) (proc_blk hb₂)
  have pC : ∀ ℓ ∈ bC c y v₁ r₁ r₂ βc₁ βc₂, ℓ.proc = c :=
    proc_append (proc_blk hc₁) (proc_blk hc₂)
  have hrun₀ : I.run E₀ = some D := hrun
  -- `a` is idle after `E₀`
  obtain ⟨Cαγ, h1, h2⟩ := I.runFrom_eq_some_of_append hrun
  obtain ⟨Cα, h3, h4⟩ := I.runFrom_eq_some_of_append h1
  have hDa : D.pend a = none := by
    rw [(I.runFrom_other h2 (q := a) (fun ℓ hℓ => by rw [pB ℓ hℓ]; exact Ne.symm hab)).2,
      (I.runFrom_other h4 (q := a) (fun ℓ hℓ => by rw [pC ℓ hℓ]; exact Ne.symm hac)).2]
    obtain ⟨-, -, -, -, -, h⟩ := blk_spec ha₁ h3
    exact h
  -- `R₄(x)`
  have hps := fun w (βa₂ : List (Lbl P X V)) (ha₂ : Taus a βa₂) =>
    pstate_a_before (v₁ := v₁) (r₁ := r₁) (r₂ := r₂) (s₁ := s₁) (s₂ := s₂) (x := x) (y := y) v₀ hab hac ha₁ hc₁
      hc₂ hb₁ hb₂ w ha₂
  have hnw₀ : ¬ HasWrite E₀ (cur E₀ a) := by
    have := (hps v₁ [] (by simp [Taus])).1
    simp only [HasWrite, cur, txRec, hE₀, this]; simp
  obtain ⟨w, hw⟩ := hWF E₀ D a (.read x) hrun₀ hDa (by simp [TOp.IsWrite]) hnw₀
  obtain ⟨βa₂, ha₂, D₁, hD₁⟩ := blk_of_solo hw
  obtain ⟨C₁, hC₁, hp₁, ⟨l, hl⟩, -, hD₁a⟩ := blk_spec ha₂ hD₁
  have hrunC₁ : I.run (E₀ ++ (.inv a (.read x) :: βa₂)) = some C₁ := by
    rw [Impl.run_append_of_eq I hrun₀]; exact hC₁
  have hw' : w = v₀ x ∨ w = v₁ := by
    rcases hL _ C₁ a x w l hrunC₁ hp₁ hl with h | ⟨q, hq⟩
    · exact Or.inl h
    · right
      have key := inv_mem_scenario (v₁ := v₁) (r₁ := r₁) (r₂ := r₂) (s₁ := s₁) (s₂ := s₂) (x := x) (y := y)
        v₀ ha₁ hc₁ hc₂ hb₁ hb₂ (ℓ := .inv q (.write x w)) rfl
      simp only [hE₀, List.mem_append, List.mem_cons] at hq
      rcases hq with ((hq | hq) | hq) | hq | hq
      · exact absurd (key.1 hq).2 (by simp)
      · rcases (key.2.1 hq).2 with h | h <;> simp_all
      · rcases (key.2.2 hq).2 with h | h <;> simp_all
      · simp at hq
      · exact absurd (ha₂ _ hq) (by simp)
  -- `c₄`
  have hrunD₁ : I.run (E₀ ++ Blk a (.read x) βa₂ (some w)) = some D₁ := by
    rw [Impl.run_append_of_eq I hrun₀]; exact hD₁
  have hnw₁ : ¬ HasWrite (E₀ ++ Blk a (.read x) βa₂ (some w))
      (cur (E₀ ++ Blk a (.read x) βa₂ (some w)) a) := by
    have := (hps w βa₂ ha₂).2
    simp only [HasWrite, cur, txRec, hE₀, this]; simp
  obtain ⟨u, hu⟩ := hWF _ D₁ a .tryC hrunD₁ hD₁a (by simp [TOp.IsWrite]) hnw₁
  obtain ⟨βa₃, ha₃, D₂, hD₂⟩ := blk_of_solo hu
  have hrunE : I.runFrom I.initCfg (E₀ ++ (Blk a (.read x) βa₂ (some w) ++
      Blk a .tryC βa₃ (some u))) = some D₂ := by
    rw [← List.append_assoc, Impl.runFrom_append_of_eq I hrunD₁]; exact hD₂
  refine ⟨w, u, βa₂, βa₃, ha₂, ha₃, hw', ⟨D₂, ?_⟩, ⟨D₂, ?_⟩⟩
  · simpa [execE, bR, hE₀, Impl.run] using hrunE
  · have hc := commute_scenario v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hrun
    have : I.runFrom I.initCfg ((bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bA v₀ a y βa₁ ++
        bC c y v₁ r₁ r₂ βc₁ βc₂) ++ (Blk a (.read x) βa₂ (some w) ++
        Blk a .tryC βa₃ (some u))) = some D₂ := by
      rw [Impl.runFrom_append_of_eq I hc]
      rw [hE₀, Impl.runFrom_append_of_eq I hrun] at hrunE; exact hrunE
    simpa [execE', bR, Impl.run] using this

include hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ in
/-- From the core: a history (with unique written values) violating RTO. -/
theorem not_ensuresRTO_of_run (hW : WDAP I) (hWF : WaitFreeReadOnly I) (hL : LegalReads I v₀)
    (hx : v₁ ≠ v₀ x) (hy : v₁ ≠ v₀ y) {D : Config (tmSpec X V) B P L}
    (hrun : I.runFrom I.initCfg (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂) = some D) :
    ¬ EnsuresRTO I v₀ := by
  intro H
  obtain ⟨w, u, βa₂, βa₃, ha₂, ha₃, hw, hE, hE'⟩ :=
    core v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hrun
  rcases hw with rfl | rfl
  · exact not_preservesWRTO_execE' v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy
      (H _ hE' (uniqueWrites_execE' v₀ ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy hx hy)).preservesWRTO
  · exact not_preservesRTO_execE v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy
      (H _ hE (uniqueWrites_execE v₀ ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy hx hy))

include hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ in
/-- From the core: explicitly, `E` (with `R₄(x)` returning `T₂`'s value) or `E'` (with `R₄(x)`
returning the initial value) is an execution whose history violates RTO. -/
theorem violation_of_run (hW : WDAP I) (hWF : WaitFreeReadOnly I) (hL : LegalReads I v₀)
    {D : Config (tmSpec X V) B P L}
    (hrun : I.runFrom I.initCfg (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂) = some D) :
    ∃ u βa₂ βa₃,
      (I.Valid (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
        ¬ PreservesRTO v₀ (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂)) ∨
      (I.Valid (execE' v₀ a b c x y v₁ (v₀ x) r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
        ¬ PreservesRTO v₀
          (execE' v₀ a b c x y v₁ (v₀ x) r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂)) := by
  obtain ⟨w, u, βa₂, βa₃, ha₂, ha₃, hw, hE, hE'⟩ :=
    core v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hrun
  refine ⟨u, βa₂, βa₃, ?_⟩
  rcases hw with rfl | rfl
  · exact Or.inr ⟨hE', fun H => not_preservesWRTO_execE' v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁
      hb₂ hxy H.preservesWRTO⟩
  · exact Or.inl ⟨hE, not_preservesRTO_execE v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy⟩

include hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ in
/-- From the core, under WRTO: the TM produces `H_WRTO`. -/
theorem hWRTO_of_run (hW : WDAP I) (hWF : WaitFreeReadOnly I) (hL : LegalReads I v₀)
    (hWR : EnsuresWRTO I v₀) (hx : v₁ ≠ v₀ x) (hy : v₁ ≠ v₀ y) {D : Config (tmSpec X V) B P L}
    (hrun : I.runFrom I.initCfg (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂) = some D) :
    ∃ u βa₂ βa₃, Taus a βa₂ ∧ Taus a βa₃ ∧
      I.Valid (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
      ¬ PreservesRTO v₀ (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) := by
  obtain ⟨w, u, βa₂, βa₃, ha₂, ha₃, hw, hE, hE'⟩ :=
    core v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hrun
  rcases hw with rfl | rfl
  · exact absurd (hWR _ hE' (uniqueWrites_execE' v₀ ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy hx hy))
      (not_preservesWRTO_execE' v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂
      hxy)
  · exact ⟨u, βa₂, βa₃, ha₂, ha₃, hE,
      not_preservesRTO_execE v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy⟩

end Core

/-! ### Running the transactions of Figure 1 -/

section Run

omit [DecidableEq X] [DecidableEq ι] in
lemma pstate_append_taus {q : P} {β : List (Lbl P X V)} (hβ : Taus q β) (π : List (Lbl P X V))
    (p : P) : pstate (π ++ β) p = pstate π p := by
  rw [pstate_eq_foldl, projP_append, List.foldl_append]
  have : projP β p = if q = p then β else [] := projP_of_proc (fun ℓ h => by simp [hβ ℓ h, Label.proc]) p
  rw [this]; split_ifs <;> simp [foldl_taus hβ, pstate_eq_foldl]

omit [DecidableEq X] [DecidableEq ι] in
lemma pstate_append_blk {q : P} {o : TOp X V} {β : List (Lbl P X V)} {r : Option V}
    (hβ : Taus q β) (π : List (Lbl P X V)) (p : P) :
    pstate (π ++ Blk q o β r) p =
      if q = p then ((pstate π p).step (.inv q o)).step (.ret q r) else pstate π p := by
  rw [pstate_eq_foldl, projP_append, List.foldl_append, foldl_projP_blk hβ, ← pstate_eq_foldl]

omit [DecidableEq X] in
/-- A two-operation write transaction `W(z, v₁) · tryC`, run solo by `p` from a configuration in
which `p` has no transaction yet, completes and commits, given progress for such transactions. -/
lemma write_txn {α₁ : List (Lbl P X V)} {C : Config (tmSpec X V) B P L} {p : P} (z : X) (v₁ : V)
    (hprog : ∀ α₂ C' (o : TOp X V), I.run (α₁ ++ α₂) = some C' → (∀ ℓ ∈ α₂, ℓ.proc = p) →
      C'.pend p = none → (o.IsWrite ∨ HasWrite (α₁ ++ α₂) (cur (α₁ ++ α₂) p)) →
      ∃ v, SoloCompletes I C' p o v)
    (hC : I.run α₁ = some C) (hp : C.pend p = none) (hα₁ : pstate α₁ p = PState.init) :
    ∃ r₁ r₂ β₁ β₂ D, Taus p β₁ ∧ Taus p β₂ ∧
      I.runFrom C (Blk p (.write z v₁) β₁ (some r₁) ++ Blk p .tryC β₂ (some r₂)) = some D := by
  obtain ⟨r₁, h1⟩ := hprog [] C (.write z v₁) (by simpa using hC) (by simp) hp
    (Or.inl (by simp [TOp.IsWrite]))
  obtain ⟨β₁, hβ₁, C₁, hC₁⟩ := blk_of_solo h1
  obtain ⟨-, -, -, -, -, hp₁⟩ := blk_spec hβ₁ hC₁
  have hrun₁ : I.run (α₁ ++ Blk p (.write z v₁) β₁ (some r₁)) = some C₁ := by
    rw [Impl.run_append_of_eq I hC]; exact hC₁
  obtain ⟨r₂, h2⟩ := hprog _ C₁ .tryC hrun₁ (proc_blk hβ₁) hp₁ (Or.inr (by
    left
    refine ⟨z, v₁, some r₁, ?_⟩
    simp [cur, txRec, pstate_append_blk hβ₁, hα₁, PState.step, PState.init, endsTx,
      TxRec.empty]))
  obtain ⟨β₂, hβ₂, D, hD⟩ := blk_of_solo h2
  exact ⟨r₁, r₂, β₁, β₂, D, hβ₁, hβ₂, by rw [Impl.runFrom_append_of_eq I hC₁]; exact hD⟩

omit [DecidableEq X] in
/-- `T₄`'s first read `R₄(y)`, run solo from the initial configuration, returns the initial value
(by WFRO and legal reads). -/
lemma first_read (v₀ : X → V) (hWF : WaitFreeReadOnly I) (hL : LegalReads I v₀) (a : P) (y : X) :
    ∃ βa₁ C, Taus a βa₁ ∧ I.runFrom I.initCfg (bA v₀ a y βa₁) = some C := by
  obtain ⟨v, hv⟩ := hWF [] I.initCfg a (.read y) run_initCfg rfl (by simp [TOp.IsWrite])
    (by simp [HasWrite, cur, txRec, pstate, projP, PState.init, TxRec.empty])
  obtain ⟨β, hβ, C, hC⟩ := blk_of_solo hv
  obtain ⟨C₁, hC₁, hp₁, ⟨l, hl⟩, -⟩ := blk_spec hβ hC
  rcases hL _ C₁ a y v l hC₁ hp₁ hl with h | ⟨q, hq⟩
  · subst h; exact ⟨β, C, hβ, hC⟩
  · simp only [List.mem_cons] at hq
    rcases hq with hq | hq
    · simp at hq
    · exact absurd (hβ _ hq) (by simp)

omit [DecidableEq X] in
/-- The steps of a read of a transaction without writes do not change the memory, under IRO. -/
lemma taus_mem (hIRO : InvisibleReads I) {p : P} {z : X} :
    ∀ (β : List (Lbl P X V)) (π : List (Lbl P X V)) (C C' : Config (tmSpec X V) B P L),
      Taus p β → I.run π = some C → C.pend p = some (.read z) → ¬ HasWrite π (cur π p) →
      I.runFrom C β = some C' → C'.mem = C.mem
  | [], _, C, C', _, _, _, _, h => by simp at h; rw [h]
  | ℓ :: β, π, C, C', hβ, hπ, hp, hnw, h => by
    have hℓ := hβ ℓ (by simp)
    subst hℓ
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C (.tau p) with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨-, hpend, i, o, k, hact, hmem, -⟩ := Impl.step_tau hs
      have htriv := hIRO π C p z hπ hp hnw i o k hact
      have hm₁ : C₁.mem = C.mem := by rw [hmem, htriv]; simp
      have hπ₁ : I.run (π ++ [.tau p]) = some C₁ := by
        rw [Impl.run_append_of_eq I hπ, Impl.runFrom_singleton]; exact hs
      have hτ : Taus p ([.tau p] : List (Lbl P X V)) := by simp [Taus]
      have := taus_mem hIRO β (π ++ [.tau p]) C₁ C' (fun ℓ h => hβ ℓ (by simp [h])) hπ₁
        (by rw [hpend]; exact hp) (by simpa [cur, HasWrite, txRec, pstate_append_taus hτ] using hnw) h
      rw [this, hm₁]

omit [DecidableEq X] in
/-- Under IRO, `T₄`'s first read does not change the memory. -/
lemma invisible_first_read (v₀ : X → V) (hIRO : InvisibleReads I) {a : P} {y : X}
    {βa₁ : List (Lbl P X V)} (ha₁ : Taus a βa₁) {Cα : Config (tmSpec X V) B P L}
    (hα : I.runFrom I.initCfg (bA v₀ a y βa₁) = some Cα) :
    Impl.AgreeOn {q | q ≠ a} I.initCfg Cα := by
  obtain ⟨C₁, hC₁, -, -, hret, -⟩ := blk_spec ha₁ hα
  simp only [Impl.runFrom_cons] at hC₁
  cases hs : I.step I.initCfg (.inv a (.read y)) with
  | none => simp [hs] at hC₁
  | some C₀ =>
    simp only [hs, Option.bind_some] at hC₁
    obtain ⟨-, -, hp₀, -, hm₀⟩ := Impl.step_inv hs
    have hπ : I.run [.inv a (.read y)] = some C₀ := by
      rw [Impl.run, Impl.runFrom_singleton]; exact hs
    have hm := taus_mem (z := y) hIRO βa₁ _ C₀ C₁ ha₁ hπ (by rw [hp₀]; simp)
      (by simp [HasWrite, cur, txRec, pstate, projP, Label.proc, PState.step, PState.init,
        TxRec.empty]) hC₁
    obtain ⟨-, -, hm', -⟩ := Impl.step_ret hret
    refine ⟨by rw [hm', hm, hm₀], fun q hq => ?_, fun q hq => ?_⟩ <;>
    · have := I.runFrom_other hα (q := q) (fun ℓ h => by rw [proc_blk ha₁ ℓ h]; exact Ne.symm hq)
      first | exact this.1.symm | exact this.2.symm

/-- The execution `R₄(y) · T₃ · T₂` under obstruction-freedom (Theorem 1). -/
lemma run_theorem_1 (v₀ : X → V) (hOF : ObstructionFreeWrites I) (hWF : WaitFreeReadOnly I)
    (hL : LegalReads I v₀) {a b c : P} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x y : X)
    (v₁ : V) :
    ∃ βa₁ βc₁ βc₂ βb₁ βb₂ r₁ r₂ s₁ s₂ D, Taus a βa₁ ∧ Taus c βc₁ ∧ Taus c βc₂ ∧ Taus b βb₁ ∧
      Taus b βb₂ ∧ I.runFrom I.initCfg (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
        bB b x v₁ s₁ s₂ βb₁ βb₂) = some D := by
  obtain ⟨βa₁, Cα, ha₁, hα⟩ := first_read v₀ hWF hL a y
  have pA : ∀ ℓ ∈ bA v₀ a y βa₁, ℓ.proc = a := proc_blk ha₁
  have hpα : ∀ p, p ≠ a → pstate (bA v₀ a y βa₁) p = PState.init := by
    intro p hp
    rw [show bA v₀ a y βa₁ = [] ++ Blk a (.read y) βa₁ (some (v₀ y)) from rfl,
      pstate_append_blk ha₁]
    simp [Ne.symm hp, pstate, projP]
  -- `T₃` commits (obstruction-freedom: it runs solo)
  obtain ⟨r₁, r₂, βc₁, βc₂, Cγ, hc₁, hc₂, hγ⟩ := write_txn (C := Cα) (p := c) y v₁
    (fun α₂ C' o h1 h2 h3 h4 => hOF _ α₂ C' c o h1
      (by simp [Began, cur, txRec, hpα c (Ne.symm hac), PState.init, TxRec.empty]) h2 h3 h4)
    hα (by rw [(I.runFrom_other hα (q := c) (fun ℓ h => by rw [pA ℓ h]; exact hac)).2]; rfl)
    (hpα c (Ne.symm hac))
  set γ := Blk c (.write y v₁) βc₁ (some r₁) ++ Blk c .tryC βc₂ (some r₂)
  have pC : ∀ ℓ ∈ γ, ℓ.proc = c := proc_append (proc_blk hc₁) (proc_blk hc₂)
  have hαγ : I.run (bA v₀ a y βa₁ ++ γ) = some Cγ := by
    rw [Impl.run_append_of_eq I hα]; exact hγ
  have hpb : pstate (bA v₀ a y βa₁ ++ γ) b = PState.init := by
    simp [γ, ← List.append_assoc, pstate_append_blk hc₁, pstate_append_blk hc₂,
      Ne.symm hbc, hpα b hab.symm]
  -- `T₂` commits (obstruction-freedom: it runs solo)
  obtain ⟨s₁, s₂, βb₁, βb₂, D, hb₁, hb₂, hβ⟩ := write_txn (C := Cγ) (p := b) x v₁
    (fun α₂ C' o h1 h2 h3 h4 => hOF _ α₂ C' b o h1
      (by simp [Began, cur, txRec, hpb, PState.init, TxRec.empty]) h2 h3 h4)
    hαγ (by
      rw [(I.runFrom_other hγ (q := b) (fun ℓ h => by rw [pC ℓ h]; exact Ne.symm hbc)).2,
        (I.runFrom_other hα (q := b) (fun ℓ h => by rw [pA ℓ h]; exact hab)).2]; rfl)
    hpb
  exact ⟨βa₁, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, D, ha₁, hc₁, hc₂, hb₁, hb₂,
    (Impl.runFrom_append_of_eq I hαγ _).trans hβ⟩

/-- The execution `R₄(y) · T₃ · T₂` under weak progressiveness and invisible reads (Theorem 2):
`T₃` and `T₂` commit in the execution without `T₄`, and cannot distinguish it from the one with
`T₄`'s invisible first read. -/
lemma run_theorem_2 (v₀ : X → V) (hWP : IsolatedWritesCommit I) (hWF : WaitFreeReadOnly I)
    (hIRO : InvisibleReads I) (hL : LegalReads I v₀) {a b c : P} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (x y : X) (v₁ : V) :
    ∃ βa₁ βc₁ βc₂ βb₁ βb₂ r₁ r₂ s₁ s₂ D, Taus a βa₁ ∧ Taus c βc₁ ∧ Taus c βc₂ ∧ Taus b βb₁ ∧
      Taus b βb₂ ∧ I.runFrom I.initCfg (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
        bB b x v₁ s₁ s₂ βb₁ βb₂) = some D := by
  obtain ⟨βa₁, Cα, ha₁, hα⟩ := first_read v₀ hWF hL a y
  have hag := invisible_first_read v₀ hIRO ha₁ hα
  have hinit : ∀ p, pstate ([] : List (Lbl P X V)) p = PState.init := fun _ => rfl
  -- `T₃` alone from the initial configuration
  obtain ⟨r₁, r₂, βc₁, βc₂, G₁, hc₁, hc₂, hγ⟩ := write_txn (C := I.initCfg) (p := c) y v₁
    (fun α₂ C' o h1 h2 h3 h4 => hWP [] α₂ C' c o h1
      (by intro q; simp [Began, cur, txRec, hinit, PState.init, TxRec.empty]) h2 h3 h4)
    run_initCfg rfl (hinit c)
  set γ := Blk c (.write y v₁) βc₁ (some r₁) ++ Blk c .tryC βc₂ (some r₂)
  have pC : ∀ ℓ ∈ γ, ℓ.proc = c := proc_append (proc_blk hc₁) (proc_blk hc₂)
  have hpγ : ∀ q, pstate γ q = if c = q then ⟨[⟨[(.write y v₁, some r₁), (.tryC, some r₂)],
      none⟩], TxRec.empty⟩ else PState.init := by
    intro q
    rw [show γ = [] ++ Blk c (.write y v₁) βc₁ (some r₁) ++ Blk c .tryC βc₂ (some r₂) from rfl,
      pstate_append_blk hc₂, pstate_append_blk hc₁, hinit]
    split_ifs <;> simp [PState.step, PState.init, endsTx, TxRec.empty]
  -- `T₂` alone after `T₃`
  obtain ⟨s₁, s₂, βb₁, βb₂, G₂, hb₁, hb₂, hβ⟩ := write_txn (C := G₁) (p := b) x v₁
    (fun α₂ C' o h1 h2 h3 h4 => hWP γ α₂ C' b o h1
      (by
        intro q
        simp only [Began, cur, txRec, hpγ q]
        split_ifs <;> simp [PState.init, TxRec.empty])
      h2 h3 h4)
    hγ (by rw [(I.runFrom_other hγ (q := b) (fun ℓ h => by rw [pC ℓ h]; exact Ne.symm hbc)).2]; rfl)
    (by simp [hpγ b, Ne.symm hbc])
  -- transfer to the execution with `T₄`'s invisible first read
  have hγβ : I.runFrom I.initCfg (γ ++ (Blk b (.write x v₁) βb₁ (some s₁) ++
      Blk b .tryC βb₂ (some s₂))) = some G₂ := (Impl.runFrom_append_of_eq I hγ _).trans hβ
  obtain ⟨D, hD, -⟩ := Impl.runFrom_agreeOn hag (fun ℓ h => by
    rcases List.mem_append.1 h with h | h
    · show ℓ.proc ≠ a; rw [pC ℓ h]; exact Ne.symm hac
    · show ℓ.proc ≠ a; rw [proc_append (proc_blk hb₁) (proc_blk hb₂) ℓ h]; exact Ne.symm hab)
    hγβ
  exact ⟨βa₁, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, D, ha₁, hc₁, hc₂, hb₁, hb₂,
    by simpa [γ, bC, bB, List.append_assoc] using (Impl.runFrom_append_of_eq I hα _).trans hD⟩

end Run

/-! ### Theorems 1 and 2 -/

section Theorems

variable (v₀ : X → V) {a b c : P} {x y : X}

/-- **Theorem 1** of the paper. No WDAP TM with obstruction-free write transactions and wait-free
read-only transactions (whose reads return the initial value or a written value) ensures
real-time order: some execution (in fact `E` or `E'` of Figure 1, with three processes and two
objects) produces a history with unique written values that does not preserve RTO. The value
domain must contain a value other than the initial values of `x` and `y` (to write fresh
versions). -/
theorem theorem_1 (hW : WDAP I) (hOF : ObstructionFreeWrites I) (hWF : WaitFreeReadOnly I)
    (hL : LegalReads I v₀) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y)
    (hV : ∃ v : V, v ≠ v₀ x ∧ v ≠ v₀ y) :
    ¬ EnsuresRTO I v₀ := by
  obtain ⟨v₁, hx, hy⟩ := hV
  obtain ⟨βa₁, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, D, ha₁, hc₁, hc₂, hb₁, hb₂, hrun⟩ :=
    run_theorem_1 v₀ hOF hWF hL hab hac hbc x y v₁
  exact not_ensuresRTO_of_run v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hx hy hrun

/-- **Theorem 1, as proved in the paper**: a WDAP TM with obstruction-free write transactions and
wait-free read-only transactions that ensures WRTO produces the history `H_WRTO` of Figure 1
(`R₄(y)` returns the initial value, `R₄(x)` returns `T₂`'s value `v₁`, all transactions commit),
which does not preserve RTO. -/
theorem theorem_1_wrto (hW : WDAP I) (hOF : ObstructionFreeWrites I) (hWF : WaitFreeReadOnly I)
    (hL : LegalReads I v₀) (hWR : EnsuresWRTO I v₀) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (v₁ : V) (hx : v₁ ≠ v₀ x) (hy : v₁ ≠ v₀ y) :
    ∃ βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂ r₁ r₂ s₁ s₂ u,
      I.Valid (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
      ¬ PreservesRTO v₀ (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) := by
  obtain ⟨βa₁, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, D, ha₁, hc₁, hc₂, hb₁, hb₂, hrun⟩ :=
    run_theorem_1 v₀ hOF hWF hL hab hac hbc x y v₁
  obtain ⟨u, βa₂, βa₃, -, -, hE, hnot⟩ :=
    hWRTO_of_run v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hWR hx hy hrun
  exact ⟨βa₁, βa₂, βa₃, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, u, hE, hnot⟩

/-- **Theorem 2** of the paper. No WDAP TM with weakly progressive write transactions (write
transactions that run in isolation commit) and wait-free invisible read-only transactions (whose
reads return the initial value or a written value) ensures real-time order (as `theorem_1`). -/
theorem theorem_2 (hW : WDAP I) (hWP : IsolatedWritesCommit I) (hWF : WaitFreeReadOnly I)
    (hIRO : InvisibleReads I) (hL : LegalReads I v₀) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (hV : ∃ v : V, v ≠ v₀ x ∧ v ≠ v₀ y) : ¬ EnsuresRTO I v₀ := by
  obtain ⟨v₁, hx, hy⟩ := hV
  obtain ⟨βa₁, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, D, ha₁, hc₁, hc₂, hb₁, hb₂, hrun⟩ :=
    run_theorem_2 v₀ hWP hWF hIRO hL hab hac hbc x y v₁
  exact not_ensuresRTO_of_run v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hx hy hrun

/-- **Theorem 2, as proved in the paper**: such a TM that ensures WRTO produces `H_WRTO`. -/
theorem theorem_2_wrto (hW : WDAP I) (hWP : IsolatedWritesCommit I) (hWF : WaitFreeReadOnly I)
    (hIRO : InvisibleReads I) (hL : LegalReads I v₀) (hWR : EnsuresWRTO I v₀) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y) (v₁ : V) (hx : v₁ ≠ v₀ x) (hy : v₁ ≠ v₀ y) :
    ∃ βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂ r₁ r₂ s₁ s₂ u,
      I.Valid (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
      ¬ PreservesRTO v₀ (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) := by
  obtain ⟨βa₁, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, D, ha₁, hc₁, hc₂, hb₁, hb₂, hrun⟩ :=
    run_theorem_2 v₀ hWP hWF hIRO hL hab hac hbc x y v₁
  obtain ⟨u, βa₂, βa₃, -, -, hE, hnot⟩ :=
    hWRTO_of_run v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hWR hx hy hrun
  exact ⟨βa₁, βa₂, βa₃, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, u, hE, hnot⟩

/-- **Theorem 1, explicit form.** For any value `v₁` written by `T₃` (to `y`) and `T₂` (to `x`),
one of the executions `E`, `E'` of Figure 1 produces a history that does not preserve RTO. For
`v₁` different from the initial values, all written values are unique, so read-from is
unambiguous in these histories. -/
theorem theorem_1_explicit (hW : WDAP I) (hOF : ObstructionFreeWrites I)
    (hWF : WaitFreeReadOnly I) (hL : LegalReads I v₀) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (v₁ : V) :
    ∃ βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂ r₁ r₂ s₁ s₂ u,
      (I.Valid (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
        ¬ PreservesRTO v₀ (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂)) ∨
      (I.Valid (execE' v₀ a b c x y v₁ (v₀ x) r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
        ¬ PreservesRTO v₀
          (execE' v₀ a b c x y v₁ (v₀ x) r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂)) := by
  obtain ⟨βa₁, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, D, ha₁, hc₁, hc₂, hb₁, hb₂, hrun⟩ :=
    run_theorem_1 v₀ hOF hWF hL hab hac hbc x y v₁
  obtain ⟨u, βa₂, βa₃, h⟩ := violation_of_run v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hrun
  exact ⟨βa₁, βa₂, βa₃, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, u, h⟩

/-- **Theorem 2, explicit form** (as `theorem_1_explicit`). -/
theorem theorem_2_explicit (hW : WDAP I) (hWP : IsolatedWritesCommit I)
    (hWF : WaitFreeReadOnly I) (hIRO : InvisibleReads I) (hL : LegalReads I v₀) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y) (v₁ : V) :
    ∃ βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂ r₁ r₂ s₁ s₂ u,
      (I.Valid (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
        ¬ PreservesRTO v₀ (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂)) ∨
      (I.Valid (execE' v₀ a b c x y v₁ (v₀ x) r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) ∧
        ¬ PreservesRTO v₀
          (execE' v₀ a b c x y v₁ (v₀ x) r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂)) := by
  obtain ⟨βa₁, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, D, ha₁, hc₁, hc₂, hb₁, hb₂, hrun⟩ :=
    run_theorem_2 v₀ hWP hWF hIRO hL hab hac hbc x y v₁
  obtain ⟨u, βa₂, βa₃, h⟩ := violation_of_run v₀ hab hac hbc hxy ha₁ hc₁ hc₂ hb₁ hb₂ hW hWF hL hrun
  exact ⟨βa₁, βa₂, βa₃, βc₁, βc₂, βb₁, βb₂, r₁, r₂, s₁, s₂, u, h⟩

end Theorems

end Podc.DAPInvisibleReads
