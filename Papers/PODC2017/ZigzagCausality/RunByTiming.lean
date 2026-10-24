import Papers.PODC2017.ZigzagCausality.BoundsGraph

/-!
# Runs from valid timings — Lemma 8 (run by timing) and Lemma 9 (Appendix B)

* `PClosed` — a set of nodes of `G_B(r)` closed under predecessors along edges (Definition 11).
* `ValidTiming` — `T a + w ≤ T b` for every edge `a --w--> b` of `G_B(r)` inside the set
  (Definition 10).
* `Timing` — bundles a p-closed set `V` of nodes of `r` with a valid timing `T`; `Timing.run` is
  the run `r[T]` of Lemma 8: the same initial states as `r`, each message sent at a node of `V` is
  delivered at `T` of its receiving node in `r`, the external inputs of a node `σ ∈ V` are
  delivered at `T σ`, and nothing else happens.
* `run_by_timing` — **Lemma 8**, `basic_run` — **Lemma 9**.

The key invariant (`Timing.isLatest_st`) is that the local state of `j` at time `t` in `r[T]` is
the state of the latest non-initial `j`-node `σ ∈ V` with `T σ ≤ t` (or the initial state).
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

namespace Sys

variable (γ : Sys P S M E) (r : Sched P S E) [Finite P]

/-- A set `V` of nodes of `G_B(r)` is *precedence-closed* (p-closed, Definition 11): for every
edge `(σ₁, σ₂)` of `G_B(r)`, if `σ₂ ∈ V` then `σ₁ ∈ V`. -/
def PClosed (V : Set (BNode P S M E)) : Prop :=
  ∀ a w b, γ.BEdge r a w b → b ∈ V → a ∈ V

/-- A *valid timing function* for `V` w.r.t. `G_B(r)` (Definition 10):
`T(σ₁) + w(σ₁, σ₂) ≤ T(σ₂)` for every edge `(σ₁, σ₂)` of `G_B(r)` with `σ₁, σ₂ ∈ V`. -/
def ValidTiming (V : Set (BNode P S M E)) (T : BNode P S M E → ℕ) : Prop :=
  ∀ a w b, γ.BEdge r a w b → a ∈ V → b ∈ V → (T a : ℤ) + w ≤ T b

/-- A p-closed set of nodes of `G_B(r)` (nodes that appear in `r`) with a valid timing. -/
structure Timing where
  /-- The p-closed set `V'`. -/
  V : Set (BNode P S M E)
  /-- The timing function (only its values on `V` matter). -/
  T : BNode P S M E → ℕ
  appears : ∀ σ ∈ V, γ.appears r σ
  closed : γ.PClosed r V
  valid : γ.ValidTiming r V T

variable {γ r}

/-- The predecessor of a node on the timeline of its process. -/
theorem isSucc_pred {σ : BNode P S M E} (h : γ.appears r σ) (h0 : 0 < γ.timer r σ) :
    γ.IsSucc r (σ.1, γ.st r (γ.timer r σ - 1) σ.1) σ := by
  refine ⟨γ.appears_st r _ _, h, rfl, ?_⟩
  rw [γ.hist_of_timer_pos r h h0]
  simp

namespace Timing

variable (τ : γ.Timing r)

/-- The non-initial nodes of `V`. -/
def Pos (σ : BNode P S M E) : Prop := σ ∈ τ.V ∧ 0 < γ.timer r σ

/-- `σ ∈ V` is a non-initial `j`-node with `T σ = t`. -/
def At (j : P) (t : ℕ) (σ : BNode P S M E) : Prop := τ.Pos σ ∧ σ.1 = j ∧ τ.T σ = t

/-- The run `r[T]` of Lemma 8. -/
noncomputable def run : Sched P S E where
  g := r.g
  dlv i s j := if h : ∃ σ, τ.At i s σ then
      τ.T (j, γ.st r (r.dlv i (γ.timer r h.choose) j) j) else 0
  ext t j := if h : ∃ σ, τ.At j t σ then r.ext (γ.timer r h.choose) j else ∅

variable {τ}

theorem Pos.appears {σ : BNode P S M E} (h : τ.Pos σ) : γ.appears r σ := τ.appears σ h.1

theorem Pos.hist_ne_nil {σ : BNode P S M E} (h : τ.Pos σ) : σ.2.hist ≠ [] :=
  (γ.timer_pos_iff r h.appears).1 h.2

theorem init_of_mem {σ : BNode P S M E} (h : σ ∈ τ.V) : σ.2.init = r.g σ.1 := by
  obtain ⟨t, ht⟩ := τ.appears σ h
  rw [← ht, st_init]

theorem pred_mem {σ : BNode P S M E} (h : τ.Pos σ) :
    (σ.1, γ.st r (γ.timer r σ - 1) σ.1) ∈ τ.V ∧
      (τ.T (σ.1, γ.st r (γ.timer r σ - 1) σ.1) : ℤ) + 1 ≤ τ.T σ := by
  have e := BEdge.succ (isSucc_pred h.appears h.2)
  exact ⟨τ.closed _ _ _ e h.1, τ.valid _ _ _ e (τ.closed _ _ _ e h.1) h.1⟩

theorem Pos.T_pos {σ : BNode P S M E} (h : τ.Pos σ) : 0 < τ.T σ := by
  have := (pred_mem h).2; omega

/-- `T` is strictly increasing along the timeline of a process inside `V`. -/
theorem T_lt_of_timer_lt {σ σ' : BNode P S M E} (h : σ ∈ τ.V) (h' : σ' ∈ τ.V)
    (hp : σ.1 = σ'.1) (hlt : γ.timer r σ < γ.timer r σ') : τ.T σ < τ.T σ' := by
  induction hn : γ.timer r σ' using Nat.strong_induction_on generalizing σ' with
  | _ n ih =>
    subst hn
    have hpos : τ.Pos σ' := ⟨h', by omega⟩
    obtain ⟨hπ, hTπ⟩ := pred_mem hpos
    have hπa : γ.appears r (σ'.1, γ.st r (γ.timer r σ' - 1) σ'.1) := γ.appears_st r _ _
    have hπt : γ.timer r (σ'.1, γ.st r (γ.timer r σ' - 1) σ'.1) ≤ γ.timer r σ' - 1 :=
      γ.timer_st_le r _ _
    have hσπ : γ.timer r σ ≤ γ.timer r (σ'.1, γ.st r (γ.timer r σ' - 1) σ'.1) := by
      rw [γ.timer_le_iff_prefix r (σ := σ) (σ' := (σ'.1, γ.st r (γ.timer r σ' - 1) σ'.1)) hp (τ.appears σ h) hπa]
      rw [← γ.st_timer r (τ.appears σ h), hp]
      exact γ.hist_prefix r (by omega) _
    rcases Nat.lt_or_ge (γ.timer r σ) (γ.timer r (σ'.1, γ.st r (γ.timer r σ' - 1) σ'.1))
      with hl | hl
    · have := ih _ (by omega) hπ hp hl rfl
      omega
    · have : σ = (σ'.1, γ.st r (γ.timer r σ' - 1) σ'.1) :=
        γ.eq_of_timer_eq r hp (τ.appears σ h) hπa (by omega)
      rw [this]; omega

theorem timer_lt_of_T_lt {σ σ' : BNode P S M E} (h : σ ∈ τ.V) (h' : σ' ∈ τ.V)
    (hp : σ.1 = σ'.1) (hlt : τ.T σ < τ.T σ') : γ.timer r σ < γ.timer r σ' := by
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hl | he
  · have := T_lt_of_timer_lt h' h hp.symm hl; omega
  · have := γ.eq_of_timer_eq r hp.symm (τ.appears σ' h') (τ.appears σ h) he
    subst this; omega

theorem timer_le_of_T_le {σ σ' : BNode P S M E} (h : σ ∈ τ.V) (h' : σ' ∈ τ.V)
    (hp : σ.1 = σ'.1) (hle : τ.T σ ≤ τ.T σ') : γ.timer r σ ≤ γ.timer r σ' := by
  by_contra hlt
  push Not at hlt
  have := T_lt_of_timer_lt h' h hp.symm hlt; omega

theorem T_inj {σ σ' : BNode P S M E} (h : σ ∈ τ.V) (h' : σ' ∈ τ.V) (hp : σ.1 = σ'.1)
    (hT : τ.T σ = τ.T σ') : σ = σ' :=
  γ.eq_of_timer_eq r hp (τ.appears σ h) (τ.appears σ' h')
    (le_antisymm (timer_le_of_T_le h h' hp hT.le) (timer_le_of_T_le h' h hp.symm hT.ge))

theorem At.unique {j : P} {t : ℕ} {σ σ' : BNode P S M E} (h : τ.At j t σ) (h' : τ.At j t σ') :
    σ = σ' :=
  T_inj h.1.1 h'.1.1 (h.2.1.trans h'.2.1.symm) (h.2.2.trans h'.2.2.symm)

theorem choose_eq {j : P} {t : ℕ} {σ : BNode P S M E} (h : τ.At j t σ) (he : ∃ σ, τ.At j t σ) :
    he.choose = σ := he.choose_spec.unique h

theorem prefix_of_T_le {σ σ' : BNode P S M E} (h : σ ∈ τ.V) (h' : σ' ∈ τ.V) (hp : σ.1 = σ'.1)
    (hle : τ.T σ ≤ τ.T σ') : σ.2.hist <+: σ'.2.hist :=
  (γ.timer_le_iff_prefix r hp (τ.appears σ h) (τ.appears σ' h')).1 (timer_le_of_T_le h h' hp hle)

/-- Receivers of messages sent at nodes of `V` are in `V` (the `−U` edge). -/
theorem recv_mem_right {σ ρ : BNode P S M E} {j : P} (h : γ.recv r σ j = some ρ) (hσ : σ ∈ τ.V) :
    ρ ∈ τ.V :=
  τ.closed _ _ _ (BEdge.bwd h) hσ

/-- Senders of messages received at nodes of `V` are in `V` (the `L` edge). -/
theorem recv_mem_left {σ ρ : BNode P S M E} {j : P} (h : γ.recv r σ j = some ρ) (hρ : ρ ∈ τ.V) :
    σ ∈ τ.V :=
  τ.closed _ _ _ (BEdge.fwd h) hρ

theorem recv_T {σ ρ : BNode P S M E} {j : P} (h : γ.recv r σ j = some ρ)
    (hσ : σ ∈ τ.V) (hρ : ρ ∈ τ.V) :
    τ.T σ + γ.net.L σ.1 j ≤ τ.T ρ ∧ τ.T ρ ≤ τ.T σ + γ.net.U σ.1 j := by
  have h1 := τ.valid _ _ _ (BEdge.fwd h) hσ hρ
  have h2 := τ.valid _ _ _ (BEdge.bwd h) hρ hσ
  omega

theorem recv_pos (hr : γ.Valid r) {σ ρ : BNode P S M E} {j : P} (h : γ.recv r σ j = some ρ)
    (hσ : σ ∈ τ.V) : τ.Pos σ ∧ τ.Pos ρ := by
  have hs := recv_spec hr h
  have := γ.net.one_le_L _ _ hs.2.2.1
  exact ⟨⟨hσ, (recv_appears_left h).2⟩, ⟨recv_mem_right h hσ, by omega⟩⟩

/-- A non-initial node of `V` sends exactly what it sends in `r`. -/
theorem sends_iff {σ : BNode P S M E} (h : τ.Pos σ) (j : P) :
    γ.Sends r σ.1 (γ.timer r σ) j ↔ γ.net.Chan σ.1 j ∧ (γ.send σ.1 σ.2 j).isSome := by
  simp only [Sends, γ.st_timer r h.appears, γ.active_timer r h.appears h.2, true_and]

theorem dlv_run {σ ρ : BNode P S M E} {j : P} (h : τ.Pos σ) (hr' : γ.recv r σ j = some ρ) :
    τ.run.dlv σ.1 (τ.T σ) j = τ.T ρ := by
  have hA : τ.At σ.1 (τ.T σ) σ := ⟨h, rfl, rfl⟩
  have he : ∃ σ', τ.At σ.1 (τ.T σ) σ' := ⟨σ, hA⟩
  simp only [run, he, ↓reduceDIte, choose_eq hA he]
  rw [((γ.recv_eq_some r).1 hr').2]

theorem ext_run_of {σ : BNode P S M E} {j : P} {t : ℕ} (h : τ.At j t σ) :
    τ.run.ext t j = r.ext (γ.timer r σ) j := by
  have he : ∃ σ', τ.At j t σ' := ⟨σ, h⟩
  simp only [run, he, ↓reduceDIte, choose_eq h he]

theorem ext_run_of_not {j : P} {t : ℕ} (h : ¬ ∃ σ, τ.At j t σ) : τ.run.ext t j = ∅ := by
  simp only [run, h, ↓reduceDIte]

/-! ### The invariant -/

/-- `ℓ` is the state of the latest non-initial `j`-node `σ ∈ V` with `T σ ≤ t`, or the initial
state of `j` if there is none. -/
def IsLatest (j : P) (t : ℕ) (ℓ : LState P S M E) : Prop :=
  (∀ σ, τ.Pos σ → σ.1 = j → τ.T σ ≤ t → σ.2.hist <+: ℓ.hist) ∧
    (ℓ = ⟨r.g j, []⟩ ∨ (τ.Pos (j, ℓ) ∧ τ.T (j, ℓ) ≤ t))

theorem IsLatest.unique {j : P} {t t' : ℕ} {ℓ ℓ' : LState P S M E} (h : τ.IsLatest j t ℓ)
    (h' : τ.IsLatest j t' ℓ') (h1 : ∀ σ, τ.Pos σ → σ.1 = j → τ.T σ ≤ t → τ.T σ ≤ t')
    (h2 : ∀ σ, τ.Pos σ → σ.1 = j → τ.T σ ≤ t' → τ.T σ ≤ t) : ℓ = ℓ' := by
  rcases h.2 with rfl | ⟨hp, hT⟩ <;> rcases h'.2 with rfl | ⟨hp', hT'⟩
  · rfl
  · exact absurd (List.eq_nil_of_prefix_nil (h.1 _ hp' rfl (h2 _ hp' rfl hT'))) hp'.hist_ne_nil
  · exact absurd (List.eq_nil_of_prefix_nil (h'.1 _ hp rfl (h1 _ hp rfl hT))) hp.hist_ne_nil
  · have a := h.1 _ hp' rfl (h2 _ hp' rfl hT')
    have b := h'.1 _ hp rfl (h1 _ hp rfl hT)
    refine LState.ext' ?_ (a.eq_of_length (le_antisymm a.length_le b.length_le)).symm
    rw [init_of_mem hp.1, init_of_mem hp'.1]

theorem IsLatest.eq {j : P} {t : ℕ} {ℓ : LState P S M E} {σ : BNode P S M E}
    (h : τ.IsLatest j t ℓ) (hσ : τ.At j t σ) : ℓ = σ.2 := by
  obtain ⟨hp, rfl, rfl⟩ := hσ
  have a := h.1 σ hp rfl le_rfl
  rcases h.2 with rfl | ⟨hq, hT⟩
  · exact absurd (List.eq_nil_of_prefix_nil a) hp.hist_ne_nil
  · have b := prefix_of_T_le hq.1 hp.1 rfl hT
    exact LState.ext' (by rw [init_of_mem hq.1, init_of_mem hp.1])
      (b.eq_of_length (le_antisymm b.length_le a.length_le))

theorem IsLatest.ne {j : P} {t : ℕ} {ℓ : LState P S M E} {σ : BNode P S M E}
    (h : τ.IsLatest j t ℓ) (hp : τ.Pos σ) (hj : σ.1 = j) (ht : t < τ.T σ) : ℓ ≠ σ.2 := by
  rintro rfl
  rcases h.2 with he | ⟨_, hT⟩
  · exact hp.hist_ne_nil (by rw [he])
  · have : ((j, σ.2) : BNode P S M E) = σ := by rw [← hj]
    rw [this] at hT; omega

section Step

variable (hr : γ.Valid r) {t : ℕ} (H : ∀ s ≤ t, ∀ i, τ.IsLatest i s (γ.st τ.run s i))
include hr H

theorem active_run_iff {s : ℕ} (hs : s ≤ t) (i : P) :
    γ.Active τ.run i s ↔ ∃ σ, τ.At i s σ := by
  rcases s with _ | s
  · simp only [Active, ActiveH, lt_irrefl, false_and, false_iff]
    rintro ⟨σ, hp, -, hT⟩
    have := hp.T_pos; omega
  · by_cases hex : ∃ σ, τ.At i (s + 1) σ
    · obtain ⟨σ, hσ⟩ := hex
      refine iff_of_true ⟨by omega, ?_⟩ ⟨σ, hσ⟩
      rw [(H _ hs i).eq hσ, Nat.add_sub_cancel]
      exact ((H s (by omega) i).ne hσ.1 hσ.2.1 (by rw [hσ.2.2]; omega)).symm
    · refine iff_of_false ?_ hex
      rintro ⟨-, hne⟩
      refine hne ((H _ hs i).unique (H s (by omega) i) ?_ ?_)
      · intro σ hp hj hT
        rcases Nat.lt_or_ge (τ.T σ) (s + 1) with h | h
        · omega
        · exact absurd ⟨σ, hp, hj, by omega⟩ hex
      · intro σ _ _ hT; omega

theorem st_run_of_at {s : ℕ} (hs : s ≤ t) {i : P} {σ : BNode P S M E} (h : τ.At i s σ) :
    γ.st τ.run s i = σ.2 :=
  (H s hs i).eq h

/-- Every message delivered in `r[T]` up to time `t + 1` comes from a message of `r` between
non-initial nodes of `V`, delivered at `T` of its receiver. -/
theorem msg_source {j i : P} {m : M} (hm : (i, m) ∈ (γ.batch τ.run t j).msgs) :
    ∃ σ ρ, τ.Pos σ ∧ σ.1 = i ∧ γ.recv r σ j = some ρ ∧ τ.At j (t + 1) ρ ∧
      γ.send i σ.2 j = some m ∧ τ.T σ < t + 1 := by
  rw [mem_batch_msgs] at hm
  obtain ⟨s, hs, ha, hc, hd, hsend⟩ := hm
  obtain ⟨σ, hσ⟩ := (active_run_iff hr H (by omega) i).1 ha
  rw [st_run_of_at hr H (by omega) hσ] at hsend
  obtain ⟨hp, rfl, rfl⟩ := hσ
  have hS : γ.Sends r σ.1 (γ.timer r σ) j := (sends_iff hp j).2 ⟨hc, by rw [hsend]; rfl⟩
  obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.1 ((γ.recv_isSome_iff r).2 hS)
  rw [dlv_run hp hρ] at hd
  have hj : ρ.1 = j := (recv_spec hr hρ).1
  exact ⟨σ, ρ, hp, rfl, hρ, ⟨(recv_pos hr hρ hp.1).2, hj, hd⟩, hsend, hs⟩

theorem batch_run_of_not {j : P} (hn : ¬ ∃ σ, τ.At j (t + 1) σ) :
    γ.batch τ.run t j = ⟨∅, ∅⟩ := by
  refine Batch.ext' ?_ (by rw [batch_ext, ext_run_of_not hn])
  ext ⟨i, m⟩
  simp only [Finset.notMem_empty, iff_false]
  intro hm
  obtain ⟨_, ρ, -, -, -, hρ, -⟩ := msg_source hr H hm
  exact hn ⟨ρ, hρ⟩

theorem batch_run_of_at {j : P} {σ : BNode P S M E} (hσ : τ.At j (t + 1) σ) :
    γ.batch τ.run t j = γ.batch r (γ.timer r σ - 1) j := by
  have hpos := hσ.1.2
  refine Batch.ext' ?_ ?_
  · ext ⟨i, m⟩
    constructor
    · intro hm
      obtain ⟨σi, ρ, hpi, rfl, hρ, hAt, hsend, -⟩ := msg_source hr H hm
      obtain rfl := hAt.unique hσ
      have hs := recv_spec hr hρ
      have := γ.net.one_le_L _ _ hs.2.2.1
      rw [mem_batch_msgs]
      refine ⟨γ.timer r σi, by omega, γ.active_timer r hpi.appears hpi.2, hs.2.2.1, by omega, ?_⟩
      rw [γ.st_timer r hpi.appears]; exact hsend
    · intro hm
      rw [mem_batch_msgs] at hm
      obtain ⟨s', hs', ha, hc, hd, hsend⟩ := hm
      set σi : BNode P S M E := (i, γ.st r s' i) with hσi
      have hti : γ.timer r σi = s' := γ.timer_eq_of_active r ha
      have hrecv : γ.recv r σi j = some σ := by
        rw [recv_eq_some]
        refine ⟨⟨by rw [hti]; exact ha, hc, by rw [hti, hsend]; rfl⟩, ?_⟩
        obtain ⟨hp, rfl, -⟩ := hσ
        rw [hti, hd, Nat.sub_add_cancel hpos, γ.st_timer r hp.appears]
      have hσiV : σi ∈ τ.V := recv_mem_left hrecv hσ.1.1
      have hpi : τ.Pos σi := ⟨hσiV, by rw [hti]; exact ha.1⟩
      have hT := recv_T hrecv hσiV hσ.1.1
      have := γ.net.one_le_L σi.1 j hc
      rw [hσ.2.2] at hT
      rw [mem_batch_msgs]
      refine ⟨τ.T σi, by omega, (active_run_iff hr H (by omega) i).2 ⟨σi, hpi, rfl, rfl⟩, hc,
        by rw [dlv_run hpi hrecv, hσ.2.2], ?_⟩
      rw [st_run_of_at hr H (by omega) ⟨hpi, rfl, rfl⟩]
      exact hsend
  · rw [batch_ext, batch_ext, ext_run_of hσ, Nat.sub_add_cancel hpos]

theorem isLatest_succ (j : P) : τ.IsLatest j (t + 1) (γ.st τ.run (t + 1) j) := by
  by_cases hex : ∃ σ, τ.At j (t + 1) σ
  · obtain ⟨σ, hσ⟩ := hex
    obtain ⟨hp, rfl, hT⟩ := id hσ
    obtain ⟨hπV, hTπ⟩ := pred_mem hp
    -- the state at time `t` is the predecessor of `σ`
    have hlat : τ.IsLatest σ.1 t (γ.st r (γ.timer r σ - 1) σ.1) := by
      refine ⟨fun ρ hρ hj hTρ => ?_, ?_⟩
      · have := timer_lt_of_T_lt hρ.1 hp.1 hj (by omega)
        rw [← γ.st_timer r hρ.appears, hj]
        exact γ.hist_prefix r (by omega) _
      · by_cases h0 : 0 < γ.timer r (σ.1, γ.st r (γ.timer r σ - 1) σ.1)
        · exact Or.inr ⟨⟨hπV, h0⟩, by omega⟩
        · left
          have := γ.st_timer r (γ.appears_st r (γ.timer r σ - 1) σ.1)
          rw [show γ.timer r (σ.1, γ.st r (γ.timer r σ - 1) σ.1) = 0 by omega] at this
          dsimp only at this
          rw [← this, st_zero]
    have hprev : γ.st τ.run t σ.1 = γ.st r (γ.timer r σ - 1) σ.1 :=
      (H t le_rfl σ.1).unique hlat (fun _ _ _ h => h) (fun _ _ _ h => h)
    have hnew : γ.st τ.run (t + 1) σ.1 = σ.2 := by
      rw [st_succ, hprev, batch_run_of_at hr H hσ, ← st_succ, Nat.sub_add_cancel hp.2,
        γ.st_timer r hp.appears]
    rw [hnew]
    refine ⟨fun ρ hρ hj hTρ => prefix_of_T_le hρ.1 hp.1 hj (by omega),
      Or.inr ⟨hp, show τ.T σ ≤ t + 1 by omega⟩⟩
  · have hst : γ.st τ.run (t + 1) j = γ.st τ.run t j := by
      rw [st_succ, batch_run_of_not hr H hex, step_eq]; simp
    rw [hst]
    obtain ⟨h1, h2⟩ := H t le_rfl j
    refine ⟨fun σ hp hj hT => h1 σ hp hj ?_, h2.imp_right fun h => ⟨h.1, by omega⟩⟩
    rcases Nat.lt_or_ge (τ.T σ) (t + 1) with h | h
    · omega
    · exact absurd ⟨σ, hp, hj, by omega⟩ hex

end Step

theorem isLatest_zero (j : P) : τ.IsLatest j 0 (γ.st τ.run 0 j) :=
  ⟨fun σ hp _ hT => absurd hp.T_pos (by omega), Or.inl rfl⟩

/-- The key invariant of the run `r[T]`. -/
theorem isLatest_st (hr : γ.Valid r) (t : ℕ) (j : P) : τ.IsLatest j t (γ.st τ.run t j) := by
  induction t using Nat.strong_induction_on generalizing j with
  | _ t ih =>
    rcases t with _ | t
    · exact isLatest_zero j
    · exact isLatest_succ hr (fun s hs i => ih s (by omega) i) j

/-! ### Properties of `r[T]` -/

variable (hr : γ.Valid r)
include hr

theorem active_run (i : P) (s : ℕ) : γ.Active τ.run i s ↔ ∃ σ, τ.At i s σ :=
  active_run_iff hr (fun s' _ i' => isLatest_st hr s' i') le_rfl i

theorem st_run {σ : BNode P S M E} (h : τ.Pos σ) : γ.st τ.run (τ.T σ) σ.1 = σ.2 :=
  (isLatest_st hr _ _).eq ⟨h, rfl, rfl⟩

theorem timer_run {σ : BNode P S M E} (h : τ.Pos σ) : γ.timer τ.run σ = τ.T σ := by
  have := γ.timer_eq_of_active τ.run ((active_run hr σ.1 (τ.T σ)).2 ⟨σ, h, rfl, rfl⟩)
  rwa [st_run hr h] at this

/-- The nodes of `r[T]` are exactly the nodes of `V` and the initial nodes of `r`. -/
theorem appears_run_iff (σ : BNode P S M E) :
    γ.appears τ.run σ ↔ σ ∈ τ.V ∨ (γ.appears r σ ∧ γ.timer r σ = 0) := by
  constructor
  · rintro ⟨t, ht⟩
    rcases (isLatest_st hr t σ.1).2 with h | ⟨hp, -⟩
    · right
      rw [ht] at h
      have ha : γ.appears r σ := ⟨0, by rw [st_zero, h]⟩
      exact ⟨ha, Nat.le_zero.1 (γ.timer_le r (by rw [st_zero, h]))⟩
    · left; rw [ht] at hp; exact hp.1
  · have hinit : ∀ σ : BNode P S M E, γ.appears r σ → γ.timer r σ = 0 → γ.appears τ.run σ := by
      intro σ ha h0
      refine ⟨0, ?_⟩
      have := γ.st_timer r ha
      rw [h0, st_zero] at this
      rw [st_zero, ← this]; rfl
    rintro (h | ⟨ha, h0⟩)
    · by_cases h0 : 0 < γ.timer r σ
      · exact ⟨_, st_run hr ⟨h, h0⟩⟩
      · exact hinit σ (τ.appears σ h) (by omega)
    · exact hinit σ ha h0

/-- The message relation of `r[T]` is that of `r` restricted to `V`. -/
theorem recv_run_iff {σ ρ : BNode P S M E} {j : P} :
    γ.recv τ.run σ j = some ρ ↔ γ.recv r σ j = some ρ ∧ ρ ∈ τ.V := by
  constructor
  · intro h
    obtain ⟨hS, rfl⟩ := (γ.recv_eq_some τ.run).1 h
    obtain ⟨hap, -⟩ := γ.sends_timer τ.run hS
    obtain ⟨σ', hp', hj', hT'⟩ := (active_run hr _ _).1 hS.1
    have hσσ' : σ = σ' := by
      have e1 := γ.st_timer τ.run hap
      rw [← hT', ← hj', st_run hr hp'] at e1
      exact Prod.ext hj'.symm e1.symm
    subst hσσ'
    have hS' : γ.Sends r σ.1 (γ.timer r σ) j := by
      rw [sends_iff hp']
      refine ⟨hS.2.1, ?_⟩
      have := hS.2.2
      rwa [← hT', st_run hr hp'] at this
    obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.1 ((γ.recv_isSome_iff r).2 hS')
    have hρV := recv_mem_right hρ hp'.1
    have hρp := (recv_pos hr hρ hp'.1).2
    have hj : ρ.1 = j := (recv_spec hr hρ).1
    have hρe : ((j, γ.st τ.run (τ.T ρ) j) : BNode P S M E) = ρ := by
      rw [← hj, st_run hr hρp]
    rw [← hT', dlv_run hp' hρ, hρe]
    exact ⟨hρ, hρV⟩
  · rintro ⟨h, hρ⟩
    have hσV := recv_mem_left h hρ
    obtain ⟨hp, hρp⟩ := recv_pos hr h hσV
    have hS : γ.Sends r σ.1 (γ.timer r σ) j := ((γ.recv_eq_some r).1 h).1
    rw [recv_eq_some, timer_run hr hp]
    have hj : ρ.1 = j := (recv_spec hr h).1
    refine ⟨⟨(active_run hr _ _).2 ⟨σ, hp, rfl, rfl⟩, hS.2.1, ?_⟩, ?_⟩
    · rw [st_run hr hp]; exact ((sends_iff hp j).1 hS).2
    · rw [dlv_run hp h, ← hj, st_run hr hρp]

theorem valid_run : γ.Valid τ.run where
  init := hr.init
  bounds := by
    intro i s j hS
    obtain ⟨σ, hp, rfl, rfl⟩ := (active_run hr _ _).1 hS.1
    have hS' : γ.Sends r σ.1 (γ.timer r σ) j := by
      rw [sends_iff hp]
      refine ⟨hS.2.1, ?_⟩
      have := hS.2.2
      rwa [st_run hr hp] at this
    obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.1 ((γ.recv_isSome_iff r).2 hS')
    rw [dlv_run hp hρ]
    exact recv_T hρ hp.1 (recv_mem_right hρ hp.1)
  ext_unique := by
    intro e t j t' j' he he'
    by_cases h : ∃ σ, τ.At j t σ
    · by_cases h' : ∃ σ, τ.At j' t' σ
      · obtain ⟨σ, hσ⟩ := h
        obtain ⟨σ', hσ'⟩ := h'
        rw [ext_run_of hσ] at he
        rw [ext_run_of hσ'] at he'
        obtain ⟨htt, rfl⟩ := hr.ext_unique _ _ _ _ _ he he'
        have := γ.eq_of_timer_eq r (hσ.2.1.trans hσ'.2.1.symm) hσ.1.appears hσ'.1.appears htt
        subst this
        exact ⟨hσ.2.2.symm.trans hσ'.2.2, rfl⟩
      · rw [ext_run_of_not h'] at he'; simp at he'
    · rw [ext_run_of_not h] at he; simp at he

theorem appears_of_run {σ : BNode P S M E} (h : γ.appears τ.run σ) : γ.appears r σ := by
  rcases (appears_run_iff hr σ).1 h with h | h
  · exact τ.appears σ h
  · exact h.1

theorem isSucc_run_iff {a b : BNode P S M E} :
    γ.IsSucc τ.run a b ↔ γ.IsSucc r a b ∧ b ∈ τ.V := by
  constructor
  · rintro ⟨ha, hb, hp, hl⟩
    refine ⟨⟨appears_of_run hr ha, appears_of_run hr hb, hp, hl⟩, ?_⟩
    rcases (appears_run_iff hr b).1 hb with h | ⟨hb', h0⟩
    · exact h
    · have : b.2.hist = [] := by
        by_contra hne
        have := (γ.timer_pos_iff r hb').2 hne
        omega
      rw [this] at hl; simp at hl
  · rintro ⟨⟨ha, hb, hp, hl⟩, hbV⟩
    have haV : a ∈ τ.V := τ.closed _ _ _ (BEdge.succ ⟨ha, hb, hp, hl⟩) hbV
    exact ⟨(appears_run_iff hr a).2 (Or.inl haV), (appears_run_iff hr b).2 (Or.inl hbV), hp, hl⟩

/-- The bounds graph of `r[T]` is the subgraph of `G_B(r)` induced by `V` (plus the isolated
initial nodes of `r`): an edge of `G_B(r)` ends in `V` iff it is an edge of `G_B(r[T])` (by
p-closedness, both its endpoints are then in `V`). -/
theorem bedge_run_iff {a b : BNode P S M E} {w : ℤ} :
    γ.BEdge τ.run a w b ↔ γ.BEdge r a w b ∧ b ∈ τ.V := by
  constructor
  · intro h
    cases h with
    | succ h =>
      obtain ⟨h, hb⟩ := (isSucc_run_iff hr).1 h
      exact ⟨BEdge.succ h, hb⟩
    | fwd h =>
      obtain ⟨h, hb⟩ := (recv_run_iff hr).1 h
      exact ⟨BEdge.fwd h, hb⟩
    | bwd h =>
      obtain ⟨h, ha⟩ := (recv_run_iff hr).1 h
      exact ⟨BEdge.bwd h, recv_mem_left h ha⟩
  · rintro ⟨h, hb⟩
    cases h with
    | succ h => exact BEdge.succ ((isSucc_run_iff hr).2 ⟨h, hb⟩)
    | fwd h => exact BEdge.fwd ((recv_run_iff hr).2 ⟨h, hb⟩)
    | bwd h => exact BEdge.bwd ((recv_run_iff hr).2 ⟨h, recv_mem_right h hb⟩)

/-! ### Lemma 9 -/

/-- Message chains of `r[T]` are message chains of `r`. -/
theorem gbasic_of_run {σ ρ : BNode P S M E} {q : List P} (h : γ.gbasic τ.run σ q = some ρ) :
    γ.gbasic r σ q = some ρ := by
  induction q generalizing σ with
  | nil =>
    simp only [gbasic_nil] at h ⊢
    split_ifs at h with ha
    cases h; simp [appears_of_run hr ha]
  | cons j q ih =>
    simp only [gbasic_cons] at h ⊢
    obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rw [((recv_run_iff hr).1 h1).1]
    exact ih h2

/-- The origin of a message chain of `r` ending in `V` is in `V`. -/
theorem mem_of_gbasic {σ ρ : BNode P S M E} {q : List P} (h : γ.gbasic r σ q = some ρ)
    (hρ : ρ ∈ τ.V) : σ ∈ τ.V := by
  induction q generalizing σ with
  | nil =>
    simp only [gbasic_nil] at h
    split_ifs at h; cases h; exact hρ
  | cons j q ih =>
    simp only [gbasic_cons] at h
    obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact recv_mem_left h1 (ih h2)

/-- Message chains of `r` ending at a node of `r[T]` are message chains of `r[T]`. -/
theorem gbasic_run {σ ρ : BNode P S M E} {q : List P} (h : γ.gbasic r σ q = some ρ)
    (hρ : γ.appears τ.run ρ) : γ.gbasic τ.run σ q = some ρ := by
  cases q with
  | nil =>
    simp only [gbasic_nil] at h ⊢
    split_ifs at h; cases h; simp [hρ]
  | cons j q =>
    -- `ρ` received a message, so it is not an initial node; hence `ρ ∈ V`
    have hρV : ρ ∈ τ.V := by
      simp only [gbasic_cons] at h
      obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
      have := recv_spec hr h1
      have := HB.timer_le hr (HB.of_gbasic h2)
      have := γ.net.one_le_L _ _ (recv_spec hr h1).2.2.1
      rcases (appears_run_iff hr ρ).1 hρ with h' | h'
      · exact h'
      · omega
    clear hρ
    induction q generalizing σ j with
    | nil =>
      simp only [gbasic_cons, gbasic_nil] at h ⊢
      obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
      split_ifs at h2 with ha
      cases h2
      rw [(recv_run_iff hr).2 ⟨h1, hρV⟩]
      simp [(appears_run_iff hr _).2 (Or.inl hρV)]
    | cons k q ih =>
      rw [gbasic_cons] at h ⊢
      obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
      have hσ' : σ' ∈ τ.V := mem_of_gbasic hr h2 hρV
      rw [(recv_run_iff hr).2 ⟨h1, hσ'⟩]
      exact ih k h2

/-- **Lemma 9.** Let `σ = basic(θ, r)`. If `σ` appears in `r[T]` then `basic(θ, r[T]) = σ`, and
if `θ` appears in `r[T]` then so does `σ`: either both `θ` and `σ` appear in `r[T]` and
`σ = basic(θ, r[T])`, or neither does. -/
theorem basic_run {θ : GNode P S M E} {σ : BNode P S M E} (h : γ.basic r θ = some σ) :
    (γ.appears τ.run σ → γ.basic τ.run θ = some σ) ∧ (γ.appearsG τ.run θ → γ.appears τ.run σ) := by
  refine ⟨gbasic_run hr h, fun hθ => ?_⟩
  obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.1 hθ
  have := gbasic_of_run hr hρ
  have e : ρ = σ := Option.some_injective _ (this.symm.trans h)
  subst e
  exact (gbasic_appears γ τ.run hρ).2

end Timing

/-- **Lemma 8 (Run by timing).** Let `V' ⊆ V` be a p-closed set of nodes of `G_B(r)` and `T` a
valid timing function for `V'`. Then there is a run `r[T] ∈ R` with the same initial states
whose nodes are exactly `V' ∪ V^{r,0}` (`V^{r,0}`: the initial nodes of `r`), whose message
relation is that of `r` restricted to messages received in `V'` (hence `G_B(r[T])` is the
subgraph of `G_B(r)` induced by `V' ∪ V^{r,0}`), and in which every non-initial node `σ ∈ V'`
appears at time `T σ`. -/
theorem run_by_timing (hr : γ.Valid r) {V : Set (BNode P S M E)} {T : BNode P S M E → ℕ}
    (hV : ∀ σ ∈ V, γ.appears r σ) (hc : γ.PClosed r V) (hT : γ.ValidTiming r V T) :
    ∃ r' : Sched P S E, γ.Valid r' ∧ r'.g = r.g ∧
      (∀ σ, γ.appears r' σ ↔ σ ∈ V ∨ (γ.appears r σ ∧ γ.timer r σ = 0)) ∧
      (∀ σ j ρ, γ.recv r' σ j = some ρ ↔ γ.recv r σ j = some ρ ∧ ρ ∈ V) ∧
      (∀ a w b, γ.BEdge r' a w b ↔ γ.BEdge r a w b ∧ b ∈ V) ∧
      (∀ σ ∈ V, 0 < γ.timer r σ → γ.timer r' σ = T σ) := by
  let τ : γ.Timing r := ⟨V, T, hV, hc, hT⟩
  exact ⟨τ.run, Timing.valid_run hr, rfl, Timing.appears_run_iff hr,
    fun _ _ _ => Timing.recv_run_iff hr, fun _ _ _ => Timing.bedge_run_iff hr, fun σ h h0 => Timing.timer_run (τ := τ) hr ⟨h, h0⟩⟩

end Sys

end Podc.ZigzagCausality
