import Papers.PODC2011.CCvsDSMSeparation.Trace

/-!
# Stability and regular histories (Definitions 6.3–6.6, 6.8)

The paper's regularity (Definition 6.6), relative to the set `B` of *active* processes (the
participants outside `B` are the *finished* ones, which are idle and never move again):

1. (`NoSee`) no process reads a value last written by another active process;
2. (`NoTouch`) no process accesses a variable in the module of another active process;
3. (`SoleW`) for every variable `v`: if the last write to `v` is by an active process `q`, then
   after erasing `q` the last write to `v` is not by an active process.

Condition 3 is **weaker** than the paper's ("if `v` is written by more than one process and the
last write is by `p`, then `p` is finished"). The paper's condition is not preserved by its own
construction (an unstable process kept in the erasing case may write a variable previously written
by a finished process), while the weaker one is, and it is all the proof needs: erasing any set of
active processes reverts every variable to a value written by a finished process (or to its
initial value).
-/

namespace Podc.CCvsDSMSeparation

variable {N : ℕ} {V Val S : Type*}

/-- The (optional) process `w` is not an active process other than `p`. -/
def OkW (B : Finset (Fin N)) (p : Fin N) (w : Option (Fin N)) : Prop :=
  ∀ q, w = some q → q ∈ B → q = p

lemma OkW.mono {B B' : Finset (Fin N)} {p : Fin N} {w : Option (Fin N)} (h : OkW B p w)
    (hB : B' ⊆ B) : OkW B' p w := fun q hq hqB => h q hq (hB hqB)

@[simp] lemma okW_none (B : Finset (Fin N)) (p : Fin N) : OkW B p none := by
  intro q hq; cases hq

@[simp] lemma okW_self (B : Finset (Fin N)) (p : Fin N) : OkW B p (some p) := by
  intro q hq _; cases hq; rfl

lemma okW_of_not_mem {B : Finset (Fin N)} {p q : Fin N} (h : q ∉ B) : OkW B p (some q) := by
  intro r hr hrB; cases hr; exact absurd hrB h

/-- Definition 6.6(1): nobody sees another active process. -/
def NoSee (B : Finset (Fin N)) (τ : List (Ev N V Val)) : Prop :=
  Steps (fun ρ e => ∀ v x, e.op = .read v x → OkW B e.p (writer v ρ)) τ

/-- Definition 6.6(3), weakened (see the module docstring). -/
def SoleW (B : Finset (Fin N)) (τ : List (Ev N V Val)) (v : V) : Prop :=
  ∀ q, writer v τ = some q → q ∈ B → ∀ q', writer v (erase {q} τ) = some q' → q' ∉ B

namespace Algorithm

variable (A : Algorithm N V Val S)

/-- Definition 6.6(2): nobody touches another active process. -/
def NoTouch (B : Finset (Fin N)) (τ : List (Ev N V Val)) : Prop :=
  ∀ e ∈ τ, ∀ v, e.op.var = some v → OkW B e.p (some (A.home v))

/-- Definition 6.6 (regular history), relative to the set `B` of active processes. -/
structure Regular (B : Finset (Fin N)) (τ : List (Ev N V Val)) : Prop where
  noSee : NoSee B τ
  noTouch : A.NoTouch B τ
  sole : ∀ v, SoleW B τ v

/-- The participants outside `B` (the finished processes) are idle. -/
def Settled (B : Finset (Fin N)) (τ : List (Ev N V Val)) : Prop :=
  ∀ q ∈ par τ, q ∉ B → A.Idle τ q

end Algorithm

/-! ### Erasing active processes -/

lemma NoSee.noSeeOf {B E : Finset (Fin N)} {τ : List (Ev N V Val)} (h : NoSee B τ)
    (hE : E ⊆ B) : NoSeeOf E τ := by
  refine Steps.mono h ?_
  intro ρ e _ he hpE v x hx q hq hqE
  have := he v x hx q hq (hE hqE)
  subst this; exact hpE hqE

lemma NoSee.mono {B B' : Finset (Fin N)} {τ : List (Ev N V Val)} (h : NoSee B τ)
    (hB : B' ⊆ B) : NoSee B' τ :=
  Steps.mono h fun _ _ _ he v x hx => (he v x hx).mono hB

lemma SoleW.mono {B B' : Finset (Fin N)} {τ : List (Ev N V Val)} {v : V} (h : SoleW B τ v)
    (hB : B' ⊆ B) : SoleW B' τ v :=
  fun q hq hqB q' hq' hq'B => h q hq (hB hqB) q' hq' (hB hq'B)

lemma SoleW.of_writer_not_mem {B : Finset (Fin N)} {τ : List (Ev N V Val)} {v : V}
    (h : ∀ q, writer v τ = some q → q ∉ B) : SoleW B τ v :=
  fun q hq hqB => absurd hqB (h q hq)

/-- After erasing a set `E` of active processes containing the last writer of `v`, the last
writer of `v` is not active. -/
lemma SoleW.erase_writer_not_mem {B E : Finset (Fin N)} {τ : List (Ev N V Val)} {v : V}
    (h : SoleW B τ v) (hE : E ⊆ B) {q : Fin N} (hq : writer v τ = some q) (hqE : q ∈ E) :
    ∀ q', writer v (erase E τ) = some q' → q' ∉ B := by
  have he : erase E τ = erase (E \ {q}) (erase {q} τ) := by
    rw [erase_erase]; congr 1; ext r; by_cases hr : r = q <;> simp [hr, hqE]
  rw [he]
  have hw := h q hq (hE hqE)
  rw [writer_erase]
  · exact hw
  · intro r hr hrE; exact hw r hr (hE (Finset.sdiff_subset hrE))

lemma SoleW.writer_of_erase {B E : Finset (Fin N)} {τ : List (Ev N V Val)} {v : V}
    (h : SoleW B τ v) (hE : E ⊆ B) {q : Fin N} (hq : writer v (erase E τ) = some q)
    (hqB : q ∈ B) : writer v τ = some q := by
  rcases hw : writer v τ with _ | r
  · rw [writer_erase (by simp [hw]), hw] at hq; cases hq
  · by_cases hr : r ∈ E
    · exact absurd hqB (h.erase_writer_not_mem hE hw hr q hq)
    · rw [writer_erase (by intro r' hr'; rw [hw] at hr'; cases hr'; exact hr), hw] at hq
      exact hq

/-- After erasing a set `E ⊆ B` of active processes, the last writer of any variable is not in
`E`, and if it is active then it was already the last writer. -/
lemma SoleW.okW_erase {B E : Finset (Fin N)} {τ : List (Ev N V Val)} {v : V}
    (h : SoleW B τ v) (hE : E ⊆ B) (q : Fin N) (hq : writer v (erase E τ) = some q) :
    q ∉ E ∧ (q ∈ B → writer v τ = some q) := by
  refine ⟨fun hqE => ?_, fun hqB => h.writer_of_erase hE hq hqB⟩
  obtain ⟨e, he, rfl, -⟩ := writer_mem hq
  exact (mem_erase.1 he).2 hqE

lemma NoSee.erase {B E : Finset (Fin N)} {τ : List (Ev N V Val)} (h : NoSee B τ) (hE : E ⊆ B) :
    NoSee (B \ E) (erase E τ) := by
  induction τ using List.reverseRecOn with
  | nil => simp [NoSee]
  | append_singleton τ e ih =>
    unfold NoSee at h; rw [steps_snoc] at h
    rw [erase_append, erase_singleton]
    split_ifs with he
    · simpa using ih h.1
    · unfold NoSee; rw [steps_snoc]
      refine ⟨ih h.1, fun v x hx => ?_⟩
      have h2 := h.2 v x hx
      rw [writer_erase]
      · exact h2.mono Finset.sdiff_subset
      · intro q hq hqE
        have := h2 q hq (hE hqE); subst this; exact he hqE

/-! ### Appending steps -/

lemma writer_append_cases (v : V) (τ σ : List (Ev N V Val)) (q : Fin N)
    (h : writer v (τ ++ σ) = some q) : writer v τ = some q ∨ ∃ e ∈ σ, e.p = q ∧ e.Writes v := by
  by_cases hw : ∃ e ∈ σ, e.Writes v
  · right
    induction σ using List.reverseRecOn with
    | nil => simp at hw
    | append_singleton σ e ih =>
      rw [← List.append_assoc, writer_snoc] at h
      split_ifs at h with he
      · cases h; exact ⟨e, by simp, rfl, he⟩
      · have hw' : ∃ e ∈ σ, e.Writes v := by
          obtain ⟨e', he', hw'⟩ := hw
          rcases List.mem_append.1 he' with he' | he'
          · exact ⟨e', he', hw'⟩
          · simp at he'; subst he'; exact absurd hw' he
        obtain ⟨e', he', h1, h2⟩ := ih h hw'
        exact ⟨e', by simp [he'], h1, h2⟩
  · left
    push Not at hw
    rwa [writer_append_of_not_writes v τ σ hw] at h

lemma NoSee.snoc {B : Finset (Fin N)} {τ : List (Ev N V Val)} {e : Ev N V Val}
    (h : NoSee B τ) (h1 : ∀ v x, e.op = .read v x → OkW B e.p (writer v τ)) :
    NoSee B (τ ++ [e]) := by
  unfold NoSee; rw [steps_snoc]; exact ⟨h, h1⟩

lemma SoleW.snoc_not_writes {B : Finset (Fin N)} {τ : List (Ev N V Val)} {e : Ev N V Val}
    {u : V} (h : SoleW B τ u) (hw : ¬ e.Writes u) : SoleW B (τ ++ [e]) u := by
  intro q hq hqB q' hq' hq'B
  rw [writer_snoc] at hq; simp only [hw, ↓reduceIte] at hq
  rw [erase_append, writer_append_of_not_writes] at hq'
  · exact h q hq hqB q' hq' hq'B
  · intro e' he'
    rw [erase_singleton] at he'
    split_ifs at he' <;> simp_all

lemma SoleW.snoc_write {B : Finset (Fin N)} {τ : List (Ev N V Val)} {e : Ev N V Val}
    {u : V} (h : SoleW B τ u) (h3 : e.p ∈ B → OkW B e.p (writer u τ)) :
    SoleW B (τ ++ [e]) u := by
  by_cases hw : e.Writes u
  · intro q hq hqB q' hq' hq'B
    rw [writer_snoc] at hq; simp only [hw, ↓reduceIte, Option.some.injEq] at hq
    subst hq
    rw [erase_append, erase_singleton] at hq'
    simp only [Finset.mem_singleton_self, ↓reduceIte, List.append_nil] at hq'
    have hok := h3 hqB
    rcases hwu : writer u τ with _ | r
    · rw [writer_erase (by simp [hwu]), hwu] at hq'; cases hq'
    · by_cases hr : r = e.p
      · subst hr; exact h _ hwu hqB q' hq' hq'B
      · have hrB : r ∉ B := fun hrB => hr (hok r hwu hrB)
        rw [writer_erase (by intro r' hr'; rw [hwu] at hr'; cases hr'; simpa using hr),
          hwu] at hq'
        cases hq'; exact hrB hq'B
  · exact h.snoc_not_writes hw

namespace Algorithm

variable (A : Algorithm N V Val S)

lemma NoTouch.mono {B B' : Finset (Fin N)} {τ : List (Ev N V Val)} (h : A.NoTouch B τ)
    (hB : B' ⊆ B) : A.NoTouch B' τ :=
  fun e he v hv => (h e he v hv).mono hB

lemma NoTouch.append {B : Finset (Fin N)} {τ σ : List (Ev N V Val)} (h : A.NoTouch B τ)
    (h' : A.NoTouch B σ) : A.NoTouch B (τ ++ σ) := by
  intro e he; rcases List.mem_append.1 he with he | he
  · exact h e he
  · exact h' e he

lemma Regular.mono {B B' : Finset (Fin N)} {τ : List (Ev N V Val)} (h : A.Regular B τ)
    (hB : B' ⊆ B) : A.Regular B' τ :=
  ⟨h.noSee.mono hB, NoTouch.mono A h.noTouch hB, fun v => (h.sole v).mono hB⟩

lemma Regular.valid_erase {B E : Finset (Fin N)} {τ : List (Ev N V Val)} (h : A.Regular B τ)
    (hv : A.Valid τ) (hE : E ⊆ B) : A.Valid (erase E τ) :=
  A.valid_erase hv (h.noSee.noSeeOf hE)

lemma Regular.erase {B E : Finset (Fin N)} {τ : List (Ev N V Val)} (h : A.Regular B τ)
    (hE : E ⊆ B) : A.Regular (B \ E) (Podc.CCvsDSMSeparation.erase E τ) := by
  refine ⟨h.noSee.erase hE, ?_, ?_⟩
  · intro e he v hv
    exact (h.noTouch e (mem_erase.1 he).1 v hv).mono Finset.sdiff_subset
  · intro v q hq hqB q' hq' hq'B
    have hq0 : writer v τ = some q :=
      (h.sole v).writer_of_erase hE hq (Finset.sdiff_subset hqB)
    have hw := h.sole v q hq0 (Finset.sdiff_subset hqB)
    rw [erase_erase, Finset.union_comm, ← erase_erase] at hq'
    rw [writer_erase] at hq'
    · exact hw q' hq' (Finset.sdiff_subset hq'B)
    · intro r hr hrE; exact hw r hr (hE hrE)

lemma Settled.erase {B E : Finset (Fin N)} {τ : List (Ev N V Val)} (h : A.Settled B τ) :
    A.Settled (B \ E) (Podc.CCvsDSMSeparation.erase E τ) := by
  intro q hq hqB
  rw [par_erase, Finset.mem_sdiff] at hq
  have hqB' : q ∉ B := fun h' => hqB (Finset.mem_sdiff.2 ⟨h', hq.2⟩)
  obtain ⟨s, hs⟩ := h q hq.1 hqB'
  exact ⟨s, by simp only [state, proj_erase_of_not_mem τ hq.2] at hs ⊢; exact hs⟩

lemma okW_writer_of_home {B : Finset (Fin N)} {τ : List (Ev N V Val)} (h : A.NoTouch B τ)
    {p : Fin N} (hp : p ∈ B) {v : V} (hv : A.home v = p) : OkW B p (writer v τ) := by
  intro q hq hqB
  obtain ⟨e, he, rfl, hw⟩ := writer_mem hq
  have := h e he v hw.var (A.home v) rfl (hv ▸ hp)
  rw [← this, hv]

/-- Appending a step that sees and touches no other active process, and does not overwrite the
last write of another active process, preserves regularity. -/
lemma Regular.snoc {B : Finset (Fin N)} {τ : List (Ev N V Val)} {e : Ev N V Val}
    (h : A.Regular B τ)
    (h1 : ∀ v x, e.op = .read v x → OkW B e.p (writer v τ))
    (h2 : ∀ v, e.op.var = some v → OkW B e.p (some (A.home v)))
    (h3 : ∀ v x, e.op = .write v x → e.p ∈ B → OkW B e.p (writer v τ)) :
    A.Regular B (τ ++ [e]) := by
  refine ⟨h.noSee.snoc h1, ?_, fun u => ?_⟩
  · refine NoTouch.append A h.noTouch ?_
    intro e' he' v hv; simp at he'; subst he'; exact h2 v hv
  · by_cases hw : e.Writes u
    · obtain ⟨x, hx⟩ := hw
      exact (h.sole u).snoc_write (h3 u x hx)
    · exact (h.sole u).snoc_not_writes hw

/-- A step accessing only the process' own module (or no memory) preserves regularity. -/
lemma Regular.snoc_local {B : Finset (Fin N)} {τ : List (Ev N V Val)} {e : Ev N V Val}
    (h : A.Regular B τ) (hp : e.p ∈ B) (hl : ∀ v, e.op.var = some v → A.home v = e.p) :
    A.Regular B (τ ++ [e]) := by
  refine Regular.snoc A h ?_ ?_ ?_
  · intro v x hx
    exact A.okW_writer_of_home h.noTouch hp (hl v (by simp [hx, Op.var]))
  · intro v hv; rw [hl v hv]; exact okW_self _ _
  · intro v x hx _
    exact A.okW_writer_of_home h.noTouch hp (hl v (by simp [hx, Op.var]))

/-- Steps of a non-active process that neither see nor touch the active processes (as of `τ`)
preserve regularity. -/
lemma Regular.append_outsider {B : Finset (Fin N)} {τ σ : List (Ev N V Val)}
    (h : A.Regular B τ) (hσ : ∀ e ∈ σ, e.p ∉ B)
    (hacc : ∀ e ∈ σ, ∀ v, e.op.var = some v → A.home v ∉ B ∧ ∀ q ∈ B, writer v τ ≠ some q) :
    A.Regular B (τ ++ σ) := by
  induction σ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton σ e ih =>
    rw [← List.append_assoc]
    have ih' := ih (fun e' he' => hσ e' (by simp [he']))
      (fun e' he' => hacc e' (by simp [he']))
    have he := hσ e (by simp)
    refine Regular.snoc A ih' ?_ ?_ (fun _ _ _ h' => absurd h' he)
    · intro v x hx q hq hqB
      rcases writer_append_cases v τ σ q hq with hq | ⟨e', he', rfl, -⟩
      · exact absurd hq ((hacc e (by simp) v (by simp [hx, Op.var])).2 q hqB)
      · exact absurd hqB (hσ e' (by simp [he']))
    · intro v hv
      exact okW_of_not_mem (hacc e (by simp) v hv).1

lemma Settled.snoc {B : Finset (Fin N)} {τ : List (Ev N V Val)} {e : Ev N V Val}
    (h : A.Settled B τ) (he : e.p ∈ B ∨ A.Idle (τ ++ [e]) e.p) : A.Settled B (τ ++ [e]) := by
  intro q hq hqB
  rw [par_append, Finset.mem_union] at hq
  by_cases hqe : e.p = q
  · subst hqe; rcases he with he | he
    · exact absurd he hqB
    · exact he
  · rcases hq with hq | hq
    · obtain ⟨s, hs⟩ := h q hq hqB
      exact ⟨s, by rw [state_snoc_ne _ _ _ hqe]; exact hs⟩
    · simp [mem_par] at hq; exact absurd hq hqe

lemma Settled.append_active {B : Finset (Fin N)} {τ σ : List (Ev N V Val)}
    (h : A.Settled B τ) (hσ : ∀ e ∈ σ, e.p ∈ B) : A.Settled B (τ ++ σ) := by
  intro q hq hqB
  rw [par_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · obtain ⟨s, hs⟩ := h q hq hqB
    refine ⟨s, ?_⟩
    rw [state_append_of_forall]
    · exact hs
    · intro e he heq; exact hqB (heq ▸ hσ e he)
  · obtain ⟨e, he, rfl⟩ := mem_par.1 hq; exact absurd (hσ e he) hqB

/-! ### Stability -/

/-- Stability only depends on the local history of `p` and on the values in `p`'s module. -/
lemma stable_congr {τ τ' : List (Ev N V Val)} {p : Fin N} (hv : A.Valid τ)
    (hp : proj τ' p = proj τ p) (hm : ∀ v, A.home v = p → A.memVal τ' v = A.memVal τ v)
    (hs : A.Stable τ p) : A.Stable τ' p := by
  intro σ hσ hval
  by_contra hne
  obtain ⟨σ₁, e, σ₂, rfl, h0, hr⟩ := A.exists_first_remote hne
  have hσ₁ : ∀ e' ∈ σ₁, e'.p = p := fun e' he' => (hσ e' (by simp [he'])).1
  have hep : e.p = p := (hσ e (by simp)).1
  have hloc : ∀ e' ∈ σ₁, ∀ v, e'.op.var = some v → A.home v = p := by
    intro e' he' v hv
    rw [← hσ₁ e' he']
    exact A.home_eq_of_not_remote ((A.rmr_eq_zero_iff).1 h0 e' he') hv
  have hv1 : A.Valid (τ' ++ σ₁ ++ [e]) :=
    Valid.of_prefix A hval ⟨σ₂, by simp⟩
  have hvτ : A.Valid (τ ++ σ₁) := by
    refine A.valid_transport (τ := τ') (Valid.of_append A hv1) hv ?_ ?_
    · intro e' he'; rw [hσ₁ e' he', hp]
    · intro e' he' v hv'; exact (hm v (hloc e' he' v hv')).symm
  have hs1 : A.StepOK (τ' ++ σ₁) e := ((A.valid_snoc _ e).1 hv1).2
  have hs2 := A.stepOK_reval (τ' := τ ++ σ₁) hs1 (by
    rw [proj_append, proj_append, hep, hp])
  have hv2 : A.Valid (τ ++ (σ₁ ++ [⟨e.p, e.op.reval (A.memVal (τ ++ σ₁))⟩])) := by
    rw [← List.append_assoc, valid_snoc]; exact ⟨hvτ, hs2⟩
  have := hs _ ?_ hv2
  · rw [rmr_append, rmr_singleton, Ev.remote_reval] at this
    simp [hr] at this
  · intro e' he'
    rcases List.mem_append.1 he' with he' | he'
    · exact hσ e' (by simp [he'])
    · simp at he'; subst he'; simp [hep, (hσ e (by simp)).2]

/-- An unstable process, run solo, eventually performs an RMR: its *next RMR*. -/
lemma exists_next_rmr {τ : List (Ev N V Val)} {p : Fin N} (h : ¬ A.Stable τ p) :
    ∃ α e, SoloPoll p (α ++ [e]) ∧ A.Valid (τ ++ α ++ [e]) ∧ A.rmr α = 0 ∧
      e.remote A.home = true := by
  simp only [Stable, not_forall] at h
  obtain ⟨σ, hσ, hv, hne⟩ := h
  obtain ⟨σ₁, e, σ₂, rfl, h0, hr⟩ := A.exists_first_remote hne
  refine ⟨σ₁, e, fun e' he' => hσ e' (by simp at he' ⊢; tauto), ?_, h0, hr⟩
  exact Valid.of_prefix A hv ⟨σ₂, by simp⟩

end Algorithm

end Podc.CCvsDSMSeparation
