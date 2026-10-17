import Papers.PODC2026.ConsistentRefereeing.Cases

/-!
# Theorem 5: the stack case

Case 4 of the proof of Theorem 5 of [ACE26]: the critical steps of `i` and `j` access the same
stack `R`.

* both pop: the two orders lead to the same memory (case 4a);
* otherwise (case 4b/4c) we may assume that `j` pushes `u`. Compare `α·i·j` (a descendant of
  `α·i`) with `α·j`: their stacks are `X₁ ++ S` and `X₂ ++ S` with `X₁, X₂` starting with `u`,
  and they agree on every process except `i`. Run the canonical finishing execution of `α·i·j`
  (a third competitor solo, then the referee) from both, in lock-step (`lockstep`). If no step pops
  into `X₁`/`X₂`, the referee returns the same value in both runs. Otherwise, at the first such pop
  by `q`, the configuration reached by `α·i·j·β₁·q` *equals* the one reached by `α·j·β₁·q·i`
  (both stacks become the same once `u` is popped and `i` takes its step). Either way a
  descendant of `α·i` and a descendant of `α·j` share a value — a contradiction.

The paper assumes w.l.o.g. that pushed values are distinct (by stamping them); the lock-step
argument tracks stack positions instead and needs no such assumption.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Referee

open Impl

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι]
variable {I : Impl (contestObj P) B P L} {ref : P}

/-! ## Generic facts -/

omit [DecidableEq ι] in
/-- Admissibility only depends on the per-process histories of the prefix. -/
lemma Adm.transfer {α₁ α₂ β : List (Label P (contestObj P))} (h₁ : Adm ref (α₁ ++ β))
    (h₂ : Adm ref α₂) (hops : ∀ q, opsOf α₁ q = opsOf α₂ q)
    (hresps : ∀ q, respsOf α₁ q ≠ [] → respsOf α₂ q ≠ []) : Adm ref (α₂ ++ β) := by
  refine ⟨fun p => ?_, fun p o ho => ?_, fun β' γ o h => ?_⟩
  · have := h₁.oneShot p; simpa [opsOf_append, hops] using this
  · exact h₁.role p o (by simpa [opsOf_append, hops] using ho)
  · rcases List.append_eq_append_iff.1 h with ⟨a', rfl, h2⟩ | ⟨c', h1, h2⟩
    · -- the invocation lies in `β`
      obtain ⟨c, hc, hcr⟩ := h₁.late (α₁ ++ a') γ o (by rw [h2]; simp)
      refine ⟨c, hc, ?_⟩
      rw [respsOf_append] at hcr ⊢
      by_cases h' : respsOf α₁ c = []
      · rw [h', List.nil_append] at hcr; simp [hcr]
      · simp [hresps c h']
    · rcases c' with _ | ⟨z, c'⟩
      · simp only [List.nil_append, List.append_nil] at h1 h2
        subst h1
        obtain ⟨c, hc, hcr⟩ := h₁.late α₁ γ o (by rw [← h2])
        exact ⟨c, hc, hresps c hcr⟩
      · simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        exact h₂.late β' c' _ h1

omit [DecidableEq ι] in
lemma respOf_transfer {α₁ α₂ β : List (Label P (contestObj P))} (h : respsOf α₁ ref = respsOf α₂ ref) :
    respOf (α₁ ++ β) (ref, 0) = respOf (α₂ ++ β) (ref, 0) := by
  simp [respOf, respsOf_append, h]

lemma Config.ext_of {C D : Config (contestObj P) B P L} (h1 : C.loc = D.loc) (h2 : C.pend = D.pend)
    (h3 : C.mem = D.mem) : C = D := by
  cases C; cases D; simp_all

lemma step_tau_eq {C : Config (contestObj P) B P L} {p : P} (hp : C.pend p ≠ none) {a : ι}
    {o : (B a).Op} {k : (B a).Resp → L} (hact : I.act p (C.loc p) = .access a o k) :
    I.step C (.tau p) = some { C with
      mem := Function.update C.mem a ((B a).δ (C.mem a) o).1
      loc := Function.update C.loc p (k ((B a).δ (C.mem a) o).2) } := by
  simp [step, hp, hact]

variable (I ref) in
/-- The canonical finishing execution: competitor `k` (invoked if necessary) runs solo to
completion, then the referee invokes `decide` and runs solo to completion. -/
theorem exists_finish_labels (H : Hyps I ref) {α : List (Label P (contestObj P))}
    {C : Config (contestObj P) B P L} (hC : I.run α = some C) (hA : Adm ref α)
    (href : opsOf α ref = []) {k : P} (hk : k ≠ ref) :
    ∃ β D w, I.runFrom C β = some D ∧ (∀ ℓ ∈ β, ℓ.proc = k ∨ ℓ.proc = ref) ∧
      Adm ref (α ++ β) ∧ respOf (α ++ β) (ref, 0) = some (.winner (some w)) := by
  -- invoke `k` if necessary
  obtain ⟨β₀, C₀, hC₀, hβ₀, hA₀, hk₀, -⟩ : ∃ β₀ C₀, I.runFrom C β₀ = some C₀ ∧
      (∀ ℓ ∈ β₀, ℓ.proc = k) ∧ Adm ref (α ++ β₀) ∧ opsOf (α ++ β₀) k ≠ [] ∧ True := by
    by_cases hk₁ : opsOf α k = []
    · have hnx : nxt I ref α C k = some (.inv k (roleOp ref k)) := by simp [nxt, hk₁]
      obtain ⟨C₀, hC₀, hA₀⟩ := nxt_step I ref H.allowed hC hA hnx (fun h => absurd h hk)
      exact ⟨[.inv k (roleOp ref k)], C₀, by simp [runFrom_cons, hC₀], by simp [Label.proc],
        hA₀, by simp [opsOf_append], trivial⟩
    · exact ⟨[], C, rfl, by simp, by simpa using hA, by simpa using hk₁, trivial⟩
  have hr₀ : I.run (α ++ β₀) = some C₀ := by rw [run_append_of_eq I hC, hC₀]
  have href₀ : opsOf (α ++ β₀) ref = [] := by
    rw [opsOf_append, href, opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hβ₀ ℓ hℓ]; exact hk)]
    rfl
  -- `k` completes
  obtain ⟨β₁, D₁, hD₁, hD₁k, hβ₁p, hβ₁ops⟩ := exists_finish I ref H.lf hr₀ hA₀ k
  have hr₁ : I.run (α ++ β₀ ++ β₁) = some D₁ := by rw [run_append_of_eq I hr₀, hD₁]
  have hA₁ := hA₀.append_noInv ref (noInv_of_opsOf hβ₁ops)
  have hops₁ : ∀ q, opsOf (α ++ β₀ ++ β₁) q = opsOf (α ++ β₀) q := fun q => by
    simp [opsOf_append, hβ₁ops q]
  have hcomp : respsOf (α ++ β₀ ++ β₁) k ≠ [] :=
    respsOf_ne_nil_of_done I hr₁ hD₁k (by rw [hops₁]; exact hk₀)
  -- the referee runs
  have hrr : roleOp ref ref = (.decide : ContestOp P) := by simp [roleOp]
  have hnx : nxt I ref (α ++ β₀ ++ β₁) D₁ ref = some (.inv ref .decide) := by
    unfold nxt; rw [hops₁, href₀, hrr]; simp
  obtain ⟨E₁, hE₁, hAE₁⟩ := nxt_step I ref H.allowed hr₁ hA₁ hnx (fun _ => ⟨k, hk, hcomp⟩)
  have hrE₁ : I.run (α ++ β₀ ++ β₁ ++ [.inv ref .decide]) = some E₁ := by
    rw [run_append_of_eq I hr₁, runFrom_singleton, hE₁]
  obtain ⟨γ, F₁, hF₁, hF₁r, hγp, hγops⟩ := exists_finish I ref H.lf hrE₁ hAE₁ ref
  have hrF : I.run (α ++ β₀ ++ β₁ ++ [.inv ref .decide] ++ γ) = some F₁ := by
    rw [run_append_of_eq I hrE₁, hF₁]
  have hAF := hAE₁.append_noInv ref (noInv_of_opsOf hγops)
  have hops : opsOf (α ++ β₀ ++ β₁ ++ [.inv ref .decide] ++ γ) ref ≠ [] := by
    simp [opsOf_append]
  have hdone := respsOf_ne_nil_of_done I hrF hF₁r hops
  obtain ⟨r, hr⟩ : ∃ r, respOf (α ++ β₀ ++ β₁ ++ [.inv ref .decide] ++ γ) (ref, 0) = some r := by
    simp only [respOf]
    exact ⟨_, List.getElem?_eq_getElem (List.length_pos_of_ne_nil hdone)⟩
  obtain ⟨hlin, hlinf, -⟩ := H.sl
  obtain ⟨w, rfl, -⟩ := decide_some I ref ⟨_, hrF⟩ hAF (hlinf _ ⟨_, hrF⟩ hAF) hr
  refine ⟨β₀ ++ β₁ ++ [.inv ref .decide] ++ γ, F₁, w, ?_, ?_, by simpa using hAF,
    by simpa using hr⟩
  · rw [show β₀ ++ β₁ ++ [.inv ref .decide] ++ γ = β₀ ++ (β₁ ++ ([.inv ref .decide] ++ γ)) by
      simp, runFrom_append_of_eq I hC₀, runFrom_append_of_eq I hD₁,
      runFrom_append_of_eq I (by rw [runFrom_singleton]; exact hE₁), hF₁]
  · intro ℓ hℓ
    simp only [List.mem_append, List.mem_singleton] at hℓ
    rcases hℓ with ((h | h) | h) | h
    · exact Or.inl (hβ₀ ℓ h)
    · exact Or.inl (hβ₁p ℓ h)
    · subst h; exact Or.inr rfl
    · exact Or.inr (hγp ℓ h)

/-! ## Lock-step runs on two configurations differing in one stack -/

section Lockstep

variable {V : Type} {R : ι} (rep : StackRep (B R) V) (Q : Set P) (X₁ X₂ S : List V)

/-- `E₁` and `E₂` agree on the processes of `Q` and on all objects but `R`, have the same
pending operations, and the stack `R` is `T ++ X₁ ++ S` in `E₁` and `T ++ X₂ ++ S` in `E₂`. -/
structure SRel (T : List V) (E₁ E₂ : Config (contestObj P) B P L) : Prop where
  loc : ∀ q ∈ Q, E₁.loc q = E₂.loc q
  pend : E₁.pend = E₂.pend
  mem : ∀ a, a ≠ R → E₁.mem a = E₂.mem a
  st₁ : rep.toList (E₁.mem R) = T ++ (X₁ ++ S)
  st₂ : rep.toList (E₂.mem R) = T ++ (X₂ ++ S)

variable (I) in
/-- The label `ℓ` pops the stack `R` when its top part `T` is empty. -/
def Esc (T : List V) (E : Config (contestObj P) B P L) (ℓ : Label P (contestObj P)) : Prop :=
  T = [] ∧ ∃ q o k, ℓ = .tau q ∧ I.act q (E.loc q) = .access R o k ∧ rep.push o = none

variable {rep Q X₁ X₂ S}

lemma SRel.step {T : List V} {E₁ E₂ E₁' : Config (contestObj P) B P L} (h : SRel rep Q X₁ X₂ S T E₁ E₂)
    {ℓ : Label P (contestObj P)} (hs : I.step E₁ ℓ = some E₁') (hQ : ℓ.proc ∈ Q)
    (hesc : ¬ Esc I rep T E₁ ℓ) :
    ∃ T' E₂', I.step E₂ ℓ = some E₂' ∧ SRel rep Q X₁ X₂ S T' E₁' E₂' := by
  classical
  cases ℓ with
  | inv q o =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := step_inv hs
    have hq : q ∈ Q := hQ
    refine ⟨T, { E₂ with
      pend := Function.update E₂.pend q (some o)
      loc := Function.update E₂.loc q (I.invoke q (E₂.loc q) o) }, ?_, ?_⟩
    · have h0' : E₂.pend q = none := by rw [← h.pend]; exact h0
      simp [Impl.step, h0', h1]
    · refine ⟨fun q' hq' => ?_, by rw [h2, h.pend], fun a ha => by rw [h4]; exact h.mem a ha,
        by rw [h4]; exact h.st₁, h.st₂⟩
      rw [h3]
      by_cases e : q' = q
      · subst e; simp [h.loc _ hq]
      · simp [Function.update_of_ne e, h.loc q' hq']
  | ret q r =>
    obtain ⟨h0, h1, h2, l, hact, hl⟩ := step_ret hs
    have hq : q ∈ Q := hQ
    have hact' : I.act q (E₂.loc q) = .ret r l := by rw [← h.loc q hq, hact]
    refine ⟨T, { E₂ with
      pend := Function.update E₂.pend q none
      loc := Function.update E₂.loc q l }, ?_, ?_⟩
    · have h0' : E₂.pend q ≠ none := by rw [← h.pend]; exact h0
      simp [Impl.step, h0', hact']
    · refine ⟨fun q' hq' => ?_, by rw [h1, h.pend], fun a ha => by rw [h2]; exact h.mem a ha,
        by rw [h2]; exact h.st₁, h.st₂⟩
      rw [hl]
      by_cases e : q' = q
      · subst e; simp
      · simp [Function.update_of_ne e, h.loc q' hq']
  | tau q =>
    obtain ⟨h0, h1, a, o, k, hact, hm, hl⟩ := step_tau hs
    have hq : q ∈ Q := hQ
    have hact' : I.act q (E₂.loc q) = .access a o k := by rw [← h.loc q hq, hact]
    have h0' : E₂.pend q ≠ none := by rw [← h.pend]; exact h0
    by_cases haR : a = R
    · subst haR
      cases hpo : rep.push o with
      | some v =>
        refine ⟨v :: T, _, step_tau_eq h0' hact', ⟨fun q' hq' => ?_, by rw [h1]; exact h.pend,
          fun a' ha' => ?_, ?_, ?_⟩⟩
        · rw [hl]
          by_cases e : q' = q
          · subst e; simp [rep.push_resp (E₁.mem a) (E₂.mem a) o v hpo]
          · simp [Function.update_of_ne e, h.loc q' hq']
        · rw [hm]; simp [Function.update_of_ne ha', h.mem a' ha']
        · rw [hm]; simp [rep.push_state _ o v hpo, h.st₁]
        · simp [rep.push_state _ o v hpo, h.st₂]
      | none =>
        cases T with
        | nil => exact absurd ⟨rfl, q, o, k, rfl, hact, hpo⟩ hesc
        | cons t T =>
          have hhead : (rep.toList (E₁.mem a)).head? = (rep.toList (E₂.mem a)).head? := by
            rw [h.st₁, h.st₂]; rfl
          refine ⟨T, _, step_tau_eq h0' hact', ⟨fun q' hq' => ?_, by rw [h1]; exact h.pend,
            fun a' ha' => ?_, ?_, ?_⟩⟩
          · rw [hl]
            by_cases e : q' = q
            · subst e; simp [rep.pop_resp (E₁.mem a) (E₂.mem a) o hpo hhead]
            · simp [Function.update_of_ne e, h.loc q' hq']
          · rw [hm]; simp [Function.update_of_ne ha', h.mem a' ha']
          · rw [hm]; simp [rep.pop_state _ o hpo, h.st₁]
          · simp [rep.pop_state _ o hpo, h.st₂]
    · have hma := h.mem a haR
      refine ⟨T, _, step_tau_eq h0' hact', ⟨fun q' hq' => ?_, by rw [h1]; exact h.pend,
        fun a' ha' => ?_, ?_, ?_⟩⟩
      · rw [hl]
        by_cases e : q' = q
        · subst e; simp [hma]
        · simp [Function.update_of_ne e, h.loc q' hq']
      · rw [hm]
        by_cases e : a' = a
        · subst e; simp [hma]
        · simp [Function.update_of_ne e, h.mem a' ha']
      · rw [hm]; simp [Function.update_of_ne (Ne.symm haR), h.st₁]
      · simp [Function.update_of_ne (Ne.symm haR), h.st₂]

/-- **Lock-step runs.** A run of processes of `Q` from `E₁` can be replayed from `E₂` (keeping
the relation), unless at some point a step pops the stack `R` while its top part is empty. -/
theorem lockstep : ∀ (β : List (Label P (contestObj P))) {T : List V}
    {E₁ E₂ E₁' : Config (contestObj P) B P L}, SRel rep Q X₁ X₂ S T E₁ E₂ →
    I.runFrom E₁ β = some E₁' → (∀ ℓ ∈ β, ℓ.proc ∈ Q) →
    (∃ T' E₂', I.runFrom E₂ β = some E₂' ∧ SRel rep Q X₁ X₂ S T' E₁' E₂') ∨
    (∃ β₁ ℓ β₂ F₁ F₂, β = β₁ ++ ℓ :: β₂ ∧ I.runFrom E₁ β₁ = some F₁ ∧
      I.runFrom E₂ β₁ = some F₂ ∧ SRel rep Q X₁ X₂ S [] F₁ F₂ ∧ Esc I rep [] F₁ ℓ ∧
      ∃ F₁', I.step F₁ ℓ = some F₁' ∧ I.runFrom F₁' β₂ = some E₁') := by
  intro β
  induction β with
  | nil =>
    intro T E₁ E₂ E₁' h hr _
    simp only [runFrom_nil, Option.some.injEq] at hr; subst hr
    exact Or.inl ⟨T, E₂, rfl, h⟩
  | cons ℓ β ih =>
    intro T E₁ E₂ E₁' h hr hQ
    simp only [runFrom_cons] at hr
    cases hs : I.step E₁ ℓ with
    | none => simp [hs] at hr
    | some G₁ =>
      simp only [hs, Option.bind_some] at hr
      by_cases hesc : Esc I rep T E₁ ℓ
      · right
        have hT := hesc.1; subst hT
        exact ⟨[], ℓ, β, E₁, E₂, rfl, rfl, rfl, h, hesc, G₁, hs, hr⟩
      · obtain ⟨T', G₂, hG₂, h'⟩ := h.step hs (hQ ℓ (by simp)) hesc
        rcases ih h' hr (fun ℓ' hℓ' => hQ ℓ' (by simp [hℓ'])) with
          ⟨T'', E₂', hE₂', h''⟩ | ⟨β₁, ℓ', β₂, F₁, F₂, hβ, hF₁, hF₂, hrel, hesc', F₁', hF₁', hr'⟩
        · exact Or.inl ⟨T'', E₂', by simp [runFrom_cons, hG₂, hE₂'], h''⟩
        · exact Or.inr ⟨ℓ :: β₁, ℓ', β₂, F₁, F₂, by simp [hβ], by simp [runFrom_cons, hs, hF₁],
            by simp [runFrom_cons, hG₂, hF₂], hrel, hesc', F₁', hF₁', hr'⟩

end Lockstep

/-! ## The stack case -/

namespace Crit

variable (K : Crit I ref) (H : Hyps I ref)
include H

/-- Case 4b/4c: `j` pushes on the stack `R` and `i` modifies `R`. -/
theorem stack_push {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref) (hk : k ≠ ref) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hv : K.v i ≠ K.v j) {V : Type} {R : ι} (rep : StackRep (B R) V)
    {oi oj : (B R).Op} {ki kj : (B R).Resp → L} (hli : K.lbl i = .tau i)
    (hai : I.act i (K.C.loc i) = .access R oi ki)
    (hmi : ((B R).δ (K.C.mem R) oi).1 ≠ K.C.mem R) (hlj : K.lbl j = .tau j)
    (haj : I.act j (K.C.loc j) = .access R oj kj) {uj : V} (hpj : rep.push oj = some uj) :
    False := by
  classical
  obtain ⟨C₁, h₁, hA₁⟩ := K.step₁ H.allowed hi
  obtain ⟨C₁₂, h₁₂, hA₁₂⟩ := K.step₂ H.allowed hi hj hij h₁ hA₁
  obtain ⟨C₂, h₂, hA₂⟩ := K.step₁ H.allowed hj
  simp only [hli, hlj] at h₁ h₁₂ h₂ hA₁ hA₁₂ hA₂
  obtain ⟨m₁, l₁, p₁⟩ := step_tau_mem h₁ hai
  have hai' : I.act j (C₁.loc j) = .access R oj kj := by
    rw [l₁, Function.update_of_ne (Ne.symm hij)]; exact haj
  obtain ⟨m₁₂, l₁₂, p₁₂⟩ := step_tau_mem h₁₂ hai'
  obtain ⟨m₂, l₂, p₂⟩ := step_tau_mem h₂ haj
  have hpendi : K.C.pend i ≠ none := (step_tau h₁).1
  set s := K.C.mem R with hs
  -- the two stacks
  obtain ⟨X₁, X₂, S, hX₁, hX₂, hresp⟩ : ∃ X₁ X₂ S,
      rep.toList (C₁₂.mem R) = [] ++ (uj :: X₁ ++ S) ∧ rep.toList (C₂.mem R) = [] ++ (uj :: X₂ ++ S) ∧
      ∀ (Y : List V) (y : (B R).State), rep.toList y = X₂ ++ S →
        rep.toList ((B R).δ y oi).1 = X₁ ++ S ∧ ((B R).δ y oi).2 = ((B R).δ s oi).2 := by
    have e₁₂ : rep.toList (C₁₂.mem R) = uj :: rep.toList ((B R).δ s oi).1 := by
      rw [m₁₂, Function.update_self, m₁, Function.update_self, rep.push_state _ _ _ hpj]
    have e₂ : rep.toList (C₂.mem R) = uj :: rep.toList s := by
      rw [m₂, Function.update_self, rep.push_state _ _ _ hpj]
    cases hpi : rep.push oi with
    | some ui =>
      refine ⟨[ui], [], rep.toList s, by rw [e₁₂, rep.push_state _ _ _ hpi]; rfl,
        by rw [e₂]; rfl, fun Y y hy => ⟨?_, rep.push_resp _ _ _ _ hpi⟩⟩
      rw [rep.push_state _ _ _ hpi, hy]; rfl
    | none =>
      obtain ⟨a, S, hsS⟩ : ∃ a S, rep.toList s = a :: S := by
        cases h : rep.toList s with
        | nil =>
          refine absurd (rep.inj ?_) hmi
          rw [rep.pop_state _ _ hpi, h]; rfl
        | cons a S => exact ⟨a, S, rfl⟩
      refine ⟨[], [a], S, by rw [e₁₂, rep.pop_state _ _ hpi, hsS]; rfl,
        by rw [e₂, hsS]; rfl, fun Y y hy => ⟨?_, rep.pop_resp _ _ _ hpi (by rw [hy, hsS]; rfl)⟩⟩
      rw [rep.pop_state _ _ hpi, hy]; rfl
  -- the relation between `α·i·j` and `α·j`
  let Q : Set P := {q | q ≠ i}
  have hrel : SRel rep Q (uj :: X₁) (uj :: X₂) S [] C₁₂ C₂ := by
    refine ⟨fun q hq => ?_, by rw [p₁₂, p₁, p₂], fun a ha => ?_, hX₁, hX₂⟩
    · have hqi : q ≠ i := hq
      rw [l₁₂, l₂, l₁]
      by_cases hqj : q = j
      · subst hqj
        simp only [Function.update_self]
        congr 1
        exact rep.push_resp _ _ _ _ hpj
      · simp [Function.update_of_ne hqj, Function.update_of_ne hqi]
    · rw [m₁₂, m₂, m₁, Function.update_of_ne ha, Function.update_of_ne ha, Function.update_of_ne ha]
  -- the finishing run of `α·i·j`
  have hr₁₂ : I.run (K.α ++ [.tau i] ++ [.tau j]) = some C₁₂ := by
    rw [run_append_of_eq I (by rw [run_append_of_eq I K.run, runFrom_singleton, h₁]),
      runFrom_singleton, h₁₂]
  have hr₂ : I.run (K.α ++ [.tau j]) = some C₂ := by
    rw [run_append_of_eq I K.run, runFrom_singleton, h₂]
  obtain ⟨β, D, w, hD, hβp, hAβ, hw⟩ := exists_finish_labels I ref H hr₁₂ hA₁₂
    (by simp [opsOf_append, K.noref]) hk
  have hwi : w = K.v i := K.uni i hi w
    ⟨[.tau j] ++ β, ⟨D, by rw [hli, ← List.append_assoc, run_append_of_eq I hr₁₂, hD]⟩,
      by rw [hli, ← List.append_assoc]; exact hAβ, by rw [hli, ← List.append_assoc]; exact hw⟩
  have hβQ : ∀ ℓ ∈ β, ℓ.proc ∈ Q := fun ℓ hℓ => by
    rcases hβp ℓ hℓ with h | h <;> rw [h]
    · exact Ne.symm hik
    · exact Ne.symm hi
  -- per-process histories of `α·i·j` and `α·j` coincide
  have hops : ∀ (γ : List (Label P (contestObj P))) q,
      opsOf (K.α ++ [.tau i] ++ [.tau j] ++ γ) q = opsOf (K.α ++ [.tau j] ++ γ ++ [.tau i]) q :=
    fun γ q => by simp [opsOf_append]
  have hresps : ∀ (γ : List (Label P (contestObj P))) q,
      respsOf (K.α ++ [.tau i] ++ [.tau j] ++ γ) q = respsOf (K.α ++ [.tau j] ++ γ ++ [.tau i]) q :=
    fun γ q => by simp [respsOf_append]
  rcases lockstep β hrel hD hβQ with ⟨T', E₂, hE₂, -⟩ |
    ⟨β₁, ℓ, β₂, F₁, F₂, hβ, hF₁, hF₂, hrelF, ⟨-, q, o, kq, rfl, hactq, hpo⟩, F₁', hF₁', hrest⟩
  · -- no pop into the critical part: both runs give the same response
    have hA : Adm ref (K.α ++ [.tau j] ++ β) :=
      Adm.transfer hAβ (by simpa using hA₂) (fun q => by simp [opsOf_append])
        (fun q h => by simpa [respsOf_append] using h)
    have hwj : w = K.v j := K.uni j hj w ⟨β, ⟨E₂, by
      rw [hlj, run_append_of_eq I hr₂, hE₂]⟩, by rw [hlj]; exact hA, by
      rw [hlj, ← hw, respOf_transfer]; simp [respsOf_append]⟩
    exact hv (hwi.symm.trans hwj)
  · -- the first pop into the critical part, by `q`
    have hqQ : q ∈ Q := hβQ (.tau q) (by rw [hβ]; simp)
    have hqi : q ≠ i := hqQ
    have hpq : F₁.pend q ≠ none := (step_tau hF₁').1
    obtain ⟨mF₁, lF₁, pF₁⟩ := step_tau_mem hF₁' hactq
    have hactq₂ : I.act q (F₂.loc q) = .access R o kq := by rw [← hrelF.loc q hqQ]; exact hactq
    have hpq₂ : F₂.pend q ≠ none := by rw [← hrelF.pend]; exact hpq
    have hF₂' := step_tau_eq hpq₂ hactq₂
    set F₂' := { F₂ with
      mem := Function.update F₂.mem R ((B R).δ (F₂.mem R) o).1
      loc := Function.update F₂.loc q (kq ((B R).δ (F₂.mem R) o).2) } with hF₂'def
    -- `i` has not moved in the run from `α·j`
    have hiF₂ : F₂.loc i = K.C.loc i ∧ F₂.pend i = K.C.pend i := by
      have h1 := I.runFrom_other hF₂ (q := i) (fun ℓ hℓ => (hβQ ℓ (by rw [hβ]; simp [hℓ])))
      rw [h1.1, h1.2, l₂, p₂, Function.update_of_ne hij]; exact ⟨rfl, rfl⟩
    have hactF₂' : I.act i (F₂'.loc i) = .access R oi ki := by
      simp only [hF₂'def, Function.update_of_ne hqi.symm]; rw [hiF₂.1]; exact hai
    have hpF₂' : F₂'.pend i ≠ none := by simp only [hF₂'def]; rw [hiF₂.2]; exact hpendi
    have hF₂'' := step_tau_eq hpF₂' hactF₂'
    -- the stacks after the pop of `q`
    have hstF₂' : rep.toList (F₂'.mem R) = X₂ ++ S := by
      simp only [hF₂'def, Function.update_self]
      rw [rep.pop_state _ _ hpo, hrelF.st₂]; rfl
    obtain ⟨hsti, hrespi⟩ := hresp (X₂ ++ S) (F₂'.mem R) hstF₂'
    -- `i`'s state in the run from `α·i·j`
    have hiF₁ : F₁'.loc i = ki ((B R).δ s oi).2 := by
      have h1 := I.runFrom_other hF₁ (q := i) (fun ℓ hℓ => (hβQ ℓ (by rw [hβ]; simp [hℓ])))
      rw [lF₁, Function.update_of_ne hqi.symm, h1.1, l₁₂, Function.update_of_ne hij,
        l₁, Function.update_self]
    -- the two configurations coincide
    have heq : F₁' = { F₂' with
        mem := Function.update F₂'.mem R ((B R).δ (F₂'.mem R) oi).1
        loc := Function.update F₂'.loc i (ki ((B R).δ (F₂'.mem R) oi).2) } := by
      apply Config.ext_of
      · funext p
        by_cases hpi : p = i
        · subst hpi; simp only [Function.update_self]; rw [hiF₁, hrespi]
        · simp only [Function.update_of_ne hpi, hF₂'def]
          rw [lF₁]
          by_cases hpq' : p = q
          · subst hpq'; simp only [Function.update_self]
            congr 1
            exact rep.pop_resp _ _ _ hpo (by rw [hrelF.st₁, hrelF.st₂]; rfl)
          · simp only [Function.update_of_ne hpq']; exact hrelF.loc p hpi
      · rw [pF₁, hrelF.pend]
      · funext a
        by_cases haR : a = R
        · subst haR
          simp only [Function.update_self]
          apply rep.inj
          rw [mF₁, Function.update_self, rep.pop_state _ _ hpo, hrelF.st₁, hsti]; rfl
        · simp only [Function.update_of_ne haR, hF₂'def]; rw [mF₁, Function.update_of_ne haR]
          exact hrelF.mem a haR
    -- hence `w` is also a value of `α·j`
    have hrun : I.runFrom C₂ (β₁ ++ [.tau q] ++ [.tau i] ++ β₂) = some D := by
      rw [List.append_assoc, List.append_assoc, runFrom_append_of_eq I hF₂, List.singleton_append,
        runFrom_cons, hF₂', Option.bind_some, List.singleton_append, runFrom_cons, hF₂'',
        Option.bind_some, ← heq, hrest]
    have hApre : Adm ref (K.α ++ [.tau j] ++ (β₁ ++ [.tau q]) ++ [.tau i]) := by
      have h1 : Adm ref (K.α ++ [.tau i] ++ [.tau j] ++ (β₁ ++ [.tau q])) :=
        hAβ.of_prefix ⟨β₂, by rw [hβ]; simp⟩
      have h2 := Adm.transfer (α₂ := K.α ++ [.tau j]) h1 (by simpa using hA₂)
        (fun q => by simp [opsOf_append]) (fun q h => by simpa [respsOf_append] using h)
      exact h2.append_noInv ref (fun ℓ hℓ q => by simp at hℓ; subst hℓ; rfl)
    have hA : Adm ref (K.α ++ [.tau j] ++ (β₁ ++ [.tau q] ++ [.tau i] ++ β₂)) := by
      have h1 : Adm ref (K.α ++ [.tau i] ++ [.tau j] ++ (β₁ ++ [.tau q]) ++ β₂) := by
        rw [hβ] at hAβ; simpa using hAβ
      have := Adm.transfer (α₂ := K.α ++ [.tau j] ++ (β₁ ++ [.tau q]) ++ [.tau i]) h1 hApre
        (fun q' => hops _ q') (fun q' h => by rw [← hresps]; exact h)
      simpa using this
    have hwj : w = K.v j := K.uni j hj w ⟨β₁ ++ [.tau q] ++ [.tau i] ++ β₂, ⟨D, by
      rw [hlj, run_append_of_eq I hr₂, hrun]⟩, by rw [hlj]; simpa using hA, by
      rw [hlj, ← hw, hβ]
      have := respOf_transfer (ref := ref) (β := β₂) (hresps (β₁ ++ [.tau q]) ref)
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
        at this ⊢
      exact this.symm⟩
    exact hv (hwi.symm.trans hwj)

end Crit

end Referee

end Cslib.SharedMemory
