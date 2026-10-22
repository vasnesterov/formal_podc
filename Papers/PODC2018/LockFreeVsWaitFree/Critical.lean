import Papers.PODC2018.LockFreeVsWaitFree.Valency

/-!
# Critical executions (Definition 5 and Lemma 10 of [ACHP18])

* `Ctx.Critical α v q v'` — Definition 5: `p₀(C)` is `v`-univalent, `p₀(q(C))` is
  `v'`-univalent (`v ≠ v'`, `q ≠ p₀`), and `p₀(C')` is univalent for every extension `C'` of
  `C`. We only require the last condition for extensions in which `p₀` takes no step, which is
  all that Lemma 8 (Claim 9) uses; this makes the notion weaker and Lemma 8 stronger.
* `Ctx.biv_nil` — the empty execution is bivalent (first paragraph of the proof of Lemma 10):
  `p₀` running solo outputs at least `1/2`, while after two operations of `p₁` it outputs at
  most `3/8`.
* `Ctx.exists_critical` — **Lemma 10**: a wait-free linearizable implementation has a critical
  execution.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeVsWaitFree

open Cslib SharedMemory Impl

namespace Ctx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] {X : Ctx P ι L B}

variable (X) in
/-- **Definition 5 of [ACHP18]** (for extensions without steps of `p₀`): `α` is
`(v, q, v')`-critical. -/
def Critical (α : List (LLabel P)) (v : ℝ) (q : P) (v' : ℝ) : Prop :=
  X.Good α ∧ q ≠ X.p₀ ∧ v ≠ v' ∧ X.Univ (X.ext1 α X.p₀) v ∧ X.Univ (X.ext α [q, X.p₀]) v' ∧
    ∀ σ : List P, X.p₀ ∉ σ → ∃ w, X.Univ (X.ext α (σ ++ [X.p₀])) w

/-! ### Labels of good executions are the scheduled ones -/

/-- In a good execution, the label taken by a process is its next label. -/
lemma Good.nl_of_append {α : List (LLabel P)} {ℓ : LLabel P} (h : X.Good (α ++ [ℓ])) :
    X.nl α ℓ.proc = some ℓ := by
  have hα : X.Good α := h.of_append
  have hs : X.I.step (X.cfg α) ℓ = some (X.cfg (α ++ [ℓ])) := by
    have := h.run
    rw [run_append_of_eq _ hα.run, runFrom_singleton] at this
    exact this
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, -⟩ := step_inv hs
    have ho : o = side X.p₀ p := h.2.side p o (by simp [opsOf_append])
    subst ho
    show X.nl α p = _
    unfold nl
    rw [ite_eq_left_of_eq_true _ _ (eq_true h0), ite_eq_right_of_eq_false _ _ (eq_false ?_)]
    rintro ⟨rfl, hne⟩
    have := h.2.once
    simp only [opsOf_append, opsOf_cons, Label.invOf_inv, ite_true, Option.toList_some,
      opsOf_nil, List.append_nil, List.length_append, List.length_singleton] at this
    exact hne (List.length_eq_zero_iff.1 (by omega))
  | tau p =>
    obtain ⟨h0, -, i, o, k, hact, -⟩ := step_tau hs
    simp [Label.proc, nl, h0, nextLabel, hact]
  | ret p r =>
    obtain ⟨h0, -, -, l, hact, -⟩ := step_ret hs
    simp [Label.proc, nl, h0, nextLabel, hact]

/-- Every good extension is the extension by the schedule of its processes. -/
lemma Good.ext_map_proc {α β : List (LLabel P)} (h : X.Good (α ++ β)) :
    X.ext α (β.map Label.proc) = α ++ β := by
  induction β using List.reverseRecOn with
  | nil => simp
  | append_singleton β ℓ ih =>
    have h1 : X.Good (α ++ β) := by
      rw [← List.append_assoc] at h; exact h.of_append
    rw [List.map_append, List.map_singleton, ext_concat, ih h1,
      ext1_of_some (by rw [← List.append_assoc] at h; exact h.nl_of_append)]
    simp

/-- `p₀` has a next label as long as it has not returned. -/
lemma Good.nl_p₀_isSome {α : List (LLabel P)} (hα : X.Good α) (hr : respsOf α X.p₀ = []) :
    (X.nl α X.p₀).isSome := by
  unfold nl
  split_ifs with h1 h2
  · exfalso
    rcases hα.p₀_counts with ⟨-, b⟩ | ⟨a, -, -⟩
    · rw [hr] at b; exact h2.2 (List.length_eq_zero_iff.1 b)
    · exact a h1
  · rfl
  · rfl

/-- `p₀` has invoked after a step of it. -/
lemma Good.opsOf_ext1_p₀_ne_nil {α : List (LLabel P)} (hα : X.Good α) : opsOf (X.ext1 α X.p₀) X.p₀ ≠ [] := by
  unfold Ctx.ext1 nl
  split_ifs with h1 h2
  · simpa using h2.2
  · simp [opsOf_append, opsOf_cons]
  · simp only [Option.toList_some, opsOf_append, ne_eq, List.append_eq_nil_iff, not_and]
    intro h3
    rcases hα.p₀_counts with ⟨a, -⟩ | ⟨-, b, -⟩
    · exact absurd a h1
    · rw [h3] at b; simp at b

/-- `p₀` is pending if it has invoked and not returned. -/
lemma Good.pend_p₀ {α : List (LLabel P)} (hα : X.Good α) (ho : opsOf α X.p₀ ≠ [])
    (hr : respsOf α X.p₀ = []) : (X.cfg α).pend X.p₀ ≠ none := by
  rcases hα.p₀_counts with ⟨-, b⟩ | ⟨a, -, -⟩
  · rw [hr] at b; exact absurd (List.length_eq_zero_iff.1 b) ho
  · exact a

/-! ### Linearizations of executions in which `p₀` returned -/

/-- In a linearization of a good execution in which `p₀` returned `v`, `p₀`'s operation is an
entry `(0, v)` and all other entries are operations of side `1`. -/
lemma Good.lin_p₀ {γ : List (LLabel P)} (hγ : X.Good γ) {v : ℝ}
    (hw : respsOf γ X.p₀ = [v]) {Lin : List (OpId P × Fin 2 × ℝ)}
    (hL : IsNLinearization llaaSpec γ Lin) :
    ∃ j : ℕ, (Lin.map Prod.fst)[j]? = some (X.p₀, 0) ∧ (Lin.map Prod.snd)[j]? = some (0, v) ∧
      ∀ t (a : Fin 2 × ℝ), (Lin.map Prod.snd)[t]? = some a → t ≠ j → a.1 = 1 := by
  have hc0 : Completed γ (X.p₀, 0) := by simp [Completed, hw]
  have hside : ∀ y ∈ Lin, y.2.1 = side X.p₀ y.1.1 := by
    intro y hy
    have h1 := hL.op_eq y hy
    simp only [opOf] at h1
    exact hγ.2.side _ _ (List.mem_of_getElem? h1)
  have hp₀ : ∀ y ∈ Lin, y.1.1 = X.p₀ → y.1.2 = 0 := by
    intro y hy hy0
    have h1 := hL.op_eq y hy
    simp only [opOf] at h1
    have h2 := (List.getElem?_eq_some_iff.1 h1).1
    have := hγ.2.once; rw [hy0] at h2; omega
  have hnd : (Lin.map Prod.fst).Nodup := hL.nodup
  obtain ⟨j, hj, hjM⟩ := List.getElem_of_mem (hL.complete _ hc0)
  have hjL : j < Lin.length := by simpa using hj
  have h1 : Lin[j].1 = (X.p₀, 0) := by simpa using hjM
  refine ⟨j, List.getElem?_eq_some_iff.2 ⟨hj, hjM⟩, ?_, ?_⟩
  · rw [List.getElem?_map, List.getElem?_eq_getElem hjL]
    have hs := hside _ (List.getElem_mem hjL)
    have hr := hL.resp_eq _ (List.getElem_mem hjL) v (by rw [h1]; simp [respOf, hw])
    simp only [Option.map_some, Option.some.injEq]
    rw [h1] at hs; simp only [side, ite_true] at hs
    exact Prod.ext hs hr
  · intro t a ha htj
    rw [List.getElem?_map] at ha
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 ha
    obtain ⟨ht, hyt⟩ := List.getElem?_eq_some_iff.1 hy
    have hymem : y ∈ Lin := hyt ▸ List.getElem_mem ht
    rw [hside y hymem]
    by_cases hy0 : y.1.1 = X.p₀
    · exfalso
      have hy1 : y.1 = (X.p₀, 0) := Prod.ext hy0 (hp₀ y hymem hy0)
      have : (Lin.map Prod.fst)[t]'(by simpa using ht) = (Lin.map Prod.fst)[j] := by
        simp only [List.getElem_map, hyt, hy1, h1]
      exact htj ((List.Nodup.getElem_inj_iff hnd).1 this)
    · simp [side, hy0]

/-! ### The empty execution is bivalent -/

/-- The empty execution is bivalent (proof of Lemma 10 of [ACHP18]). -/
theorem biv_nil {p₁ : P} (hp₁ : p₁ ≠ X.p₀) : X.Biv [] := by
  -- `p₀` running solo outputs at least `1/2`
  obtain ⟨N, v₁, hv₁⟩ := (good_nil (X := X)).exists_p₀_resp
  set γ₁ := X.ext [] (List.replicate N X.p₀)
  have hγ₁ : X.Good γ₁ := good_nil.ext _
  have hv₁' : 1 / 2 ≤ v₁ := by
    obtain ⟨Lin, hL⟩ := X.lin γ₁ hγ₁.1 hγ₁.2
    obtain ⟨j, hjM, hj, hone⟩ := hγ₁.lin_p₀ hv₁ hL
    -- only `p₀` invoked, so `j = 0`
    have hj0 : j = 0 := by
      by_contra hj0
      obtain ⟨y, hy⟩ : ∃ y, (Lin.map Prod.fst)[0]? = some y := by
        have : j < (Lin.map Prod.fst).length := (List.getElem?_eq_some_iff.1 hjM).1
        exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨h0, hy0⟩ := List.getElem?_eq_some_iff.1 hy
      have hmem : (Lin.map Prod.fst)[0] ∈ Lin.map Prod.fst := List.getElem_mem h0
      obtain ⟨z, hz, hzy⟩ := List.mem_map.1 hmem
      have hop := hL.op_eq z hz
      simp only [opOf] at hop
      have hinv := (List.getElem?_eq_some_iff.1 hop).1
      have hz0 : z.1.1 = X.p₀ := by
        by_contra hne
        rw [opsOf_ext_of_not_mem (fun h => hne (List.eq_of_mem_replicate h))] at hinv; simp at hinv
      have hz1 : z.1.2 = 0 := by have := hγ₁.2.once; rw [hz0] at hinv; omega
      have : (Lin.map Prod.fst)[0] = (Lin.map Prod.fst)[j]'(List.getElem?_eq_some_iff.1 hjM).1 := by
        rw [← hzy, (List.getElem?_eq_some_iff.1 hjM).2]; exact Prod.ext hz0 hz1
      exact hj0 ((List.Nodup.getElem_inj_iff hL.nodup).1 this).symm
    subst hj0
    exact half_le_of_legal_zero hL.legal hj
  -- after two operations of `p₁`, `p₀` outputs at most `3/8`
  obtain ⟨N₁, hN₁⟩ := (good_nil (X := X)).exists_resps p₁ 2 (fun h => absurd h hp₁)
  set δ := X.ext [] (List.replicate N₁ p₁)
  have hδ : X.Good δ := good_nil.ext _
  obtain ⟨N₂, v₂, hv₂⟩ := hδ.exists_p₀_resp
  set γ₂ := X.ext δ (List.replicate N₂ X.p₀)
  have hγ₂ : X.Good γ₂ := hδ.ext _
  have hv₂' : v₂ ≤ 3 / 8 := by
    obtain ⟨Lin, hL⟩ := X.lin γ₂ hγ₂.1 hγ₂.2
    obtain ⟨j, hjM, hj, hone⟩ := hγ₂.lin_p₀ hv₂ hL
    have hjlt : j < (Lin.map Prod.fst).length := (List.getElem?_eq_some_iff.1 hjM).1
    have hp₀δ : opsOf δ X.p₀ = [] := by
      rw [opsOf_ext_of_not_mem (fun h => hp₁ (List.eq_of_mem_replicate h).symm)]; rfl
    have h2 : 2 ≤ j := by
      have := le_idx_of_sublist hL.nodup hjlt (List.getElem?_eq_some_iff.1 hjM).2
        [(p₁, 0), (p₁, 1)] (by simp) (by
          intro a ha
          have hca : Completed δ a := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl <;> simp only [Completed] <;> omega
          refine hL.realtime _ _ ⟨δ, X.extL δ (List.replicate N₂ X.p₀), rfl, hca, ?_⟩
            (List.mem_of_getElem? hjM)
          simp [Invoked, hp₀δ])
      simpa using this
    exact le_three_eighths_of_legal hL.legal hj hone h2
  have e₂ : [] ++ X.extL [] (List.replicate N₁ p₁ ++ List.replicate N₂ X.p₀) = γ₂ := by
    rw [← ext_eq_append, ext_append]
  exact ⟨v₁, v₂, by intro h; rw [h] at hv₁'; linarith,
    ⟨X.extL [] (List.replicate N X.p₀), hγ₁, hv₁⟩,
    ⟨X.extL [] (List.replicate N₁ p₁ ++ List.replicate N₂ X.p₀), by rw [e₂]; exact hγ₂,
      by rw [e₂]; exact hv₂⟩⟩

/-! ### Lemma 10 -/

lemma exists_first_split {a : P} {τ : List P} (h : a ∈ τ) :
    ∃ σ τ', τ = σ ++ a :: τ' ∧ a ∉ σ := by
  induction τ with
  | nil => simp at h
  | cons b τ ih =>
    by_cases hb : b = a
    · exact ⟨[], τ, by simp [hb], by simp⟩
    · have : a ∈ τ := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hb
        · exact h
      obtain ⟨σ, τ', rfl, hσ⟩ := ih this
      exact ⟨b :: σ, τ', by simp, by simp [hσ, Ne.symm hb]⟩

lemma prefix_take_of_prefix {Y : Type} {l₁ l₂ : List Y} (h : l₁ <+: l₂) {m : ℕ}
    (hm : l₁.length ≤ m) : l₁ <+: l₂.take m := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append, List.take_of_length_le hm]
  exact List.prefix_append _ _

/-- No infinite chain of bivalent executions (proof of Lemma 10 of [ACHP18]): some bivalent
execution `α` has the property that `p₀(C')` is univalent for every extension `C'` of `α` without
steps of `p₀`. -/
lemma exists_biv_univ (hbiv : X.Biv []) :
    ∃ α, X.Biv α ∧ ∀ σ, X.p₀ ∉ σ → ∃ w, X.Univ (X.ext α (σ ++ [X.p₀])) w := by
  by_contra H
  push Not at H
  have key : ∀ α, X.Biv α → ∃ σ, X.p₀ ∉ σ ∧ X.Biv (X.ext α (σ ++ [X.p₀])) := by
    intro α hα
    obtain ⟨σ, hσ, hnu⟩ := H α hα
    refine ⟨σ, hσ, ?_⟩
    have hg := hα.good.ext (σ ++ [X.p₀])
    obtain ⟨w, hw⟩ := hg.exists_potent
    have : ¬ ∀ w', X.Potent (X.ext α (σ ++ [X.p₀])) w' → w' = w := fun h => hnu w ⟨hw, h⟩
    push Not at this
    obtain ⟨w', hw', hne⟩ := this
    exact ⟨w', w, hne, hw', hw⟩
  choose! σf hσf hbf using key
  set f : List (LLabel P) → List (LLabel P) := fun α => X.ext α (σf α ++ [X.p₀]) with hf
  set a : ℕ → List (LLabel P) := fun k => f^[k] [] with ha
  have hsucc : ∀ k, a (k + 1) = f (a k) := fun k => Function.iterate_succ_apply' f k []
  have hbiv' : ∀ k, X.Biv (a k) := by
    intro k; induction k with
    | zero => exact hbiv
    | succ k ih => rw [hsucc]; exact hbf _ ih
  -- the configuration before `p₀`'s step and `p₀`'s label
  set β : ℕ → List (LLabel P) := fun k => X.ext (a k) (σf (a k)) with hβ
  have hβgood : ∀ k, X.Good (β k) := fun k => (hbiv' k).good.ext _
  have hβr : ∀ k, respsOf (β k) X.p₀ = [] := fun k => by
    simp only [hβ]; rw [respsOf_ext_of_not_mem (hσf _ (hbiv' k))]; exact (hbiv' k).resps_nil
  have hsome : ∀ k, ∃ ℓ, X.nl (β k) X.p₀ = some ℓ := fun k =>
    Option.isSome_iff_exists.1 ((hβgood k).nl_p₀_isSome (hβr k))
  choose ℓ hℓ using hsome
  have hstep : ∀ k, a (k + 1) = β k ++ [ℓ k] := fun k => by
    rw [hsucc]; simp only [hf, hβ]; rw [ext_concat, ext1_of_some (hℓ k)]
  have hβpre : ∀ k, a k <+: β k := fun k => List.prefix_append _ _
  have hmono : ∀ k, a k <+: a (k + 1) := fun k => by
    rw [hstep]; exact (hβpre k).trans (List.prefix_append _ _)
  have hmono' : ∀ k k', k ≤ k' → a k <+: a k' := by
    intro k k' hk
    induction k', hk using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ k' _ ih => exact ih.trans (hmono k')
  have hlenβ : ∀ k, (a k).length ≤ (β k).length := fun k => (hβpre k).length_le
  have hlen : ∀ k, k ≤ (a k).length := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [hstep]; simp; have := hlenβ k; omega
  obtain ⟨e, hadm, hlbl, -⟩ := exists_infExec_of_chain a hmono hlen (fun k => (hbiv' k).good)
  -- `p₀` has invoked in `a 1`
  have hops1 : opsOf (a 1) X.p₀ ≠ [] := by
    have := (hβgood 0).opsOf_ext1_p₀_ne_nil
    rwa [ext1_of_some (hℓ 0), ← hstep] at this
  set n₀ := (a 1).length
  have hpre : ∀ m, e.pre m = (a m).take m := fun m => e.pre_eq_take (hlen m) (hlbl m)
  have hgpre : ∀ m, X.Good (e.pre m) := fun m => by
    rw [hpre]; exact (hbiv' m).good.of_prefix (List.take_prefix _ _)
  obtain ⟨N₁, hN₁⟩ := X.wf e hadm X.p₀ n₀ (by
    intro m hm
    have hcfg : X.cfg (e.pre m) = e.cfg m := by
      have := (hgpre m).run; rw [e.run_pre] at this; exact (Option.some.inj this).symm
    rw [← hcfg]
    apply (hgpre m).pend_p₀
    · have hp : a 1 <+: e.pre m := by
        rw [hpre]
        exact prefix_take_of_prefix (hmono' 1 m (by have := hlen 1; omega)) hm
      obtain ⟨t, ht⟩ := hp
      rw [← ht, opsOf_append]; simp [hops1]
    · have hp : e.pre m <+: a m := by rw [hpre]; exact List.take_prefix _ _
      obtain ⟨t, ht⟩ := hp
      have := (hbiv' m).resps_nil
      rw [← ht, respsOf_append] at this
      exact List.append_eq_nil_iff.1 this |>.1)
  -- `p₀`'s label in `a (k + 1)` is an internal step, beyond position `N₁`
  set k := N₁ + n₀ + 1
  have hpendk : (X.cfg (β k)).pend X.p₀ ≠ none := by
    apply (hβgood k).pend_p₀ _ (hβr k)
    obtain ⟨t, ht⟩ := (hmono' 1 k (by omega)).trans (hβpre k)
    rw [← ht, opsOf_append]; simp [hops1]
  have htau : ℓ k = .tau X.p₀ := by
    have h1 := hℓ k
    rw [nl_of_pend hpendk] at h1
    have h2 := Option.some.inj h1
    unfold nextLabel at h2
    split at h2
    · exact h2.symm
    · exfalso
      have := (hbiv' (k + 1)).resps_nil
      rw [hstep, respsOf_append, ← h2] at this
      simp at this
  have hidx : e.lbl (β k).length = .tau X.p₀ := by
    rw [hlbl (k + 1) (β k).length (by rw [hstep]; simp)]
    simp only [hstep, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton,
      htau]
  exact hN₁ (β k).length (by have := hlenβ k; have := hlen k; omega) hidx

/-- **Lemma 10 of [ACHP18].** A wait-free linearizable implementation of `n`-LLAA (`n ≥ 2`) has a
critical execution. -/
theorem exists_critical {p₁ : P} (hp₁ : p₁ ≠ X.p₀) :
    ∃ α v q v', X.Critical α v q v' := by
  obtain ⟨α, hbiv, hall⟩ := exists_biv_univ (biv_nil hp₁)
  have hα := hbiv.good
  obtain ⟨v, hv⟩ := hall [] (by simp)
  simp only [List.nil_append] at hv
  -- a value `v' ≠ v` that `α` is potent for
  obtain ⟨v', hv'v, hv'⟩ : ∃ v', v' ≠ v ∧ X.Potent α v' := by
    obtain ⟨w₁, w₂, hne, h1, h2⟩ := hbiv
    by_cases h : w₁ = v
    · exact ⟨w₂, fun h' => hne (h.trans h'.symm), h2⟩
    · exact ⟨w₁, h, h1⟩
  obtain ⟨βv, hβv, hrv⟩ := hv'
  have hτ := hβv.ext_map_proc
  set τ := βv.map Label.proc
  -- `p₀` takes a step in `βv`
  have hp₀τ : X.p₀ ∈ τ := by
    by_contra hn
    have := respsOf_ext_of_not_mem (X := X) (α := α) hn
    rw [hτ, hrv, hbiv.resps_nil] at this; simp at this
  obtain ⟨σ₁, τ₂, hτsplit, hσ₁⟩ := exists_first_split hp₀τ
  -- `p₀(C₁)` is `v'`-univalent, where `C₁` is reached by `σ₁`
  obtain ⟨w₁, hw₁⟩ := hall σ₁ hσ₁
  have hw₁v' : w₁ = v' := by
    have hpot : X.Potent (X.ext α (σ₁ ++ [X.p₀])) v' := by
      have : X.ext α τ = X.ext α (σ₁ ++ [X.p₀]) ++ X.extL (X.ext α (σ₁ ++ [X.p₀])) τ₂ := by
        rw [← ext_eq_append, ← ext_append, hτsplit]; simp
      exact Potent.of_append (β := X.extL (X.ext α (σ₁ ++ [X.p₀])) τ₂)
        ⟨[], by rw [List.append_nil, ← this, hτ]; exact hβv, by rw [List.append_nil, ← this, hτ]; exact hrv⟩
    exact (hw₁.2 v' hpot).symm
  subst hw₁v'
  -- the last prefix of `σ₁` after which `p₀`'s step is `v`-univalent
  set Pr : ℕ → Prop := fun j => X.Univ (X.ext α (σ₁.take j ++ [X.p₀])) v with hPr
  have hP0 : Pr 0 := by simpa [hPr] using hv
  have hPn : ¬ Pr σ₁.length := by
    intro h
    simp only [hPr, List.take_length] at h
    exact hv'v (hw₁.unique h)
  classical
  have hex : ∃ j, ¬ Pr j := ⟨_, hPn⟩
  set j₀ := Nat.find hex
  have hj₀ : ¬ Pr j₀ := Nat.find_spec hex
  have hj₀pos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h] at hj₀; exact absurd hP0 hj₀
    · exact h
  obtain ⟨j, hj⟩ : ∃ j, j₀ = j + 1 := ⟨j₀ - 1, by omega⟩
  have hPj : Pr j := by
    have := Nat.find_min hex (show j < j₀ by omega); simpa using this
  have hjlt : j < σ₁.length := by
    by_contra hge
    push Not at hge
    have : Pr j₀ := by
      simp only [hPr] at hPj ⊢
      rw [List.take_of_length_le (by omega)]
      rwa [List.take_of_length_le hge] at hPj
    exact hj₀ this
  set q := σ₁[j]
  have hq : q ≠ X.p₀ := fun h => hσ₁ (h ▸ List.getElem_mem hjlt)
  have htake : σ₁.take (j + 1) = σ₁.take j ++ [q] := List.take_succ_eq_append_getElem hjlt
  obtain ⟨w, hw⟩ := hall (σ₁.take (j + 1)) (fun h => hσ₁ (List.mem_of_mem_take h))
  have hwv : v ≠ w := by
    intro h; subst h
    apply hj₀; rw [hj]; exact hw
  refine ⟨X.ext α (σ₁.take j), v, q, w, hα.ext _, hq, hwv, ?_, ?_, ?_⟩
  · rw [← ext_singleton, ← ext_append]; exact hPj
  · rw [← ext_append, show σ₁.take j ++ [q, X.p₀] = σ₁.take (j + 1) ++ [X.p₀] by
      rw [htake]; simp]
    exact hw
  · intro σ hσ
    obtain ⟨w', hw'⟩ := hall (σ₁.take j ++ σ) (by
      simp only [List.mem_append, not_or]
      exact ⟨fun h => hσ₁ (List.mem_of_mem_take h), hσ⟩)
    exact ⟨w', by rw [← ext_append]; simpa using hw'⟩

end Ctx

end Podc.LockFreeVsWaitFree
