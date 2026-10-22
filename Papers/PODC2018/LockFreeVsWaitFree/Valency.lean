import Papers.PODC2018.LockFreeVsWaitFree.Basic

/-!
# Solo runs, valency and the convergence bound (Section 5 of [ACHP18])

* `Ctx.exists_infExec_of_chain` — limits of chains of good executions are infinite admissible
  executions (to which wait-freedom applies).
* `Ctx.Good.exists_resps` — **solo runs**: by wait-freedom, a process `q ≠ p₀` running solo
  completes as many operations as we like, and `p₀` running solo completes its operation.
* `Ctx.Potent`, `Ctx.Univ`, `Ctx.Biv` — valency (paper: `v`-potent, `v`-univalent, bivalent);
  `Ctx.Good.exists_potent`, `Ctx.Univ.ext`, `Ctx.Univ.potent_of_agree` (an execution that `p₀`
  cannot distinguish from a `v`-univalent one is `v`-potent).
* `Ctx.close_of_univ` — **the convergence bound** used twice in the proof of Theorem 11: if `α`
  is `v`-univalent and some `q ≠ p₀` returned `x` in its `m`-th operation, `m ≥ k + 2`
  (0-based), then `|x - v| < 1/2^(k+1)`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeVsWaitFree

open Cslib SharedMemory Impl

namespace Ctx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] {X : Ctx P ι L B}

/-! ### Infinite executions from chains of good executions -/

/-- A chain of good executions of unbounded length has an infinite admissible limit. -/
lemma exists_infExec_of_chain (E : ℕ → List (LLabel P)) (hmono : ∀ k, E k <+: E (k + 1))
    (hlen : ∀ k, k ≤ (E k).length) (hgood : ∀ k, X.Good (E k)) :
    ∃ e : X.I.InfExec, (∀ t, Adm X.p₀ (e.pre t)) ∧
      (∀ k n (hn : n < (E k).length), e.lbl n = (E k)[n]) ∧
      ∀ k, e.cfg (E k).length = X.cfg (E k) := by
  obtain ⟨e, hlbl, hrun⟩ := X.I.exists_infExec_of_chain E hmono hlen (fun k => (hgood k).1)
  refine ⟨e, fun t => ?_, hlbl, fun k => ?_⟩
  · rw [e.pre_eq_take (hlen t) (hlbl t)]
    exact ((hgood t).of_prefix (List.take_prefix _ _)).2
  · have := hrun k (E k).length le_rfl
    rw [List.take_length, (hgood k).run] at this
    exact (Option.some.inj this).symm

/-! ### Solo runs -/

lemma ext_replicate_succ (α : List (LLabel P)) (q : P) (N : ℕ) :
    X.ext α (List.replicate (N + 1) q) = X.ext1 (X.ext α (List.replicate N q)) q := by
  rw [List.replicate_succ', ext_concat]

-- CSLib candidate
/-- A bounded monotone sequence of naturals is eventually constant. -/
lemma eventually_const_of_mono_lt {c : ℕ → ℕ} (hmono : Monotone c) {K : ℕ} (hK : ∀ N, c N < K) :
    ∃ N₀, ∀ N ≥ N₀, c N = c N₀ := by
  by_contra h
  push Not at h
  have key : ∀ j, ∃ N, j ≤ c N := by
    intro j
    induction j with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨N', hN', hne⟩ := h N
      exact ⟨N', by have := hmono hN'; omega⟩
  obtain ⟨N, hN⟩ := key K
  exact absurd (hK N) (by omega)

/-- **Solo runs.** By wait-freedom, a process running solo completes any number of operations
(`p₀` completes its single operation). -/
lemma Good.exists_resps {α : List (LLabel P)} (hα : X.Good α) (q : P) (K : ℕ)
    (hK : q = X.p₀ → K ≤ 1) :
    ∃ N, K ≤ (respsOf (X.ext α (List.replicate N q)) q).length := by
  by_contra H
  push Not at H
  set E : ℕ → List (LLabel P) := fun N => X.ext α (List.replicate N q) with hE
  have hgood : ∀ N, X.Good (E N) := fun N => hα.ext _
  -- the next label of `q` always exists
  have hsome : ∀ N, ∃ ℓ, X.nl (E N) q = some ℓ := by
    intro N
    by_cases hq : q = X.p₀
    · subst hq
      have hK1 := hK rfl
      have hr : respsOf (E N) X.p₀ = [] := by
        have : (respsOf (E N) X.p₀).length < K := H N
        rw [← List.length_eq_zero_iff]; omega
      unfold nl
      split_ifs with h1 h2
      · exfalso
        rcases (hgood N).p₀_counts with ⟨-, b⟩ | ⟨a, -, -⟩
        · rw [hr] at b; exact h2.2 (List.length_eq_zero_iff.1 b)
        · exact a h1
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact Option.isSome_iff_exists.1 (nl_isSome_of_ne hq)
  choose ℓ hℓ using hsome
  have hsucc : ∀ N, E (N + 1) = E N ++ [ℓ N] := fun N => by
    simp only [hE]; rw [ext_replicate_succ, ext1_of_some (hℓ N)]
  have hlen : ∀ N, (E N).length = α.length + N := by
    intro N; induction N with
    | zero => simp [hE]
    | succ N ih => rw [hsucc, List.length_append, ih]; simp; omega
  have hmono : ∀ N, E N <+: E (N + 1) := fun N => by rw [hsucc]; exact List.prefix_append _ _
  obtain ⟨e, hadm, hlbl, hcfg⟩ := exists_infExec_of_chain E hmono
    (fun N => by rw [hlen]; omega) hgood
  -- the number of responses of `q` is eventually constant
  set c : ℕ → ℕ := fun N => (respsOf (E N) q).length with hc
  have hcmono : Monotone c := by
    apply monotone_nat_of_le_succ
    intro N; simp only [hc, hsucc, respsOf_append, List.length_append]; omega
  obtain ⟨N₀, hN₀⟩ := eventually_const_of_mono_lt hcmono H
  have hproc : ∀ N, (ℓ N).proc = q := fun N => nl_proc (hℓ N)
  -- no response of `q` after `N₀`
  have hnoret : ∀ N ≥ N₀, ∀ r, ℓ N ≠ .ret q r := by
    intro N hN r hr
    have := hN₀ (N + 1) (by omega)
    have h2 := hN₀ N hN
    simp only [hc, hsucc, respsOf_append, List.length_append, hr, respsOf_cons,
      Label.retOf_ret, ite_true, Option.toList_some, respsOf_nil] at this h2
    simp at this; omega
  -- `q` is pending from `N₀ + 1` on, and its labels are internal steps
  have hpend : ∀ N ≥ N₀ + 1, (X.cfg (E N)).pend q ≠ none := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      have hs := ((hgood N₀).nl_step (hℓ N₀)).1
      rw [← hsucc] at hs
      by_cases hp : (X.cfg (E N₀)).pend q = none
      · have hl : ℓ N₀ = .inv q (side X.p₀ q) := by
          have := hℓ N₀
          unfold nl at this
          split_ifs at this with h2
          exact (Option.some.inj this).symm
        rw [hl] at hs
        rw [(step_inv hs).2.2.1]; simp
      · cases hl : ℓ N₀ with
        | inv p o =>
          have := hproc N₀; rw [hl] at this; subst this
          rw [hl] at hs; exact absurd (step_inv hs).1 hp
        | ret p r =>
          have := hproc N₀; rw [hl] at this; subst this
          exact absurd hl (hnoret N₀ le_rfl r)
        | tau p =>
          have := hproc N₀; rw [hl] at this; subst this
          rw [hl] at hs; rw [(step_tau hs).2.1]; exact hp
    | succ N hN ih =>
      have hs := ((hgood N).nl_step (hℓ N)).1
      rw [← hsucc] at hs
      cases hl : ℓ N with
      | inv p o =>
        have := hproc N; rw [hl] at this; subst this
        rw [hl] at hs; exact absurd (step_inv hs).1 ih
      | ret p r =>
        have := hproc N; rw [hl] at this; subst this
        exact absurd hl (hnoret N (by omega) r)
      | tau p =>
        have := hproc N; rw [hl] at this; subst this
        rw [hl] at hs; rw [(step_tau hs).2.1]; exact ih
  have htau : ∀ N ≥ N₀ + 1, ℓ N = .tau q := by
    intro N hN
    have h1 := hℓ N
    rw [nl_of_pend (hpend N hN)] at h1
    have h2 := Option.some.inj h1
    unfold nextLabel at h2
    split at h2
    · exact h2.symm
    · exact absurd h2.symm (hnoret N (by omega) _)
  have hlbl' : ∀ N, e.lbl (α.length + N) = ℓ N := by
    intro N
    have := hlbl (N + 1) (α.length + N) (by rw [hlen]; omega)
    rw [this]
    simp only [hsucc]
    rw [List.getElem_append_right (by rw [hlen])]
    simp [hlen]
  obtain ⟨N₁, hN₁⟩ := X.wf e hadm q (α.length + (N₀ + 1)) (by
    intro m hm
    obtain ⟨N, rfl⟩ : ∃ N, m = α.length + N := ⟨m - α.length, by omega⟩
    have := hcfg N
    rw [hlen] at this
    rw [this]; exact hpend N (by omega))
  exact hN₁ (α.length + (N₁ + N₀ + 1)) (by omega) (by rw [hlbl']; exact htau _ (by omega))

/-- `p₀` running solo completes its operation. -/
lemma Good.exists_p₀_resp {α : List (LLabel P)} (hα : X.Good α) :
    ∃ N v, respsOf (X.ext α (List.replicate N X.p₀)) X.p₀ = [v] := by
  obtain ⟨N, hN⟩ := hα.exists_resps X.p₀ 1 (fun _ => le_rfl)
  have h1 := (hα.ext (List.replicate N X.p₀)).resps_le_one
  obtain ⟨v, hv⟩ : ∃ v, respsOf (X.ext α (List.replicate N X.p₀)) X.p₀ = [v] :=
    List.length_eq_one_iff.1 (by omega)
  exact ⟨N, v, hv⟩

/-- A process `q ≠ p₀` running solo completes any number of operations within the solo run. -/
lemma Good.exists_resps_extL {α : List (LLabel P)} (hα : X.Good α) {q : P} (hq : q ≠ X.p₀)
    (K : ℕ) : ∃ N, K ≤ (respsOf (X.extL α (List.replicate N q)) q).length := by
  obtain ⟨N, hN⟩ := hα.exists_resps q (K + (respsOf α q).length) (fun h => absurd h hq)
  refine ⟨N, ?_⟩
  rw [ext_eq_append, respsOf_append, List.length_append] at hN
  omega

/-! ### Valency -/

variable (X)

/-- `α` is `v`-potent: some admissible extension completes `p₀`'s operation with output `v`. -/
def Potent (α : List (LLabel P)) (v : ℝ) : Prop :=
  ∃ β, X.Good (α ++ β) ∧ respsOf (α ++ β) X.p₀ = [v]

/-- `α` is `v`-univalent. -/
def Univ (α : List (LLabel P)) (v : ℝ) : Prop := X.Potent α v ∧ ∀ w, X.Potent α w → w = v

/-- `α` is bivalent. -/
def Biv (α : List (LLabel P)) : Prop := ∃ v w, v ≠ w ∧ X.Potent α v ∧ X.Potent α w

variable {X}

lemma Potent.good {α : List (LLabel P)} {v : ℝ} (h : X.Potent α v) : X.Good α := by
  obtain ⟨β, hβ, -⟩ := h; exact hβ.of_append

lemma Univ.good {α : List (LLabel P)} {v : ℝ} (h : X.Univ α v) : X.Good α := h.1.good

lemma Potent.of_append {α β : List (LLabel P)} {v : ℝ} (h : X.Potent (α ++ β) v) :
    X.Potent α v := by
  obtain ⟨γ, h1, h2⟩ := h
  exact ⟨β ++ γ, by simpa using h1, by simpa using h2⟩

/-- Every good execution is potent for some value (by wait-freedom). -/
lemma Good.exists_potent {α : List (LLabel P)} (hα : X.Good α) : ∃ v, X.Potent α v := by
  obtain ⟨N, v, hv⟩ := hα.exists_p₀_resp
  exact ⟨v, X.extL α (List.replicate N X.p₀), hα.ext _, hv⟩

/-- Good extensions of a `v`-univalent execution are `v`-univalent. -/
lemma Univ.ext {α β : List (LLabel P)} {v : ℝ} (h : X.Univ α v) (hβ : X.Good (α ++ β)) :
    X.Univ (α ++ β) v := by
  obtain ⟨w, hw⟩ := hβ.exists_potent
  have : w = v := h.2 w hw.of_append
  subst this
  exact ⟨hw, fun w' hw' => h.2 w' hw'.of_append⟩

lemma Univ.ext' {α β : List (LLabel P)} {v : ℝ} (h : X.Univ α v) (hp : α <+: β) (hβ : X.Good β) :
    X.Univ β v := by
  obtain ⟨γ, rfl⟩ := hp; exact h.ext hβ

lemma Univ.unique {α : List (LLabel P)} {v w : ℝ} (h : X.Univ α v) (hw : X.Univ α w) : v = w :=
  (h.2 w hw.1).symm

/-- A good execution that `p₀` cannot distinguish from a `v`-univalent one (same memory, same
state of `p₀`, same operations and responses of `p₀`) is `v`-potent. -/
lemma Univ.potent_of_agree {α α' : List (LLabel P)} {v : ℝ} (h : X.Univ α v) (hα' : X.Good α')
    (hag : Agree X.p₀ (X.cfg α) (X.cfg α')) (hops : opsOf α X.p₀ = opsOf α' X.p₀)
    (hres : respsOf α X.p₀ = respsOf α' X.p₀) : X.Potent α' v := by
  have hα := h.good
  obtain ⟨N, w, hw⟩ := hα.exists_p₀_resp
  have hwv : w = v := h.2 w ⟨_, hα.ext _, hw⟩
  subst hwv
  obtain ⟨e1, -, -⟩ := transfer (Q := {X.p₀}) hα hα'
    ⟨hag.mem, fun q hq => by rw [hq]; exact hag.loc, fun q hq => by rw [hq]; exact hag.pend⟩
    (fun _ => by rw [hops]) (σ := List.replicate N X.p₀)
    (fun p hp => by rw [List.eq_of_mem_replicate hp]; rfl)
  refine ⟨X.extL α' (List.replicate N X.p₀), hα'.ext _, ?_⟩
  rw [ext_eq_append, respsOf_append] at hw
  rw [respsOf_append, ← e1, ← hres, hw]

/-- An execution in which `p₀` has returned is univalent for its output. -/
lemma Good.univ_of_resps {α : List (LLabel P)} (hα : X.Good α) {v : ℝ}
    (h : respsOf α X.p₀ = [v]) : X.Univ α v := by
  refine ⟨⟨[], by simpa using hα, by simpa using h⟩, fun w ⟨β, _, hβ⟩ => ?_⟩
  rw [respsOf_append, h] at hβ
  have := congrArg List.head? hβ
  simp at this; exact this.symm

lemma Biv.good {α : List (LLabel P)} (h : X.Biv α) : X.Good α := by
  obtain ⟨v, w, -, hv, -⟩ := h; exact hv.good

/-- In a bivalent execution, `p₀` has not returned. -/
lemma Biv.resps_nil {α : List (LLabel P)} (h : X.Biv α) : respsOf α X.p₀ = [] := by
  obtain ⟨v, w, hvw, hv, hw⟩ := h
  have h1 := hv.good.resps_le_one
  rcases hr : respsOf α X.p₀ with _ | ⟨r, l⟩
  · rfl
  · exfalso
    have hl : l = [] := by rw [hr] at h1; simpa using h1
    subst hl
    have hu := hv.good.univ_of_resps hr
    exact hvw ((hu.2 v hv).trans (hu.2 w hw).symm)

/-! ### The convergence bound -/

-- CSLib candidate
/-- In a duplicate-free list, the elements that come before the element at position `i` are
at most `i`. -/
lemma le_idx_of_sublist {Y : Type} {M : List Y} (hnd : M.Nodup) {i : ℕ} (hi : i < M.length)
    {b : Y} (hb : M[i] = b) (S : List Y) (hS : S.Nodup) (hsub : ∀ a ∈ S, [a, b].Sublist M) :
    S.length ≤ i := by
  have hM : M = M.take i ++ b :: M.drop (i + 1) := by
    rw [← hb, List.getElem_cons_drop, List.take_append_drop]
  have hsubset : S ⊆ M.take i := by
    intro a ha
    have h := hsub a ha
    rw [hM] at h hnd
    exact mem_left_of_sublist_pair hnd h
  have := hS.length_le_of_subset hsubset
  simpa [List.length_take, hi.le] using this

/-- **The convergence bound** (proof of Theorem 11 of [ACHP18]). If `α` is `v`-univalent and
some process `q ≠ p₀` returned `x` in its `m`-th operation (`0`-based) with `k + 2 ≤ m`, then
`|x - v| < 1/2^(k+1)`. (In any linearization of a completion of `α`, `q`'s operation is preceded
by its `m` earlier operations, and `p₀`'s operation, with output `v`, is the only one of side
`0`.) -/
theorem close_of_univ {α : List (LLabel P)} {v : ℝ} (hu : X.Univ α v) {q : P} (hq : q ≠ X.p₀)
    {m k : ℕ} {x : ℝ} (hx : respOf α (q, m) = some x) (hk : k + 2 ≤ m) :
    |x - v| < (1 / 2 : ℝ) ^ (k + 1) := by
  have hα := hu.good
  obtain ⟨N, w, hw⟩ := hα.exists_p₀_resp
  have hwv : w = v := hu.2 w ⟨_, hα.ext _, hw⟩
  rw [hwv] at hw
  set γ := X.ext α (List.replicate N X.p₀)
  have hγ : X.Good γ := hα.ext _
  have hxγ : respOf γ (q, m) = some x := by
    have hc : Completed α (q, m) := by
      simp only [Completed]; simp only [respOf] at hx
      exact (List.getElem?_eq_some_iff.1 hx).1
    rw [show γ = α ++ X.extL α (List.replicate N X.p₀) from rfl,
      respOf_append_of_completed hc, hx]
  have hcq : ∀ j ≤ m, Completed γ (q, j) := by
    intro j hj; simp only [Completed]; simp only [respOf] at hxγ
    have := (List.getElem?_eq_some_iff.1 hxγ).1; omega
  have hc0 : Completed γ (X.p₀, 0) := by simp [Completed, hw]
  have hwf : WellFormed γ := hγ.1.wellFormed
  obtain ⟨Lin, hL⟩ := X.lin γ hγ.1 hγ.2
  -- the side of every linearized operation
  have hside : ∀ y ∈ Lin, y.2.1 = side X.p₀ y.1.1 := by
    intro y hy
    have h1 := hL.op_eq y hy
    simp only [opOf] at h1
    exact hγ.2.side _ _ (List.mem_of_getElem? h1)
  -- the only operation of `p₀` is `(p₀, 0)`
  have hp₀ : ∀ y ∈ Lin, y.1.1 = X.p₀ → y.1.2 = 0 := by
    intro y hy hy0
    have h1 := hL.op_eq y hy
    simp only [opOf] at h1
    have h2 := (List.getElem?_eq_some_iff.1 h1).1
    have := hγ.2.once; rw [hy0] at h2; omega
  set M := Lin.map Prod.fst with hM
  have hnd : M.Nodup := hL.nodup
  have hmemM : ∀ a, Completed γ a → a ∈ M := hL.complete
  obtain ⟨j, hj, hjM⟩ := List.getElem_of_mem (hmemM _ hc0)
  obtain ⟨i, hi, hiM⟩ := List.getElem_of_mem (hmemM _ (hcq m le_rfl))
  -- `q`'s operation is preceded by its `m` earlier operations
  have hidx : m ≤ i := by
    have := le_idx_of_sublist hnd hi hiM ((List.range m).map fun t => (q, t))
      (List.nodup_range.map fun a b h => by simpa using h) (by
        intro a ha
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
        rw [List.mem_range] at ht
        refine hL.realtime _ _ (hwf.precedes_of_lt ht ?_) (hmemM _ (hcq m le_rfl))
        have := hcq m le_rfl; simp only [Completed, Invoked] at this ⊢
        have := (hwf.counts (β := γ) (γ := []) (by simp) q).1; omega)
    simpa using this
  have hjL : j < Lin.length := by simpa [hM] using hj
  have hiL : i < Lin.length := by simpa [hM] using hi
  have hj' : (Lin.map Prod.snd)[j]? = some (0, v) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hjL]
    have h1 : Lin[j].1 = (X.p₀, 0) := by simpa [hM] using hjM
    have hs := hside _ (List.getElem_mem hjL)
    have hr := hL.resp_eq _ (List.getElem_mem hjL) v (by rw [h1]; simp [respOf, hw])
    simp only [Option.map_some, Option.some.injEq]
    rw [h1] at hs; simp only [side, ite_true] at hs
    exact Prod.ext hs hr
  have hi' : (Lin.map Prod.snd)[i]? = some (1, x) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hiL]
    have h1 : Lin[i].1 = (q, m) := by simpa [hM] using hiM
    have hs := hside _ (List.getElem_mem hiL)
    have hr := hL.resp_eq _ (List.getElem_mem hiL) x (by rw [h1]; exact hxγ)
    simp only [Option.map_some, Option.some.injEq]
    rw [h1] at hs; simp only [side, hq, ite_false] at hs
    exact Prod.ext hs hr
  have hone : ∀ t a, (Lin.map Prod.snd)[t]? = some a → t ≠ j → a.1 = 1 := by
    intro t a ha htj
    rw [List.getElem?_map] at ha
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 ha
    obtain ⟨ht, hyt⟩ := List.getElem?_eq_some_iff.1 hy
    have hymem : y ∈ Lin := hyt ▸ List.getElem_mem ht
    rw [hside y hymem]
    by_cases hy0 : y.1.1 = X.p₀
    · exfalso
      have hy1 : y.1 = (X.p₀, 0) := Prod.ext hy0 (hp₀ y hymem hy0)
      have : M[t]'(by simpa [hM] using ht) = M[j] := by
        simp only [hM, List.getElem_map, hyt, hy1]
        exact (by simpa [hM] using hjM : Lin[j].1 = _).symm
      exact htj ((List.Nodup.getElem_inj_iff hnd).1 this)
    · simp [side, hy0]
  exact close_of_legal (k := k) hL.legal hj' hone hi' (by omega)

end Ctx

end Podc.LockFreeVsWaitFree
