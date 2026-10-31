import Papers.PODC2022.MultipleSpending.Broadcast

/-!
# The lower bound of Theorem 5.1, repaired (§5.1)

The paper's gluing argument, made precise in the asynchronous Byzantine broadcast model
`Cslib.Byzantine.AsyncBroadcast`.

* `exists_exec_of_reachable`: every reachable state lies on an infinite execution that stutters
  in it forever.
* `Mirror R γ₀ τ γ` and `Mirror.reach` (**replay lemma**): a run `τ₀ →* τ` without corruption of
  the members of `R` can be replayed, restricted to the processes of `R`, on top of any state `γ₀`
  in which those processes have not acted yet and are uncorrupted, provided every process outside
  `R` from which a member of `R` receives a message is corrupted in `γ₀`: sends and decisions of
  members of `R` are replayed as such, receptions from members of `R` as deliveries and
  receptions from outside `R` as Byzantine injections; all other steps are dropped.
* `IsKCB.dec_eq_of_reachable`: in a failure-free run with source value `m`, every decision is `m`
  (Integrity, applied to the stuttering execution; needs `∅ ∈ F`).
* `lower_bound`: if the source lies in `F ∈ F` and `C` is independent in `G_{F,S}`, then
  `|C| ≤ k` for every `k`-CB algorithm with (per-value) Local Progress.
* `srcInconsistencyNumber_le`: `λ_s ≤ k` (the repaired Theorem 5.1).
* `lower_bound_needs_empty_mem`: the hypothesis `∅ ∈ F` (a consequence of the paper's standing
  assumption that `F` is inclusion-closed) cannot be dropped.
-/

namespace Podc.MultipleSpending

open Cslib.Byzantine.AsyncBroadcast Finset

/-! ### Replaying a run on a subset of processes -/

section Replay

variable {P M I O : Type*} {A : Protocol P M I O} {x x' : P → I} {k : FaultKind} {t t' : ℕ}

-- CSLib candidate
/-- `γ` mirrors `τ` on the processes of `R`: their receptions, broadcasts and decisions are those
of `τ`; the receptions, broadcasts and decisions of the other processes, and the corrupted set,
are those of `γ₀`. -/
structure Mirror (R : Set P) (γ₀ τ γ : State P M O) : Prop where
  bad : γ.bad = γ₀.bad
  rcv_in : ∀ q ∈ R, ∀ r m, (q, r, m) ∈ γ.rcv ↔ (q, r, m) ∈ τ.rcv
  sent_in : ∀ q ∈ R, ∀ m, (q, m) ∈ γ.sent ↔ (q, m) ∈ τ.sent
  dec_in : ∀ q ∈ R, γ.dec q = τ.dec q
  rcv_out : ∀ q ∉ R, ∀ r m, (q, r, m) ∈ γ.rcv ↔ (q, r, m) ∈ γ₀.rcv
  sent_out : ∀ q ∉ R, ∀ m, (q, m) ∈ γ.sent ↔ (q, m) ∈ γ₀.sent
  dec_out : ∀ q ∉ R, γ.dec q = γ₀.dec q

namespace Mirror

variable {R : Set P} {γ₀ τ γ : State P M O}

theorem inbox_eq (h : Mirror R γ₀ τ γ) {q : P} (hq : q ∈ R) : γ.inbox q = τ.inbox q := by
  funext r; ext m; exact h.rcv_in q hq r m

theorem out_eq (h : Mirror R γ₀ τ γ) {q : P} (hq : q ∈ R) : γ.out q = τ.out q := by
  ext m; exact h.sent_in q hq m

theorem insert_rcv (h : Mirror R γ₀ τ γ) {q r : P} {m : M} (hq : q ∈ R) :
    Mirror R γ₀ { τ with rcv := insert (q, r, m) τ.rcv }
      { γ with rcv := insert (q, r, m) γ.rcv } where
  bad := h.bad
  rcv_in q' hq' r' m' := by simp only [Set.mem_insert_iff, h.rcv_in q' hq' r' m']
  sent_in := h.sent_in
  dec_in := h.dec_in
  rcv_out q' hq' r' m' := by
    have : q' ≠ q := fun e => hq' (e ▸ hq)
    simp [Set.mem_insert_iff, this, h.rcv_out q' hq' r' m']
  sent_out := h.sent_out
  dec_out := h.dec_out

theorem insert_rcv_skip (h : Mirror R γ₀ τ γ) {q r : P} {m : M} (hq : q ∉ R) :
    Mirror R γ₀ { τ with rcv := insert (q, r, m) τ.rcv } γ where
  bad := h.bad
  rcv_in q' hq' r' m' := by
    have : q' ≠ q := fun e => hq (e ▸ hq')
    simp [Set.mem_insert_iff, this, h.rcv_in q' hq' r' m']
  sent_in := h.sent_in
  dec_in := h.dec_in
  rcv_out := h.rcv_out
  sent_out := h.sent_out
  dec_out := h.dec_out

theorem insert_sent (h : Mirror R γ₀ τ γ) {p : P} {m : M} (hp : p ∈ R) :
    Mirror R γ₀ { τ with sent := insert (p, m) τ.sent }
      { γ with sent := insert (p, m) γ.sent } where
  bad := h.bad
  rcv_in := h.rcv_in
  sent_in q' hq' m' := by simp only [Set.mem_insert_iff, h.sent_in q' hq' m']
  dec_in := h.dec_in
  rcv_out := h.rcv_out
  sent_out q' hq' m' := by
    have : q' ≠ p := fun e => hq' (e ▸ hp)
    simp [Set.mem_insert_iff, this, h.sent_out q' hq' m']
  dec_out := h.dec_out

theorem insert_sent_skip (h : Mirror R γ₀ τ γ) {p : P} {m : M} (hp : p ∉ R) :
    Mirror R γ₀ { τ with sent := insert (p, m) τ.sent } γ where
  bad := h.bad
  rcv_in := h.rcv_in
  sent_in q' hq' m' := by
    have : q' ≠ p := fun e => hp (e ▸ hq')
    simp [Set.mem_insert_iff, this, h.sent_in q' hq' m']
  dec_in := h.dec_in
  rcv_out := h.rcv_out
  sent_out := h.sent_out
  dec_out := h.dec_out

theorem set_bad (h : Mirror R γ₀ τ γ) (B : Set P) : Mirror R γ₀ { τ with bad := B } γ where
  bad := h.bad
  rcv_in := h.rcv_in
  sent_in := h.sent_in
  dec_in := h.dec_in
  rcv_out := h.rcv_out
  sent_out := h.sent_out
  dec_out := h.dec_out

end Mirror

variable [DecidableEq P]

-- CSLib candidate
/-- Every reachable state lies on an execution that stutters in it forever. -/
theorem exists_exec_of_reachable {σ : State P M O} (h : Reachable A x k t σ) :
    ∃ E : Exec A x k t, ∃ N, ∀ i, N ≤ i → E.σ i = σ := by
  unfold Reachable at h
  induction h with
  | refl => exact ⟨⟨fun _ => State.init, rfl, fun _ => Or.inr rfl⟩, 0, fun _ _ => rfl⟩
  | @tail σ₁ σ₂ _ hst ih =>
    obtain ⟨E, N, hE⟩ := ih
    refine ⟨⟨fun i => if i ≤ N then E.σ i else σ₂, by simp [E.zero], fun i => ?_⟩, N + 1,
      fun i hi => ?_⟩
    · rcases lt_trichotomy i N with hi | rfl | hi
      · simp only [show i ≤ N by omega, show i + 1 ≤ N by omega, ↓reduceIte]
        exact E.step i
      · simp only [le_refl, show ¬ (i + 1 ≤ i) by omega, ↓reduceIte]
        left; rw [hE i le_rfl]; exact hst
      · right; simp [show ¬ i ≤ N by omega, show ¬ (i + 1 ≤ N) by omega]
    · simp only [show ¬ i ≤ N by omega, ↓reduceIte]

-- CSLib candidate
/-- In an execution that eventually stutters in `σ`, the correct processes are those not
corrupted in `σ`. -/
theorem correct_iff_of_stutter {E : Exec A x k t} {σ : State P M O} {N : ℕ}
    (hE : ∀ i, N ≤ i → E.σ i = σ) (p : P) : E.Correct p ↔ p ∉ σ.bad := by
  constructor
  · intro h; rw [← hE N le_rfl]; exact h N
  · intro h i hi
    exact h (by rw [← hE (i + N) (by omega)]; exact E.bad_mono (by omega) hi)

namespace Mirror

variable {R : Set P} {γ₀ τ γ : State P M O}

theorem update_dec (h : Mirror R γ₀ τ γ) {p : P} {o : O} (hp : p ∈ R) :
    Mirror R γ₀ { τ with dec := Function.update τ.dec p (some o) }
      { γ with dec := Function.update γ.dec p (some o) } where
  bad := h.bad
  rcv_in := h.rcv_in
  sent_in := h.sent_in
  dec_in q' hq' := by
    by_cases e : q' = p
    · subst e; simp
    · simp [Function.update_of_ne e, h.dec_in q' hq']
  rcv_out := h.rcv_out
  sent_out := h.sent_out
  dec_out q' hq' := by
    have : q' ≠ p := fun e => hq' (e ▸ hp)
    simp [Function.update_of_ne this, h.dec_out q' hq']

theorem update_dec_skip (h : Mirror R γ₀ τ γ) {p : P} {o : O} (hp : p ∉ R) :
    Mirror R γ₀ { τ with dec := Function.update τ.dec p (some o) } γ where
  bad := h.bad
  rcv_in := h.rcv_in
  sent_in := h.sent_in
  dec_in q' hq' := by
    have : q' ≠ p := fun e => hp (e ▸ hq')
    simp [Function.update_of_ne this, h.dec_in q' hq']
  rcv_out := h.rcv_out
  sent_out := h.sent_out
  dec_out := h.dec_out

/-- One step of `τ` can be mirrored by at most one (Byzantine) step of `γ`. -/
theorem step (h : Mirror R γ₀ τ γ) {τ' : State P M O} (hst : Step A x k t τ τ')
    (hR : ∀ q ∈ R, q ∉ γ₀.bad) (hx : ∀ q ∈ R, x' q = x q) (hgood : ∀ q ∈ R, q ∉ τ'.bad)
    (hsrc : ∀ q ∈ R, ∀ r m, (q, r, m) ∈ τ'.rcv → r ∉ R → r ∈ γ₀.bad) :
    ∃ γ', Reach A x' .byzantine t' γ γ' ∧ Mirror R γ₀ τ' γ' := by
  cases hst with
  | send p m _ hg =>
    by_cases hpR : p ∈ R
    · refine ⟨_, Relation.ReflTransGen.single (Step.send γ p m ?_ ?_), h.insert_sent hpR⟩
      · rw [h.bad]; exact hR p hpR
      · rw [hx p hpR, h.inbox_eq hpR, h.out_eq hpR]; exact hg
    · exact ⟨γ, .refl, h.insert_sent_skip hpR⟩
  | deliver q r m hs =>
    by_cases hqR : q ∈ R
    · refine ⟨_, Relation.ReflTransGen.single ?_, h.insert_rcv hqR⟩
      by_cases hrR : r ∈ R
      · exact Step.deliver γ q r m ((h.sent_in r hrR m).2 hs)
      · exact Step.inject γ q r m rfl
          (by rw [h.bad]; exact hsrc q hqR r m (Set.mem_insert _ _) hrR)
    · exact ⟨γ, .refl, h.insert_rcv_skip hqR⟩
  | inject q r m _ hb =>
    by_cases hqR : q ∈ R
    · refine ⟨_, Relation.ReflTransGen.single ?_, h.insert_rcv hqR⟩
      by_cases hrR : r ∈ R
      · exact absurd hb (hgood r hrR)
      · exact Step.inject γ q r m rfl
          (by rw [h.bad]; exact hsrc q hqR r m (Set.mem_insert _ _) hrR)
    · exact ⟨γ, .refl, h.insert_rcv_skip hqR⟩
  | decide p o _ hd hg =>
    by_cases hpR : p ∈ R
    · refine ⟨_, Relation.ReflTransGen.single (Step.decide γ p o ?_ ?_ ?_), h.update_dec hpR⟩
      · rw [h.bad]; exact hR p hpR
      · rw [h.dec_in p hpR]; exact hd
      · rw [hx p hpR, h.inbox_eq hpR, h.out_eq hpR]; exact hg
    · exact ⟨γ, .refl, h.update_dec_skip hpR⟩
  | corrupt p _ => exact ⟨γ, .refl, h.set_bad _⟩

-- CSLib candidate
/-- **Replay lemma.** A run `τ₀ →* τ` in which no member of `R` is corrupted can be replayed on
the members of `R` on top of `γ₀` (where they are uncorrupted and have the same inputs), provided
every process outside `R` from which a member of `R` receives a message in `τ` is corrupted in
`γ₀`: receptions from such processes become Byzantine injections. -/
theorem reach {τ₀ : State P M O} (h : Mirror R γ₀ τ₀ γ) {τ : State P M O}
    (hτ : Reach A x k t τ₀ τ) (hR : ∀ q ∈ R, q ∉ γ₀.bad) (hx : ∀ q ∈ R, x' q = x q)
    (hgood : ∀ q ∈ R, q ∉ τ.bad)
    (hsrc : ∀ q ∈ R, ∀ r m, (q, r, m) ∈ τ.rcv → r ∉ R → r ∈ γ₀.bad) :
    ∃ γ', Reach A x' .byzantine t' γ γ' ∧ Mirror R γ₀ τ γ' := by
  induction hτ with
  | refl => exact ⟨γ, .refl, h⟩
  | @tail τ₁ τ₂ _ hst ih =>
    obtain ⟨γ₁, h₁, hm₁⟩ := ih (fun q hq hb => hgood q hq (hst.bad_subset hb))
      (fun q hq r m hm => hsrc q hq r m (hst.rcv_subset hm))
    obtain ⟨γ₂, h₂, hm₂⟩ := hm₁.step hst hR hx hgood hsrc
    exact ⟨γ₂, h₁.trans h₂, hm₂⟩

end Mirror

end Replay

/-! ### The lower bound -/

section LowerBound

variable {P M V : Type*} [Fintype P] [DecidableEq P]

/-- The state in which exactly the processes of `F` are corrupted and nothing else happened. -/
def corrupted (F : Finset P) : State P M V := ⟨∅, ∅, fun _ => none, ↑F⟩

theorem reach_corrupted {I : Type*} {A : Protocol P M I V} {x : P → I} {k : FaultKind}
    (F : Finset P) : Reach A x k (Fintype.card P) State.init (corrupted F) := by
  induction F using Finset.induction_on with
  | empty =>
    show Reach A x k _ State.init ⟨∅, ∅, fun _ => none, ((∅ : Finset P) : Set P)⟩
    rw [Finset.coe_empty]; exact .refl
  | insert a F _ ih =>
    have e : (corrupted (insert a F) : State P M V) =
        { (corrupted F : State P M V) with bad := insert a (corrupted F : State P M V).bad } := by
      simp [corrupted]
    rw [e]
    refine ih.tail (Step.corrupt _ a ?_)
    rw [← Nat.card_eq_fintype_card]; exact Set.ncard_le_card _

variable {T : TrustModel P} {s : P} {k : ℕ} {A : Protocol P M (Option V) V}

/-- In a failure-free run in which the source broadcasts `m`, a `k`-CB algorithm only delivers
`m` (Integrity, applied to the execution stuttering in the final state; this execution complies
with the fault model iff `∅ ∈ F`). -/
theorem IsKCB.dec_eq_of_reachable (hA : IsKCB T s k A) (h0 : ∅ ∈ T.F) {m : V}
    {σ : State P M V} (hσ : Reachable A (srcInput s (some m)) .byzantine (Fintype.card P) σ)
    (hb : σ.bad = ∅) {p : P} (hp : σ.dec p ≠ none) : σ.dec p = some m := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨E, N, hE⟩ := exists_exec_of_reachable hσ
  have hc : ∀ q, E.Correct q := fun q =>
    (correct_iff_of_stutter hE q).2 (by rw [hb]; exact Set.notMem_empty q)
  have hfs : faultySet E = ∅ := by ext q; simp [faultySet, hc q]
  have := hA.integrity (some m) E (by rw [hfs]; exact h0) (hc s) p N v (hc p)
    (by rw [hE N le_rfl]; exact hv)
  rw [hv, this]

/-- **Lower bound of Theorem 5.1** (repaired). Let `F ∈ F` contain the source `s` and let `C` be
an independent set of `G_{F,S}`. Then every algorithm implementing `k`-CB with (per-value) Local
Progress has `|C| ≤ k`: replaying, for each `p ∈ C`, the Local Progress run of `p` with value
`val p` on the correct members of `S p` (pairwise disjoint by independence), with the members of
`F` (including the source) Byzantine, yields an execution complying with `F` in which the members
of `C` deliver `|C|` distinct values. The fault model must contain `∅` (failure-free executions
comply with it), which follows from the paper's standing assumption that `F` is
inclusion-closed. -/
theorem lower_bound (hA : IsKCB T s k A) (hLP : LocalProgressAll T s A) (h0 : ∅ ∈ T.F)
    {F : Finset P} (hF : F ∈ T.F) (hsF : s ∈ F) {S : P → Finset P} (hS : S ∈ T.QuorumMaps)
    {C : Finset P} (hC : IsIndep F S C) (val : P → V) (hval : Set.InjOn val C) :
    C.card ≤ k := by
  -- the Local Progress runs
  choose σ hreach hbad hdec honly using fun p => hLP p (S p) (hS p) (val p)
  have hdecv : ∀ p, (σ p).dec p = some (val p) := fun p =>
    hA.dec_eq_of_reachable h0 (hreach p) (hbad p) (hdec p)
  have hCF : ∀ p ∈ C, p ∉ F := fun p hp => Finset.disjoint_left.mp hC.1 hp
  -- the correct members of the quorums
  let R : P → Set P := fun p => {q | q ∈ S p ∧ q ∉ F}
  have hpR : ∀ p ∈ C, p ∈ R p := by
    intro p hp
    have h1 := (honly p).2.2 p (hdec p)
    rcases Finset.mem_insert.mp h1 with h1 | h1
    · exact absurd (h1 ▸ hsF) (hCF p hp)
    · exact ⟨h1, hCF p hp⟩
  have hdisj : ∀ p ∈ C, ∀ p' ∈ C, p ≠ p' → ∀ q ∈ R p, q ∉ R p' := by
    rintro p hp p' hp' hne q ⟨hq1, hq2⟩ ⟨hq1', -⟩
    exact hq2 (hC.2 p hp p' hp' hne (Finset.mem_inter.mpr ⟨hq1, hq1'⟩))
  -- gluing the runs, one member of `C` after the other
  have key : ∀ D ⊆ C, ∃ γ, Reach A (srcInput s none) .byzantine (Fintype.card P) (corrupted F) γ ∧
      γ.bad = ↑F ∧ (∀ p ∈ D, γ.dec p = some (val p)) ∧
      ∀ q, (∀ p ∈ D, q ∉ R p) →
        (∀ r m, (q, r, m) ∉ γ.rcv) ∧ (∀ m, (q, m) ∉ γ.sent) ∧ γ.dec q = none := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨corrupted F, .refl, rfl, by simp,
        fun q _ => ⟨by simp [corrupted], by simp [corrupted], rfl⟩⟩
    | insert a D ha ih =>
      intro hD
      have haC : a ∈ C := hD (Finset.mem_insert_self a D)
      have hDC : D ⊆ C := (Finset.subset_insert a D).trans hD
      obtain ⟨γ, hγ, hγbad, hγdec, hγfr⟩ := ih hDC
      have hfra : ∀ q ∈ R a, (∀ r m, (q, r, m) ∉ γ.rcv) ∧ (∀ m, (q, m) ∉ γ.sent) ∧
          γ.dec q = none := fun q hq =>
        hγfr q fun p hp => hdisj a haC p (hDC hp) (fun e => ha (e ▸ hp)) q hq
      have hm0 : Mirror (R a) γ State.init γ :=
        { bad := rfl
          rcv_in := fun q hq r m => by simp [State.init, (hfra q hq).1 r m]
          sent_in := fun q hq m => by simp [State.init, (hfra q hq).2.1 m]
          dec_in := fun q hq => (hfra q hq).2.2
          rcv_out := fun _ _ _ _ => Iff.rfl
          sent_out := fun _ _ _ => Iff.rfl
          dec_out := fun _ _ => rfl }
      obtain ⟨γ', hγ', hm⟩ := hm0.reach (x' := srcInput s none) (t' := Fintype.card P) (hreach a)
        (fun q hq => by rw [hγbad]; exact hq.2)
        (fun q hq => by
          have : q ≠ s := fun e => hq.2 (e ▸ hsF)
          simp [srcInput, this])
        (fun q _ => by rw [hbad a]; exact Set.notMem_empty q)
        (fun q _ r m hm hr => by
          rw [hγbad]
          rcases (hreach a).rcv_origin hm with h1 | ⟨-, h1⟩
          · rcases Finset.mem_insert.mp ((honly a).1 r m h1) with h2 | h2
            · rw [h2]; exact hsF
            · by_contra h3; exact hr ⟨h2, h3⟩
          · rw [hbad a] at h1; exact absurd h1 (Set.notMem_empty r))
      refine ⟨γ', hγ.trans hγ', hm.bad.trans hγbad, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · rw [hm.dec_in p (hpR p haC)]; exact hdecv p
        · have hpa : p ∉ R a :=
            hdisj p (hDC hp) a haC (fun e => ha (e ▸ hp)) p (hpR p (hDC hp))
          rw [hm.dec_out p hpa]; exact hγdec p hp
      · intro q hq
        have hqa : q ∉ R a := hq a (Finset.mem_insert_self a D)
        obtain ⟨h1, h2, h3⟩ := hγfr q fun p hp => hq p (Finset.mem_insert_of_mem hp)
        exact ⟨fun r m => by rw [hm.rcv_out q hqa r m]; exact h1 r m,
          fun m => by rw [hm.sent_out q hqa m]; exact h2 m, by rw [hm.dec_out q hqa]; exact h3⟩
  obtain ⟨γ, hγ, hγbad, hγdec, -⟩ := key C subset_rfl
  -- the glued execution
  obtain ⟨E, N, hE⟩ := exists_exec_of_reachable (reach_corrupted F |>.trans hγ)
  have hcorr : ∀ p, E.Correct p ↔ p ∉ F := fun p => by
    rw [correct_iff_of_stutter hE, hγbad]; rfl
  have hfs : faultySet E = F := by ext p; simp [faultySet, hcorr p]
  have hsub : val '' ↑C ⊆ delivered E := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, N, (hcorr p).2 (hCF p hp), by rw [hE N le_rfl]; exact hγdec p hp⟩
  have := (Set.encard_le_encard hsub).trans (hA.consistency none E (hfs ▸ hF))
  rw [hval.encard_image, Set.encard_coe_eq_coe_finsetCard] at this
  exact_mod_cast this

/-- **Theorem 5.1** (repaired): an algorithm implementing `k`-CB with source `s` and per-value
Local Progress has `k ≥ λ_s`, the largest independence number of a graph `G_{F,S}` with `s ∈ F`.
(The value set must be large enough to give the members of an independent set distinct values;
`∅ ∈ F` follows from the paper's standing assumption that `F` is inclusion-closed.) -/
theorem srcInconsistencyNumber_le [Infinite V] (h0 : ∅ ∈ T.F) (hA : IsKCB T s k A)
    (hLP : LocalProgressAll T s A) : srcInconsistencyNumber T s ≤ k := by
  let e : P ↪ V := (Fintype.equivFin P).toEmbedding.trans
    (Fin.valEmbedding.trans (Infinite.natEmbedding V))
  apply TrustModel.inconsistencyNumber_le
  rintro F ⟨hF, hsF⟩ S hS C hC
  exact lower_bound hA hLP h0 hF hsF hS hC e e.injective.injOn

/-! ### The hypothesis `∅ ∈ F` is needed -/

/-- The algorithm in which every process delivers `v₀` at once and nobody sends anything. -/
def constAlg (v₀ : V) : Protocol P M (Option V) V where
  send _ _ _ _ _ := False
  decide _ _ _ _ o := o = v₀

omit [Fintype P] in
theorem constAlg_dec {v₀ : V} {x : P → Option V} {k : FaultKind} {t : ℕ} {σ : State P M V}
    (h : Reachable (constAlg v₀) x k t σ) {p : P} {v : V} (hv : σ.dec p = some v) : v = v₀ :=
  h.dec_just (J := fun _ o _ _ => o = v₀) (fun _ _ _ _ _ _ _ _ h => h) (fun _ _ _ _ h => h) hv

/-- **The hypothesis `∅ ∈ F` of `lower_bound` cannot be dropped.** Three processes, the only
quorum of each process is itself, and the only admissible faulty set is `{0}` (so `F` is not
inclusion-closed). The source `0` is never correct in a compliant execution, so the algorithm in
which everybody delivers `0` at once is a `1`-CB with per-value Local Progress, although
`{1, 2}` is independent in `G_{{0},S}` and `0 ∈ {0}`. -/
theorem lower_bound_needs_empty_mem :
    let T : TrustModel (Fin 3) := ⟨fun p => {{p}}, {{0}}⟩
    T.SelfMem ∧ IsKCB (M := Unit) T 0 1 (constAlg (0 : ℕ)) ∧
      LocalProgressAll (M := Unit) T 0 (constAlg (0 : ℕ)) ∧
      ({0} : Finset (Fin 3)) ∈ T.F ∧ (fun p => ({p} : Finset (Fin 3))) ∈ T.QuorumMaps ∧
      IsIndep {0} (fun p => ({p} : Finset (Fin 3))) {1, 2} ∧
      ¬ (({1, 2} : Finset (Fin 3)).card ≤ 1) := by
  intro T
  have hsrc : ∀ mo (E : BExec (constAlg (M := Unit) (0 : ℕ)) (0 : Fin 3) mo), faultySet E ∈ T.F →
      ¬ E.Correct 0 := by
    intro mo E hF hs
    have h1 : faultySet E = {0} := hF
    have h2 : (0 : Fin 3) ∈ faultySet E := by rw [h1]; exact Finset.mem_singleton_self 0
    simp [faultySet] at h2
    exact h2 hs
  refine ⟨fun p Q hQ => ?_, ⟨fun m E _ hF hs => absurd hs (hsrc _ E hF), fun mo E _ => ?_,
    fun mo E hF hs => absurd hs (hsrc _ E hF)⟩, fun p Q hQ m => ?_, rfl, fun p => rfl, ?_,
    by decide⟩
  · rw [Set.mem_singleton_iff.mp hQ]; exact Finset.mem_singleton_self p
  · have hsub : delivered E ⊆ {0} := by
      rintro v ⟨p, i, -, hv⟩
      exact constAlg_dec (E.reachable i) hv
    exact (Set.encard_le_encard hsub).trans (by simp)
  · rw [Set.mem_singleton_iff.mp hQ]
    let σ : State (Fin 3) Unit ℕ :=
      { (State.init : State (Fin 3) Unit ℕ) with
        dec := Function.update (State.init : State (Fin 3) Unit ℕ).dec p (some 0) }
    have hst : Step (constAlg (0 : ℕ)) (srcInput 0 (some m)) .byzantine (Fintype.card (Fin 3))
        State.init σ :=
      Step.decide _ p 0 (by simp [State.init]) (by simp [State.init]) rfl
    refine ⟨σ, Relation.ReflTransGen.single hst, rfl, by simp [σ], ?_, ?_, ?_⟩
    · intro q m' hq; simp [σ, State.init] at hq
    · intro q r m' hq; simp [σ, State.init] at hq
    · intro q hq
      by_cases e : q = p
      · rw [e]; simp
      · simp [σ, State.init, Function.update_of_ne e] at hq
  · unfold IsIndep; decide

end LowerBound

end Podc.MultipleSpending
