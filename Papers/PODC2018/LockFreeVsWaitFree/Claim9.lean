import Papers.PODC2018.LockFreeVsWaitFree.Commute

/-!
# Claim 9 of [ACHP18] and the final contradiction

* `Ctx.Wr α p i` — after `α`, process `p` is about to write base object `i` (it is poised to apply
  a non-read-only operation to `i`); `Ctx.NoW α σ R` — the schedule `σ` takes no write to `R`.
* `Ctx.claim9` — **Claim 9**: if `α` is `(v, q, v')`-critical and the next steps of `p₀` and `q`
  both write the same base object `R`, then for every extension by a schedule `σ` without `p₀`,
  `q` and writes to `R`, `p₀(C')` is `v`-univalent and `p₀(q(C'))` is `v'`-univalent.
* `Ctx.false_of_witness` — the final contradiction of the proof of Theorem 11: a `v`-univalent
  and a `w`-univalent execution (`v ≠ w`) in which the same process `q ≠ p₀` returned the same
  value `x` in an operation with index `≥ k + 2`, where `1/2^k < |v - w|`.
* `Ctx.solo_witness` — a process `q` running solo from two executions it cannot distinguish
  produces such a common value.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeVsWaitFree

open Cslib SharedMemory Impl

-- CSLib candidate
/-- A process is poised to apply at most one operation to a given base object. -/
lemma PoisedAt.op_eq {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} {I : Impl A B P L}
    {C : Config A B P L} {p : P} {i : ι} {o o' : (B i).Op} (h : I.PoisedAt C p i o)
    (h' : I.PoisedAt C p i o') : o = o' := by
  obtain ⟨-, k, h1⟩ := h
  obtain ⟨-, k', h2⟩ := h'
  rw [h1] at h2
  cases h2; rfl

namespace Ctx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] {X : Ctx P ι L B}

variable (X) in
/-- After `α`, process `p` is about to write base object `i`. -/
def Wr (α : List (LLabel P)) (p : P) (i : ι) : Prop :=
  ∃ o, X.I.PoisedAt (X.cfg α) p i o ∧ ¬ (B i).ReadOnly o

variable (X) in
/-- The schedule `σ`, run from `α`, takes no write to the base object `R`. -/
def NoW (R : ι) : List (LLabel P) → List P → Prop
  | _, [] => True
  | α, p :: σ => ¬ X.Wr α p R ∧ NoW R (X.ext1 α p) σ

@[simp] lemma noW_nil (R : ι) (α : List (LLabel P)) : X.NoW R α [] := trivial

lemma noW_append (R : ι) (α : List (LLabel P)) (σ τ : List P) :
    X.NoW R α (σ ++ τ) ↔ X.NoW R α σ ∧ X.NoW R (X.ext α σ) τ := by
  induction σ generalizing α with
  | nil => simp
  | cons p σ ih => simp only [List.cons_append, NoW, ih, ext_cons, and_assoc]

lemma noW_concat (R : ι) (α : List (LLabel P)) (σ : List P) (p : P) :
    X.NoW R α (σ ++ [p]) ↔ X.NoW R α σ ∧ ¬ X.Wr (X.ext α σ) p R := by
  rw [noW_append]; simp [NoW]

lemma noW_replicate (R : ι) (α : List (LLabel P)) (r : P) (N : ℕ)
    (h : ∀ n < N, ¬ X.Wr (X.ext α (List.replicate n r)) r R) :
    X.NoW R α (List.replicate N r) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.replicate_succ', noW_concat]
    exact ⟨ih fun n hn => h n (by omega), h N (by omega)⟩

/-- Being about to write is not changed by steps of other processes. -/
lemma Good.wr_ext_of_not_mem {α : List (LLabel P)} (hα : X.Good α) {p : P} {σ : List P}
    (hp : p ∉ σ) {i : ι} : X.Wr (X.ext α σ) p i ↔ X.Wr α p i := by
  unfold Wr
  simp only [hα.poised_ext_of_not_mem hp]

/-! ### Critical executions: basic facts -/

/-- In a critical execution, `p₀` has not returned. -/
lemma Critical.nl_p₀ {α : List (LLabel P)} {v v' : ℝ} {q : P} (hc : X.Critical α v q v') :
    (X.nl α X.p₀).isSome := by
  obtain ⟨hα, hq, hvv, hv, hv', -⟩ := hc
  by_contra hn
  have hn' : X.nl α X.p₀ = none := Option.not_isSome_iff_eq_none.1 hn
  rw [ext1_of_none hn'] at hv
  have hn2 : X.nl (X.ext α [q]) X.p₀ = none := by
    rw [hα.nl_ext_of_not_mem (by simpa using Ne.symm hq), hn']
  rw [show [q, X.p₀] = [q] ++ [X.p₀] from rfl, ext_concat, ext1_of_none hn2, ext_singleton] at hv'
  exact hvv (hv.ext' (by unfold Ctx.ext1; exact List.prefix_append _ _) hv'.good |>.unique hv')

/-- **Commuting the next steps of two processes**, schedule version. -/
lemma Good.swap' {α : List (LLabel P)} (hα : X.Good α) {a b : P} (hab : a ≠ b)
    (ha : (X.nl α a).isSome) (hb : (X.nl α b).isSome)
    (hnw : ∀ i o, X.I.PoisedAt (X.cfg α) b i o → ∀ o', X.I.PoisedAt (X.cfg α) a i o' →
      (B i).ReadOnly o') :
    AgreeOn {r | r ≠ a} (X.cfg (X.ext α [a, b])) (X.cfg (X.ext α [b, a])) := by
  obtain ⟨ℓa, hla⟩ := Option.isSome_iff_exists.1 ha
  obtain ⟨ℓb, hlb⟩ := Option.isSome_iff_exists.1 hb
  obtain ⟨e1, e2, hag⟩ := hα.swap hab hla hlb hnw
  rw [e1, e2]; exact hag

/-- `p₀`'s operations and responses after a schedule in which it occurs once. -/
lemma p₀_eq_of_single {α : List (LLabel P)} (hα : X.Good α) {σ τ σ' τ' : List P}
    (h1 : X.p₀ ∉ σ) (h2 : X.p₀ ∉ τ) (h3 : X.p₀ ∉ σ') (h4 : X.p₀ ∉ τ') :
    opsOf (X.ext α (σ ++ X.p₀ :: τ)) X.p₀ = opsOf (X.ext α (σ' ++ X.p₀ :: τ')) X.p₀ ∧
      respsOf (X.ext α (σ ++ X.p₀ :: τ)) X.p₀ = respsOf (X.ext α (σ' ++ X.p₀ :: τ')) X.p₀ := by
  obtain ⟨a1, b1⟩ := opsOf_ext_single α h1 h2 hα
  obtain ⟨a2, b2⟩ := opsOf_ext_single α h3 h4 hα
  exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩

/-! ### Claim 9 -/

/-- **Claim 9 of [ACHP18].** Let `α` be `(v, q, v')`-critical, with the next steps of `p₀` and of
`q` both writing base object `R`. For every schedule `σ` without `p₀` and `q` whose steps do not
write `R`, `p₀(C')` is `v`-univalent and `p₀(q(C'))` is `v'`-univalent, `C'` the configuration
after `σ`. -/
theorem claim9 {α : List (LLabel P)} {v v' : ℝ} {q : P} (hc : X.Critical α v q v') {R : ι}
    (hR0 : X.Wr α X.p₀ R) (hRq : X.Wr α q R) :
    ∀ σ : List P, X.p₀ ∉ σ → q ∉ σ → X.NoW R α σ →
      X.Univ (X.ext α (σ ++ [X.p₀])) v ∧ X.Univ (X.ext α (σ ++ [q, X.p₀])) v' := by
  have hα := hc.1
  have hq := hc.2.1
  have hs0 := hc.nl_p₀
  intro σ
  induction σ using List.reverseRecOn with
  | nil => intro _ _ _; exact ⟨by simpa [ext_singleton] using hc.2.2.2.1, by simpa using hc.2.2.2.2.1⟩
  | append_singleton σ r ih =>
    intro h0 hq' hnw
    simp only [List.mem_append, List.mem_singleton, not_or] at h0 hq'
    obtain ⟨h0σ, h0r⟩ := h0
    obtain ⟨hqσ, hqr⟩ := hq'
    rw [noW_concat] at hnw
    obtain ⟨hnwσ, hwr⟩ := hnw
    obtain ⟨ih0, ihq⟩ := ih h0σ hqσ hnwσ
    rw [ext_append] at ih0 ihq
    have hβg' : X.Good (X.ext α σ) := hα.ext σ
    have hpσ : ∀ p, p ∉ σ → ∀ i (o : (B i).Op),
        X.I.PoisedAt (X.cfg (X.ext α σ)) p i o ↔ X.I.PoisedAt (X.cfg α) p i o :=
      fun p hp i o => hα.poised_ext_of_not_mem hp
    have hnlσ : X.nl (X.ext α σ) X.p₀ = X.nl α X.p₀ := hα.nl_ext_of_not_mem h0σ
    have hcrit := hc.2.2.2.2.2
    have hσr : ∀ τ : List P, X.ext α (σ ++ τ) = X.ext (X.ext α σ) τ := fun τ => ext_append _ _ _
    generalize hβ : X.ext α σ = β at ih0 ihq hwr hβg' hpσ hnlσ hσr
    have hβg := hβg'
    have hr0 : r ≠ X.p₀ := fun h => h0r h.symm
    have hrq : r ≠ q := fun h => hqr h.symm
    -- the only base object `p₀` and `q` access is `R`
    obtain ⟨o₀, hpo₀, -⟩ := hR0
    obtain ⟨oq, hpoq, -⟩ := hRq
    have hR0β : ∀ γ : List P, X.p₀ ∉ γ → ∀ i o, X.I.PoisedAt (X.cfg (X.ext β γ)) X.p₀ i o → i = R :=
      fun γ hγ i o h => by
        rw [hβg.poised_ext_of_not_mem hγ, hpσ _ h0σ] at h
        exact h.unique hpo₀
    have hRqβ : ∀ γ : List P, q ∉ γ → ∀ i o, X.I.PoisedAt (X.cfg (X.ext β γ)) q i o → i = R :=
      fun γ hγ i o h => by
        rw [hβg.poised_ext_of_not_mem hγ, hpσ _ hqσ] at h
        exact h.unique hpoq
    -- `r` does not write `R` (also after a step of `q`)
    have hnoRO : ∀ γ : List P, r ∉ γ → ∀ o, X.I.PoisedAt (X.cfg (X.ext β γ)) r R o →
        (B R).ReadOnly o := fun γ hγ o h => by
      by_contra hro
      rw [hβg.poised_ext_of_not_mem hγ] at h
      exact hwr ⟨o, h, hro⟩
    have hsr : ∀ γ : List P, (X.nl (X.ext β γ) r).isSome := fun γ => nl_isSome_of_ne hr0
    have hs0β : ∀ γ : List P, X.p₀ ∉ γ → (X.nl (X.ext β γ) X.p₀).isSome := fun γ hγ => by
      rw [hβg.nl_ext_of_not_mem hγ, hnlσ]; exact hs0
    have hsq : ∀ γ : List P, (X.nl (X.ext β γ) q).isSome := fun γ => nl_isSome_of_ne hq
    have hnil0 : X.p₀ ∉ ([] : List P) := List.not_mem_nil
    -- first statement
    have ag1 : AgreeOn {x | x ≠ r} (X.cfg (X.ext β [r, X.p₀])) (X.cfg (X.ext β [X.p₀, r])) := by
      have := hβg.swap' hr0 (by simpa using hsr []) (by simpa using hs0β [] hnil0)
        (fun i o h o' h' => by
          have hi := hR0β [] hnil0 i o (by simpa using h); subst hi
          exact hnoRO [] List.not_mem_nil o' (by simpa using h'))
      exact this
    have hv1 : X.Univ (X.ext β [X.p₀, r]) v := by
      have : X.ext β [X.p₀, r] = X.ext β [X.p₀] ++ X.extL (X.ext β [X.p₀]) [r] := by
        rw [← ext_eq_append, ← ext_append]; rfl
      rw [this]
      refine Univ.ext ?_ ?_
      · exact ih0
      · rw [← this]; exact hβg.ext _
    have hpot1 : X.Potent (X.ext β [r, X.p₀]) v := by
      obtain ⟨e1, e2⟩ := p₀_eq_of_single (X := X) hβg (σ := []) (τ := [r]) (σ' := [r]) (τ' := [])
        (by simp) (by simpa using hr0.symm) (by simpa using hr0.symm) (by simp)
      exact hv1.potent_of_agree (hβg.ext _) (ag1.agree (show X.p₀ ≠ r from hr0.symm)).symm
        (by simpa using e1) (by simpa using e2)
    obtain ⟨w₁, hw₁⟩ := hcrit (σ ++ [r]) (by simp [h0σ, hr0.symm])
    have e1 : X.ext α ((σ ++ [r]) ++ [X.p₀]) = X.ext β [r, X.p₀] := by
      rw [List.append_assoc, hσr]; rfl
    rw [e1] at hw₁
    have hw₁v : w₁ = v := (hw₁.2 v hpot1).symm
    subst hw₁v
    refine ⟨by rw [e1]; exact hw₁, ?_⟩
    -- second statement: `[r, q, p₀]` against `[q, p₀, r]`
    have agA : AgreeOn {x | x ≠ r} (X.cfg (X.ext β [r, q])) (X.cfg (X.ext β [q, r])) :=
      hβg.swap' hrq (by simpa using hsr []) (by simpa using hsq [])
        (fun i o h o' h' => by
          have hi := hRqβ [] List.not_mem_nil i o (by simpa using h); subst hi
          exact hnoRO [] List.not_mem_nil o' (by simpa using h'))
    have agA' : AgreeOn {x | x ≠ r} (X.cfg (X.ext β [r, q, X.p₀])) (X.cfg (X.ext β [q, r, X.p₀])) := by
      have h1 := (transfer (Q := {x | x ≠ r}) (hβg.ext [r, q]) (hβg.ext [q, r]) agA
        (fun _ => by
          rw [opsOf_ext_of_not_mem (by simp [Ne.symm hr0, Ne.symm hq]),
            opsOf_ext_of_not_mem (by simp [Ne.symm hr0, Ne.symm hq])])
        (σ := [X.p₀]) (by simpa using hr0.symm)).2.1
      simpa only [← ext_append, List.cons_append, List.nil_append] using h1
    have agB : AgreeOn {x | x ≠ r} (X.cfg (X.ext β [q, r, X.p₀])) (X.cfg (X.ext β [q, X.p₀, r])) := by
      have hβq : X.Good (X.ext β [q]) := hβg.ext _
      have := hβq.swap' hr0
        (hsr [q])
        (hs0β [q] (by simpa using Ne.symm hq))
        (fun i o h o' h' => by
          have hi := hR0β [q] (by simpa using Ne.symm hq) i o (by simpa using h); subst hi
          exact hnoRO [q] (by simpa using hrq) o' (by simpa using h'))
      simpa only [← ext_append, List.cons_append, List.nil_append] using this
    have hv2 : X.Univ (X.ext β [q, X.p₀, r]) v' := by
      have : X.ext β [q, X.p₀, r] = X.ext β [q, X.p₀] ++ X.extL (X.ext β [q, X.p₀]) [r] := by
        rw [← ext_eq_append, ← ext_append]; rfl
      rw [this]
      refine Univ.ext ?_ ?_
      · exact ihq
      · rw [← this]; exact hβg.ext _
    have hpot2 : X.Potent (X.ext β [r, q, X.p₀]) v' := by
      obtain ⟨e1, e2⟩ := p₀_eq_of_single (X := X) hβg (σ := [q]) (τ := [r]) (σ' := [r, q])
        (τ' := []) (by simpa using Ne.symm hq) (by simpa using hr0.symm)
        (by simp [Ne.symm hr0, Ne.symm hq]) (by simp)
      exact hv2.potent_of_agree (hβg.ext _)
        ((agA'.trans agB).agree (show X.p₀ ≠ r from hr0.symm)).symm
        (by simpa using e1) (by simpa using e2)
    obtain ⟨w₂, hw₂⟩ := hcrit (σ ++ [r, q]) (by simp [h0σ, hr0.symm, hq.symm])
    have e2 : X.ext α ((σ ++ [r, q]) ++ [X.p₀]) = X.ext β [r, q, X.p₀] := by
      rw [List.append_assoc, hσr]; rfl
    rw [e2] at hw₂
    have hw₂v : w₂ = v' := (hw₂.2 v' hpot2).symm
    subst hw₂v
    have e3 : X.ext α ((σ ++ [r]) ++ [q, X.p₀]) = X.ext β [r, q, X.p₀] := by
      rw [List.append_assoc, hσr]; rfl
    rw [e3]; exact hw₂

/-! ### The final contradiction -/

/-- The final contradiction of the proof of Theorem 11 of [ACHP18]. -/
theorem false_of_witness {γ₁ γ₂ : List (LLabel P)} {v w : ℝ} (h₁ : X.Univ γ₁ v)
    (h₂ : X.Univ γ₂ w) {k : ℕ} (hk : (1 / 2 : ℝ) ^ k < |v - w|) {q : P} (hq : q ≠ X.p₀)
    {x : ℝ} {m₁ m₂ : ℕ} (hx₁ : respOf γ₁ (q, m₁) = some x) (hm₁ : k + 2 ≤ m₁)
    (hx₂ : respOf γ₂ (q, m₂) = some x) (hm₂ : k + 2 ≤ m₂) : False := by
  have c1 := close_of_univ h₁ hq hx₁ hm₁
  have c2 := close_of_univ h₂ hq hx₂ hm₂
  have : |v - w| ≤ |x - v| + |x - w| := by
    have := abs_sub_le v x w; rw [abs_sub_comm v x] at this; exact this
  have hpow : (1 / 2 : ℝ) ^ k = 2 * (1 / 2) ^ (k + 1) := by ring
  linarith

/-- The last response of `q` in a fragment with at least `k + 3` responses of `q` has index at
least `k + 2` in any execution ending with the fragment. -/
lemma exists_last_resp {β : List (LLabel P)} {q : P} {k : ℕ}
    (hβ : k + 3 ≤ (respsOf β q).length) :
    ∃ x, ∀ γ : List (LLabel P), ∃ m, k + 2 ≤ m ∧ respOf (γ ++ β) (q, m) = some x := by
  refine ⟨(respsOf β q)[(respsOf β q).length - 1], fun γ =>
    ⟨(respsOf γ q).length + ((respsOf β q).length - 1), by omega, ?_⟩⟩
  simp only [respOf, respsOf_append]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem?_eq_getElem _

/-- A process `q ≠ p₀` running solo from two good executions it cannot distinguish returns the
same value in an operation with index at least `k + 2`. -/
theorem solo_witness {γ₁ γ₂ : List (LLabel P)} (h₁ : X.Good γ₁) (h₂ : X.Good γ₂) {q : P}
    (hq : q ≠ X.p₀) (hag : Agree q (X.cfg γ₁) (X.cfg γ₂)) (k : ℕ) :
    ∃ N x m₁ m₂, k + 2 ≤ m₁ ∧ respOf (X.ext γ₁ (List.replicate N q)) (q, m₁) = some x ∧
      k + 2 ≤ m₂ ∧ respOf (X.ext γ₂ (List.replicate N q)) (q, m₂) = some x := by
  obtain ⟨N, hN⟩ := h₁.exists_resps_extL hq (k + 3)
  obtain ⟨e1, -, -⟩ := transfer (Q := {q}) h₁ h₂
    ⟨hag.mem, fun r hr => by rw [hr]; exact hag.loc, fun r hr => by rw [hr]; exact hag.pend⟩
    (fun h => absurd (Set.mem_singleton_iff.1 h).symm hq) (σ := List.replicate N q)
    (fun p hp => by rw [List.eq_of_mem_replicate hp]; rfl)
  obtain ⟨x, hx⟩ := exists_last_resp hN
  obtain ⟨m₁, hm₁, hx₁⟩ := hx γ₁
  obtain ⟨m₂, hm₂, hx₂⟩ := hx γ₂
  rw [e1] at hx₂
  exact ⟨N, x, m₁, m₂, hm₁, hx₁, hm₂, hx₂⟩

end Ctx

end Podc.LockFreeVsWaitFree
