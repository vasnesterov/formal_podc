import Papers.PODC2011.UnboundedConcurrency.Common

/-!
# Valency with respect to all processes, and Lemma 13 (existence of a critical state)

Afek–Morrison–Wertheim, PODC 2011, Section 5.3. In the unbounded concurrency model the valency
of an execution is taken with respect to *all* extensions (by any of the infinitely many
processes). A bivalent execution then need not have a critical extension in the usual sense
(new processes may keep the execution bivalent forever, each taking one step), so the paper uses
a weaker notion (Definition 2): `α` is critical if a step of `P` leads to a `v`-valent execution
while a step of `Q` followed by a step of `P` leads to a `(¬v)`-valent one.

## Main definitions

* `Uni A x α v`: no extension of `α` (by any processes) decides `¬v` (`α` is `v`-valent, or
  decides nothing at all, which wait-freedom excludes)

## Main statements

* `Uni.append`, `false_of_out_both`, `false_of_agree`, `false_of_mem_eq`: executions of opposite
  valencies are distinguishable — by every process that outputs in both, by every process with
  the same local state in both, and by a fresh process if the memories are equal;
* `lemma_13`: a critical execution (Definition 2) exists.
-/

-- CSLib candidate: `Uni`, `false_of_*`, `solo_reach`, `lemma_13` (valency w.r.t. all processes in
-- `Cslib.SharedMemory.Arrival`, any object family)
namespace Podc.UnboundedConcurrency

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} (A : Alg T ℕ Bool Bool)

/-- No extension of `α` (by any processes) decides `¬v`. -/
def Uni (x : ℕ → Bool) (α : List ℕ) (v : Bool) : Prop := ¬ CanDec A Set.univ x α (!v)

variable {A}

lemma Uni.append {x : ℕ → Bool} {α : List ℕ} {v : Bool} (h : Uni A x α v) (β : List ℕ) :
    Uni A x (α ++ β) v :=
  fun hc => h (hc.of_append (fun _ _ => trivial))

/-- A process that outputs `w` (and took a step) in extensions of executions of opposite
valencies gives a contradiction. -/
lemma false_of_out_both {x : ℕ → Bool} {α₁ α₂ β₁ β₂ : List ℕ} {u : Bool}
    (h₁ : Uni A x α₁ u) (h₂ : Uni A x α₂ (!u)) {r : ℕ} (hr₁ : r ∈ β₁) (hr₂ : r ∈ β₂) {w : Bool}
    (ho₁ : (A.exec x (α₁ ++ β₁)).Out r w) (ho₂ : (A.exec x (α₂ ++ β₂)).Out r w) : False := by
  have hd₁ : CanDec A Set.univ x α₁ w := ⟨β₁, fun _ _ => trivial, r, by simp [hr₁], ho₁⟩
  have hd₂ : CanDec A Set.univ x α₂ w := ⟨β₂, fun _ _ => trivial, r, by simp [hr₂], ho₂⟩
  cases u <;> cases w
  · exact h₂ hd₂
  · exact h₁ hd₁
  · exact h₁ hd₁
  · exact h₂ hd₂

section WaitFree

variable (hwf : WaitFree A (fun s => (Set.range s).Finite))
include hwf

/-- Two executions of opposite valencies that are indistinguishable to some process `r` give a
contradiction (run `r` solo in both). -/
lemma false_of_agree {x : ℕ → Bool} {α₁ α₂ : List ℕ} {u : Bool}
    (h₁ : Uni A x α₁ u) (h₂ : Uni A x α₂ (!u)) {r : ℕ}
    (hagr : AgreeOn {r} (A.exec x α₁) (A.exec x α₂)) : False := by
  obtain ⟨m, w, hout⟩ := exists_solo_out hwf x α₁ r
  have hrep : ∀ s ∈ List.replicate (m + 1) r, s ∈ ({r} : Set ℕ) := fun s hs => by
    rw [List.eq_of_mem_replicate hs]; rfl
  have h2 := Alg.run_agreeOn hagr hrep
  rw [← Alg.exec_append, ← Alg.exec_append] at h2
  have hout2 := (h2.out_iff (by rfl) w).1 hout
  exact false_of_out_both h₁ h₂ (by simp) (by simp) hout hout2

/-- Two executions of opposite valencies with the same memory give a contradiction (a fresh
process cannot tell them apart). -/
lemma false_of_mem_eq {x : ℕ → Bool} {α₁ α₂ : List ℕ} {u : Bool}
    (h₁ : Uni A x α₁ u) (h₂ : Uni A x α₂ (!u))
    (hmem : (A.exec x α₁).mem = (A.exec x α₂).mem) : False := by
  obtain ⟨r, hr⟩ := exists_fresh (α₁ ++ α₂)
  simp only [List.mem_append, not_or] at hr
  refine false_of_agree hwf h₁ h₂ (r := r) ⟨hmem, fun p hp => ?_⟩
  simp only [Set.mem_singleton_iff] at hp; subst hp
  simp only [Alg.exec]
  rw [Alg.run_loc_other _ _ hr.1, Alg.run_loc_other _ _ hr.2]

/-- From every execution some value can be decided. -/
lemma exists_canDec_univ (x : ℕ → Bool) (α : List ℕ) : ∃ v, CanDec A Set.univ x α v :=
  exists_canDec hwf (Set.mem_univ 0) x α

lemma not_uni_both {x : ℕ → Bool} {α : List ℕ} {u : Bool} (h₁ : Uni A x α u)
    (h₂ : Uni A x α (!u)) : False := by
  obtain ⟨v, hv⟩ := exists_canDec_univ hwf x α
  cases u <;> cases v
  · exact h₂ hv
  · exact h₁ hv
  · exact h₁ hv
  · exact h₂ hv

/-- **Solo simulation.** Let `Rel` be a relation between configurations that is preserved by the
steps of `r` from configurations that are not `Bad`, and that forces equal local states of `r`.
If the two executions `α₁`, `α₂` have opposite valencies and are related, then running `r` solo
after both reaches a `Bad` configuration (after `α₁ r^n`), the configurations staying related. -/
lemma solo_reach (Rel : Cfg A → Cfg A → Prop) (Bad : Cfg A → Prop) (r : ℕ)
    (hstep : ∀ C D, Rel C D → ¬ Bad C → Rel (C.step r) (D.step r))
    (hloc : ∀ C D, Rel C D → C.loc r = D.loc r)
    {x : ℕ → Bool} {α₁ α₂ : List ℕ} {u : Bool} (h₁ : Uni A x α₁ u) (h₂ : Uni A x α₂ (!u))
    (h : Rel (A.exec x α₁) (A.exec x α₂)) :
    ∃ n, (∀ j < n, ¬ Bad (A.exec x (α₁ ++ List.replicate j r))) ∧
      Bad (A.exec x (α₁ ++ List.replicate n r)) ∧
      Rel (A.exec x (α₁ ++ List.replicate n r)) (A.exec x (α₂ ++ List.replicate n r)) := by
  classical
  have hiter : ∀ n, (∀ j < n, ¬ Bad (A.exec x (α₁ ++ List.replicate j r))) →
      Rel (A.exec x (α₁ ++ List.replicate n r)) (A.exec x (α₂ ++ List.replicate n r)) := by
    intro n
    induction n with
    | zero => intro _; simpa using h
    | succ n ih =>
      intro hb
      have := hstep _ _ (ih (fun j hj => hb j (by omega))) (hb n (by omega))
      simpa [List.replicate_succ', ← List.append_assoc, Alg.exec_concat] using this
  obtain ⟨m, w, hout⟩ := exists_solo_out hwf x α₁ r
  by_cases hex : ∃ n, Bad (A.exec x (α₁ ++ List.replicate n r))
  · refine ⟨Nat.find hex, fun j hj => Nat.find_min hex hj, Nat.find_spec hex,
      hiter _ (fun j hj => Nat.find_min hex hj)⟩
  · push Not at hex
    exfalso
    have hrel := hiter (m + 1) (fun j _ => hex j)
    have hout2 : (A.exec x (α₂ ++ List.replicate (m + 1) r)).Out r w := by
      unfold Cfg.Out; rw [← hloc _ _ hrel]; exact hout
    exact false_of_out_both h₁ h₂ (by simp) (by simp) hout hout2

end WaitFree

/-! ### Lemma 13 -/

section Lemma13

variable (hag : Agreement A (fun _ => True)) (hwf : WaitFree A infArrival)
include hag hwf

/-- One round of the construction of Lemma 13: if no critical execution exists, every bivalent
execution has a bivalent extension in which process `pp` takes a step. -/
lemma lemma_13_step (pp : ℕ) {x : ℕ → Bool}
    (hno : ¬ ∃ α qq v, Uni A x (α ++ [pp]) v ∧ Uni A x (α ++ [qq, pp]) (!v))
    {α : List ℕ} (hb : Biv A Set.univ x α) :
    ∃ γ, pp ∈ γ ∧ Biv A Set.univ x (α ++ γ) := by
  classical
  have hwf' : WaitFree A (fun s => (Set.range s).Finite) := fun x s _ => hwf x s trivial
  -- run `pp` solo until its next step makes the execution univalent
  have hex : ∃ k, ¬ Biv A Set.univ x (α ++ List.replicate (k + 1) pp) := by
    obtain ⟨m, v, hout⟩ := exists_solo_out hwf' x α pp
    exact ⟨m, fun hb' => hb'.not_out hag (Or.inr (Set.mem_univ pp)) v hout⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀n : ¬ Biv A Set.univ x (α ++ List.replicate (k₀ + 1) pp) := Nat.find_spec hex
  have hk₀b : Biv A Set.univ x (α ++ List.replicate k₀ pp) := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · rw [h0]; simpa using hb
    · have := Nat.find_min hex (show k₀ - 1 < k₀ by omega)
      rw [not_not, show k₀ - 1 + 1 = k₀ by omega] at this
      exact this
  set α' := α ++ List.replicate k₀ pp with hα'
  have hα'P : α ++ List.replicate (k₀ + 1) pp = α' ++ [pp] := by
    rw [hα', List.replicate_succ', List.append_assoc]
  rw [hα'P] at hk₀n
  obtain ⟨v, hv⟩ := exists_canDec_univ hwf' x (α' ++ [pp])
  have huni : Uni A x (α' ++ [pp]) v := by
    intro hc
    apply hk₀n
    cases v
    · exact ⟨hv, hc⟩
    · exact ⟨hc, hv⟩
  -- an extension of `α'` deciding `¬v`
  have hcd : CanDec A Set.univ x α' (!v) := by cases v; exact hk₀b.2; exact hk₀b.1
  obtain ⟨β, -, hβ⟩ := hcd
  let f : ℕ → Prop := fun j => CanDec A Set.univ x (α' ++ β.take j ++ [pp]) (!v)
  have hfex : ∃ j, f j := ⟨β.length, ⟨[], fun _ _ => trivial, by
    simpa [List.take_length] using hβ.append [pp]⟩⟩
  set j₀ := Nat.find hfex with hj₀
  have hj₀f : f j₀ := Nat.find_spec hfex
  have hj₀pos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h0 | h
    · exfalso; have := hj₀f; rw [h0] at this; exact huni (by simpa [f] using this)
    · exact h
  have hj₀min : ¬ f (j₀ - 1) := Nat.find_min hfex (by omega)
  have hjlt : j₀ - 1 < β.length := by
    by_contra hge
    push Not at hge
    apply hj₀min
    have : β.take (j₀ - 1) = β := List.take_of_length_le hge
    exact ⟨[], fun _ _ => trivial, by simpa [this] using hβ.append [pp]⟩
  set δ := α' ++ β.take (j₀ - 1) with hδ
  set b := β[j₀ - 1] with hb
  have htake : β.take j₀ = β.take (j₀ - 1) ++ [b] := by
    rw [show j₀ = j₀ - 1 + 1 by omega, List.take_add_one, List.getElem?_eq_getElem hjlt]
    simp [hb]
  have hδP : Uni A x (δ ++ [pp]) v := by
    intro h; apply hj₀min; simpa [f, hδ] using h
  have hδbP : CanDec A Set.univ x (δ ++ [b, pp]) (!v) := by
    have := hj₀f
    simp only [f, htake] at this
    simpa [hδ, List.append_assoc] using this
  by_cases hboth : CanDec A Set.univ x (δ ++ [b, pp]) v
  · refine ⟨List.replicate k₀ pp ++ β.take (j₀ - 1) ++ [b, pp], by simp, ?_⟩
    have heq : α ++ (List.replicate k₀ pp ++ β.take (j₀ - 1) ++ [b, pp]) = δ ++ [b, pp] := by
      simp [hδ, hα', List.append_assoc]
    rw [heq]
    cases v
    · exact ⟨hboth, hδbP⟩
    · exact ⟨hδbP, hboth⟩
  · exact absurd ⟨δ, b, v, hδP, by simpa [Uni] using hboth⟩ hno

/-- **Lemma 13** of [AMW11]. If some execution is bivalent, a critical execution (Definition 2)
exists: an execution `α`, processes `P`, `Q` and a value `v` such that after `α P` only `v`, and
after `α Q P` only `¬v` can be decided. -/
theorem lemma_13 {x : ℕ → Bool} {α₀ : List ℕ} (hb : Biv A Set.univ x α₀) :
    ∃ α pp qq v, Uni A x (α ++ [pp]) v ∧ Uni A x (α ++ [qq, pp]) (!v) := by
  classical
  by_contra hno
  have hno' : ∀ pp, ¬ ∃ α qq v, Uni A x (α ++ [pp]) v ∧ Uni A x (α ++ [qq, pp]) (!v) :=
    fun pp ⟨α, qq, v, h⟩ => hno ⟨α, pp, qq, v, h⟩
  let B := {α : List ℕ // Biv A Set.univ x α}
  have hstep : ∀ β : B, ∃ γ, 0 ∈ γ ∧ Biv A Set.univ x (β.1 ++ γ) :=
    fun β => lemma_13_step hag hwf 0 (hno' 0) β.2
  choose γ hγ0 hγ using hstep
  let st : ℕ → B := fun k => Nat.rec ⟨α₀, hb⟩ (fun _ β => ⟨β.1 ++ γ β, hγ β⟩) k
  have hsucc : ∀ k, (st (k + 1)).1 = (st k).1 ++ γ (st k) := fun k => rfl
  have hlen : ∀ k, k ≤ (st k).1.length := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      rw [hsucc, List.length_append]
      have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (hγ0 (st k)))
      omega
  obtain ⟨s, hs⟩ := exists_seq_of_chain (fun k => (st k).1)
    (fun k => by simp only [hsucc]; exact List.prefix_append _ _) hlen
  have hinf : InfOften s 0 := by
    intro N
    have h1 := hs (N + 1)
    simp only [hsucc, List.length_append, pre_add] at h1
    rw [hs N] at h1
    have h2 := List.append_cancel_left h1
    have h3 : 0 ∈ pre (fun t => s ((st N).1.length + t)) (γ (st N)).length := by
      rw [h2]; exact hγ0 (st N)
    obtain ⟨u, -, hsu⟩ := mem_pre.1 h3
    exact ⟨_ + u, by have := hlen N; omega, hsu⟩
  obtain ⟨t, v, hout⟩ := hwf x s trivial 0 hinf
  apply (st t).2.not_out hag (Or.inr (Set.mem_univ 0)) v
  obtain ⟨τ, hτ⟩ := pre_prefix s (hlen t)
  rw [hs t] at hτ
  rw [← hτ, Alg.exec_append]
  exact Alg.Cfg.Out.run hout τ

end Lemma13

end Podc.UnboundedConcurrency
