import Papers.PODC2017.MemoryAnonymousCoordination.ImpCommon
import Cslib.Computability.Distributed.SharedMemory.BinaryReduction

/-!
# Theorem 6.3: no obstruction-free consensus with unnamed registers

Taubenfeld, *Coordination Without Prior Agreement*, PODC 2017, Section 6.3.

There is no obstruction-free consensus algorithm using unnamed read/write registers
(1) when the number of processes is not a priori known (`theorem_6_3_1`), and (2) for `n ≥ 2`
processes using `n − 1` (or fewer) registers (`theorem_6_3_2`).

The algorithm is an arbitrary (not necessarily symmetric) read/write algorithm
`I : Impl (MCons Val) (RegFamily ι V v₀) P L` (`MCons Val` is CSLib's reducible copy of
`taskObj Val Val`) in local register names; it solves the
problem if `I.unnamed π` does for every choice `π` of the processes' private register numberings.
Consensus is CSLib's `consensus P Val` (agreement + validity) with one-shot obstruction-freedom
(`OneShotOF`, weaker than obstruction-freedom, so the impossibility is stronger); two distinct
input values suffice.
-/

open Cslib.SharedMemory Impl

namespace Podc.MemoryAnonymousCoordination

variable {ι V P L Val : Type} {v₀ : V} [DecidableEq P] [DecidableEq ι] [Inhabited Val]
  {I : Impl (MCons Val) (RegFamily ι V v₀) P L}

/-- `π` makes `I` a one-shot obstruction-free consensus algorithm. -/
def ConsOK (I : Impl (MCons Val) (RegFamily ι V v₀) P L) (π : P → Equiv.Perm ι) : Prop :=
  (I.unnamed π).Solves (consensus P Val) ∧ (I.unnamed π).OneShotOF

lemma oneShot_single (p : P) (x : Val) : OneShot ([.inv p x] : List (Label P (MCons Val))) := by
  intro r
  by_cases h : r = p
  · simp [opsOf, Label.invOf, h]
  · simp [opsOf, Label.invOf, Ne.symm h]

/-- A process running solo from the initial configuration decides its own input. -/
lemma cons_solo_run {π : P → Equiv.Perm ι} (H : ConsOK I π) (hall : ∀ p x, I.allowed p x) (p : P)
    (x : Val) :
    ∃ β D, (∀ ℓ ∈ β, ℓ.proc = p) ∧ (∀ r, opsOf β r = if r = p then [x] else []) ∧
      (I.unnamed π).run β = some D ∧ D.pend p = none ∧ outputs β p = some x := by
  set J := I.unnamed π
  obtain ⟨F, hF⟩ : ∃ F, J.run [.inv p x] = some F :=
    ⟨_, by simp only [run, runFrom_cons, runFrom_nil]; rw [step_inv_eq_some (I := J) rfl (by simpa [J] using hall p x)]; rfl⟩
  obtain ⟨γ, D, hγ, hops, hr, hfin⟩ := solo_from H.2 hF (oneShot_single p x) p
  have hrun : J.run (.inv p x :: γ) = some D := by
    rw [show (.inv p x :: γ : List _) = [.inv p x] ++ γ from rfl, run, runFrom_append]
    rw [run] at hF; rw [hF]; exact hr
  have hops' : ∀ r, opsOf (.inv p x :: γ) r = if r = p then [x] else [] := by
    intro r
    rw [opsOf_cons, hops r]
    by_cases h : r = p
    · simp [Label.invOf, h]
    · simp [Label.invOf, Ne.symm h, h]
  have hos : OneShot (.inv p x :: γ) := fun r => by rw [hops' r]; split_ifs <;> simp
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1
    (J.outputs_ne_none_of_run hrun (p := p) (by simp [hops']) hfin)
  obtain ⟨r, hr'⟩ := (H.1 _ ⟨D, hrun⟩ hos).2 p y hy
  have hrp : r = p := by
    by_contra hne
    change (opsOf (Label.inv p x :: γ : List (Label P (MCons Val))) r).head? = some y at hr'
    rw [hops' r] at hr'; simp [hne] at hr'
  subst hrp
  change (opsOf (Label.inv r x :: γ : List (Label P (MCons Val))) r).head? = some y at hr'
  rw [hops' r] at hr'
  simp only [↓reduceIte] at hr'
  simp only [List.head?_cons, Option.some.injEq] at hr'
  refine ⟨_, D, fun ℓ hℓ => ?_, hops', hrun, hfin, by rw [hy, hr']⟩
  rcases List.mem_cons.1 hℓ with rfl | h
  · rfl
  · exact hγ ℓ h

/-- If a process decides in an execution that leaves the memory in its initial state, another
process with another input can run solo afterwards and decide its own input: contradiction. -/
lemma cons_false_of_silent {π : P → Equiv.Perm ι} (H : ConsOK I π) (hall : ∀ p x, I.allowed p x)
    {p : P} {α : List (Label P (MCons Val))} {C : Config _ _ P L}
    (hα : (I.unnamed π).run α = some C) (hlab : ∀ ℓ ∈ α, ℓ.proc = p) (hos : OneShot α)
    (hmem : C.mem = fun _ => v₀) {r : Val} (hout : outputs α p = some r) {p' : P} (hp' : p' ≠ p)
    {x' : Val} (hx' : x' ≠ r) : False := by
  set J := I.unnamed π
  obtain ⟨β, D, hβ, hops, hrun, -, hout'⟩ := cons_solo_run H hall p' x'
  have hag : AgreeOn {p'} J.initCfg C :=
    (I.agreeOn_init_of_silent π hα hmem (fun ℓ hℓ h => hp' (h.symm.trans (hlab ℓ hℓ)))).symm
  obtain ⟨D', hD', -⟩ := runFrom_agreeOn hag (fun ℓ hℓ => by simp [hβ ℓ hℓ]) hrun
  have hrun' : J.run (α ++ β) = some D' := by rw [run, runFrom_append]; rw [run] at hα; rw [hα]; exact hD'
  have hαp' : ∀ ℓ ∈ α, ℓ.proc ≠ p' := fun ℓ hℓ h => hp' (h.symm.trans (hlab ℓ hℓ))
  have hos' : OneShot (α ++ β) := by
    intro s
    rw [opsOf_append, hops s]
    by_cases hs : s = p'
    · subst hs; simp [opsOf_eq_nil_of_proc_ne hαp']
    · simpa [hs] using hos s
  have h1 : outputs (α ++ β) p = some r := by
    rw [outputs_append_of_ne_none _ (by simp [hout]), hout]
  have h2 : outputs (α ++ β) p' = some x' := by
    rw [outputs_append, outputs_eq_none_of_proc_ne hαp', hout']; rfl
  exact hx' ((H.1 _ ⟨D', hrun'⟩ hos').1 p p' r x' h1 h2).symm

/-- Every process, invoking `x` and running solo from the initial memory, reads until it
writes (the paper: "a process that runs alone must write at least once before it decides"). -/
lemma cons_must_write (H : ConsOK I (fun _ => 1)) (hall : ∀ p x, I.allowed p x) {a b : Val}
    (hab : a ≠ b) (h2 : ∀ p : P, ∃ p', p' ≠ p) (p : P) (x : Val) :
    ∃ j, (∀ t < j, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (I.locInit p) x))) ∧
      I.IsWrite p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) x)) := by
  classical
  obtain ⟨j, hr, hw | ⟨r, l', hret⟩⟩ := I.unnamed_blind_cases (fun _ => 1) H.2 p x (hall p x)
  · exact ⟨j, hr, hw⟩
  · exfalso
    have hrun := I.unnamed_run_silent (fun _ => 1) (hall p x) hr hret
    set α : List (Label P (MCons Val)) := (.inv p x :: List.replicate j (.tau p)) ++ [.ret p r]
    have hlab : ∀ ℓ ∈ α, ℓ.proc = p := by
      intro ℓ hℓ
      simp only [α, List.mem_append, List.mem_cons, List.mem_replicate] at hℓ
      rcases hℓ with (rfl | ⟨-, rfl⟩) | rfl | h <;> first | rfl | simp at h
    have hops : ∀ s, opsOf α s = if s = p then [x] else [] := by
      intro s
      have hrep : opsOf (List.replicate j (Label.tau p : Label P (MCons Val))) s = [] := by
        simp only [opsOf, List.filterMap_eq_nil_iff]
        intro ℓ hℓ; rw [List.eq_of_mem_replicate hℓ]; rfl
      simp only [α, opsOf_append, opsOf_cons, hrep]
      by_cases h : s = p
      · subst h; simp [Label.invOf, opsOf]
      · simp [Label.invOf, Ne.symm h, h, opsOf]
    have hos : OneShot α := fun s => by rw [hops s]; split_ifs <;> simp
    have hout : outputs α p = some r := by
      have hrep : respsOf (List.replicate j (Label.tau p : Label P (MCons Val))) p = [] := by
        simp only [respsOf, List.filterMap_eq_nil_iff]
        intro ℓ hℓ; rw [List.eq_of_mem_replicate hℓ]; rfl
      rw [show α = ([.inv p x] ++ List.replicate j (.tau p)) ++ [.ret p r] from rfl]
      simp only [outputs, respsOf_append, hrep]
      simp [respsOf, Label.retOf]
    obtain ⟨p', hp'⟩ := h2 p
    have hx' : (if r = a then b else a) ≠ r := by
      split_ifs with h
      · rw [h]; exact Ne.symm hab
      · exact Ne.symm h
    exact cons_false_of_silent H hall hrun hlab hos rfl hout hp' hx'


/-- The core of Theorem 6.3: if for every register set `W` there are `|W|` processes besides any
given one (and at least two processes), no read/write algorithm is one-shot obstruction-free
consensus under every numbering of the unnamed registers. -/
theorem consensus_impossible (I : Impl (MCons Val) (RegFamily ι V v₀) P L)
    (hall : ∀ p x, I.allowed p x) {a b : Val} (hab : a ≠ b) (h2 : ∃ p p' : P, p ≠ p')
    (hP : ∀ (q : P) (W : Finset ι), ∃ ps : List P, ps.Nodup ∧ q ∉ ps ∧ ps.length = W.card) :
    ¬ ∀ π, ConsOK I π := by
  intro H
  obtain ⟨q, q', hqq'⟩ := h2
  have h2' : ∀ p : P, ∃ p', p' ≠ p := fun p => by
    by_cases h : q = p
    · exact ⟨q', h ▸ hqq'.symm⟩
    · exact ⟨q, h⟩
  have hw := cons_must_write (H fun _ => 1) hall hab h2'
  -- `q` runs alone with input `a` and decides `a`
  obtain ⟨y, Cy, hyq, hyops, hy, -, hyout⟩ := cons_solo_run (H fun _ => 1) hall q a
  have hosy : OneShot y := fun s => by rw [hyops s]; split_ifs <;> simp
  obtain ⟨W, hW⟩ := runFrom_exists_finset _ hy
  have hW' : ∀ i ∉ W, Cy.mem i = v₀ := fun i hi => hW i hi
  by_cases hW0 : W = ∅
  · exact cons_false_of_silent (H fun _ => 1) hall hy hyq hosy
      (funext fun i => hW' i (by simp [hW0])) hyout hqq'.symm hab.symm
  obtain ⟨ps, hnd, hqps, hlen⟩ := hP q W
  obtain ⟨π, -, x, bw, C, D, hlab, hops, hresps, hC, hD, hag, hDq, -⟩ :=
    covering_construction q hyq hy W hW' ps hnd hqps hlen (fun _ => b) (fun p => hall p b)
      (fun p => hw p b)
  have hps : ps ≠ [] := by
    intro h; rw [h] at hlen; exact hW0 (Finset.card_eq_zero.1 hlen.symm)
  set p₀ := ps.head hps
  have hp₀ : p₀ ∈ ps := List.head_mem hps
  have hp₀q : p₀ ≠ q := fun h => hqps (h ▸ hp₀)
  set J := I.unnamed π
  have hos₁ : OneShot (x ++ bw) := fun s => by rw [hops s]; split_ifs <;> simp
  obtain ⟨γ, E, hγ, hγops, hE, hEp⟩ := solo_from (H π).2 hC hos₁ p₀
  -- without `q`: `p₀` decides `b`
  have hρ' : J.run (x ++ bw ++ γ) = some E := by rw [run, runFrom_append]; rw [run] at hC; rw [hC]; exact hE
  have hopsρ' : ∀ s, opsOf (x ++ bw ++ γ) s = if s ∈ ps then [b] else [] := fun s => by
    rw [opsOf_append, hops s, hγops s, List.append_nil]
  have hosρ' : OneShot (x ++ bw ++ γ) := fun s => by rw [hopsρ' s]; split_ifs <;> simp
  obtain ⟨r₀, hr₀⟩ := Option.ne_none_iff_exists'.1
    (J.outputs_ne_none_of_run hρ' (p := p₀) (by simp only [hopsρ' p₀, hp₀, ↓reduceIte]; simp) hEp)
  have hr₀b : r₀ = b := by
    obtain ⟨s, hs⟩ := ((H π).1 _ ⟨E, hρ'⟩ hosρ').2 p₀ r₀ hr₀
    change (opsOf (x ++ bw ++ γ) s).head? = some r₀ at hs
    rw [hopsρ' s] at hs
    split_ifs at hs <;> simp_all
  -- with `q` inserted before the block write
  obtain ⟨E', hE', -⟩ := runFrom_agreeOn hag (fun ℓ hℓ => by
    show ℓ.proc ∈ ps; rw [hγ ℓ hℓ]; exact hp₀) hE
  have hρ : J.run (x ++ y ++ bw ++ γ) = some E' := by
    rw [run, runFrom_append]; rw [run] at hD; rw [hD]; exact hE'
  have hxq : ∀ ℓ ∈ x, ℓ.proc ≠ q := fun ℓ hℓ h => hqps (h ▸ hlab ℓ (by simp [hℓ]))
  have hbq : ∀ ℓ ∈ bw, ℓ.proc ≠ q := fun ℓ hℓ h => hqps (h ▸ hlab ℓ (by simp [hℓ]))
  have hγq : ∀ ℓ ∈ γ, ℓ.proc ≠ q := fun ℓ hℓ h => hp₀q (by rw [← h, hγ ℓ hℓ])
  have hyp₀ : ∀ ℓ ∈ y, ℓ.proc ≠ p₀ := fun ℓ hℓ h => hp₀q (by rw [← h, hyq ℓ hℓ])
  have hosρ : OneShot (x ++ y ++ bw ++ γ) := by
    intro s
    by_cases hs : s = q
    · subst hs
      simp only [opsOf_append, opsOf_eq_nil_of_proc_ne hxq, opsOf_eq_nil_of_proc_ne hbq,
        opsOf_eq_nil_of_proc_ne hγq, hyops]
      simp
    · have : ∀ ℓ ∈ y, ℓ.proc ≠ s := fun ℓ hℓ h => hs (by rw [← h, hyq ℓ hℓ])
      rw [List.append_assoc (x ++ y) bw γ, opsOf_append_middle this, ← List.append_assoc]
      exact hosρ' s
  have h1 : outputs (x ++ y ++ bw ++ γ) q = some a := by
    rw [← hyout]
    simp only [outputs, respsOf_append, respsOf_eq_nil_of_proc_ne hxq,
      respsOf_eq_nil_of_proc_ne hbq, respsOf_eq_nil_of_proc_ne hγq, List.nil_append,
      List.append_nil]
  have h2 : outputs (x ++ y ++ bw ++ γ) p₀ = some b := by
    rw [← hr₀b, ← hr₀]
    simp only [outputs]
    rw [List.append_assoc (x ++ y) bw γ, respsOf_append_middle hyp₀, ← List.append_assoc]
  exact hab (((H π).1 _ ⟨E', hρ⟩ hosρ).1 q p₀ a b h1 h2)

/-- **Theorem 6.3 (1)** of [Taubenfeld, PODC 2017]. There is no obstruction-free consensus
algorithm using (any number of) unnamed registers when the number of processes is not a priori
known: for an unbounded set `P` of potential participants, every read/write algorithm fails
agreement, validity or (one-shot) obstruction-freedom for some numbering `π` of the registers. -/
theorem theorem_6_3_1 [Infinite P] (I : Impl (MCons Val) (RegFamily ι V v₀) P L)
    (hall : ∀ p x, I.allowed p x) {a b : Val} (hab : a ≠ b) :
    ∃ π, ¬ ((I.unnamed π).Solves (consensus P Val) ∧ (I.unnamed π).OneShotOF) := by
  by_contra h
  push Not at h
  obtain ⟨p, p', hpp'⟩ := exists_pair_ne P
  exact consensus_impossible I hall hab ⟨p, p', hpp'⟩ exists_ps_of_infinite fun π => h π

/-- **Theorem 6.3 (2)** of [Taubenfeld, PODC 2017]. There is no obstruction-free consensus
algorithm for `n ≥ 2` processes using `n − 1` unnamed registers (or fewer). -/
theorem theorem_6_3_2 [Fintype P] [Fintype ι] (I : Impl (MCons Val) (RegFamily ι V v₀) P L)
    (hn : 2 ≤ Fintype.card P) (hm : Fintype.card ι ≤ Fintype.card P - 1)
    (hall : ∀ p x, I.allowed p x) {a b : Val} (hab : a ≠ b) :
    ∃ π, ¬ ((I.unnamed π).Solves (consensus P Val) ∧ (I.unnamed π).OneShotOF) := by
  by_contra h
  push Not at h
  obtain ⟨p, p', hpp'⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card P)
  exact consensus_impossible I hall hab ⟨p, p', hpp'⟩ (exists_ps_of_card_lt (by omega))
    fun π => h π

end Podc.MemoryAnonymousCoordination
