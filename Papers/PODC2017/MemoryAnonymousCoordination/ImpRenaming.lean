import Papers.PODC2017.MemoryAnonymousCoordination.ImpCommon
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Theorem 6.5: no obstruction-free adaptive perfect renaming with unnamed registers

Taubenfeld, *Coordination Without Prior Agreement*, PODC 2017, Section 6.4.

*Adaptive perfect renaming* (Section 5): every participating process that terminates acquires a
new name; names are distinct, and when `k` processes participate, the names are in `{1, …, k}`.
There is no obstruction-free algorithm for it using unnamed read/write registers (1) when the
number of processes is not a priori known (`theorem_6_5_1`), and (2) for `n ≥ 2` processes using
`n − 1` (or fewer) registers (`theorem_6_5_2`).
-/

open Cslib.SharedMemory Impl

namespace Podc.MemoryAnonymousCoordination

/-- The renaming object: invoking it (no input) returns the new name. A reducible copy of
`taskObj Unit ℕ`. -/
abbrev RenObj : ObjSpec where
  State := Unit
  Op := Unit
  Resp := ℕ
  init := ()
  δ _ _ := ((), default)

example : RenObj = taskObj Unit ℕ := rfl

/-- **Adaptive perfect renaming** (Section 5 of the paper): distinct new names, and every name
acquired is in `{1, …, k}` where `k` is the number of participating processes. -/
def adaptiveRenaming (P : Type) : Cslib.SharedMemory.Task P where
  In := Unit
  Out := ℕ
  Δ ins outs := (∀ p q a b, p ≠ q → outs p = some a → outs q = some b → a ≠ b) ∧
    ∀ p a, outs p = some a → 1 ≤ a ∧ a ≤ {q | ins q ≠ none}.ncard

instance {P : Type} : Inhabited (adaptiveRenaming P).Out := inferInstanceAs (Inhabited ℕ)

variable {ι V P L : Type} {v₀ : V} [DecidableEq P] [DecidableEq ι]
  {I : Impl RenObj (RegFamily ι V v₀) P L}

/-- `π` makes `I` a one-shot obstruction-free adaptive perfect renaming algorithm. -/
def RenOK (I : Impl RenObj (RegFamily ι V v₀) P L) (π : P → Equiv.Perm ι) : Prop :=
  (I.unnamed π).Solves (adaptiveRenaming P) ∧ (I.unnamed π).OneShotOF

lemma participants_eq {α : List (Label P RenObj)} (S : P → Prop) [DecidablePred S]
    (h : ∀ s, opsOf α s = if S s then [()] else []) :
    {q | inputs (A := RenObj) α q ≠ none} =
      {q | S q} := by
  ext s
  change (opsOf α s).head? ≠ none ↔ S s
  rw [h s]; split_ifs with hs <;> simp [hs]

/-- A process running solo from the initial configuration acquires the name `1`. -/
lemma ren_solo_run {π : P → Equiv.Perm ι} (H : RenOK I π) (hall : ∀ p, I.allowed p ()) (p : P) :
    ∃ β D, (∀ ℓ ∈ β, ℓ.proc = p) ∧ (∀ r, opsOf β r = if r = p then [()] else []) ∧
      (I.unnamed π).run β = some D ∧ outputs β p = some 1 := by
  set J := I.unnamed π
  obtain ⟨F, hF⟩ : ∃ F, J.run [.inv p ()] = some F :=
    ⟨_, by simp only [run, runFrom_cons, runFrom_nil]
           rw [step_inv_eq_some (I := J) rfl (by simpa [J] using hall p)]; rfl⟩
  have hos0 : OneShot ([.inv p ()] : List (Label P RenObj)) := by
    intro r; by_cases h : r = p
    · simp [opsOf, Label.invOf, h]
    · simp [opsOf, Label.invOf, Ne.symm h]
  obtain ⟨γ, D, hγ, hops, hr, hfin⟩ := solo_from H.2 hF hos0 p
  have hrun : J.run (.inv p () :: γ) = some D := by
    rw [show (.inv p () :: γ : List _) = [.inv p ()] ++ γ from rfl, run, runFrom_append]
    rw [run] at hF; rw [hF]; exact hr
  have hops' : ∀ r, opsOf (.inv p () :: γ) r = if r = p then [()] else [] := by
    intro r
    rw [opsOf_cons, hops r]
    by_cases h : r = p
    · simp [Label.invOf, h]
    · simp [Label.invOf, Ne.symm h, h]
  have hos : OneShot (.inv p () :: γ) := fun r => by rw [hops' r]; split_ifs <;> simp
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1
    (J.outputs_ne_none_of_run hrun (p := p) (by simp [hops']) hfin)
  have h1 := (H.1 _ ⟨D, hrun⟩ hos).2 p y hy
  change 1 ≤ y ∧ y ≤ {q | inputs (A := RenObj) (Label.inv p () :: γ) q ≠ none}.ncard at h1
  rw [participants_eq (· = p) hops', Set.ofPred_eq_eq_singleton, Set.ncard_singleton] at h1
  refine ⟨_, D, fun ℓ hℓ => ?_, hops', hrun, by rw [hy]; congr 1; exact le_antisymm h1.2 h1.1⟩
  rcases List.mem_cons.1 hℓ with rfl | h
  · rfl
  · exact hγ ℓ h

/-- If a process acquires a name in an execution that leaves the memory in its initial state,
another process can run solo afterwards and acquire the name `1` too. -/
lemma ren_false_of_silent {π : P → Equiv.Perm ι} (H : RenOK I π) (hall : ∀ p, I.allowed p ())
    {p : P} {α : List (Label P RenObj)} {C : Config _ _ P L}
    (hα : (I.unnamed π).run α = some C) (hlab : ∀ ℓ ∈ α, ℓ.proc = p)
    (hops : ∀ s, opsOf α s = if s = p then [()] else [])
    (hmem : C.mem = fun _ => v₀) {r : ℕ} (hout : outputs α p = some r) {p' : P}
    (hp' : p' ≠ p) : False := by
  set J := I.unnamed π
  have hos : OneShot α := fun s => by rw [hops s]; split_ifs <;> simp
  have hr1 : r = 1 := by
    have h1 := (H.1 _ ⟨C, hα⟩ hos).2 p r hout
    change 1 ≤ r ∧ r ≤ {q | inputs (A := RenObj) α q ≠ none}.ncard at h1
    rw [participants_eq (· = p) hops, Set.ofPred_eq_eq_singleton, Set.ncard_singleton] at h1
    omega
  obtain ⟨β, D, hβ, hopsβ, hrun, hout'⟩ := ren_solo_run H hall p'
  have hαp' : ∀ ℓ ∈ α, ℓ.proc ≠ p' := fun ℓ hℓ h => hp' (h.symm.trans (hlab ℓ hℓ))
  have hag : AgreeOn {p'} J.initCfg C := (I.agreeOn_init_of_silent π hα hmem hαp').symm
  obtain ⟨D', hD', -⟩ := runFrom_agreeOn hag (fun ℓ hℓ => by simp [hβ ℓ hℓ]) hrun
  have hrun' : J.run (α ++ β) = some D' := by
    rw [run, runFrom_append]; rw [run] at hα; rw [hα]; exact hD'
  have hos' : OneShot (α ++ β) := by
    intro s
    rw [opsOf_append, hopsβ s]
    by_cases hs : s = p'
    · subst hs; simp [opsOf_eq_nil_of_proc_ne hαp']
    · simpa [hs] using hos s
  have h1 : outputs (α ++ β) p = some 1 := by
    rw [outputs_append_of_ne_none _ (by simp [hout]), hout, hr1]
  have h2 : outputs (α ++ β) p' = some 1 := by
    rw [outputs_append, outputs_eq_none_of_proc_ne hαp', hout']; rfl
  exact ((H.1 _ ⟨D', hrun'⟩ hos').1 p p' 1 1 hp'.symm h1 h2) rfl

/-- Every process running solo from the initial memory reads until it writes ("a process that
runs alone must write at least once before it decides"). -/
lemma ren_must_write (H : RenOK I (fun _ => 1)) (hall : ∀ p, I.allowed p ())
    (h2 : ∀ p : P, ∃ p', p' ≠ p) (p : P) :
    ∃ j, (∀ t < j, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (I.locInit p) ()))) ∧
      I.IsWrite p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) ())) := by
  obtain ⟨j, hr, hw | ⟨r, l', hret⟩⟩ := I.unnamed_blind_cases (fun _ => 1) H.2 p () (hall p)
  · exact ⟨j, hr, hw⟩
  · exfalso
    have hrun := I.unnamed_run_silent (fun _ => 1) (hall p) hr hret
    set α : List (Label P RenObj) := (.inv p () :: List.replicate j (.tau p)) ++ [.ret p r]
    have hlab : ∀ ℓ ∈ α, ℓ.proc = p := by
      intro ℓ hℓ
      simp only [α, List.mem_append, List.mem_cons, List.mem_replicate] at hℓ
      rcases hℓ with (rfl | ⟨-, rfl⟩) | rfl | h <;> first | rfl | simp at h
    have hops : ∀ s, opsOf α s = if s = p then [()] else [] := by
      intro s
      have hrep : opsOf (List.replicate j (Label.tau p : Label P RenObj)) s = [] := by
        simp only [opsOf, List.filterMap_eq_nil_iff]
        intro ℓ hℓ; rw [List.eq_of_mem_replicate hℓ]; rfl
      simp only [α, opsOf_append, opsOf_cons, hrep]
      by_cases h : s = p
      · subst h; simp [Label.invOf, opsOf]
      · simp [Label.invOf, Ne.symm h, h, opsOf]
    have hout : outputs α p = some r := by
      have hrep : respsOf (List.replicate j (Label.tau p : Label P RenObj)) p = [] := by
        simp only [respsOf, List.filterMap_eq_nil_iff]
        intro ℓ hℓ; rw [List.eq_of_mem_replicate hℓ]; rfl
      rw [show α = ([.inv p ()] ++ List.replicate j (.tau p)) ++ [.ret p r] from rfl]
      simp only [outputs, respsOf_append, hrep]
      simp [respsOf, Label.retOf]
    obtain ⟨p', hp'⟩ := h2 p
    exact ren_false_of_silent H hall hrun hlab hops rfl hout hp'


/-- The core of Theorem 6.5 (cf. `consensus_impossible`). -/
theorem renaming_impossible (I : Impl RenObj (RegFamily ι V v₀) P L)
    (hall : ∀ p, I.allowed p ()) (h2 : ∃ p p' : P, p ≠ p')
    (hP : ∀ (q : P) (W : Finset ι), ∃ ps : List P, ps.Nodup ∧ q ∉ ps ∧ ps.length = W.card) :
    ¬ ∀ π, RenOK I π := by
  intro H
  obtain ⟨q, q', hqq'⟩ := h2
  have h2' : ∀ p : P, ∃ p', p' ≠ p := fun p => by
    by_cases h : q = p
    · exact ⟨q', h ▸ hqq'.symm⟩
    · exact ⟨q, h⟩
  have hw := ren_must_write (H fun _ => 1) hall h2'
  -- `q` runs alone and acquires the name `1`
  obtain ⟨y, Cy, hyq, hyops, hy, hyout⟩ := ren_solo_run (H fun _ => 1) hall q
  obtain ⟨W, hW⟩ := runFrom_exists_finset _ hy
  have hW' : ∀ i ∉ W, Cy.mem i = v₀ := fun i hi => hW i hi
  by_cases hW0 : W = ∅
  · exact ren_false_of_silent (H fun _ => 1) hall hy hyq hyops
      (funext fun i => hW' i (by simp [hW0])) hyout hqq'.symm
  obtain ⟨ps, hnd, hqps, hlen⟩ := hP q W
  obtain ⟨π, -, x, bw, C, D, hlab, hops, hresps, hC, hD, hag, -, -⟩ :=
    covering_construction q hyq hy W hW' ps hnd hqps hlen (fun _ => ()) (fun p => hall p) hw
  have hps : ps ≠ [] := by
    intro h; rw [h] at hlen; exact hW0 (Finset.card_eq_zero.1 hlen.symm)
  set J := I.unnamed π
  have hos₁ : OneShot (x ++ bw) := fun s => by rw [hops s]; split_ifs <;> simp
  -- without `q`: all of `ps` finish, one of them with the name `1`
  obtain ⟨γ, E, hγ, hγops, hE, hfin, -⟩ := J.exists_finish (E := OneShot) (H π).2
    (fun _ _ h h' => h.append_of_opsOf_nil h') ps hC hos₁
  have hρ' : J.run (x ++ bw ++ γ) = some E := by
    rw [run, runFrom_append]; rw [run] at hC; rw [hC]; exact hE
  have hopsρ' : ∀ s, opsOf (x ++ bw ++ γ) s = if s ∈ ps then [()] else [] := fun s => by
    rw [opsOf_append, hops s, hγops s, List.append_nil]
  have hosρ' : OneShot (x ++ bw ++ γ) := fun s => by rw [hopsρ' s]; split_ifs <;> simp
  have hout : ∀ p ∈ ps, ∃ a, outputs (x ++ bw ++ γ) p = some a := fun p hp =>
    Option.ne_none_iff_exists'.1
      (J.outputs_ne_none_of_run hρ' (p := p) (by simp only [hopsρ' p, hp, ↓reduceIte]; simp)
        (hfin p hp))
  obtain ⟨huniq, hrange⟩ := (H π).1 _ ⟨E, hρ'⟩ hosρ'
  have hpart : {s | inputs (A := RenObj) (x ++ bw ++ γ) s ≠ none}.ncard = ps.length := by
    rw [participants_eq (· ∈ ps) hopsρ']
    rw [show {s | s ∈ ps} = (ps.toFinset : Set P) by ext; simp, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hnd]
  let f : P → ℕ := fun p => (outputs (x ++ bw ++ γ) p).getD 0
  have hf : ∀ p ∈ ps, outputs (x ++ bw ++ γ) p = some (f p) := fun p hp => by
    obtain ⟨a, ha⟩ := hout p hp; simp only [f, ha, Option.getD_some]
  have himg : ps.toFinset.image f = Finset.Icc 1 ps.length := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      have := hrange p (f p) (hf p (List.mem_toFinset.1 hp))
      change 1 ≤ f p ∧ f p ≤ {s | inputs (A := RenObj) (x ++ bw ++ γ) s ≠ none}.ncard at this
      rw [hpart] at this
      exact Finset.mem_Icc.2 this
    · rw [Nat.card_Icc, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd]
      · omega
      · intro p hp p' hp' hpp
        by_contra hne
        exact huniq p p' (f p) (f p') hne (hf p (List.mem_toFinset.1 hp))
          (hf p' (List.mem_toFinset.1 hp')) hpp
  obtain ⟨p₀, hp₀, hp₀1⟩ : ∃ p ∈ ps.toFinset, f p = 1 := by
    have : 1 ∈ ps.toFinset.image f := by
      rw [himg, Finset.mem_Icc]
      exact ⟨le_rfl, List.length_pos_iff.2 hps⟩
    simpa using this
  rw [List.mem_toFinset] at hp₀
  have hp₀q : p₀ ≠ q := fun h => hqps (h ▸ hp₀)
  -- with `q` inserted before the block write
  obtain ⟨E', hE', -⟩ := runFrom_agreeOn hag (fun ℓ hℓ => hγ ℓ hℓ) hE
  have hρ : J.run (x ++ y ++ bw ++ γ) = some E' := by
    rw [run, runFrom_append]; rw [run] at hD; rw [hD]; exact hE'
  have hxq : ∀ ℓ ∈ x, ℓ.proc ≠ q := fun ℓ hℓ h => hqps (h ▸ hlab ℓ (by simp [hℓ]))
  have hbq : ∀ ℓ ∈ bw, ℓ.proc ≠ q := fun ℓ hℓ h => hqps (h ▸ hlab ℓ (by simp [hℓ]))
  have hγq : ∀ ℓ ∈ γ, ℓ.proc ≠ q := fun ℓ hℓ h => hqps (h ▸ hγ ℓ hℓ)
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
  have h1 : outputs (x ++ y ++ bw ++ γ) q = some 1 := by
    rw [← hyout]
    simp only [outputs, respsOf_append, respsOf_eq_nil_of_proc_ne hxq,
      respsOf_eq_nil_of_proc_ne hbq, respsOf_eq_nil_of_proc_ne hγq, List.nil_append,
      List.append_nil]
  have h2 : outputs (x ++ y ++ bw ++ γ) p₀ = some 1 := by
    rw [← hp₀1, ← hf p₀ hp₀]
    simp only [outputs]
    rw [List.append_assoc (x ++ y) bw γ, respsOf_append_middle hyp₀, ← List.append_assoc]
  exact ((H π).1 _ ⟨E', hρ⟩ hosρ).1 q p₀ 1 1 hp₀q.symm h1 h2 rfl

/-- **Theorem 6.5 (1)** of [Taubenfeld, PODC 2017]. There is no obstruction-free adaptive
perfect renaming algorithm using (any number of) unnamed registers when the number of processes
is not a priori known. -/
theorem theorem_6_5_1 [Infinite P] (I : Impl RenObj (RegFamily ι V v₀) P L)
    (hall : ∀ p, I.allowed p ()) :
    ∃ π, ¬ ((I.unnamed π).Solves (adaptiveRenaming P) ∧ (I.unnamed π).OneShotOF) := by
  by_contra h
  push Not at h
  obtain ⟨p, p', hpp'⟩ := exists_pair_ne P
  exact renaming_impossible I hall ⟨p, p', hpp'⟩ exists_ps_of_infinite fun π => h π

/-- **Theorem 6.5 (2)** of [Taubenfeld, PODC 2017]. There is no obstruction-free adaptive
perfect renaming algorithm for `n ≥ 2` processes using `n − 1` unnamed registers (or fewer). -/
theorem theorem_6_5_2 [Fintype P] [Fintype ι] (I : Impl RenObj (RegFamily ι V v₀) P L)
    (hn : 2 ≤ Fintype.card P) (hm : Fintype.card ι ≤ Fintype.card P - 1)
    (hall : ∀ p, I.allowed p ()) :
    ∃ π, ¬ ((I.unnamed π).Solves (adaptiveRenaming P) ∧ (I.unnamed π).OneShotOF) := by
  by_contra h
  push Not at h
  obtain ⟨p, p', hpp'⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card P)
  exact renaming_impossible I hall ⟨p, p', hpp'⟩ (exists_ps_of_card_lt (by omega)) fun π => h π

end Podc.MemoryAnonymousCoordination
