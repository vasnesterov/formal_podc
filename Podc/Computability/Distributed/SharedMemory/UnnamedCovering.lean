/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

import Podc.Computability.Distributed.SharedMemory.Unnamed
import Cslib.Computability.Distributed.SharedMemory.Task
import Mathlib.GroupTheory.Perm.Basic

/-!
# Covering arguments with unnamed registers

The covering argument of Taubenfeld (PODC 2017, Section 6) for unnamed registers. Since every
register initially holds `v₀`, a process running solo from the initial memory reads `v₀` until
its first write, whatever its numbering of the registers is (`blindStep`). The adversary may thus
choose the numbering of a process so that its first write goes to *any* given physical register.
Hence a set of `|W|` fresh processes can be made to cover any finite set `W` of registers, with
no write before the block write (`covering_construction`).

## Main definitions

* `Impl.blindStep I p l`: the local state of `p` after reading `v₀` (if its next action is a
  read).
* `Impl.IsRead`, `Impl.IsWrite`: the next action of `p` is a read / a write.

## Main results

* `Impl.unnamed_blind_cases`: under one-shot obstruction-freedom, a process running solo from the
  initial memory performs only reads until it either writes or returns (`blindRun_valid`).
* `Impl.agreeOn_init_of_silent`: after an execution that leaves the memory in its initial state,
  any process that has not taken a step cannot distinguish the configuration from the initial one.
* `Impl.covering_construction`: if `q`'s execution `y` changes only registers in `W`, and every
  process writes before returning when running solo from the initial memory, then for some
  numbering a list `ps` of `|W|` other processes can run (reads only) to cover `W`; after their
  block write, the executions with and without `y` are indistinguishable to `ps`.

CSLib candidate.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} {v₀ : V}

namespace Impl

variable (I : Impl A (RegFamily ι V v₀) P L)

/-- The next action of `p` in local state `l` is a read. -/
def IsRead (p : P) (l : L) : Prop := ∃ i k, I.act p l = .access i .read k

/-- The next action of `p` in local state `l` is a write. -/
def IsWrite (p : P) (l : L) : Prop := ∃ i v k, I.act p l = .access i (.write v) k

/-- The local state of `p` after reading `v₀` (unchanged if its next action is not a read). -/
def blindStep (p : P) (l : L) : L :=
  match I.act p l with
  | .access _ .read k => k v₀
  | _ => l

lemma blindStep_of_read {p : P} {l : L} {i : ι} {k : V → L}
    (h : I.act p l = .access i .read k) : I.blindStep p l = k v₀ := by
  simp [blindStep, h]

variable [DecidableEq P] [DecidableEq ι] (π : P → Equiv.Perm ι)

/-- A read step of `p` in a memory where every register holds `v₀`. -/
lemma unnamed_step_read {C : Config A (RegFamily ι V v₀) P L} {p : P}
    (hmem : C.mem = fun _ => v₀) (hpend : C.pend p ≠ none) (hr : I.IsRead p (C.loc p)) :
    (I.unnamed π).step C (.tau p) =
      some { C with loc := Function.update C.loc p (I.blindStep p (C.loc p)) } := by
  obtain ⟨i, k, hk⟩ := hr
  rw [I.blindStep_of_read hk]
  simp only [step, hpend, ↓reduceIte, I.unnamed_act_access π hk]
  simp only [Function.update_eq_self, hmem]

/-- `j` reads of `p` from a memory where every register holds `v₀`. -/
lemma unnamed_runFrom_reads {C : Config A (RegFamily ι V v₀) P L} {p : P}
    (hmem : C.mem = fun _ => v₀) (hpend : C.pend p ≠ none) (j : ℕ)
    (hr : ∀ t < j, I.IsRead p ((I.blindStep p)^[t] (C.loc p))) :
    (I.unnamed π).runFrom C (List.replicate j (.tau p)) =
      some { C with loc := Function.update C.loc p ((I.blindStep p)^[j] (C.loc p)) } := by
  induction j generalizing C with
  | zero => simp
  | succ j ih =>
    have hr' : ∀ t < j, I.IsRead p ((I.blindStep p)^[t]
        (({ C with loc := Function.update C.loc p (I.blindStep p (C.loc p)) } :
          Config A (RegFamily ι V v₀) P L).loc p)) := by
      intro t ht
      have := hr (t + 1) (by omega)
      rw [Function.iterate_succ_apply] at this
      simpa using this
    rw [List.replicate_succ, runFrom_cons,
      I.unnamed_step_read π hmem hpend (by simpa using hr 0 (by omega)), Option.bind_some,
      ih (C := { C with loc := Function.update C.loc p (I.blindStep p (C.loc p)) }) hmem hpend hr']
    simp only [Function.update_self, Function.update_idem]
    rw [← Function.iterate_succ_apply]

/-- Invocation followed by `j` reads, from a memory where every register holds `v₀`. -/
lemma unnamed_runFrom_invReads {C : Config A (RegFamily ι V v₀) P L} {p : P} {o : A.Op}
    (hmem : C.mem = fun _ => v₀) (hpend : C.pend p = none) (hall : I.allowed p o) (j : ℕ)
    (hr : ∀ t < j, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (C.loc p) o))) :
    (I.unnamed π).runFrom C (.inv p o :: List.replicate j (.tau p)) =
      some { C with loc := Function.update C.loc p ((I.blindStep p)^[j] (I.invoke p (C.loc p) o)),
                    pend := Function.update C.pend p (some o) } := by
  have h1 := I.unnamed_runFrom_reads π (p := p)
    (C := ⟨Function.update C.loc p (I.invoke p (C.loc p) o), Function.update C.pend p (some o),
      C.mem⟩) hmem (by simp) j (by simpa using hr)
  rw [runFrom_cons, step_inv_eq_some hpend (by simpa using hall), Option.bind_some]
  simp only [unnamed_invoke] at h1 ⊢
  rw [h1]
  simp


/-- A solo step of a reading process in a memory where every register holds `v₀`. -/
lemma unnamed_soloStep_read {C : Config A (RegFamily ι V v₀) P L} {p : P}
    (hmem : C.mem = fun _ => v₀) (hpend : C.pend p ≠ none) (hr : I.IsRead p (C.loc p)) :
    (I.unnamed π).soloStep p C =
      { C with loc := Function.update C.loc p (I.blindStep p (C.loc p)) } := by
  have hnl : (I.unnamed π).nextLabel C p = .tau p := by
    obtain ⟨i, k, hk⟩ := hr
    simp [nextLabel, I.unnamed_act_access π hk]
  simp [soloStep, hpend, hnl, I.unnamed_step_read π hmem hpend hr]

/-- **Solo runs from the initial memory.** Under one-shot obstruction-freedom, a process that
invokes `o` and runs solo from a configuration with the initial memory performs reads (of `v₀`)
until its next action is a write or a return. -/
lemma unnamed_blind_cases_of_fin (p : P) (o : A.Op) (hall : I.allowed p o)
    (hfin : ∀ C₁, (I.unnamed π).run [.inv p o] = some C₁ →
      ∃ K, (((I.unnamed π).soloStep p)^[K] C₁).pend p = none) :
    ∃ j, (∀ t < j, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (I.locInit p) o))) ∧
      (I.IsWrite p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) o)) ∨
        ∃ r l', I.act p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) o)) = .ret r l') := by
  classical
  set l := I.invoke p (I.locInit p) o with hl
  set J := I.unnamed π
  set C₁ : Config A (RegFamily ι V v₀) P L :=
    ⟨Function.update I.locInit p l, Function.update (fun _ => none) p (some o), fun _ => v₀⟩
  have hC₁ : J.run [.inv p o] = some C₁ := by
    simp only [run, runFrom_cons, runFrom_nil, J, unnamed_initCfg]
    rw [step_inv_eq_some (by rfl) (by simpa using hall)]
    simp [C₁, l]
  obtain ⟨K, hK⟩ := hfin C₁ hC₁
  have hex : ∃ t, ¬ I.IsRead p ((I.blindStep p)^[t] l) := by
    by_contra hall'
    push Not at hall'
    have key : ∀ t, (J.soloStep p)^[t] C₁ =
        { C₁ with loc := Function.update C₁.loc p ((I.blindStep p)^[t] l) } := by
      intro t
      induction t with
      | zero => simp [C₁]
      | succ t ih =>
        rw [Function.iterate_succ_apply', ih, I.unnamed_soloStep_read π rfl (by simp [C₁])
          (by simpa using hall' t)]
        simp [Function.iterate_succ_apply']
    rw [key K] at hK
    simp [C₁] at hK
  refine ⟨Nat.find hex, fun t ht => by simpa using Nat.find_min hex ht, ?_⟩
  have hnr := Nat.find_spec hex
  rcases hact : I.act p ((I.blindStep p)^[Nat.find hex] l) with ⟨i, o', k⟩ | ⟨r, l'⟩
  · cases o' with
    | read => exact absurd ⟨i, k, hact⟩ hnr
    | write v => exact Or.inl ⟨i, v, k, hact⟩
  · exact Or.inr ⟨r, l', rfl⟩

/-- **Solo runs from the initial memory.** Under one-shot obstruction-freedom, a process that
invokes `o` and runs solo from the initial configuration performs reads (of `v₀`) until its next
action is a write or a return. -/
lemma unnamed_blind_cases (hof : (I.unnamed π).OneShotOF) (p : P) (o : A.Op)
    (hall : I.allowed p o) :
    ∃ j, (∀ t < j, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (I.locInit p) o))) ∧
      (I.IsWrite p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) o)) ∨
        ∃ r l', I.act p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) o)) = .ret r l') := by
  refine I.unnamed_blind_cases_of_fin π p o hall fun C₁ hC₁ => ?_
  have hos : OneShot ([.inv p o] : List (Label P A)) := by
    intro r
    by_cases h : r = p
    · simp [opsOf, Label.invOf, h]
    · simp [opsOf, Label.invOf, Ne.symm h]
  refine hof _ C₁ p hC₁ hos ?_
  simp only [run, runFrom_cons, runFrom_nil] at hC₁
  rw [step_inv_eq_some rfl (by simpa using hall)] at hC₁
  simp only [Option.bind_some, Option.some.injEq] at hC₁
  rw [← hC₁]; simp

/-- A *silent* solo run: invoke, read `j` times, return. The memory is unchanged and every
other process is still in its initial state. -/
lemma unnamed_run_silent {p : P} {o : A.Op} (hall : I.allowed p o) {j : ℕ}
    (hr : ∀ t < j, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (I.locInit p) o)))
    {r : A.Resp} {l' : L} (hret : I.act p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) o)) = .ret r l') :
    (I.unnamed π).run ((.inv p o :: List.replicate j (.tau p)) ++ [.ret p r]) =
      some ⟨Function.update I.locInit p l', fun _ => none, fun _ => v₀⟩ := by
  have h1 := I.unnamed_runFrom_invReads π (C := (I.unnamed π).initCfg) (p := p) (o := o) rfl rfl
    (by simpa using hall) j (by simpa using hr)
  rw [run, runFrom_append, h1, Option.bind_some, runFrom_singleton,
    step_ret_eq_some (by simp) (by simpa using I.unnamed_act_ret π hret)]
  simp only [unnamed_initCfg, Function.update_idem]
  congr 2
  funext r'
  by_cases h : r' = p <;> simp [h]

/-- After an execution that leaves the memory in its initial state and in which `q` takes no
step, `q` cannot distinguish the configuration from the initial one. -/
lemma agreeOn_init_of_silent {C : Config A (RegFamily ι V v₀) P L} {α : List (Label P A)}
    (h : (I.unnamed π).run α = some C) (hmem : C.mem = fun _ => v₀) {q : P}
    (hq : ∀ ℓ ∈ α, ℓ.proc ≠ q) : AgreeOn {q} C (I.unnamed π).initCfg := by
  have := (I.unnamed π).runFrom_other h hq
  refine ⟨hmem, fun r hr => ?_, fun r hr => ?_⟩
  · rw [Set.mem_singleton_iff.1 hr]; exact this.1
  · rw [Set.mem_singleton_iff.1 hr]; exact this.2


omit [DecidableEq ι] in
variable {π} in
/-- The labels of `ps`'s read phases: each `p ∈ ps` in turn invokes `o p` and reads `j p` times. -/
def phases (o : P → A.Op) (j : P → ℕ) (ps : List P) : List (Label P A) :=
  ps.flatMap fun p => .inv p (o p) :: List.replicate (j p) (.tau p)

omit [DecidableEq ι] in
lemma proc_mem_of_mem_phases {o : P → A.Op} {j : P → ℕ} {ps : List P} {ℓ : Label P A}
    (h : ℓ ∈ phases o j ps) : ℓ.proc ∈ ps := by
  simp only [phases, List.mem_flatMap, List.mem_cons, List.mem_replicate] at h
  obtain ⟨p, hp, rfl | ⟨-, rfl⟩⟩ := h <;> exact hp

omit [DecidableEq ι] in
lemma opsOf_phases (o : P → A.Op) (j : P → ℕ) {ps : List P} (hnd : ps.Nodup) (r : P) :
    opsOf (phases o j ps) r = if r ∈ ps then [o r] else [] := by
  induction ps with
  | nil => simp [phases]
  | cons p ps ih =>
    have hrest : opsOf (phases o j ps) r = if r ∈ ps then [o r] else [] :=
      ih (List.nodup_cons.1 hnd).2
    have e : phases o j (p :: ps) = (.inv p (o p) :: List.replicate (j p) (.tau p)) ++
        phases o j ps := by simp [phases]
    rw [e, opsOf_append, hrest]
    have hrep : opsOf (List.replicate (j p) (Label.tau p : Label P A)) r = [] := by
      simp only [opsOf, List.filterMap_eq_nil_iff]
      intro ℓ hℓ; rw [List.eq_of_mem_replicate hℓ]; rfl
    have hp : p ∉ ps := (List.nodup_cons.1 hnd).1
    rw [opsOf_cons, hrep]
    by_cases hr : r = p
    · subst hr; simp [Label.invOf, hp]
    · simp [Label.invOf, Ne.symm hr, hr]

omit [DecidableEq ι] in
lemma respsOf_phases (o : P → A.Op) (j : P → ℕ) (ps : List P) (r : P) :
    respsOf (phases o j ps) r = [] := by
  simp only [respsOf, List.filterMap_eq_nil_iff]
  intro ℓ hℓ
  simp only [phases, List.mem_flatMap, List.mem_cons, List.mem_replicate] at hℓ
  obtain ⟨p, -, rfl | ⟨-, rfl⟩⟩ := hℓ <;> rfl

/-- The read phases of distinct processes, from the initial memory: afterwards every `p ∈ ps` is
pending with local state `(blindStep p)^[j p] (invoke …)`, and the memory is unchanged. -/
lemma unnamed_runFrom_phases (o : P → A.Op) (j : P → ℕ) (hall : ∀ p, I.allowed p (o p))
    (hr : ∀ p, ∀ t < j p, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (I.locInit p) (o p)))) :
    ∀ (ps : List P), ps.Nodup → ∀ C : Config A (RegFamily ι V v₀) P L, C.mem = (fun _ => v₀) →
      (∀ p ∈ ps, C.loc p = I.locInit p ∧ C.pend p = none) →
      ∃ C', (I.unnamed π).runFrom C (phases o j ps) = some C' ∧ C'.mem = (fun _ => v₀) ∧
        (∀ p ∈ ps, C'.loc p = (I.blindStep p)^[j p] (I.invoke p (I.locInit p) (o p)) ∧
          C'.pend p = some (o p)) ∧
        (∀ r, r ∉ ps → C'.loc r = C.loc r ∧ C'.pend r = C.pend r) := by
  intro ps
  induction ps with
  | nil => intro _ C hmem _; exact ⟨C, rfl, hmem, by simp, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons p ps ih =>
    intro hnd C hmem hC
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hl, hpe⟩ := hC p (by simp)
    have h1 := I.unnamed_runFrom_invReads π (C := C) (p := p) (o := o p) hmem hpe (hall p) (j p)
      (by rw [hl]; exact hr p)
    set C₁ : Config A (RegFamily ι V v₀) P L :=
      { C with loc := Function.update C.loc p ((I.blindStep p)^[j p] (I.invoke p (C.loc p) (o p))),
               pend := Function.update C.pend p (some (o p)) }
    have hne : ∀ r ∈ ps, r ≠ p := fun r hr hrp => hp (hrp ▸ hr)
    obtain ⟨C', h2, hm', hin, hout⟩ := ih hnd' C₁ hmem (fun r hr => by
      simp only [C₁, Function.update_of_ne (hne r hr)]; exact hC r (by simp [hr]))
    refine ⟨C', ?_, hm', fun r hr => ?_, fun r hr => ?_⟩
    · have e : phases o j (p :: ps) = (.inv p (o p) :: List.replicate (j p) (.tau p)) ++
          phases o j ps := by simp [phases]
      rw [e, runFrom_append, h1, Option.bind_some, h2]
    · rcases List.mem_cons.1 hr with rfl | hr
      · rw [(hout r hp).1, (hout r hp).2]; simp [C₁, hl]
      · exact hin r hr
    · have hrp : r ≠ p := fun h => hr (by simp [h])
      rw [(hout r (fun h => hr (by simp [h]))).1, (hout r (fun h => hr (by simp [h]))).2]
      simp [C₁, hrp]


variable {I} in
/-- **The covering construction** (Taubenfeld, PODC 2017, proofs of Theorems 6.2, 6.3, 6.5).
Let `q` run `y` alone from the initial configuration (under the identity numbering of `q`),
changing only registers of `W`, and let `ps` be `|W|` other processes. If every process `p`,
invoking `o p` and running solo from the initial memory, reads until it writes, then there is a
numbering `π` (identity for `q`) and executions `x` (each `p ∈ ps` invokes `o p` and only reads)
and `b` (block write by `ps` covering `W`) such that `x ++ b` and `x ++ y ++ b` are
indistinguishable to all of `ps`, while `q` is in the state reached by `y`. -/
theorem covering_construction (q : P) {y : List (Label P A)} {Cy : Config A (RegFamily ι V v₀) P L}
    (hyq : ∀ ℓ ∈ y, ℓ.proc = q) (hy : (I.unnamed fun _ => 1).run y = some Cy)
    (W : Finset ι) (hW : ∀ i ∉ W, Cy.mem i = v₀)
    (ps : List P) (hnd : ps.Nodup) (hq : q ∉ ps) (hlen : ps.length = W.card)
    (o : P → A.Op) (hall : ∀ p, I.allowed p (o p))
    (hw : ∀ p, ∃ j, (∀ t < j, I.IsRead p ((I.blindStep p)^[t] (I.invoke p (I.locInit p) (o p)))) ∧
      I.IsWrite p ((I.blindStep p)^[j] (I.invoke p (I.locInit p) (o p)))) :
    ∃ π : P → Equiv.Perm ι, π q = 1 ∧ ∃ (x b : List (Label P A))
      (C D : Config A (RegFamily ι V v₀) P L),
      (∀ ℓ ∈ x ++ b, ℓ.proc ∈ ps) ∧ (∀ r, opsOf (x ++ b) r = if r ∈ ps then [o r] else []) ∧
      (∀ r, respsOf (x ++ b) r = []) ∧
      (I.unnamed π).run (x ++ b) = some C ∧ (I.unnamed π).run (x ++ y ++ b) = some D ∧
      AgreeOn {p | p ∈ ps} C D ∧ D.loc q = Cy.loc q ∧ D.pend q = Cy.pend q := by
  classical
  choose j hjr hjw using hw
  choose i v k hk using hjw
  set ws := W.toList with hws
  set cs := ps.zip ws with hcs
  have hlen' : ps.length = ws.length := by simp [hws, hlen]
  have hfst : cs.map Prod.fst = ps := by simp [hcs, List.map_fst_zip, hlen'.le]
  have hsnd : cs.map Prod.snd = ws := by simp [hcs, List.map_snd_zip, hlen'.ge]
  have huniq : ∀ r w w', (r, w) ∈ cs → (r, w') ∈ cs → w = w' := by
    intro r w w' h1 h2
    have := List.inj_on_of_nodup_map (hfst ▸ hnd : (cs.map Prod.fst).Nodup) h1 h2 rfl
    simpa using congrArg Prod.snd this
  let π : P → Equiv.Perm ι := fun r =>
    if h : ∃ w, (r, w) ∈ cs then Equiv.swap (i r) h.choose else 1
  have hπ : ∀ r w, (r, w) ∈ cs → π r (i r) = w := by
    intro r w hrw
    have h : ∃ w, (r, w) ∈ cs := ⟨w, hrw⟩
    simp only [π, h, ↓reduceDIte, Equiv.swap_apply_left]
    exact huniq r _ _ h.choose_spec hrw
  have hπq : π q = 1 := by
    have : ¬ ∃ w, (q, w) ∈ cs := fun ⟨w, hw⟩ => hq (hfst ▸ List.mem_map_of_mem (f := Prod.fst) hw)
    simp [π, this]
  set J := I.unnamed π
  -- the read phases
  obtain ⟨Cx, hx, hxm, hxin, hxout⟩ := I.unnamed_runFrom_phases π o j hall hjr ps hnd J.initCfg rfl
    (fun p _ => ⟨rfl, rfl⟩)
  -- `q`'s execution after the read phases
  have hyJ : J.run y = some Cy := by
    rw [← hy]
    exact I.unnamed_runFrom_congr (fun ℓ hℓ => by rw [hyq ℓ hℓ, hπq]) _
  have hagq : AgreeOn {q} J.initCfg Cx :=
    ⟨hxm.symm, fun r hr => by rw [Set.mem_singleton_iff.1 hr, (hxout q hq).1],
      fun r hr => by rw [Set.mem_singleton_iff.1 hr, (hxout q hq).2]⟩
  obtain ⟨Dy, hDy, hagy⟩ := runFrom_agreeOn hagq (fun ℓ hℓ => by simp [hyq ℓ hℓ]) hyJ
  have hyoth : ∀ r ∈ ps, Dy.loc r = Cx.loc r ∧ Dy.pend r = Cx.pend r := fun r hr =>
    J.runFrom_other hDy (fun ℓ hℓ h => hq (by rw [← hyq ℓ hℓ, h]; exact hr))
  -- covering
  have hcov : ∀ c ∈ cs, J.Covers Cx c.1 c.2 := by
    rintro ⟨r, w⟩ hc
    have hr : r ∈ ps := hfst ▸ List.mem_map_of_mem (f := Prod.fst) hc
    refine ⟨by simp [(hxin r hr).2], .write (v r), k r, ?_, register_write_overwrites _ _⟩
    rw [(hxin r hr).1, I.unnamed_act_access π (hk r), hπ r w hc]
  obtain ⟨C, D, hC, hD, hag⟩ := blockWrite_agreeOn (I := J) (Q := {p | p ∈ ps}) (by rw [hfst]; exact hnd)
    (fun c hc => by simpa using (hfst ▸ List.mem_map_of_mem (f := Prod.fst) hc : c.1 ∈ ps))
    hcov (fun r hr => (hyoth r hr).1.symm) (fun r hr => (hyoth r hr).2.symm)
    (fun w hw => by
      rw [hsnd] at hw
      have hwW : w ∉ W := by simpa [hws] using hw
      rw [hxm, ← hagy.mem]
      exact (hW w hwW).symm)
  rw [hfst] at hC hD
  set b := blockWrite (A := A) ps
  refine ⟨π, hπq, phases o j ps, b, C, D, ?_, ?_, ?_, ?_, ?_, hag, ?_, ?_⟩
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with h | h
    · exact proc_mem_of_mem_phases h
    · exact mem_blockWrite h
  · intro r
    have : opsOf b r = [] := by
      simp only [opsOf, List.filterMap_eq_nil_iff]
      intro ℓ hℓ; obtain ⟨p, rfl⟩ := blockWrite_tau ℓ hℓ; rfl
    rw [opsOf_append, opsOf_phases o j hnd, this, List.append_nil]
  · intro r
    have : respsOf b r = [] := by
      simp only [respsOf, List.filterMap_eq_nil_iff]
      intro ℓ hℓ; obtain ⟨p, rfl⟩ := blockWrite_tau ℓ hℓ; rfl
    rw [respsOf_append, respsOf_phases, this, List.append_nil]
  · rw [run, runFrom_append, hx, Option.bind_some, hC]
  · rw [run, runFrom_append, runFrom_append, hx, Option.bind_some, hDy, Option.bind_some, hD]
  · rw [(J.runFrom_other hD (q := q) (fun ℓ hℓ h => hq (by rw [← h]; exact mem_blockWrite hℓ))).1]
    exact (hagy.loc q rfl).symm
  · rw [(J.runFrom_other hD (q := q) (fun ℓ hℓ h => hq (by rw [← h]; exact mem_blockWrite hℓ))).2]
    exact (hagy.pend q rfl).symm


/-! ### Auxiliary facts on executions -/

section Aux

variable {B : ι → ObjSpec}

/-- A finite execution changes only finitely many base objects. -/
lemma runFrom_exists_finset (J : Impl A B P L) {C C' : Config A B P L} {α : List (Label P A)}
    (h : J.runFrom C α = some C') : ∃ s : Finset ι, ∀ i ∉ s, C'.mem i = C.mem i := by
  classical
  induction α generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; exact ⟨∅, fun _ _ => rfl⟩
  | cons ℓ α ih =>
    simp only [runFrom_cons] at h
    cases hs : J.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨s, hs'⟩ := ih h
      let T : Finset ι := if hh : ∃ i o k, J.act ℓ.proc (C.loc ℓ.proc) = .access i o k
        then {hh.choose} else ∅
      refine ⟨s ∪ T, fun i hi => ?_⟩
      simp only [Finset.mem_union, not_or] at hi
      rw [hs' i hi.1]
      rcases J.mem_of_step hs i with e | ⟨-, -, o, k, hact, -⟩
      · exact e
      · exfalso; apply hi.2
        have hh : ∃ i o k, J.act ℓ.proc (C.loc ℓ.proc) = .access i o k := ⟨i, o, k, hact⟩
        simp only [T, hh, ↓reduceDIte, Finset.mem_singleton]
        obtain ⟨o', k', h'⟩ := hh.choose_spec
        exact (Action.access.inj (hact.symm.trans h')).1

/-- Labels of a process that does not appear in the middle part of an execution. -/
lemma opsOf_append_middle {α β γ : List (Label P A)} {r : P} (h : ∀ ℓ ∈ β, ℓ.proc ≠ r) :
    opsOf (α ++ β ++ γ) r = opsOf (α ++ γ) r := by
  simp [opsOf_eq_nil_of_proc_ne h]

lemma respsOf_append_middle {α β γ : List (Label P A)} {r : P} (h : ∀ ℓ ∈ β, ℓ.proc ≠ r) :
    respsOf (α ++ β ++ γ) r = respsOf (α ++ γ) r := by
  simp [respsOf_eq_nil_of_proc_ne h]

/-- A process that invoked once and is no longer pending has an output. -/
lemma outputs_ne_none_of_run (J : Impl A B P L) {α : List (Label P A)} {C : Config A B P L}
    (h : J.run α = some C) {p : P} (hops : opsOf α p ≠ []) (hp : C.pend p = none) :
    outputs α p ≠ none := by
  rcases J.run_counts h p with ⟨-, hc⟩ | ⟨hc, -⟩
  · intro hn
    simp only [outputs, List.head?_eq_none_iff] at hn
    rw [hn] at hc
    exact hops (List.eq_nil_of_length_eq_zero hc)
  · exact absurd hp hc

end Aux

end Impl

end Cslib.SharedMemory
