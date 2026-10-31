import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth
import Cslib.Computability.Distributed.Byzantine.PartialSync.RunClasses
import Cslib.Foundations.Combinatorics.Labelling

/-!
# Reliable broadcast, non-equivocation, imitating adversaries

Clement, Junqueira, Kate, Rodrigues, *On the (Limited) Power of Non-Equivocation*, PODC 2012.

We work in CSLib's discrete-time Byzantine message-passing model
(`Cslib.Byzantine.PartialSync`): deterministic processes, authenticated point-to-point links,
runs given by the adversary's data (faulty set, inputs, Byzantine messages, delivery times).
The asynchronous model of the paper is `Run.AsyncValid f` (any finite delays); our impossibility
results are proved for the smaller classes `Run.Valid f δ` (partial synchrony with an arbitrary
known post-GST bound `δ`), which makes them stronger.

* `IsRBroadcast A s Adm`: Definition 1 (r-broadcast with sender `s`): L1, L2, S1, S2, S3 in
  every admissible run. The sender's message is its input `R.inp s`; a process *delivers* `v`
  when its decision is `v` (`Run.Decides`).
* Non-equivocation (Section 2.4): every message has a key (`key : M → κ`); a process never
  sends two different messages with the same key. `NonEquivocating key`: the faulty
  processes respect this; `RespectsNE A key`: correct processes do (the protocol uses
  the primitive as intended).
* `Imitating A`: every faulty process `q` sends, on each link and at each time, either nothing
  or exactly what `q` sends at that time in some run in which `q` is correct. Such a process only
  says what a correct process could say, so it never equivocates
  (`Imitating.nonEquivocating`) and never needs to forge anybody's authentication.
-/

set_option linter.unusedSectionVars false

namespace Podc.NonEquivocationLimits

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K κ : Type*} [DecidableEq P]

/-! ### Definition 1: reliable broadcast -/

/-- **Definition 1** (r-broadcast) with distinguished sender `s`, required in every run of `Adm`.
The sender r-broadcasts its input `R.inp s`; "`p` delivers `v`" is `R.Decides A p v`. -/
structure IsRBroadcast (A : Algorithm P M S V V) (s : P) (Adm : Set (Run P M V)) : Prop where
  /-- (L1) Sender termination: a correct sender delivers its own message. -/
  senderTermination : ∀ R ∈ Adm, s ∉ R.faulty → R.Decides A s (R.inp s)
  /-- (L2) Completeness: if a correct process delivers, every correct process delivers. -/
  completeness : ∀ R ∈ Adm, (∃ p ∉ R.faulty, ∃ v, R.Decides A p v) →
    ∀ q ∉ R.faulty, ∃ v, R.Decides A q v
  /-- (S1) Validity: with a correct sender, correct processes only deliver its message. -/
  validity : ∀ R ∈ Adm, s ∉ R.faulty → ∀ p ∉ R.faulty, ∀ v, R.Decides A p v → v = R.inp s
  /-- (S2) Agreement. -/
  agreement : ∀ R ∈ Adm, ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w,
    R.Decides A p v → R.Decides A q w → v = w
  /-- (S3) Integrity: a correct process delivers at most one message. -/
  integrity : ∀ R ∈ Adm, ∀ p ∉ R.faulty, ∀ v w, R.Decides A p v → R.Decides A p w → v = w

namespace IsRBroadcast

variable {A : Algorithm P M S V V} {s : P} {Adm Adm' : Set (Run P M V)}

/-- r-broadcast on a class of runs implies r-broadcast on every subclass. -/
theorem mono (h : IsRBroadcast A s Adm) (h' : Adm' ⊆ Adm) : IsRBroadcast A s Adm' where
  senderTermination R hR := h.senderTermination R (h' hR)
  completeness R hR := h.completeness R (h' hR)
  validity R hR := h.validity R (h' hR)
  agreement R hR := h.agreement R (h' hR)
  integrity R hR := h.integrity R (h' hR)

/-- If a correct process delivers `v`, every correct process delivers `v` (L2 + S2). -/
theorem all_decide (h : IsRBroadcast A s Adm) {R : Run P M V} (hR : R ∈ Adm) {p : P}
    (hp : p ∉ R.faulty) {v : V} (hv : R.Decides A p v) : ∀ q ∉ R.faulty, R.Decides A q v := by
  intro q hq
  obtain ⟨w, hw⟩ := h.completeness R hR ⟨p, hp, v, hv⟩ q hq
  rwa [h.agreement R hR p hp q hq v w hv hw]

/-- With a correct sender, every correct process delivers the sender's message (L1 + L2 + S2). -/
theorem all_decide_inp (h : IsRBroadcast A s Adm) {R : Run P M V} (hR : R ∈ Adm)
    (hs : s ∉ R.faulty) : ∀ q ∉ R.faulty, R.Decides A q (R.inp s) :=
  h.all_decide hR hs (h.senderTermination R hR hs)

end IsRBroadcast

/-- A common deadline for finitely many processes that all deliver `v`. -/
theorem exists_deadline [Fintype P] {A : Algorithm P M S V V} {R : Run P M V} (X : P → Prop)
    {v : V} (h : ∀ p, X p → R.Decides A p v) :
    ∃ T, ∀ p, X p → ∃ τ ≤ T, A.decide p (R.st A τ p) = some v := by
  classical
  choose! t ht using h
  refine ⟨univ.sup t, fun p hp => ⟨t p, le_sup (mem_univ p), ht p hp⟩⟩

/-! ### Non-equivocation and imitating adversaries -/

/-- A sending pattern `out τ p` (messages sent at time `τ` to `p`) is *non-equivocating* for the
key map `key`: two messages with the same key are equal (Section 2.4:
`valid_p(k, m) ∧ valid_p(k, m') → m = m'`), across all receivers and times. -/
def SendsConsistently (key : M → κ) (out : ℕ → P → List M) : Prop :=
  ∀ τ τ' p p', ∀ m ∈ out τ p, ∀ m' ∈ out τ' p', key m = key m' → m = m'

/-- The faulty processes of `R` cannot equivocate. -/
def NonEquivocating {VI : Type*} (key : M → κ) (R : Run P M VI) : Prop :=
  ∀ q ∈ R.faulty, SendsConsistently key (R.byz q)

/-- The algorithm uses the non-equivocation primitive as intended: in every run, a correct
process never sends two different messages with the same key. -/
def RespectsNE {VI VO : Type*} (A : Algorithm P M S VI VO) (key : M → κ) : Prop :=
  ∀ (R : Run P M VI) q, q ∉ R.faulty → SendsConsistently key (R.out A q)

/-- **Imitating adversary.** Every faulty process `q` sends, at every time and on every link,
either nothing or exactly what `q` sends there in some fixed run `R'` in which `q` is correct
(i.e. follows the protocol, with whatever it received in `R'`). -/
def Imitating {VI VO : Type*} (A : Algorithm P M S VI VO) (R : Run P M VI) : Prop :=
  ∀ q ∈ R.faulty, ∃ R' : Run P M VI, q ∉ R'.faulty ∧
    ∀ τ p, R.byz q τ p = [] ∨ R.byz q τ p = R'.out A q τ p

/-- An imitating faulty process does not equivocate if the protocol does not. -/
theorem Imitating.nonEquivocating {VI VO : Type*} {A : Algorithm P M S VI VO}
    {key : M → κ} (hA : RespectsNE A key) {R : Run P M VI} (hR : Imitating A R) :
    NonEquivocating key R := by
  intro q hq τ τ' p p' m hm m' hm' hk
  obtain ⟨R', hq', hR'⟩ := hR q hq
  rcases hR' τ p with h | h <;> rw [h] at hm
  · simp at hm
  rcases hR' τ' p' with h' | h' <;> rw [h'] at hm'
  · simp at hm'
  exact hA R' q hq' τ τ' p p' m hm m' hm' hk

/-! ### Splitting the processes into three groups -/

/-- If `3 ≤ n ≤ 3f`, the processes split into three nonempty groups `0, 1, 2` of size at most
`f`, with the sender `s` in group `0`. -/
theorem exists_three_groups [Fintype P] {f : ℕ} (s : P) (h3 : 3 ≤ Fintype.card P)
    (hf : Fintype.card P ≤ 3 * f) :
    ∃ g : P → Fin 3, g s = 0 ∧ (∀ i, ∃ p, g p = i) ∧ ∀ i, #{p | g p = i} ≤ f := by
  obtain ⟨g, hg, hc⟩ := Fintype.exists_fin_labelling_le (α := P) (k := 3) (t := f) univ
    (by simpa using h3) hf
  let e : Equiv.Perm (Fin 3) := Equiv.swap (g s) 0
  refine ⟨e ∘ g, by simp [e], fun i => ?_, fun i => ?_⟩
  · obtain ⟨p, hp⟩ := hg (e.symm i) (mem_univ _)
    exact ⟨p, by simp [hp]⟩
  · have : (univ.filter fun p => (e ∘ g) p = i) = univ.filter fun p => g p = e.symm i := by
      ext p; simp [Equiv.eq_symm_apply]
    rw [this]; exact hc _

end Podc.NonEquivocationLimits
