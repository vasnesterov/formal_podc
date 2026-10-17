import Papers.PODC2026.PartialAuthBC.Gradecast
import Cslib.Computability.Distributed.Byzantine.LockStep.Restrict
import Cslib.Computability.Distributed.Byzantine.LockStep.Sequential
import Mathlib

/-!
# The broadcast protocol Π_BC (Figure 2): Theorems 3.13 and 3.14

Π_BC runs Π_GC for `4s` rounds; then the unregistered parties `N = Regᶜ` run a black-box
unauthenticated Byzantine agreement protocol `ba` among themselves (on the complete graph of `N`)
with their gradecast values as inputs. Output rule: registered parties and unregistered parties with
grade `1` output their gradecast value (at round `4s`); unregistered parties with grade `0` output
the decision of `ba`. All parties keep participating in `ba` (registered parties stay silent).

Π_BC is built with the shared lock-step combinators: the sequential composition `Protocol.seq`
(`Cslib/Computability/Distributed/Byzantine/LockStep/Sequential.lean`) of Π_GC with the agreement phase `bcPhase2`, in which `ba` runs
among `N` through the committee simulation `Protocol.extend` (`Cslib/Computability/Distributed/Byzantine/LockStep/Restrict.lean`).
`bcWith` takes the gradecast protocol as a parameter (also used for the exclusive reading in
`Exclusive.lean`).

* `bc_send_decide`: the composed protocol, spelled out as in Figure 2.
* `bc_decides_*`: decisions of Π_BC in terms of the gradecast run `sc₁` and the `ba` run `sc₂`.
* `bc_bb_of_honest_reg`, `bc_bb_of_ba`: the two cases of Lemma 3.12 (and Lemma 3.11).
* `theorem313`: Π_BC solves Byzantine broadcast with a registered sender against
  `t ≤ s + ⌈(n - s)/3⌉ - 1` Byzantine parties, if `ba` solves unauthenticated BA among `N` against
  every Byzantine set `B` with `3|B| < |N|`.
* `theorem314`: if `n - s ≤ 2`, Π_BC with the "OR of the values" exchange (`orBA`) solves Byzantine
  broadcast with a registered sender against any number of Byzantine parties (Figure 4).
-/

namespace PartialAuthBC

open Cslib.Byzantine.LockStep

variable {P : Type}

/-- The unregistered parties as a type. -/
abbrev Unreg (Reg : Set P) := ↥(Regᶜ)

section Defs

variable (Reg : Set P) (snd : P) {M' : Type} (ba : Protocol (Unreg Reg) Bool M' Bool)

open Classical in
/-- The agreement phase of Π_BC (rounds `≥ 4s`), on input `(v, g)` (the gradecast output): the
unregistered parties run the black box `ba` on `v` among themselves (registered parties stay
silent); registered parties and unregistered parties with grade `1` output `v` at once, the others
output the decision of `ba`. -/
noncomputable def bcPhase2 : Protocol P (Bool × Bool) M' Bool where
  send p x h q := (ba.extend Regᶜ).send p x.1 h q
  decide p x h := if p ∈ Reg ∨ x.2 = true then some x.1 else (ba.extend Regᶜ).decide p x.1 h

/-- The input of the agreement phase: the gradecast output (`(false, false)` if there is none). -/
def bcIn (_ : P) (_ : Bool) (o : Option (Bool × Bool)) : Bool × Bool := o.getD (false, false)

/-- Π_BC over a gradecast protocol `gcp` that outputs `(v, g)` at round `4s`: run `gcp` for the
first `4s` rounds, then `bcPhase2` on its output (sequential composition). -/
noncomputable def bcWith (gcp : Protocol P Bool (GMsg P) (Bool × Bool)) :
    Protocol P Bool (GMsg P ⊕ M') Bool :=
  gcp.seq (4 * Reg.ncard) bcIn (bcPhase2 Reg ba)

/-- **Π_BC** (Figure 2) with the black-box agreement protocol `ba` among the unregistered parties:
Π_GC for `4s` rounds, then the agreement phase `bcPhase2`. -/
noncomputable abbrev bc : Protocol P Bool (GMsg P ⊕ M') Bool := bcWith Reg ba (gc Reg snd)

/-- Tokens of Π_BC: those of the gradecast messages; agreement messages carry none. -/
def bcAuth (M' : Type) : Auth P (GMsg P ⊕ M') (List P) where
  signer := (gAuth Reg snd).signer
  tokens m := match m with
    | Sum.inl m => (gAuth Reg snd).tokens m
    | Sum.inr _ => ∅

lemma bcAuth_registered (M' : Type) : RegisteredSigners Reg (bcAuth Reg snd M') := by
  rintro (m | m) τ hτ
  · exact gAuth_registered Reg snd m τ hτ
  · exact absurd hτ (Set.notMem_empty τ)

/-- Π_BC is unforging as soon as its gradecast part is. -/
theorem bcWith_unforging {gcp : Protocol P Bool (GMsg P) (Bool × Bool)}
    (h : gcp.Unforging (gAuth Reg snd)) : (bcWith Reg ba gcp).Unforging (bcAuth Reg snd M') :=
  Protocol.Unforging.seq_of_left_right h fun _ _ _ _ _ _ τ hτ => absurd hτ (Set.notMem_empty τ)

theorem bc_unforging : (bc Reg snd ba).Unforging (bcAuth Reg snd M') :=
  bcWith_unforging Reg snd ba gc_unforging

omit snd in
/-- Π_GC decides the state after the first `4s` rounds. -/
lemma gc_firstDecide {snd p : P} {x : Bool} {h : History P (GMsg P)}
    (hl : h.length = 4 * Reg.ncard) :
    (gc Reg snd).firstDecide p x h =
      some ((gstOf Reg snd p x h).v, (gstOf Reg snd p x h).g) := by
  rw [Protocol.firstDecide, hl]
  refine firstUpTo_of_firstSome (r := 4 * Reg.ncard) ?_ (fun r hr => ?_) le_rfl
  · have ht : h.take (4 * Reg.ncard) = h := List.take_of_length_le hl.le
    simp [gc, hl, ht]
  · simp only [gc, List.length_take, hl]
    split_ifs <;> first | rfl | omega

open Classical in
/-- `bcWith` spelled out, for a gradecast protocol `gcp` whose first decision after `4s` rounds is
the state `out` (`(v, g)`) computed from the history of those rounds. -/
theorem bcWith_send_decide {gcp : Protocol P Bool (GMsg P) (Bool × Bool)}
    (out : P → Bool → History P (GMsg P) → GSt P)
    (hout : ∀ p x (h : History P (GMsg P)), h.length = 4 * Reg.ncard →
      gcp.firstDecide p x h = some ((out p x h).v, (out p x h).g))
    (p q : P) (x : Bool) (h : History P (GMsg P ⊕ M')) :
    let st := out p x (histL (h.take (4 * Reg.ncard)))
    let hba := restrictHist Regᶜ (histR (h.drop (4 * Reg.ncard)))
    (bcWith Reg ba gcp).send p x h q =
      (if h.length < 4 * Reg.ncard then (gcp.send p x (histL h) q).map Sum.inl
       else if hp : p ∈ Regᶜ then
         if hq : q ∈ Regᶜ then (ba.send ⟨p, hp⟩ st.v hba ⟨q, hq⟩).map Sum.inr else none
       else none) ∧
    (bcWith Reg ba gcp).decide p x h =
      (if 4 * Reg.ncard ≤ h.length then
         if hp : p ∈ Regᶜ then (if st.g then some st.v else ba.decide ⟨p, hp⟩ st.v hba)
         else some st.v
       else none) := by
  intro st hba
  have hin : ∀ hl : 4 * Reg.ncard ≤ h.length,
      gcp.seqInput (4 * Reg.ncard) bcIn p x h = (st.v, st.g) := fun hl => by
    rw [Protocol.seqInput, hout p x _ (by simp [histL]; omega)]
    rfl
  constructor
  · split_ifs with hl hp hq
    · exact seq_send_lt _ _ _ _ hl q
    · rw [bcWith, seq_send_ge _ _ _ _ (not_lt.1 hl), hin (not_lt.1 hl)]
      simp only [bcPhase2, Protocol.extend_send_of_mem ba hp hq]
      rfl
    · have hq' : q ∈ Reg := by simpa using hq
      rw [bcWith, seq_send_ge _ _ _ _ (not_lt.1 hl)]
      simp [bcPhase2, Protocol.extend, hq']
    · have hp' : p ∈ Reg := by simpa using hp
      rw [bcWith, seq_send_ge _ _ _ _ (not_lt.1 hl)]
      simp [bcPhase2, Protocol.extend, hp']
  · by_cases hl : 4 * Reg.ncard ≤ h.length
    · simp only [bcWith, Protocol.seq, not_lt.2 hl, ↓reduceIte, hl]
      rw [hin hl]
      by_cases hp : p ∈ Regᶜ
      · have hp' : p ∉ Reg := hp
        simp only [bcPhase2, hp, hp', false_or, ↓reduceDIte, Protocol.extend_decide_of_mem ba hp]
        cases st.g <;> rfl
      · have hp' : p ∈ Reg := not_not.1 hp
        simp [bcPhase2, hp, hp']
    · simp [bcWith, Protocol.seq, lt_of_not_ge hl, hl]

open Classical in
/-- **Π_BC is the protocol of Figure 2.** During the first `4s` rounds it runs Π_GC on the
gradecast messages. Afterwards, with `(v, g)` the Π_GC state after those rounds, the unregistered
parties run `ba` among themselves on input `v` (on the agreement messages from unregistered
senders, registered parties stay silent); registered parties and parties with `g = 1` decide `v`,
the others decide what `ba` decides. -/
theorem bc_send_decide (p q : P) (x : Bool) (h : History P (GMsg P ⊕ M')) :
    let st := gstOf Reg snd p x (histL (h.take (4 * Reg.ncard)))
    let hba := restrictHist Regᶜ (histR (h.drop (4 * Reg.ncard)))
    (bc Reg snd ba).send p x h q =
      (if h.length < 4 * Reg.ncard then ((gc Reg snd).send p x (histL h) q).map Sum.inl
       else if hp : p ∈ Regᶜ then
         if hq : q ∈ Regᶜ then (ba.send ⟨p, hp⟩ st.v hba ⟨q, hq⟩).map Sum.inr else none
       else none) ∧
    (bc Reg snd ba).decide p x h =
      (if 4 * Reg.ncard ≤ h.length then
         if hp : p ∈ Regᶜ then (if st.g then some st.v else ba.decide ⟨p, hp⟩ st.v hba)
         else some st.v
       else none) :=
  bcWith_send_decide Reg ba (gstOf Reg snd) (fun _ _ _ hl => gc_firstDecide Reg hl) p q x h

end Defs

/-! ### The derived runs -/

section Runs

variable {Reg : Set P} {snd : P} {M' : Type} {ba : Protocol (Unreg Reg) Bool M' Bool}
  {gcp : Protocol P Bool (GMsg P) (Bool × Bool)} (s : Scenario P Bool (GMsg P ⊕ M'))

local notation "T" => 4 * Reg.ncard

/-- The gradecast scenario (first `4s` rounds). -/
noncomputable abbrev sc₁ (Reg : Set P) (s : Scenario P Bool (GMsg P ⊕ M')) :
    Scenario P Bool (GMsg P) :=
  s.seqFst (4 * Reg.ncard)

/-- The agreement scenario among the unregistered parties (rounds `≥ 4s`), with inputs `x`. -/
noncomputable def sc₂With (Reg : Set P) (s : Scenario P Bool (GMsg P ⊕ M')) (x : Unreg Reg → Bool) :
    Scenario (Unreg Reg) Bool M' where
  byz := {q | q.1 ∈ s.byz}
  input := x
  adv r b q := (s.adv (4 * Reg.ncard + r) b.1 q.1).bind Sum.getRight?
  drop r b q := s.drop (4 * Reg.ncard + r) b.1 q.1

/-- The agreement scenario of Π_BC: the unregistered parties start with their gradecast values. -/
noncomputable abbrev sc₂ (Reg : Set P) (snd : P) (s : Scenario P Bool (GMsg P ⊕ M')) :
    Scenario (Unreg Reg) Bool M' :=
  sc₂With Reg s fun q => (gS (sc₁ Reg s) Reg snd (4 * Reg.ncard) q.1).v

@[simp] lemma sc₂With_byz {x : Unreg Reg → Bool} (q : Unreg Reg) :
    q ∈ (sc₂With Reg s x).byz ↔ q.1 ∈ s.byz := Iff.rfl
@[simp] lemma sc₂With_drop {x : Unreg Reg → Bool} (r : ℕ) (b q : Unreg Reg) :
    (sc₂With Reg s x).drop r b q = s.drop (4 * Reg.ncard + r) b.1 q.1 := rfl
lemma sc₂With_adv {x : Unreg Reg → Bool} (r : ℕ) (b q : Unreg Reg) :
    (sc₂With Reg s x).adv r b q = (s.adv (4 * Reg.ncard + r) b.1 q.1).bind Sum.getRight? := rfl

lemma sc₁_reliable (hrel : s.Reliable) : (sc₁ Reg s).Reliable := hrel

lemma sc₁_authValid (hV : s.AuthValid ⊤ (bcWith Reg ba gcp) (bcAuth Reg snd M')) :
    (sc₁ Reg s).AuthValid ⊤ gcp (gAuth Reg snd) :=
  hV.seqFst_left ⊤ gcp _ _ _

/-- The second phase only runs `ba` (on the gradecast values) among the unregistered parties. -/
lemma hist_bcPhase2 (s₂ : Scenario P (Bool × Bool) M') :
    hist ⊤ (bcPhase2 Reg ba) s₂ = hist ⊤ (ba.extend Regᶜ) (s₂.mapInput Prod.fst) := by
  exact (hist_eq_of_send_eq ⊤ (bcPhase2 Reg ba) s₂
    (alg' := (ba.extend Regᶜ).comapInput Prod.fst) rfl).trans
    (funext (hist_comapInput ⊤ _ Prod.fst s₂))

/-- The inputs of the agreement phase: the gradecast outputs. -/
local notation "X" => seqInputs ⊤ gcp (4 * Reg.ncard) bcIn s

/-- Registered parties and parties with grade `1` decide their gradecast value. -/
lemma bcWith_decides_of_g {p : P} (hp : p ∈ Reg ∨ (X p).2 = true) (o : Bool) :
    Decides ⊤ (bcWith Reg ba gcp) s p o ↔ o = (X p).1 := by
  rw [bcWith, decides_seq_iff]
  exact firstSome_iff_of_forall fun r => by simp [status, bcPhase2, hp]

/-- Unregistered parties with grade `0` decide what `ba` decides. -/
lemma bcWith_decides_of_g0 (p : Unreg Reg) (hp : (X p.1).2 = false) (o : Bool) :
    Decides ⊤ (bcWith Reg ba gcp) s p.1 o ↔
      Decides ⊤ ba (sc₂With Reg s fun q => (X q.1).1) p o := by
  rw [bcWith, decides_seq_iff]
  show _ ↔ Decides ⊤ ba (((s.seqSnd _ X).mapInput Prod.fst).restrict Regᶜ) p o
  rw [← decides_extend_iff (G := ⊤) (G' := ⊤) (by simp) ba]
  refine FirstSome.congr fun r => ?_
  have hpR : p.1 ∉ Reg := p.2
  simp only [status]
  rw [hist_bcPhase2]
  simp only [bcPhase2, hpR, Scenario.seqSnd_input, hp, false_or, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The gradecast part outputs at round `4s`. -/
lemma seqInputs_bcWith {p : P} {o₁ : Bool × Bool}
    (h : status ⊤ gcp (sc₁ Reg s) (4 * Reg.ncard) p = some o₁)
    (hlt : ∀ r < 4 * Reg.ncard, status ⊤ gcp (sc₁ Reg s) r p = none) : X p = o₁ :=
  seqInputs_eq ⊤ gcp _ _ s p o₁ ⟨_, h, hlt⟩ ⟨_, le_rfl, _, h⟩

lemma seqInputs_bc (p : P) :
    seqInputs ⊤ (gc Reg snd) (4 * Reg.ncard) bcIn s p =
      ((gS (sc₁ Reg s) Reg snd T p).v, (gS (sc₁ Reg s) Reg snd T p).g) :=
  seqInputs_bcWith s (by rw [gc_status]; simp)
    fun r hr => by rw [gc_status]; simp; omega

/-- Registered parties and parties with grade `1` decide their gradecast value. -/
lemma bc_decides_of_g {p : P} (hp : p ∈ Reg ∨ (gS (sc₁ Reg s) Reg snd T p).g = true) (o : Bool) :
    Decides ⊤ (bc Reg snd ba) s p o ↔ o = (gS (sc₁ Reg s) Reg snd T p).v := by
  rw [bcWith_decides_of_g s (by rwa [seqInputs_bc s]), seqInputs_bc s]

/-- Unregistered parties with grade `0` decide what `ba` decides. -/
lemma bc_decides_of_g0 (p : Unreg Reg) (hp : (gS (sc₁ Reg s) Reg snd T p.1).g = false) (o : Bool) :
    Decides ⊤ (bc Reg snd ba) s p.1 o ↔ Decides ⊤ ba (sc₂ Reg snd s) p o := by
  rw [bcWith_decides_of_g0 s p (by rw [seqInputs_bc s]; exact hp)]
  simp only [seqInputs_bc s]

end Runs

/-! ### Lemmas 3.11 and 3.12 -/

section Main

variable [Finite P] {Reg : Set P} {snd : P} {M' : Type} {ba : Protocol (Unreg Reg) Bool M' Bool}
  (s : Scenario P Bool (GMsg P ⊕ M')) (hsR : snd ∈ Reg) (hrel : s.Reliable)
  (hV : s.AuthValid ⊤ (bc Reg snd ba) (bcAuth Reg snd M'))

local notation "T" => 4 * Reg.ncard

include hsR hrel hV

/-- Lemmas 3.11/3.12, case 1: if some registered party is honest, Π_BC satisfies broadcast. -/
theorem bc_bb_of_honest_reg {k : P} (hk : k ∉ s.byz) (hkR : k ∈ Reg) :
    BB snd s.input s.honest (Decides ⊤ (bc Reg snd ba) s) := by
  have hrel₁ := sc₁_reliable (Reg := Reg) s hrel
  have hV₁ := sc₁_authValid s hV
  have hdec : ∀ p ∉ s.byz, ∀ o, Decides ⊤ (bc Reg snd ba) s p o ↔
      o = (gS (sc₁ Reg s) Reg snd T p).v := fun p hp o =>
    bc_decides_of_g s (Or.inr (lemma310 (sc₁ Reg s) hrel₁ hV₁ hsR hk hkR hp)) o
  refine ⟨fun p hp => ⟨_, (hdec p hp _).2 rfl⟩, fun hsnd p hp => ?_, fun p hp q hq v w hv hw => ?_⟩
  · rw [hdec p hp]; exact ((lemma36 (sc₁ Reg s) hrel₁ hV₁ hsR hsnd hp).1).symm
  · rw [hdec p hp] at hv; rw [hdec q hq] at hw
    rw [hv, hw, lemma35 (sc₁ Reg s) hrel₁ hV₁ hsR hk hkR hp,
      lemma35 (sc₁ Reg s) hrel₁ hV₁ hsR hk hkR hq]

/-- Lemma 3.12, case 2: if all registered parties are Byzantine and `ba` satisfies Byzantine
agreement among the unregistered parties, Π_BC satisfies broadcast. -/
theorem bc_bb_of_ba (hReg : Reg ⊆ s.byz)
    (hba : BA (sc₂ Reg snd s).input (sc₂ Reg snd s).honest (Decides ⊤ ba (sc₂ Reg snd s))) :
    BB snd s.input s.honest (Decides ⊤ (bc Reg snd ba) s) := by
  have hrel₁ := sc₁_reliable (Reg := Reg) s hrel
  have hV₁ := sc₁_authValid s hV
  have hN : ∀ p ∉ s.byz, p ∈ Regᶜ := fun p hp hpR => hp (hReg hpR)
  obtain ⟨hterm, hval, hagr⟩ := hba
  -- every honest party decides `v` if it has grade `1`, otherwise the `ba` decision
  have hdec : ∀ p (hp : p ∉ s.byz), ∀ o, Decides ⊤ (bc Reg snd ba) s p o ↔
      ((gS (sc₁ Reg s) Reg snd T p).g = true ∧ o = (gS (sc₁ Reg s) Reg snd T p).v) ∨
      ((gS (sc₁ Reg s) Reg snd T p).g = false ∧ Decides ⊤ ba (sc₂ Reg snd s) ⟨p, hN p hp⟩ o) := by
    intro p hp o
    rcases Bool.eq_false_or_eq_true (gS (sc₁ Reg s) Reg snd T p).g with hg | hg
    · rw [bc_decides_of_g s (Or.inr hg)]; simp [hg]
    · have := bc_decides_of_g0 (ba := ba) s ⟨p, hN p hp⟩ hg o
      rw [this]; simp [hg]
  refine ⟨fun p hp => ?_, fun hsnd => absurd (hReg hsR) hsnd, fun p hp q hq v w hv hw => ?_⟩
  · rcases Bool.eq_false_or_eq_true (gS (sc₁ Reg s) Reg snd T p).g with hg | hg
    · exact ⟨_, (hdec p hp _).2 (Or.inl ⟨hg, rfl⟩)⟩
    · obtain ⟨o, ho⟩ := hterm ⟨p, hN p hp⟩ hp
      exact ⟨o, (hdec p hp _).2 (Or.inr ⟨hg, ho⟩)⟩
  · rw [hdec p hp] at hv; rw [hdec q hq] at hw
    by_cases hj : ∃ j, j ∉ s.byz ∧ (gS (sc₁ Reg s) Reg snd T j).g = true
    · -- Case 2a: some honest party has grade 1; all honest values agree and `ba` keeps them
      obtain ⟨j, hj, hgj⟩ := hj
      have hall : ∀ p ∉ s.byz, (gS (sc₁ Reg s) Reg snd T p).v = (gS (sc₁ Reg s) Reg snd T j).v :=
        fun p hp => lemma37 (sc₁ Reg s) hrel₁ hV₁ hsR hj hp hgj
      have hbaval := hval (gS (sc₁ Reg s) Reg snd T j).v (fun p hp => hall p.1 hp)
      have key : ∀ p (hp : p ∉ s.byz) o,
          ((gS (sc₁ Reg s) Reg snd T p).g = true ∧ o = (gS (sc₁ Reg s) Reg snd T p).v) ∨
          ((gS (sc₁ Reg s) Reg snd T p).g = false ∧
            Decides ⊤ ba (sc₂ Reg snd s) ⟨p, hN p hp⟩ o) → o = (gS (sc₁ Reg s) Reg snd T j).v := by
        rintro p hp o (⟨-, rfl⟩ | ⟨-, ho⟩)
        · exact hall p hp
        · exact Decides.unique _ _ ho (hbaval ⟨p, hN p hp⟩ hp)
      rw [key p hp v hv, key q hq w hw]
    · push Not at hj
      rcases hv with ⟨hg, -⟩ | ⟨-, hv⟩
      · exact absurd hg (by simp [hj p hp])
      rcases hw with ⟨hg, -⟩ | ⟨-, hw⟩
      · exact absurd hg (by simp [hj q hq])
      exact hagr ⟨p, hN p hp⟩ hp ⟨q, hN q hq⟩ hq v w hv hw

omit [Finite P] hsR hrel hV in
/-- Termination of a party with grade `0` needs only the termination of `ba`. -/
lemma bc_terminates {p : P}
    (hterm : ∀ hpN : p ∈ Regᶜ, ∃ o, Decides ⊤ ba (sc₂ Reg snd s) ⟨p, hpN⟩ o) :
    ∃ o, Decides ⊤ (bc Reg snd ba) s p o := by
  by_cases h : p ∈ Reg ∨ (gS (sc₁ Reg s) Reg snd T p).g = true
  · exact ⟨_, (bc_decides_of_g s h _).2 rfl⟩
  · push Not at h
    obtain ⟨o, ho⟩ := hterm h.1
    exact ⟨o, (bc_decides_of_g0 s ⟨p, h.1⟩ (by simpa using h.2) o).2 ho⟩

end Main

/-! ### The "OR" exchange among the unregistered parties (Figure 4) -/

section OrBA

variable (N : Type)

open Classical in
/-- Every party sends its value; after one round it decides the OR of its own value and the values
received. With no Byzantine party this is Byzantine agreement. -/
noncomputable def orBA : Protocol N Bool Bool Bool where
  send _ x _ _ := some x
  decide _ x h := match h with
    | [] => none
    | ib :: _ => some (x || decide (∃ q, ib q = some true))

variable {N}

open Classical in
lemma orBA_decides (s : Scenario N Bool Bool) (p : N) (o : Bool) :
    Decides ⊤ (orBA N) s p o ↔ o = (s.input p || decide (∃ q,
      deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 q p = some true)) := by
  have hst : ∀ r, status ⊤ (orBA N) s (r + 1) p = some (s.input p || decide (∃ q,
      deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 q p = some true)) := by
    intro r
    have h1 := take_hist ⊤ (orBA N) s (show 1 ≤ r + 1 by omega) p
    obtain ⟨ib, l, hl⟩ : ∃ ib l, hist ⊤ (orBA N) s (r + 1) p = ib :: l := by
      cases h : hist ⊤ (orBA N) s (r + 1) p with
      | nil => have := length_hist ⊤ (orBA N) s (r + 1) p; rw [h] at this; simp at this
      | cons ib l => exact ⟨ib, l, rfl⟩
    rw [hl] at h1
    simp only [List.take_succ_cons, List.take_zero, hist_succ, hist_zero, List.nil_append,
      List.cons.injEq, and_true] at h1
    subst h1; rw [status, hl]; rfl
  constructor
  · rintro ⟨r, hr, -⟩
    cases r with
    | zero => simp [status, orBA] at hr
    | succ r => rw [hst] at hr; exact (Option.some_injective _ hr).symm
  · rintro rfl
    exact ⟨1, hst 0, fun r hr => by
      obtain rfl : r = 0 := by omega
      simp [status, orBA]⟩

lemma orBA_terminates (s : Scenario N Bool Bool) (p : N) : ∃ o, Decides ⊤ (orBA N) s p o :=
  ⟨_, (orBA_decides s p _).2 rfl⟩

/-- Without Byzantine parties, `orBA` solves Byzantine agreement. -/
lemma orBA_BA (s : Scenario N Bool Bool) (hrel : s.Reliable) (hB : s.byz = ∅) :
    BA s.input s.honest (Decides ⊤ (orBA N) s) := by
  classical
  have key : ∀ p o, Decides ⊤ (orBA N) s p o ↔ o = decide (∃ q, s.input q = true) := by
    intro p o
    rw [orBA_decides]
    have hdel : ∀ q, q ≠ p → deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 q p = some (s.input q) := by
      intro q hqp
      rw [deliver_honest ⊤ _ s hrel (by simp [hB]) hqp]; rfl
    have hself : deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 p p = none := by simp [deliver]
    suffices (s.input p || decide (∃ q, deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 q p = some true))
        = decide (∃ q, s.input q = true) by rw [this]
    rcases Bool.eq_false_or_eq_true (s.input p) with h | h
    · simp only [h, Bool.true_or]; exact (decide_eq_true ⟨p, h⟩).symm
    · simp only [h, Bool.false_or, decide_eq_decide]
      constructor
      · rintro ⟨q, hq⟩
        by_cases hqp : q = p
        · subst hqp; rw [hself] at hq; simp at hq
        · rw [hdel q hqp] at hq; exact ⟨q, Option.some_injective _ hq⟩
      · rintro ⟨q, hq⟩
        have hqp : q ≠ p := by rintro rfl; simp_all
        exact ⟨q, by rw [hdel q hqp, hq]⟩
  refine ⟨fun p _ => ⟨_, (key p _).2 rfl⟩, fun v hv p hp => (key p v).2 ?_,
    fun p _ q _ v w hv hw => by rw [(key p v).1 hv, (key q w).1 hw]⟩
  have hall : ∀ q, s.input q = v := fun q => hv q (by simp [Scenario.honest, hB])
  rcases Bool.eq_false_or_eq_true v with h | h
  · subst h; exact (decide_eq_true ⟨p, hall p⟩).symm
  · subst h; simp [hall]

end OrBA

/-! ### Theorems 3.13 and 3.14 -/

section Theorems

variable [Finite P] {Reg : Set P} {snd : P}

omit [Finite P] in
lemma sc₂_reliable {M' : Type} {s : Scenario P Bool (GMsg P ⊕ M')} (hrel : s.Reliable) :
    (sc₂ Reg snd s).Reliable := fun _ _ _ => hrel _ _ _

lemma ncard_sc₂_byz {M' : Type} (s : Scenario P Bool (GMsg P ⊕ M')) (hReg : Reg ⊆ s.byz) :
    (sc₂ Reg snd s).byz.ncard + Reg.ncard = s.byz.ncard := by
  have h1 : Subtype.val '' (sc₂ Reg snd s).byz = s.byz \ Reg := by
    ext x; constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨hq, q.2⟩
    · rintro ⟨hx, hxR⟩; exact ⟨⟨x, hxR⟩, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, h1]
  exact Set.ncard_sdiff_add_ncard_of_subset hReg

lemma nat_card_unreg : Nat.card (Unreg Reg) = Nat.card P - Reg.ncard := by
  rw [Nat.card_coe_set_eq, Set.ncard_compl]

omit [Finite P] in
/-- The bound of Theorem 3.13 in the paper's equivalent form `3t < n + 2s` (abstract). -/
lemma resilience_iff {n s t : ℕ} (hs : s ≤ n) : t < s + (n - s + 2) / 3 ↔ 3 * t < n + 2 * s := by
  omega

/-- **Theorem 3.13.** Π_BC is a Byzantine broadcast protocol for a registered sender tolerating
`t ≤ s + ⌈(n - s)/3⌉ - 1` Byzantine parties (written `t < s + ⌈(n-s)/3⌉`), given a black-box
unauthenticated Byzantine agreement protocol among the `n - s` unregistered parties tolerating every
Byzantine set `B` with `3|B| < n - s`. -/
theorem theorem313 (hsR : snd ∈ Reg) {M' : Type} (ba : Protocol (Unreg Reg) Bool M' Bool)
    (hba : Solves ⊤ ba {B | 3 * B.ncard < Nat.card (Unreg Reg)} BA) (t : ℕ)
    (ht : t < Reg.ncard + (Nat.card P - Reg.ncard + 2) / 3) :
    SolvesAuth ⊤ (bc Reg snd ba) (bcAuth Reg snd M') (atMost t) (BB snd) := by
  intro s hs hrel hV
  by_cases hk : ∃ k, k ∉ s.byz ∧ k ∈ Reg
  · obtain ⟨k, hk, hkR⟩ := hk
    exact bc_bb_of_honest_reg s hsR hrel hV hk hkR
  · push Not at hk
    have hReg : Reg ⊆ s.byz := fun k hkR => by by_contra h; exact hk k h hkR
    refine bc_bb_of_ba s hsR hrel hV hReg (hba _ ?_ (sc₂_reliable hrel))
    have h1 := ncard_sc₂_byz (snd := snd) s hReg
    have h2 : s.byz.ncard ≤ t := hs
    show 3 * (sc₂ Reg snd s).byz.ncard < Nat.card (Unreg Reg)
    rw [nat_card_unreg]
    omega

/-- Theorem 3.13 in solvability form: Byzantine broadcast with a registered sender is solvable in
the partially authenticated setting for `t < s + ⌈(n-s)/3⌉`, provided unauthenticated Byzantine
agreement among `n - s` parties against `3|B| < n - s` is solvable. -/
theorem theorem313_solvable (hsR : snd ∈ Reg)
    (hba : Solvable (⊤ : SimpleGraph (Unreg Reg)) {B | 3 * B.ncard < Nat.card (Unreg Reg)}
      (BA (V := Bool)))
    (t : ℕ) (ht : t < Reg.ncard + (Nat.card P - Reg.ncard + 2) / 3) :
    SolvablePA Reg (atMost t) (BB (V := Bool) snd) := by
  obtain ⟨M', ba, hba⟩ := hba
  exact ⟨_, _, bcAuth Reg snd M', bc Reg snd ba, bcAuth_registered Reg snd M', bc_unforging Reg snd ba,
    theorem313 hsR ba hba t ht⟩

/-- Non-vacuity of Theorem 3.13: for at most three unregistered parties the black box is
discharged by `orBA` (the only admissible Byzantine set among `N` is `∅`). -/
theorem theorem313_small (hsR : snd ∈ Reg) (hn : Nat.card P ≤ Reg.ncard + 3) (t : ℕ)
    (ht : t < Reg.ncard + (Nat.card P - Reg.ncard + 2) / 3) :
    SolvablePA Reg (atMost t) (BB (V := Bool) snd) := by
  refine theorem313_solvable hsR ⟨Bool, orBA _, fun s hs hrel => orBA_BA s hrel ?_⟩ t ht
  have hs' : 3 * s.byz.ncard < Nat.card (Unreg Reg) := hs
  rw [nat_card_unreg] at hs'
  exact (Set.ncard_eq_zero (Set.toFinite _)).mp (by omega)

/-- **Theorem 3.14** (Figure 4, Lemma 6.1). If `n - s ≤ 2`, Π_BC with the OR-exchange among the
unregistered parties solves Byzantine broadcast with a registered sender against **any** set of
Byzantine parties. -/
theorem theorem314 (hsR : snd ∈ Reg) (hn : Nat.card P ≤ Reg.ncard + 2) :
    SolvesAuth ⊤ (bc Reg snd (orBA (Unreg Reg))) (bcAuth Reg snd Bool) Set.univ (BB snd) := by
  intro s _ hrel hV
  by_cases hk : ∃ k, k ∉ s.byz ∧ k ∈ Reg
  · obtain ⟨k, hk, hkR⟩ := hk
    exact bc_bb_of_honest_reg s hsR hrel hV hk hkR
  push Not at hk
  have hReg : Reg ⊆ s.byz := fun k hkR => by by_contra h; exact hk k h hkR
  by_cases hN : (sc₂ Reg snd s).byz = ∅
  · exact bc_bb_of_ba s hsR hrel hV hReg (orBA_BA _ (sc₂_reliable hrel) hN)
  -- some unregistered party is Byzantine: at most one honest party
  obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hN
  have hone : ∀ p q, p ∉ s.byz → q ∉ s.byz → p = q := by
    intro p q hp hq
    by_contra hpq
    have hpu : p ≠ u.1 := by rintro rfl; exact hp hu
    have hqu : q ≠ u.1 := by rintro rfl; exact hq hu
    have h3 : ({p, q, u.1} : Set P).ncard = 3 := Set.ncard_eq_three.mpr ⟨p, q, u.1, hpq, hpu, hqu, rfl⟩
    have hsub : ({p, q, u.1} : Set P) ⊆ Regᶜ := by
      rintro x (rfl | rfl | rfl)
      · exact fun h => hp (hReg h)
      · exact fun h => hq (hReg h)
      · exact u.2
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_compl] at this
    omega
  refine ⟨fun p hp => bc_terminates s (fun _ => orBA_terminates _ _),
    fun hsnd => absurd (hReg hsR) hsnd, fun p hp q hq v w hv hw => ?_⟩
  obtain rfl := hone p q hp hq
  exact Decides.unique _ _ hv hw

theorem theorem314_solvable (hsR : snd ∈ Reg) (hn : Nat.card P ≤ Reg.ncard + 2) :
    SolvablePA Reg Set.univ (BB (V := Bool) snd) :=
  ⟨_, _, bcAuth Reg snd Bool, bc Reg snd (orBA _), bcAuth_registered Reg snd Bool,
    bc_unforging Reg snd _, theorem314 hsR hn⟩

end Theorems

/-- **Theorem 4.1 needs the hypothesis "unregistered sender".** With `n = s = 3` (everybody
registered, sender `0`) and `t = 2 ≥ max{⌈s/2⌉, ⌈n/3⌉} = 2`, Byzantine broadcast *is* solvable
(Theorem 3.14), although Theorem 4.1 as printed (without the sender hypothesis) claims it is not. -/
theorem theorem41_false_registered_sender :
    max (((Set.univ : Set (Fin 3)).ncard + 1) / 2) ((Nat.card (Fin 3) + 2) / 3) ≤ 2 ∧
    SolvablePA (Set.univ : Set (Fin 3)) (atMost 2) (BB (V := Bool) (0 : Fin 3)) := by
  refine ⟨by simp, (theorem314_solvable (Set.mem_univ _) (by simp)).mono (Set.subset_univ _)⟩

end PartialAuthBC
