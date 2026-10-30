import Papers.PODC2023.PPDoubleExpThresholds.Machine
import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolGeneric

/-!
# Conversion of population machines into population protocols (Appendix B.3): definitions

Let `A = (Q, F, 𝓕, I)` be a population machine.

**States.** Register agents use the states `Q`; the agent of pointer `X` uses states `X^v_s` with
`v ∈ 𝓕_X` (the value) and `s ∈ S_X` (the stage of an instruction in progress), where
`S_IP = {none, wait, half}`, `S_{V_x} = {none, done, emit, take, test, true, false}` (`x ∈ Q`) and
`S_X = {none, done}` otherwise; finally map states `X^i_map` for instructions `I_i = (X := f(Y))`.
We represent all of them in the type `St Q F` (`St.reg`, `St.ptr X v s`, `St.map X i`) and collect
the valid ones in the finite set `U A`.

**Deviation (IP domain).** The Lean semantics of machines (`Machine.Exec`) executes a
non-jump instruction `I_L` and sets `IP := L + 1` (after which the machine hangs), whereas the paper's
Definition 13 does not execute `I_L` at all. To simulate the Lean semantics the IP agent may also
hold the value `L + 1` (`dom' A IP = {1, …, L + 1}`), and the side conditions `i < L` of the paper's
transitions are dropped.

**Leader election** `⟨elect⟩`: pointers are enumerated `X_1, …, X_{|F|}` (`ptrAt`, levels `lvl`
`0, …, |F| - 1`) with `X_{|F|} = IP`; `(X_i)^∗_∗, (X_i)^∗_∗ ↦ (X_i)^{v_i}_none, (X_{i+1})^{v_{i+1}}_none`
and `IP^∗_∗, IP^∗_∗ ↦ (X_1)^{v_1}_none, z`. The wildcard `(X_i)^∗_∗` also matches the map states
`(X_i)^j_map` of `X_i` (see `St.owner`).

**Initial values** `v_X` (`v0`): `v_IP = 1`, `v_{V_x} = x`, and — deviating from the paper, which
allows any value — `v_OF = false` (with fewer than `|F|` agents the election may produce an `OF`
agent but never an `IP` agent; with `v_OF = true` such an agent would broadcast `true`).

**Instructions**: transitions `⟨move⟩`, `⟨test⟩`, `⟨pointer⟩` (`Tr`), with the special cases
`X = IP`, `X = Y` of the paper and two additional ones for `Y = IP` (the paper assumes `Y ≠ IP`
"without loss of generality").

**Output broadcast**: `Q' = Q* × {true, false}` (`bcast`), then restricted to valid states.
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem

/-- Stages of a pointer agent (`tt`, `ff` are the paper's `true`, `false`). -/
inductive Stage
  | none | wait | half | done | emit | take | test | tt | ff
  deriving DecidableEq

/-- (Raw) states of the protocol `PP` of Appendix B.3. -/
inductive St (Q F : Type*)
  /-- A register agent in register `q`. -/
  | reg (q : Q)
  /-- The agent of pointer `X` with value `v` and stage `s`, `X^v_s`. -/
  | ptr (X : F) (v : Val Q) (s : Stage)
  /-- The map state `X^i_map`. -/
  | map (X : F) (i : ℕ)
  deriving DecidableEq

namespace St

variable {Q F : Type*}

/-- The pointer an agent belongs to (`none` for register agents). -/
def owner : St Q F → Option F
  | reg _ => none
  | ptr X _ _ => some X
  | map X _ => some X

@[simp] theorem owner_reg (q : Q) : (reg q : St Q F).owner = none := rfl
@[simp] theorem owner_ptr (X : F) (v : Val Q) (s : Stage) : (ptr X v s).owner = some X := rfl
@[simp] theorem owner_map (X : F) (i : ℕ) : (map X i : St Q F).owner = some X := rfl

end St

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

/-! ### Enumeration of the pointers -/

include A in
theorem card_F_pos : 0 < Fintype.card F := Fintype.card_pos_iff.2 ⟨A.IP⟩

/-- An enumeration of the pointers with `IP` last. -/
noncomputable def lvlE : F ≃ Fin (Fintype.card F) :=
  (Fintype.equivFin F).trans
    (Equiv.swap (Fintype.equivFin F A.IP) ⟨Fintype.card F - 1, by have := A.card_F_pos; omega⟩)

/-- The level of a pointer (`X_{i}` has level `i - 1`). -/
noncomputable def lvl (X : F) : ℕ := (A.lvlE X).val

/-- The pointer at level `l` (`IP` if `l ≥ |F|`). -/
noncomputable def ptrAt (l : ℕ) : F :=
  if h : l < Fintype.card F then A.lvlE.symm ⟨l, h⟩ else A.IP

/-- The next pointer `X_{i+1}` of `X_i`. -/
noncomputable def nxt (X : F) : F := A.ptrAt (A.lvl X + 1)

/-- The first pointer `X_1`. -/
noncomputable def X1 : F := A.ptrAt 0

theorem lvl_lt (X : F) : A.lvl X < Fintype.card F := (A.lvlE X).isLt

theorem lvl_injective : Function.Injective A.lvl := fun X Y h =>
  A.lvlE.injective (Fin.ext h)

theorem lvl_IP : A.lvl A.IP = Fintype.card F - 1 := by
  simp [lvl, lvlE]

theorem lvl_ptrAt {l : ℕ} (hl : l < Fintype.card F) : A.lvl (A.ptrAt l) = l := by
  simp [ptrAt, hl, lvl]

theorem ptrAt_lvl (X : F) : A.ptrAt (A.lvl X) = X :=
  A.lvl_injective (A.lvl_ptrAt (A.lvl_lt X))

theorem lvl_eq_iff {X Y : F} : A.lvl X = A.lvl Y ↔ X = Y := A.lvl_injective.eq_iff

theorem lvl_lt_of_ne_IP {X : F} (h : X ≠ A.IP) : A.lvl X + 1 < Fintype.card F := by
  have h1 := A.lvl_lt X
  have h2 : A.lvl X ≠ A.lvl A.IP := fun h' => h (A.lvl_injective h')
  rw [lvl_IP] at h2
  omega

theorem lvl_nxt {X : F} (h : X ≠ A.IP) : A.lvl (A.nxt X) = A.lvl X + 1 :=
  A.lvl_ptrAt (A.lvl_lt_of_ne_IP h)

theorem lvl_X1 : A.lvl A.X1 = 0 := A.lvl_ptrAt A.card_F_pos

theorem lvl_eq_zero_iff {X : F} : A.lvl X = 0 ↔ X = A.X1 := by
  rw [← A.lvl_X1, A.lvl_eq_iff]

/-! ### Initial values, the fixed register `z`, domains and stages -/

include A in
theorem exists_reg : ∃ q : Q, True := by
  obtain ⟨v, hv⟩ := A.dom_V_none
  obtain ⟨q, -⟩ := A.dom_V none v hv
  exact ⟨q, trivial⟩

include A in
theorem nonempty_Q : Nonempty Q := let ⟨q, _⟩ := A.exists_reg; ⟨q⟩

include A in
/-- The fixed register `z` used by `⟨move⟩` and `⟨elect⟩`. -/
noncomputable def z0 : Q := Classical.choice A.nonempty_Q

open Classical in
/-- The initial values `v_X` of the pointers. -/
noncomputable def v0 (X : F) : Val Q :=
  if X = A.IP then .nat 1
  else if X = A.OF ∨ X = A.CF then .bool false
  else if h : ∃ x, X = A.V (some x) then .reg h.choose
  else if h : (A.dom X).Nonempty then h.choose else .bool false

theorem v0_IP : A.v0 A.IP = .nat 1 := by simp [v0]

theorem v0_OF : A.v0 A.OF = .bool false := by simp [v0, A.OF_ne_IP]

theorem v0_CF : A.v0 A.CF = .bool false := by simp [v0, A.CF_ne_IP]

theorem v0_V (x : Q) : A.v0 (A.V (some x)) = .reg x := by
  have h : ∃ y, A.V (some x) = A.V (some y) := ⟨x, rfl⟩
  have := h.choose_spec
  have hx : h.choose = x := (Option.some_injective _ (A.V_inj this)).symm
  simp only [v0, A.V_ne_IP, A.V_ne_OF, A.V_ne_CF, false_or, ite_false, dif_pos h]
  rw [hx]

/-- The pointer domains used by the protocol: `𝓕_X`, except that `IP` may also hold `L + 1`. -/
def dom' (X : F) : Finset (Val Q) :=
  if X = A.IP then (Finset.Icc 1 (A.instrs.length + 1)).image Val.nat else A.dom X

/-- The stages `S_X`. -/
def stg (X : F) : Finset Stage :=
  if X = A.IP then {.none, .wait, .half}
  else if ∃ x, X = A.V (some x) then {.none, .done, .emit, .take, .test, .tt, .ff}
  else {.none, .done}

/-- The target pointer of an instruction `I_i = (X := f(Y))`. -/
def asgTarget (i : ℕ) : Option F :=
  match A.instr i with
  | some (.assign X _ _) => some X
  | _ => none

/-- The valid states `Q* = Q ∪ ⋃_X Q_X ∪ Q_map`. -/
def U : Finset (St Q F) :=
  Finset.univ.image St.reg ∪
    Finset.univ.biUnion (fun X => (A.dom' X ×ˢ A.stg X).image (fun p => St.ptr X p.1 p.2)) ∪
    ((Finset.univ ×ˢ Finset.Icc 1 A.instrs.length).filter
      (fun p => A.asgTarget p.2 = some p.1)).image (fun p => St.map p.1 p.2)

/-! ### Transitions -/

/-- The value of the output flag stored in a state. -/
def ofv : St Q F → Option Bool
  | .ptr X (.bool b) _ => if X = A.OF then some b else none
  | _ => none

/-- The initial state `(X_1)^{v_1}_none`. -/
noncomputable def initS : St Q F := .ptr A.X1 (A.v0 A.X1) .none

local notation "P" => St.ptr

/-- The transitions `δ` of `PP` (Appendix B.3). -/
inductive Tr : Transition (St Q F) → Prop
  /-- `⟨elect⟩`: `(X_i)^∗_∗, (X_i)^∗_∗ ↦ (X_i)^{v_i}_none, (X_{i+1})^{v_{i+1}}_none`. -/
  | elect {X : F} {a b : St Q F} (hX : X ≠ A.IP) (ha : a.owner = some X) (hb : b.owner = some X) :
      Tr ⟨a, b, P X (A.v0 X) .none, P (A.nxt X) (A.v0 (A.nxt X)) .none⟩
  /-- `⟨elect⟩`: `IP^∗_∗, IP^∗_∗ ↦ (X_1)^{v_1}_none, z`. -/
  | electIP {a b : St Q F} (ha : a.owner = some A.IP) (hb : b.owner = some A.IP) :
      Tr ⟨a, b, P A.X1 (A.v0 A.X1) .none, .reg A.z0⟩
  /-- `⟨move⟩`: `IP^i_none, (V_x)^v_∗ ↦ IP^i_wait, (V_x)^v_emit`. -/
  | mvStart {i : ℕ} {x y : Q} {v : Val Q} {s : Stage} (hI : A.instr i = some (.move x y))
      (hv : v ∈ A.dom (A.V (some x))) :
      Tr ⟨P A.IP (.nat i) .none, P (A.V (some x)) v s, P A.IP (.nat i) .wait,
        P (A.V (some x)) v .emit⟩
  /-- `⟨move⟩`: `(V_x)^v_emit, v ↦ (V_x)^v_done, z`. -/
  | mvEmit {i : ℕ} {x y u : Q} (hI : A.instr i = some (.move x y))
      (hv : .reg u ∈ A.dom (A.V (some x))) :
      Tr ⟨P (A.V (some x)) (.reg u) .emit, .reg u, P (A.V (some x)) (.reg u) .done, .reg A.z0⟩
  /-- `⟨move⟩`: `IP^i_wait, (V_x)^v_done ↦ IP^i_half, (V_x)^v_none`. -/
  | mvHalf {i : ℕ} {x y : Q} {v : Val Q} (hI : A.instr i = some (.move x y))
      (hv : v ∈ A.dom (A.V (some x))) :
      Tr ⟨P A.IP (.nat i) .wait, P (A.V (some x)) v .done, P A.IP (.nat i) .half,
        P (A.V (some x)) v .none⟩
  /-- `⟨move⟩`: `IP^i_half, (V_y)^v_∗ ↦ IP^i_wait, (V_y)^v_take`. -/
  | mvTake {i : ℕ} {x y : Q} {v : Val Q} {s : Stage} (hI : A.instr i = some (.move x y))
      (hv : v ∈ A.dom (A.V (some y))) :
      Tr ⟨P A.IP (.nat i) .half, P (A.V (some y)) v s, P A.IP (.nat i) .wait,
        P (A.V (some y)) v .take⟩
  /-- `⟨move⟩`: `(V_y)^v_take, z ↦ (V_y)^v_done, v`. -/
  | mvPut {i : ℕ} {x y u : Q} (hI : A.instr i = some (.move x y))
      (hv : .reg u ∈ A.dom (A.V (some y))) :
      Tr ⟨P (A.V (some y)) (.reg u) .take, .reg A.z0, P (A.V (some y)) (.reg u) .done, .reg u⟩
  /-- `⟨move⟩`: `IP^i_wait, (V_y)^v_done ↦ IP^{i+1}_none, (V_y)^v_none`. -/
  | mvEnd {i : ℕ} {x y : Q} {v : Val Q} (hI : A.instr i = some (.move x y))
      (hv : v ∈ A.dom (A.V (some y))) :
      Tr ⟨P A.IP (.nat i) .wait, P (A.V (some y)) v .done, P A.IP (.nat (i + 1)) .none,
        P (A.V (some y)) v .none⟩
  /-- `⟨test⟩`: `IP^i_none, (V_x)^v_∗ ↦ IP^i_wait, (V_x)^v_test`. -/
  | tsStart {i : ℕ} {x : Q} {v : Val Q} {s : Stage} (hI : A.instr i = some (.detect x))
      (hv : v ∈ A.dom (A.V (some x))) :
      Tr ⟨P A.IP (.nat i) .none, P (A.V (some x)) v s, P A.IP (.nat i) .wait,
        P (A.V (some x)) v .test⟩
  /-- `⟨test⟩`: `(V_x)^v_test, v ↦ (V_x)^v_true, v`. -/
  | tsYes {i : ℕ} {x u : Q} (hI : A.instr i = some (.detect x))
      (hv : .reg u ∈ A.dom (A.V (some x))) :
      Tr ⟨P (A.V (some x)) (.reg u) .test, .reg u, P (A.V (some x)) (.reg u) .tt, .reg u⟩
  /-- `⟨test⟩`: `(V_x)^v_test, q ↦ (V_x)^v_false, q` for `q ≠ v`. -/
  | tsNo {i : ℕ} {x u : Q} {q : St Q F} (hI : A.instr i = some (.detect x))
      (hv : .reg u ∈ A.dom (A.V (some x))) (hq : q ≠ .reg u) :
      Tr ⟨P (A.V (some x)) (.reg u) .test, q, P (A.V (some x)) (.reg u) .ff, q⟩
  /-- `⟨test⟩`: `(V_x)^v_b, CF^∗_∗ ↦ (V_x)^v_done, CF^b_none`. -/
  | tsSet {i : ℕ} {x : Q} {v w : Val Q} {s : Stage} (b : Bool)
      (hI : A.instr i = some (.detect x)) (hv : v ∈ A.dom (A.V (some x))) :
      Tr ⟨P (A.V (some x)) v (if b then .tt else .ff), P A.CF w s, P (A.V (some x)) v .done,
        P A.CF (.bool b) .none⟩
  /-- `⟨test⟩`: `IP^i_wait, (V_x)^v_done ↦ IP^{i+1}_none, (V_x)^v_none`. -/
  | tsEnd {i : ℕ} {x : Q} {v : Val Q} (hI : A.instr i = some (.detect x))
      (hv : v ∈ A.dom (A.V (some x))) :
      Tr ⟨P A.IP (.nat i) .wait, P (A.V (some x)) v .done, P A.IP (.nat (i + 1)) .none,
        P (A.V (some x)) v .none⟩
  /-- `⟨pointer⟩` (`X ∉ {Y, IP}`, `Y ≠ IP`): `IP^i_none, X^∗_∗ ↦ IP^i_wait, X^i_map`. -/
  | asStart {i : ℕ} {X Y : F} {f : Val Q → Val Q} {v : Val Q} {s : Stage}
      (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y) (hX : X ≠ A.IP) (hY : Y ≠ A.IP) :
      Tr ⟨P A.IP (.nat i) .none, P X v s, P A.IP (.nat i) .wait, .map X i⟩
  /-- `⟨pointer⟩`: `X^i_map, Y^v_∗ ↦ X^{f(v)}_done, Y^v_none`. -/
  | asMap {i : ℕ} {X Y : F} {f : Val Q → Val Q} {v : Val Q} {s : Stage}
      (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y) (hX : X ≠ A.IP) (hY : Y ≠ A.IP)
      (hv : v ∈ A.dom Y) :
      Tr ⟨.map X i, P Y v s, P X (f v) .done, P Y v .none⟩
  /-- `⟨pointer⟩`: `IP^i_wait, X^v_done ↦ IP^{i+1}_none, X^v_none`. -/
  | asEnd {i : ℕ} {X Y : F} {f : Val Q → Val Q} {v : Val Q}
      (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y) (hX : X ≠ A.IP) (hY : Y ≠ A.IP)
      (hv : v ∈ A.dom X) :
      Tr ⟨P A.IP (.nat i) .wait, P X v .done, P A.IP (.nat (i + 1)) .none, P X v .none⟩
  /-- `⟨pointer⟩`, `X = IP`: `IP^i_none, Y^v_∗ ↦ IP^{f(v)}_none, Y^v_none`. -/
  | jmp {i : ℕ} {Y : F} {f : Val Q → Val Q} {v : Val Q} {s : Stage}
      (hI : A.instr i = some (.assign A.IP Y f)) (hY : Y ≠ A.IP) (hv : v ∈ A.dom Y) :
      Tr ⟨P A.IP (.nat i) .none, P Y v s, P A.IP (f v) .none, P Y v .none⟩
  /-- `⟨pointer⟩`, `X = Y`: `IP^i_none, Y^v_∗ ↦ IP^{i+1}_none, Y^{f(v)}_none`. -/
  | asSelf {i : ℕ} {Y : F} {f : Val Q → Val Q} {v : Val Q} {s : Stage}
      (hI : A.instr i = some (.assign Y Y f)) (hY : Y ≠ A.IP) (hv : v ∈ A.dom Y) :
      Tr ⟨P A.IP (.nat i) .none, P Y v s, P A.IP (.nat (i + 1)) .none, P Y (f v) .none⟩
  /-- Added case `Y = IP ≠ X` (`f(IP) = f(i)` is a constant):
  `IP^i_none, X^∗_∗ ↦ IP^{i+1}_none, X^{f(i)}_none`. -/
  | asIP {i : ℕ} {X : F} {f : Val Q → Val Q} {v : Val Q} {s : Stage}
      (hI : A.instr i = some (.assign X A.IP f)) (hX : X ≠ A.IP) :
      Tr ⟨P A.IP (.nat i) .none, P X v s, P A.IP (.nat (i + 1)) .none, P X (f (.nat i)) .none⟩
  /-- Added case `X = Y = IP`: `IP^i_none, q ↦ IP^{f(i)}_none, q`. -/
  | jmpIP {i : ℕ} {f : Val Q → Val Q} {q : St Q F} (hI : A.instr i = some (.assign A.IP A.IP f)) :
      Tr ⟨P A.IP (.nat i) .none, q, P A.IP (f (.nat i)) .none, q⟩

/-- The population protocol `PP = (Q*, δ, I, O)` before the output broadcast (on raw states;
`O` is irrelevant and taken to be the states of `OF` with value `true`). -/
noncomputable def basePP : PProtocol (St Q F) where
  δ := {t | A.Tr t}
  I := {A.initS}
  O := {s | A.ofv s = some true}

/-- The protocol `PP'` with output broadcast, on raw states. -/
noncomputable def bcastPP : PProtocol (St Q F × Bool) where
  δ := bcast {t | A.Tr t} A.ofv
  I := {(A.initS, false)}
  O := {s | s.2 = true}

/-- The valid states `Q' = Q* × {true, false}`. -/
def U' : Finset (St Q F × Bool) := A.U ×ˢ Finset.univ

/-- The final protocol `PP'` of Proposition 16, on the finite set of states `Q*× {true, false}`. -/
noncomputable def toProtocol : PProtocol (A.U' : Finset (St Q F × Bool)) :=
  A.bcastPP.restrictTo A.U'

end Machine

end Podc.PPDoubleExpThresholds
