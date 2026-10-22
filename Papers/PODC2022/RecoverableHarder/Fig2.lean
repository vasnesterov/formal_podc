import Podc.Computability.Distributed.SharedMemory.Recoverable.Composition
import Papers.PODC2022.RecoverableHarder.Recording

/-!
# The recoverable team consensus algorithm of Figure 2

Delporte-Gallet, Fatourou, Fauconnier, Ruppert, PODC 2022, Section 3.1.

Objects live at the nodes `π : List Bool` of the tournament tree (`Idx`): two registers
`R_A = (π, false)`, `R_B = (π, true)` with values `Option Bool` (initially `⊥ = none`) and one
object `O = π` of the readable type `S` (initially `q₀`). `fig2 rd π u team o` is the code of
Figure 2 for processes `Fin k` with teams `team` (`false` = A, `true` = B), operations `o` and
initial value `u = q₀`, *assuming* `q₀ ∉ Q_B` (the paper swaps the teams otherwise); `rd` is the
read operation of `S`.

Program counters (`PC`): `wr` (line 4/16, write the input to the team's register), `rd1` (line 5/17,
read `O`), `chk` (line 19, `|B| = 1`: read `R_A`), `upd` (line 8/22, apply `op_i`), `rd2` (line 9/23,
read `O` again), `rdR Y` (line 11–12/26–27, read `R_Y` and return it), `done w` (output `w`).

`fig2_safe`: Lemmas 9–13 — agreement and validity for team-uniform inputs, with arbitrary crashes
and recoveries; `fig2_ranked`: recoverable wait-freedom (no loops).
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

/-- Object indices: registers `(π, X)` and objects `π` at the nodes `π` of the tournament tree. -/
abbrev Idx := (List Bool × Bool) ⊕ List Bool

/-- Registers with values `Option Bool`, initially `⊥`. -/
abbrev Reg : ObjSpec := register (Option Bool) none

/-- The objects: registers and objects of type `S`. -/
abbrev Obj (S : ObjSpec) : Idx → ObjSpec := withRW (fun _ => Reg) S

/-- The initial memory: registers `⊥`, objects of type `S` in state `u`. -/
def mem0 (S : ObjSpec) (u : S.State) : (i : Idx) → (Obj S i).State
  | .inl _ => (none : Option Bool)
  | .inr _ => u

/-- Program counters of Figure 2. -/
inductive PC where
  | wr
  | rd1
  | chk
  | upd
  | rd2
  | rdR (Y : Bool)
  | done (w : Bool)
  deriving DecidableEq

/-- Local states: the process, its input and its program counter. -/
structure TL (k : ℕ) where
  /-- The process. -/
  p : Fin k
  /-- Its input. -/
  v : Bool
  /-- Its program counter. -/
  pc : PC

section Fig2

variable {S : ObjSpec} (rd : S.Op) {k : ℕ} (π : List Bool) (u : S.State) (team : Fin k → Bool)
  (o : Fin k → S.Op)

/-- `Q_X(q₀, op₁, …, opₖ)`: values reached by schedules of distinct processes starting on team
`X`. -/
def QX (X : Bool) (q : S.State) : Prop :=
  ∃ p σ, (p :: σ).Nodup ∧ team p = X ∧ apply S u o (p :: σ) = q

open Classical in
/-- The team that went first according to the response `r` of a read of `O`: `A` (`false`) iff the
value read is in `Q_A` (lines 11 and 26). -/
noncomputable def side (r : S.Resp) : Bool :=
  if ∃ q, (S.δ q rd).2 = r ∧ QX u team o false q then false else true

open Classical in
/-- The algorithm of Figure 2 at node `π`. -/
noncomputable def fig2 : Alg k (Obj S) where
  L := TL k
  init p x := ⟨p, x, .wr⟩
  act l := match l with
    | ⟨p, v, .wr⟩ => .access (.inl (π, team p)) (RWOp.write (some v)) (fun _ => ⟨p, v, .rd1⟩)
    | ⟨p, v, .rd1⟩ => .access (.inr π) rd (fun r => ⟨p, v,
        if r = (S.δ u rd).2 then (if team p = true ∧ (∃! q, team q = true) then .chk else .upd)
        else .rdR (side rd u team o r)⟩)
    | ⟨p, v, .chk⟩ => .access (.inl (π, false)) RWOp.read (fun r => ⟨p, v,
        match (r : Option Bool) with
        | some w => .done w
        | none => .upd⟩)
    | ⟨p, v, .upd⟩ => .access (.inr π) (o p) (fun _ => ⟨p, v, .rd2⟩)
    | ⟨p, v, .rd2⟩ => .access (.inr π) rd (fun r => ⟨p, v, .rdR (side rd u team o r)⟩)
    | ⟨p, v, .rdR Y⟩ => .access (.inl (π, Y)) RWOp.read (fun r => ⟨p, v,
        .done ((r : Option Bool).getD false)⟩)
    | ⟨_, _, .done w⟩ => .out w
  mem₀ := mem0 S u

/-- Program counters can be ranked: the code has no loops. -/
def pcRank : PC → ℕ
  | .wr => 6
  | .rd1 => 5
  | .chk => 4
  | .upd => 3
  | .rd2 => 2
  | .rdR _ => 1
  | .done _ => 0

theorem fig2_ranked : Ranked (fig2 rd π u team o) := by
  refine ⟨fun l => pcRank l.pc, fun l i o' κ r h => ?_⟩
  obtain ⟨p, v, pc⟩ := l
  cases pc with
  | wr => simp only [fig2] at h; cases h
          simp [pcRank]
  | rd1 =>
    simp only [fig2] at h; cases h
    simp only [pcRank]; split_ifs <;> simp [pcRank]
  | chk =>
    simp only [fig2] at h; cases h
    simp only [pcRank]; rcases (r : Option Bool) with _ | w <;> simp [pcRank]
  | upd => simp only [fig2] at h; cases h
           simp [pcRank]
  | rd2 => simp only [fig2] at h; cases h
           simp [pcRank]
  | rdR Y => simp only [fig2] at h; cases h
             simp [pcRank]
  | done w => simp [fig2] at h

/-- The objects accessed at node `π`. -/
def nodeFP (π : List Bool) (i : Idx) : Prop :=
  i = .inl (π, false) ∨ i = .inl (π, true) ∨ i = .inr π

theorem fig2_footprint : ∀ l i o' κ, (fig2 rd π u team o).act l = .access i o' κ → nodeFP π i := by
  intro l i o' κ h
  obtain ⟨p, v, pc⟩ := l
  cases pc with
  | done w => simp [fig2] at h
  | rdR Y =>
    simp only [fig2] at h; cases h
    cases Y <;> simp [nodeFP]
  | wr =>
    simp only [fig2] at h; cases h
    cases team p <;> simp [nodeFP]
  | _ => simp only [fig2] at h; cases h; simp [nodeFP]

end Fig2

end Podc.RecoverableHarder
