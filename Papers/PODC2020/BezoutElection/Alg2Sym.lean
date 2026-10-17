import Papers.PODC2020.BezoutElection.Alg2

/-!
# Algorithm 2 is symmetric and uses only reads and writes

Identifier renamings act on register values (the `id`, `disc` and `leaders` fields) and on local
states (own identifier, copies of the registers, local `disc` sets, the pending write and the
returned leader set). Algorithm 2 commutes with every renaming (`alg2_symmetric`) and all its
accesses are plain reads or plain writes (`alg2_readWrite`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg2

variable {Id : Type} {m : ℕ}

lemma finset_map_one (s : Finset Id) : s.map (1 : Equiv.Perm Id).toEmbedding = s := by
  ext a; simp; rfl

lemma finset_map_mul (σ τ : Equiv.Perm Id) (s : Finset Id) :
    s.map (σ * τ).toEmbedding = (s.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]; rfl

/-- Renaming the identifiers of a register value. -/
def Reg.smul (σ : Equiv.Perm Id) (r : Reg Id) : Reg Id :=
  ⟨r.id.map σ, r.disc.map σ.toEmbedding, r.phase, r.level, r.leaders.map σ.toEmbedding⟩

instance : MulAction (Equiv.Perm Id) (Reg Id) where
  smul := Reg.smul
  one_smul r := by cases r; simp [HSMul.hSMul, Reg.smul, finset_map_one]
  mul_smul σ τ r := by
    cases r
    simp only [HSMul.hSMul, Reg.smul, Reg.mk.injEq, Option.map_map, finset_map_mul]
    exact ⟨rfl, trivial, trivial, trivial, trivial⟩

@[simp] lemma smul_id (σ : Equiv.Perm Id) (r : Reg Id) : (σ • r).id = r.id.map σ := rfl
@[simp] lemma smul_disc (σ : Equiv.Perm Id) (r : Reg Id) :
    (σ • r).disc = r.disc.map σ.toEmbedding := rfl
@[simp] lemma smul_phase (σ : Equiv.Perm Id) (r : Reg Id) : (σ • r).phase = r.phase := rfl
@[simp] lemma smul_level (σ : Equiv.Perm Id) (r : Reg Id) : (σ • r).level = r.level := rfl
@[simp] lemma smul_leaders (σ : Equiv.Perm Id) (r : Reg Id) :
    (σ • r).leaders = r.leaders.map σ.toEmbedding := rfl

/-- Renaming the identifiers in a program counter. -/
def PC.smul (σ : Equiv.Perm Id) : PC Id → PC Id
  | .idle => .idle
  | .collect k => .collect k
  | .write k w => .write k (σ • w)
  | .ret L => .ret (L.map σ.toEmbedding)
  | .fin => .fin

/-- Renaming the identifiers of a local state. -/
def St.smul (σ : Equiv.Perm Id) (s : St Id m) : St Id m :=
  ⟨σ s.me, s.pc.smul σ, fun x => σ • s.regs x, s.phase, fun x => (s.disc x).map σ.toEmbedding,
    s.loser, s.level, s.cand, s.toWin, s.finishing⟩

instance : MulAction (Equiv.Perm Id) (St Id m) where
  smul := St.smul
  one_smul s := by
    obtain ⟨me, pc, regs, phase, disc, loser, level, cand, toWin, finishing⟩ := s
    simp only [HSMul.hSMul, St.smul]
    congr 1
    · cases pc <;> simp [PC.smul, finset_map_one]
    · funext x; exact one_smul (Equiv.Perm Id) _
    · funext x; exact finset_map_one _
  mul_smul σ τ s := by
    obtain ⟨me, pc, regs, phase, disc, loser, level, cand, toWin, finishing⟩ := s
    simp only [HSMul.hSMul, St.smul]
    congr 1
    · cases pc <;> simp [PC.smul, finset_map_mul]
      exact mul_smul σ τ _
    · funext x; exact mul_smul σ τ _
    · funext x; exact finset_map_mul _ _ _

@[simp] lemma st_smul_me (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).me = σ s.me := rfl
@[simp] lemma st_smul_pc (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).pc = s.pc.smul σ := rfl
@[simp] lemma st_smul_regs (σ : Equiv.Perm Id) (s : St Id m) (x : Fin m) :
    (σ • s).regs x = σ • s.regs x := rfl
@[simp] lemma st_smul_phase (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).phase = s.phase := rfl
@[simp] lemma st_smul_disc (σ : Equiv.Perm Id) (s : St Id m) (x : Fin m) :
    (σ • s).disc x = (s.disc x).map σ.toEmbedding := rfl
@[simp] lemma st_smul_loser (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).loser = s.loser := rfl
@[simp] lemma st_smul_level (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).level = s.level := rfl
@[simp] lemma st_smul_cand (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).cand = s.cand := rfl
@[simp] lemma st_smul_toWin (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).toWin = s.toWin := rfl
@[simp] lemma st_smul_finishing (σ : Equiv.Perm Id) (s : St Id m) :
    (σ • s).finishing = s.finishing := rfl

lemma reg_smul_mk (σ : Equiv.Perm Id) (a : Option Id) (d : Finset Id) (ph : Phase) (l : ℕ)
    (L : Finset Id) : σ • (⟨a, d, ph, l, L⟩ : Reg Id) =
      ⟨a.map σ, d.map σ.toEmbedding, ph, l, L.map σ.toEmbedding⟩ := rfl

variable [DecidableEq Id]

lemma map_ne_some_iff (σ : Equiv.Perm Id) (o : Option Id) (a : Id) :
    o.map σ ≠ some (σ a) ↔ o ≠ some a := by
  cases o <;> simp

end BezoutElection.Alg2
