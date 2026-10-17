import Papers.PODC2020.BezoutElection.Alg1

/-!
# Algorithm 1 is symmetric and uses only reads and writes

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Section 3 (Algorithm 1).

Identifier renamings `σ : Equiv.Perm Id` act on register values (`id`, `discarded`) and on local
states (`id_i`, `discarded_i`, and the identifiers in the program counter). Algorithm 1 is
equivariant under this action as soon as the output map is (`alg1_symmetric`: *symmetry with
equality*, identifiers are only stored and compared), and every read-modify-write it performs is
a plain read or a plain write (`alg1_readWrite`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg1

variable {Id : Type}

/-- Renaming the identifiers of a register value. -/
instance : MulAction (Equiv.Perm Id) (Reg Id) where
  smul σ r := ⟨r.id.map σ, r.disc.map σ.toEmbedding, r.phase⟩
  one_smul r := by
    obtain ⟨i, d, ph⟩ := r
    change Reg.mk _ _ _ = _
    congr 1
    · cases i <;> rfl
    · ext x; simp only [Finset.mem_map_equiv]; exact Iff.rfl
  mul_smul σ τ r := by
    obtain ⟨i, d, ph⟩ := r
    change Reg.mk _ _ _ = Reg.mk _ _ _
    congr 1
    · cases i <;> rfl
    · show d.map (σ * τ).toEmbedding = (d.map τ.toEmbedding).map σ.toEmbedding
      rw [Finset.map_map]; rfl

@[simp] lemma Reg.smul_id (σ : Equiv.Perm Id) (r : Reg Id) : (σ • r).id = r.id.map σ := rfl
@[simp] lemma Reg.smul_disc (σ : Equiv.Perm Id) (r : Reg Id) :
    (σ • r).disc = r.disc.map σ.toEmbedding := rfl
@[simp] lemma Reg.smul_mk (σ : Equiv.Perm Id) (i : Option Id) (d : Finset Id) (ph : Phase) :
    σ • (Reg.mk i d ph) = Reg.mk (i.map σ) (d.map σ.toEmbedding) ph := rfl
@[simp] lemma Reg.smul_phase (σ : Equiv.Perm Id) (r : Reg Id) : (σ • r).phase = r.phase := rfl

/-- Renaming the identifiers in a program counter. -/
def PC.map (σ : Equiv.Perm Id) : PC Id → PC Id
  | .idle => .idle
  | .read => .read
  | .write w => .write (σ • w)
  | .ret ℓ => .ret (σ ℓ)
  | .fin => .fin

@[simp] lemma PC.map_idle (σ : Equiv.Perm Id) : PC.map σ .idle = .idle := rfl
@[simp] lemma PC.map_read (σ : Equiv.Perm Id) : PC.map σ .read = .read := rfl
@[simp] lemma PC.map_write (σ : Equiv.Perm Id) (w : Reg Id) :
    PC.map σ (.write w) = .write (σ • w) := rfl
@[simp] lemma PC.map_ret (σ : Equiv.Perm Id) (ℓ : Id) : PC.map σ (.ret ℓ) = .ret (σ ℓ) := rfl
@[simp] lemma PC.map_fin (σ : Equiv.Perm Id) : PC.map σ .fin = .fin := rfl

lemma PC.map_one (pc : PC Id) : PC.map 1 pc = pc := by
  cases pc <;> simp

lemma PC.map_mul (σ τ : Equiv.Perm Id) (pc : PC Id) :
    PC.map (σ * τ) pc = PC.map σ (PC.map τ pc) := by
  cases pc <;> simp [mul_smul, Equiv.Perm.mul_apply]

/-- Renaming the identifiers of a local state. -/
instance : MulAction (Equiv.Perm Id) (St Id) where
  smul σ s := ⟨σ s.me, s.pc.map σ, s.phase, s.disc.map σ.toEmbedding, s.loser⟩
  one_smul s := by
    obtain ⟨me, pc, ph, d, l⟩ := s
    change St.mk _ _ _ _ _ = _
    congr 1
    · exact PC.map_one pc
    · ext x; simp only [Finset.mem_map_equiv]; exact Iff.rfl
  mul_smul σ τ s := by
    obtain ⟨me, pc, ph, d, l⟩ := s
    change St.mk _ _ _ _ _ = St.mk _ _ _ _ _
    congr 1
    · exact PC.map_mul σ τ pc
    · show d.map (σ * τ).toEmbedding = (d.map τ.toEmbedding).map σ.toEmbedding
      rw [Finset.map_map]; rfl

@[simp] lemma St.smul_me (σ : Equiv.Perm Id) (s : St Id) : (σ • s).me = σ s.me := rfl
@[simp] lemma St.smul_pc (σ : Equiv.Perm Id) (s : St Id) : (σ • s).pc = s.pc.map σ := rfl
@[simp] lemma St.smul_phase (σ : Equiv.Perm Id) (s : St Id) : (σ • s).phase = s.phase := rfl
@[simp] lemma St.smul_disc (σ : Equiv.Perm Id) (s : St Id) :
    (σ • s).disc = s.disc.map σ.toEmbedding := rfl
@[simp] lemma St.smul_mk (σ : Equiv.Perm Id) (me : Id) (pc : PC Id) (ph : Phase) (d : Finset Id)
    (l : Bool) : σ • (St.mk me pc ph d l) = St.mk (σ me) (pc.map σ) ph (d.map σ.toEmbedding) l := rfl
@[simp] lemma St.smul_loser (σ : Equiv.Perm Id) (s : St Id) : (σ • s).loser = s.loser := rfl

lemma St.smul_with_pc (σ : Equiv.Perm Id) (s : St Id) (pc : PC Id) :
    ({ σ • s with pc := pc.map σ } : St Id) = σ • { s with pc := pc } := rfl

variable [DecidableEq Id]

/-- The local computation after a read is equivariant. -/
lemma afterRead_smul (n : ℕ) (σ : Equiv.Perm Id) (s : St Id) (r : Reg Id) :
    afterRead n (σ • s) (σ • r) = σ • afterRead n s r := by
  obtain ⟨me, pc, ph, d, l⟩ := s
  obtain ⟨i, rd, rph⟩ := r
  have hcard : (rd.map σ.toEmbedding).card = rd.card := Finset.card_map _
  have hnone : i.map σ = none ↔ i = none := Option.map_eq_none_iff
  have hsome : i.map σ = some (σ me) ↔ i = some me := by
    cases i <;> simp
  have hmem : σ me ∈ rd.map σ.toEmbedding ↔ me ∈ rd := by simp
  unfold afterRead
  simp only [Reg.smul_phase, St.smul_phase, Reg.smul_disc, Reg.smul_id, St.smul_loser,
    St.smul_me, St.smul_disc, hcard, hnone, ne_eq, hsome, hmem]
  split_ifs
  all_goals first
    | rfl
    | (cases i <;> rfl)
    | simp [Finset.map_union, Finset.map_insert]

variable {R : Type} [Inhabited R]

/-- **Algorithm 1 is symmetric** (with equality) when the output map is. -/
theorem alg1_symmetric (n : ℕ) (out : Id → Id → R)
    (hout : ∀ (σ : Equiv.Perm Id) a b, out (σ a) (σ b) = out a b) :
    (alg1 Id n out).Symmetric where
  bot σ := by
    show σ • (Reg.init : Reg Id) = Reg.init
    simp [Reg.init]
  init σ a := by
    show St.mk (σ a) .idle .electing ∅ false = σ • St.mk a .idle .electing ∅ false
    simp
  invoke σ s o := by
    simp only [alg1, St.smul_pc]
    cases s.pc <;> simp
  act σ s := by
    simp only [alg1, St.smul_pc]
    cases h : s.pc with
    | idle => rfl
    | read =>
      simp only [PC.map_read, SymAction.smul, smul_inv_smul, SymAction.rmw.injEq, true_and]
      funext v
      rw [← afterRead_smul, smul_inv_smul]
    | write w =>
      simp only [PC.map_write, SymAction.smul, SymAction.rmw.injEq, true_and]
      rfl
    | ret ℓ =>
      simp only [PC.map_ret, SymAction.smul, St.smul_me, hout]
      rfl
    | fin => rfl

/-- **Algorithm 1 only uses reads and writes.** -/
theorem alg1_readWrite (n : ℕ) (out : Id → Id → R) : (alg1 Id n out).ReadWrite := by
  intro s x f k h
  simp only [alg1] at h
  cases hpc : s.pc with
  | read =>
    rw [hpc] at h
    simp only [SymAction.rmw.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact Or.inl fun _ => rfl
  | write w =>
    rw [hpc] at h
    simp only [SymAction.rmw.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact Or.inr ⟨_, _, fun _ => rfl, fun _ => rfl⟩
  | _ => rw [hpc] at h; simp at h

end BezoutElection.Alg1
