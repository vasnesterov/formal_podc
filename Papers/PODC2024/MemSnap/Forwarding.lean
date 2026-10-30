import Papers.PODC2024.MemSnap.Steps

/-!
# The Forwarding Invariant `I₁` (Figure 1, Lemma 7.1)

`FInv` is an inductive strengthening of the paper's Forwarding Invariant `I₁` (stated literally
as `I1`): it adds the shape of the local states (which line a process can be at, and its pending
operation), the facts `x̂_π ≤ x_π` at lines 11–12 and `x = X` at the write of line 1, and, crucially,
extends Part (6) to processes in the *second* iteration of the for-loop that have read `B[i]` and
whose copy `b` is still current (`B[i] = b`). Without this extension Part (7) is not preserved by
a successful CAS of another process, so the paper's `I₁` is not inductive by itself.

* `FInv.init`, `FInv.step` — `FInv` is an inductive invariant; `finv_of_arun`.
* `I1`, `FInv.i1` — the nine parts of Figure 1; `lemma_7_1`: **Lemma 7.1** (`I₁` is an
  invariant of Algorithm 2).
-/

set_option linter.unusedSectionVars false

namespace Podc.MemSnap

open Cslib.SharedMemory

variable {W : ObjSpec} {K : Type} [DecidableEq K] {v₀ : K → W.State}
variable {P : Type} [DecidableEq P] {σ : P}

/-! ## Accessors of local states -/

/-- `(i, k₂, b)` for a process at lines 10–12 of `forward(i)`. -/
def Loc.rd : Loc W K → Option (K × Bool × (W.State × ℕ))
  | .f10 i _ k b => some (i, k, b)
  | .f11 i _ k b _ => some (i, k, b)
  | .f12 i _ k b _ _ => some (i, k, b)
  | _ => none

/-- `(i, b, x)` for a process at lines 11–12 of `forward(i)`. -/
def Loc.poised : Loc W K → Option (K × (W.State × ℕ) × ℕ)
  | .f11 i _ _ b x => some (i, b, x)
  | .f12 i _ _ b x _ => some (i, b, x)
  | _ => none

/-- `pc ∈ [3, 5]`: the process executes an `observe` (including the `forward` of line 3). -/
def Loc.IsObs : Loc W K → Prop
  | .f9 _ none _ => True
  | .f10 _ none _ _ => True
  | .f11 _ none _ _ _ => True
  | .f12 _ none _ _ _ _ => True
  | .o4 _ => True
  | .o5 _ => True
  | _ => False

@[simp] lemma Loc.rd_idle : (Loc.idle : Loc W K).rd = none := rfl
@[simp] lemma Loc.rd_c1 : (Loc.c1 : Loc W K).rd = none := rfl
@[simp] lemma Loc.rd_c1w (x : ℕ) : (Loc.c1w x : Loc W K).rd = none := rfl
@[simp] lemma Loc.rd_c2 : (Loc.c2 : Loc W K).rd = none := rfl
@[simp] lemma Loc.rd_f9 (i : K) (u : Option W.Op) (k : Bool) : (Loc.f9 i u k).rd = none := rfl
@[simp] lemma Loc.rd_f10 (i : K) (u : Option W.Op) (k : Bool) (b : W.State × ℕ) :
    (Loc.f10 i u k b).rd = some (i, k, b) := rfl
@[simp] lemma Loc.rd_f11 (i : K) (u : Option W.Op) (k : Bool) (b : W.State × ℕ) (x : ℕ) :
    (Loc.f11 i u k b x).rd = some (i, k, b) := rfl
@[simp] lemma Loc.rd_f12 (i : K) (u : Option W.Op) (k : Bool) (b : W.State × ℕ) (x : ℕ)
    (a : W.State) : (Loc.f12 i u k b x a).rd = some (i, k, b) := rfl
@[simp] lemma Loc.rd_o4 (i : K) : (Loc.o4 i : Loc W K).rd = none := rfl
@[simp] lemma Loc.rd_o5 (v : W.State) : (Loc.o5 v : Loc W K).rd = none := rfl
@[simp] lemma Loc.rd_u7 (i : K) (o : W.Op) : (Loc.u7 i o : Loc W K).rd = none := rfl
@[simp] lemma Loc.rd_u8 (r : W.Resp) : (Loc.u8 r : Loc W K).rd = none := rfl
@[simp] lemma Loc.poised_idle : (Loc.idle : Loc W K).poised = none := rfl
@[simp] lemma Loc.poised_c1 : (Loc.c1 : Loc W K).poised = none := rfl
@[simp] lemma Loc.poised_c1w (x : ℕ) : (Loc.c1w x : Loc W K).poised = none := rfl
@[simp] lemma Loc.poised_c2 : (Loc.c2 : Loc W K).poised = none := rfl
@[simp] lemma Loc.poised_f9 (i : K) (u : Option W.Op) (k : Bool) : (Loc.f9 i u k).poised = none :=
  rfl
@[simp] lemma Loc.poised_f10 (i : K) (u : Option W.Op) (k : Bool) (b : W.State × ℕ) :
    (Loc.f10 i u k b).poised = none := rfl
@[simp] lemma Loc.poised_f11 (i : K) (u : Option W.Op) (k : Bool) (b : W.State × ℕ) (x : ℕ) :
    (Loc.f11 i u k b x).poised = some (i, b, x) := rfl
@[simp] lemma Loc.poised_f12 (i : K) (u : Option W.Op) (k : Bool) (b : W.State × ℕ) (x : ℕ)
    (a : W.State) : (Loc.f12 i u k b x a).poised = some (i, b, x) := rfl
@[simp] lemma Loc.poised_o4 (i : K) : (Loc.o4 i : Loc W K).poised = none := rfl
@[simp] lemma Loc.poised_o5 (v : W.State) : (Loc.o5 v : Loc W K).poised = none := rfl
@[simp] lemma Loc.poised_u7 (i : K) (o : W.Op) : (Loc.u7 i o : Loc W K).poised = none := rfl
@[simp] lemma Loc.poised_u8 (r : W.Resp) : (Loc.u8 r : Loc W K).poised = none := rfl

@[simp] lemma fcont_rd (i : K) (u : Option W.Op) : (fcont i u).rd = none := by cases u <;> rfl
@[simp] lemma fcont_poised (i : K) (u : Option W.Op) : (fcont i u).poised = none := by
  cases u <;> rfl

/-! ## Shape of local states -/

/-- Shape of a process inside `forward(i)` called with `u`, with pending operation `o`. -/
def fwdShape (σ π : P) (i : K) : Option W.Op → Option (COp W K) → Prop
  | none, o => π = σ ∧ o = some (.observe i)
  | some op, o => π ≠ σ ∧ o = some (.update i op)

/-- Which lines a process can be at, given its pending operation. -/
def Shape (σ π : P) : Loc W K → Option (COp W K) → Prop
  | .idle, o => o = none
  | .c1, o => π = σ ∧ o = some .click
  | .c1w _, o => π = σ ∧ o = some .click
  | .c2, o => π = σ ∧ o = some .click
  | .f9 i u _, o => fwdShape σ π i u o
  | .f10 i u _ _, o => fwdShape σ π i u o
  | .f11 i u _ _ _, o => fwdShape σ π i u o
  | .f12 i u _ _ _ _, o => fwdShape σ π i u o
  | .o4 i, o => π = σ ∧ o = some (.observe i)
  | .o5 _, o => π = σ ∧ ∃ i, o = some (.observe i)
  | .u7 i op, o => π ≠ σ ∧ o = some (.update i op)
  | .u8 _, o => π ≠ σ ∧ ∃ i op, o = some (.update i op)

lemma fcont_shape {π : P} {i : K} {u : Option W.Op} {o : Option (COp W K)}
    (h : fwdShape σ π i u o) : Shape σ π (fcont i u) o := by
  cases u <;> exact h

/-! ## The invariant -/

/-- The "mission" of `forward` called by `π` on component `i` (Parts (6)/(7)): either
`B[i].seq ≥ x̂_π` already, or every process poised to change `B[i]` will make it so. -/
def Mission (C : Cfg W K v₀ P) (G : Ghost W K v₀ P) (π : P) (i : K) : Prop :=
  G.xh π ≤ (C.B i).2 ∨ ∀ μ b x, (C.loc μ).poised = some (i, b, x) → C.B i = b → G.xh π ≤ x

variable (σ) in
/-- The inductive strengthening of the Forwarding Invariant `I₁`. -/
structure FInv (C : Cfg W K v₀ P) (G : Ghost W K v₀ P) : Prop where
  shape : ∀ π, Shape σ π (C.loc π) (C.pend π)
  /-- Part (1). -/
  seq_le : ∀ j, (C.B j).2 ≤ C.X
  /-- Part (2). -/
  obs_xh : ∀ π, (C.loc π).IsObs → G.xh π = C.X
  /-- Part (3) (for all processes). -/
  xh_le : ∀ π, G.xh π ≤ C.X
  c1w_x : ∀ π x, C.loc π = .c1w x → x = C.X
  /-- Part (4), plus `x̂ ≤ x`. -/
  poised : ∀ π i b x, (C.loc π).poised = some (i, b, x) → b.2 < x ∧ x ≤ C.X ∧ G.xh π ≤ x
  /-- Part (5). -/
  rd_lt : ∀ π i k b, (C.loc π).rd = some (i, k, b) → C.B i ≠ b → b.2 < (C.B i).2
  /-- Part (6) at lines 10–12, extended to the second iteration with `B[i] = b`. -/
  mission : ∀ π i k b, (C.loc π).rd = some (i, k, b) → (C.B i ≠ b ∨ k = true) → Mission C G π i
  /-- Part (6) at line 9 of the second iteration. -/
  mission9 : ∀ π i u, C.loc π = .f9 i u true → Mission C G π i
  /-- Part (7). -/
  done2 : ∀ π i b, (C.loc π).rd = some (i, true, b) → C.B i ≠ b → G.xh π ≤ (C.B i).2
  /-- Part (8). -/
  o4 : ∀ π i, C.loc π = .o4 i → (C.B i).2 = C.X
  /-- Part (9). -/
  u7 : ∀ π i o, C.loc π = .u7 i o → G.xh π ≤ (C.B i).2

/-! ## Preservation -/

section Preservation

variable {C C' : Cfg W K v₀ P} {G G' : Ghost W K v₀ P} {π : P}

lemma shape_none {l : Loc W K} (h : Shape σ π l none) : l = .idle := by
  cases l with
  | idle => rfl
  | f9 i u _ | f10 i u _ _ | f11 i u _ _ _ | f12 i u _ _ _ _ =>
    cases u <;> simp [Shape, fwdShape] at h
  | _ => simp [Shape] at h

/-- Mission of `μ` survives a step of `π ≠ μ` that keeps `B[i]` and `x̂_μ`, and in which `π`
becomes poised only with `x = X`. -/
lemma mission_frame (hI : FInv σ C G) {μ : P} {i : K} (hm : Mission C G μ i)
    (hB : C'.B i = C.B i) (hxh : G'.xh μ = G.xh μ)
    (hloc : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν)
    (hpo : ∀ j b x, (C'.loc π).poised = some (j, b, x) →
      (C.loc π).poised = some (j, b, x) ∨ x = C.X) :
    Mission C' G' μ i := by
  rcases hm with hm | hm
  · left; rw [hB, hxh]; exact hm
  · right
    intro ν b x hν hb
    rw [hxh]
    by_cases hνπ : ν = π
    · subst hνπ
      rcases hpo _ _ _ hν with h1 | h1
      · exact hm ν b x h1 (hB ▸ hb)
      · rw [h1]; exact hI.xh_le μ
    · rw [hloc ν hνπ] at hν
      exact hm ν b x hν (hB ▸ hb)

/-- Frame lemma: a step of `π` that keeps `X`, `B`, and the local states, pending operations and
`x̂` of the other processes preserves `FInv` provided the new local state `l'` of `π` satisfies
the local obligations. -/
lemma FInv.frame (hI : FInv σ C G) (l' : Loc W K)
    (hX : C'.X = C.X) (hB : ∀ j, C'.B j = C.B j)
    (hloc : C'.loc = Function.update C.loc π l')
    (hpend : ∀ μ, μ ≠ π → C'.pend μ = C.pend μ) (hxh : ∀ μ, μ ≠ π → G'.xh μ = G.xh μ)
    (ha : Shape σ π l' (C'.pend π))
    (hb : l'.IsObs → G'.xh π = C.X) (hxl : G'.xh π ≤ C.X)
    (hc : ∀ x, l' = .c1w x → x = C.X)
    (hd : ∀ i b x, l'.poised = some (i, b, x) → b.2 < x ∧ x ≤ C.X ∧ G'.xh π ≤ x)
    (he : ∀ i k b, l'.rd = some (i, k, b) → C.B i ≠ b → b.2 < (C.B i).2)
    (hf : ∀ i k b, l'.rd = some (i, k, b) → (C.B i ≠ b ∨ k = true) → Mission C' G' π i)
    (hg : ∀ i u, l' = .f9 i u true → Mission C' G' π i)
    (hh : ∀ i b, l'.rd = some (i, true, b) → C.B i ≠ b → G'.xh π ≤ (C.B i).2)
    (hi : ∀ i, l' = .o4 i → (C.B i).2 = C.X)
    (hj : ∀ i o, l' = .u7 i o → G'.xh π ≤ (C.B i).2)
    (hk : ∀ j b x, l'.poised = some (j, b, x) → (C.loc π).poised = some (j, b, x) ∨ x = C.X) :
    FInv σ C' G' := by
  have hlocπ : C'.loc π = l' := by rw [hloc]; simp
  have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by rw [hloc, Function.update_of_ne h]
  have hpo : ∀ j b x, (C'.loc π).poised = some (j, b, x) →
      (C.loc π).poised = some (j, b, x) ∨ x = C.X := by rw [hlocπ]; exact hk
  have mf : ∀ μ i, μ ≠ π → Mission C G μ i → Mission C' G' μ i := fun μ i hμ hm =>
    mission_frame hI hm (hB i) (hxh μ hμ) hlocν hpo
  refine ⟨fun μ => ?_, fun j => ?_, fun μ => ?_, fun μ => ?_, fun μ x => ?_, fun μ i b x => ?_,
    fun μ i k b => ?_, fun μ i k b => ?_, fun μ i u => ?_, fun μ i b => ?_, fun μ i => ?_,
    fun μ i o => ?_⟩ <;> try simp only [hX, hB]
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact ha
    · rw [hlocν μ hμ, hpend μ hμ]; exact hI.shape μ
  · exact hI.seq_le j
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact hb
    · rw [hlocν μ hμ, hxh μ hμ]; exact hI.obs_xh μ
  · by_cases hμ : μ = π
    · subst hμ; exact hxl
    · rw [hxh μ hμ]; exact hI.xh_le μ
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact hc x
    · rw [hlocν μ hμ]; exact hI.c1w_x μ x
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact hd i b x
    · rw [hlocν μ hμ, hxh μ hμ]; exact hI.poised μ i b x
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact he i k b
    · rw [hlocν μ hμ]; exact hI.rd_lt μ i k b
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact hf i k b
    · rw [hlocν μ hμ]; intro h1 h2; exact mf μ i hμ (hI.mission μ i k b h1 h2)
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact hg i u
    · rw [hlocν μ hμ]; intro h1; exact mf μ i hμ (hI.mission9 μ i u h1)
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact hh i b
    · rw [hlocν μ hμ, hxh μ hμ]; exact hI.done2 μ i b
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact hi i
    · rw [hlocν μ hμ]; exact hI.o4 μ i
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ]; exact hj i o
    · rw [hlocν μ hμ, hxh μ hμ]; exact hI.u7 μ i o

lemma Shape.isObs {μ : P} {l : Loc W K} {o : Option (COp W K)} (h : Shape σ μ l o)
    (hl : l.IsObs) : μ = σ := by
  cases l with
  | f9 i u _ | f10 i u _ _ | f11 i u _ _ _ | f12 i u _ _ _ _ =>
    cases u
    · exact h.1
    · simp [Loc.IsObs] at hl
  | o4 i => exact h.1
  | o5 v => exact h.1
  | _ => simp [Loc.IsObs] at hl

lemma Shape.c1w {μ : P} {x : ℕ} {o : Option (COp W K)} (h : Shape σ μ (.c1w x) o) : μ = σ := h.1

lemma Shape.o4 {μ : P} {i : K} {o : Option (COp W K)} (h : Shape σ μ (.o4 i) o) : μ = σ := h.1

lemma augStep_tau_xh (C : Cfg W K v₀ P) (π : P) (G : Ghost W K v₀ P) :
    (augStep σ C (.tau π) G).xh = G.xh := by
  simp only [augStep]; split <;> rfl

lemma augStep_ret_xh (C : Cfg W K v₀ P) (π : P) (r : CResp W) (G : Ghost W K v₀ P) :
    (augStep σ C (.ret π r) G).xh = G.xh := rfl

lemma isObs_fcont {i : K} {u : Option W.Op} (h : (fcont i u : Loc W K).IsObs) : u = none := by
  cases u
  · rfl
  · simp [fcont, Loc.IsObs] at h

lemma poised_rd {l : Loc W K} {i : K} {b : W.State × ℕ} {x : ℕ}
    (h : l.poised = some (i, b, x)) : ∃ k, l.rd = some (i, k, b) := by
  cases l <;> simp [Loc.poised] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> exact ⟨_, rfl⟩

/-- A successful CAS installing a sequence number larger than every copy makes every mission on
that component trivially true. -/
lemma mission_after_cas (hI : FInv σ C G) {π μ : P} {i : K} {b : W.State × ℕ} {x : ℕ}
    {a : W.State} (hb : C.B i = b) (hbx : b.2 < x)
    (hB : ∀ j, C'.B j = if j = i then (a, x) else C.B j)
    (hloc : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν) (hπ : (C'.loc π).poised = none) :
    Mission C' G μ i := by
  right
  intro ν b' x' hν hb'
  have hνπ : ν ≠ π := by rintro rfl; rw [hπ] at hν; cases hν
  rw [hloc ν hνπ] at hν
  simp only [hB i, ↓reduceIte] at hb'
  obtain ⟨k, hrd⟩ := poised_rd hν
  by_cases hne : C.B i = b'
  · rw [hb, ← hb'] at hne; rw [hne] at hbx; simp at hbx
  · have := hI.rd_lt ν i k b' hrd hne
    rw [hb, ← hb'] at this; simp at this; omega

/-- Preservation by a successful CAS at line 12. -/
lemma FInv.cas_succ (hI : FInv σ C G) {π : P}
    (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {i : K}
    {u : Option W.Op} {k : Bool} {b : W.State × ℕ} {x : ℕ} {a : W.State}
    (hl : C.loc π = .f12 i u k b x a) (hb : C.B i = b) (hsh : Shape σ π (.f12 i u k b x a) (C.pend π))
    (hpoπ : b.2 < x ∧ x ≤ C.X ∧ G.xh π ≤ x) :
    FInv σ C' { G with PP := (augStep σ C (.tau π) G).PP } := by
  obtain ⟨hp, hX, -, hB, hloc⟩ := tau_f12_succ h hl hb
  have hlocπ : C'.loc π = fcont i u := by rw [hloc]; simp
  have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by
    rw [hloc, Function.update_of_ne h]
  have hπpo : (C'.loc π).poised = none := by rw [hlocπ]; simp
  have hBj : ∀ j, j ≠ i → C'.B j = C.B j := fun j hj => by simp [hB j, hj]
  have hBi : C'.B i = (a, x) := by simp [hB i]
  -- missions on other components survive, on `i` they become trivial
  have mis : ∀ μ j, Mission C G μ j → Mission C' { G with PP := (augStep σ C (.tau π) G).PP } μ j :=
    by
    intro μ j hm
    by_cases hj : j = i
    · subst hj; exact mission_after_cas hI hb hpoπ.1 hB hlocν hπpo
    · exact mission_frame hI hm (hBj j hj) rfl hlocν (by rw [hπpo]; simp)
  refine ⟨fun μ => ?_, fun j => ?_, fun μ hμ => ?_, fun μ => ?_, fun μ y hμ => ?_,
    fun μ j b' y hμ => ?_, fun μ j k' b' hμ => ?_, fun μ j k' b' hμ => ?_, fun μ j u' hμ => ?_,
    fun μ j b' hμ => ?_, fun μ j hμ => ?_, fun μ j o hμ => ?_⟩ <;> try simp only [hX]
  · by_cases hμ : μ = π
    · subst hμ; rw [hlocπ, hp]; exact fcont_shape hsh
    · rw [hlocν μ hμ, hp]; exact hI.shape μ
  · rw [hB j]; split_ifs
    · exact hpoπ.2.1
    · exact hI.seq_le j
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hlocπ] at hμ
      exact hI.obs_xh μ (by rw [hl]; rw [isObs_fcont hμ]; simp [Loc.IsObs])
    · rw [hlocν μ hμπ] at hμ; exact hI.obs_xh μ hμ
  · exact hI.xh_le μ
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hlocπ] at hμ; cases u <;> simp [fcont] at hμ
    · rw [hlocν μ hμπ] at hμ; exact hI.c1w_x μ y hμ
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hπpo] at hμ; cases hμ
    · rw [hlocν μ hμπ] at hμ; exact hI.poised μ j b' y hμ
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hlocπ] at hμ; simp at hμ
    · rw [hlocν μ hμπ] at hμ
      intro hne
      by_cases hj : j = i
      · subst hj; rw [hBi]
        by_cases hb' : C.B j = b'
        · rw [hb] at hb'; subst hb'; exact hpoπ.1
        · have := hI.rd_lt μ j k' b' hμ hb'; rw [hb] at this; exact this.trans hpoπ.1
      · rw [hBj j hj] at hne ⊢; exact hI.rd_lt μ j k' b' hμ hne
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hlocπ] at hμ; simp at hμ
    · rw [hlocν μ hμπ] at hμ
      intro h2
      by_cases hj : j = i
      · subst hj; exact mission_after_cas hI hb hpoπ.1 hB hlocν hπpo
      · rw [hBj j hj] at h2; exact mis μ j (hI.mission μ j k' b' hμ h2)
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hlocπ] at hμ; cases u <;> simp [fcont] at hμ
    · rw [hlocν μ hμπ] at hμ; exact mis μ j (hI.mission9 μ j u' hμ)
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hlocπ] at hμ; simp at hμ
    · rw [hlocν μ hμπ] at hμ
      intro hne
      by_cases hj : j = i
      · subst hj; rw [hBi]; simp only
        by_cases hb' : C.B j = b'
        · rcases hI.mission μ j true b' hμ (Or.inr rfl) with hm | hm
          · rw [hb'] at hm; rw [hb] at hb'; subst hb'; exact hm.trans hpoπ.1.le
          · exact hm π b x (by rw [hl]; rfl) (hb.trans rfl)
        · have := hI.done2 μ j b' hμ hb'; rw [hb] at this; exact this.trans hpoπ.1.le
      · rw [hBj j hj] at hne ⊢; exact hI.done2 μ j b' hμ hne
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hlocπ] at hμ; cases u <;> simp [fcont] at hμ; subst hμ
      rw [hBi]
      have h1 := hI.obs_xh μ (by rw [hl]; simp [Loc.IsObs])
      simp only; omega
    · rw [hlocν μ hμπ] at hμ
      by_cases hj : j = i
      · subst hj; have := hI.o4 μ j hμ; rw [hb] at this; omega
      · rw [hBj j hj]; exact hI.o4 μ j hμ
  · by_cases hμπ : μ = π
    · subst hμπ; rw [hlocπ] at hμ; cases u <;> simp [fcont] at hμ; obtain ⟨rfl, rfl⟩ := hμ
      rw [hBi]; exact hpoπ.2.2
    · rw [hlocν μ hμπ] at hμ
      by_cases hj : j = i
      · subst hj; have := hI.u7 μ j o hμ; rw [hb] at this; rw [hBi]; exact this.trans hpoπ.1.le
      · rw [hBj j hj]; exact hI.u7 μ j o hμ

theorem FInv.step (hI : FInv σ C G) {ℓ : CLabel W K v₀ P}
    (h : (memSnap W K v₀ σ).step C ℓ = some C') : FInv σ C' (augStep σ C ℓ G) := by
  cases ℓ with
  | inv π o =>
    obtain ⟨hp, hall, hmem, hpend, hloc⟩ := inv_eq h
    have hidle := shape_none (hp ▸ hI.shape π)
    have hX : C'.X = C.X := by simp [Cfg.X, hmem]
    have hB : ∀ j, C'.B j = C.B j := by simp [Cfg.B, hmem]
    have hpπ : C'.pend π = some o := by rw [hpend]; simp
    have hxh : ∀ μ, μ ≠ π → (augStep σ C (.inv π o) G).xh μ = G.xh μ := by
      intro μ hμ; cases o <;> simp [augStep, Function.update_of_ne hμ]
    refine hI.frame (invoke W K o) hX hB hloc
      (fun μ hμ => by rw [hpend, Function.update_of_ne hμ]) hxh ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      cases o <;> simp_all [invoke, Shape, fwdShape, Allowed, Loc.IsObs, augStep] <;>
      exact hI.xh_le _
  | tau π =>
    rw [show augStep σ C (.tau π) G = { G with PP := (augStep σ C (.tau π) G).PP } from by
      cases h' : augStep σ C (.tau π) G; rw [← augStep_tau_xh C π G, h']]
    obtain ⟨hn1, hn2, hn3, hn4⟩ := tau_ret_none h
    have hsh := hI.shape π
    cases hl : C.loc π with
    | idle => exact absurd hl hn1
    | c2 => exact absurd hl hn2
    | o5 v => exact absurd hl (hn3 v)
    | u8 r => exact absurd hl (hn4 r)
    | c1 =>
      obtain ⟨hp, hmem, hloc⟩ := tau_c1 h hl
      rw [hl] at hsh
      refine hI.frame (G' := { G with PP := _ }) (.c1w C.X) (by simp [Cfg.X, hmem])
        (by simp [Cfg.B, hmem]) hloc (fun μ _ => by rw [hp]) (fun _ _ => rfl) (by rw [hp]; exact hsh)
        (by simp [Loc.IsObs]) (hI.xh_le π) (fun x hx => by cases hx; rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp
    | c1w x =>
      obtain ⟨hp, hX, hA, hB, hloc⟩ := tau_c1w h hl
      have hσ : π = σ := (hl ▸ hsh).1
      have hx := hI.c1w_x π x hl
      have hlocπ : C'.loc π = .c2 := by rw [hloc]; simp
      have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by
        rw [hloc, Function.update_of_ne h]
      have notπ : ∀ μ, (C.loc μ).IsObs → False := fun μ hμ => by
        have := (hI.shape μ).isObs hμ
        subst this; subst hσ; rw [hl] at hμ; exact hμ
      refine ⟨fun μ => ?_, fun j => ?_, fun μ hμ => ?_, fun μ => ?_, fun μ y hμ => ?_,
        fun μ i b y hμ => ?_, fun μ i k b hμ => ?_, fun μ i k b hμ => ?_, fun μ i u hμ => ?_,
        fun μ i b hμ => ?_, fun μ i hμ => ?_, fun μ i o hμ => ?_⟩ <;>
        try simp only [hX, hB]
      · by_cases hμ : μ = π
        · subst hμ; rw [hlocπ, hp]; rw [hl] at hsh; exact hsh
        · rw [hlocν μ hμ, hp]; exact hI.shape μ
      · have := hI.seq_le j; omega
      · exfalso; by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; exact hμ.elim
        · rw [hlocν μ hμπ] at hμ; exact (notπ μ hμ).elim
      · have := hI.xh_le μ; omega
      · by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; cases hμ
        · rw [hlocν μ hμπ] at hμ
          have := (hμ ▸ hI.shape μ).c1w; exact absurd (this.trans hσ.symm) hμπ
      · by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; cases hμ
        · rw [hlocν μ hμπ] at hμ; have := hI.poised μ i b y hμ; omega
      · by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; cases hμ
        · rw [hlocν μ hμπ] at hμ; exact hI.rd_lt μ i k b hμ
      · by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; cases hμ
        · rw [hlocν μ hμπ] at hμ
          intro h2
          exact mission_frame hI (hI.mission μ i k b hμ h2) (hB i) rfl hlocν
            (by rw [hlocπ]; simp)
      · by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; cases hμ
        · rw [hlocν μ hμπ] at hμ
          exact mission_frame hI (hI.mission9 μ i u hμ) (hB i) rfl hlocν (by rw [hlocπ]; simp)
      · by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; cases hμ
        · rw [hlocν μ hμπ] at hμ; exact hI.done2 μ i b hμ
      · by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; cases hμ
        · rw [hlocν μ hμπ] at hμ
          exact absurd ((hμ ▸ hI.shape μ).o4.trans hσ.symm) hμπ
      · by_cases hμπ : μ = π
        · subst hμπ; rw [hlocπ] at hμ; cases hμ
        · rw [hlocν μ hμπ] at hμ; exact hI.u7 μ i o hμ
    | f9 i u k =>
      obtain ⟨hp, hmem, hloc⟩ := tau_f9 h hl
      have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by
        rw [hloc, Function.update_of_ne h]
      have hpo : ∀ j b x, (C'.loc π).poised = some (j, b, x) →
          (C.loc π).poised = some (j, b, x) ∨ x = C.X := by rw [hloc]; simp
      refine hI.frame (G' := { G with PP := _ }) (.f10 i u k (C.B i)) (by simp [Cfg.X, hmem])
        (by simp [Cfg.B, hmem]) hloc (fun μ _ => by rw [hp]) (fun _ _ => rfl)
        (by rw [hp]; rw [hl] at hsh; exact hsh)
        (fun ho => hI.obs_xh π (by rw [hl]; cases u <;> simp_all [Loc.IsObs])) (hI.xh_le π)
        (by simp) (by simp) (by simp) ?_ (by simp) (by simp) (by simp) (by simp) (by simp)
      intro j k' b hrd hk
      simp only [Loc.rd_f10, Option.some.injEq, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      have hk' : k = true := by simpa using hk
      subst hk'
      exact mission_frame hI (hI.mission9 π _ u hl) (by simp [Cfg.B, hmem]) rfl hlocν hpo
    | f10 i u k b =>
      obtain ⟨hp, hmem, hloc⟩ := tau_f10 h hl
      have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by
        rw [hloc, Function.update_of_ne h]
      have hBb : b.2 ≤ (C.B i).2 := by
        by_cases hb : C.B i = b
        · rw [hb]
        · exact (hI.rd_lt π i k b (by rw [hl]; rfl) hb).le
      have hX := hI.seq_le i
      rw [hl] at hsh
      split_ifs at hloc with hbx
      · refine hI.frame (G' := { G with PP := _ }) (fcont i u) (by simp [Cfg.X, hmem])
          (by simp [Cfg.B, hmem]) hloc (fun μ _ => by rw [hp]) (fun _ _ => rfl)
          (by rw [hp]; exact fcont_shape hsh)
          (fun ho => hI.obs_xh π (by rw [hl]; rw [isObs_fcont ho]; simp [Loc.IsObs]))
          (hI.xh_le π) (by cases u <;> simp [fcont]) (by simp) (by simp) (by simp)
          (by cases u <;> simp [fcont]) (by simp) ?_ ?_ (by simp)
        · intro j hj; cases u <;> simp [fcont] at hj; subst hj; omega
        · intro j o hj; cases u <;> simp [fcont] at hj; obtain ⟨rfl, rfl⟩ := hj
          have := hI.xh_le π; dsimp only; omega
      · have hlt : b.2 < C.X := lt_of_le_of_ne (hBb.trans hX) hbx
        have hpo : ∀ j b' x, (C'.loc π).poised = some (j, b', x) →
            (C.loc π).poised = some (j, b', x) ∨ x = C.X := by
          rw [hloc]; simp only [Function.update_self, Loc.poised_f11, Option.some.injEq,
            Prod.mk.injEq]; rintro j b' x ⟨-, -, rfl⟩; right; rfl
        refine hI.frame (G' := { G with PP := _ }) (.f11 i u k b C.X) (by simp [Cfg.X, hmem])
          (by simp [Cfg.B, hmem]) hloc (fun μ _ => by rw [hp]) (fun _ _ => rfl)
          (by rw [hp]; exact hsh)
          (fun ho => hI.obs_xh π (by rw [hl]; cases u <;> simp_all [Loc.IsObs])) (hI.xh_le π)
          (by simp) ?_ ?_ ?_ (by simp) ?_ (by simp) (by simp) ?_
        · simp only [Loc.poised_f11, Option.some.injEq, Prod.mk.injEq]
          rintro j b' x ⟨rfl, rfl, rfl⟩; exact ⟨hlt, le_rfl, hI.xh_le π⟩
        · intro j k' b' h'; exact hI.rd_lt π j k' b' (by rw [hl]; exact h')
        · intro j k' b' h' h2
          exact mission_frame hI (hI.mission π j k' b' (by rw [hl]; exact h') h2)
            (by simp [Cfg.B, hmem]) rfl hlocν hpo
        · intro j b' h'; exact hI.done2 π j b' (by rw [hl]; exact h')
        · simp only [Loc.poised_f11, Option.some.injEq, Prod.mk.injEq]
          rintro _ _ _ ⟨-, -, rfl⟩; exact Or.inr rfl
    | f11 i u k b x =>
      obtain ⟨hp, hmem, hloc⟩ := tau_f11 h hl
      have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by
        rw [hloc, Function.update_of_ne h]
      have hpo : ∀ j b' x', (C'.loc π).poised = some (j, b', x') →
          (C.loc π).poised = some (j, b', x') ∨ x' = C.X := by
        rw [hloc, hl]; simp
      rw [hl] at hsh
      refine hI.frame (G' := { G with PP := _ }) (.f12 i u k b x (C.A i)) (by simp [Cfg.X, hmem])
        (by simp [Cfg.B, hmem]) hloc (fun μ _ => by rw [hp]) (fun _ _ => rfl)
        (by rw [hp]; exact hsh)
        (fun ho => hI.obs_xh π (by rw [hl]; cases u <;> simp_all [Loc.IsObs])) (hI.xh_le π)
        (by simp) ?_ ?_ ?_ (by simp) ?_ (by simp) (by simp) ?_
      · intro j b' y h'; exact hI.poised π j b' y (by rw [hl]; exact h')
      · intro j k' b' h'; exact hI.rd_lt π j k' b' (by rw [hl]; exact h')
      · intro j k' b' h' h2
        exact mission_frame hI (hI.mission π j k' b' (by rw [hl]; exact h') h2)
          (by simp [Cfg.B, hmem]) rfl hlocν hpo
      · intro j b' h'; exact hI.done2 π j b' (by rw [hl]; exact h')
      · intro j b' y h'; rw [hl]; exact Or.inl h'
    | f12 i u k b x a =>
      rw [hl] at hsh
      have hpoπ := hI.poised π i b x (by rw [hl]; rfl)
      by_cases hb : C.B i = b
      · exact FInv.cas_succ hI h hl hb hsh hpoπ
      · obtain ⟨hp, hmem, hloc⟩ := tau_f12_fail h hl hb
        have hlocν : ∀ ν, ν ≠ π → C'.loc ν = C.loc ν := fun ν h => by
          rw [hloc, Function.update_of_ne h]
        have hpo : ∀ j b' x', (C'.loc π).poised = some (j, b', x') →
            (C.loc π).poised = some (j, b', x') ∨ x' = C.X := by
          rw [hloc]; cases k <;> simp
        cases k
        · refine hI.frame (G' := { G with PP := _ }) (.f9 i u true) (by simp [Cfg.X, hmem])
            (by simp [Cfg.B, hmem]) hloc (fun μ _ => by rw [hp]) (fun _ _ => rfl)
            (by rw [hp]; exact hsh)
            (fun ho => hI.obs_xh π (by rw [hl]; cases u <;> simp_all [Loc.IsObs])) (hI.xh_le π)
            (by simp) (by simp) (by simp) (by simp) ?_ (by simp) (by simp) (by simp)
            (by simp)
          rintro j u' ⟨rfl, rfl, -⟩
          exact mission_frame hI (hI.mission π _ false b (by rw [hl]; rfl) (Or.inl hb))
            (by simp [Cfg.B, hmem]) rfl hlocν hpo
        · have hd := hI.done2 π i b (by rw [hl]; rfl) hb
          refine hI.frame (G' := { G with PP := _ }) (fcont i u) (by simp [Cfg.X, hmem])
            (by simp [Cfg.B, hmem]) hloc (fun μ _ => by rw [hp]) (fun _ _ => rfl)
            (by rw [hp]; exact fcont_shape hsh)
            (fun ho => hI.obs_xh π (by rw [hl]; rw [isObs_fcont ho]; simp [Loc.IsObs]))
            (hI.xh_le π) (by cases u <;> simp [fcont]) (by simp) (by simp) (by simp)
            (by cases u <;> simp [fcont]) (by simp) ?_ ?_ (by simp)
          · intro j hj; cases u <;> simp [fcont] at hj; subst hj
            have h1 := hI.obs_xh π (by rw [hl]; simp [Loc.IsObs])
            have h2 := hI.seq_le i
            omega
          · intro j o hj; cases u <;> simp [fcont] at hj; obtain ⟨rfl, rfl⟩ := hj; exact hd
    | o4 i =>
      obtain ⟨hp, hmem, hloc⟩ := tau_o4 h hl
      rw [hl] at hsh
      refine hI.frame (G' := { G with PP := _ }) (.o5 (C.B i).1) (by simp [Cfg.X, hmem])
        (by simp [Cfg.B, hmem]) hloc (fun μ _ => by rw [hp]) (fun _ _ => rfl)
        (by rw [hp]; exact ⟨hsh.1, i, hsh.2⟩)
        (fun _ => hI.obs_xh π (by rw [hl]; simp [Loc.IsObs])) (hI.xh_le π)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    | u7 i o =>
      obtain ⟨hp, hX, -, hB, hloc⟩ := tau_u7 h hl
      rw [hl] at hsh
      refine hI.frame (G' := { G with PP := _ }) (.u8 (W.δ (C.A i) o).2) hX hB hloc
        (fun μ _ => by rw [hp]) (fun _ _ => rfl)
        (by rw [hp]; exact ⟨hsh.1, i, o, hsh.2⟩)
        (by simp [Loc.IsObs]) (hI.xh_le π)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  | ret π r =>
    obtain ⟨hp, hmem, hpend, hloc, -⟩ := ret_eq h
    refine hI.frame .idle (by simp [Cfg.X, hmem]) (by simp [Cfg.B, hmem]) hloc
      (fun μ hμ => by rw [hpend, Function.update_of_ne hμ]) (fun _ _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ <;> simp_all [Shape, Loc.IsObs, augStep_ret_xh, hI.xh_le π]

end Preservation

/-! ## Lemma 7.1 -/

lemma FInv.init : FInv σ (memSnap W K v₀ σ).initCfg (ginit W K v₀ P) := by
  refine ⟨fun _ => rfl, fun _ => le_rfl, fun _ h => ?_, fun _ => le_rfl, fun _ _ h => ?_,
    fun _ _ _ _ h => ?_, fun _ _ _ _ h => ?_, fun _ _ _ _ h => ?_, fun _ _ _ h => ?_,
    fun _ _ _ h => ?_, fun _ _ h => ?_, fun _ _ _ h => ?_⟩ <;>
    simp [memSnap, Impl.initCfg, Loc.IsObs] at h

/-- `FInv` holds in every reachable configuration of Algorithm 2. -/
theorem finv_of_arun {α : List (CLabel W K v₀ P)} {C : Cfg W K v₀ P} {G : Ghost W K v₀ P}
    (h : arun σ α = some (C, G)) : FInv σ C G :=
  arun_induction (Q := fun _ C G => FInv σ C G) FInv.init
    (fun _ _ _ _ _ _ hI hst => hI.step hst) h

variable (σ) in
/-- **Statement `I₁`** (Figure 1), the Forwarding Invariant, in our notation: `pc ∈ [3, 5]` is
`IsObs`, `pc ∈ [6, 8]` is `IsUpd`, `pc ∈ [10, 12]` with `(i, k, b)` is `rd = some (i, k, b)`,
`pc ∈ [11, 12]` with `(i, b, x)` is `poised = some (i, b, x)`, `k = 1` is `k₂ = false`. -/
def I1 (C : Cfg W K v₀ P) (G : Ghost W K v₀ P) : Prop :=
  -- (1)
  (∀ j, C.X ≥ (C.B j).2) ∧
  -- (2)
  ((C.loc σ).IsObs → C.X = G.xh σ) ∧
  -- (3)
  (∀ μ, μ ≠ σ → (C.loc μ).IsUpd → C.X ≥ G.xh μ) ∧
  -- (4)
  (∀ μ i b x, (C.loc μ).poised = some (i, b, x) → C.X ≥ x ∧ x > b.2) ∧
  -- (5)
  (∀ μ i k b, (C.loc μ).rd = some (i, k, b) → C.B i ≠ b → (C.B i).2 > b.2) ∧
  -- (6)
  (∀ μ i, ((∃ b, (C.loc μ).rd = some (i, false, b) ∧ C.B i ≠ b) ∨
      (∃ u, C.loc μ = .f9 i u true)) →
    ((C.B i).2 ≥ G.xh μ ∨
      ∀ μ' b' x', ((C.loc μ').poised = some (i, b', x') ∧ C.B i = b') → x' ≥ G.xh μ)) ∧
  -- (7)
  (∀ μ i b, (C.loc μ).rd = some (i, true, b) ∧ C.B i ≠ b → (C.B i).2 ≥ G.xh μ) ∧
  -- (8)
  (∀ i, C.loc σ = .o4 i → (C.B i).2 = C.X) ∧
  -- (9)
  (∀ μ i o, μ ≠ σ → C.loc μ = .u7 i o → (C.B i).2 ≥ G.xh μ)

lemma FInv.i1 {C : Cfg W K v₀ P} {G : Ghost W K v₀ P} (hI : FInv σ C G) : I1 σ C G := by
  refine ⟨hI.seq_le, fun h => (hI.obs_xh σ h).symm, fun μ _ _ => hI.xh_le μ,
    fun μ i b x h => ⟨(hI.poised μ i b x h).2.1, (hI.poised μ i b x h).1⟩, hI.rd_lt,
    fun μ i h => ?_, fun μ i b h => hI.done2 μ i b h.1 h.2, hI.o4 σ, fun μ i o _ h => hI.u7 μ i o h⟩
  have hm : Mission C G μ i := by
    rcases h with ⟨b, hb, hne⟩ | ⟨u, hu⟩
    · exact hI.mission μ i false b hb (Or.inl hne)
    · exact hI.mission9 μ i u hu
  rcases hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr fun μ' b' x' h => hm μ' b' x' h.1 h.2

/-- **Lemma 7.1** of [MemSnap]: statement `I₁` (Figure 1) is an invariant of Algorithm 2. -/
theorem lemma_7_1 {α : List (CLabel W K v₀ P)} {C : Cfg W K v₀ P} {G : Ghost W K v₀ P}
    (h : arun σ α = some (C, G)) : I1 σ C G :=
  (finv_of_arun h).i1

end Podc.MemSnap
