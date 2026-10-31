import Papers.PODC2018.NestingSafeRecoverable.Alg1Step

/-!
# The invariant of the correctness proof of Algorithm 1

The proof of Lemma 2 maintains, along every execution, a *ghost linearization* `L` of the
history and the ghost set `G` of the values that `R` has held. Linearization points:

* a `READ` is linearized when it reads `R` (lines 8/19); if it crashes before returning, the
  entry is retracted (`IsLinearization.erase_ro`);
* a `WRITE` is linearized when it writes `R` (line 4);
* a `WRITE` of `p` that may return without writing (the paper's case "`curr ≠ R`, a write by a
  different process `q` happened between the two reads of `R` by `p`") is linearized
  *speculatively* immediately before the write of `q` that disarms it ("phantom" entry). The
  phantom entry stays immediately followed by a write entry (`FW`), so it can be retracted
  (`IsLinearization.erase_absorbed`) if `p` writes `R` itself later or re-executes `WRITE`.

The pending `WRITE(val)` of `p` is in `L` iff `LinW` holds: `p` has written `val` to `R`
(`val ∈ G`), or `S_p = ⟨0, val⟩`, or `S_p = ⟨1, c⟩` with `R ≠ c`, or `p` is about to execute
line 3 with `temp ≠ R`. The freshness of written values makes `R ≠ c` stable.
-/

set_option linter.unusedSectionVars false

namespace Podc.NestingSafeRecoverable.Alg1

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] {v₀ : V}

/-- When the pending `WRITE(val)` of a process is linearized (`G`: values `R` has held, `R`:
current value of `R`, `s`: value of `S_p`, `pc`, `v`: local state). -/
def LinW (G : Set V) (R : V) (s : Bool × Option V) (val : V) (pc : PC1) (v : Loc1 V) : Prop :=
  val ∈ G ∨ s = (false, some val) ∨ (∃ c, s = (true, some c) ∧ R ≠ c) ∨ (pc = .w3 ∧ v.temp ≠ R)

/-- Facts about a process running `WRITE(val)` (or its recovery), by program location. -/
def LocW (G : Set V) (R : V) (s : Bool × Option V) (val : V) (pc : PC1) (v : Loc1 V) : Prop :=
  match pc with
  | .w2 => val ∉ G ∧ s ≠ (false, some val)
  | .w3 => val ∉ G ∧ s ≠ (false, some val) ∧ v.temp ∈ G
  | .w4 => val ∉ G ∧ s.1 = true
  | .w5 => val ∈ G
  | .w6 => val ∈ G ∧ s.1 = false
  | .r8 => False
  | .r9 => False
  | .c11 => True
  | .c12 => v.flag = s.1 ∧ v.curr = s.2
  | .c14 => s.1 = true ∧ v.curr = s.2
  | .c15 => s.1 = true ∧ v.curr = s.2 ∧
      ∀ c, s.2 = some c → (v.temp ≠ c → R ≠ c) ∧ (v.temp = c → val ∉ G)
  | .c16 => LinW G R s val pc v
  | .c17 => s = (false, some val)

/-- The invariant of a process running `WRITE(val)`, current instance `x`. -/
def WInv (L : List (OpId P × RWOp V)) (G : Set V) (R : V) (s : Bool × Option V) (x : OpId P)
    (val : V) (pc : PC1) (v : Loc1 V) : Prop :=
  (x ∈ L.map Prod.fst ↔ LinW G R s val pc v) ∧
  (x ∈ L.map Prod.fst → val ∉ G → FW L x (.write val)) ∧
  (s.1 = false → s.2 ≠ some val → val ∉ G) ∧
  (∀ c, s = (true, some c) → val ∈ G → R ≠ c) ∧
  LocW G R s val pc v

/-- The invariant of a process running `READ`, current instance `x`. -/
def RInv (L : List (OpId P × RWOp V)) (s : Bool × Option V) (x : OpId P) (pc : PC1)
    (v : Loc1 V) : Prop :=
  s.1 = false ∧
    ((pc = .r8 ∧ x ∉ L.map Prod.fst) ∨
      (pc = .r9 ∧ (register V v₀).respIn v₀ L x = some v.temp))

/-- The invariant of one process. -/
def PInv (L : List (OpId P × RWOp V)) (G : Set V) (R : V) (s : Bool × Option V) (x : OpId P) :
    Option (RWOp V × PC1 × Loc1 V) → Prop
  | none => s.1 = false
  | some (.read, pc, v) => RInv (v₀ := v₀) L s x pc v
  | some (.write val, pc, v) => WInv L G R s x val pc v

/-- Facts about the registers `S_p`. -/
def SInv (α : List (Label P (register V v₀))) (G : Set V) (s : Bool × Option V) : Prop :=
  (∀ c, s = (true, some c) → c ∈ G) ∧ s ≠ (true, none) ∧
    (∀ c, s = (false, some c) → ∃ y, opOf α y = some (.write c))

/-- The invariant of the correctness proof: `L` is a linearization of the history, its abstract
state is the value of `R`, `G` is a set of values containing `R` and only `v₀` and arguments of
`WRITE`s, and every process satisfies `PInv`. -/
structure Inv (C : (alg1 P V v₀).Cfg) (L : List (OpId P × RWOp V)) (G : Set V) : Prop where
  wf : Alg.WFInv C
  pend : Alg.PendOp C
  lin : IsLinearization (N C.hist) L
  state : (register V v₀).runOps v₀ (L.map Prod.snd) = Rv C
  gR : Rv C ∈ G
  gV : ∀ w ∈ G, w = v₀ ∨ ∃ y, opOf (N C.hist) y = some (.write w)
  sinv : ∀ p, SInv (N C.hist) G (Sv C p)
  proc : ∀ p, PInv (v₀ := v₀) L G (Rv C) (Sv C p) (curOp (N C.hist) p) (C.st p)

lemma inv_init : Inv (alg1 P V v₀).init [] {v₀} := by
  refine ⟨Alg.wfInv_init, Alg.pendOp_init, isLinearization_nil, rfl, rfl, ?_, ?_, ?_⟩
  · intro w hw; exact Or.inl hw
  · intro p; refine ⟨?_, ?_, ?_⟩ <;> simp [Sv, Alg.init]
  · intro p; simp [PInv, Sv, Alg.init]

/-- `L'` looks like `L` to every instance of a process other than `p`. -/
def LSame (p : P) (L L' : List (OpId P × RWOp V)) : Prop :=
  ∀ k : OpId P, k.1 ≠ p → (k ∈ L'.map Prod.fst ↔ k ∈ L.map Prod.fst) ∧
    (register V v₀).respIn v₀ L' k = (register V v₀).respIn v₀ L k ∧
    ∀ o, FW L k o → FW L' k o

lemma LSame.rfl' (p : P) (L : List (OpId P × RWOp V)) : LSame (v₀ := v₀) p L L :=
  fun _ _ => ⟨Iff.rfl, rfl, fun _ h => h⟩

lemma PInv.of_L {L L' : List (OpId P × RWOp V)} {G : Set V} {R : V} {s : Bool × Option V}
    {x : OpId P} {st : Option (RWOp V × PC1 × Loc1 V)} (h : PInv (v₀ := v₀) L G R s x st)
    (hmem : x ∈ L'.map Prod.fst ↔ x ∈ L.map Prod.fst)
    (hresp : (register V v₀).respIn v₀ L' x = (register V v₀).respIn v₀ L x)
    (hfw : ∀ o, FW L x o → FW L' x o) : PInv (v₀ := v₀) L' G R s x st := by
  rcases st with _ | ⟨_ | val, pc, v⟩
  · exact h
  · obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨h3, by rwa [hmem]⟩
    · exact Or.inr ⟨h3, by rwa [hresp]⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨hmem.trans h1, fun hx hv => hfw _ (h2 (hmem.1 hx) hv), h3, h4, h5⟩

lemma LSame.pinv {p q : P} {L L' : List (OpId P × RWOp V)} (hL : LSame (v₀ := v₀) p L L')
    (hq : q ≠ p) {G : Set V} {R : V} {s : Bool × Option V} {α : List (Label P (register V v₀))}
    {st : Option (RWOp V × PC1 × Loc1 V)}
    (h : PInv (v₀ := v₀) L G R s (curOp α q) st) : PInv (v₀ := v₀) L' G R s (curOp α q) st :=
  have := hL (curOp α q) hq
  h.of_L this.1 this.2.1 this.2.2

/-- Frame lemma: an event of `p` that changes neither `R`, nor the history `N(H)`, nor the
registers and local states of the other processes. -/
lemma Inv.frame {C C' : (alg1 P V v₀).Cfg} {L L' : List (OpId P × RWOp V)} {G : Set V} {p : P}
    (hI : Inv C L G) (hwf : Alg.WFInv C') (hpend : Alg.PendOp C')
    (hN : N C'.hist = N C.hist) (hR : Rv C' = Rv C) (hS : ∀ q, q ≠ p → Sv C' q = Sv C q)
    (hst : ∀ q, q ≠ p → C'.st q = C.st q)
    (hlin : IsLinearization (N C.hist) L')
    (hstate : (register V v₀).runOps v₀ (L'.map Prod.snd) = (register V v₀).runOps v₀ (L.map Prod.snd))
    (hsame : LSame (v₀ := v₀) p L L')
    (hSp : SInv (N C.hist) G (Sv C' p))
    (hPp : PInv (v₀ := v₀) L' G (Rv C) (Sv C' p) (curOp (N C.hist) p) (C'.st p)) :
    Inv C' L' G := by
  refine ⟨hwf, hpend, hN ▸ hlin, by rw [hstate, hR]; exact hI.state, hR ▸ hI.gR,
    hN ▸ hI.gV, fun q => ?_, fun q => ?_⟩
  · by_cases hq : q = p
    · subst hq; rw [hN]; exact hSp
    · rw [hN, hS q hq]; exact hI.sinv q
  · rw [hN, hR]
    by_cases hq : q = p
    · subst hq; exact hPp
    · rw [hS q hq, hst q hq]; exact hsame.pinv hq (hI.proc q)

end Podc.NestingSafeRecoverable.Alg1
