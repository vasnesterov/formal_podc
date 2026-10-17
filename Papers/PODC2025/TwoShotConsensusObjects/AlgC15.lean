import Papers.PODC2025.TwoShotConsensusObjects.AlgC15Core

/-!
# Class `C₁.₅` solves two-shot two-process consensus (Section 5.2, Algorithms 1 and 2)

Process `a` runs Algorithm 1 (role `p₀`), process `b` runs Algorithm 2 (role `p₁`); the registers
`Val[i]`, `Ret[i]` are indexed by roles. The code is the paper's, line by line; the only change
is that "return `Val[j]`" is a read of `Val[j]` followed by an output of the value read.

Safety is proved with an invariant (`Inv`) of reachable configurations which keeps a ghost
*role history* `h` (the roles of the operations applied to `O` so far, in order; the state of `O`
is `after O s (IL P h)`), the values of the local variables and registers in terms of `h`, and
the facts learned by reading `Ret[·]` (`RF0`, `RF1`, `RF2`). At each decision, the decision
rules are correct by `core0`, `core1a`, `core1b` (Lemma 1 of the paper).
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable C1Common

namespace C15Alg

/-- Local states of Algorithms 1 (`p…`) and 2 (`q…`), with the local variables. -/
inductive Loc (ρ : Type)
  /-- line 1: `Val[0] ← v` -/
  | p0 (v : Bool)
  /-- line 2: `v[0][0] ← O.f` -/
  | p1
  /-- line 3: `Ret[0] ← v[0][0]` -/
  | p2 (r : ρ)
  /-- line 4: `v[1][0] ← Ret[1]` -/
  | p3 (r : ρ)
  /-- line 5: `v[0][1] ← O.f'` (then decide, lines 6–19) -/
  | p4 (r : ρ) (x : Option ρ)
  /-- line 20: `Val[1] ← v` -/
  | q0 (v : Bool)
  /-- line 21: `v[1][0] ← O.g` -/
  | q1
  /-- line 22: `Ret[1] ← v[1][0]` -/
  | q2 (r : ρ)
  /-- line 23: `v[0][0] ← Ret[0]` -/
  | q3 (r : ρ)
  /-- line 24: `v[1][1] ← O.g'` (then lines 25–30 if `v[0][0] ≠ ⊥`) -/
  | q4 (r : ρ) (y : Option ρ)
  /-- line 32: `v[0][0] ← Ret[0]` (then decide, lines 33–48) -/
  | q5 (r r' : ρ)
  /-- `return Val[j]`: read `Val[j]` -/
  | dec (j : Fin 2)
  /-- output `w` -/
  | out (w : Bool)

variable {O : ObjSpec} (P : Par O)

/-- The code of Algorithms 1 and 2. -/
noncomputable def act : Loc O.Resp → Act (Obj O) (Loc O.Resp)
  | .p0 v => .access (.inl (.val 0)) (RWOp.write (some v)) fun _ => .p1
  | .p1 => .access (.inr ()) P.f fun r => .p2 r
  | .p2 r => .access (.inl (.ret 0)) (RWOp.write (some r)) fun _ => .p3 r
  | .p3 r => .access (.inl (.ret 1)) RWOp.read fun x => .p4 r x
  | .p4 r x => .access (.inr ()) P.f' fun r' => .dec (dec0 P r x r')
  | .q0 v => .access (.inl (.val 1)) (RWOp.write (some v)) fun _ => .q1
  | .q1 => .access (.inr ()) P.g fun r => .q2 r
  | .q2 r => .access (.inl (.ret 1)) (RWOp.write (some r)) fun _ => .q3 r
  | .q3 r => .access (.inl (.ret 0)) RWOp.read fun y => .q4 r y
  | .q4 r y => .access (.inr ()) P.g' fun r' =>
      match y with
      | some v => .dec (dec1a P v)
      | none => .q5 r r'
  | .q5 r r' => .access (.inl (.ret 0)) RWOp.read fun z => .dec (dec1b P r r' z)
  | .dec j => .access (.inl (.val j)) RWOp.read fun v => .out ((v : Option Bool).getD false)
  | .out w => .out w

/-- The algorithm: process `a` runs Algorithm 1, process `b` Algorithm 2; `O` starts in `s`,
all registers in `⊥`. -/
noncomputable abbrev alg : Alg 2 (Obj O) where
  L := Loc O.Resp
  init p v := if p = P.a then .p0 v else .q0 v
  act := act P
  mem₀ := fun
    | .inl (.val _) => (none : Option Bool)
    | .inl (.ret _) => (none : Option O.Resp)
    | .inr () => P.s

/-! ## The invariant -/

variable {P}

/-- Content of `Val[i]`. -/
def valR (C : Cfg (alg P)) (i : Fin 2) : Option Bool := C.mem (.inl (.val i))

/-- Content of `Ret[i]`. -/
def retR (C : Cfg (alg P)) (i : Fin 2) : Option O.Resp := C.mem (.inl (.ret i))

/-- State of `O`. -/
def objS (C : Cfg (alg P)) : O.State := C.mem (.inr ())

variable (P) in
/-- Invariant of the local state of `p₀` (`x` = inputs indexed by roles). -/
def I0 (x : Fin 2 → Bool) : Loc O.Resp → Option Bool → Option O.Resp → List (Fin 2) → Prop
  | .p0 v, _, rt, h => v = x 0 ∧ h.count 0 = 0 ∧ V P h P.a = [] ∧ rt = none
  | .p1, vl, rt, h => h.count 0 = 0 ∧ V P h P.a = [] ∧ vl = some (x 0) ∧ rt = none
  | .p2 r, vl, rt, h => h.count 0 = 1 ∧ V P h P.a = [r] ∧ vl = some (x 0) ∧ rt = none
  | .p3 r, vl, rt, h => h.count 0 = 1 ∧ V P h P.a = [r] ∧ vl = some (x 0) ∧ rt = some r
  | .p4 r y, vl, rt, h =>
    h.count 0 = 1 ∧ V P h P.a = [r] ∧ vl = some (x 0) ∧ rt = some r ∧ RF0 y h
  | .dec j, vl, rt, h => h.count 0 = 2 ∧ vl = some (x 0) ∧
    (∃ r, rt = some r ∧ (V P h P.a).head? = some r) ∧ h.head? = some j
  | .out w, vl, rt, h => h.count 0 = 2 ∧ vl = some (x 0) ∧
    (∃ r, rt = some r ∧ (V P h P.a).head? = some r) ∧ ∃ j, h.head? = some j ∧ w = x j
  | _, _, _, _ => False

variable (P) in
/-- Invariant of the local state of `p₁`. -/
def I1 (x : Fin 2 → Bool) : Loc O.Resp → Option Bool → Option O.Resp → List (Fin 2) → Prop
  | .q0 v, _, rt, h => v = x 1 ∧ h.count 1 = 0 ∧ V P h P.b = [] ∧ rt = none
  | .q1, vl, rt, h => h.count 1 = 0 ∧ V P h P.b = [] ∧ vl = some (x 1) ∧ rt = none
  | .q2 r, vl, rt, h => h.count 1 = 1 ∧ V P h P.b = [r] ∧ vl = some (x 1) ∧ rt = none
  | .q3 r, vl, rt, h => h.count 1 = 1 ∧ V P h P.b = [r] ∧ vl = some (x 1) ∧ rt = some r
  | .q4 r y, vl, rt, h =>
    h.count 1 = 1 ∧ V P h P.b = [r] ∧ vl = some (x 1) ∧ rt = some r ∧ RF1 P y h
  | .q5 r r', vl, rt, h => h.count 1 = 2 ∧ V P h P.b = [r, r'] ∧ vl = some (x 1) ∧
    rt = some r ∧ Snap h fun h₁ => h₁.count 1 = 1 ∧ h₁.count 0 ≤ 1
  | .dec j, vl, rt, h => h.count 1 = 2 ∧ vl = some (x 1) ∧ (∃ r, rt = some r) ∧
    h.head? = some j
  | .out w, vl, rt, h => h.count 1 = 2 ∧ vl = some (x 1) ∧ (∃ r, rt = some r) ∧
    ∃ j, h.head? = some j ∧ w = x j
  | _, _, _, _ => False

variable (P) in
/-- The process playing role `j`. -/
def pr (j : Fin 2) : Fin 2 := if j = 0 then P.a else P.b

variable (P) in
/-- The invariant of reachable configurations (`x` = inputs indexed by processes). -/
def Inv (x : Fin 2 → Bool) (C : Cfg (alg P)) : Prop :=
  ∃ h : List (Fin 2), objS C = after O P.s (IL P h) ∧
    I0 P (fun j => x (pr P j)) (C.loc P.a) (valR C 0) (retR C 0) h ∧
    I1 P (fun j => x (pr P j)) (C.loc P.b) (valR C 1) (retR C 1) h

/-! ## Lemmas about role histories -/

lemma IL_append (h : List (Fin 2)) (r : Fin 2) :
    IL P (h ++ [r]) = IL P h ++
      [if r = 0 then (P.a, if h.count 0 = 0 then P.f else P.f')
        else (P.b, if h.count 1 = 0 then P.g else P.g')] :=
  il_append O P.a P.b P.f P.f' P.g P.g' h r

lemma V_append_0a (h : List (Fin 2)) :
    V P (h ++ [0]) P.a =
      V P h P.a ++ [(O.δ (after O P.s (IL P h)) (if h.count 0 = 0 then P.f else P.f')).2] := by
  simp [V, IL_append, view_append, view_single_self]

lemma V_append_1b (h : List (Fin 2)) :
    V P (h ++ [1]) P.b =
      V P h P.b ++ [(O.δ (after O P.s (IL P h)) (if h.count 1 = 0 then P.g else P.g')).2] := by
  simp [V, IL_append, view_append, view_single_self]

lemma V_append_0b (hab : P.a ≠ P.b) (h : List (Fin 2)) : V P (h ++ [0]) P.b = V P h P.b := by
  simp [V, IL_append, view_append, view_single_other O _ hab]

lemma V_append_1a (hab : P.a ≠ P.b) (h : List (Fin 2)) : V P (h ++ [1]) P.a = V P h P.a := by
  simp [V, IL_append, view_append, view_single_other O _ (Ne.symm hab)]

lemma head?_append_of_eq {α : Type} {l : List α} {v : α} (h : l.head? = some v) (t : List α) :
    (l ++ t).head? = some v := by
  cases l with
  | nil => simp at h
  | cons y l => simpa using h

lemma count_append_ne (h : List (Fin 2)) {r q : Fin 2} (hrq : r ≠ q) :
    (h ++ [r]).count q = h.count q := by
  simp [List.count_append, hrq]

lemma count_append_self (h : List (Fin 2)) (r : Fin 2) :
    (h ++ [r]).count r = h.count r + 1 := by
  simp [List.count_append]

/-! ## Lemmas about the local invariants -/

variable {x : Fin 2 → Bool} {l : Loc O.Resp} {vl : Option Bool} {rt : Option O.Resp}
  {h : List (Fin 2)}

lemma I0_mono (hab : P.a ≠ P.b) (hI : I0 P x l vl rt h) : I0 P x l vl rt (h ++ [1]) := by
  have hc := count_append_ne h (show (1 : Fin 2) ≠ 0 by decide)
  have hV := V_append_1a hab h
  cases l with
  | p0 v => simpa [I0, hc, hV] using hI
  | p1 => simpa [I0, hc, hV] using hI
  | p2 r => simpa [I0, hc, hV] using hI
  | p3 r => simpa [I0, hc, hV] using hI
  | p4 r y =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    refine ⟨hc ▸ h1, hV ▸ h2, h3, h4, ?_⟩
    cases y <;> simp only [RF0] at h5 ⊢ <;> exact Snap.append h5 _
  | dec j =>
    obtain ⟨h1, h2, h3, h4⟩ := hI
    exact ⟨hc ▸ h1, h2, hV ▸ h3, head?_append_of_eq h4 _⟩
  | out w =>
    obtain ⟨h1, h2, h3, j, h4, h5⟩ := hI
    exact ⟨hc ▸ h1, h2, hV ▸ h3, j, head?_append_of_eq h4 _, h5⟩
  | _ => exact hI.elim

lemma I1_mono (hab : P.a ≠ P.b) (hI : I1 P x l vl rt h) : I1 P x l vl rt (h ++ [0]) := by
  have hc := count_append_ne h (show (0 : Fin 2) ≠ 1 by decide)
  have hV := V_append_0b hab h
  have hVa := V_append_0a (P := P) h
  cases l with
  | q0 v => simpa [I1, hc, hV] using hI
  | q1 => simpa [I1, hc, hV] using hI
  | q2 r => simpa [I1, hc, hV] using hI
  | q3 r => simpa [I1, hc, hV] using hI
  | q4 r y =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    refine ⟨hc ▸ h1, hV ▸ h2, h3, h4, ?_⟩
    cases y with
    | none => simp only [RF1] at h5 ⊢; exact Snap.append h5 _
    | some v => exact ⟨hVa ▸ head?_append_of_eq h5.1 _, Snap.append h5.2 _⟩
  | q5 r r' =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    exact ⟨hc ▸ h1, hV ▸ h2, h3, h4, Snap.append h5 _⟩
  | dec j =>
    obtain ⟨h1, h2, h3, h4⟩ := hI
    exact ⟨hc ▸ h1, h2, h3, head?_append_of_eq h4 _⟩
  | out w =>
    obtain ⟨h1, h2, h3, j, h4, h5⟩ := hI
    exact ⟨hc ▸ h1, h2, h3, j, head?_append_of_eq h4 _, h5⟩
  | _ => exact hI.elim

lemma I0_ret (hI : I0 P x l vl rt h) :
    (rt = none → h.count 0 ≤ 1) ∧
      ∀ v, rt = some v → (V P h P.a).head? = some v ∧ 1 ≤ h.count 0 := by
  cases l <;> simp only [I0] at hI
  case p0 => exact ⟨fun _ => by omega, fun v hv => by simp_all⟩
  case p1 => exact ⟨fun _ => by omega, fun v hv => by simp_all⟩
  case p2 => exact ⟨fun _ => by omega, fun v hv => by simp_all⟩
  case p3 => exact ⟨fun _ => by omega, fun v hv => by simp_all⟩
  case p4 => exact ⟨fun _ => by omega, fun v hv => by simp_all⟩
  case dec =>
    obtain ⟨h1, -, ⟨r, h3, h4⟩, -⟩ := hI
    exact ⟨fun h0 => by simp_all, fun v hv => by simp_all⟩
  case out =>
    obtain ⟨h1, -, ⟨r, h3, h4⟩, -⟩ := hI
    exact ⟨fun h0 => by simp_all, fun v hv => by simp_all⟩

lemma I1_ret (hI : I1 P x l vl rt h) :
    (rt = none → h.count 1 ≤ 1) ∧ ∀ v, rt = some v → 1 ≤ h.count 1 := by
  cases l <;> simp only [I1] at hI
  case q0 => exact ⟨fun _ => by omega, fun v hv => by simp_all⟩
  case q1 => exact ⟨fun _ => by omega, fun v hv => by simp_all⟩
  case q2 => exact ⟨fun _ => by omega, fun v hv => by simp_all⟩
  case q3 => exact ⟨fun _ => by omega, fun v hv => by omega⟩
  case q4 => exact ⟨fun _ => by omega, fun v hv => by omega⟩
  case q5 => exact ⟨fun h0 => by simp_all, fun v hv => by omega⟩
  case dec => exact ⟨fun h0 => by simp_all, fun v hv => by omega⟩
  case out => exact ⟨fun h0 => by simp_all, fun v hv => by omega⟩

lemma I0_val (hI : I0 P x l vl rt h) (hc : 0 < h.count 0) : vl = some (x 0) := by
  cases l <;> simp only [I0] at hI
  all_goals first | exact hI.elim | omega | tauto

lemma I1_val (hI : I1 P x l vl rt h) (hc : 0 < h.count 1) : vl = some (x 1) := by
  cases l <;> simp only [I1] at hI
  all_goals first | exact hI.elim | omega | tauto

lemma I0_count (hI : I0 P x l vl rt h) : h.count 0 ≤ 2 := by
  cases l <;> simp only [I0] at hI
  all_goals first | exact hI.elim | omega

lemma I1_count (hI : I1 P x l vl rt h) : h.count 1 ≤ 2 := by
  cases l <;> simp only [I1] at hI
  all_goals first | exact hI.elim | omega

/-! ## Preservation of the invariant -/

lemma step_a (hG : Good P) (x : Fin 2 → Bool) (C : Cfg (alg P)) (hC : Inv P x C) :
    Inv P x (C.stepP P.a) := by
  have hab := hG.1
  have hba := Ne.symm hab
  obtain ⟨h, hO, h0, h1⟩ := hC
  generalize hl : C.loc P.a = l at h0
  cases l with
  | p0 v =>
    obtain ⟨hv, hc, hV, hr⟩ := h0
    have hact : (alg P).act (C.loc P.a) = .access (.inl (.val 0)) (RWOp.write (some v))
        fun _ => .p1 := by rw [hl]; rfl
    rw [stepP_of_access C hact]
    refine ⟨h, hO, ?_, ?_⟩
    · simpa [I0, valR, retR, hc, hV, hv] using hr
    · simpa [valR, retR, Function.update_of_ne hba] using h1
  | p1 =>
    obtain ⟨hc, hV, hv, hr⟩ := h0
    have hact : (alg P).act (C.loc P.a) = .access (.inr ()) P.f fun r => .p2 r := by
      rw [hl]; rfl
    rw [stepP_of_access C hact]
    have hV' := V_append_0a (P := P) h
    rw [hc, hV, ← hO] at hV'
    refine ⟨h ++ [0], ?_, ?_, ?_⟩
    · simp only [IL_append, after_append, ← hO]; simp [hc, objS]; rfl
    · simp only [I0, valR, retR, Function.update_self]
      exact ⟨by simp [hc], hV', hv, hr⟩
    · simpa [valR, retR, Function.update_of_ne hba] using I1_mono hab h1
  | p2 r =>
    obtain ⟨hc, hV, hv, hr⟩ := h0
    have hact : (alg P).act (C.loc P.a) = .access (.inl (.ret 0)) (RWOp.write (some r))
        fun _ => .p3 r := by rw [hl]; rfl
    rw [stepP_of_access C hact]
    refine ⟨h, hO, ?_, ?_⟩
    · simpa [I0, valR, retR, hc, hV] using hv
    · simpa [valR, retR, Function.update_of_ne hba] using h1
  | p3 r =>
    obtain ⟨hc, hV, hv, hr⟩ := h0
    have hact : (alg P).act (C.loc P.a) = .access (.inl (.ret 1)) RWOp.read
        fun y => .p4 r y := by rw [hl]; rfl
    rw [stepP_of_access C hact, upd_read_ret]
    have hRF : RF0 (retR C 1) h := by
      have := I1_ret h1
      cases hy : retR C 1 with
      | none => simp only [RF0]; exact Snap.now ⟨hc, this.1 hy⟩
      | some v => simp only [RF0]; exact Snap.now ⟨hc, this.2 v hy⟩
    refine ⟨h, hO, ?_, ?_⟩
    · simp only [I0, Function.update_self]
      exact ⟨hc, hV, hv, hr, hRF⟩
    · simpa [valR, retR, Function.update_of_ne hba] using h1
  | p4 r y =>
    obtain ⟨hc, hV, hv, hr, hRF⟩ := h0
    have hact : (alg P).act (C.loc P.a) = .access (.inr ()) P.f' fun r' =>
        .dec (dec0 P r y r') := by rw [hl]; rfl
    rw [stepP_of_access C hact]
    have hV' := V_append_0a (P := P) h
    rw [hc, hV, ← hO] at hV'
    simp only [one_ne_zero, ite_false] at hV'
    have hc1 := I1_count h1
    refine ⟨h ++ [0], ?_, ?_, ?_⟩
    · simp only [IL_append, after_append, ← hO]; simp [hc, objS]; rfl
    · simp only [I0, valR, retR, Function.update_self]
      refine ⟨by simp [hc], hv, ⟨r, hr, by simp [hV']⟩, ?_⟩
      refine core0 P hG _ (by simp [hc]) (by simpa [count_append_ne] using hc1) r _ hV' y ?_
      cases y <;> simp only [RF0] at hRF ⊢ <;> exact Snap.append hRF _
    · simpa [valR, retR, Function.update_of_ne hba] using I1_mono hab h1
  | dec j =>
    have h0' := h0
    obtain ⟨hc, hv, hr, hj⟩ := h0
    have hact : (alg P).act (C.loc P.a) = .access (.inl (.val j)) RWOp.read
        fun v => .out ((v : Option Bool).getD false) := by rw [hl]; rfl
    have hvj : valR C j = some (x (pr P j)) := by
      have hpos : 0 < h.count j := by
        cases h with
        | nil => simp at hj
        | cons y t => simp at hj; subst hj; simp
      fin_cases j
      · exact I0_val h0' hpos
      · exact I1_val h1 hpos
    rw [stepP_of_access C hact, upd_read_val]
    refine ⟨h, hO, ?_, ?_⟩
    · simp only [I0, Function.update_self]
      simp only [valR] at hvj
      exact ⟨hc, hv, hr, j, hj, by simp [hvj]⟩
    · simpa [valR, retR, Function.update_of_ne hba] using h1
  | out w =>
    rw [stepP_of_out C (show C.Out P.a w by simp [Cfg.Out, hl]; rfl)]
    exact ⟨h, hO, hl ▸ h0, h1⟩
  | _ => exact h0.elim

lemma step_b (hG : Good P) (x : Fin 2 → Bool) (C : Cfg (alg P)) (hC : Inv P x C) :
    Inv P x (C.stepP P.b) := by
  have hab := hG.1
  have hba := Ne.symm hab
  obtain ⟨h, hO, h0, h1⟩ := hC
  generalize hl : C.loc P.b = l at h1
  cases l with
  | q0 v =>
    obtain ⟨hv, hc, hV, hr⟩ := h1
    have hact : (alg P).act (C.loc P.b) = .access (.inl (.val 1)) (RWOp.write (some v))
        fun _ => .q1 := by rw [hl]; rfl
    rw [stepP_of_access C hact]
    refine ⟨h, hO, ?_, ?_⟩
    · simpa [valR, retR, Function.update_of_ne hab] using h0
    · simpa [I1, valR, retR, hc, hV, hv] using hr
  | q1 =>
    obtain ⟨hc, hV, hv, hr⟩ := h1
    have hact : (alg P).act (C.loc P.b) = .access (.inr ()) P.g fun r => .q2 r := by
      rw [hl]; rfl
    rw [stepP_of_access C hact]
    have hV' := V_append_1b (P := P) h
    rw [hc, hV, ← hO] at hV'
    refine ⟨h ++ [1], ?_, ?_, ?_⟩
    · simp only [IL_append, after_append, ← hO]; simp [hc, objS]; rfl
    · simpa [valR, retR, Function.update_of_ne hab] using I0_mono hab h0
    · simp only [I1, valR, retR, Function.update_self]
      exact ⟨by simp [hc], hV', hv, hr⟩
  | q2 r =>
    obtain ⟨hc, hV, hv, hr⟩ := h1
    have hact : (alg P).act (C.loc P.b) = .access (.inl (.ret 1)) (RWOp.write (some r))
        fun _ => .q3 r := by rw [hl]; rfl
    rw [stepP_of_access C hact]
    refine ⟨h, hO, ?_, ?_⟩
    · simpa [valR, retR, Function.update_of_ne hab] using h0
    · simpa [I1, valR, retR, hc, hV] using hv
  | q3 r =>
    obtain ⟨hc, hV, hv, hr⟩ := h1
    have hact : (alg P).act (C.loc P.b) = .access (.inl (.ret 0)) RWOp.read
        fun y => .q4 r y := by rw [hl]; rfl
    rw [stepP_of_access C hact, upd_read_ret]
    have hRF : RF1 P (retR C 0) h := by
      have := I0_ret h0
      cases hy : retR C 0 with
      | none => simp only [RF1]; exact Snap.now ⟨hc, this.1 hy⟩
      | some v =>
        simp only [RF1]; exact ⟨(this.2 v hy).1, Snap.now ⟨hc, (this.2 v hy).2⟩⟩
    refine ⟨h, hO, ?_, ?_⟩
    · simpa [valR, retR, Function.update_of_ne hab] using h0
    · simp only [I1, Function.update_self]
      exact ⟨hc, hV, hv, hr, hRF⟩
  | q4 r y =>
    obtain ⟨hc, hV, hv, hr, hRF⟩ := h1
    have hV' := V_append_1b (P := P) h
    rw [hc, hV, ← hO] at hV'
    simp only [one_ne_zero, ite_false] at hV'
    have hc0 := I0_count h0
    have hc1' : (h ++ [1]).count 1 = 2 := by simp [hc]
    have hc0' : (h ++ [1]).count 0 ≤ 2 := by simpa [count_append_ne] using hc0
    have hO' : objS (C.stepP P.b) = after O P.s (IL P (h ++ [1])) := by
      simp only [Cfg.stepP, hl]
      simp only [IL_append, after_append, ← hO]; simp [hc, objS]; rfl
    cases y with
    | some v =>
      have hact : (alg P).act (C.loc P.b) = .access (.inr ()) P.g' fun _ =>
          .dec (dec1a P v) := by rw [hl]; rfl
      rw [stepP_of_access C hact] at hO' ⊢
      refine ⟨h ++ [1], hO', ?_, ?_⟩
      · simpa [valR, retR, Function.update_of_ne hab] using I0_mono hab h0
      · simp only [I1, valR, retR, Function.update_self]
        refine ⟨hc1', hv, ⟨r, hr⟩, ?_⟩
        simp only [RF1] at hRF
        exact core1a P hG _ hc1' hc0' v (by rw [V_append_1a hab]; exact hRF.1)
          (Snap.append hRF.2 _)
    | none =>
      have hact : (alg P).act (C.loc P.b) = .access (.inr ()) P.g' fun r' => .q5 r r' := by
        rw [hl]; rfl
      rw [stepP_of_access C hact] at hO' ⊢
      refine ⟨h ++ [1], hO', ?_, ?_⟩
      · simpa [valR, retR, Function.update_of_ne hab] using I0_mono hab h0
      · simp only [I1, valR, retR, Function.update_self]
        simp only [RF1] at hRF
        exact ⟨hc1', hV', hv, hr, Snap.append hRF _⟩
  | q5 r r' =>
    obtain ⟨hc, hV, hv, hr, hS⟩ := h1
    have hact : (alg P).act (C.loc P.b) = .access (.inl (.ret 0)) RWOp.read
        fun z => .dec (dec1b P r r' z) := by rw [hl]; rfl
    rw [stepP_of_access C hact, upd_read_ret]
    have hRF : RF2 P (retR C 0) h := by
      have := I0_ret h0
      cases hy : retR C 0 with
      | none => simp only [RF2]; exact Snap.now ⟨hc, this.1 hy⟩
      | some v => simp only [RF2]; exact (this.2 v hy).1
    refine ⟨h, hO, ?_, ?_⟩
    · simpa [valR, retR, Function.update_of_ne hab] using h0
    · simp only [I1, Function.update_self]
      exact ⟨hc, hv, ⟨r, hr⟩, core1b P hG h hc (I0_count h0) r r' hV hS _ hRF⟩
  | dec j =>
    have h1' := h1
    obtain ⟨hc, hv, hr, hj⟩ := h1
    have hact : (alg P).act (C.loc P.b) = .access (.inl (.val j)) RWOp.read
        fun v => .out ((v : Option Bool).getD false) := by rw [hl]; rfl
    have hvj : valR C j = some (x (pr P j)) := by
      have hpos : 0 < h.count j := by
        cases h with
        | nil => simp at hj
        | cons y t => simp at hj; subst hj; simp
      fin_cases j
      · exact I0_val h0 hpos
      · exact I1_val h1' hpos
    rw [stepP_of_access C hact, upd_read_val]
    refine ⟨h, hO, ?_, ?_⟩
    · simpa [valR, retR, Function.update_of_ne hab] using h0
    · simp only [I1, Function.update_self]
      simp only [valR] at hvj
      exact ⟨hc, hv, hr, j, hj, by simp [hvj]⟩
  | out w =>
    rw [stepP_of_out C (show C.Out P.b w by simp [Cfg.Out, hl]; rfl)]
    exact ⟨h, hO, h0, hl ▸ h1⟩
  | _ => exact h1.elim

lemma fin2_cases {a b : Fin 2} (hab : a ≠ b) (p : Fin 2) : p = a ∨ p = b := by omega

lemma inv_step (hG : Good P) (x : Fin 2 → Bool) (C : Cfg (alg P)) (p : Fin 2)
    (hC : Inv P x C) : Inv P x (C.stepP p) := by
  rcases fin2_cases hG.1 p with rfl | rfl
  · exact step_a hG x C hC
  · exact step_b hG x C hC

lemma inv_init (hab : P.a ≠ P.b) (x : Fin 2 → Bool) : Inv P x (initCfg (alg P) x) := by
  refine ⟨[], rfl, ?_, ?_⟩
  · simp [initCfg, I0, pr, valR, retR, V, IL, il, ilAux, view]
  · simp [initCfg, I1, pr, valR, retR, V, IL, il, ilAux, view, Ne.symm hab]

lemma act_out {l : Loc O.Resp} {w : Bool} (h : act P l = .out w) : l = .out w := by
  rcases l with v | _ | r | r | ⟨r, x⟩ | v | _ | r | r | ⟨r, _ | v⟩ | ⟨r, r'⟩ | j | w' <;>
    simp [act] at h
  rw [h]

lemma inv_out (hab : P.a ≠ P.b) (x : Fin 2 → Bool) (C : Cfg (alg P)) (hC : Inv P x C) :
    ∃ q, ∀ p w, C.Out p w → w = x q := by
  obtain ⟨h, -, h0, h1⟩ := hC
  refine ⟨pr P (h.head?.getD 0), fun p w hw => ?_⟩
  have hl : C.loc p = .out w := act_out hw
  rcases fin2_cases hab p with hp | hp <;> subst hp
  · rw [hl] at h0
    obtain ⟨-, -, -, j, hj, rfl⟩ := h0
    simp [hj]
  · rw [hl] at h1
    obtain ⟨-, -, -, j, hj, rfl⟩ := h1
    simp [hj]

/-- Remaining steps (for wait-freedom). -/
def rank : Loc O.Resp → ℕ
  | .p0 _ => 6 | .p1 => 5 | .p2 _ => 4 | .p3 _ => 3 | .p4 _ _ => 2
  | .q0 _ => 7 | .q1 => 6 | .q2 _ => 5 | .q3 _ => 4 | .q4 _ _ => 3 | .q5 _ _ => 2
  | .dec _ => 1 | .out _ => 0

lemma rank_lt (l : Loc O.Resp) (i : Reg ⊕ Unit) (o : (Obj O i).Op)
    (κ : (Obj O i).Resp → Loc O.Resp) (r : (Obj O i).Resp) (hact : act P l = .access i o κ) :
    rank (κ r) < rank l := by
  rcases l with v | _ | r | r | ⟨r, x⟩ | v | _ | r | r | ⟨r, _ | v⟩ | ⟨r, r'⟩ | j | w <;>
    simp only [act] at hact <;> cases hact <;> simp [rank]

/-- Remaining accesses to `O` (for two-shotness). -/
def budget : Loc O.Resp → ℕ
  | .p0 _ => 2 | .p1 => 2 | .p2 _ => 1 | .p3 _ => 1 | .p4 _ _ => 1
  | .q0 _ => 2 | .q1 => 2 | .q2 _ => 1 | .q3 _ => 1 | .q4 _ _ => 1 | .q5 _ _ => 0
  | .dec _ => 0 | .out _ => 0

lemma budget_step (l : Loc O.Resp) (i : Reg ⊕ Unit) (o : (Obj O i).Op)
    (κ : (Obj O i).Resp → Loc O.Resp) (r : (Obj O i).Resp) (k : Unit)
    (hact : act P l = .access i o κ) :
    budget (κ r) + (if i = .inr k then 1 else 0) ≤ budget l := by
  rcases l with v | _ | r | r | ⟨r, x⟩ | v | _ | r | r | ⟨r, _ | v⟩ | ⟨r, r'⟩ | j | w <;>
    simp only [act] at hact <;> cases hact <;> simp [budget]

variable (P) in
/-- Which process may be in a local state (for the allowance map). -/
def owner (p : Fin 2) : Loc O.Resp → Prop
  | .p0 _ | .p1 | .p2 _ | .p3 _ | .p4 _ _ => p = P.a
  | .q0 _ | .q1 | .q2 _ | .q3 _ | .q4 _ _ | .q5 _ _ => p = P.b
  | .dec _ | .out _ => True

lemma owner_step (p : Fin 2) (l : Loc O.Resp) (i : Reg ⊕ Unit) (o : (Obj O i).Op)
    (κ : (Obj O i).Resp → Loc O.Resp) (r : (Obj O i).Resp) (hG : owner P p l)
    (hact : act P l = .access i o κ) : owner P p (κ r) := by
  rcases l with v | _ | r | r | ⟨r, x⟩ | v | _ | r | r | ⟨r, _ | v⟩ | ⟨r, r'⟩ | j | w <;>
    simp only [act] at hact <;> cases hact <;> simp_all [owner]

lemma owner_ok (m : Fin 2 → Set O.Op) (hf : P.f ∈ m P.a) (hf' : P.f' ∈ m P.a)
    (hg : P.g ∈ m P.b) (hg' : P.g' ∈ m P.b) (p : Fin 2) (l : Loc O.Resp) (k : Unit)
    (o : O.Op) (κ : O.Resp → Loc O.Resp) (hG : owner P p l)
    (hact : act P l = .access (.inr k) o κ) : o ∈ m p := by
  rcases l with v | _ | r | r | ⟨r, x⟩ | v | _ | r | r | ⟨r, _ | v⟩ | ⟨r, r'⟩ | j | w <;>
    simp only [act] at hact <;> cases hact <;> simp_all [owner]

end C15Alg

open C15Alg in
/-- **Section 5.2, Theorem 1**: objects satisfying the five properties of class `C₁.₅` (with
process `a` in the role of `p₀` and `b ≠ a` in the role of `p₁`) solve two-shot two-process
consensus, by Algorithms 1 and 2. -/
theorem solvable_of_C15Cond {O : ObjSpec} {m : Fin 2 → Set O.Op} {a b : Fin 2} (hab : a ≠ b)
    (hC : C15Cond O m a b) : Solvable O m := by
  classical
  obtain ⟨s, f, f', g, g', hf, hf', hg, hg', h1, h2, h3, h4, h5⟩ := hC
  let P : Par O := ⟨a, b, s, f, f', g, g'⟩
  have hG : Good P := ⟨hab, h1, h2, h3, h4, h5⟩
  refine ⟨Reg, Unit, inferInstance, inferInstance, inferInstance, RegT O.Resp, rwLike_RegT _,
    alg P, ?_, ?_, ?_⟩
  · exact wfConsensus_of_inv (Inv P) (inv_init hab) (inv_step hG) (inv_out hab) rank
      (fun l i o κ r hact => rank_lt l i o κ r hact)
  · refine twoShot_of_budget (fun l _ => budget l) (fun p v k => ?_)
      (fun l i o κ r k hact => budget_step l i o κ r k hact)
    simp only; split <;> simp [budget]
  · refine allowed_of_inv m (fun p l => owner P p l) (fun p v => ?_)
      (fun p l i o κ r hG hact => owner_step p l i o κ r hG hact)
      (fun p l k o κ hG hact => owner_ok m hf hf' hg hg' p l k o κ hG hact)
    simp only; split
    · rename_i hpa; exact hpa
    · rename_i hpa
      rcases fin2_cases hab p with h | h
      · exact absurd h hpa
      · exact h

end TwoShotCons
