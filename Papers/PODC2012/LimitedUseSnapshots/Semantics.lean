import Papers.PODC2012.LimitedUseSnapshots.Algorithm

/-!
# Step semantics of Algorithm 2

Explicit description of the steps of `alg P T true` (the corrected algorithm): every internal step
(`TStep`) and every response (`RStep`) of a process, with the successor configuration built from
the setters `setLoc`, `setSw`, `setSec`. Also: memory monotonicity along executions (switches only
go from `0` to `1`, max registers only grow).
-/

set_option linter.unusedSectionVars false

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- Configurations of Algorithm 2. -/
abbrev Cfg (P : Type) := Config maxArrObj baseObj P Loc

/-- The switch of node `a`. -/
def sw (C : Cfg P) (a : List Bool) : Bool := C.mem (.sw a)

/-- The `second` max register of node `a`. -/
def sc (C : Cfg P) (a : List Bool) : ℕ := C.mem (.sec a)

/-- Set the local state of `p`. -/
def setLoc (C : Cfg P) (p : P) (l : Loc) : Cfg P := { C with loc := Function.update C.loc p l }

/-- Set the switch of node `a`. -/
def setSw (C : Cfg P) (a : List Bool) (b : Bool) : Cfg P :=
  { C with mem := Function.update C.mem (.sw a) b }

/-- Set the `second` register of node `a`. -/
def setSec (C : Cfg P) (a : List Bool) (n : ℕ) : Cfg P :=
  { C with mem := Function.update C.mem (.sec a) n }

section Setters

variable (C : Cfg P)

@[simp] lemma setLoc_loc (p : P) (l : Loc) : (setLoc C p l).loc = Function.update C.loc p l := rfl
@[simp] lemma setLoc_pend (p : P) (l : Loc) : (setLoc C p l).pend = C.pend := rfl
@[simp] lemma sw_setLoc (p : P) (l : Loc) (a : List Bool) : sw (setLoc C p l) a = sw C a := rfl
@[simp] lemma sc_setLoc (p : P) (l : Loc) (a : List Bool) : sc (setLoc C p l) a = sc C a := rfl
@[simp] lemma sw_setLoc' (p : P) (l : Loc) : sw (setLoc C p l) = sw C := rfl
@[simp] lemma sc_setLoc' (p : P) (l : Loc) : sc (setLoc C p l) = sc C := rfl
@[simp] lemma sw_setSec' (a : List Bool) (n : ℕ) : sw (setSec C a n) = sw C := by
  funext a'; simp [sw, setSec]
@[simp] lemma setSw_loc (a : List Bool) (b : Bool) : (setSw C a b).loc = C.loc := rfl
@[simp] lemma setSw_pend (a : List Bool) (b : Bool) : (setSw C a b).pend = C.pend := rfl
@[simp] lemma setSec_loc (a : List Bool) (n : ℕ) : (setSec C a n).loc = C.loc := rfl
@[simp] lemma setSec_pend (a : List Bool) (n : ℕ) : (setSec C a n).pend = C.pend := rfl

@[simp] lemma sc_setSw (a a' : List Bool) (b : Bool) : sc (setSw C a b) a' = sc C a' := by
  simp [sc, setSw]

@[simp] lemma sw_setSec (a a' : List Bool) (n : ℕ) : sw (setSec C a n) a' = sw C a' := by
  simp [sw, setSec]

lemma sw_setSw (a a' : List Bool) (b : Bool) :
    sw (setSw C a b) a' = if a' = a then b else sw C a' := by
  split_ifs with h
  · subst h; simp [sw, setSw]
  · simp [sw, setSw, Function.update_of_ne (show Obj.sw a' ≠ Obj.sw a by simpa using h)]

lemma sc_setSec (a a' : List Bool) (n : ℕ) :
    sc (setSec C a n) a' = if a' = a then n else sc C a' := by
  split_ifs with h
  · subst h; simp [sc, setSec]
  · simp [sc, setSec, Function.update_of_ne (show Obj.sec a' ≠ Obj.sec a by simpa using h)]

end Setters

/-! ### `deepRight` -/

lemma deepRight_eq_none : ∀ {c : List Bool}, deepRight c = none → ∀ y ∈ c, y = false
  | [], _ => by simp
  | b :: c, h => by
    simp only [deepRight] at h
    split at h
    · cases h
    · rename_i ha
      split_ifs at h with hb
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · simpa using hb
      · exact deepRight_eq_none ha y hy

lemma deepRight_eq_some : ∀ {c a' : List Bool}, deepRight c = some a' →
    ∃ rest, c = a' ++ true :: rest ∧ ∀ y ∈ rest, y = false
  | [], _, h => by simp [deepRight] at h
  | b :: c, a', h => by
    simp only [deepRight] at h
    split at h
    · rename_i a ha
      obtain ⟨rest, rfl, hr⟩ := deepRight_eq_some ha
      cases h; exact ⟨rest, by simp, hr⟩
    · rename_i ha
      split_ifs at h with hb
      cases h; subst hb
      exact ⟨c, rfl, deepRight_eq_none ha⟩

/-- A list of `false`s has no right step. -/
lemma noTrue_of_forall {c : List Bool} (h : ∀ y ∈ c, y = false) (u x : List Bool) :
    c ≠ u ++ true :: x := by
  rintro rfl; simpa using h true (by simp)

/-- Right steps of an extension of `a' ++ true :: rest` (with `rest` all `false`) that are at or
below `a'` are `a'` itself or below `a' ++ true :: rest`. -/
lemma rightStep_cases {a' rest e u x : List Bool} (hrest : ∀ y ∈ rest, y = false)
    (hce : a' ++ true :: rest <+: e) (hu : e = u ++ true :: x) (hau : a' <+: u) :
    u = a' ∨ a' ++ true :: rest <+: u := by
  have hue : u <+: e := hu ▸ List.prefix_append u _
  by_cases hl : (a' ++ true :: rest).length ≤ u.length
  · exact Or.inr (List.prefix_of_prefix_length_le hce hue hl)
  · have huc : u <+: a' ++ true :: rest := List.prefix_of_prefix_length_le hue hce (by omega)
    obtain ⟨z, rfl⟩ := hau
    obtain ⟨w, hw⟩ := huc
    rw [List.append_assoc] at hw
    have hw' : true :: rest = z ++ w := (List.append_cancel_left hw).symm
    have hwe : a' ++ z ++ w <+: a' ++ z ++ true :: x := by rw [List.append_assoc, hw, ← hu]; exact hce
    have hwx : w <+: true :: x := (List.prefix_append_right_inj _).1 hwe
    rcases z with _ | ⟨t, z'⟩
    · left; simp
    · exfalso
      simp only [List.cons_append, List.cons.injEq] at hw'
      have hwne : w ≠ [] := by
        rintro rfl; simp [hw'.2] at hl
      obtain ⟨w0, w', rfl⟩ := List.exists_cons_of_ne_nil hwne
      have : w0 = true := by simpa using (List.cons_prefix_cons.1 hwx).1
      subst this
      simpa using hrest true (by rw [hw'.2]; simp)

/-! ### `MaxUpdate0` descent -/

lemma replicate_succ_true (n : ℕ) (a : List Bool) :
    a ++ List.replicate (n + 1) true = (a ++ [true]) ++ List.replicate n true := by
  simp [List.replicate_succ]

/-- The descent of `MaxUpdate0(v)` from node `a`: it skips right steps and stops at the first
left step (reading its switch) or at a leaf (starting the ascent). -/
lemma d0Act_cases (T : Shape) (v : ℕ) : ∀ (t : Shape) (a : List Bool), T.subD a = t →
    ∃ n, (v < T.size → a <+: T.addr v → a ++ List.replicate n true <+: T.addr v) ∧
    ((T.subD (a ++ List.replicate n true) = .leaf ∧
        d0Act v (v - T.lo a) t a = upAct v (a ++ List.replicate n true)) ∨
     (∃ l r, T.subD (a ++ List.replicate n true) = .node l r ∧
        v - T.lo (a ++ List.replicate n true) < l.size ∧
        d0Act v (v - T.lo a) t a = .access (.sw (a ++ List.replicate n true)) .read
          (fun b => if b then .up v (a ++ List.replicate n true)
            else .d0 v (a ++ List.replicate n true ++ [false]))))
  | .leaf, a, h => ⟨0, fun _ h => by simpa using h, Or.inl ⟨by simpa using h, by simp [d0Act]⟩⟩
  | .node l r, a, h => by
    by_cases hw : v - T.lo a < l.size
    · refine ⟨0, fun _ h => by simpa using h, Or.inr ⟨l, r, by simpa using h, by simpa using hw,
        ?_⟩⟩
      simp [d0Act, hw]
    · obtain ⟨n, hpre, hcases⟩ := d0Act_cases T v r (a ++ [true]) (Shape.subD_append_true h)
      have hlo : v - T.lo (a ++ [true]) = v - T.lo a - l.size := by
        rw [Shape.lo_append_true h]; omega
      refine ⟨n + 1, fun hv ha => ?_, ?_⟩
      · rw [replicate_succ_true]
        exact hpre hv ((Shape.prefix_addr_child hv ha h).2 hw)
      · rw [replicate_succ_true]
        have hd : d0Act v (v - T.lo a) (.node l r) a =
            d0Act v (v - T.lo (a ++ [true])) r (a ++ [true]) := by
          simp only [d0Act, hw, ↓reduceIte, hlo]
        rw [hd]; exact hcases

/-! ### Steps of the corrected algorithm -/

variable (T : Shape)

/-- The internal steps of process `p` in Algorithm 2 (corrected), with their effect. -/
inductive TStep (C : Cfg P) (p : P) : Cfg P → Prop
  /-- `MaxUpdate0`: read the switch at a left step `c` (line 3). -/
  | d0rd (v : ℕ) (a : List Bool) (n : ℕ) (l r : Shape) :
      C.loc p = .d0 v a → T.subD (a ++ List.replicate n true) = .node l r →
      v - T.lo (a ++ List.replicate n true) < l.size →
      (v < T.size → a <+: T.addr v → a ++ List.replicate n true <+: T.addr v) →
      TStep C p (setLoc C p (if sw C (a ++ List.replicate n true) then
        .up v (a ++ List.replicate n true) else .d0 v (a ++ List.replicate n true ++ [false])))
  /-- `MaxUpdate0`: reached a leaf, set the deepest switch on the way up (line 7). -/
  | d0wr (v : ℕ) (a : List Bool) (n : ℕ) (a' : List Bool) :
      C.loc p = .d0 v a → T.subD (a ++ List.replicate n true) = .leaf →
      deepRight (a ++ List.replicate n true) = some a' →
      (v < T.size → a <+: T.addr v → a ++ List.replicate n true <+: T.addr v) →
      TStep C p (setLoc (setSw C a' true) p (.up v a'))
  /-- `MaxUpdate0`: set the next switch on the way up (line 7). -/
  | upwr (v : ℕ) (a a' : List Bool) :
      C.loc p = .up v a → deepRight a = some a' →
      TStep C p (setLoc (setSw C a' true) p (.up v a'))
  /-- `MaxUpdate1`: `WriteMax(r.second, v)` (line 9), then the embedded scan (line 9.5). -/
  | w1 (v : ℕ) : C.loc p = .w1 v →
      TStep C p (setLoc (setSec C [] (max (sc C []) v)) p (.s1 true []))
  /-- `MaxScan` at a leaf: the final `ReadMax`. -/
  | s1leaf (e : Bool) (a : List Bool) : C.loc p = .s1 e a → T.subD a = .leaf →
      TStep C p (setLoc C p (.rt (if e then (0, 0) else (T.lo a, sc C a))))
  /-- `MaxScan`, line 11. -/
  | s1node (e : Bool) (a : List Bool) (l r : Shape) : C.loc p = .s1 e a → T.subD a = .node l r →
      TStep C p (setLoc C p (.s2 e a (sc C a)))
  /-- `MaxScan`, line 12. -/
  | s2 (e : Bool) (a : List Bool) (x : ℕ) : C.loc p = .s2 e a x →
      TStep C p (setLoc C p (if sw C a then .s4 e a else .s3 e a x))
  /-- `MaxScan`, line 13. -/
  | s3 (e : Bool) (a : List Bool) (x : ℕ) : C.loc p = .s3 e a x →
      TStep C p (setLoc (setSec C (a ++ [false]) (max (sc C (a ++ [false])) x)) p
        (.s1 e (a ++ [false])))
  /-- `MaxScan`, line 16. -/
  | s4 (e : Bool) (a : List Bool) : C.loc p = .s4 e a →
      TStep C p (setLoc C p (.s5 e a (sc C a)))
  /-- `MaxScan`, line 17. -/
  | s5 (e : Bool) (a : List Bool) (x : ℕ) : C.loc p = .s5 e a x →
      TStep C p (setLoc (setSec C (a ++ [true]) (max (sc C (a ++ [true])) x)) p
        (.s1 e (a ++ [true])))

/-- Responses of process `p`. -/
inductive RStep (C : Cfg P) (p : P) : ℕ × ℕ → Prop
  | d0 (v : ℕ) (a : List Bool) (n : ℕ) : C.loc p = .d0 v a →
      T.subD (a ++ List.replicate n true) = .leaf → deepRight (a ++ List.replicate n true) = none →
      (v < T.size → a <+: T.addr v → a ++ List.replicate n true <+: T.addr v) →
      RStep C p (0, 0)
  | up (v : ℕ) (a : List Bool) : C.loc p = .up v a → deepRight a = none → RStep C p (0, 0)
  | rt (r : ℕ × ℕ) : C.loc p = .rt r → RStep C p r
  | idle : C.loc p = .idle → RStep C p (0, 0)

lemma step_tau_cases {C C' : Cfg P} {p : P} (h : (alg P T true).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ TStep T C p C' := by
  obtain ⟨hpend, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  have hC' : C' = ⟨Function.update C.loc p (k ((baseObj i).δ (C.mem i) o).2), C.pend,
      Function.update C.mem i ((baseObj i).δ (C.mem i) o).1⟩ := by
    have := Impl.step_tau_eq_some hpend hact
    rw [h] at this; exact Option.some.inj this
  refine ⟨hpend, ?_⟩
  subst hC'
  change act T true (C.loc p) = _ at hact
  cases hl : C.loc p with
  | idle => rw [hl] at hact; simp [act] at hact
  | rt r => rw [hl] at hact; simp [act] at hact
  | w1 v =>
    rw [hl] at hact; simp only [act, Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    subst ho; subst hk
    convert TStep.w1 v hl using 1; simp [setLoc, setSec, sc]
  | s1 e a =>
    rw [hl] at hact
    cases hs : T.subD a with
    | leaf =>
      simp only [act, hs, Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      subst ho; subst hk
      convert TStep.s1leaf e a hl hs using 1; simp [setLoc, sc]
    | node l r =>
      simp only [act, hs, Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      subst ho; subst hk
      convert TStep.s1node e a l r hl hs using 1; simp [setLoc, sc]
  | s2 e a x =>
    rw [hl] at hact; simp only [act, Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    subst ho; subst hk
    convert TStep.s2 e a x hl using 1; simp [setLoc, sw]; congr
  | s3 e a x =>
    rw [hl] at hact; simp only [act, Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    subst ho; subst hk
    convert TStep.s3 e a x hl using 1; simp [setLoc, setSec, sc]
  | s4 e a =>
    rw [hl] at hact; simp only [act, Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    subst ho; subst hk
    convert TStep.s4 e a hl using 1; simp [setLoc, sc]
  | s5 e a x =>
    rw [hl] at hact; simp only [act, Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    subst ho; subst hk
    convert TStep.s5 e a x hl using 1; simp [setLoc, setSec, sc]
  | d0 v a =>
    rw [hl] at hact; simp only [act] at hact
    obtain ⟨n, hpre, hc⟩ := d0Act_cases T v (T.subD a) a rfl
    rcases hc with ⟨hleaf, hd⟩ | ⟨l, r, hnode, hlt, hd⟩
    · rw [hd] at hact
      simp only [upAct] at hact
      cases hdr : deepRight (a ++ List.replicate n true) with
      | none => rw [hdr] at hact; simp at hact
      | some a' =>
        rw [hdr] at hact; simp only [Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        subst ho; subst hk
        convert TStep.d0wr v a n a' hl hleaf hdr hpre using 1; simp [setLoc, setSw]
    · rw [hd] at hact; simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      subst ho; subst hk
      convert TStep.d0rd v a n l r hl hnode hlt hpre using 1; simp [setLoc, sw]
  | up v a =>
    rw [hl] at hact; simp only [act, upAct] at hact
    cases hdr : deepRight a with
    | none => rw [hdr] at hact; simp at hact
    | some a' =>
      rw [hdr] at hact; simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      subst ho; subst hk
      convert TStep.upwr v a a' hl hdr using 1; simp [setLoc, setSw]

lemma step_ret_cases {C C' : Cfg P} {p : P} {r : ℕ × ℕ}
    (h : (alg P T true).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ RStep T C p r ∧
      C' = ⟨Function.update C.loc p .idle, Function.update C.pend p none, C.mem⟩ := by
  obtain ⟨hpend, hpend', hmem, l, hact, hloc⟩ := Impl.step_ret h
  change act T true (C.loc p) = _ at hact
  have hC' : C' = ⟨Function.update C.loc p l, Function.update C.pend p none, C.mem⟩ := by
    cases C'; simp_all
  refine ⟨hpend, ?_⟩
  cases hl : C.loc p with
  | idle => rw [hl] at hact; simp only [act, Action.ret.injEq] at hact
            obtain ⟨rfl, rfl⟩ := hact; exact ⟨RStep.idle hl, hC'⟩
  | rt r' => rw [hl] at hact; simp only [act, Action.ret.injEq] at hact
             obtain ⟨rfl, rfl⟩ := hact; exact ⟨RStep.rt _ hl, hC'⟩
  | w1 v => rw [hl] at hact; simp [act] at hact
  | s1 e a => rw [hl] at hact; simp only [act] at hact; split at hact <;> simp at hact
  | s2 e a x => rw [hl] at hact; simp [act] at hact
  | s3 e a x => rw [hl] at hact; simp [act] at hact
  | s4 e a => rw [hl] at hact; simp [act] at hact
  | s5 e a x => rw [hl] at hact; simp [act] at hact
  | d0 v a =>
    rw [hl] at hact; simp only [act] at hact
    obtain ⟨n, hpre, hc⟩ := d0Act_cases T v (T.subD a) a rfl
    rcases hc with ⟨hleaf, hd⟩ | ⟨l', r', hnode, hlt, hd⟩
    · rw [hd] at hact
      simp only [upAct] at hact
      cases hdr : deepRight (a ++ List.replicate n true) with
      | none =>
        rw [hdr] at hact; simp only [Action.ret.injEq] at hact
        obtain ⟨rfl, rfl⟩ := hact; exact ⟨RStep.d0 v a n hl hleaf hdr hpre, hC'⟩
      | some a' => rw [hdr] at hact; simp at hact
    · rw [hd] at hact; simp at hact
  | up v a =>
    rw [hl] at hact; simp only [act, upAct] at hact
    cases hdr : deepRight a with
    | none =>
      rw [hdr] at hact; simp only [Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact; exact ⟨RStep.up v a hl hdr, hC'⟩
    | some a' => rw [hdr] at hact; simp at hact

lemma step_inv_cases {C C' : Cfg P} {p : P} {o : MAOp}
    (h : (alg P T true).step C (.inv p o) = some C') :
    C.pend p = none ∧ (alg P T true).allowed p o ∧
      C' = ⟨Function.update C.loc p (invokeLoc o), Function.update C.pend p (some o), C.mem⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Impl.step_inv h
  refine ⟨h1, h2, ?_⟩
  cases C'; simp_all; rfl

/-! ### Monotonicity of the memory -/

/-- The memory of `C'` dominates that of `C`: switches only turn on, max registers only grow. -/
def MemLE (C C' : Cfg P) : Prop := (∀ a, sw C a = true → sw C' a = true) ∧ ∀ a, sc C a ≤ sc C' a

lemma MemLE.refl (C : Cfg P) : MemLE C C := ⟨fun _ h => h, fun _ => le_rfl⟩

lemma MemLE.trans {C₁ C₂ C₃ : Cfg P} (h₁ : MemLE C₁ C₂) (h₂ : MemLE C₂ C₃) : MemLE C₁ C₃ :=
  ⟨fun a h => h₂.1 a (h₁.1 a h), fun a => (h₁.2 a).trans (h₂.2 a)⟩

lemma TStep.memLE {C C' : Cfg P} {p : P} (h : TStep T C p C') : MemLE C C' := by
  cases h with
  | d0wr | upwr =>
    refine ⟨fun a ha => ?_, fun a => by simp⟩
    simp only [sw_setLoc, sw_setSw]; split_ifs <;> simp [ha]
  | w1 | s3 | s5 =>
    refine ⟨fun a ha => by simpa using ha, fun a => ?_⟩
    simp only [sc_setLoc, sc_setSec]; split_ifs with h
    · subst h; exact le_max_left _ _
    · exact le_rfl
  | _ => exact ⟨fun a ha => by simpa using ha, fun a => by simp⟩

lemma step_memLE {C C' : Cfg P} {ℓ : Label P maxArrObj}
    (h : (alg P T true).step C ℓ = some C') : MemLE C C' := by
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, rfl⟩ := step_inv_cases T h; exact ⟨fun a ha => ha, fun a => le_rfl⟩
  | ret p r =>
    obtain ⟨-, -, rfl⟩ := step_ret_cases T h; exact ⟨fun a ha => ha, fun a => le_rfl⟩
  | tau p => exact (step_tau_cases T h).2.memLE T

lemma runFrom_memLE {C C' : Cfg P} {γ : List (Label P maxArrObj)}
    (h : (alg P T true).runFrom C γ = some C') : MemLE C C' := by
  induction γ generalizing C with
  | nil => simp at h; subst h; exact MemLE.refl _
  | cons ℓ γ ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg P T true).step C ℓ with
    | none => simp [hs] at h
    | some C₁ => simp only [hs, Option.bind_some] at h; exact (step_memLE T hs).trans (ih h)

/-- Memory monotonicity along an execution. -/
lemma run_memLE {β α : List (Label P maxArrObj)} {D C : Cfg P} (hβ : (alg P T true).run β = some D)
    (hα : (alg P T true).run α = some C) (hp : β <+: α) : MemLE D C := by
  obtain ⟨γ, rfl⟩ := hp
  rw [Impl.run_append_of_eq _ hβ] at hα
  exact runFrom_memLE T hα

end Podc.LimitedUseSnapshots
