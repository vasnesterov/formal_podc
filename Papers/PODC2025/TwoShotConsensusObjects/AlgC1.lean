import Papers.PODC2025.TwoShotConsensusObjects.AlgC1Common

/-!
# Class `C₁` solves two-shot two-process consensus (Section 5.1)

The classical algorithm: process `p` writes its input to `Val[p]`, applies its operation
(`f` for `p₀`, `g` for `p₁`) once to `O` (initially in state `s`); if the response is its solo
response from `s`, its operation was applied first and it decides `Val[p]`, otherwise it
decides `Val[1 - p]`. (Here a process decides its own input by reading it back from `Val[p]`.)
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable C1Common

namespace C1Alg

/-- Local states of the `C₁` algorithm. -/
inductive Loc
  /-- write the input `v` to `Val[p]` -/
  | wr (p : Fin 2) (v : Bool)
  /-- apply the operation of `p` to `O` -/
  | op (p : Fin 2)
  /-- read `Val[j]` and decide its content -/
  | dec (j : Fin 2)
  /-- output `w` -/
  | out (w : Bool)

variable {O : ObjSpec} (s : O.State) (f g : O.Op)

/-- The operation of process `p`. -/
def opOf (p : Fin 2) : O.Op := if p = 0 then f else g

open Classical in
/-- The code. -/
noncomputable def act : Loc → Act (Obj O) Loc
  | .wr p v => .access (.inl (.val p)) (RWOp.write (some v)) fun _ => .op p
  | .op p => .access (.inr ()) (opOf f g p) fun r =>
      .dec (if r = (O.δ s (opOf f g p)).2 then p else 1 - p)
  | .dec j => .access (.inl (.val j)) RWOp.read fun v => .out ((v : Option Bool).getD false)
  | .out w => .out w

/-- The algorithm. -/
noncomputable abbrev alg : Alg 2 (Obj O) where
  L := Loc
  init p v := .wr p v
  act := act s f g
  mem₀ := fun
    | .inl (.val _) => (none : Option Bool)
    | .inl (.ret _) => (none : Option O.Resp)
    | .inr () => s

variable {s f g}

/-- Content of `Val[i]`. -/
def valR (C : Cfg (alg s f g)) (i : Fin 2) : Option Bool := C.mem (.inl (.val i))

/-- State of `O`. -/
def objS (C : Cfg (alg s f g)) : O.State := C.mem (.inr ())

/-- Per-process invariant (`h`: the processes whose operation was applied to `O`, in order). -/
def I (x : Fin 2 → Bool) (p : Fin 2) : Loc → Option Bool → List (Fin 2) → Prop
  | .wr q v, _, h => q = p ∧ v = x p ∧ h.count p = 0
  | .op q, val, h => q = p ∧ h.count p = 0 ∧ val = some (x p)
  | .dec j, val, h => h.count p = 1 ∧ val = some (x p) ∧ h.head? = some j
  | .out w, val, h => h.count p = 1 ∧ val = some (x p) ∧ ∃ j, h.head? = some j ∧ w = x j

variable (s f g) in
/-- The invariant of reachable configurations. -/
def Inv (x : Fin 2 → Bool) (C : Cfg (alg s f g)) : Prop :=
  ∃ h : List (Fin 2), objS C = after O s (il O 0 1 f f g g h) ∧
    ∀ p, I x p (C.loc p) (valR C p) h

lemma I_mono {x : Fin 2 → Bool} {p q : Fin 2} (hpq : p ≠ q) {l : Loc} {v : Option Bool}
    {h : List (Fin 2)} (hI : I x q l v h) : I x q l v (h ++ [p]) := by
  have hc : (h ++ [p]).count q = h.count q := by simp [List.count_append, hpq]
  cases l with
  | wr r w => simpa [I, hc] using hI
  | op r => simpa [I, hc] using hI
  | dec j =>
    obtain ⟨h1, h2, h3⟩ := hI
    refine ⟨hc ▸ h1, h2, ?_⟩
    cases h with
    | nil => simp at h3
    | cons y t => simpa using h3
  | out w =>
    obtain ⟨h1, h2, j, h3, h4⟩ := hI
    refine ⟨hc ▸ h1, h2, j, ?_, h4⟩
    cases h with
    | nil => simp at h3
    | cons y t => simpa using h3

lemma I_val {x : Fin 2 → Bool} {p : Fin 2} {l : Loc} {v : Option Bool} {h : List (Fin 2)}
    (hI : I x p l v h) (hc : 0 < h.count p) : v = some (x p) := by
  cases l with
  | wr r w => simp [I] at hI; omega
  | op r => exact hI.2.2
  | dec j => exact hI.2.1
  | out w => exact hI.2.1

open Classical in
lemma I_count {x : Fin 2 → Bool} {p : Fin 2} {l : Loc} {v : Option Bool} {h : List (Fin 2)}
    (hI : I x p l v h) : h.count p ≤ 1 := by
  cases l with
  | wr r w => simp [I] at hI; omega
  | op r => simp [I] at hI; omega
  | dec j => exact hI.1.le
  | out w => exact hI.1.le

open Classical in
/-- The decision rule is correct: the response of `p`'s operation is its solo response iff
it is applied first. -/
lemma core (hd : DistBoth O s [(0, f), (1, g)] [(1, g), (0, f)]) (q : Fin 2) (h : List (Fin 2))
    (hc : h.count q = 0) (hc' : h.count (1 - q) ≤ 1) :
    (h ++ [q]).head? = some (if (O.δ (after O s (il O 0 1 f f g g h)) (opOf f g q)).2 =
      (O.δ s (opOf f g q)).2 then q else 1 - q) := by
  obtain ⟨hd0, hd1⟩ := hd
  simp only [Dist, view, resps, List.filterMap] at hd0 hd1
  have hd0' := Ne.symm hd0
  have hmem := hist_cases (h := h) (by fin_cases q <;> simp_all; omega)
    (by fin_cases q <;> simp_all; omega)
  fin_cases q <;>
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hc hc' <;> simp_all [il, ilAux, opOf]

open Classical in
lemma inv_step (hd : DistBoth O s [(0, f), (1, g)] [(1, g), (0, f)])
    (x : Fin 2 → Bool) (C : Cfg (alg s f g)) (p : Fin 2) (hC : Inv s f g x C) :
    Inv s f g x (C.stepP p) := by
  obtain ⟨h, hO, hI⟩ := hC
  have hIp := hI p
  generalize hl : C.loc p = l at hIp
  cases l with
  | wr q v =>
    obtain ⟨rfl, rfl, hc⟩ := hIp
    have hact : (alg s f g).act (C.loc q) = .access (.inl (.val q)) (RWOp.write (some (x q)))
        (fun _ => .op q) := by rw [hl]; rfl
    rw [stepP_of_access C hact]
    refine ⟨h, hO, fun r => ?_⟩
    by_cases hr : r = q
    · subst hr; simp [I, valR, hc]
    · have := hI r
      simpa [valR, hr, Function.update_of_ne hr] using this
  | op q =>
    obtain ⟨rfl, hc, hv⟩ := hIp
    have hact : (alg s f g).act (C.loc q) = .access (.inr ()) (opOf f g q) fun r =>
        .dec (if r = (O.δ s (opOf f g q)).2 then q else 1 - q) := by rw [hl]; rfl
    rw [stepP_of_access C hact]
    have hq' : (1 - q) ≠ q := by fin_cases q <;> decide
    refine ⟨h ++ [q], ?_, fun r => ?_⟩
    · simp only [il_append, after_append, ← hO]
      fin_cases q <;> simp [opOf] <;> rfl
    · by_cases hr : r = q
      · subst hr
        simp only [valR, Function.update_self, I]
        refine ⟨by simp [hc], hv, ?_⟩
        have := core hd r h hc (I_count (hI (1 - r)))
        rw [← hO] at this
        exact this
      · have := I_mono (Ne.symm hr) (hI r)
        simpa [valR, hr, Function.update_of_ne hr] using this
  | dec j =>
    obtain ⟨hc, hv, hj⟩ := hIp
    have hact : (alg s f g).act (C.loc p) = .access (.inl (.val j)) RWOp.read
        fun v => .out ((v : Option Bool).getD false) := by rw [hl]; rfl
    have hvj : valR C j = some (x j) := by
      apply I_val (hI j)
      cases h with
      | nil => simp at hj
      | cons y t => simp at hj; subst hj; simp
    rw [stepP_of_access C hact, upd_read_val]
    refine ⟨h, hO, fun r => ?_⟩
    by_cases hr : r = p
    · subst hr
      simp only [valR, Function.update_self, I] at hvj hv ⊢
      exact ⟨hc, hv, j, hj, by simp [hvj]⟩
    · have := hI r
      simpa [valR, hr, Function.update_of_ne hr] using this
  | out w =>
    rw [stepP_of_out C (show C.Out p w by simp [Cfg.Out, hl]; rfl)]
    exact ⟨h, hO, hI⟩

lemma inv_init (x : Fin 2 → Bool) : Inv s f g x (initCfg (alg s f g) x) :=
  ⟨[], rfl, fun p => ⟨rfl, rfl, by simp⟩⟩

lemma inv_out (x : Fin 2 → Bool) (C : Cfg (alg s f g)) (hC : Inv s f g x C) :
    ∃ q, ∀ p w, C.Out p w → w = x q := by
  obtain ⟨h, -, hI⟩ := hC
  refine ⟨h.head?.getD 0, fun p w hw => ?_⟩
  have hIp := hI p
  simp only [Cfg.Out] at hw
  generalize C.loc p = l at hIp hw
  cases l with
  | out w' =>
    simp only [act, Act.out.injEq] at hw
    subst hw
    obtain ⟨-, -, j, hj, rfl⟩ := hIp
    simp [hj]
  | _ => simp [act] at hw

/-- Remaining steps. -/
def rank : Loc → ℕ
  | .wr _ _ => 3
  | .op _ => 2
  | .dec _ => 1
  | .out _ => 0

lemma rank_lt (l : Loc) (i : Reg ⊕ Unit) (o : (Obj O i).Op) (κ : (Obj O i).Resp → Loc)
    (r : (Obj O i).Resp) (hact : act s f g l = .access i o κ) : rank (κ r) < rank l := by
  cases l <;> simp only [act] at hact <;> cases hact <;> simp [rank]

end C1Alg

open C1Alg in
/-- **Section 5.1** (known result): objects of class `C₁` solve two-shot two-process
consensus. -/
theorem solvable_of_C1 {O : ObjSpec} {m : Fin 2 → Set O.Op} (hC : C1 O m) : Solvable O m := by
  classical
  obtain ⟨s, f, g, hf, hg, hd⟩ := hC
  refine ⟨Reg, Unit, inferInstance, inferInstance, inferInstance, RegT O.Resp, rwLike_RegT _,
    alg s f g, ?_, ?_, ?_⟩
  · exact wfConsensus_of_inv (Inv s f g) inv_init (fun x C p hC => inv_step hd x C p hC) inv_out
      rank (fun l i o κ r hact => rank_lt l i o κ r hact)
  · refine twoShot_of_budget (fun l _ => match l with | .wr _ _ => 1 | .op _ => 1 | _ => 0)
      (fun p b k => by simp) ?_
    intro l i o κ r k hact
    cases l <;> simp only [alg, act] at hact <;> cases hact <;> simp
  · refine allowed_of_inv m (fun p l => match l with | .wr q _ => q = p | .op q => q = p | _ => True)
      (fun p b => rfl) ?_ ?_
    · intro p l i o κ r hG hact
      cases l <;> simp only [alg, act] at hact <;> cases hact <;> simp_all
    · intro p l k o κ hG hact
      cases l <;> simp only [alg, act] at hact <;> cases hact
      rename_i q
      subst hG
      fin_cases q <;> simp [C1Alg.opOf, hf, hg]

end TwoShotCons
