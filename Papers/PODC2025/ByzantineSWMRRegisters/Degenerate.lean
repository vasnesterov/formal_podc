import Papers.PODC2025.ByzantineSWMRRegisters.Objects
import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# A degenerate case of Theorem 31: authenticated registers over a one-element domain

Theorem 31 of Hu–Toueg is stated for SWMR authenticated registers without restriction on the
value domain `V`. If `V` has a single element (`V = Unit`, `v₀ = ()`), the authenticated register
is trivial: every `Read` returns `()`, every `Verify(())` returns `true` (`v₀` counts as written)
and `Write` has no observable effect. It is implemented without any shared object, by processes
that answer immediately, and this implementation is correct against any number of Byzantine
processes (`authenticated_unit_byzCorrect`), in particular for `3 ≤ n ≤ 3f`. Hence the hypothesis
`v ≠ v₀` of `theorem31_authenticated` (some value different from the initial one) is needed.
-/

namespace Podc.ByzantineSWMRRegisters

open Cslib.SharedMemory Cslib.SharedMemory.Byzantine

noncomputable section

variable {P : Type} [DecidableEq P]

-- Base objects indexed by `Empty`: there are none.
variable {B : Empty → ObjSpec} {acc : Access P B}

/-- The response of an operation of the authenticated register over `Unit`. -/
def unitResp : AuthOp Unit → RegResp Unit
  | .read => .val ()
  | .write _ => .done
  | .verify _ => .bool true

/-- The trivial implementation: the local state holds the response to return. -/
def unitAuthImpl (B : Empty → ObjSpec) (w : P) :
    Impl (authReg Unit ()) B P (Option (RegResp Unit)) where
  memInit i := i.elim
  locInit _ := none
  invoke _ _ o := some (unitResp o)
  act _ l := match l with
    | none => .ret .done none
    | some r => .ret r none
  allowed := authAllowed w

lemma unit_written (os : List (AuthOp Unit)) :
    () ∈ ((authReg Unit ()).runOps (authReg Unit ()).init os).written := by
  suffices ∀ q : (authReg Unit ()).State, () ∈ q.written →
      () ∈ ((authReg Unit ()).runOps q os).written from this _ (by simp)
  induction os with
  | nil => intro q hq; exact hq
  | cons o os ih =>
    intro q hq
    rw [ObjSpec.runOps_cons]
    apply ih
    cases o <;> simp [hq]

lemma unit_resp (q : (authReg Unit ()).State) (hq : () ∈ q.written) (o : AuthOp Unit) :
    ((authReg Unit ()).δ q o).2 = unitResp o := by
  cases o <;> simp [unitResp, hq]

variable (w : P)

/-- The invariant of the trivial implementation. -/
structure UnitInv (Bz : Finset P) (C : Config (authReg Unit ()) B P (Option (RegResp Unit)))
    (h : List (Label P (authReg Unit ()))) (L : List (OpId P × (authReg Unit ()).Op)) : Prop where
  lin : IsLinearization h L
  allow : ∀ p o, Label.inv p o ∈ h → authAllowed w p o
  done : ∀ y ∈ L.map Prod.fst, Completed h y
  pend : ∀ p ∉ Bz, (C.pend p = none ∧ C.loc p = none ∧
      (opsOf h p).length = (respsOf h p).length) ∨
    ∃ o, C.pend p = some o ∧ C.loc p = some (unitResp o) ∧
      opOf h (p, (respsOf h p).length) = some o ∧
      (opsOf h p).length = (respsOf h p).length + 1

theorem unitInv_exec {Bz : Finset P} :
    ∀ (α : List (Event P (authReg Unit ()) B)) C,
      (unitAuthImpl B w).brun acc α = some C → (∀ e ∈ α, e.Respects Bz) →
      ∃ L, UnitInv w Bz C (hist α) L := by
  intro α
  induction α using List.reverseRecOn with
  | nil =>
    intro C hC _
    simp only [Impl.brun, Impl.brunFrom_nil, Option.some.injEq] at hC; subst hC
    refine ⟨[], ⟨⟨by simp, by simp, fun a ha => by simp [Completed] at ha,
      fun a b _ hb => by simp at hb, trivial⟩, by simp, by simp, fun p _ => ?_⟩⟩
    left; simp [Impl.initCfg, unitAuthImpl]
  | append_singleton α e ih =>
    intro C hC hresp
    obtain ⟨D, hD, he⟩ := (unitAuthImpl B w).brunFrom_append_eq_some _ hC
    rw [Impl.brunFrom_singleton] at he
    obtain ⟨L, hI⟩ := ih D hD (fun e' he' => hresp e' (by simp [he']))
    have hre := hresp e (by simp)
    cases e with
    | byz p i o => exact i.elim
    | tau p =>
      have hh : hist (α ++ [.tau p]) = hist α := by simp [hist]
      rw [hh]
      simp only [Impl.bstep] at he
      split at he
      · rename_i i _ _ _; exact i.elim
      · split_ifs at he; cases he; exact ⟨L, hI⟩
    | inv p o =>
      have hp : p ∉ Bz := hre
      have hh : hist (α ++ [.inv p o]) = hist α ++ [.inv p o] := by simp [hist]
      rw [hh]
      simp only [Impl.bstep] at he
      split_ifs at he with hen
      cases he
      obtain ⟨hpend, hall⟩ := hen
      have hcnt : (opsOf (hist α) p).length = (respsOf (hist α) p).length := by
        rcases hI.pend p hp with ⟨-, -, h⟩ | ⟨o', h, -⟩
        · exact h
        · rw [hpend] at h; cases h
      refine ⟨L, ⟨hI.lin.append_inv p o, fun q o' hq => ?_, fun y hy => (hI.done y hy).mono,
        fun q hq => ?_⟩⟩
      · rcases List.mem_append.1 hq with hq | hq
        · exact hI.allow q o' hq
        · simp at hq; obtain ⟨rfl, rfl⟩ := hq; exact hall
      · by_cases hqp : q = p
        · subst hqp
          right
          refine ⟨o, by simp, by simp [unitAuthImpl], ?_, by simp [hcnt]⟩
          simp [opOf, ← hcnt]
        · simp only [Function.update_of_ne hqp]
          rcases hI.pend q hq with ⟨h1, h2, h3⟩ | ⟨o', h1, h2, h3, h4⟩
          · left; exact ⟨h1, h2, by simp [Ne.symm hqp, h3]⟩
          · right
            refine ⟨o', h1, h2, ?_, by simp [Ne.symm hqp, h4]⟩
            rw [show respsOf (hist α ++ [.inv p o]) q = respsOf (hist α) q by simp]
            rw [opOf_append_of_invoked (by simp [Invoked]; omega)]; exact h3
    | ret p r =>
      have hp : p ∉ Bz := hre
      have hh : hist (α ++ [.ret p r]) = hist α ++ [.ret p r] := by simp [hist]
      rw [hh]
      simp only [Impl.bstep] at he
      split_ifs at he with hpend
      split at he
      · rename_i i _ _ _; exact i.elim
      rename_i r' l hact
      split_ifs at he with hr
      subst hr
      cases he
      obtain ⟨o, ho, hloc, hop, hcnt⟩ : ∃ o, D.pend p = some o ∧ D.loc p = some (unitResp o) ∧
          opOf (hist α) (p, (respsOf (hist α) p).length) = some o ∧
          (opsOf (hist α) p).length = (respsOf (hist α) p).length + 1 := by
        rcases hI.pend p hp with ⟨h1, -⟩ | h
        · exact absurd h1 hpend
        · exact h
      rw [hloc] at hact
      simp only [unitAuthImpl] at hact
      cases hact
      set x : OpId P := (p, (respsOf (hist α) p).length)
      have hnc : ¬ Completed (hist α) x := by simp [x, Completed]
      have hnot : x ∉ L.map Prod.fst := fun hm => hnc (hI.done x hm)
      have hlin := (hI.lin.push hop hnot hnc).append_ret (r := unitResp o) L [] o rfl
        (unit_resp _ (unit_written _) o)
      refine ⟨L ++ [(x, o)], ⟨hlin, fun q o' hq => ?_, fun y hy => ?_, fun q hq => ?_⟩⟩
      · rcases List.mem_append.1 hq with hq | hq
        · exact hI.allow q o' hq
        · simp at hq
      · simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
          List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact (hI.done y hy).mono
        · simp [x, Completed]
      · by_cases hqp : q = p
        · subst hqp; left; simp [hcnt]
        · simp only [Function.update_of_ne hqp]
          rcases hI.pend q hq with ⟨h1, h2, h3⟩ | ⟨o', h1, h2, h3, h4⟩
          · left; exact ⟨h1, h2, by simp [Ne.symm hqp, h3]⟩
          · right
            refine ⟨o', h1, h2, ?_, by simp [Ne.symm hqp, h4]⟩
            rw [show respsOf (hist α ++ [.ret p (unitResp o)]) q = respsOf (hist α) q by
              simp [Ne.symm hqp]]
            simpa [opOf] using h3

/-- The trivial implementation of the authenticated register over the one-element domain `Unit`
(no shared objects) is correct against any number `f` of Byzantine processes, for every
invocation pattern; in particular Theorem 31 fails for authenticated registers whose domain has
only the initial value (the hypothesis `v ≠ v₀` of `theorem31_authenticated` is needed). -/
theorem authenticated_unit_byzCorrect (f : ℕ) :
    (unitAuthImpl B w).ByzCorrect acc f (fun _ _ => True) := by
  refine ⟨fun Bz _ α hα _ => ?_, fun Bz _ ev hval hfair _ p hp k => ?_⟩
  · obtain ⟨⟨C, hC⟩, hresp⟩ := hα
    obtain ⟨L, hI⟩ := unitInv_exec w α C hC hresp
    exact ⟨hist α, (unitAuthImpl B w).bhist_wellFormed acc hC, hI.allow, rfl, L, hI.lin⟩
  · set I := unitAuthImpl B w
    let cfg : ℕ → Config (authReg Unit ()) B P (Option (RegResp Unit)) :=
      fun k => Classical.choose (hval k).1
    have hcfg : ∀ k, I.brun acc (pre ev k) = some (cfg k) :=
      fun k => Classical.choose_spec (hval k).1
    have hstep : ∀ k, I.bstep acc (cfg k) (ev k) = some (cfg (k + 1)) := by
      intro k
      have := hcfg (k + 1)
      rw [Impl.pre_succ, Impl.brun] at this
      obtain ⟨C', h1, h2⟩ := I.brunFrom_append_eq_some _ this
      rw [← Impl.brun, hcfg k] at h1
      cases h1
      rwa [Impl.brunFrom_singleton] at h2
    obtain ⟨j, hj, hs⟩ := hfair p hp k
    have key : (cfg j).pend p = none ∨ (cfg (j + 1)).pend p = none := by
      by_cases hpj : (cfg j).pend p = none
      · exact Or.inl hpj
      right
      have h1 := hstep j
      cases hev : ev j with
      | inv q o => rw [hev] at hs; exact hs.elim
      | byz q i o => exact i.elim
      | tau q =>
        rw [hev] at hs h1; simp only [Event.IsStepOf] at hs; subst hs
        simp only [Impl.bstep] at h1
        split at h1
        · rename_i i _ _ _; exact i.elim
        · split_ifs at h1 with h2; exact absurd h2 hpj
      | ret q r =>
        rw [hev] at hs h1; simp only [Event.IsStepOf] at hs; subst hs
        simp only [Impl.bstep] at h1
        split_ifs at h1
        split at h1
        · rename_i i _ _ _; exact i.elim
        · split_ifs at h1; rw [← Option.some.inj h1]; simp
    rcases key with h | h
    · exact ⟨j, hj, fun C hC => by rw [hcfg j] at hC; cases hC; exact h⟩
    · exact ⟨j + 1, by omega, fun C hC => by rw [hcfg (j + 1)] at hC; cases hC; exact h⟩

/-- The degenerate case in the exact setting of `theorem31_authenticated`: an implementation of
the authenticated register over `V = Unit` from (zero) SWMR registers that is correct for every
`f`, although `3 ≤ n ≤ 3f` may hold. -/
theorem authenticated_unit_swmr (owner : Empty → P) {Val : Empty → Type}
    {v₀ : (i : Empty) → Val i} (f : ℕ) :
    ∃ I : Impl (authReg Unit ()) (fun i => register (Val i) (v₀ i)) P (Option (RegResp Unit)),
      I.allowed = authAllowed w ∧ I.RespectsAccess (swmrAccess owner) ∧
      I.ByzCorrect (swmrAccess owner) f (fun _ _ => True) :=
  ⟨unitAuthImpl _ w, rfl, fun _ _ i => i.elim, authenticated_unit_byzCorrect w f⟩

end

end Podc.ByzantineSWMRRegisters
