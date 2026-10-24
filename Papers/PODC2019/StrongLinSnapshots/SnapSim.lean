import Papers.PODC2019.StrongLinSnapshots.SnapInv

/-!
# Algorithm 3: the invariant is preserved; strong linearizability (Theorem 25)
-/

namespace Podc.StrongLinSnapshots.Snap

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {n : ℕ}

lemma Clause.first {α : Exec n} {C : Cfg n} {Lin : LinT n} {l : Vec n} {p : Fin n}
    (h : Clause α C Lin l p) (h1 : ¬ PostU (C.loc p)) (h2 : updVal (C.loc p) = none) :
    Sv C p = l p ∧ Q Lin p = l p := by
  obtain ⟨a, b⟩ := h
  exact ⟨a.resolve_right (fun h => h1 h.1), b.resolve_right (fun h => by rw [h2] at h; simp at h)⟩

lemma clause_of_first {α : Exec n} {C : Cfg n} {Lin : LinT n} {l : Vec n} {p : Fin n}
    (h1 : Sv C p = l p) (h2 : Q Lin p = l p) : Clause α C Lin l p := ⟨Or.inl h1, Or.inl h2⟩

/-! ## Invocations and responses -/

lemma step_inv_inv {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n} {o : SnapOp n}
    (hrun : (impl (n := n)).run α = some C) (hI : Inv α C Lin)
    (hstep : (impl (n := n)).step C (.inv p o) = some C') : Inv (α ++ [.inv p o]) C' Lin := by
  obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hstep
  have hidle : C.loc p = .idle := by
    have := hI.st p; unfold St at this; split at this <;> simp_all
  have hnot : ¬ Lp α Lin p := fun hm =>
    ((impl (n := n)).not_invoked_curOp_of_idle hrun h0) (hI.lin.invoked_of_mem hm)
  have hop : opOf (α ++ [.inv p o]) (curOp α p) = some o := by
    have hcnt := (impl (n := n)).run_idle_counts hrun h0
    simp [opOf, opsOf_append, hcnt]
  have hLp' : ¬ Lp (α ++ [.inv p o]) Lin p := by unfold Lp; rw [curOp_append_inv]; exact hnot
  have hg1 := hI.g1 p
  rw [hidle] at hg1
  have hSQ : Sv C p = Q Lin p := hg1.resolve_right (fun h => h.1)
  have hlp : C'.loc p = (impl (n := n)).invoke p .idle o := by
    rw [hloc, Function.update_self, hidle]
  have hcl : ∀ l, Clause α C Lin l p → Sv C p = l p ∧ Q Lin p = l p := fun l h =>
    h.first (by rw [hidle]; simp [PostU]) (by rw [hidle]; rfl)
  have hSv : Sv C' = Sv C := by simp [Sv, hmem]
  refine hI.frame (hI.lin.append_inv p o) (fun r hr => by rw [hloc, Function.update_of_ne hr])
    (fun r hr => by rw [hpend, Function.update_of_ne hr]) hSv
    (Or.inr ⟨by simp [Rv, hmem], fun q _ => by simp [Rv, hmem]⟩) (fun r _ => curOp_append_inv _ _ _ _)
    (fun _ _ h => opOf_append_of_eq_some h _) ?_ (Or.inl hSQ) ?_ ?_ ?_ ?_ ?_
  all_goals cases o with
    | update i x =>
      obtain ⟨rfl, -⟩ := hal
      simp only [impl] at hlp
      first
      | (unfold St; rw [hlp, hpend, Function.update_self, curOp_append_inv]
         exact ⟨by simp, hop⟩)
      | (intro x' h1 h2; rw [hlp] at h2; exact absurd h2 (by simp [PostU]))
      | (intro x' _ h; exact absurd h hLp')
      | (intro s1 h; rw [hlp] at h; simp at h)
      | (intro s1 l h; rw [hlp] at h; simp at h)
      | (intro l h; obtain ⟨a, b⟩ := hcl l h; exact clause_of_first (by rw [hSv]; exact a) b)
    | scan =>
      simp only [impl] at hlp
      first
      | (unfold St; rw [hlp, hpend, Function.update_self, curOp_append_inv]
         exact ⟨by simp, hLp', hop⟩)
      | (intro x' h1 h2; rw [hlp] at h2; exact absurd h2 (by simp [PostU]))
      | (intro x' h; rw [hlp] at h; simp [updVal] at h)
      | (intro s1 h; rw [hlp] at h; simp at h)
      | (intro s1 l h; rw [hlp] at h; simp at h)
      | (intro l h; obtain ⟨a, b⟩ := hcl l h; exact clause_of_first (by rw [hSv]; exact a) b)

lemma step_ret_inv {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n} {r : Vec n}
    (hI : Inv α C Lin) (hstep : (impl (n := n)).step C (.ret p r) = some C') :
    Inv (α ++ [.ret p r]) C' Lin := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hstep
  have hst := hI.st p
  have hlp : C'.loc p = l := by rw [hloc, Function.update_self]
  have hSv : Sv C' = Sv C := by simp [Sv, hmem]
  -- the returning process is at `uRet` or `sRet v`; both are "first-disjunct" states
  have key : ∀ pc : PC n, C.loc p = pc → ¬ PostU pc → updVal pc = none → l = .idle →
      (snapObj n).respIn (snapObj n).init Lin (curOp α p) = some r →
      Inv (α ++ [.ret p r]) C' Lin := by
    intro pc hpc hpost hupd hl hresp
    have hg1 := hI.g1 p
    rw [hpc] at hg1
    have hSQ : Sv C p = Q Lin p := hg1.resolve_right (fun h => hpost h.1)
    refine hI.frame (hI.lin.append_ret_of_respIn hresp)
      (fun q hq => by rw [hloc, Function.update_of_ne hq])
      (fun q hq => by rw [hpend, Function.update_of_ne hq]) hSv
      (Or.inr ⟨by simp [Rv, hmem], fun q _ => by simp [Rv, hmem]⟩)
      (fun q hq => curOp_append_ret_of_ne _ _ (Ne.symm hq))
      (fun _ _ h => opOf_append_of_eq_some h _) ?_ (Or.inl hSQ) ?_ ?_ ?_ ?_ ?_
    · unfold St; rw [hlp, hl, hpend, Function.update_self]
    · intro x h; rw [hlp, hl] at h; simp [updVal] at h
    · intro x h; rw [hlp, hl] at h; simp [updVal] at h
    · intro s1 h; rw [hlp, hl] at h; simp at h
    · intro s1 l' h; rw [hlp, hl] at h; simp at h
    · intro l' h
      obtain ⟨a, b⟩ := h.first (by rw [hpc]; exact hpost) (by rw [hpc]; exact hupd)
      exact clause_of_first (by rw [hSv]; exact a) b
  cases hpc : C.loc p
  case idle => unfold St at hst; rw [hpc] at hst; exact absurd hst h0
  case uRet =>
    simp only [impl, act, hpc, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact
    unfold St at hst; rw [hpc] at hst
    obtain ⟨-, hL, x, hx⟩ := hst
    exact key _ hpc (by simp [PostU]) rfl rfl (respIn_update hI.lin hL hx)
  case sRet v =>
    simp only [impl, act, hpc, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact
    unfold St at hst; rw [hpc] at hst
    exact key _ hpc (by simp [PostU]) rfl rfl hst.2
  all_goals simp [impl, act, hpc] at hact

/-! ## Internal steps -/

lemma tau_eq {C C' : Cfg n} {p : Fin n} {i : Obj} {o : (B n i).Op} {k : (B n i).Resp → PC n}
    (h : (impl (n := n)).step C (.tau p) = some C')
    (hact : (impl (n := n)).act p (C.loc p) = .access i o k) :
    C' = ⟨Function.update C.loc p (k ((B n i).δ (C.mem i) o).2), C.pend,
      Function.update C.mem i ((B n i).δ (C.mem i) o).1⟩ := by
  rw [Impl.step_tau_eq_some (Impl.step_tau h).1 hact] at h
  exact (Option.some.inj h).symm

lemma tau_u44 {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n} {x : ℕ}
    (hI : Inv α C Lin) (hpc : C.loc p = .u44 x)
    (hstep : (impl (n := n)).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have hact : (impl (n := n)).act p (C.loc p) = .access .S .scan (fun s => .u45 x s) := by
    simp [impl, act, hpc]
  have hC := tau_eq hstep hact
  have hlp : C'.loc p = .u45 x (C.mem .S) := by rw [hC]; simp
  have hloc : ∀ r, r ≠ p → C'.loc r = C.loc r := fun r hr => by rw [hC]; simp [hr]
  have hmem : C'.mem = C.mem := by rw [hC]; simp
  have hst := hI.st p
  unfold St at hst; rw [hpc] at hst
  have hg1 := hI.g1 p
  rw [hpc] at hg1
  refine hI.frame (hI.lin.append_tau p) hloc (fun q _ => by rw [hC]) (by simp [Sv, hmem])
    (Or.inr ⟨by simp [Rv, hmem], fun q _ => by simp [Rv, hmem]⟩) (fun q _ => curOp_append_tau _ _ _)
    (fun _ _ h => opOf_append_of_eq_some h _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold St; rw [hlp, curOp_append_tau, hC]
    exact ⟨hst.1, opOf_append_of_eq_some hst.2 _⟩
  · rw [hlp, Lp_tau]; exact hg1
  · intro x' h1 h2; rw [hlp] at h1; exact hI.g1' p x' (by rw [hpc]; exact h1) (by rw [hpc]; trivial)
  · intro x' h1 h2; rw [hlp] at h1; rw [Lp_tau] at h2
    exact hI.g2 p x' (by rw [hpc]; exact h1) h2
  · intro s1 h; rw [hlp] at h; simp at h
  · intro s1 l h; rw [hlp] at h; simp at h
  · intro l h
    unfold Clause at h ⊢
    rw [hpc] at h
    rw [hlp, Lp_tau, show Sv C' = Sv C by simp [Sv, hmem]]
    exact h

/-- Program counters inside the main loop of `SLscan`. -/
def IsScanPC : PC n → Prop
  | .s47 | .s48 _ | .s49 _ _ | .s51 _ => True
  | _ => False

lemma IsScanPC.postU {pc : PC n} (h : IsScanPC pc) : ¬ PostU pc := by
  cases pc <;> simp_all [IsScanPC, PostU]

lemma IsScanPC.updVal_eq {pc : PC n} (h : IsScanPC pc) : updVal pc = none := by
  cases pc <;> simp_all [IsScanPC, updVal]

lemma IsScanPC.st {α : Exec n} {C : Cfg n} {Lin : LinT n} {p : Fin n} (h : IsScanPC (C.loc p)) :
    St α C Lin p ↔ (C.pend p ≠ none ∧ ¬ Lp α Lin p ∧ opOf α (curOp α p) = some .scan) := by
  unfold St
  cases hc : C.loc p <;> rw [hc] at h <;> simp_all [IsScanPC]

/-- Frame for an internal step of a scanner inside its main loop that does not touch `S`. -/
lemma Inv.scan_frame {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n}
    (hI : Inv α C Lin) (hold : IsScanPC (C.loc p)) (hnew : IsScanPC (C'.loc p))
    (hloc : ∀ r, r ≠ p → C'.loc r = C.loc r) (hpend : C'.pend = C.pend)
    (hS : Sv C' = Sv C)
    (hR : (∀ q, (Rv C').2 q = true) ∨
      ((Rv C').1 = (Rv C).1 ∧ ∀ q, q ≠ p → (Rv C').2 q = (Rv C).2 q))
    (hrf : ∀ s1, (C'.loc p = .s48 s1 ∨ ∃ l, C'.loc p = .s49 s1 l) → (Rv C').2 p = false →
      (Rv C).1 = s1)
    (hgood : ∀ s1 l, C'.loc p = .s49 s1 l → (Rv C').2 p = false → s1 = l → Good α C Lin l) :
    Inv (α ++ [.tau p]) C' Lin := by
  have hst := (hold.st (α := α) (Lin := Lin)).1 (hI.st p)
  have hg1 := hI.g1 p
  have hSQ : Sv C p = Q Lin p := hg1.resolve_right (fun h => hold.postU h.1)
  refine hI.frame (hI.lin.append_tau p) hloc (fun q _ => by rw [hpend]) hS hR
    (fun q _ => curOp_append_tau _ _ _) (fun _ _ h => opOf_append_of_eq_some h _) ?_
    (Or.inl hSQ) ?_ ?_ hrf hgood ?_
  · rw [hnew.st, curOp_append_tau, hpend, Lp_tau]
    exact ⟨hst.1, hst.2.1, opOf_append_of_eq_some hst.2.2 _⟩
  · intro x h; rw [hnew.updVal_eq] at h; simp at h
  · intro x h; rw [hnew.updVal_eq] at h; simp at h
  · intro l h
    obtain ⟨a, b⟩ := h.first hold.postU hold.updVal_eq
    exact clause_of_first (by rw [hS]; exact a) b

lemma tau_s47 {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n}
    (hI : Inv α C Lin) (hpc : C.loc p = .s47)
    (hstep : (impl (n := n)).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have hact : (impl (n := n)).act p (C.loc p) = .access .R (.dread p) (fun r => .s48 r.1) := by
    simp [impl, act, hpc]
  have hC := tau_eq hstep hact
  have hlp : C'.loc p = .s48 (C.mem .R).1 := by rw [hC]; simp
  refine hI.scan_frame (by rw [hpc]; trivial) (by rw [hlp]; trivial)
    (fun r hr => by rw [hC]; simp [hr]) (by rw [hC]) (by rw [hC]; simp [Sv])
    (Or.inr ⟨by rw [hC]; simp [Rv], fun q hq => by
      rw [hC]; simp only [Rv, Function.update_self]
      exact Function.update_of_ne hq _ _⟩) ?_ ?_
  · intro s1 h _
    rw [hlp] at h
    rcases h with h | ⟨l, h⟩
    · cases h; rfl
    · cases h
  · intro s1 l h; rw [hlp] at h; cases h

lemma tau_s48 {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n} {s1 : Vec n}
    (hI : Inv α C Lin) (hpc : C.loc p = .s48 s1)
    (hstep : (impl (n := n)).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have hact : (impl (n := n)).act p (C.loc p) = .access .S .scan (fun l => .s49 s1 l) := by
    simp [impl, act, hpc]
  have hC := tau_eq hstep hact
  have hlp : C'.loc p = .s49 s1 (C.mem .S) := by rw [hC]; simp
  have hmem : C'.mem = C.mem := by rw [hC]; simp
  refine hI.scan_frame (by rw [hpc]; trivial) (by rw [hlp]; trivial)
    (fun r hr => by rw [hC]; simp [hr]) (by rw [hC]) (by simp [Sv, hmem])
    (Or.inr ⟨by simp [Rv, hmem], fun q _ => by simp [Rv, hmem]⟩) ?_ ?_
  · intro s1' h hf
    rw [hlp] at h
    rcases h with h | ⟨l, h⟩
    · cases h
    · cases h
      rw [show Rv C' = Rv C by simp [Rv, hmem]] at hf
      exact hI.rf p s1 (Or.inl hpc) hf
  · intro s1' l h hf he
    rw [hlp] at h
    cases h
    -- `S = ℓ`: establish `Good ℓ` from `g1`, `g1'`
    intro r
    refine ⟨Or.inl rfl, ?_⟩
    rcases hI.g1 r with h | ⟨hpost, hnl⟩
    · exact Or.inl h.symm
    · obtain ⟨x, hx⟩ := updVal_of_postU hpost
      have := hI.g1' r x hx hpost
      exact Or.inr ⟨by rw [hx, ← this], hnl⟩

lemma tau_s51 {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n} {l : Vec n}
    (hI : Inv α C Lin) (hpc : C.loc p = .s51 l)
    (hstep : (impl (n := n)).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have hact : (impl (n := n)).act p (C.loc p) = .access .R (.dwrite l) (fun _ => .s47) := by
    simp [impl, act, hpc]
  have hC := tau_eq hstep hact
  have hlp : C'.loc p = .s47 := by rw [hC]; simp
  refine hI.scan_frame (by rw [hpc]; trivial) (by rw [hlp]; trivial)
    (fun r hr => by rw [hC]; simp [hr]) (by rw [hC]) (by rw [hC]; simp [Sv])
    (Or.inl fun q => by rw [hC]; simp [Rv]) ?_ ?_
  · intro s1 h; rw [hlp] at h; simp at h
  · intro s1 l h; rw [hlp] at h; cases h

lemma tau_u43 {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n} {x : ℕ}
    (hI : Inv α C Lin) (hpc : C.loc p = .u43 x)
    (hstep : (impl (n := n)).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have hact : (impl (n := n)).act p (C.loc p) = .access .S (.update p x) (fun _ => .u44 x) := by
    simp [impl, act, hpc]
  have hC := tau_eq hstep hact
  have hlp : C'.loc p = .u44 x := by rw [hC]; simp
  have hloc : ∀ r, r ≠ p → C'.loc r = C.loc r := fun r hr => by rw [hC]; simp [hr]
  have hR : Rv C' = Rv C := by rw [hC]; simp [Rv]
  have hSp : Sv C' p = x := by rw [hC]; simp [Sv]
  have hSr : ∀ r, r ≠ p → Sv C' r = Sv C r := fun r hr => by
    rw [hC]; simp [Sv, Function.update_of_ne hr]
  have hst := hI.st p
  unfold St at hst; rw [hpc] at hst
  have hg2p : Lp α Lin p → Q Lin p = x := hI.g2 p x (by rw [hpc]; rfl)
  refine ⟨hI.lin.append_tau p, fun r => ?_, fun r => ?_, fun r y => ?_, fun r y => ?_,
    fun q s1 hq hf => ?_, fun q s1 l hq hf he => ?_⟩
  · by_cases hr : r = p
    · subst hr
      unfold St; rw [hlp, curOp_append_tau, hC]
      exact ⟨hst.1, opOf_append_of_eq_some hst.2 _⟩
    · simpa using (hI.st r).transfer (M := []) (hloc r hr) (by rw [hC])
        (curOp_append_tau _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp)
  · rw [Lp_tau]
    by_cases hr : r = p
    · subst hr
      rw [hlp, hSp]
      by_cases hL : Lp α Lin r
      · exact Or.inl (hg2p hL).symm
      · exact Or.inr ⟨trivial, hL⟩
    · rw [hSr r hr, hloc r hr]; exact hI.g1 r
  · intro h1 _
    by_cases hr : r = p
    · subst hr; rw [hlp] at h1; simp only [updVal, Option.some.injEq] at h1; rw [hSp, h1]
    · rename_i hpost
      rw [hloc r hr] at h1 hpost; rw [hSr r hr]; exact hI.g1' r y h1 hpost
  · intro h1 h2
    rw [Lp_tau] at h2
    by_cases hr : r = p
    · subst hr; rw [hlp] at h1; exact hI.g2 r y (by rw [hpc]; exact h1) h2
    · rw [hloc r hr] at h1; exact hI.g2 r y h1 h2
  · rw [hR] at hf ⊢
    by_cases hqp : q = p
    · subst hqp; rw [hlp] at hq; simp at hq
    · rw [hloc q hqp] at hq; exact hI.rf q s1 hq hf
  · rw [hR] at hf
    by_cases hqp : q = p
    · subst hqp; rw [hlp] at hq; cases hq
    rw [hloc q hqp] at hq
    have old := hI.good q s1 l hq hf he
    intro r
    have hor := old r
    show (Sv C' r = l r ∨ PostU (C'.loc r) ∧ ¬Lp (α ++ [Label.tau p]) Lin r) ∧
      (Q Lin r = l r ∨ updVal (C'.loc r) = some (l r) ∧ ¬Lp (α ++ [Label.tau p]) Lin r)
    rw [Lp_tau]
    by_cases hr : r = p
    · subst hr
      rw [hpc] at hor
      rw [hlp, hSp]
      refine ⟨?_, hor.2⟩
      by_cases hL : Lp α Lin r
      · rcases hor.2 with h | h
        · exact Or.inl ((hg2p hL).symm.trans h)
        · exact absurd hL h.2
      · exact Or.inr ⟨trivial, hL⟩
    · rw [hSr r hr, hloc r hr]; exact hor

lemma tau_u45 {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n} {x : ℕ} {sv : Vec n}
    (hI : Inv α C Lin) (hpc : C.loc p = .u45 x sv)
    (hstep : (impl (n := n)).step C (.tau p) = some C') :
    ∃ M, Inv (α ++ [.tau p]) C' (Lin ++ M) := by
  have hact : (impl (n := n)).act p (C.loc p) = .access .R (.dwrite sv) (fun _ => .uRet) := by
    simp [impl, act, hpc]
  have hC := tau_eq hstep hact
  have hlp : C'.loc p = .uRet := by rw [hC]; simp
  have hloc : ∀ r, r ≠ p → C'.loc r = C.loc r := fun r hr => by rw [hC]; simp [hr]
  have hS : Sv C' = Sv C := by rw [hC]; simp [Sv]
  have hRall : ∀ q, (Rv C').2 q = true := fun q => by rw [hC]; simp [Rv]
  have hst := hI.st p
  unfold St at hst; rw [hpc] at hst
  have hSp : Sv C p = x := hI.g1' p x (by rw [hpc]; rfl) (by rw [hpc]; trivial)
  -- the update is linearized now, unless it already was
  obtain ⟨M, hlin', hM, hQp, hQr, hLpp⟩ : ∃ M : LinT n,
      IsLinearization (α ++ [.tau p]) (Lin ++ M) ∧ (∀ r, r ≠ p → curOp α r ∉ M.map Prod.fst) ∧
      Q (Lin ++ M) p = x ∧ (∀ r, r ≠ p → Q (Lin ++ M) r = Q Lin r) ∧ Lp α (Lin ++ M) p := by
    by_cases hL : Lp α Lin p
    · refine ⟨[], by simpa using hI.lin.append_tau p, by simp, ?_, by simp, by simpa using hL⟩
      simpa using hI.g2 p x (by rw [hpc]; rfl) hL
    · refine ⟨[(curOp α p, .update p x)], (hI.lin.push hst.2 hL (not_completed_curOp α p)).append_tau p,
        fun r hr => by simp [curOp, hr], by rw [Q, linState_concat]; simp,
        fun r hr => by rw [Q, linState_concat]; simp [Function.update_of_ne hr],
        by simp [Lp]⟩
  have hLp : ∀ r, r ≠ p → (Lp α (Lin ++ M) r ↔ Lp α Lin r) := fun r hr => by
    unfold Lp; rw [List.map_append, List.mem_append]
    exact ⟨fun h => h.resolve_right (hM r hr), Or.inl⟩
  refine ⟨M, hlin', fun r => ?_, fun r => ?_, fun r y => ?_, fun r y => ?_,
    fun q s1 _ hf => ?_, fun q s1 l _ hf _ => ?_⟩
  · by_cases hr : r = p
    · subst hr
      unfold St; rw [hlp, curOp_append_tau, hC]
      exact ⟨hst.1, by simpa [Lp] using hLpp, x, opOf_append_of_eq_some hst.2 _⟩
    · exact (hI.st r).transfer (hloc r hr) (by rw [hC]) (curOp_append_tau _ _ _)
        (fun _ h => opOf_append_of_eq_some h _) (fun _ => hM r hr)
  · rw [hS, Lp_tau]
    by_cases hr : r = p
    · subst hr; exact Or.inl (hSp.trans hQp.symm)
    · rw [hQr r hr, hloc r hr, hLp r hr]; exact hI.g1 r
  · intro h1 h2
    rw [hS]
    by_cases hr : r = p
    · subst hr; rw [hlp] at h1; simp [updVal] at h1
    · rw [hloc r hr] at h1 h2; exact hI.g1' r y h1 h2
  · intro h1 h2
    rw [Lp_tau] at h2
    by_cases hr : r = p
    · subst hr; rw [hlp] at h1; simp [updVal] at h1
    · rw [hloc r hr] at h1; rw [hLp r hr] at h2; rw [hQr r hr]; exact hI.g2 r y h1 h2
  · rw [hRall q] at hf; simp at hf
  · rw [hRall q] at hf; simp at hf

lemma St.opOf_upd {α : Exec n} {C : Cfg n} {Lin : LinT n} {r : Fin n} {x : ℕ}
    (h : St α C Lin r) (hx : updVal (C.loc r) = some x) :
    opOf α (curOp α r) = some (.update r x) := by
  unfold St at h
  cases hc : C.loc r <;> rw [hc] at h hx <;> simp only [updVal, reduceCtorEq,
    Option.some.injEq] at hx <;> subst hx <;> exact h.2

/-- The processes whose pending updates are linearized by a scan returning `l`. -/
def helpers (α : Exec n) (C : Cfg n) (Lin : LinT n) (l : Vec n) : List (Fin n) :=
  (List.finRange n).filter fun r => decide (updVal (C.loc r) = some (l r) ∧ ¬ Lp α Lin r)

lemma mem_helpers {α : Exec n} {C : Cfg n} {Lin : LinT n} {l : Vec n} {r : Fin n} :
    r ∈ helpers α C Lin l ↔ updVal (C.loc r) = some (l r) ∧ ¬ Lp α Lin r := by
  simp [helpers]

lemma tau_s49 {α : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n} {s1 l : Vec n}
    (hI : Inv α C Lin) (hpc : C.loc p = .s49 s1 l)
    (hstep : (impl (n := n)).step C (.tau p) = some C') :
    ∃ M, Inv (α ++ [.tau p]) C' (Lin ++ M) := by
  have hact : (impl (n := n)).act p (C.loc p) = .access .R (.dread p) (fun r =>
      if s1 = l ∧ l = r.1 then (if r.2 = false then .sRet r.1 else .s47) else .s51 l) := by
    simp [impl, act, hpc]
  have hC := tau_eq hstep hact
  set R := Rv C with hRdef
  have hRv : Rv C' = (R.1, Function.update R.2 p false) := by rw [hC]; simp [Rv, R]
  have hS : Sv C' = Sv C := by rw [hC]; simp [Sv]
  have hloc : ∀ r, r ≠ p → C'.loc r = C.loc r := fun r hr => by rw [hC]; simp [hr]
  have hRr : (Rv C').1 = (Rv C).1 ∧ ∀ q, q ≠ p → (Rv C').2 q = (Rv C).2 q :=
    ⟨by rw [hRv], fun q hq => by rw [hRv]; exact Function.update_of_ne hq _ _⟩
  have hlp0 : C'.loc p = if s1 = l ∧ l = R.1 then (if R.2 p = false then .sRet R.1 else .s47)
      else .s51 l := by rw [hC]; simp [R, Rv]
  by_cases hg : s1 = l ∧ l = R.1
  swap
  · -- the vectors differ: help (line 51)
    simp only [eq_false hg, ↓reduceIte] at hlp0
    have := hI.scan_frame (by rw [hpc]; trivial) (by rw [hlp0]; trivial) hloc
      (by rw [hC]) hS (Or.inr hRr) (fun s1' h => by rw [hlp0] at h; simp at h)
      (fun s1' l' h => by rw [hlp0] at h; cases h)
    exact ⟨[], by simpa using this⟩
  by_cases hf : R.2 p = false
  swap
  · -- `R` was written since line 47: repeat
    simp only [eq_true hg, eq_false hf, ↓reduceIte] at hlp0
    have := hI.scan_frame (by rw [hpc]; trivial) (by rw [hlp0]; trivial) hloc
      (by rw [hC]) hS (Or.inr hRr) (fun s1' h => by rw [hlp0] at h; simp at h)
      (fun s1' l' h => by rw [hlp0] at h; cases h)
    exact ⟨[], by simpa using this⟩
  -- the linearization point of the scan
  simp only [eq_true hg, eq_true hf, ↓reduceIte] at hlp0
  obtain ⟨hsl, hlR⟩ := hg
  have hgood := hI.good p s1 l hpc hf hsl
  set hs := helpers α C Lin l with hhs
  set H : LinT n := hs.map fun r => (curOp α r, SnapOp.update r (l r)) with hH
  set M : LinT n := H ++ [(curOp α p, .scan)] with hMdef
  have hst := hI.st p
  rw [(show IsScanPC (C.loc p) by rw [hpc]; trivial).st] at hst
  obtain ⟨h0, hnLp, hopp⟩ := hst
  have hpH : p ∉ hs := by rw [hhs, mem_helpers, hpc]; simp [updVal]
  have hQH : ∀ r, Q (Lin ++ H) r = if r ∈ hs then l r else Q Lin r := by
    intro r
    rw [Q, linState_append, hH, List.map_map]
    show (snapObj n).runOps _ (hs.map fun r => SnapOp.update r (l r)) r = _
    rw [runOps_updates]
  have hQl : Q (Lin ++ H) = l := by
    funext r
    rw [hQH r]
    split_ifs with hr
    · rfl
    · rcases (hgood r).2 with h | h
      · exact h
      · exact absurd (mem_helpers.2 h) hr
  have hQM : Q (Lin ++ M) = l := by
    rw [hMdef, ← List.append_assoc, Q, linState_concat]; exact hQl
  have hLpM : ∀ r, Lp α (Lin ++ M) r ↔ Lp α Lin r ∨ r ∈ hs ∨ r = p := by
    intro r
    have e1 : curOp α r ∈ H.map Prod.fst ↔ r ∈ hs := by
      rw [hH, List.map_map, List.mem_map]
      exact ⟨fun ⟨a, ha, he⟩ => curOp_inj he ▸ ha, fun h => ⟨r, h, rfl⟩⟩
    have e2 : curOp α r = curOp α p ↔ r = p := ⟨curOp_inj, fun h => h ▸ rfl⟩
    unfold Lp
    rw [hMdef, List.map_append, List.map_append, List.mem_append, List.mem_append, e1]
    simp only [List.map_cons, List.map_nil, List.mem_singleton, e2]
  have hSl : ∀ r, r ∈ hs → Sv C r = l r := by
    intro r hr
    rcases (hgood r).1 with h | ⟨hpost, -⟩
    · exact h
    · exact hI.g1' r (l r) (mem_helpers.1 hr).1 hpost
  -- the new linearization
  have hlin : IsLinearization α (Lin ++ M) := by
    refine hI.lin.push_list M (fun y hy => ?_) ?_ (fun y hy => ?_)
    · rw [hMdef, List.mem_append] at hy
      rcases hy with hy | hy
      · rw [hH, List.mem_map] at hy
        obtain ⟨r, hr, rfl⟩ := hy
        exact ⟨(hI.st r).opOf_upd (mem_helpers.1 hr).1, not_completed_curOp _ _⟩
      · simp only [List.mem_singleton] at hy; subst hy
        exact ⟨hopp, not_completed_curOp _ _⟩
    · rw [hMdef, hH, List.map_append, List.map_map, List.nodup_append]
      refine ⟨((List.nodup_finRange n).filter _).map (fun a b h => curOp_inj h),
        List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
      subst hb
      exact hpH (by rw [← curOp_inj hab]; exact hr)
    · rw [hMdef, List.mem_append] at hy
      rcases hy with hy | hy
      · rw [hH, List.mem_map] at hy
        obtain ⟨r, hr, rfl⟩ := hy
        exact (mem_helpers.1 hr).2
      · simp only [List.mem_singleton] at hy; subst hy; exact hnLp
  have hlp : C'.loc p = .sRet l := by rw [hlp0, hlR]
  refine ⟨M, hlin.append_tau p, fun r => ?_, fun r => ?_, fun r y => ?_, fun r y => ?_,
    fun q s1' hq hf' => ?_, fun q s1' l' hq hf' he => ?_⟩
  · by_cases hr : r = p
    · subst hr
      unfold St
      rw [hlp, curOp_append_tau, hMdef, ← List.append_assoc]
      refine ⟨by rw [hC]; exact h0, ?_⟩
      rw [ObjSpec.respIn_concat_self (by
        rw [List.map_append, List.mem_append, not_or]
        refine ⟨hnLp, fun hm => ?_⟩
        rw [hH, List.map_map, List.mem_map] at hm
        obtain ⟨r', hr', he⟩ := hm
        exact hpH (by rw [← curOp_inj he]; exact hr'))]
      exact congrArg some hQl
    · refine (hI.st r).transfer (hloc r hr) (by rw [hC]) (curOp_append_tau _ _ _)
        (fun _ h => opOf_append_of_eq_some h _) (fun hn hm => ?_)
      rw [hMdef, hH, List.map_append, List.map_map, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨r', hr', he⟩ := List.mem_map.1 hm
        have := curOp_inj he
        subst this
        rw [mem_helpers, hn] at hr'; simp at hr'
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hm
        exact hr (curOp_inj hm)
  · rw [hS, Lp_tau, hQM]
    by_cases hr : r ∈ hs
    · exact Or.inl (hSl r hr)
    by_cases hrp : r = p
    · subst hrp; rw [hlp]
      exact Or.inl ((hgood r).1.resolve_right (fun h => by rw [hpc] at h; exact h.1))
    rw [hloc r hrp]
    rcases (hgood r).1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, fun hL => ((hLpM r).1 hL).elim h.2 (fun h' => h'.elim hr hrp)⟩
  · intro h1 h2
    rw [hS]
    by_cases hrp : r = p
    · subst hrp; rw [hlp] at h1; simp [updVal] at h1
    · rw [hloc r hrp] at h1 h2; exact hI.g1' r y h1 h2
  · intro h1 h2
    rw [Lp_tau] at h2
    rw [hQM]
    by_cases hrp : r = p
    · subst hrp; rw [hlp] at h1; simp [updVal] at h1
    rw [hloc r hrp] at h1
    by_cases hr : r ∈ hs
    · rw [(mem_helpers.1 hr).1] at h1; exact Option.some.inj h1
    · have hL : Lp α Lin r := ((hLpM r).1 h2).resolve_right (fun h' => h'.elim hr hrp)
      have hq := hI.g2 r y h1 hL
      rcases (hgood r).2 with h | h
      · exact h.symm.trans hq
      · exact absurd hL h.2
  · rw [hRv] at hf' ⊢
    by_cases hqp : q = p
    · subst hqp; rw [hlp] at hq; simp at hq
    · rw [hloc q hqp] at hq
      simp only [Function.update_of_ne hqp] at hf'
      exact hI.rf q s1' hq hf'
  · rw [hRv] at hf'
    by_cases hqp : q = p
    · subst hqp; rw [hlp] at hq; cases hq
    rw [hloc q hqp] at hq
    simp only [Function.update_of_ne hqp] at hf'
    have hR1 := hI.rf q s1' (Or.inr ⟨l', hq⟩) hf'
    have hl' : l' = l := by rw [← he, ← hR1, hlR]
    subst hl'
    intro r
    refine ⟨?_, Or.inl (by rw [hQM])⟩
    rw [hS, Lp_tau]
    by_cases hr : r ∈ hs
    · exact Or.inl (hSl r hr)
    rcases (hgood r).1 with h | h
    · exact Or.inl h
    · have hrp : r ≠ p := fun e => by subst e; rw [hpc] at h; exact h.1
      rw [hloc r hrp]
      exact Or.inr ⟨h.1, fun hL => ((hLpM r).1 hL).elim h.2 (fun h' => h'.elim hr hrp)⟩

/-! ## The simulation -/

lemma initInv : Inv (n := n) [] (impl (n := n)).initCfg [] := by
  refine ⟨isLinearization_nil, fun p => ?_, fun p => Or.inl rfl, fun p x h => ?_, fun p x h => ?_,
    fun q s1 h => ?_, fun q s1 l h => ?_⟩
  · simp [St, impl, Impl.initCfg]
  all_goals simp [impl, Impl.initCfg, updVal] at h

/-- The invariant is a forward simulation into the atomic snapshot. -/
theorem linSim : (impl (n := n)).LinSim Inv where
  init := initInv
  lin _ _ _ _ h := h.lin
  step := by
    intro α C Lin ℓ C' hrun hI hstep
    cases ℓ with
    | inv p o => exact ⟨[], by rw [List.append_nil]; exact step_inv_inv hrun hI hstep⟩
    | ret p r => exact ⟨[], by rw [List.append_nil]; exact step_ret_inv hI hstep⟩
    | tau p =>
      cases hpc : C.loc p with
      | u43 x => exact ⟨[], by rw [List.append_nil]; exact tau_u43 hI hpc hstep⟩
      | u44 x => exact ⟨[], by rw [List.append_nil]; exact tau_u44 hI hpc hstep⟩
      | u45 x s => exact tau_u45 hI hpc hstep
      | s47 => exact ⟨[], by rw [List.append_nil]; exact tau_s47 hI hpc hstep⟩
      | s48 s1 => exact ⟨[], by rw [List.append_nil]; exact tau_s48 hI hpc hstep⟩
      | s49 s1 l => exact tau_s49 hI hpc hstep
      | s51 l => exact ⟨[], by rw [List.append_nil]; exact tau_s51 hI hpc hstep⟩
      | idle | uRet | sRet _ =>
        obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hstep
        simp [impl, act, hpc] at hact

/-- **Theorem 25** (Ovens–Woelfel), for atomic `S` and `R`: Algorithm 3 is a strongly
linearizable implementation of the single-writer snapshot. The linearization points are those
of R-1/R-2 (scans at their last `R.DRead`; updates at the first scan returning their value, or at
their own `R.DWrite`). -/
theorem stronglyLinearizable : (impl (n := n)).StronglyLinearizable :=
  (impl (n := n)).stronglyLinearizable_of_linSim _ linSim

end Podc.StrongLinSnapshots.Snap
