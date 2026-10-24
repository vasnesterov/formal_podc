import Papers.PODC2019.StrongLinSnapshots.ABAInv

/-!
# Algorithm 2: the invariant is preserved (forward simulation)

Every step preserves `Inv` (`linSim`); the step that writes `X` linearizes the `DWrite`
(Q-2), the last read of `X` in a `DRead` linearizes the `DRead` (Q-1). Hence Algorithm 2 is
strongly linearizable (`stronglyLinearizable`, Theorem 12 of the paper).
-/

namespace Podc.StrongLinSnapshots

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

set_option linter.unusedSectionVars false

variable {n : ℕ} {V : Type} [DecidableEq V] {v₀ : V} {pick : List (Seq n) → Seq n}

/-- Frame lemma: a step that changes only `p`'s local state (keeping its `GetSeq` state, never
at a `wX`), possibly `p`'s pending operation and `A[p]`, and does not linearize anything. -/
lemma Inv.frame {α α' : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n}
    (hI : Inv α C Lin) (hlin : IsLinearization α' Lin)
    (hloc : ∀ q, q ≠ p → C'.loc q = C.loc q) (hpend : ∀ q, q ≠ p → C'.pend q = C.pend q)
    (hX : C'.mem none = C.mem none) (hA : ∀ q, q ≠ p → C'.mem (some q) = C.mem (some q))
    (hcur : ∀ q, q ≠ p → curOp α' q = curOp α q)
    (hop : ∀ x o, opOf α x = some o → opOf α' x = some o)
    (hgs : (C'.loc p).gs = (C.loc p).gs) (hw : (C.loc p).pc.isWX = false)
    (hw' : (C'.loc p).pc.isWX = false)
    (hst : St α' C' Lin p)
    (hrd : RInv (C'.loc p).pc (C.mem none) (C'.mem (some p)).2 ((linState Lin).2 p))
    (hcl : CleanPC (C'.loc p).pc →
      CleanPC (C.loc p).pc ∧ (C'.mem (some p)).2 = (C.mem (some p)).2) :
    Inv α' C' Lin := by
  refine ⟨hlin, fun q => ?_, by rw [hX]; exact hI.val, fun q => ?_, fun q => ?_, ?_⟩
  · by_cases hq : q = p
    · subst hq; exact hst
    · simpa using (hI.st q).transfer (M := []) (hloc q hq) (hpend q hq) (hcur q hq)
        (hop _) (by simp)
  · by_cases hq : q = p
    · subst hq; rw [hX]; exact hrd
    · rw [hloc q hq, hX, hA q hq]; exact hI.rd q
  · rw [hX]
    by_cases hq : q = p
    · subst hq; exact (hI.wr q).congr hgs hw hw'
    · rw [hloc q hq]; exact hI.wr q
  · intro q p' s' hc ha
    have hold : ProtBy (C.loc p') q s' := by
      by_cases hq : q = p
      · subst hq
        obtain ⟨hc', ha'⟩ := hcl hc
        exact hI.prot q p' s' hc' (ha'.symm.trans ha)
      · rw [hloc q hq] at hc; rw [hA q hq] at ha
        exact hI.prot q p' s' hc ha
    by_cases hp' : p' = p
    · subst hp'; exact hold.congr hgs hw'
    · rw [hloc p' hp']; exact hold

/-- The current operation of an idle process is not linearized. -/
lemma curOp_notMem_of_idle {α : Exec n V v₀} {C : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n}
    (hrun : (impl v₀ pick).run α = some C) (hlin : IsLinearization α Lin)
    (h0 : C.pend p = none) : curOp α p ∉ Lin.map Prod.fst := by
  intro hm
  have := hlin.invoked_of_mem hm
  have := (impl v₀ pick).not_invoked_curOp_of_idle hrun h0
  contradiction

/-- The high-level operation being executed in a program counter of `p` (before its
linearization point). -/
def pendOp (p : Fin n) : PC n V → Option (ABAOp (Fin n) V)
  | .wA x | .wX x _ => some (.dwrite x)
  | .r34 _ | .r35 _ _ | .r36 _ _ _ | .r37 _ _ _ => some (.dread p)
  | _ => none

lemma st_iff_of_pendOp {α : Exec n V v₀} {C : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n}
    {o : ABAOp (Fin n) V} (h : pendOp p (C.loc p).pc = some o) :
    St α C Lin p ↔ (C.pend p ≠ none ∧ curOp α p ∉ Lin.map Prod.fst ∧
      opOf α (curOp α p) = some o) := by
  unfold St
  cases hpc : (C.loc p).pc <;> rw [hpc] at h <;> simp only [pendOp, reduceCtorEq,
    Option.some.injEq] at h <;> subst h <;> simp only

/-- A step of `p` that neither linearizes nor completes its operation keeps its status. -/
lemma St.tau_self {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n}
    {o : ABAOp (Fin n) V} (hst : St α C Lin p) (ho : pendOp p (C.loc p).pc = some o)
    (ho' : pendOp p (C'.loc p).pc = some o) (hpend : C'.pend p = C.pend p) :
    St (α ++ [.tau p]) C' Lin p := by
  rw [st_iff_of_pendOp ho] at hst
  rw [st_iff_of_pendOp ho', hpend, curOp_append_tau]
  exact ⟨hst.1, hst.2.1, opOf_append_of_eq_some hst.2.2 _⟩

/-! ## Invocations and responses -/

lemma step_inv_inv {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n}
    {o : ABAOp (Fin n) V} (hrun : (impl v₀ pick).run α = some C) (hI : Inv α C Lin)
    (hstep : (impl v₀ pick).step C (.inv p o) = some C') :
    Inv (α ++ [.inv p o]) C' Lin := by
  obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hstep
  have hidle : (C.loc p).pc = .idle := by
    have := hI.st p
    unfold St at this
    split at this <;> simp_all
  have hnot := curOp_notMem_of_idle hrun hI.lin h0
  have hop : opOf (α ++ [.inv p o]) (curOp α p) = some o := by
    have hcnt := (impl v₀ pick).run_idle_counts hrun h0
    simp [opOf, opsOf_append, hcnt]
  have hr := hI.rd p
  rw [hidle] at hr
  have hr : (linState Lin).2 p = true ↔ (C.mem none).2 ≠ (C.mem (some p)).2 := hr.1 trivial
  have key : ∀ pc' : PC n V, C'.loc p = ⟨pc', (C.loc p).gs⟩ → pc'.isWX = false →
      opOf (α ++ [.inv p o]) (curOp α p) = some o →
      St (α ++ [.inv p o]) C' Lin p →
      RInv pc' (C.mem none) (C.mem (some p)).2 ((linState Lin).2 p) →
      Inv (α ++ [.inv p o]) C' Lin := by
    intro pc' hlp hw' _ hst hrd
    refine hI.frame (hI.lin.append_inv p o) (fun q hq => by rw [hloc, Function.update_of_ne hq])
      (fun q hq => by rw [hpend, Function.update_of_ne hq]) (by rw [hmem])
      (fun q _ => by rw [hmem]) (fun q _ => curOp_append_inv _ _ _ _)
      (fun _ _ h => opOf_append_of_eq_some h _) (by rw [hlp]) (by rw [hidle]; rfl)
      (by rw [hlp]; exact hw') hst (by rw [hlp, hmem]; exact hrd)
      (by rw [hlp, hidle, hmem]; exact fun _ => ⟨trivial, rfl⟩)
  cases o with
  | dwrite x =>
    have hlp : C'.loc p = ⟨.wA x, (C.loc p).gs⟩ := by rw [hloc, Function.update_self]; rfl
    refine key _ hlp rfl hop ?_ ⟨fun _ => hr, trivial⟩
    unfold St; rw [hlp, hpend, Function.update_self, curOp_append_inv]
    exact ⟨by simp, hnot, hop⟩
  | dread q =>
    have hq : q = p := hal
    subst hq
    have hlp : C'.loc q = ⟨.r34 false, (C.loc q).gs⟩ := by rw [hloc, Function.update_self]; rfl
    refine key _ hlp rfl hop ?_ ⟨fun _ => hr, by simp⟩
    unfold St; rw [hlp, hpend, Function.update_self, curOp_append_inv]
    exact ⟨by simp, hnot, hop⟩

lemma step_ret_inv {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n}
    {r : V × Bool} (hI : Inv α C Lin)
    (hstep : (impl v₀ pick).step C (.ret p r) = some C') :
    Inv (α ++ [.ret p r]) C' Lin := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hstep
  have hst := hI.st p
  have hr := hI.rd p
  have key : ∀ pc : PC n V, (C.loc p).pc = pc → CleanPC pc → pc.isWX = false →
      l = ⟨.idle, (C.loc p).gs⟩ →
      (abaObj (Fin n) V v₀).respIn (abaObj (Fin n) V v₀).init Lin (curOp α p) = some r →
      Inv (α ++ [.ret p r]) C' Lin := by
    intro pc hpc hc hw hl hresp
    rw [hpc] at hr
    have hlp : C'.loc p = ⟨.idle, (C.loc p).gs⟩ := by rw [hloc, Function.update_self, hl]
    refine hI.frame (hI.lin.append_ret_of_respIn hresp)
      (fun q hq => by rw [hloc, Function.update_of_ne hq])
      (fun q hq => by rw [hpend, Function.update_of_ne hq]) (by rw [hmem])
      (fun q _ => by rw [hmem]) (fun q hq => curOp_append_ret_of_ne _ _ (Ne.symm hq))
      (fun _ _ h => opOf_append_of_eq_some h _) (by rw [hlp]) (by rw [hpc]; exact hw)
      (by rw [hlp]; rfl) ?_ ?_ (by rw [hlp, hpc, hmem]; exact fun _ => ⟨hc, rfl⟩)
    · unfold St; rw [hlp, hpend, Function.update_self]
    · rw [hlp, hmem]; exact ⟨fun _ => hr.1 hc, trivial⟩
  cases hpc : (C.loc p).pc
  case idle => unfold St at hst; rw [hpc] at hst; exact absurd hst h0
  case wRet x =>
    simp only [impl, implG, actG, hpc, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact
    unfold St at hst; rw [hpc] at hst
    exact key _ hpc trivial rfl rfl hst.2
  case rRet x ch =>
    simp only [impl, implG, actG, hpc, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact
    unfold St at hst; rw [hpc] at hst
    exact key _ hpc trivial rfl rfl hst.2
  all_goals simp [impl, implG, actG, hpc] at hact

/-! ## Internal steps -/

/-- Frame for internal steps of `p` that keep its `GetSeq` state, change at most `A[p]` and
linearize nothing. -/
lemma Inv.tau_frame {α : Exec n V v₀} {C : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n}
    (hI : Inv α C Lin) (m : (i : Obj n) → (B n V v₀ i).State) (pc' : PC n V)
    (hm : ∀ i, i ≠ some p → m i = C.mem i)
    (hw : (C.loc p).pc.isWX = false) (hw' : pc'.isWX = false)
    {o : ABAOp (Fin n) V} (ho : pendOp p (C.loc p).pc = some o) (ho' : pendOp p pc' = some o)
    (hrd : RInv pc' (C.mem none) (m (some p)).2 ((linState Lin).2 p))
    (hcl : CleanPC pc' → CleanPC (C.loc p).pc ∧ (m (some p)).2 = (C.mem (some p)).2) :
    Inv (α ++ [.tau p]) (⟨Function.update C.loc p ⟨pc', (C.loc p).gs⟩, C.pend, m⟩ : Cfg n V v₀)
      Lin := by
  have hlp : (Function.update C.loc p (⟨pc', (C.loc p).gs⟩ : Loc n V)) p = ⟨pc', (C.loc p).gs⟩ :=
    Function.update_self _ _ _
  refine hI.frame (hI.lin.append_tau p) (fun q hq => Function.update_of_ne hq _ _)
    (fun q _ => rfl) (hm none (by simp)) (fun q hq => hm _ (by simpa using hq))
    (fun q _ => curOp_append_tau _ _ _) (fun _ _ h => opOf_append_of_eq_some h _)
    (by simp only [hlp]) hw (by simp only [hlp]; exact hw') ?_ (by simp only [hlp]; exact hrd)
    (by simp only [hlp]; exact hcl)
  exact (hI.st p).tau_self ho (by simp only [hlp]; exact ho') rfl

/-- The response of a register read. -/
lemma reg_read (m : Val n V) : (register (Val n V) (v₀, none)).δ m .read = (m, m) := rfl

lemma tau_r34 {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n} {ch : Bool}
    (hI : Inv α C Lin) (hpc : (C.loc p).pc = .r34 ch)
    (hstep : (impl v₀ pick).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have h0 := (Impl.step_tau hstep).1
  have hact : (impl v₀ pick).act p (C.loc p) = .access none .read
      (fun v => (⟨.r35 ch v, (C.loc p).gs⟩ : Loc n V)) := by
    simp [impl, implG, actG, hpc]
  rw [Impl.step_tau_eq_some h0 hact] at hstep
  obtain rfl := Option.some.inj hstep
  have hr := hI.rd p
  rw [hpc] at hr
  refine hI.tau_frame _ (.r35 ch (C.mem none)) (fun i _ => by
      by_cases hi : i = none
      · subst hi; simp
      · rw [Function.update_of_ne hi]) (by rw [hpc]; rfl) rfl (by rw [hpc]; rfl) rfl ?_ ?_
  · simp only [Function.update_of_ne (show (some p : Obj n) ≠ none by simp)]
    exact ⟨hr.1, hr.2, fun _ => rfl⟩
  · simp only [Function.update_of_ne (show (some p : Obj n) ≠ none by simp), hpc]
    exact fun h => ⟨h, trivial⟩

lemma tau_r35 {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n} {ch : Bool}
    {v : Val n V} (hI : Inv α C Lin) (hpc : (C.loc p).pc = .r35 ch v)
    (hstep : (impl v₀ pick).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have h0 := (Impl.step_tau hstep).1
  have hact : (impl v₀ pick).act p (C.loc p) = .access (some p) .read
      (fun a => (⟨.r36 ch v a.2, (C.loc p).gs⟩ : Loc n V)) := by
    simp [impl, implG, actG, hpc]
  rw [Impl.step_tau_eq_some h0 hact] at hstep
  obtain rfl := Option.some.inj hstep
  have hr := hI.rd p
  rw [hpc] at hr
  refine hI.tau_frame _ (.r36 ch v (C.mem (some p)).2) (fun i _ => by
      by_cases hi : i = some p
      · subst hi; simp
      · rw [Function.update_of_ne hi]) (by rw [hpc]; rfl) rfl (by rw [hpc]; rfl) rfl ?_ ?_
  · simp only [Function.update_self]
    exact ⟨hr.1, rfl, hr.2.1, hr.2.2⟩
  · simp only [Function.update_self, hpc]
    exact fun h => ⟨h, trivial⟩

lemma tau_r36 {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n} {ch : Bool}
    {v : Val n V} {a' : Tag n} (hI : Inv α C Lin) (hpc : (C.loc p).pc = .r36 ch v a')
    (hstep : (impl v₀ pick).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have h0 := (Impl.step_tau hstep).1
  have hact : (impl v₀ pick).act p (C.loc p) = .access (some p) (.write (v₀, v.2))
      (fun _ => (⟨.r37 ch v a', (C.loc p).gs⟩ : Loc n V)) := by
    simp [impl, implG, actG, hpc]
  rw [Impl.step_tau_eq_some h0 hact] at hstep
  obtain rfl := Option.some.inj hstep
  have hr := hI.rd p
  rw [hpc] at hr
  obtain ⟨hc, ha', hch, hFX⟩ := hr
  refine hI.tau_frame _ (.r37 ch v a') (fun i hi => Function.update_of_ne hi _ _)
    (by rw [hpc]; rfl) rfl (by rw [hpc]; rfl) rfl ?_ ?_
  · simp only [Function.update_self]
    refine ⟨fun ⟨h1, h2⟩ => ?_, rfl, hch, fun hF => by
      exact hFX hF,
      fun hne => ?_⟩
    · have : v.2 = (C.mem (some p)).2 := h2.symm.trans ha'
      simp only [this]
      exact hc h1
    · by_contra hF
      simp only [Bool.not_eq_true] at hF
      cases ch
      · have := (hc rfl).not.1 (by simp [hF])
        rw [not_not, hFX hF] at this
        exact hne (ha'.trans this.symm)
      · simp [hch rfl] at hF
  · simp only [Function.update_self, hpc]
    exact fun ⟨h1, h2⟩ => ⟨h1, (h2.symm.trans ha' : v.2 = _)⟩

lemma tau_r37 {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀} {p : Fin n} {ch : Bool}
    {v : Val n V} {a' : Tag n} (hI : Inv α C Lin) (hpc : (C.loc p).pc = .r37 ch v a')
    (hstep : (impl v₀ pick).step C (.tau p) = some C') :
    ∃ L', Inv (α ++ [.tau p]) C' (Lin ++ L') := by
  have h0 := (Impl.step_tau hstep).1
  have hact : (impl v₀ pick).act p (C.loc p) = .access none .read
      (fun v' => if a' = v.2 ∧ v = v' then (⟨.rRet v'.1 ch, (C.loc p).gs⟩ : Loc n V)
        else ⟨.r34 true, (C.loc p).gs⟩) := by
    simp [impl, implG, actG, hpc]
  rw [Impl.step_tau_eq_some h0 hact] at hstep
  obtain rfl := Option.some.inj hstep
  have hr := hI.rd p
  rw [hpc] at hr
  obtain ⟨hc, hAv, hch, hFX, hav⟩ := hr
  have hmem : Function.update C.mem none (C.mem none) = C.mem := Function.update_eq_self _ _
  rw [show (B n V v₀ none).δ (C.mem none) RWOp.read = (C.mem none, C.mem none) from rfl]
  simp only [hmem]
  by_cases hg : a' = v.2 ∧ v = C.mem none
  · -- the linearization point of the `DRead`
    simp only [hg, and_self, ↓reduceIte]
    obtain ⟨hav2, hvX⟩ := hg
    have hst := hI.st p
    rw [st_iff_of_pendOp (o := .dread p) (by rw [hpc]; rfl)] at hst
    obtain ⟨-, hnot, hop⟩ := hst
    have hXA : (C.mem none).2 = (C.mem (some p)).2 := by rw [← hvX, hAv]
    have hFch : (linState Lin).2 p = ch := by
      cases ch
      · by_contra hF
        simp only [Bool.not_eq_false] at hF
        exact ((hc ⟨rfl, hav2⟩).1 hF) hXA
      · exact hch rfl
    set C' : Cfg n V v₀ := ⟨Function.update C.loc p ⟨.rRet (C.mem none).1 ch, (C.loc p).gs⟩,
      C.pend, C.mem⟩ with hC'
    have hlp : C'.loc p = ⟨.rRet (C.mem none).1 ch, (C.loc p).gs⟩ := Function.update_self _ _ _
    have hlq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => Function.update_of_ne hq _ _
    have hF' : ∀ q, (linState (A := abaObj (Fin n) V v₀) (Lin ++ [(curOp α p, ABAOp.dread p)])).2 q =
        Function.update (linState Lin).2 p false q := by
      intro q; rw [linState_dread]
    refine ⟨[(curOp α p, .dread p)], ⟨(hI.lin.push hop hnot (not_completed_curOp α p)).append_tau p,
      fun q => ?_, by rw [linState_dread]; exact hI.val, fun q => ?_, fun q => ?_, ?_⟩⟩
    · by_cases hq : q = p
      · subst hq
        unfold St; rw [hlp, curOp_append_tau, ObjSpec.respIn_concat_self hnot]
        refine ⟨h0, ?_⟩
        change some ((linState Lin).1, (linState Lin).2 q) = some ((C.mem none).1, ch)
        rw [hI.val, hFch]
      · exact (hI.st q).transfer (hlq q hq) rfl (curOp_append_tau _ _ _)
          (fun _ h => opOf_append_of_eq_some h _)
          (by simp only [List.map_cons, List.map_nil, List.mem_singleton]
              intro h; exact hq (by simpa [curOp] using congrArg Prod.fst h))
    · rw [hF']
      by_cases hq : q = p
      · subst hq
        rw [hlp, Function.update_self]
        exact ⟨fun _ => ⟨fun h => absurd h (by simp), fun h => absurd hXA h⟩, trivial⟩
      · rw [Function.update_of_ne hq, hlq q hq]; exact hI.rd q
    · by_cases hq : q = p
      · subst hq; rw [hlp]; exact (hI.wr q).congr rfl (by rw [hpc]; rfl) rfl
      · rw [hlq q hq]; exact hI.wr q
    · intro q p' s' hcq haq
      have hW : ∀ r, WInv r (C'.loc r) (C.mem none) := by
        intro r
        by_cases hr : r = p
        · subst hr; rw [hlp]; exact (hI.wr r).congr rfl (by rw [hpc]; rfl) rfl
        · rw [hlq r hr]; exact hI.wr r
      by_cases hq : q = p
      · subst hq
        exact protBy_of_wInv (hW p') (hXA.trans haq)
      · rw [hlq q hq] at hcq
        have hold := hI.prot q p' s' hcq haq
        by_cases hp' : p' = p
        · subst hp'; rw [hlp]; exact hold.congr rfl rfl
        · rw [hlq p' hp']; exact hold
  · -- the loop repeats
    simp only [hg, ↓reduceIte]
    have hF : (linState Lin).2 p = true := by
      by_contra hF
      simp only [Bool.not_eq_true] at hF
      have h1 := hFX hF
      have h2 : a' = v.2 := by
        by_contra hne; rw [hav hne] at hF; exact absurd hF (by simp)
      exact hg ⟨h2, h1.symm⟩
    refine ⟨[], ?_⟩
    rw [List.append_nil]
    have := hI.tau_frame C.mem (.r34 true) (fun _ _ => rfl) (by rw [hpc]; rfl) rfl
      (o := .dread p) (by rw [hpc]; rfl) rfl ⟨fun h => absurd h (by simp [CleanPC]), fun _ => hF⟩
      (fun h => absurd h (by simp [CleanPC]))
    exact this

lemma tau_wA (hpick : PickSpec pick) {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀}
    {p : Fin n} {x : V} (hI : Inv α C Lin) (hpc : (C.loc p).pc = .wA x)
    (hstep : (impl v₀ pick).step C (.tau p) = some C') : Inv (α ++ [.tau p]) C' Lin := by
  have h0 := (Impl.step_tau hstep).1
  set g := (C.loc p).gs with hg
  set c := g.c
  have hact : (impl v₀ pick).act p (C.loc p) = .access (some c) .read
      (fun r => (⟨.wX x (getSeq pick p g r.2).1, (getSeq pick p g r.2).2⟩ : Loc n V)) := by
    simp [impl, implG, actG, hpc, g, c]
  rw [Impl.step_tau_eq_some h0 hact] at hstep
  obtain rfl := Option.some.inj hstep
  rw [show (B n V v₀ (some c)).δ (C.mem (some c)) RWOp.read =
    (C.mem (some c), C.mem (some c)) from rfl]
  simp only [Function.update_eq_self]
  set t := (C.mem (some c)).2
  set l' : Loc n V := ⟨.wX x (getSeq pick p g t).1, (getSeq pick p g t).2⟩
  set C' : Cfg n V v₀ := ⟨Function.update C.loc p l', C.pend, C.mem⟩ with hC'
  have hlp : C'.loc p = l' := Function.update_self _ _ _
  have hlq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => Function.update_of_ne hq _ _
  have hw := hI.wr p
  obtain ⟨hlen, -, hXw⟩ := hw
  refine ⟨hI.lin.append_tau p, fun q => ?_, hI.val, fun q => ?_, fun q => ?_, ?_⟩
  · by_cases hq : q = p
    · subst hq
      exact (hI.st q).tau_self (o := .dwrite x) (by rw [hpc]; rfl) (by rw [hlp]; rfl) rfl
    · simpa using (hI.st q).transfer (M := []) (hlq q hq) rfl (curOp_append_tau _ _ _)
        (fun _ h => opOf_append_of_eq_some h _) (by simp)
  · by_cases hq : q = p
    · subst hq
      have hr := hI.rd q
      rw [hpc] at hr
      rw [hlp]; exact ⟨hr.1, trivial⟩
    · rw [hlq q hq]; exact hI.rd q
  · by_cases hq : q = p
    · subst hq
      rw [hlp]
      have hn : 1 ≤ n := q.pos
      have hnot := getSeq_fst_notMem hpick q g t hlen
      refine ⟨List.length_take_le _ _, fun x' s hs => ?_, fun s' hs' => ?_⟩
      · simp only [l', PC.wX.injEq] at hs
        obtain ⟨-, rfl⟩ := hs
        refine ⟨by simp [l', getSeq], fun hm => hnot ?_⟩
        simp only [getSeq, List.take_succ_cons] at hm
        exact mem_excl_of_usedQ (List.mem_of_mem_take hm)
      · have := hXw s' hs'
        simp only [PC.isWX, hpc] at this
        simp only [l', PC.isWX, ↓reduceIte, getSeq, List.getElem?_take]
        rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]
        simpa using this
    · rw [hlq q hq]; exact hI.wr q
  · intro q p' s' hcq haq
    have hcq' : CleanPC (C.loc q).pc := by
      by_cases hq : q = p
      · subst hq; rw [hpc]; trivial
      · rwa [hlq q hq] at hcq
    have hold := hI.prot q p' s' hcq' haq
    by_cases hp' : p' = p
    · subst hp'
      rw [hlp]
      exact protBy_getSeq hpick hold hlen (fun hc => by subst hc; exact haq)
    · rw [hlq p' hp']; exact hold

lemma tau_wX {α : Exec n V v₀} {C C' : Cfg n V v₀} {Lin : LinT n V v₀}
    {p : Fin n} {x : V} {s : Seq n} (hI : Inv α C Lin) (hpc : (C.loc p).pc = .wX x s)
    (hstep : (impl v₀ pick).step C (.tau p) = some C') :
    ∃ L', Inv (α ++ [.tau p]) C' (Lin ++ L') := by
  have h0 := (Impl.step_tau hstep).1
  have hact : (impl v₀ pick).act p (C.loc p) = .access none (.write (x, some (p, s)))
      (fun _ => (⟨.wRet x, (C.loc p).gs⟩ : Loc n V)) := by
    simp [impl, implG, actG, hpc]
  rw [Impl.step_tau_eq_some h0 hact] at hstep
  obtain rfl := Option.some.inj hstep
  rw [show (B n V v₀ none).δ (C.mem none) (RWOp.write (x, some (p, s))) =
    ((x, some (p, s)), (x, some (p, s))) from rfl]
  have hst := hI.st p
  rw [st_iff_of_pendOp (o := .dwrite x) (by rw [hpc]; rfl)] at hst
  obtain ⟨-, hnot, hop⟩ := hst
  set l' : Loc n V := ⟨.wRet x, (C.loc p).gs⟩
  dsimp only
  set C' : Cfg n V v₀ :=
    ⟨Function.update C.loc p l', C.pend, Function.update C.mem none (x, some (p, s))⟩ with hC'
  have hlp : C'.loc p = l' := Function.update_self _ _ _
  have hlq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => Function.update_of_ne hq _ _
  have hmX : C'.mem none = (x, some (p, s)) := by simp [C']
  have hmA : ∀ q, C'.mem (some q) = C.mem (some q) := fun q => by simp [C']
  -- the new tag differs from every clean announcement
  have hne : ∀ q, CleanPC (C.loc q).pc → (some (p, s) : Tag n) ≠ (C.mem (some q)).2 := by
    intro q hc ha
    exact (hI.prot q p s hc ha.symm).1 x s hpc rfl
  have hw := hI.wr p
  obtain ⟨hlen, hwx, -⟩ := hw
  refine ⟨[(curOp α p, .dwrite x)],
    ⟨(hI.lin.push hop hnot (not_completed_curOp α p)).append_tau p, fun q => ?_,
      ?_, fun q => ?_, fun q => ?_, ?_⟩⟩
  · by_cases hq : q = p
    · subst hq
      unfold St; rw [hlp, curOp_append_tau, ObjSpec.respIn_concat_self hnot]
      exact ⟨h0, rfl⟩
    · exact (hI.st q).transfer (hlq q hq) rfl (curOp_append_tau _ _ _)
        (fun _ h => opOf_append_of_eq_some h _)
        (by simp only [List.map_cons, List.map_nil, List.mem_singleton]
            intro h; exact hq (by simpa [curOp] using congrArg Prod.fst h))
  · rw [linState_dwrite, hmX]
  · rw [linState_dwrite, hmX, hmA]
    by_cases hq : q = p
    · subst hq
      rw [hlp]
      exact ⟨fun _ => by simpa using hne q (by rw [hpc]; trivial), trivial⟩
    · rw [hlq q hq]
      exact (hI.rd q).of_true (fun hc => hne q hc)
  · rw [hmX]
    by_cases hq : q = p
    · subst hq
      rw [hlp]
      refine ⟨hlen, fun x' s' h => by simp [l'] at h, fun s' h => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h
      subst h
      simpa [l', PC.isWX] using (hwx x s hpc).1
    · rw [hlq q hq]
      obtain ⟨h1, h2, -⟩ := hI.wr q
      refine ⟨h1, h2, fun s' h => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact absurd h.1.symm hq
  · intro q p' s' hcq haq
    rw [hmA] at haq
    have hcq' : CleanPC (C.loc q).pc := by
      by_cases hq : q = p
      · subst hq; rw [hpc]; trivial
      · rwa [hlq q hq] at hcq
    have hold := hI.prot q p' s' hcq' haq
    by_cases hp' : p' = p
    · subst hp'; rw [hlp]; exact hold.congr rfl rfl
    · rw [hlq p' hp']; exact hold

/-! ## The simulation -/

/-- The invariant is a forward simulation into the atomic ABA-detecting register. -/
theorem linSim (hpick : PickSpec pick) : (impl v₀ pick).LinSim Inv where
  init := initInv
  lin _ _ _ _ h := h.lin
  step := by
    intro α C Lin ℓ C' hrun hI hstep
    cases ℓ with
    | inv p o => exact ⟨[], by rw [List.append_nil]; exact step_inv_inv hrun hI hstep⟩
    | ret p r => exact ⟨[], by rw [List.append_nil]; exact step_ret_inv hI hstep⟩
    | tau p =>
      cases hpc : (C.loc p).pc with
      | wA x => exact ⟨[], by rw [List.append_nil]; exact tau_wA hpick hI hpc hstep⟩
      | wX x s => exact tau_wX hI hpc hstep
      | r34 ch => exact ⟨[], by rw [List.append_nil]; exact tau_r34 hI hpc hstep⟩
      | r35 ch v => exact ⟨[], by rw [List.append_nil]; exact tau_r35 hI hpc hstep⟩
      | r36 ch v a => exact ⟨[], by rw [List.append_nil]; exact tau_r36 hI hpc hstep⟩
      | r37 ch v a => exact tau_r37 hI hpc hstep
      | idle | wRet _ | rRet _ _ =>
        obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hstep
        simp [impl, implG, actG, hpc] at hact

/-- **Theorem 12** (Ovens–Woelfel): Algorithm 2 is a strongly linearizable implementation of an
ABA-detecting register (for every admissible choice `pick` of fresh sequence numbers). -/
theorem stronglyLinearizable (hpick : PickSpec pick) : (impl v₀ pick).StronglyLinearizable :=
  (impl v₀ pick).stronglyLinearizable_of_linSim _ (linSim hpick)

end Podc.StrongLinSnapshots
