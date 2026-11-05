import Papers.PODC2023.DuraCAS.CInvOther

/-!
# Simulation toolkit: A-level steps and the continuation of a process
-/

set_option linter.unusedSectionVars false

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-! ## A-level steps -/

theorem ecsc_succ {Y : Obj K → Cell V} {ls : Hd P → ℕ} {x : Orph P K V} (h : (Y x.o).1 = x.s) :
    ecsc Y ls x = (Function.update Y x.o (max (ls x.h) x.s + 1, x.v),
      Function.update ls x.h (max (ls x.h) x.s + 1), true) := by
  simp [ecsc, h]

theorem ecsc_fail {Y : Obj K → Cell V} {ls : Hd P → ℕ} {x : Orph P K V} (h : (Y x.o).1 ≠ x.s) :
    ecsc Y ls x = (Y, ls, false) := by
  simp [ecsc, h]

theorem astep_aft {a : AS P K V} {p : P} {r : OpRec K V} {c : Pc V} {b : Bool}
    (hop : (a.ps p).op = some r) (hpc : (a.ps p).pc = .aft c b) :
    AStep a (a.next p (afterCall c b)) :=
  ⟨.step p, ⟨r, hop, fun j h => by rw [hpc] at h; cases h⟩,
    by simp [ALbl.apply, apstep, hop, hpc]⟩

theorem astep_recv {a : AS P K V} {p : P} {r : OpRec K V} {j : Fin 4}
    (hop : (a.ps p).op = some r) (hpc : (a.ps p).pc = .at (.recv j))
    (hor : ∀ x, (a.ps p).orph = some x → x.o ≠ recObj r.k j) :
    AStep a (a.next p (afterCall (.recv j) false)) :=
  ⟨.step p, ⟨r, hop, fun j' h x hx => by rw [hpc] at h; cases h; exact hor x hx⟩,
    by simp [ALbl.apply, apstep, hop, hpc]⟩

theorem astep_sc {a : AS P K V} {p : P} {r : OpRec K V} {c : Pc V} {x : Orph P K V}
    (hop : (a.ps p).op = some r) (hpc : (a.ps p).pc = .at c) (hx : scArgs p r.k r.op c = some x) :
    AStep a { a with Y := (ecsc a.Y a.ls x).1, ls := ((ecsc a.Y a.ls x).2).1,
                       ps := Function.update a.ps p { a.ps p with pc := .aft c ((ecsc a.Y a.ls x).2).2 } } := by
  refine ⟨.step p, ⟨r, hop, fun j h => ?_⟩, ?_⟩
  · rw [hpc] at h; cases h; simp [scArgs] at hx
  · cases c <;> simp [scArgs] at hx <;> simp [ALbl.apply, apstep, hop, hpc, scArgs, hx]

theorem astep_orph {a : AS P K V} {p : P} {x : Orph P K V} (hor : (a.ps p).orph = some x)
    (hs : (a.Y x.o).1 = x.s) :
    AStep a { a with Y := (ecsc a.Y a.ls x).1, ls := ((ecsc a.Y a.ls x).2).1,
                       ps := Function.update a.ps p { a.ps p with orph := none } } :=
  ⟨.orph p, ⟨x, hor, hs⟩, by simp [ALbl.apply, AS.orphEff, hor]⟩

theorem AS.next_setPc (a : AS P K V) (p : P) (pc : APc V) (n : Next V) :
    (a.setPc p pc).next p n = a.next p n := by
  cases n <;> simp [AS.next, AS.setPc]

/-! ## Continuation of a process (`applyNext` / `AS.next`) -/

/-- Before a continuation of `p`: the pending installs of other processes are owned as usual,
those of `p` are orphans of `p`. -/
def OwnPre (m : Mem P K V) (ps : P → PState P K V) (aps : P → APS P K V) (p : P) : Prop :=
  ∀ o g, (m.X o).1 = some g → Pend m o →
    (g.1 ≠ p ∧ Owner m ps aps o g) ∨ (g.1 = p ∧ ∃ x, (aps p).orph = some x ∧ x.o = o)

/-- The continuation `n` is consistent with the orphan of `p`. -/
def NextOK (m : Mem P K V) (p : P) (op : Option (OpRec K V)) (orph : Option (Orph P K V)) :
    Next V → Prop
  | .go pc => pc ≠ .idle ∧ ∀ x, orph = some x → COrphOK m p ⟨pc, none, op⟩ x
  | _ => orph = none

theorem forall_update_PInv {m : Mem P K V} {ls : Hd P → ℕ} {ps : P → PState P K V}
    {aps : P → APS P K V} {p : P} {st : PState P K V} {ap : APS P K V}
    (hp : PInv m ls p st ap) (hq : ∀ q, q ≠ p → PInv m ls q (ps q) (aps q)) :
    ∀ q, PInv m ls q (Function.update ps p st q) (Function.update aps p ap q) := by
  intro q
  by_cases hqp : q = p
  · subst hqp; simpa using hp
  · simpa [Function.update_of_ne hqp] using hq q hqp

theorem inv_applyNext {s : St P K V} {a : AS P K V} {p : P} {m' : Mem P K V} {n : Next V}
    (hY : a.Y = m'.Y) (hh : a.hist = s.hist) (hn : a.nid = s.nid) (hg : CGInv m' a.ls)
    (hq : ∀ q, q ≠ p → PInv m' a.ls q (s.ps q) (a.ps q))
    (hown : OwnPre m' s.ps a.ps p)
    (hop : (a.ps p).op = (s.ps p).op) (hsome : (s.ps p).op.isSome)
    (hnext : NextOK m' p (s.ps p).op (a.ps p).orph n) :
    Inv (applyNext s p m' n) (a.next p n) := by
  -- no pending install of `p` when it has no orphan
  have hfree : (a.ps p).orph = none → ∀ o g, (m'.X o).1 = some g → g.1 = p → ¬ Pend m' o := by
    intro hor o g hx hgp hp
    rcases hown o g hx hp with ⟨h, -⟩ | ⟨-, x, hx', -⟩
    · exact h hgp
    · rw [hor] at hx'; cases hx'
  have hown' : ∀ (ps' : P → PState P K V) (aps' : P → APS P K V),
      (∀ q, q ≠ p → ps' q = s.ps q) → (∀ q, q ≠ p → aps' q = a.ps q) →
      (aps' p).orph = (a.ps p).orph →
      ∀ o g, (m'.X o).1 = some g → Pend m' o → Owner m' ps' aps' o g := by
    intro ps' aps' hps haps hor o g hx hp
    rcases hown o g hx hp with ⟨hgp, hO⟩ | ⟨hgp, x, hx', hxo⟩
    · rcases hO with ⟨f, hf, h⟩ | ⟨x, hx', h⟩
      · exact Or.inl ⟨f, by rw [hps _ hgp]; exact hf, h⟩
      · exact Or.inr ⟨x, by rw [haps _ hgp]; exact hx', h⟩
    · exact Or.inr ⟨x, by rw [hgp, hor]; exact hx', hxo⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
  cases n with
  | go pc =>
    obtain ⟨hne, hor⟩ := hnext
    refine ⟨hY, hh, hn, hg, ?_, ?_⟩
    · apply forall_update_PInv _ hq
      refine ⟨hop, ?_, ?_, ?_, hor, ?_⟩
      · simp [hr, hne]
      · intro _; rfl
      · simp [apcOf]
      · intro f hf; cases hf
    · apply hown' <;> simp [applyNext, AS.next]
      · intro q hq; simp [Function.update_of_ne hq]
      · intro q hq; simp [Function.update_of_ne hq]
  | ret rr =>
    have hor : (a.ps p).orph = none := hnext
    have hdet : m'.det (p, .crit) = a.ls (p, .crit) :=
      hg.detEq _ (fun o hx => hfree hor o _ hx rfl)
    refine ⟨hY, ?_, hn, hg, ?_, ?_⟩
    · simp [applyNext, AS.next, hh, hop, hdet]
    · apply forall_update_PInv _ hq
      refine ⟨rfl, by simp, fun _ => rfl, by simp [apcOf], ?_, ?_⟩
      · intro x hx; simp only at hx; rw [hor] at hx; cases hx
      · intro f hf; cases hf
    · apply hown' <;> simp [applyNext, AS.next, hor]
      · intro q hq; simp [Function.update_of_ne hq]
      · intro q hq; simp [Function.update_of_ne hq]
  | rdone =>
    have hor : (a.ps p).orph = none := hnext
    have hdet : m'.det (p, .crit) = a.ls (p, .crit) :=
      hg.detEq _ (fun o hx => hfree hor o _ hx rfl)
    refine ⟨hY, ?_, hn, hg, ?_, ?_⟩
    · simp [applyNext, AS.next, hh, hop, hdet]
    · apply forall_update_PInv _ hq
      refine ⟨rfl, by simp, fun _ => rfl, by simp [apcOf], ?_, ?_⟩
      · intro x hx; simp only at hx; rw [hor] at hx; cases hx
      · intro f hf; cases hf
    · apply hown' <;> simp [applyNext, AS.next, hor]
      · intro q hq; simp [Function.update_of_ne hq]
      · intro q hq; simp [Function.update_of_ne hq]

theorem afterCall_sc_ne_idle {p : P} {k : K} {op : Op V} {c : Pc V} {x : Orph P K V}
    (hx : scArgs p k op c = some x) (b : Bool) : afterCall c b ≠ .go .idle := by
  cases c <;> simp [scArgs] at hx
  · rename_i i z; cases b <;> cases i <;> simp [afterCall]
  · simp [afterCall]
  · rename_i ret _ _; cases ret <;> simp [afterCall, afterTW]

theorem nextOK_none {m : Mem P K V} {p : P} {op : Option (OpRec K V)} {n : Next V}
    (hn : n ≠ .go .idle) : NextOK m p op none n := by
  cases n with
  | go pc => exact ⟨fun h => hn (by rw [h]), fun x hx => by cases hx⟩
  | ret => rfl
  | rdone => rfl

/-- Return of a DurEC call (lines 12, 21 of DurEC): the A-level steps of the returning process. -/
theorem ret_frame {s : St P K V} {a : AS P K V} {p : P} {m' : Mem P K V} {f : Frame P K V}
    {rr : Bool} {r : OpRec K V}
    (hY : a.Y = m'.Y) (hh : a.hist = s.hist) (hn : a.nid = s.nid) (hg : CGInv m' a.ls)
    (hq : ∀ q, q ≠ p → PInv m' a.ls q (s.ps q) (a.ps q))
    (hown : OwnPre m' s.ps a.ps p)
    (hop : (a.ps p).op = some r) (hsop : (s.ps p).op = some r)
    (hsc : f.kind = .sc → scArgs p r.k r.op (s.ps p).pc = some ⟨f.o, f.h, f.s, f.v⟩)
    (hrecv : f.kind = .recov → ∃ j, (s.ps p).pc = .recv j ∧ f.o = recObj r.k j)
    (hapc : (a.ps p).pc = if f.kind = .sc ∧ rr = true then .aft (s.ps p).pc true
      else .at (s.ps p).pc)
    (hfail : f.kind = .sc → rr = false → (m'.Y f.o).1 ≠ f.s)
    (horsc : f.kind = .sc → (a.ps p).orph = none)
    (horrec : f.kind = .recov → ∀ x, (a.ps p).orph = some x →
      x.o ≠ f.o ∧ COrphOK m' p (s.ps p) x) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧
      Inv (applyNext s p m' (afterCall (s.ps p).pc rr)) a' := by
  have hsome : (s.ps p).op.isSome := by simp [hsop]
  have hop' : (a.ps p).op = (s.ps p).op := by rw [hop, hsop]
  cases hk : f.kind with
  | sc =>
    have hx := hsc hk
    have hor := horsc hk
    have hnext : NextOK m' p (s.ps p).op (a.ps p).orph (afterCall (s.ps p).pc rr) := by
      rw [hor]; exact nextOK_none (afterCall_sc_ne_idle hx rr)
    cases rr with
    | true =>
      simp only [hk, and_self, ite_true] at hapc
      exact ⟨_, Relation.ReflTransGen.single (astep_aft hop hapc),
        inv_applyNext hY hh hn hg hq hown hop' hsome hnext⟩
    | false =>
      simp only [hk, true_and, Bool.false_eq_true, ite_false] at hapc
      have h1 := astep_sc hop hapc hx
      have hfl : (a.Y f.o).1 ≠ f.s := by rw [hY]; exact hfail hk rfl
      rw [ecsc_fail (x := ⟨f.o, f.h, f.s, f.v⟩) hfl] at h1
      change AStep a (a.setPc p (.aft (s.ps p).pc false)) at h1
      have h2 := astep_aft (a := a.setPc p (.aft (s.ps p).pc false)) (p := p) (r := r)
        (c := (s.ps p).pc) (b := false) (by simp [AS.setPc, hop]) (by simp [AS.setPc])
      rw [AS.next_setPc] at h2
      exact ⟨_, Relation.ReflTransGen.single h1 |>.tail h2,
        inv_applyNext hY hh hn hg hq hown hop' hsome hnext⟩
  | recov =>
    obtain ⟨j, hpc, hfo⟩ := hrecv hk
    simp only [hk, reduceCtorEq, false_and, ite_false, hpc] at hapc
    have hac : afterCall (s.ps p).pc rr = afterCall (.recv j) false := by
      rw [hpc]; rfl
    rw [hac]
    refine ⟨_, Relation.ReflTransGen.single (astep_recv hop hapc
      (fun x hx => hfo ▸ (horrec hk x hx).1)), ?_⟩
    apply inv_applyNext hY hh hn hg hq hown hop' hsome
    cases hor : (a.ps p).orph with
    | none =>
      apply nextOK_none
      simp only [afterCall]; split <;> simp
    | some x =>
      obtain ⟨hxo, h1, h2, h3, h4, h5, r', j', hr', hpc', hj⟩ := horrec hk x hor
      rw [hsop] at hr'; cases hr'
      rw [hpc] at hpc'; cases hpc'
      rw [hfo] at hxo
      have hj0 : j.val = 0 ∧ x.o = (r.k, .Z) := by
        rcases hj with ⟨ho, hj⟩ | ⟨ho, hj⟩
        · exfalso; apply hxo; rw [ho]; simp [recObj, hj]
        · refine ⟨?_, ho⟩
          rcases Nat.lt_or_ge j.val 1 with h | h
          · omega
          · exfalso; apply hxo; rw [ho]
            have : j.val = 1 := by omega
            simp [recObj, this]
      have hj' : j = 0 := Fin.ext hj0.1
      subst hj'
      refine ⟨by simp, fun x' hx' => ?_⟩
      cases hx'
      refine ⟨h1, h2, h3, h4, h5, r, ⟨1, by omega⟩, hsop, by simp, Or.inr ⟨hj0.2, ?_⟩⟩
      simp

end Podc.DuraCAS
