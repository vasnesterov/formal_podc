import Papers.PODC2022.RecoverableHarder.Theorem8
import Papers.PODC2022.RecoverableHarder.RuppertNec

/-!
# Ruppert's theorem (Theorem 3), sufficiency

A deterministic readable `n`-discerning type `S` solves wait-free consensus among `n` processes
(with registers). Team consensus (Section 3 of the paper, "conversely, team consensus can be
solved…"): each process writes its input to its team's register, applies its operation to `O`,
reads `O`, determines from its response and the value read which team updated `O` first, and
outputs that team's register. A tournament (`Cslib.SharedMemory.Recoverable.tournament`, crash-free
version) gives consensus.

`discTC` is the team consensus algorithm, `discTC_safe` its safety (crash-free executions, by an
invariant with the ghost list of processes that updated `O`), `theorem3_suff` the result.
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

/-- Program counters of the discerning team consensus algorithm. -/
inductive PCD (S : ObjSpec) where
  | wr
  | op
  | rd (r : S.Resp)
  | rdR (X : Bool)
  | done (w : Bool)

/-- Local states. -/
structure TLD (S : ObjSpec) (k : ℕ) where
  /-- The process. -/
  p : Fin k
  /-- Its input. -/
  v : Bool
  /-- Its program counter. -/
  pc : PCD S

section Disc

variable {S : ObjSpec} (rd : S.Op) {k : ℕ} (π : List Bool) (u : S.State) (team : Fin k → Bool)
  (o : Fin k → S.Op)

/-- `(r, q) ∈ R_{X,j}` of Definition 2. -/
def InR (X : Bool) (j : Fin k) (r : S.Resp) (q : S.State) : Prop :=
  ∃ (σ : List (Fin k)) (m : ℕ) (hm : m < σ.length), σ.Nodup ∧ (∃ h t, σ = h :: t ∧ team h = X) ∧
    σ[m] = j ∧ (S.δ (apply S u o (σ.take m)) (o j)).2 = r ∧ apply S u o σ = q

open Classical in
/-- The team that went first, according to the response `r` of `p`'s operation and the response
`s` of its read of `O`. -/
noncomputable def dside (p : Fin k) (r : S.Resp) (s : S.Resp) : Bool :=
  if ∃ q, (S.δ q rd).2 = s ∧ InR u team o false p r q then false else true

/-- The team consensus algorithm for an `n`-discerning readable type (crash-free model). -/
noncomputable def discTC : Alg k (Obj S) where
  L := TLD S k
  init p x := ⟨p, x, .wr⟩
  act l := match l with
    | ⟨p, v, .wr⟩ => .access (.inl (π, team p)) (RWOp.write (some v)) (fun _ => ⟨p, v, .op⟩)
    | ⟨p, v, .op⟩ => .access (.inr π) (o p) (fun r => ⟨p, v, .rd r⟩)
    | ⟨p, v, .rd r⟩ => .access (.inr π) rd (fun s => ⟨p, v, .rdR (dside rd u team o p r s)⟩)
    | ⟨p, v, .rdR X⟩ => .access (.inl (π, X)) RWOp.read (fun r => ⟨p, v,
        .done ((r : Option Bool).getD false)⟩)
    | ⟨_, _, .done w⟩ => .out w
  mem₀ := mem0 S u

/-- Ranks of program counters. -/
def pcdRank : PCD S → ℕ
  | .wr => 4
  | .op => 3
  | .rd _ => 2
  | .rdR _ => 1
  | .done _ => 0

theorem discTC_ranked : Ranked (discTC rd π u team o) := by
  refine ⟨fun l => pcdRank l.pc, fun l i o' κ r h => ?_⟩
  obtain ⟨p, v, pc⟩ := l
  cases pc with
  | done w => simp [discTC] at h
  | _ => simp only [discTC] at h; cases h; simp [pcdRank]

theorem discTC_footprint :
    ∀ l i o' κ, (discTC rd π u team o).act l = .access i o' κ → nodeFP π i := by
  intro l i o' κ h
  obtain ⟨p, v, pc⟩ := l
  cases pc with
  | done w => simp [discTC] at h
  | rdR X => simp only [discTC] at h; cases h; cases X <;> simp [nodeFP]
  | wr => simp only [discTC] at h; cases h; cases team p <;> simp [nodeFP]
  | _ => simp only [discTC] at h; cases h; simp [nodeFP]

/-- The invariant on views (program counters, registers, object), with the ghost list `L` of the
processes that applied their operation to `O`. -/
structure InvD (x : Fin k → Bool) (pcf : Fin k → PCD S) (R : Bool → Option Bool) (O : S.State)
    (L : List (Fin k)) : Prop where
  regv : ∀ X w, R X = some w → ∀ q, team q = X → x q = w
  wrote : ∀ q, (∀ h : pcf q = .wr, False) → R (team q) ≠ none
  obj : O = apply S u o L
  nodup : L.Nodup
  notin : ∀ q, (pcf q = .wr ∨ pcf q = .op) → q ∉ L
  rd : ∀ q r, pcf q = .rd r → ∃ (m : ℕ) (hm : m < L.length), L[m] = q ∧
    r = (S.δ (apply S u o (L.take m)) (o q)).2
  rdR : ∀ q X, pcf q = .rdR X → L.head?.map team = some X
  done : ∀ q w, pcf q = .done w → ∃ h ∈ L.head?, ∀ q', team q' = team h → x q' = w

variable {rd π u team o}

/-- The value of the first updater's team. -/
def decL (x : Fin k → Bool) (L : List (Fin k)) : Option Bool := L.head?.map x

section Steps

variable {x : Fin k → Bool} {pcf : Fin k → PCD S} {R : Bool → Option Bool} {O : S.State}
  {L : List (Fin k)} {p : Fin k}

lemma InvD.wr (hx : ∀ p q, team p = team q → x p = x q) (hI : InvD u team o x pcf R O L)
    (hp : pcf p = .wr) :
    InvD u team o x (Function.update pcf p .op) (Function.update R (team p) (some (x p))) O L := by
  have hR : ∀ Y, R Y ≠ none → Function.update R (team p) (some (x p)) Y ≠ none := by
    intro Y hY; by_cases h : Y = team p
    · subst h; simp
    · simp [h, hY]
  have hupd : ∀ q, q ≠ p → Function.update pcf p .op q = pcf q := fun q hq => by simp [hq]
  refine ⟨fun X w hw q hq => ?_, fun q hq => ?_, hI.obj, hI.nodup, fun q hq => ?_,
    fun q r hq => ?_, fun q X hq => ?_, fun q w hq => ?_⟩
  · by_cases hX : X = team p
    · subst hX; simp at hw; subst hw; exact hx q p hq
    · simp [hX] at hw; exact hI.regv X w hw q hq
  · by_cases hqp : q = p
    · subst hqp; simp
    · rw [hupd q hqp] at hq; exact hR _ (hI.wrote q hq)
  · by_cases hqp : q = p
    · subst hqp; exact hI.notin q (Or.inl hp)
    · rw [hupd q hqp] at hq; exact hI.notin q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rd q r hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rdR q X hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.done q w hq

lemma head?_append_singleton_of_ne {L : List (Fin k)} (hL : L ≠ []) (p : Fin k) :
    (L ++ [p]).head? = L.head? := by
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hL; simp

lemma InvD.op (hI : InvD u team o x pcf R O L) (hp : pcf p = .op) :
    InvD u team o x (Function.update pcf p (.rd (S.δ O (o p)).2)) R (S.δ O (o p)).1
      (L ++ [p]) := by
  have hpL : p ∉ L := hI.notin p (Or.inr hp)
  have hupd : ∀ q, q ≠ p → Function.update pcf p (.rd (S.δ O (o p)).2) q = pcf q :=
    fun q hq => by simp [hq]
  -- processes at `rdR` or `done` imply `L ≠ []`
  refine ⟨hI.regv, fun q hq => ?_, by rw [apply_append, ← hI.obj]; rfl, ?_, fun q hq => ?_,
    fun q r hq => ?_, fun q X hq => ?_, fun q w hq => ?_⟩
  · by_cases hqp : q = p
    · subst hqp; exact hI.wrote q (by rw [hp]; exact fun h => by cases h)
    · rw [hupd q hqp] at hq; exact hI.wrote q hq
  · rw [List.nodup_append]
    exact ⟨hI.nodup, by simp, fun a ha b hb => by simp at hb; subst hb; rintro rfl; exact hpL ha⟩
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq
      have := hI.notin q hq
      simp [this, hqp]
  · by_cases hqp : q = p
    · subst hqp
      simp at hq; subst hq
      refine ⟨L.length, by simp, by simp, ?_⟩
      rw [List.take_left' rfl, ← hI.obj]
    · rw [hupd q hqp] at hq
      obtain ⟨m, hm, hLm, hr⟩ := hI.rd q r hq
      refine ⟨m, by simp; omega, by rw [List.getElem_append_left hm]; exact hLm, ?_⟩
      rw [List.take_append_of_le_length hm.le]; exact hr
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq
      have h := hI.rdR q X hq
      have hL : L ≠ [] := by rintro rfl; simp at h
      rw [head?_append_singleton_of_ne hL]; exact h
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq
      obtain ⟨h, hh, hw⟩ := hI.done q w hq
      have hL : L ≠ [] := by rintro rfl; simp at hh
      exact ⟨h, by rw [head?_append_singleton_of_ne hL]; exact hh, hw⟩

lemma dside_eq {rd : S.Op} (hinj : Function.Injective fun q => (S.δ q rd).2)
    (hd : DiscCond S u team o) {L : List (Fin k)} (hL : L.Nodup) {m : ℕ} (hm : m < L.length)
    {h : Fin k} {t : List (Fin k)} (hht : L = h :: t) :
    dside rd u team o L[m] (S.δ (apply S u o (L.take m)) (o L[m])).2
      (S.δ (apply S u o L) rd).2 = team h := by
  classical
  have hin : InR u team o (team h) L[m] (S.δ (apply S u o (L.take m)) (o L[m])).2
      (apply S u o L) := ⟨L, m, hm, hL, ⟨h, t, hht, rfl⟩, rfl, rfl, rfl⟩
  unfold dside
  cases hth : team h
  · rw [ite_eq_left ⟨_, rfl, hth ▸ hin⟩]
  · rw [ite_eq_right]
    rintro ⟨q, hq, σ, m', hm', hσ, ⟨h', t', hσht, th'⟩, hσj, hr, hq'⟩
    have hq'' : q = apply S u o L := hinj hq
    subst hq''
    subst hσht hht
    exact hd (h' :: t') (h :: t) _ m' m hm' hm hσ hL (by simp) (by simp) (by simpa using th')
      (by simpa using hth) hσj rfl (by rw [hr, hq'])

lemma InvD.step_rd {rd : S.Op} (hinj : Function.Injective fun q => (S.δ q rd).2)
    (hd : DiscCond S u team o) (hI : InvD u team o x pcf R O L) {r : S.Resp}
    (hp : pcf p = .rd r) :
    InvD u team o x (Function.update pcf p (.rdR (dside rd u team o p r (S.δ O rd).2))) R O L := by
  obtain ⟨m, hm, hLm, hr⟩ := hI.rd p r hp
  have hL : L ≠ [] := by rintro rfl; simp at hm
  obtain ⟨h, t, hht⟩ := List.exists_cons_of_ne_nil hL
  have hside : dside rd u team o p r (S.δ O rd).2 = team h := by
    rw [hr, hI.obj, ← hLm]; exact dside_eq hinj hd hI.nodup hm hht
  have hupd : ∀ q, q ≠ p → Function.update pcf p (.rdR (dside rd u team o p r (S.δ O rd).2)) q =
      pcf q := fun q hq => by simp [hq]
  refine ⟨hI.regv, fun q hq => ?_, hI.obj, hI.nodup, fun q hq => ?_,
    fun q r' hq => ?_, fun q X hq => ?_, fun q w hq => ?_⟩
  · by_cases hqp : q = p
    · subst hqp; exact hI.wrote q (by rw [hp]; exact fun h => by cases h)
    · rw [hupd q hqp] at hq; exact hI.wrote q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.notin q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rd q r' hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq; rw [← hq, hside, hht]; rfl
    · rw [hupd q hqp] at hq; exact hI.rdR q X hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.done q w hq

lemma InvD.step_rdR (hI : InvD u team o x pcf R O L) {X : Bool} (hp : pcf p = .rdR X) :
    ∃ w, R X = some w ∧ InvD u team o x (Function.update pcf p (.done w)) R O L := by
  have h := hI.rdR p X hp
  obtain ⟨h₀, hh, rfl⟩ := Option.map_eq_some_iff.1 h
  have hh0 : h₀ ∈ L := List.mem_of_mem_head? hh
  have hw : R (team h₀) ≠ none := hI.wrote h₀ (fun hwr => hI.notin h₀ (Or.inl hwr) hh0)
  obtain ⟨w, hRw⟩ := Option.ne_none_iff_exists'.1 hw
  have hupd : ∀ q, q ≠ p → Function.update pcf p (.done w) q = pcf q := fun q hq => by simp [hq]
  refine ⟨w, hRw, hI.regv, fun q hq => ?_, hI.obj, hI.nodup, fun q hq => ?_,
    fun q r' hq => ?_, fun q X hq => ?_, fun q w' hq => ?_⟩
  · by_cases hqp : q = p
    · subst hqp; exact hI.wrote q (by rw [hp]; exact fun h => by cases h)
    · rw [hupd q hqp] at hq; exact hI.wrote q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.notin q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rd q r' hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rdR q X hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq; subst hq
      exact ⟨h₀, hh, fun q' hq' => hI.regv _ _ hRw q' hq'⟩
    · rw [hupd q hqp] at hq; exact hI.done q w' hq

end Steps

section Safe

/-- Views of a configuration of `discTC`. -/
def RVd (C : Cfg (discTC rd π u team o)) (X : Bool) : Option Bool := C.mem (.inl (π, X))
def OVd (C : Cfg (discTC rd π u team o)) : S.State := C.mem (.inr π)
def PCd (C : Cfg (discTC rd π u team o)) : Fin k → PCD S := fun q => (C.loc q).pc

/-- The invariant on configurations; the ghost is the list `L` and the decided value. -/
def InvCD (x : Fin k → Bool) (C : Cfg (discTC rd π u team o)) (g : List (Fin k) × Option Bool) :
    Prop :=
  C.inp = x ∧ (∀ q, (C.loc q).p = q ∧ (C.loc q).v = x q) ∧
    InvD u team o x (PCd C) (RVd C) (OVd C) g.1 ∧ g.2 = g.1.head?.map x

lemma pcd_stepP (C : Cfg (discTC rd π u team o)) (p : Fin k) {i : Idx} {o' : (Obj S i).Op}
    {κ : (Obj S i).Resp → TLD S k} (h : (discTC rd π u team o).act (C.loc p) = .access i o' κ) :
    PCd (C.stepP p) = Function.update (PCd C) p (κ ((Obj S i).δ (C.mem i) o').2).pc := by
  funext q
  by_cases hq : q = p
  · subst hq; simp [PCd, stepP_loc_self C h]
  · simp [PCd, stepP_loc_other C hq, hq]

lemma locd_stepP {x : Fin k → Bool} {C : Cfg (discTC rd π u team o)}
    (hl : ∀ q, (C.loc q).p = q ∧ (C.loc q).v = x q) (p : Fin k) {i : Idx} {o' : (Obj S i).Op}
    {κ : (Obj S i).Resp → TLD S k} (h : (discTC rd π u team o).act (C.loc p) = .access i o' κ)
    (hκ : ∀ r, (κ r).p = p ∧ (κ r).v = x p) :
    ∀ q, ((C.stepP p).loc q).p = q ∧ ((C.stepP p).loc q).v = x q := by
  intro q
  by_cases hq : q = p
  · subst hq; rw [stepP_loc_self C h]; exact hκ _
  · rw [stepP_loc_other C hq]; exact hl q

variable (hrd : ∀ q, (S.δ q rd).1 = q) (hinj : Function.Injective fun q => (S.δ q rd).2)
  (hd : DiscCond S u team o)

include hrd hinj hd in
theorem InvCD.stepP {x : Fin k → Bool} (hx : ∀ p q, team p = team q → x p = x q)
    {C : Cfg (discTC rd π u team o)} {g : List (Fin k) × Option Bool} (hI : InvCD x C g)
    (p : Fin k) :
    ∃ g', InvCD x (C.stepP p) g' ∧ ∀ d, g.2 = some d → g'.2 = some d := by
  obtain ⟨hinp0, hloc, hV, hdec⟩ := hI
  have hl : C.loc p = ⟨p, x p, (C.loc p).pc⟩ := by
    obtain ⟨h1, h2⟩ := hloc p
    rcases hl : C.loc p with ⟨p', v', pc'⟩
    rw [hl] at h1 h2; simp only at h1 h2; subst h1 h2; rfl
  have hinp : (C.stepP p).inp = x := by rw [stepP_inp]; exact hinp0
  rcases hpc : (C.loc p).pc with _ | _ | r | X | w
  · -- wr
    rw [hpc] at hl
    have h : (discTC rd π u team o).act (C.loc p) = .access (.inl (π, team p))
        (RWOp.write (some (x p))) (fun _ => ⟨p, x p, .op⟩) := by rw [hl]; rfl
    refine ⟨g, ⟨hinp, locd_stepP hloc p h (fun _ => ⟨rfl, rfl⟩), ?_, hdec⟩, fun d hd => hd⟩
    have hR : RVd (C.stepP p) = Function.update (RVd C) (team p) (some (x p)) := by
      funext X
      by_cases hX : X = team p
      · subst hX; simp only [RVd, Function.update_self]; rw [stepP_mem_self C h]; rfl
      · simp only [RVd, Function.update_of_ne hX]
        rw [stepP_mem_other C h (by simpa using hX)]
    have hO : OVd (C.stepP p) = OVd C := by
      simp only [OVd]; rw [stepP_mem_other C h (by simp)]
    rw [pcd_stepP C p h, hR, hO]
    exact hV.wr hx hpc
  · -- op
    rw [hpc] at hl
    have h : (discTC rd π u team o).act (C.loc p) = .access (.inr π) (o p)
        (fun r => ⟨p, x p, .rd r⟩) := by rw [hl]; rfl
    refine ⟨(g.1 ++ [p], (g.1 ++ [p]).head?.map x),
      ⟨hinp, locd_stepP hloc p h (fun _ => ⟨rfl, rfl⟩), ?_, rfl⟩, fun d hd => ?_⟩
    · have hR : RVd (C.stepP p) = RVd C := by
        funext X; simp only [RVd]; rw [stepP_mem_other C h (by simp)]
      have hO : OVd (C.stepP p) = (S.δ (OVd C) (o p)).1 := by
        simp only [OVd]; rw [stepP_mem_self C h]; rfl
      rw [pcd_stepP C p h, hR, hO]
      exact hV.op hpc
    · rw [hdec] at hd
      have hL : g.1 ≠ [] := by rintro h; simp [h] at hd
      simp only
      rw [head?_append_singleton_of_ne hL]; exact hd
  · -- rd
    rw [hpc] at hl
    have h : (discTC rd π u team o).act (C.loc p) = .access (.inr π) rd
        (fun s => ⟨p, x p, .rdR (dside rd u team o p r s)⟩) := by rw [hl]; rfl
    refine ⟨g, ⟨hinp, locd_stepP hloc p h (fun _ => ⟨rfl, rfl⟩), ?_, hdec⟩, fun d hd => hd⟩
    have hmem : (C.stepP p).mem = C.mem := by
      rw [stepP_mem_of_access C h]
      exact Function.update_eq_self_iff.2 (hrd _)
    have hR : RVd (C.stepP p) = RVd C := by funext X; simp only [RVd]; rw [hmem]
    have hO : OVd (C.stepP p) = OVd C := by simp only [OVd]; rw [hmem]
    rw [pcd_stepP C p h, hR, hO]
    exact hV.step_rd hinj hd hpc
  · -- rdR
    rw [hpc] at hl
    have h : (discTC rd π u team o).act (C.loc p) = .access (.inl (π, X)) RWOp.read
        (fun r => ⟨p, x p, .done ((r : Option Bool).getD false)⟩) := by rw [hl]; rfl
    obtain ⟨w, hw, hV'⟩ := hV.step_rdR hpc
    refine ⟨g, ⟨hinp, locd_stepP hloc p h (fun _ => ⟨rfl, rfl⟩), ?_, hdec⟩, fun d hd => hd⟩
    have hmem : (C.stepP p).mem = C.mem := by
      rw [stepP_mem_of_access C h]
      exact Function.update_eq_self_iff.2 rfl
    have hR : RVd (C.stepP p) = RVd C := by funext X; simp only [RVd]; rw [hmem]
    have hO : OVd (C.stepP p) = OVd C := by simp only [OVd]; rw [hmem]
    rw [pcd_stepP C p h, hR, hO]
    have : (Obj S (.inl (π, X))).δ (C.mem (.inl (π, X))) RWOp.read = (RVd C X, RVd C X) := rfl
    rw [this, hw]
    exact hV'
  · -- done
    rw [hpc] at hl
    have h : C.Out p w := by simp only [Cfg.Out]; rw [hl]; rfl
    rw [stepP_of_out C h]
    exact ⟨g, ⟨hinp0, hloc, hV, hdec⟩, fun d hd => hd⟩

include hrd hinj hd in
/-- The discerning team consensus algorithm is safe in crash-free executions (team-uniform
inputs). -/
theorem discTC_safe :
    Safe (discTC rd π u team o) (fun x => ∀ p q, team p = team q → x p = x q) (AdmB false) := by
  refine safe_of_ghost false _ (fun x C g => InvCD x C g) Prod.snd (fun x _ => ?_)
    (fun x hx C g p hI => hI.stepP hrd hinj hd hx p) (fun h => by cases h)
    (fun x C g p w hI hout => ?_) (fun x _ C g d hI hd => ?_)
  · refine ⟨([], none), rfl, fun q => ⟨rfl, rfl⟩, ?_, rfl⟩
    refine ⟨fun X w hw => by simp [RVd, initCfg, discTC, mem0] at hw,
      fun q hq => absurd rfl hq, by simp [OVd, initCfg, discTC, mem0], by simp,
      fun _ _ => by simp, fun q r hq => by simp [PCd, initCfg, discTC] at hq,
      fun q X hq => by simp [PCd, initCfg, discTC] at hq,
      fun q w hq => by simp [PCd, initCfg, discTC] at hq⟩
  · obtain ⟨-, hloc, hV, hdec⟩ := hI
    have hl : C.loc p = ⟨p, x p, (C.loc p).pc⟩ := by
      obtain ⟨h1, h2⟩ := hloc p
      rcases hl : C.loc p with ⟨p', v', pc'⟩
      rw [hl] at h1 h2; simp only at h1 h2; subst h1 h2; rfl
    simp only [Cfg.Out] at hout
    rw [hl] at hout
    rcases hpc : (C.loc p).pc with _ | _ | r | X | w'
    all_goals rw [hpc] at hout
    all_goals simp [discTC] at hout
    obtain ⟨h₀, hh, hw⟩ := hV.done p w' (by simp [PCd, hpc])
    rw [hdec, Option.mem_def.1 hh, Option.map_some, hw h₀ rfl]
    simpa using hout
  · obtain ⟨-, -, -, hdec⟩ := hI
    rw [hdec] at hd
    obtain ⟨h₀, -, rfl⟩ := Option.map_eq_some_iff.1 hd
    exact ⟨h₀, rfl⟩

end Safe

end Disc

/-! ## Restriction and the tournament -/

theorem DiscCond.comap {S : ObjSpec} {m n : ℕ} {u : S.State} {team : Fin n → Bool}
    {o : Fin n → S.Op} (hd : DiscCond S u team o) (f : Fin m → Fin n) (hf : Function.Injective f) :
    DiscCond S u (team ∘ f) (o ∘ f) := by
  intro σ τ j m₁ m₂ hm hm' hσ hτ hσne hτne tσ tτ hσj hτj heq
  obtain ⟨p, σ', rfl⟩ := List.exists_cons_of_ne_nil hσne
  obtain ⟨q, τ', rfl⟩ := List.exists_cons_of_ne_nil hτne
  refine hd ((p :: σ').map f) ((q :: τ').map f) (f j) m₁ m₂ (by simpa using hm)
    (by simpa using hm') (hσ.map hf) (hτ.map hf) (by simp) (by simp) (by simpa using tσ)
    (by simpa using tτ) (by rw [← hσj]; exact List.getElem_map ..)
    (by rw [← hτj]; exact List.getElem_map ..) ?_
  simp only [Function.comp] at heq
  rw [← List.map_take, ← List.map_take, ← apply_map, ← apply_map, ← apply_map, ← apply_map]
  exact heq

/-- At a node `π`, for any split `kA + kB` with `1 ≤ kA ≤ |A|`, `1 ≤ kB ≤ |B|`, a safe (crash-free)
and ranked team consensus algorithm for a discerning type. -/
theorem exists_discTC {S : ObjSpec} {n : ℕ} {u : S.State} {team : Fin n → Bool}
    {o : Fin n → S.Op} (hd : DiscCond S u team o) {rd : S.Op} (hrd : ∀ q, (S.δ q rd).1 = q)
    (hinj : Function.Injective fun q => (S.δ q rd).2) {kA kB : ℕ}
    (hA : kA ≤ (Finset.univ.filter fun p => team p = false).card)
    (hB : kB ≤ (Finset.univ.filter fun p => team p = true).card) (hkA : 1 ≤ kA) (hkB : 1 ≤ kB)
    (π : List Bool) :
    ∃ TC : Alg (kA + kB) (Obj S), TC.mem₀ = mem0 S u ∧
      (∀ l i o' κ, TC.act l = .access i o' κ → nodeFP π i) ∧ Safe TC SideUniform (AdmB false) ∧
      Ranked TC := by
  classical
  obtain ⟨lA, hlA, hlenA, hmemA⟩ := Finset.exists_nodup_list hA
  obtain ⟨lB, hlB, hlenB, hmemB⟩ := Finset.exists_nodup_list hB
  let fA : Fin kA → Fin n := fun a => lA.get ⟨a, by omega⟩
  let fB : Fin kB → Fin n := fun b => lB.get ⟨b, by omega⟩
  have tA : ∀ a, team (fA a) = false := fun a => by
    have := hmemA _ (List.get_mem lA ⟨a, by omega⟩); simpa [fA] using this
  have tB : ∀ b, team (fB b) = true := fun b => by
    have := hmemB _ (List.get_mem lB ⟨b, by omega⟩); simpa [fB] using this
  have iA : Function.Injective fA := fun a a' e => Fin.ext (by
    have := (List.Nodup.get_inj_iff hlA).1 e; simpa using this)
  have iB : Function.Injective fB := fun b b' e => Fin.ext (by
    have := (List.Nodup.get_inj_iff hlB).1 e; simpa using this)
  let f : Fin (kA + kB) → Fin n := Fin.addCases fA fB
  have hf : Function.Injective f := by
    intro p q e
    induction p using Fin.addCases with
    | left a =>
      induction q using Fin.addCases with
      | left a' => simp [f] at e; rw [iA e]
      | right b' =>
        simp [f] at e; have := tA a; rw [e, tB b'] at this; cases this
    | right b =>
      induction q using Fin.addCases with
      | left a' =>
        simp [f] at e; have := tB b; rw [e, tA a'] at this; cases this
      | right b' => simp [f] at e; rw [iB e]
  have hgood : ∀ x : Fin (kA + kB) → Bool, SideUniform x → ∀ p q, (team ∘ f) p = (team ∘ f) q →
      x p = x q := by
    intro x hx p q hpq
    induction p using Fin.addCases with
    | left a =>
      induction q using Fin.addCases with
      | left a' => exact hx.1 a a'
      | right b' => simp [f, tA, tB] at hpq
    | right b =>
      induction q using Fin.addCases with
      | left a' => simp [f, tA, tB] at hpq
      | right b' => exact hx.2 b b'
  have hd' := hd.comap f hf
  exact ⟨discTC rd π u (team ∘ f) (o ∘ f), rfl, discTC_footprint _ _ _ _ _,
    ⟨fun x hx => (discTC_safe hrd hinj hd').agree x (hgood x hx),
     fun x hx => (discTC_safe hrd hinj hd').valid x (hgood x hx)⟩, discTC_ranked _ _ _ _ _⟩

/-- **Theorem 3 (Ruppert), sufficiency.** A deterministic readable `n`-discerning type, together
with registers, solves wait-free consensus among `n` processes. -/
theorem theorem3_suff {S : ObjSpec} {n : ℕ} (hread : S.Readable) (hdisc : IsDiscerning n S) :
    WFSolvable S n := by
  classical
  obtain ⟨rd, hrd, hinj⟩ := hread
  obtain ⟨u, team, o, ⟨p₀, hp₀⟩, ⟨p₁, hp₁⟩, hd⟩ := isDiscerning_iff.1 hdisc
  set a := (Finset.univ.filter fun p : Fin n => team p = false).card
  set b := (Finset.univ.filter fun p : Fin n => team p = true).card
  have hab : a + b = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun p => team p = false)
    simpa [a, b] using this
  have ha : 1 ≤ a := Finset.card_pos.2 ⟨p₀, by simp [hp₀]⟩
  have hb : 1 ≤ b := Finset.card_pos.2 ⟨p₁, by simp [hp₁]⟩
  have htour := tournament (T := Obj S) false (mem0 S u) subtreeFP nodeFP
    (fun π i hi => by
      rcases hi with rfl | rfl | rfl <;> exact List.prefix_refl π)
    (fun π c i hi => by
      cases i with
      | inl r => exact (List.prefix_append π [c]).trans hi
      | inr r => exact (List.prefix_append π [c]).trans hi)
    (fun π i h1 h2 => by
      cases i with
      | inl r => exact prefix_disj h1 h2
      | inr r => exact prefix_disj h1 h2)
    (fun π c i h1 h2 => by
      rcases h2 with rfl | rfl | rfl
      all_goals
        have := h1.length_le
        simp at this)
    n (by omega) (fun k' h1 h2 => by
      refine ⟨min a (k' - 1), k' - min a (k' - 1), by omega, by omega, by omega, fun π => ?_⟩
      exact exists_discTC hd hrd hinj (by omega) (by omega) (by omega) (by omega) π)
    []
  obtain ⟨A, -, -, hsafe, hranked⟩ := htour
  exact ⟨List Bool × Bool, List Bool, inferInstance, inferInstance, fun _ => Reg,
    fun _ => register_rwLike _ _, A, (solves_admB_false_iff A).1 (hsafe.solves hranked)⟩

/-- **Theorem 3 (Ruppert).** A deterministic readable type solves wait-free consensus among
`n ≥ 2` processes (with registers) iff it is `n`-discerning. -/
theorem theorem3 {S : ObjSpec} {n : ℕ} (hn : 2 ≤ n) (hread : S.Readable) :
    WFSolvable S n ↔ IsDiscerning n S :=
  ⟨isDiscerning_of_wfSolvable hn, theorem3_suff hread⟩

end Podc.RecoverableHarder
