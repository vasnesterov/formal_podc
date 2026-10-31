import Papers.PODC2017.MemoryAnonymousCoordination.RenamingLock

/-!
# Figure 3: uniqueness and adaptivity (Theorems 5.2 and 5.3)

The invariant `Inv` (proved for every reachable configuration, `inv_of_run`) says:

* every record `(val, round, history)` — in a register, in a local state or in a collected view —
  is well formed (`TupOK`): its history assigns exactly one winner to each round `1, …, round − 1`
  (`HistOK`), the winners are distinct, participants, different from `val`, and each of them is
  *locked* (`Locked`, see `RenamingLock.lean`) as the winner of its round;
* the owner of a local state does not occur in its history;
* the ghost invariant of a process in the middle of a collect: *if* everything it has read and
  everything it has not yet read is its own record `(p, s)`, then `s.val` is locked as the winner
  of round `s.rd`; in particular a process completing round `r` with preference `v` knows that
  `v` is locked as the winner of round `r`;
* a process returning (or having returned) the name `a` knows (`OutOK`) a well-formed history `H`
  of the rounds `1, …, a − 1` not containing it, and either it is locked as the winner of round
  `a`, or `a = n`.

Since two locks of the same round are for the same identifier, all such histories are equal, so
two processes returning the same name `a` are both winners of round `a` (hence equal), or one of
them returns `n` and then `H` together with both processes gives `n + 1` distinct processes.
Every name `a` is bounded by the number of participants: `H` lists `a − 1` participants other
than the process itself.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Renaming

open Cslib.SharedMemory

variable {P : Type} {m : ℕ} [DecidableEq P]
  {n : ℕ} {S : Sel P m} {π : P → Equiv.Perm (Fin m)}

/-- `q` has invoked the renaming operation in `α`. -/
def Part (α : List (Label P RenObj)) (q : P) : Prop := opsOf α q ≠ []

instance (α : List (Label P RenObj)) : DecidablePred (Part α) :=
  fun q => inferInstanceAs (Decidable (opsOf α q ≠ []))

lemma Part.mono {α : List (Label P RenObj)} (β : List (Label P RenObj)) {q : P} (h : Part α q) :
    Part (α ++ β) q := by
  unfold Part at *; rw [opsOf_append]; simp [h]

/-- The history `H` assigns exactly one winner to each round `1, …, r − 1`, and the winners are
distinct. -/
structure HistOK (H : Finset (P × ℕ)) (r : ℕ) : Prop where
  rds : ∀ u t, (u, t) ∈ H → 1 ≤ t ∧ t < r
  cover : ∀ t, 1 ≤ t → t < r → ∃ u, (u, t) ∈ H
  func : HFun H
  inj : ∀ u t t', (u, t) ∈ H → (u, t') ∈ H → t = t'

variable (n π) in
/-- A well-formed record. -/
structure TupOK (α : List (Label P RenObj)) (C : Cfg P m) (s : St P) : Prop where
  rd : 1 ≤ s.rd
  hist : HistOK s.hist s.rd
  val : ∀ t, (s.val, t) ∉ s.hist
  partVal : Part α s.val
  partHist : ∀ u t, (u, t) ∈ s.hist → Part α u
  locked : ∀ u t, (u, t) ∈ s.hist → Locked π n u t C

variable (n π) in
/-- A register value is the initial value or a well-formed record. -/
def EntOK (α : List (Label P RenObj)) (C : Cfg P m) (e : Option (P × St P)) : Prop :=
  ∀ q s, e = some (q, s) → TupOK n π α C s

variable (n π) in
/-- What a process returning the name `a` knows. -/
def OutOK (α : List (Label P RenObj)) (C : Cfg P m) (p : P) (a : ℕ) : Prop :=
  ∃ H, HistOK H a ∧ 1 ≤ a ∧ (∀ u t, (u, t) ∈ H → Locked π n u t C) ∧
    (∀ u t, (u, t) ∈ H → Part α u) ∧ (∀ t, (p, t) ∉ H) ∧ Part α p ∧
    (Locked π n p a C ∨ a = n)

variable (n π) in
/-- The invariant of a local state of `p`. -/
def LocOK (α : List (Label P RenObj)) (C : Cfg P m) (p : P) : Loc P m → Prop
  | .idle => True
  | .collect s _ view => TupOK n π α C s ∧ (∀ t, (p, t) ∉ s.hist) ∧ Part α p ∧
      ∀ j, EntOK n π α C (view j)
  | .write s _ b => TupOK n π α C s ∧ (∀ t, (p, t) ∉ s.hist) ∧ Part α p ∧
      (b = true → Locked π n s.val s.rd C)
  | .done a => OutOK n π α C p a

variable (n π) in
/-- The safety invariant of Figure 3. -/
structure Inv (α : List (Label P RenObj)) (C : Cfg P m) : Prop where
  idle : ∀ p, C.loc p = .idle → C.pend p = none
  mem : ∀ r, EntOK n π α C (C.mem r)
  loc : ∀ p, LocOK n π α C p (C.loc p)
  ghost : ∀ p s k view s', C.loc p = .collect s k view →
    (∀ j, mixed (π p) k view C.mem j = some (p, s')) → Locked π n s'.val s'.rd C
  out : ∀ p a, outputs α p = some a → OutOK n π α C p a

/-! ### Lifting along a step -/

section lift

variable {α β : List (Label P RenObj)} {C C' : Cfg P m}
  (hex : ∀ u t, Locked π n u t C → Locked π n u t C')

include hex

lemma TupOK.lift {s : St P} (h : TupOK n π α C s) : TupOK n π (α ++ β) C' s :=
  ⟨h.rd, h.hist, h.val, h.partVal.mono β, fun u t hu => (h.partHist u t hu).mono β,
    fun u t hu => hex u t (h.locked u t hu)⟩

lemma EntOK.lift {e : Option (P × St P)} (h : EntOK n π α C e) : EntOK n π (α ++ β) C' e :=
  fun q s he => (h q s he).lift hex

lemma OutOK.lift {p : P} {a : ℕ} (h : OutOK n π α C p a) : OutOK n π (α ++ β) C' p a := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨H, h1, h2, fun u t hu => hex u t (h3 u t hu), fun u t hu => (h4 u t hu).mono β, h5,
    h6.mono β, h7.imp (hex p a) id⟩

lemma LocOK.lift {p : P} {l : Loc P m} (h : LocOK n π α C p l) : LocOK n π (α ++ β) C' p l := by
  cases l with
  | idle => trivial
  | collect s k view =>
    exact ⟨h.1.lift hex, h.2.1, h.2.2.1.mono β, fun j => (h.2.2.2 j).lift hex⟩
  | write s j b =>
    exact ⟨h.1.lift hex, h.2.1, h.2.2.1.mono β, fun hb => hex _ _ (h.2.2.2 hb)⟩
  | done a => exact OutOK.lift hex h

end lift

/-! ### Histories -/

/-- Two well-formed locked histories of the same round are equal. -/
lemma hist_eq (hm : m + 1 = 2 * n) {C : Cfg P m} (hfun : ∀ r, HFun (histOf (C.mem r)))
    {H H' : Finset (P × ℕ)} {r : ℕ} (h : HistOK H r) (h' : HistOK H' r)
    (hl : ∀ u t, (u, t) ∈ H → Locked π n u t C) (hl' : ∀ u t, (u, t) ∈ H' → Locked π n u t C) :
    H = H' := by
  have key : ∀ {H H' : Finset (P × ℕ)}, HistOK H r → HistOK H' r →
      (∀ u t, (u, t) ∈ H → Locked π n u t C) → (∀ u t, (u, t) ∈ H' → Locked π n u t C) →
      H ⊆ H' := by
    intro H H' h h' hl hl' x hx
    obtain ⟨u, t⟩ := x
    obtain ⟨h1, h2⟩ := h.rds u t hx
    obtain ⟨u', hu'⟩ := h'.cover t h1 h2
    rwa [Locked.eq hm hfun (hl u t hx) (hl' u' t hu')]
  exact Finset.Subset.antisymm (key h h' hl hl') (key h' h hl' hl)

lemma histOK_empty : HistOK (∅ : Finset (P × ℕ)) 1 :=
  ⟨by simp, fun t h1 h2 => by omega, by simp [HFun], by simp⟩

lemma histOK_insert {H : Finset (P × ℕ)} {r : ℕ} (h : HistOK H r) (hr : 1 ≤ r) {x : P}
    (hx : ∀ t, (x, t) ∉ H) : HistOK (insert (x, r) H) (r + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u t hu
    rcases Finset.mem_insert.1 hu with hu | hu
    · simp only [Prod.mk.injEq] at hu; omega
    · have := h.rds u t hu; omega
  · intro t h1 h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
    · obtain ⟨u, hu⟩ := h.cover t h1 h2; exact ⟨u, Finset.mem_insert_of_mem hu⟩
    · exact ⟨x, by rw [h2]; exact Finset.mem_insert_self _ _⟩
  · intro u u' t hu hu'
    rcases Finset.mem_insert.1 hu with hu | hu <;> rcases Finset.mem_insert.1 hu' with hu' | hu'
    · simp only [Prod.mk.injEq] at hu hu'; rw [hu.1, hu'.1]
    · simp only [Prod.mk.injEq] at hu; have := h.rds u' t hu'; omega
    · simp only [Prod.mk.injEq] at hu'; have := h.rds u t hu; omega
    · exact h.func u u' t hu hu'
  · intro u t t' hu hu'
    rcases Finset.mem_insert.1 hu with hu | hu <;> rcases Finset.mem_insert.1 hu' with hu' | hu'
    · simp only [Prod.mk.injEq] at hu hu'; rw [hu.2, hu'.2]
    · simp only [Prod.mk.injEq] at hu; rw [hu.1] at hu'; exact absurd hu' (hx t')
    · simp only [Prod.mk.injEq] at hu'; rw [hu'.1] at hu; exact absurd hu (hx t)
    · exact h.inj u t t' hu hu'

lemma histOK_filter {H : Finset (P × ℕ)} {r a : ℕ} (h : HistOK H r) (ha : a < r) :
    HistOK (H.filter fun x => x.2 < a) a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u t hu
    simp only [Finset.mem_filter] at hu
    exact ⟨(h.rds u t hu.1).1, hu.2⟩
  · intro t h1 h2
    obtain ⟨u, hu⟩ := h.cover t h1 (by omega)
    exact ⟨u, Finset.mem_filter.2 ⟨hu, h2⟩⟩
  · intro u u' t hu hu'
    exact h.func u u' t (Finset.mem_filter.1 hu).1 (Finset.mem_filter.1 hu').1
  · intro u t t' hu hu'
    exact h.inj u t t' (Finset.mem_filter.1 hu).1 (Finset.mem_filter.1 hu').1

/-- A well-formed history of round `r` names `r − 1` distinct processes. -/
lemma HistOK.card_ids {H : Finset (P × ℕ)} {r : ℕ} (h : HistOK H r) :
    (H.image Prod.fst).card = r - 1 := by
  have h1 : (H.image Prod.fst).card = H.card :=
    Finset.card_image_of_injOn fun x hx y hy hxy => by
      obtain ⟨u, t⟩ := x; obtain ⟨u', t'⟩ := y
      simp only at hxy; subst hxy
      rw [h.inj u t t' hx hy]
  have h2 : (H.image Prod.snd).card = H.card :=
    Finset.card_image_of_injOn fun x hx y hy hxy => by
      obtain ⟨u, t⟩ := x; obtain ⟨u', t'⟩ := y
      simp only at hxy; subst hxy
      rw [h.func u u' t hx hy]
  have h3 : H.image Prod.snd = Finset.Ico 1 r := by
    ext t
    simp only [Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨u, t'⟩, hu, rfl⟩; exact h.rds u t' hu
    · rintro ⟨h1, h2⟩; obtain ⟨u, hu⟩ := h.cover t h1 h2; exact ⟨(u, t), hu, rfl⟩
  rw [h1, ← h2, h3, Nat.card_Ico]

/-! ### The record written after a collect -/

lemma tupOK_of_view {α : List (Label P RenObj)} {C : Cfg P m}
    {V : Fin m → Option (P × St P)} (hV : ∀ j, EntOK n π α C (V j)) {j : Fin m} {q : P}
    {s : St P} (h : V j = some (q, s)) : TupOK n π α C s := hV j q s h

/-- The record computed after a collect (lines 7–14) is well formed. -/
lemma finish_tupOK (hm : m + 1 = 2 * n) {α : List (Label P RenObj)} {C : Cfg P m}
    (hfun : ∀ r, HFun (histOf (C.mem r))) {p : P} {s : St P} {V : Fin m → Option (P × St P)}
    (hs : TupOK n π α C s) (hV : ∀ j, EntOK n π α C (V j)) :
    TupOK n π α C (adopt n V (catchUp S p s V)) := by
  have hn : 1 ≤ n := by omega
  set s₁ := catchUp S p s V with hs₁
  have h1 : TupOK n π α C s₁ := by
    rcases catchUp_mem S p s V with h | ⟨j, q, hj⟩
    · rw [← hs₁] at h; rw [h]; exact hs
    · exact hV j q _ hj
  rcases adopt_mem hn V s₁ with h | ⟨j, q, e, hj, hval, hrd⟩
  · rw [h]; exact h1
  · have he := hV j q e hj
    have hhist : e.hist = s₁.hist := by
      apply hist_eq hm hfun (r := s₁.rd) (hrd ▸ he.hist) h1.hist he.locked h1.locked
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [adopt_rd]; exact h1.rd
    · rw [adopt_rd, adopt_hist]; exact h1.hist
    · rw [adopt_hist, ← hval, ← hhist]; exact he.val
    · rw [← hval]; exact he.partVal
    · rw [adopt_hist]; exact h1.partHist
    · rw [adopt_hist]; exact h1.locked

lemma finish_owner {p : P} {s : St P} {V : Fin m → Option (P × St P)} (S : Sel P m) (n : ℕ)
    (hret : retName p V = none) (hs : ∀ t, (p, t) ∉ s.hist) :
    ∀ t, (p, t) ∉ (adopt n V (catchUp S p s V)).hist := by
  rw [adopt_hist]
  rcases catchUp_mem S p s V with h | ⟨j, q, hj⟩
  · rw [h]; exact hs
  · intro t ht
    have := retName_none hret j t
    rw [hj] at this; exact this ht

/-- Line 5: a process finding itself in a history returns the round it won. -/
lemma outOK_of_view {α : List (Label P RenObj)} {C : Cfg P m} {p : P}
    {e : Option (P × St P)} (he : EntOK n π α C e) {a : ℕ} (ha : (p, a) ∈ histOf e)
    (hp : Part α p) : OutOK n π α C p a := by
  cases e with
  | none => simp at ha
  | some e =>
    obtain ⟨q, s⟩ := e
    have hs := he q s rfl
    simp only [histOf_some] at ha
    obtain ⟨ha1, ha2⟩ := hs.hist.rds p a ha
    refine ⟨s.hist.filter fun x => x.2 < a, histOK_filter hs.hist ha2, ha1, ?_, ?_, ?_, hp,
      Or.inl (hs.locked p a ha)⟩
    · intro u t hu; exact hs.locked u t (Finset.mem_filter.1 hu).1
    · intro u t hu; exact hs.partHist u t (Finset.mem_filter.1 hu).1
    · intro t ht
      simp only [Finset.mem_filter] at ht
      have := hs.hist.inj p t a ht.1 ha
      omega

/-! ### The ghost invariant at the start of a collect -/

lemma ghost_establish [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n)
    {α : List (Label P RenObj)} {C : Cfg P m}
    (hmemOK : ∀ r, EntOK n π α C (C.mem r)) (hlocOK : ∀ q, LocOK n π α C q (C.loc q))
    {p : P} {s₀ : St P} {k : Fin m} {view : Fin m → Option (P × St P)}
    (hl : C.loc p = .collect s₀ k view) (hk : k.val = 0) {s : St P}
    (hall : ∀ j, C.mem (π p j) = some (p, s)) : Locked π n s.val s.rd C := by
  have hs : TupOK n π α C s := hmemOK (π p k) p s (hall k)
  refine ⟨_, lock_establish hm hcard hl hk hs.rd hall ?_ ?_⟩
  · intro q s' hq hlt
    have hq' := hlocOK q
    have ht : TupOK n π α C s' := by
      cases hlq : C.loc q with
      | idle => rw [hlq] at hq; cases hq
      | done a => rw [hlq] at hq; cases hq
      | collect s'' k'' v'' =>
        rw [hlq] at hq hq'; simp only [stOf_collect, Option.some.injEq] at hq; subst hq
        exact hq'.1
      | write s'' j'' b'' =>
        rw [hlq] at hq hq'; simp only [stOf_write, Option.some.injEq] at hq; subst hq
        exact hq'.1
    obtain ⟨u, hu⟩ := ht.hist.cover s.rd hs.rd hlt
    exact ⟨u, hu, ht.locked u _ hu⟩
  · intro q s' k' view' j hq hlt
    have hq' := hlocOK q
    rw [hq] at hq'
    have hj := hq'.2.2.2 j
    cases hv : view' j with
    | none => rw [hv] at hlt; simp at hlt
    | some e =>
      obtain ⟨q'', e⟩ := e
      have ht := hj q'' e hv
      rw [hv] at hlt; simp only [rdOf_some] at hlt
      obtain ⟨u, hu⟩ := ht.hist.cover s.rd hs.rd hlt
      exact ⟨u, hu, ht.locked u _ hu⟩

/-! ### The invariant -/

lemma inv_init : Inv n π [] (I n S π).initCfg := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p _; rfl
  · intro r q s h; simp [Impl.initCfg, Impl.unnamed, alg] at h
  · intro p; simp [Impl.initCfg, Impl.unnamed, alg, LocOK]
  · intro p s k view s' h; simp [Impl.initCfg, Impl.unnamed, alg] at h
  · intro p a h; simp [outputs] at h

lemma Inv.hfun {α : List (Label P RenObj)} {C : Cfg P m} (hI : Inv n π α C) :
    ∀ r, HFun (histOf (C.mem r)) := by
  intro r
  cases h : C.mem r with
  | none => simp [HFun]
  | some e => obtain ⟨q, s⟩ := e; exact (hI.mem r q s h).hist.func

lemma Inv.hex (hm : m + 1 = 2 * n) (hS : S.OK) {α : List (Label P RenObj)} {C C' : Cfg P m}
    {ℓ : Label P RenObj} (hI : Inv n π α C) (h : (I n S π).step C ℓ = some C') :
    ∀ u t, Locked π n u t C → Locked π n u t C' := by
  intro u t ⟨T, hT⟩
  refine lock_step hm hS hT ?_ h
  intro p s j hl ht
  have := hI.loc p
  rw [hl] at this
  have hL := this.2.2.2 rfl
  rw [ht] at hL
  exact Locked.eq hm hI.hfun hL ⟨T, hT⟩

lemma inv_step [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n) (hS : S.OK)
    {α : List (Label P RenObj)} {C C' : Cfg P m} {ℓ : Label P RenObj}
    (hI : Inv n π α C) (h : (I n S π).step C ℓ = some C') : Inv n π (α ++ [ℓ]) C' := by
  have hm0 := pos_of_hm hm
  have hn1 : 1 ≤ n := by omega
  have hex := hI.hex hm hS h
  have hfun := hI.hfun
  cases ℓ with
  | inv p o =>
    obtain ⟨hpn, hpend, hmem, hloc⟩ := inv_cases h
    have hsc : C'.loc p = .collect ⟨p, 1, ∅⟩ ⟨0, hm0⟩ (fun _ => none) := by
      rw [hloc]; simp [startCollect, hm0]
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    have hpp : Part (α ++ [.inv p o]) p := by
      unfold Part; rw [opsOf_concat]; simp [Label.invOf]
    have hmem' : ∀ r, EntOK n π (α ++ [.inv p o]) C' (C'.mem r) := fun r => by
      rw [hmem]; exact (hI.mem r).lift hex
    have hloc' : ∀ q, LocOK n π (α ++ [.inv p o]) C' q (C'.loc q) := by
      intro q
      by_cases hqp : q = p
      · subst hqp; rw [hsc]
        refine ⟨⟨le_rfl, histOK_empty, by simp, hpp, by simp, by simp⟩, by simp, hpp, ?_⟩
        intro j q' s' h'; cases h'
      · rw [hoth q hqp]; exact (hI.loc q).lift hex
    refine ⟨?_, hmem', hloc', ?_, ?_⟩
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; rw [hsc] at hq; cases hq
      · rw [hpend, Function.update_of_ne hqp]; exact hI.idle q (by rwa [← hoth q hqp])
    · intro q s k view s' hq hall
      by_cases hqp : q = p
      · subst hqp
        rw [hsc] at hq; simp only [Loc.collect.injEq] at hq; obtain ⟨-, rfl, rfl⟩ := hq
        exact ghost_establish hm hcard hmem' hloc' hsc rfl fun i => by
          have := hall i; rwa [mixed_zero _ _ _ _ rfl] at this
      · rw [hoth q hqp] at hq; rw [hmem] at hall; exact hex _ _ (hI.ghost q s k view s' hq hall)
    · intro q a hq; rw [outputs_append_inv] at hq; exact (hI.out q a hq).lift hex
  | ret p r =>
    obtain ⟨hpn, hdone, hpend, hmem, hloc⟩ := ret_cases h
    have hd : C.loc p = .done r := hdone.resolve_right (fun hi => hpn (hI.idle p hi))
    have hsc : C'.loc p = .idle := by rw [hloc]; simp
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    have hout : ∀ q (a : ℕ), outputs (α ++ [.ret p r]) q = some a →
        outputs α q = some a ∨ (q = p ∧ a = r) := by
      intro q a hq
      rw [outputs_concat] at hq
      cases ho : outputs α q with
      | some a' => rw [ho] at hq; exact Or.inl hq
      | none =>
        rw [ho] at hq
        change (Label.ret p r : Label P RenObj).retOf q = some a at hq
        rw [Label.retOf_ret] at hq
        split_ifs at hq with hpq
        · exact Or.inr ⟨hpq.symm, (Option.some.inj hq).symm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; rw [hpend]; simp
      · rw [hpend, Function.update_of_ne hqp]; exact hI.idle q (by rwa [← hoth q hqp])
    · intro r'; rw [hmem]; exact (hI.mem r').lift hex
    · intro q
      by_cases hqp : q = p
      · subst hqp; rw [hsc]; trivial
      · rw [hoth q hqp]; exact (hI.loc q).lift hex
    · intro q s k view s' hq hall
      by_cases hqp : q = p
      · subst hqp; rw [hsc] at hq; cases hq
      · rw [hoth q hqp] at hq; rw [hmem] at hall; exact hex _ _ (hI.ghost q s k view s' hq hall)
    · intro q a hq
      rcases hout q a hq with hq | ⟨rfl, rfl⟩
      · exact (hI.out q a hq).lift hex
      · have := hI.loc q; rw [hd] at this; exact OutOK.lift hex this
  | tau p =>
    obtain ⟨-, hpend, hcase⟩ := tau_cases h
    rcases hcase with ⟨s, k, view, hl, hmem, hloc⟩ | ⟨s, j, b, hl, hmem, hloc⟩
    · -- a read
      have hlv := hI.loc p
      rw [hl] at hlv
      obtain ⟨hsOK, hown, hpp, hvOK⟩ := hlv
      set V := Function.update view k (C.mem (π p k)) with hV
      have hVOK : ∀ i, EntOK n π α C (V i) := by
        intro i; rw [hV, Function.update_apply]; split_ifs
        · exact hI.mem _
        · exact hvOK i
      have hpl : C'.loc p = afterRead n S p s k view (C.mem (π p k)) := by rw [hloc]; simp
      have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hmem' : ∀ r, EntOK n π (α ++ [.tau p]) C' (C'.mem r) := fun r => by
        rw [hmem]; exact (hI.mem r).lift hex
      have hloc' : ∀ q, LocOK n π (α ++ [.tau p]) C' q (C'.loc q) := by
        intro q
        by_cases hqp : q = p
        · subst hqp; rw [hpl]; unfold afterRead
          split_ifs with hk
          · exact ⟨hsOK.lift hex, hown, hpp.mono _, fun i => (hVOK i).lift hex⟩
          · rcases finish_cases n S q s V with ⟨a, ha, i, hi⟩ | ⟨hret, hw⟩
            · rw [ha]; exact (outOK_of_view (hVOK i) hi hpp).lift hex
            · rw [hw]
              refine ⟨(finish_tupOK hm hfun hsOK hVOK).lift hex, finish_owner S n hret hown,
                hpp.mono _, ?_⟩
              intro hb
              simp only [decide_eq_true_eq] at hb
              rw [hV, mixed_last _ _ _ _ hk] at hb
              refine hex _ _ (hI.ghost q s k view _ hl ?_)
              intro i; rw [hb i, hV, mixed_last _ _ _ _ hk]
        · rw [hoth q hqp]; exact (hI.loc q).lift hex
      refine ⟨?_, hmem', hloc', ?_, ?_⟩
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq
          rcases finish_cases n S q s V with ⟨a, ha, -⟩ | ⟨-, hw⟩
          · rw [ha] at hq; cases hq
          · rw [hw] at hq; cases hq
        · rw [hpend]; exact hI.idle q (by rwa [← hoth q hqp])
      · intro q s' k' view' s'' hq hall
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq with hk
          · simp only [Loc.collect.injEq] at hq; obtain ⟨-, rfl, rfl⟩ := hq
            rw [hmem, mixed_read _ _ _ _ hk] at hall
            exact hex _ _ (hI.ghost q s k view s'' hl hall)
          · rcases finish_cases n S q s V with ⟨a, ha, -⟩ | ⟨-, hw⟩
            · rw [ha] at hq; cases hq
            · rw [hw] at hq; cases hq
        · rw [hoth q hqp] at hq; rw [hmem] at hall
          exact hex _ _ (hI.ghost q s' k' view' s'' hq hall)
      · intro q a hq; rw [outputs_append_tau] at hq; exact (hI.out q a hq).lift hex
    · -- a write of `(p, s)`
      have hlv := hI.loc p
      rw [hl] at hlv
      obtain ⟨hsOK, hown, hpp, hlast⟩ := hlv
      have hpl : C'.loc p = afterWrite n p s b := by rw [hloc]; simp
      have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hmem' : ∀ r, EntOK n π (α ++ [.tau p]) C' (C'.mem r) := by
        intro r; rw [hmem, Function.update_apply]; split_ifs
        · intro q s' hq; simp only [Option.some.injEq, Prod.mk.injEq] at hq
          obtain ⟨-, rfl⟩ := hq; exact hsOK.lift hex
        · exact (hI.mem r).lift hex
      have hloc' : ∀ q, LocOK n π (α ++ [.tau p]) C' q (C'.loc q) := by
        intro q
        by_cases hqp : q = p
        · subst hqp; rw [hpl]; unfold afterWrite
          split_ifs with hb hv hrn
          · -- line 18: return the round
            subst hb
            refine ⟨s.hist, hsOK.hist, hsOK.rd, fun u t hu => hex u t (hsOK.locked u t hu),
              fun u t hu => (hsOK.partHist u t hu).mono _, hown, hpp.mono _, Or.inl ?_⟩
            have := hex _ _ (hlast rfl); rwa [hv] at this
          · -- line 22: return `n`
            subst hb
            refine ⟨insert (s.val, s.rd) s.hist, hrn ▸ histOK_insert hsOK.hist hsOK.rd hsOK.val,
              hn1, ?_, ?_, ?_, hpp.mono _, Or.inr rfl⟩
            · intro u t hu
              rcases Finset.mem_insert.1 hu with hu | hu
              · simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu; exact hex _ _ (hlast rfl)
              · exact hex u t (hsOK.locked u t hu)
            · intro u t hu
              rcases Finset.mem_insert.1 hu with hu | hu
              · simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu; exact hsOK.partVal.mono _
              · exact (hsOK.partHist u t hu).mono _
            · intro t ht
              rcases Finset.mem_insert.1 ht with ht | ht
              · simp only [Prod.mk.injEq] at ht; exact hv ht.1.symm
              · exact hown t ht
          · -- lines 19–20, 2: the next round
            subst hb
            rw [startCollect_eq hm0]
            have hown' : ∀ t, (q, t) ∉ (nextRound q s).hist := by
              intro t ht
              rcases Finset.mem_insert.1 ht with ht | ht
              · simp only [Prod.mk.injEq] at ht; exact hv ht.1.symm
              · exact hown t ht
            refine ⟨⟨by simp [nextRound], histOK_insert hsOK.hist hsOK.rd hsOK.val, hown',
              hpp.mono _, ?_, ?_⟩, hown', hpp.mono _, fun i => by intro q' s' h'; cases h'⟩
            · intro u t hu
              rcases Finset.mem_insert.1 hu with hu | hu
              · simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu; exact hsOK.partVal.mono _
              · exact (hsOK.partHist u t hu).mono _
            · intro u t hu
              rcases Finset.mem_insert.1 hu with hu | hu
              · simp only [Prod.mk.injEq] at hu; obtain ⟨rfl, rfl⟩ := hu; exact hex _ _ (hlast rfl)
              · exact hex u t (hsOK.locked u t hu)
          · rw [startCollect_eq hm0]
            exact ⟨hsOK.lift hex, hown, hpp.mono _, fun i => by intro q' s' h'; cases h'⟩
        · rw [hoth q hqp]; exact (hI.loc q).lift hex
      refine ⟨?_, hmem', hloc', ?_, ?_⟩
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterWrite at hq
          split_ifs at hq <;> simp [startCollect, hm0] at hq
        · rw [hpend]; exact hI.idle q (by rwa [← hoth q hqp])
      · intro q s' k' view' s'' hq hall
        by_cases hqp : q = p
        · subst hqp
          have hq' := hq
          rw [hpl] at hq; unfold afterWrite at hq
          have hk : k'.val = 0 := by
            split_ifs at hq <;> simp only [startCollect, hm0, ↓reduceDIte, Loc.collect.injEq] at hq <;> obtain ⟨-, rfl, -⟩ := hq <;> rfl
          exact ghost_establish hm hcard hmem' hloc' hq' hk fun i => by
            have := hall i; rwa [mixed_zero _ _ _ _ hk] at this
        · rw [hoth q hqp] at hq
          refine hex _ _ (hI.ghost q s' k' view' s'' hq fun i => ?_)
          have hi := hall i
          rw [hmem] at hi
          rcases mixed_write (π q) k' view' C.mem (π p j) (some (p, s)) i with h' | ⟨h', -⟩
          · rwa [h'] at hi
          · rw [h'] at hi
            simp only [Option.some.injEq, Prod.mk.injEq] at hi
            exact absurd hi.1.symm hqp
      · intro q a hq; rw [outputs_append_tau] at hq; exact (hI.out q a hq).lift hex

lemma inv_of_run [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n) (hS : S.OK)
    {α : List (Label P RenObj)} {C : Cfg P m} (h : (I n S π).run α = some C) :
    Inv n π α C :=
  Impl.run_induction (Q := fun α C => Inv n π α C) inv_init
    (fun _ _ _ _ _ hI hs => inv_step hm hcard hS hI hs) h

/-! ### Uniqueness and adaptivity -/

lemma participants_eq [Fintype P] (α : List (Label P RenObj)) :
    {q | inputs (A := RenObj) α q ≠ none} = ↑(Finset.univ.filter fun q => Part α q) := by
  ext q
  rw [Finset.coe_filter]
  simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and]
  simp [Part, inputs, List.head?_eq_none_iff]

lemma safe [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n) (hS : S.OK)
    {α : List (Label P RenObj)} {C : Cfg P m} (hC : (I n S π).run α = some C) :
    (adaptiveRenaming P).Δ (inputs α) (outputs α) := by
  have hI : Inv n π α C := inv_of_run hm hcard hS hC
  have hfun := hI.hfun
  refine ⟨?_, ?_⟩
  · intro p q a b hpq ha hb hab
    subst hab
    obtain ⟨H, hH, ha1, hHl, -, hHp, -, hpw⟩ := hI.out p a ha
    obtain ⟨H', hH', -, hHl', -, hHq, -, hqw⟩ := hI.out q a hb
    have hHH := hist_eq hm hfun hH hH' hHl hHl'
    subst hHH
    by_cases hw : Locked π n p a C ∧ Locked π n q a C
    · exact hpq (Locked.eq hm hfun hw.1 hw.2)
    · have han : a = n := by
        rcases hpw with h1 | h1
        · rcases hqw with h2 | h2
          · exact absurd ⟨h1, h2⟩ hw
          · exact h2
        · exact h1
      have hc := hH.card_ids
      have hp' : p ∉ H.image Prod.fst := by
        simp only [Finset.mem_image, not_exists, not_and]
        rintro ⟨u, t⟩ hu rfl; exact hHp t hu
      have hq' : q ∉ insert p (H.image Prod.fst) := by
        simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
        refine ⟨fun h => hpq h.symm, ?_⟩
        rintro ⟨u, t⟩ hu rfl; exact hHq t hu
      have := Finset.card_le_univ (insert q (insert p (H.image Prod.fst)))
      rw [Finset.card_insert_of_notMem hq', Finset.card_insert_of_notMem hp', hc] at this
      omega
  · intro p a ha
    obtain ⟨H, hH, ha1, -, hHpart, hHp, hpp, -⟩ := hI.out p a ha
    refine ⟨ha1, ?_⟩
    rw [participants_eq, Set.ncard_coe_finset]
    have hp' : p ∉ H.image Prod.fst := by
      simp only [Finset.mem_image, not_exists, not_and]
      rintro ⟨u, t⟩ hu rfl; exact hHp t hu
    have hsub : insert p (H.image Prod.fst) ⊆ Finset.univ.filter fun q => Part α q := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_image] at hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hq with rfl | ⟨⟨u, t⟩, hu, rfl⟩
      · exact hpp
      · exact hHpart u t hu
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hp', hH.card_ids] at this
    omega

/-- Uniqueness and adaptivity for `m + 1 = 2n` registers. -/
theorem solves_of_hm [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n)
    (hS : S.OK) : ((alg n S).unnamed π).Solves (adaptiveRenaming P) := fun α hα _ => by
  obtain ⟨C, hC⟩ := hα
  exact safe hm hcard hS hC

end Podc.MemoryAnonymousCoordination.Renaming
