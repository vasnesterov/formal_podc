import Papers.PODC2022.BluntingAdversary.Moves

/-!
# Removing the unused preamble iterations (`O^k` versus `O`)

Fix, for every process, the index `J p` of the preamble iteration that the current invocation of
`p` will use. Then every execution of `P(O^k)` corresponds to an execution of `P(O)`: drop all
iterations except the chosen one, and delay the invocation to the start of the chosen iteration
(paper, proof of Lemma 4.3, `remRedundant`). Since preambles are effect-free (they only apply
read-only primitives), dropping iterations does not change the memory.

`Rel J sk so` relates a configuration `sk` of `P(O^k)` to the configuration `so` of `P(O)`
obtained this way; `InvK` collects invariants of the reachable configurations of `P(O^k)`.
Every move of `P(O^k)` is matched by at most one move of `P(O)` (`step_det`, `step_rand_client`),
except the object random step, which only fixes `J p` (`step_rand_obj`).

The main consequence (`opt_le_avg`): the value of `P(O^k)` is at most the average, over the
uniformly random choices `J`, of the values of `P(O)` from the corresponding configurations. This
is the *correct* way to compare `P(O^k)` with `P(O)`: the object random choices are independent
of everything the adversary can observe before they are made, so they can be sampled in advance;
the paper instead lets the simulating adversary pick the "best" choice afterwards, which is not a
valid (causal) adversary.
-/

set_option linter.unusedSectionVars false

namespace Podc.BluntingAdversary

open Cslib.SharedMemory
open scoped Classical

namespace Removal

variable {P : Type} [DecidableEq P] {A : ObjSpec} {C L : Type} {ι : Type} [DecidableEq ι]
  {Bs : ι → ObjSpec}

/-- Choices of preamble iterations, `0, …, k-1`. -/
abbrev Ch (k : ℕ) := Fin (k - 1 + 1)

/-- The result stored for iteration `j` (as in `iterSem`). -/
def resAt (lk : LK L) (j : ℕ) : L × Bool := lk.res.getD j (lk.cur, false)

/-- The current preamble iteration overlapped a program random step. -/
def curSp (Pi : P → L → Prop) (p : P) (lk : LK L) (coins : ℕ) : Prop :=
  lk.sp = true ∨ (Pi p lk.cur ∧ coins ≠ lk.sc)

/-- The `O`-view `(busy, local state)` of a process of `O^k` whose current invocation will use
iteration `j`. -/
def oview (j : ℕ) (b : Bool) (lk : LK L) : Bool × L :=
  if b then
    match lk.ph with
    | .pre =>
      if j < lk.res.length then (true, (resAt lk j).1)
      else if j = lk.res.length then (true, lk.cur) else (false, lk.prev)
    | .choose => (true, (resAt lk j).1)
    | .tail => (true, lk.cur)
  else (false, lk.cur)

/-- The iteration that `p` will use overlapped (or overlaps) a program random step. -/
def SpoiledJ (Pi : P → L → Prop) (j : ℕ) (p : P) (b : Bool) (lk : LK L) (coins : ℕ) : Prop :=
  b = true ∧
  match lk.ph with
  | .pre => (j < lk.res.length ∧ (resAt lk j).2 = true) ∨ (j = lk.res.length ∧ curSp Pi p lk coins)
  | .choose => (resAt lk j).2 = true
  | .tail => False

variable (Pr : Program P A C) (I : Impl A Bs P L) (Pi : P → L → Prop) (k : ℕ)

/-- Correspondence between `P(O^k)` and `P(O)` for the choices `J`. -/
structure Rel (J : P → Ch k) (sk : Cfg P C (LK L) (Mem Bs)) (so : Cfg P C L (Mem Bs)) : Prop where
  cl : so.cl = sk.cl
  view : ∀ p, (so.busy p, so.lo p) = oview (J p) (sk.busy p) (sk.lo p)
  mem : so.mem = sk.mem
  coins : so.coins = sk.coins
  bad : so.badCoin = true →
    (∃ p, (sk.lo p).xbad = true) ∨ ∃ p, SpoiledJ Pi (J p) p (sk.busy p) (sk.lo p) sk.coins

/-- Invariants of one process of `P(O^k)` (client state `c`, busy flag `b`, local state `lk`). -/
structure InvP (p : P) (c : C) (b : Bool) (lk : LK L) (coins : ℕ) : Prop where
  call : b = true → ∃ o κ, Pr.next p c = .call o κ ∧ lk.base = I.invoke p lk.prev o
  pre_len : b = true → lk.ph = .pre → lk.res.length < k
  choose_len : b = true → lk.ph = .choose → lk.res.length = k
  res_post : b = true → ∀ e ∈ lk.res, ¬ Pi p e.1
  tail_post : b = true → lk.ph = .tail → ¬ Pi p lk.cur
  pre_sp : b = true → lk.ph = .pre → Pi p lk.cur → lk.sp = false
  sc_le : lk.sc ≤ coins

/-- Invariants of the reachable configurations of `P(O^k)`. -/
def InvK (sk : Cfg P C (LK L) (Mem Bs)) : Prop :=
  ∀ p, InvP Pr I Pi k p (sk.cl p) (sk.busy p) (sk.lo p) sk.coins

variable {Pr I Pi k}

lemma InvP.mono {p : P} {c : C} {b : Bool} {lk : LK L} {n n' : ℕ}
    (h : InvP Pr I Pi k p c b lk n) (hn : n ≤ n') : InvP Pr I Pi k p c b lk n' :=
  { h with sc_le := h.sc_le.trans hn }

lemma InvP.idle {p : P} {c : C} {lk : LK L} {n : ℕ} (h : lk.sc ≤ n) :
    InvP Pr I Pi k p c false lk n where
  call h := by simp at h
  pre_len h := by simp at h
  choose_len h := by simp at h
  res_post h := by simp at h
  tail_post h := by simp at h
  pre_sp h := by simp at h
  sc_le := h

lemma rel_init (J : P → Ch k) :
    Rel Pi k J (initCfg Pr (iterSem I Pi k)) (initCfg Pr (implSem I Pi)) where
  cl := rfl
  view p := by simp [initCfg, oview, iterSem, implSem]
  mem := rfl
  coins := rfl
  bad h := by simp [initCfg] at h

lemma invK_init : InvK Pr I Pi k (initCfg Pr (iterSem I Pi k)) :=
  fun p => InvP.idle (by simp [initCfg, iterSem])

/-- Updating one process (and possibly the memory and coin counter) preserves `InvK`. -/
lemma invK_update {sk sk' : Cfg P C (LK L) (Mem Bs)} (hinv : InvK Pr I Pi k sk) (p : P)
    (hcoins : sk.coins ≤ sk'.coins)
    (hq : ∀ q, q ≠ p → sk'.cl q = sk.cl q ∧ sk'.busy q = sk.busy q ∧ sk'.lo q = sk.lo q)
    (hp : InvP Pr I Pi k p (sk'.cl p) (sk'.busy p) (sk'.lo p) sk'.coins) :
    InvK Pr I Pi k sk' := by
  intro q
  by_cases hqp : q = p
  · subst hqp; exact hp
  · obtain ⟨h1, h2, h3⟩ := hq q hqp
    rw [h1, h2, h3]; exact (hinv q).mono hcoins

/-- Updating one process (and possibly the memory) preserves `Rel`, given the view of that
process and the monotonicity of its "spoiled" status. -/
lemma rel_update {J : P → Ch k} {sk sk' : Cfg P C (LK L) (Mem Bs)} {so so' : Cfg P C L (Mem Bs)}
    (hrel : Rel Pi k J sk so) (p : P)
    (hcl : so'.cl = sk'.cl) (hmem : so'.mem = sk'.mem) (hcoins : so'.coins = sk'.coins)
    (hcoins' : sk'.coins = sk.coins) (hbad : so'.badCoin = so.badCoin)
    (hsk : ∀ q, q ≠ p → sk'.busy q = sk.busy q ∧ sk'.lo q = sk.lo q)
    (hso : ∀ q, q ≠ p → so'.busy q = so.busy q ∧ so'.lo q = so.lo q)
    (hview : (so'.busy p, so'.lo p) = oview (J p) (sk'.busy p) (sk'.lo p))
    (hxb : (sk.lo p).xbad = true → (sk'.lo p).xbad = true)
    (hsp : SpoiledJ Pi (J p) p (sk.busy p) (sk.lo p) sk.coins →
      (sk'.lo p).xbad = true ∨ SpoiledJ Pi (J p) p (sk'.busy p) (sk'.lo p) sk'.coins) :
    Rel Pi k J sk' so' where
  cl := hcl
  view q := by
    by_cases hqp : q = p
    · subst hqp; exact hview
    · rw [(hso q hqp).1, (hso q hqp).2, (hsk q hqp).1, (hsk q hqp).2]; exact hrel.view q
  mem := hmem
  coins := hcoins
  bad h := by
    rw [hbad] at h
    rcases hrel.bad h with ⟨q, hq⟩ | ⟨q, hq⟩
    · left
      by_cases hqp : q = p
      · subst hqp; exact ⟨q, hxb hq⟩
      · exact ⟨q, by rw [(hsk q hqp).2]; exact hq⟩
    · by_cases hqp : q = p
      · subst hqp
        rcases hsp hq with h' | h'
        · exact Or.inl ⟨q, h'⟩
        · exact Or.inr ⟨q, h'⟩
      · right; refine ⟨q, ?_⟩
        rw [(hsk q hqp).1, (hsk q hqp).2, hcoins']; exact hq

/-! ### Unfolding the objects -/

section Unfold

variable (I Pi k)

lemma impl_act_access {p : P} {l : L} {m : Mem Bs} {c : ℕ} {i : ι} {o : (Bs i).Op}
    {κ : (Bs i).Resp → L} (ha : I.act p l = .access i o κ) :
    (implSem I Pi).act p l m c =
      .step (κ ((Bs i).δ (m i) o).2) (Function.update m i ((Bs i).δ (m i) o).1) := by
  simp [implSem, ha]

lemma impl_act_ret {p : P} {l : L} {m : Mem Bs} {c : ℕ} {r : A.Resp} {l' : L}
    (ha : I.act p l = .ret r l') : (implSem I Pi).act p l m c = .ret r l' := by
  simp [implSem, ha]

lemma impl_call (p : P) (l : L) (o : A.Op) (m : Mem Bs) (c : ℕ) :
    (implSem I Pi).call p l o m c = .inl (I.invoke p l o, m) := rfl

lemma iter_call (p : P) (lk : LK L) (o : A.Op) (m : Mem Bs) (c : ℕ) :
    (iterSem I Pi k).call p lk o m c =
      .inl (⟨I.invoke p lk.cur o, lk.cur, I.invoke p lk.cur o, .pre, [], c, false, lk.xbad⟩, m) :=
  rfl

variable {I Pi k}

lemma iter_act_pre_access {p : P} {lk : LK L} {m : Mem Bs} {c : ℕ} {i : ι} {o : (Bs i).Op}
    {κ : (Bs i).Resp → L} (hph : lk.ph = .pre) (hpi : Pi p lk.cur)
    (ha : I.act p lk.cur = .access i o κ) :
    (iterSem I Pi k).act p lk m c =
      .step { lk with cur := κ ((Bs i).δ (m i) o).2,
                      sp := if Pi p (κ ((Bs i).δ (m i) o).2) then lk.sp else decide (c ≠ lk.sc) }
        (Function.update m i ((Bs i).δ (m i) o).1) := by
  simp [iterSem, hph, hpi, ha]

lemma iter_act_pre_ret {p : P} {lk : LK L} {m : Mem Bs} {c : ℕ} {r : A.Resp} {l' : L}
    (hph : lk.ph = .pre) (hpi : Pi p lk.cur) (ha : I.act p lk.cur = .ret r l') :
    (iterSem I Pi k).act p lk m c = .step lk m := by
  simp [iterSem, hph, hpi, ha]

lemma iter_act_restart {p : P} {lk : LK L} {m : Mem Bs} {c : ℕ}
    (hph : lk.ph = .pre) (hpi : ¬ Pi p lk.cur) (hlt : lk.res.length + 1 < k) :
    (iterSem I Pi k).act p lk m c =
      .step { lk with cur := lk.base, res := lk.res ++ [(lk.cur, lk.sp)], sc := c, sp := false } m := by
  simp [iterSem, hph, hpi, hlt]

lemma iter_act_tochoose {p : P} {lk : LK L} {m : Mem Bs} {c : ℕ}
    (hph : lk.ph = .pre) (hpi : ¬ Pi p lk.cur) (hlt : ¬ lk.res.length + 1 < k) :
    (iterSem I Pi k).act p lk m c =
      .step { lk with res := lk.res ++ [(lk.cur, lk.sp)], ph := .choose } m := by
  simp [iterSem, hph, hpi, hlt]

lemma iter_act_choose {p : P} {lk : LK L} {m : Mem Bs} {c : ℕ} (hph : lk.ph = .choose) :
    (iterSem I Pi k).act p lk m c =
      .rand (k - 1) fun j => { lk with cur := (resAt lk j).1, ph := .tail,
                                       xbad := lk.xbad || (resAt lk j).2 } := by
  simp [iterSem, hph, resAt]

lemma iter_act_tail_access {p : P} {lk : LK L} {m : Mem Bs} {c : ℕ} {i : ι} {o : (Bs i).Op}
    {κ : (Bs i).Resp → L} (hph : lk.ph = .tail) (ha : I.act p lk.cur = .access i o κ) :
    (iterSem I Pi k).act p lk m c =
      .step { lk with cur := κ ((Bs i).δ (m i) o).2 } (Function.update m i ((Bs i).δ (m i) o).1) := by
  simp [iterSem, hph, ha]

lemma iter_act_tail_ret {p : P} {lk : LK L} {m : Mem Bs} {c : ℕ} {r : A.Resp} {l' : L}
    (hph : lk.ph = .tail) (ha : I.act p lk.cur = .ret r l') :
    (iterSem I Pi k).act p lk m c = .ret r { lk with cur := l' } := by
  simp [iterSem, hph, ha]

end Unfold

/-! ### Simulation of one move -/

section Step

lemma resAt_of_lt {lk : LK L} {j : ℕ} (h : j < lk.res.length) : resAt lk j = lk.res[j] := by
  simp [resAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma resAt_mem {lk : LK L} {j : ℕ} (h : j < lk.res.length) : resAt lk j ∈ lk.res := by
  rw [resAt_of_lt h]; exact List.getElem_mem h

theorem step_det_idle (hk : 1 ≤ k)
    {J : P → Ch k} {sk sk' : Cfg P C (LK L) (Mem Bs)} {so : Cfg P C L (Mem Bs)} {p : P}
    (hinv : InvK Pr I Pi k sk) (hrel : Rel Pi k J sk so) (hb : sk.busy p = false)
    (hm : (sys Pr (iterSem I Pi k)).move sk p = .det sk') :
    InvK Pr I Pi k sk' ∧ ∃ so', Rel Pi k J sk' so' ∧
      (so' = so ∨ (sys Pr (implSem I Pi)).move so p = .det so') := by
  have hv := hrel.view p
  simp only [hb, oview, Bool.false_eq_true, ite_false, Prod.mk.injEq] at hv
  obtain ⟨hob, hol⟩ := hv
  have hcl : so.cl p = sk.cl p := by rw [hrel.cl]
  have hsp0 : ¬ SpoiledJ Pi (J p) p (sk.busy p) (sk.lo p) sk.coins := by simp [SpoiledJ, hb]
  cases hn : Pr.next p (sk.cl p) with
  | loc c =>
    rw [move_loc Pr _ sk p hb hn] at hm; cases hm
    refine ⟨invK_update hinv p le_rfl (fun q hq => by simp [Function.update_of_ne hq])
      (by simpa [hb] using
        (InvP.idle (hinv p).sc_le : InvP Pr I Pi k p c false (sk.lo p) sk.coins)),
      _, ?_, Or.inr (move_loc Pr _ so p hob (hcl ▸ hn))⟩
    exact rel_update hrel p (by simp [hrel.cl]) hrel.mem hrel.coins rfl rfl
      (fun q _ => ⟨rfl, rfl⟩) (fun q _ => ⟨rfl, rfl⟩) (hrel.view p) id (fun h => absurd h hsp0)
  | rnd m g => rw [move_rnd Pr _ sk p hb hn] at hm; cases hm
  | done => rw [move_done Pr _ sk p hb hn] at hm; cases hm
  | call o κ =>
    rw [move_call_inl Pr _ sk p hb hn (iter_call I Pi k p (sk.lo p) o sk.mem sk.coins)] at hm
    cases hm
    refine ⟨invK_update hinv p le_rfl (fun q hq => by simp [Function.update_of_ne hq]) ?_, ?_⟩
    · refine ⟨fun _ => ⟨o, κ, by simpa using hn, by simp⟩, fun _ _ => by simp; omega,
        fun _ h => by simp at h, fun _ => by simp, fun _ h => by simp at h,
        fun _ _ _ => by simp, by simp⟩
    · by_cases hJ : (J p : ℕ) = 0
      · refine ⟨{ so with busy := Function.update so.busy p true,
                          lo := Function.update so.lo p (I.invoke p (so.lo p) o) }, ?_, Or.inr ?_⟩
        · refine rel_update hrel p (by simp [hrel.cl]) hrel.mem hrel.coins rfl rfl
            (fun q hq => by simp [Function.update_of_ne hq])
            (fun q hq => by simp [Function.update_of_ne hq]) ?_ (by simp) (fun h => absurd h hsp0)
          simp [oview, hJ, hol]
        · simpa using move_call_inl Pr (implSem I Pi) so p hob (hcl ▸ hn)
            (impl_call I Pi p (so.lo p) o so.mem so.coins)
      · refine ⟨so, ?_, Or.inl rfl⟩
        refine rel_update hrel p (by simp [hrel.cl]) hrel.mem hrel.coins rfl rfl
          (fun q hq => by simp [Function.update_of_ne hq]) (fun q _ => ⟨rfl, rfl⟩) ?_ (by simp)
          (fun h => absurd h hsp0)
        simp [oview, hJ, hol, hob]


theorem step_det_busy (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi)
    {J : P → Ch k} {sk sk' : Cfg P C (LK L) (Mem Bs)} {so : Cfg P C L (Mem Bs)} {p : P}
    (hinv : InvK Pr I Pi k sk) (hrel : Rel Pi k J sk so) (hb : sk.busy p = true)
    (hm : (sys Pr (iterSem I Pi k)).move sk p = .det sk') :
    InvK Pr I Pi k sk' ∧ ∃ so', Rel Pi k J sk' so' ∧
      (so' = so ∨ (sys Pr (implSem I Pi)).move so p = .det so') := by
  obtain ⟨o, κ, hn, hbase⟩ := (hinv p).call hb
  have hv := hrel.view p
  have hcl : so.cl p = sk.cl p := by rw [hrel.cl]
  have hip := hinv p
  cases hph : (sk.lo p).ph with
  | choose => rw [move_orand Pr _ sk p hb (iter_act_choose hph)] at hm; cases hm
  | tail =>
    simp only [hb, oview, hph, ite_true, Prod.mk.injEq] at hv
    obtain ⟨hob, hol⟩ := hv
    have hpost := hip.tail_post hb hph
    cases ha : I.act p (sk.lo p).cur with
    | access i o' κ' =>
      rw [move_step Pr _ sk p hb (iter_act_tail_access hph ha)] at hm; cases hm
      refine ⟨invK_update hinv p le_rfl (fun q hq => by simp [Function.update_of_ne hq])
        ⟨fun _ => ⟨o, κ, by simpa using hn, by simpa using hbase⟩, fun _ h => by simp [hph] at h,
          fun _ h => by simp [hph] at h, fun _ => by simpa using hip.res_post hb,
          fun _ _ => by simpa using hWF.stay p _ i o' κ' _ hpost ha, fun _ h => by simp [hph] at h,
          by simpa using hip.sc_le⟩, ?_⟩
      refine ⟨{ so with lo := Function.update so.lo p (κ' ((Bs i).δ (so.mem i) o').2),
                        mem := Function.update so.mem i ((Bs i).δ (so.mem i) o').1 }, ?_, Or.inr ?_⟩
      · refine rel_update hrel p (by simp [hrel.cl]) (by simp [hrel.mem]) (by simp [hrel.coins]) rfl rfl
          (fun q hq => by simp [Function.update_of_ne hq])
          (fun q hq => by simp [Function.update_of_ne hq]) ?_ (by simp) ?_
        · simp [oview, hb, hph, hrel.mem, hob]
        · intro h; simp [SpoiledJ, hph] at h
      · exact move_step Pr _ so p hob (by rw [hol]; exact impl_act_access I Pi ha)
    | ret r l' =>
      rw [move_ret Pr _ sk p hb (iter_act_tail_ret hph ha) hn] at hm; cases hm
      refine ⟨invK_update hinv p le_rfl (fun q hq => by simp [Function.update_of_ne hq])
        (by simpa using (InvP.idle hip.sc_le :
          InvP Pr I Pi k p (κ r) false { sk.lo p with cur := l' } sk.coins)), ?_⟩
      refine ⟨{ so with cl := Function.update so.cl p (κ r), busy := Function.update so.busy p false,
                        lo := Function.update so.lo p l' }, ?_, Or.inr ?_⟩
      · refine rel_update hrel p (by simp [hrel.cl]) hrel.mem hrel.coins rfl rfl
          (fun q hq => by simp [Function.update_of_ne hq])
          (fun q hq => by simp [Function.update_of_ne hq]) ?_ (by simp) ?_
        · simp [oview]
        · intro h; simp [SpoiledJ, hph] at h
      · exact move_ret Pr _ so p hob (by rw [hol]; exact impl_act_ret I Pi ha) (hcl ▸ hn)
  | pre =>
    have hlen := hip.pre_len hb hph
    by_cases hpi : Pi p (sk.lo p).cur
    · have hsp := hip.pre_sp hb hph hpi
      cases ha : I.act p (sk.lo p).cur with
      | ret r l' =>
        rw [move_step Pr _ sk p hb (iter_act_pre_ret hph hpi ha)] at hm; cases hm
        refine ⟨?_, so, ?_, Or.inl rfl⟩
        · have : ({ sk with lo := Function.update sk.lo p (sk.lo p), mem := sk.mem } :
              Cfg P C (LK L) (Mem Bs)) = sk := by simp
          rw [this]; exact hinv
        · have : ({ sk with lo := Function.update sk.lo p (sk.lo p), mem := sk.mem } :
              Cfg P C (LK L) (Mem Bs)) = sk := by simp
          rw [this]; exact hrel
      | access i o' κ' =>
        have hro : ((Bs i).δ (sk.mem i) o').1 = sk.mem i := hEF p _ i o' κ' hpi ha (sk.mem i)
        rw [move_step Pr _ sk p hb (iter_act_pre_access hph hpi ha), hro,
          Function.update_eq_self] at hm
        cases hm
        set l1 := κ' ((Bs i).δ (sk.mem i) o').2 with hl1
        refine ⟨invK_update hinv p le_rfl (fun q hq => by simp [Function.update_of_ne hq])
          ⟨fun _ => ⟨o, κ, by simpa using hn, by simpa using hbase⟩, fun _ _ => by simpa using hlen,
            fun _ h => by simp [hph] at h, fun _ => by simpa using hip.res_post hb,
            fun _ h => by simp [hph] at h, fun _ _ h1 => by simp_all,
            by simpa using hip.sc_le⟩, ?_⟩
        by_cases hJ : (J p : ℕ) = (sk.lo p).res.length
        · simp only [hb, oview, hph, hJ, lt_irrefl, ite_false, ite_true, Prod.mk.injEq] at hv
          obtain ⟨hob, hol⟩ := hv
          refine ⟨{ so with lo := Function.update so.lo p (κ' ((Bs i).δ (so.mem i) o').2),
                            mem := Function.update so.mem i ((Bs i).δ (so.mem i) o').1 }, ?_, Or.inr ?_⟩
          · refine rel_update hrel p (by simp [hrel.cl])
              (by rw [hrel.mem, hro]; simp) (by simp [hrel.coins]) rfl rfl
              (fun q hq => by simp [Function.update_of_ne hq])
              (fun q hq => by simp [Function.update_of_ne hq]) ?_ (by simp) ?_
            · simp [oview, hb, hph, hJ, hrel.mem, hl1, hob]
            · intro h
              right
              simp only [SpoiledJ, hb, hph, hJ, lt_irrefl, false_and, true_and, false_or, curSp] at h
              simp only [SpoiledJ, hb, hph, hJ, lt_irrefl, false_and, true_and, false_or, curSp,
                Function.update_self]
              rcases h with h | h
              · simp [hsp] at h
              · by_cases hpi' : Pi p l1
                · simp [hpi', hsp, h.2]
                · simp [hpi', h.2]
          · exact move_step Pr _ so p hob (by rw [hol]; exact impl_act_access I Pi ha)
        · refine ⟨so, ?_, Or.inl rfl⟩
          refine rel_update hrel p hrel.cl (by rw [hrel.mem]) hrel.coins rfl rfl
            (fun q hq => by simp [Function.update_of_ne hq]) (fun q _ => ⟨rfl, rfl⟩) ?_ (by simp) ?_
          · rw [hv]
            rcases lt_or_gt_of_ne hJ with hlt | hgt
            · simp [oview, hb, hph, hlt, resAt, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem hlt]
            · simp [oview, hb, hph, hJ, not_lt.mpr hgt.le]
          · intro h
            right
            rcases lt_or_gt_of_ne hJ with hlt | hgt
            · simp only [SpoiledJ, hb, hph, hlt, true_and, hJ, false_and, or_false] at h
              simp only [SpoiledJ, hb, hph, Function.update_self, true_and]
              left
              refine ⟨by simpa using hlt, ?_⟩
              rw [resAt_of_lt (by simpa using hlt)]
              rw [resAt_of_lt hlt] at h
              simpa using h
            · simp [SpoiledJ, hph, hJ, not_lt.mpr hgt.le] at h
    · by_cases hlt : (sk.lo p).res.length + 1 < k
      · rw [move_step Pr _ sk p hb (iter_act_restart hph hpi hlt)] at hm; cases hm
        refine ⟨invK_update hinv p le_rfl (fun q hq => by simp [Function.update_of_ne hq])
          ⟨fun _ => ⟨o, κ, by simpa using hn, by simpa [] using hbase⟩,
            fun _ _ => by simpa [] using hlt, fun _ h => by simp [hph] at h,
            fun _ e he => ?_, fun _ h => by simp [hph] at h, fun _ _ _ => by simp [],
            by simp []⟩, ?_⟩
        · simp only [Function.update_self, List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hip.res_post hb e he
          · exact hpi
        by_cases hJ : (J p : ℕ) = (sk.lo p).res.length + 1
        · simp only [hb, oview, hph, hJ, ite_true, Prod.mk.injEq] at hv
          have hv' : so.busy p = false ∧ so.lo p = (sk.lo p).prev := by
            simpa [show ¬ (sk.lo p).res.length + 1 < (sk.lo p).res.length by omega] using hv
          obtain ⟨hob, hol⟩ := hv'
          refine ⟨{ so with busy := Function.update so.busy p true,
                            lo := Function.update so.lo p (I.invoke p (so.lo p) o) }, ?_, Or.inr ?_⟩
          · refine rel_update hrel p (by simp [hrel.cl]) (by simp [hrel.mem]) (by simp [hrel.coins])
              rfl rfl (fun q hq => by simp [Function.update_of_ne hq])
              (fun q hq => by simp [Function.update_of_ne hq]) ?_ (by simp []) ?_
            · simp [oview, hb, hph, hJ, hol, hbase]
            · intro h; simp [SpoiledJ, hph, hJ] at h
          · simpa using move_call_inl Pr (implSem I Pi) so p hob (hcl ▸ hn)
              (impl_call I Pi p (so.lo p) o so.mem so.coins)
        · refine ⟨so, ?_, Or.inl rfl⟩
          refine rel_update hrel p hrel.cl (by rw [hrel.mem]) hrel.coins rfl rfl
            (fun q hq => by simp [Function.update_of_ne hq]) (fun q _ => ⟨rfl, rfl⟩) ?_
            (by simp []) ?_
          · rw [hv]
            rcases lt_trichotomy (J p : ℕ) (sk.lo p).res.length with hl | he | hg
            · have h1 : (J p : ℕ) < (sk.lo p).res.length + 1 := by omega
              simp [oview, hb, hph, hl, h1, resAt, List.getD_eq_getElem?_getD,
                List.getElem?_append_left hl]
            · simp [oview, hb, hph, he, resAt, List.getD_eq_getElem?_getD]
            · have h1 : ¬ (J p : ℕ) < (sk.lo p).res.length + 1 := by omega
              simp [oview, hb, hph, h1, hJ, not_lt.mpr hg.le, (Nat.ne_of_gt hg)]
          · intro h
            right
            simp only [SpoiledJ, hb, hph, true_and] at h
            simp only [SpoiledJ, hb, hph, Function.update_self, true_and, List.length_append,
              List.length_singleton]
            rcases h with ⟨hl, h⟩ | ⟨he, h⟩
            · left
              refine ⟨by omega, ?_⟩
              simp only [resAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hl,
                List.getElem?_eq_getElem hl, Option.getD_some] at h ⊢
              exact h
            · left
              refine ⟨by omega, ?_⟩
              simp only [curSp, hpi, false_and, or_false] at h
              simp [resAt, List.getD_eq_getElem?_getD, he, h]
      · rw [move_step Pr _ sk p hb (iter_act_tochoose hph hpi hlt)] at hm; cases hm
        have hk' : (sk.lo p).res.length + 1 = k := by omega
        refine ⟨invK_update hinv p le_rfl (fun q hq => by simp [Function.update_of_ne hq])
          ⟨fun _ => ⟨o, κ, by simpa using hn, by simpa using hbase⟩, fun _ h => by simp at h,
            fun _ _ => by simpa using hk', fun _ e he => ?_, fun _ h => by simp at h,
            fun _ h => by simp at h, by simpa using hip.sc_le⟩, ?_⟩
        · simp only [Function.update_self, List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hip.res_post hb e he
          · exact hpi
        have hJlt : (J p : ℕ) < (sk.lo p).res.length + 1 := by
          have := (J p).isLt; omega
        refine ⟨so, ?_, Or.inl rfl⟩
        refine rel_update hrel p hrel.cl (by rw [hrel.mem]) hrel.coins rfl rfl
          (fun q hq => by simp [Function.update_of_ne hq]) (fun q _ => ⟨rfl, rfl⟩) ?_ (by simp) ?_
        · rw [hv]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hJlt with hl | he
          · simp [oview, hb, hph, hl, resAt, List.getD_eq_getElem?_getD,
              List.getElem?_append_left hl]
          · simp [oview, hb, hph, he, resAt, List.getD_eq_getElem?_getD]
        · intro h
          right
          simp only [SpoiledJ, hb, hph, true_and] at h
          simp only [SpoiledJ, hb, Function.update_self, true_and]
          rcases h with ⟨hl, h⟩ | ⟨he, h⟩
          · simp only [resAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hl] at h ⊢
            exact h
          · simp only [curSp, hpi, false_and, or_false] at h
            simp [resAt, List.getD_eq_getElem?_getD, he, h]

lemma spoiledJ_coins_succ {j : ℕ} {p : P} {b : Bool} {lk : LK L} {n : ℕ} (hsc : lk.sc ≤ n)
    (h : SpoiledJ Pi j p b lk n) : SpoiledJ Pi j p b lk (n + 1) := by
  obtain ⟨hb, h⟩ := h
  refine ⟨hb, ?_⟩
  cases hph : lk.ph <;> simp only [hph] at h ⊢
  · rcases h with h | ⟨hj, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨hj, ?_⟩
      rcases h with h | ⟨hpi, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨hpi, by omega⟩
  · exact h

/-- A program random step of `P(O^k)` is matched by the same step of `P(O)`. -/
theorem step_rand_client (hk : 1 ≤ k)
    {J : P → Ch k} {sk : Cfg P C (LK L) (Mem Bs)} {so : Cfg P C L (Mem Bs)} {p : P} {m : ℕ}
    {g : Fin (m + 1) → Cfg P C (LK L) (Mem Bs)}
    (hinv : InvK Pr I Pi k sk) (hrel : Rel Pi k J sk so) (hb : sk.busy p = false)
    (hm : (sys Pr (iterSem I Pi k)).move sk p = .rand m g) :
    ∃ g' : Fin (m + 1) → Cfg P C L (Mem Bs), (sys Pr (implSem I Pi)).move so p = .rand m g' ∧
      ∀ i, InvK Pr I Pi k (g i) ∧ Rel Pi k J (g i) (g' i) := by
  have hv := hrel.view p
  simp only [hb, oview, Bool.false_eq_true, ite_false, Prod.mk.injEq] at hv
  obtain ⟨hob, hol⟩ := hv
  have hcl : so.cl p = sk.cl p := by rw [hrel.cl]
  cases hn : Pr.next p (sk.cl p) with
  | loc c => rw [move_loc Pr _ sk p hb hn] at hm; cases hm
  | done => rw [move_done Pr _ sk p hb hn] at hm; cases hm
  | call o κ =>
    rw [move_call_inl Pr _ sk p hb hn (iter_call I Pi k p (sk.lo p) o sk.mem sk.coins)] at hm
    cases hm
  | rnd m' g0 =>
    rw [move_rnd Pr _ sk p hb hn] at hm
    cases hm
    refine ⟨_, move_rnd Pr _ so p hob (hcl ▸ hn), fun i => ⟨?_, ?_⟩⟩
    · refine invK_update hinv p (by simp) (fun q hq => by simp [Function.update_of_ne hq]) ?_
      simpa [hb] using (InvP.idle (Nat.le_succ_of_le (hinv p).sc_le) :
        InvP Pr I Pi k p (g0 i) false (sk.lo p) (sk.coins + 1))
    · refine ⟨by simp [hrel.cl], hrel.view, hrel.mem, by simp [hrel.coins], fun hbad => ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hbad
      rcases hbad with hbad | ⟨q, hqb, hqpi⟩
      · rcases hrel.bad hbad with h | ⟨q, hq⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, spoiledJ_coins_succ ((hinv q).sc_le) hq⟩
      · right
        refine ⟨q, ?_⟩
        have hvq := hrel.view q
        have hiq := hinv q
        cases hbq : sk.busy q
        · simp [oview, hbq] at hvq; simp [hvq.1] at hqb
        · have hsc := hiq.sc_le
          refine ⟨rfl, ?_⟩
          cases hph : (sk.lo q).ph with
          | pre =>
            simp only [oview, hbq, hph, ite_true] at hvq
            by_cases hl : (J q : ℕ) < (sk.lo q).res.length
            · simp only [hl, ite_true, Prod.mk.injEq] at hvq
              rw [hvq.2] at hqpi
              exact absurd hqpi (hiq.res_post hbq _ (resAt_mem hl))
            · by_cases he : (J q : ℕ) = (sk.lo q).res.length
              · simp only [hl, he, lt_irrefl, ite_false, ite_true, Prod.mk.injEq] at hvq
                rw [hvq.2] at hqpi
                exact Or.inr ⟨he, Or.inr ⟨hqpi, by simp; omega⟩⟩
              · simp only [hl, he, ite_false, Prod.mk.injEq] at hvq
                simp [hvq.1] at hqb
          | choose =>
            simp only [oview, hbq, hph, ite_true, Prod.mk.injEq] at hvq
            rw [hvq.2] at hqpi
            have hlt : (J q : ℕ) < (sk.lo q).res.length := by
              rw [hiq.choose_len hbq hph]; have := (J q).isLt; omega
            exact absurd hqpi (hiq.res_post hbq _ (resAt_mem hlt))
          | tail =>
            simp only [oview, hbq, hph, ite_true, Prod.mk.injEq] at hvq
            rw [hvq.2] at hqpi
            exact absurd hqpi (hiq.tail_post hbq hph)

/-- `Rel` only depends on the choices of processes whose choice is still open. -/
lemma rel_congr {J J' : P → Ch k} {sk : Cfg P C (LK L) (Mem Bs)} {so : Cfg P C L (Mem Bs)}
    (hrel : Rel Pi k J sk so)
    (hJ : ∀ q, J' q ≠ J q → sk.busy q = false ∨ (sk.lo q).ph = .tail) : Rel Pi k J' sk so where
  cl := hrel.cl
  view q := by
    by_cases h : J' q = J q
    · rw [h]; exact hrel.view q
    · rcases hJ q h with h' | h'
      · simpa [oview, h'] using hrel.view q
      · simpa [oview, h'] using hrel.view q
  mem := hrel.mem
  coins := hrel.coins
  bad hb := by
    rcases hrel.bad hb with h | ⟨q, hq⟩
    · exact Or.inl h
    · right; refine ⟨q, ?_⟩
      by_cases h : J' q = J q
      · rw [h]; exact hq
      · rcases hJ q h with h' | h'
        · simp [SpoiledJ, h'] at hq
        · simp [SpoiledJ, h'] at hq

/-- The object random step of `P(O^k)` (choosing iteration `j`) corresponds to no step of `P(O)`
for the choices `J` with `J p = j`. -/
theorem step_rand_obj (hk : 1 ≤ k) {sk : Cfg P C (LK L) (Mem Bs)} {p : P} {m : ℕ}
    {g : Fin (m + 1) → Cfg P C (LK L) (Mem Bs)}
    (hinv : InvK Pr I Pi k sk) (hb : sk.busy p = true)
    (hm : (sys Pr (iterSem I Pi k)).move sk p = .rand m g) :
    ∃ hmk : m = k - 1, (sk.lo p).ph = .choose ∧
      (∀ i, InvK Pr I Pi k (g i) ∧ (g i).busy p = true ∧ ((g i).lo p).ph = .tail ∧
        ∀ q, q ≠ p → (g i).busy q = sk.busy q ∧ (g i).lo q = sk.lo q) ∧
      ∀ (J : P → Ch k) (so : Cfg P C L (Mem Bs)) (j : Fin (m + 1)), Rel Pi k J sk so →
        (J p : ℕ) = j → Rel Pi k J (g j) so := by
  obtain ⟨o, κ, hn, hbase⟩ := (hinv p).call hb
  have hip := hinv p
  cases hph : (sk.lo p).ph with
  | pre =>
    exfalso
    by_cases hpi : Pi p (sk.lo p).cur
    · cases ha : I.act p (sk.lo p).cur with
      | access i o' κ' => rw [move_step Pr _ sk p hb (iter_act_pre_access hph hpi ha)] at hm; cases hm
      | ret r l' => rw [move_step Pr _ sk p hb (iter_act_pre_ret hph hpi ha)] at hm; cases hm
    · by_cases hlt : (sk.lo p).res.length + 1 < k
      · rw [move_step Pr _ sk p hb (iter_act_restart hph hpi hlt)] at hm; cases hm
      · rw [move_step Pr _ sk p hb (iter_act_tochoose hph hpi hlt)] at hm; cases hm
  | tail =>
    exfalso
    cases ha : I.act p (sk.lo p).cur with
    | access i o' κ' => rw [move_step Pr _ sk p hb (iter_act_tail_access hph ha)] at hm; cases hm
    | ret r l' => rw [move_ret Pr _ sk p hb (iter_act_tail_ret hph ha) hn] at hm; cases hm
  | choose =>
    rw [move_orand Pr _ sk p hb (iter_act_choose hph)] at hm
    cases hm
    refine ⟨rfl, rfl, fun i => ⟨?_, by simp [hb], by simp, fun q hq => by
      simp [Function.update_of_ne hq]⟩, fun J so j hrel hJ => ?_⟩
    · have hlt : (i : ℕ) < (sk.lo p).res.length := by
        rw [hip.choose_len hb hph]; have := i.isLt; omega
      refine invK_update hinv p le_rfl (fun q hq => by simp [Function.update_of_ne hq])
        ⟨fun _ => ⟨o, κ, by simpa using hn, by simpa using hbase⟩, fun _ h => by simp at h,
          fun _ h => by simp at h, fun _ => by simpa using hip.res_post hb,
          fun _ _ => by simpa using hip.res_post hb _ (resAt_mem hlt), fun _ h => by simp at h,
          by simpa using hip.sc_le⟩
    · have hv := hrel.view p
      simp only [hb, oview, hph, ite_true] at hv
      refine rel_update hrel p hrel.cl hrel.mem hrel.coins rfl rfl
        (fun q hq => by simp [Function.update_of_ne hq]) (fun q _ => ⟨rfl, rfl⟩) ?_
        (fun h => by simp [h]) ?_
      · rw [hv]; simp [oview, hb, hJ]
      · intro h
        left
        simp only [SpoiledJ, hb, hph, true_and] at h
        simp [hJ ▸ h]

end Step

/-! ### Averaging over the choices -/

section Avg

variable [Fintype P]

/-- Average over the choices `J`, each uniform in `0, …, k-1`. -/
noncomputable def avgJ (k : ℕ) (F : (P → Ch k) → ℝ) : ℝ :=
  (∑ J, F J) / Fintype.card (P → Ch k)

lemma card_pos (k : ℕ) : (0 : ℝ) < Fintype.card (P → Ch k) := by
  exact_mod_cast Fintype.card_pos

lemma avgJ_mono {k : ℕ} {F G : (P → Ch k) → ℝ} (h : ∀ J, F J ≤ G J) : avgJ k F ≤ avgJ k G :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun J _ => h J) (card_pos k).le

lemma avgJ_nonneg {k : ℕ} {F : (P → Ch k) → ℝ} (h : ∀ J, 0 ≤ F J) : 0 ≤ avgJ k F :=
  div_nonneg (Finset.sum_nonneg fun J _ => h J) (card_pos k).le

lemma avgJ_const (k : ℕ) (c : ℝ) : avgJ (P := P) k (fun _ => c) = c := by
  simp [avgJ, Finset.sum_const, Finset.card_univ]
  field_simp

/-- Averaging over one coordinate. -/
lemma sum_sum_update (p : P) {k : ℕ} (F : (P → Ch k) → ℝ) :
    ∑ j : Ch k, ∑ J : P → Ch k, F (Function.update J p j) =
      Fintype.card (Ch k) * ∑ J, F J := by
  set e := Equiv.funSplitAt p (Ch k) with he
  have hupd : ∀ (j : Ch k) (x : Ch k × ({q // q ≠ p} → Ch k)),
      Function.update (e.symm x) p j = e.symm (j, x.2) := by
    intro j x; funext q
    by_cases hq : q = p
    · subst hq; simp [he, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [he, Equiv.funSplitAt, Equiv.piSplitAt, hq, Function.update_of_ne hq]
  have h1 : ∀ j : Ch k, ∑ J : P → Ch k, F (Function.update J p j) =
      Fintype.card (Ch k) * ∑ b : {q // q ≠ p} → Ch k, F (e.symm (j, b)) := by
    intro j
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [hupd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [h1, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.sum_prod_type' (f := fun j b => F (e.symm (j, b)))]
  exact e.symm.sum_comp F

lemma avg_avgJ_update (p : P) {k : ℕ} (F : (P → Ch k) → ℝ) :
    (∑ j : Ch k, avgJ k fun J => F (Function.update J p j)) / ((k - 1 : ℕ) + 1 : ℕ) =
      avgJ k F := by
  simp only [avgJ, ← Finset.sum_div, sum_sum_update p F, Fintype.card_fin]
  have : ((k - 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

end Avg

/-! ### The value of `P(O^k)` is at most the average value of `P(O)` -/

section Main

variable [Fintype P] [Nonempty P]

omit [Fintype P] [Nonempty P] in
lemma terminal_of_rel {J : P → Ch k} {sk : Cfg P C (LK L) (Mem Bs)} {so : Cfg P C L (Mem Bs)}
    (hinv : InvK Pr I Pi k sk) (hrel : Rel Pi k J sk so)
    (ht : (sys Pr (iterSem I Pi k)).Terminal sk) : (sys Pr (implSem I Pi)).Terminal so := by
  have hinv' : ∀ q, sk.busy q = true → ∃ o κ, Pr.next q (sk.cl q) = .call o κ :=
    fun q hq => by obtain ⟨o, κ, h, -⟩ := (hinv q).call hq; exact ⟨o, κ, h⟩
  rw [terminal_iff Pr _ hinv'] at ht
  refine (terminal_iff Pr _ fun q hq => ?_).2 fun q => ?_
  · exfalso
    have := hrel.view q
    simp [oview, (ht q).1] at this
    rw [this.1] at hq; cases hq
  · have := hrel.view q
    simp [oview, (ht q).1] at this
    exact ⟨this.1, by rw [hrel.cl]; exact (ht q).2⟩

/-- **Removal of the unused iterations.** For payoffs compatible at terminal configurations,
the optimal value of `P(O^k)` from `sk` is at most the average, over the choices `J`, of the
optimal values of `P(O)` from the corresponding configurations. -/
theorem opt_le_avg (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    {payK : Cfg P C (LK L) (Mem Bs) → ℝ} {payO : Cfg P C L (Mem Bs) → ℝ}
    (hpO : ∀ s, 0 ≤ payO s) (hpO1 : ∀ s, payO s ≤ 1)
    (hterm : ∀ J sk so, InvK Pr I Pi k sk → Rel Pi k J sk so →
      (sys Pr (iterSem I Pi k)).Terminal sk → payK sk ≤ payO so)
    {sk : Cfg P C (LK L) (Mem Bs)} {fam : (P → Ch k) → Cfg P C L (Mem Bs)}
    (hinv : InvK Pr I Pi k sk) (hrel : ∀ J, Rel Pi k J sk (fam J)) :
    (sys Pr (iterSem I Pi k)).opt payK sk ≤
      avgJ k fun J => (sys Pr (implSem I Pi)).opt payO (fam J) := by
  set KS := sys Pr (iterSem I Pi k)
  set OS := sys Pr (implSem I Pi)
  refine MDP.opt_le_of_super (fun sk x => InvK Pr I Pi k sk ∧ ∃ fam : (P → Ch k) → Cfg P C L (Mem Bs),
      (∀ J, Rel Pi k J sk (fam J)) ∧ x = avgJ k fun J => OS.opt payO (fam J)) ?_ ?_ ?_ ?_
    ⟨hinv, fam, hrel, rfl⟩
  · rintro s x ⟨-, fam, -, rfl⟩
    exact avgJ_nonneg fun J => MDP.opt_nonneg hpO _
  · rintro s x ⟨hinv, fam, hrel, rfl⟩ ht
    calc payK s = avgJ k fun _ => payK s := (avgJ_const k _).symm
      _ ≤ _ := avgJ_mono fun J => by
        rw [MDP.opt_of_terminal (terminal_of_rel hinv (hrel J) ht)]
        exact hterm J s (fam J) hinv (hrel J) ht
  · rintro s x p s' ⟨hinv, fam, hrel, rfl⟩ hm
    have hstep : ∀ J, InvK Pr I Pi k s' ∧ ∃ so', Rel Pi k J s' so' ∧
        (so' = fam J ∨ OS.move (fam J) p = .det so') := fun J => by
      cases hb : s.busy p
      · exact step_det_idle hk hinv (hrel J) hb hm
      · exact step_det_busy hEF hWF hinv (hrel J) hb hm
    choose hinv' fam' hrel' hmv using hstep
    refine ⟨_, avgJ_mono fun J => ?_, hinv' (Classical.arbitrary _), fam', hrel', rfl⟩
    rcases hmv J with h | h
    · rw [h]
    · exact MDP.opt_det hpO hpO1 h
  · rintro s x p m g ⟨hinv, fam, hrel, rfl⟩ hm
    cases hb : s.busy p
    · have hstep := fun J => step_rand_client hk hinv (hrel J) hb hm
      choose g' hmv hg' using hstep
      refine ⟨fun i => avgJ k fun J => OS.opt payO (g' J i), ?_,
        fun i => ⟨(hg' (Classical.arbitrary _) i).1, fun J => g' J i, fun J => (hg' J i).2, rfl⟩⟩
      calc (∑ i, avgJ k fun J => OS.opt payO (g' J i)) / (m + 1)
          = avgJ k fun J => (∑ i, OS.opt payO (g' J i)) / (m + 1) := by
            simp only [avgJ, ← Finset.sum_div]; rw [Finset.sum_comm]; ring
        _ ≤ _ := avgJ_mono fun J => MDP.opt_rand hpO hpO1 (hmv J)
    · obtain ⟨rfl, -, hg, hrelg⟩ := step_rand_obj hk hinv hb hm
      refine ⟨fun j => avgJ k fun J => OS.opt payO (fam (Function.update J p j)), ?_, fun j =>
        ⟨(hg j).1, fun J => fam (Function.update J p j), fun J => ?_, rfl⟩⟩
      · have := avg_avgJ_update p (fun J => OS.opt payO (fam J))
        push_cast at this ⊢
        rw [this]
      · have h1 := hrelg (Function.update J p j) _ j (hrel _) (by simp)
        refine rel_congr h1 fun q hq => ?_
        by_cases hqp : q = p
        · subst hqp; exact Or.inr (hg j).2.2.1
        · exact absurd (by simp [Function.update_of_ne hqp]) hq

/-- Reachable configurations of `P(O^k)` satisfy the invariants and, for every choice `J`,
correspond to reachable configurations of `P(O)`. -/
theorem reach_rel (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    {sk : Cfg P C (LK L) (Mem Bs)}
    (h : (sys Pr (iterSem I Pi k)).Reach (initCfg Pr (iterSem I Pi k)) sk) :
    InvK Pr I Pi k sk ∧ ∀ J, ∃ so, Rel Pi k J sk so ∧
      (sys Pr (implSem I Pi)).Reach (initCfg Pr (implSem I Pi)) so := by
  suffices H : ∀ s s', (sys Pr (iterSem I Pi k)).Reach s s' → InvK Pr I Pi k s →
      (∀ J, ∃ so, Rel Pi k J s so ∧ (sys Pr (implSem I Pi)).Reach (initCfg Pr (implSem I Pi)) so) →
      InvK Pr I Pi k s' ∧ ∀ J, ∃ so', Rel Pi k J s' so' ∧
        (sys Pr (implSem I Pi)).Reach (initCfg Pr (implSem I Pi)) so' by
    exact H _ _ h invK_init fun J => ⟨_, rel_init J, .refl _⟩
  intro s s' hr
  induction hr with
  | refl s => intro hinv hJ; exact ⟨hinv, hJ⟩
  | @det s0 s1 s2 q hm _ ih =>
    intro hinv hJ
    have hst : ∀ J, InvK Pr I Pi k s1 ∧ ∃ so', Rel Pi k J s1 so' ∧
        (sys Pr (implSem I Pi)).Reach (initCfg Pr (implSem I Pi)) so' := fun J => by
      obtain ⟨so, hrel, hreach⟩ := hJ J
      have hst : InvK Pr I Pi k s1 ∧ ∃ so', Rel Pi k J s1 so' ∧
          (so' = so ∨ (sys Pr (implSem I Pi)).move so q = .det so') := by
        cases hb : s0.busy q
        · exact step_det_idle hk hinv hrel hb hm
        · exact step_det_busy hEF hWF hinv hrel hb hm
      obtain ⟨hinv', so', hrel', hmv⟩ := hst
      refine ⟨hinv', so', hrel', ?_⟩
      rcases hmv with rfl | hmv
      · exact hreach
      · exact hreach.trans (.det q hmv (.refl _))
    exact ih (hst fun _ => ⟨0, by omega⟩).1 fun J => (hst J).2
  | @rand s0 s2 q m g i hm _ ih =>
    intro hinv hJ
    cases hb : s0.busy q
    · have hst : ∀ J, InvK Pr I Pi k (g i) ∧ ∃ so', Rel Pi k J (g i) so' ∧
          (sys Pr (implSem I Pi)).Reach (initCfg Pr (implSem I Pi)) so' := fun J => by
        obtain ⟨so, hrel, hreach⟩ := hJ J
        obtain ⟨g', hmv, hg'⟩ := step_rand_client hk hinv hrel hb hm
        exact ⟨(hg' i).1, g' i, (hg' i).2, hreach.trans (.rand q m g' i hmv (.refl _))⟩
      exact ih (hst fun _ => ⟨0, by omega⟩).1 fun J => (hst J).2
    · obtain ⟨rfl, -, hg, hrelg⟩ := step_rand_obj hk hinv hb hm
      refine ih (hg i).1 fun J => ?_
      obtain ⟨so, hrel, hreach⟩ := hJ (Function.update J q i)
      refine ⟨so, rel_congr (hrelg _ so i hrel (by simp)) fun r hr => ?_, hreach⟩
      by_cases hrq : r = q
      · subst hrq; exact Or.inr (hg i).2.2.1
      · exact absurd (by simp [Function.update_of_ne hrq]) hr

end Main

end Removal

end Podc.BluntingAdversary
