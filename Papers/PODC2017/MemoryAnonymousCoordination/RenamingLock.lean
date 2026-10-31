import Papers.PODC2017.MemoryAnonymousCoordination.RenamingSteps

/-!
# Figure 3: the per-round lock invariant

`Lock π n v t C T` says that the identifier `v` is *locked* as the winner of round `t` in the
configuration `C`: from now on every process that completes a collect in round `t` adopts `v`,
except the "token holders" `T`, each of which may still write one *bad* record. A record is bad
for `(v, t)` (`Bad`) if its round is `≤ t` and it is not `(v, t)`; records of a later round are
harmless, because they all record `v` as the winner of round `t` in their history (`Hi`), and a
process seeing one catches up beyond round `t`:

* every process about to write a bad record is in `T`;
* every process `p ∉ T` in the middle of a collect has fewer than `n − |T|` bad entries in its
  virtual view (entries read so far + current contents of the registers not yet read);
* fewer than `n − |T|` registers are bad;
* every record of a round `> t` (in a register, a local state or a view) has `(v, t)` in its
  history.

The lock is preserved by every step (`lock_step`; `T` only shrinks), provided that a process
completing round `t` has preference `v` (supplied by the global invariant). It is established
when all registers hold the same record `(p, s)` and `p` starts a collect (`lock_establish`), and
two locks of the same round are for the same identifier (`Lock.eq`): each forces at least `n` of
the `2n − 1` registers to be good for it, and no register is good for two identifiers.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Renaming

open Cslib.SharedMemory

variable {P : Type} {m : ℕ} [DecidableEq P]
  {n : ℕ} {S : Sel P m} {π : P → Equiv.Perm (Fin m)}

/-- A register value is bad for the winner `v` of round `t`. -/
abbrev Bad (v : P) (t : ℕ) (e : Option (P × St P)) : Prop := rdOf e ≤ t ∧ rvOf e ≠ some (v, t)

/-- Records of a later round than `t` know that `v` won round `t`. -/
def Hi (v : P) (t : ℕ) (e : Option (P × St P)) : Prop := t < rdOf e → (v, t) ∈ histOf e

/-- Number of bad entries. -/
def nbad (v : P) (t : ℕ) (V : Fin m → Option (P × St P)) : ℕ :=
  (Finset.univ.filter fun j => Bad v t (V j)).card

/-- A history assigns at most one winner to each round. -/
def HFun (H : Finset (P × ℕ)) : Prop := ∀ u u' t, (u, t) ∈ H → (u', t) ∈ H → u = u'

/-- The identifier `v` is locked as the winner of round `t` in `C`, with token holders `T`. -/
structure Lock (π : P → Equiv.Perm (Fin m)) (n : ℕ) (v : P) (t : ℕ) (C : Cfg P m)
    (T : Finset P) : Prop where
  pos : 1 ≤ t
  writers : ∀ p s j b, C.loc p = .write s j b → Bad v t (some (p, s)) → p ∈ T
  collectors : ∀ p s k view, C.loc p = .collect s k view → p ∉ T →
    nbad v t (mixed (π p) k view C.mem) + T.card < n
  mem : nbad v t C.mem + T.card < n
  memHi : ∀ r, Hi v t (C.mem r)
  locHi : ∀ p s, stOf (C.loc p) = some s → Hi v t (some (p, s))
  viewHi : ∀ p s k view j, C.loc p = .collect s k view → Hi v t (view j)

/-- `v` is locked as the winner of round `t`. -/
def Locked (π : P → Equiv.Perm (Fin m)) (n : ℕ) (v : P) (t : ℕ) (C : Cfg P m) : Prop :=
  ∃ T, Lock π n v t C T

/-! ### Counting bad entries -/

lemma nbad_comp (f : Fin m → Option (P × St P)) (σ : Equiv.Perm (Fin m)) (v : P) (t : ℕ) :
    nbad v t (fun j => f (σ j)) = nbad v t f := by
  unfold nbad
  exact Finset.card_equiv σ (by simp)

lemma nbad_write_le {f g : Fin m → Option (P × St P)} {v : P} {t : ℕ} {e : Option (P × St P)}
    (j₀ : Fin m) (h : ∀ j, g j = f j ∨ (g j = e ∧ j = j₀)) :
    nbad v t g ≤ nbad v t f + (if Bad v t e then 1 else 0) := by
  unfold nbad
  split_ifs with he
  · calc _ ≤ (insert j₀ (Finset.univ.filter fun j => Bad v t (f j))).card := by
          apply Finset.card_le_card
          intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          intro hj; rcases h j with h | ⟨-, h⟩
          · right; rwa [← h]
          · left; exact h
      _ ≤ _ := Finset.card_insert_le _ _
  · rw [add_zero]
    apply Finset.card_le_card
    intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hj; rcases h j with h | ⟨h, -⟩
    · rwa [← h]
    · rw [h] at hj; exact absurd hj he

lemma nbad_add_good (f : Fin m → Option (P × St P)) (v : P) (t : ℕ) :
    nbad v t f + (Finset.univ.filter fun j => ¬ Bad v t (f j)).card = m := by
  unfold nbad
  rw [Finset.card_filter_add_card_filter_not]; simp

lemma rdOf_of_rvOf {e : Option (P × St P)} {u : P} {t : ℕ} (h : rvOf e = some (u, t)) :
    rdOf e = t := by
  cases e with
  | none => simp at h
  | some e => obtain ⟨q, s⟩ := e; simp only [rvOf_some, Option.some.injEq, Prod.mk.injEq] at h; simp [h.2]

lemma hi_mixed {v : P} {t : ℕ} (σ : Equiv.Perm (Fin m)) (k : Fin m)
    {view M : Fin m → Option (P × St P)} (h1 : ∀ j, Hi v t (view j)) (h2 : ∀ r, Hi v t (M r))
    (j : Fin m) : Hi v t (mixed σ k view M j) := by
  unfold mixed; split_ifs
  · exact h1 j
  · exact h2 _

@[simp] lemma hi_none (v : P) (t : ℕ) : Hi v t none := by simp [Hi]

/-! ### Two locks of the same round agree -/

lemma Lock.eq (hm : m + 1 = 2 * n) {C : Cfg P m} {v v' : P} {t : ℕ} {T T' : Finset P}
    (hfun : ∀ r, HFun (histOf (C.mem r))) (h : Lock π n v t C T) (h' : Lock π n v' t C T') :
    v = v' := by
  by_contra hne
  have hcov : ∀ r, Bad v t (C.mem r) ∨ Bad v' t (C.mem r) := by
    intro r
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.1 hc
    by_cases hr : t < rdOf (C.mem r)
    · exact hne (hfun r v v' t (h.memHi r hr) (h'.memHi r hr))
    · have e1 : rvOf (C.mem r) = some (v, t) := by
        by_contra hh; exact h1 ⟨by omega, hh⟩
      have e2 : rvOf (C.mem r) = some (v', t) := by
        by_contra hh; exact h2 ⟨by omega, hh⟩
      rw [e1] at e2; simp only [Option.some.injEq, Prod.mk.injEq] at e2; exact hne e2.1
  have : m ≤ nbad v t C.mem + nbad v' t C.mem := by
    unfold nbad
    calc m = (Finset.univ : Finset (Fin m)).card := by simp
      _ ≤ ((Finset.univ.filter fun j => Bad v t (C.mem j)) ∪
            (Finset.univ.filter fun j => Bad v' t (C.mem j))).card := by
          apply Finset.card_le_card
          intro r _; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hcov r
      _ ≤ _ := Finset.card_union_le _ _
  have := h.mem; have := h'.mem
  omega

lemma Locked.eq (hm : m + 1 = 2 * n) {C : Cfg P m} {v v' : P} {t : ℕ}
    (hfun : ∀ r, HFun (histOf (C.mem r))) (h : Locked π n v t C) (h' : Locked π n v' t C) :
    v = v' := by
  obtain ⟨T, hT⟩ := h; obtain ⟨T', hT'⟩ := h'; exact hT.eq hm hfun hT'

/-! ### Completing a collect -/

lemma pos_of_hm (hm : m + 1 = 2 * n) : 0 < m := by omega

lemma startCollect_eq (h : 0 < m) (s : St P) :
    (startCollect s : Loc P m) = .collect s ⟨0, h⟩ (fun _ => none) := by
  simp [startCollect, h]

lemma finish_cases (n : ℕ) (S : Sel P m) (p : P) (s : St P) (V : Fin m → Option (P × St P)) :
    (∃ a, finish n S p s V = .done a ∧ ∃ j, (p, a) ∈ histOf (V j)) ∨
      (retName p V = none ∧
        finish n S p s V = .write (adopt n V (catchUp S p s V))
          (S.tgt p (adopt n V (catchUp S p s V)) V)
          (decide (∀ j, V j = some (p, adopt n V (catchUp S p s V))))) := by
  unfold finish
  cases h : retName p V with
  | some a =>
    left; refine ⟨a, rfl, ?_⟩
    unfold retName at h
    split_ifs at h with h'
    simp only [Option.some.injEq] at h
    subst h
    exact h'.choose_spec
  | none => right; exact ⟨rfl, rfl⟩

lemma retName_none {p : P} {V : Fin m → Option (P × St P)} (h : retName p V = none) (j : Fin m)
    (a : ℕ) : (p, a) ∉ histOf (V j) := by
  intro h'
  unfold retName at h
  split_ifs at h with h''
  exact h'' ⟨a, j, h'⟩

/-- The record written after a collect knows the winner of round `t` if its round is later. -/
lemma finish_hi {v : P} {t : ℕ} {p : P} {s : St P} {V : Fin m → Option (P × St P)}
    (hV : ∀ j, Hi v t (V j)) (hs : Hi v t (some (p, s))) (S : Sel P m) (n : ℕ) :
    Hi v t (some (p, adopt n V (catchUp S p s V))) := by
  intro h
  simp only [rdOf_some, adopt_rd, histOf_some, adopt_hist] at h ⊢
  rcases catchUp_mem S p s V with h1 | ⟨j, q, hj⟩
  · rw [h1] at h ⊢; exact hs h
  · have := hV j; rw [hj] at this; exact this h

/-- **Key step**: a process that saw fewer than `n` bad entries writes a good record. -/
lemma finish_good (hm : m + 1 = 2 * n) (hS : S.OK) {v : P} {t : ℕ} {p : P} {s : St P}
    {V : Fin m → Option (P × St P)} (hV : nbad v t V < n) :
    ¬ Bad v t (some (p, adopt n V (catchUp S p s V))) := by
  set s₁ := catchUp S p s V with hs₁
  rintro ⟨h1, h2⟩
  simp only [rdOf_some, adopt_rd] at h1
  simp only [rvOf_some, adopt_rd, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and] at h2
  have hrd := catchUp_rd hS p s V
  rw [← hs₁] at hrd
  have hmax : maxRd V ≤ t := by omega
  -- all good entries are `(v, t)`
  have hgood := nbad_add_good V v t
  have hcnt : n ≤ cnt V t v := by
    have : (Finset.univ.filter fun j => ¬ Bad v t (V j)).card ≤ cnt V t v := by
      unfold cnt
      apply Finset.card_le_card
      intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
      intro hj; exact hj ((le_maxRd V j).trans hmax)
    omega
  have hne : (Finset.univ.filter fun j => rvOf (V j) = some (v, t)).Nonempty := by
    rw [← Finset.card_pos]; unfold cnt at hcnt; omega
  obtain ⟨j, hj⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have ht : t ≤ maxRd V := (rdOf_of_rvOf hj).symm ▸ le_maxRd V j
  have hs1 : s₁.rd = t := by omega
  apply h2 _ hs1
  apply adopt_eq hm
  rw [hs1]; exact hcnt

/-! ### Preservation -/

/-- **The lock is preserved by every step**, provided that a process about to complete round `t`
prefers `v`. -/
lemma lock_step (hm : m + 1 = 2 * n) (hS : S.OK) {C C' : Cfg P m} {ℓ : Label P RenObj} {v : P}
    {t : ℕ} {T : Finset P} (hL : Lock π n v t C T)
    (hW : ∀ p s j, C.loc p = .write s j true → s.rd = t → s.val = v)
    (h : (I n S π).step C ℓ = some C') : ∃ T', Lock π n v t C' T' := by
  have hm0 := pos_of_hm hm
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, hmem, hloc⟩ := inv_cases h
    have hpl : C'.loc p = .collect ⟨p, 1, ∅⟩ ⟨0, hm0⟩ (fun _ => none) := by
      rw [hloc]; simp [startCollect, hm0]
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    refine ⟨T, ⟨hL.pos, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro q s j b hq hb
      by_cases hqp : q = p
      · subst hqp; rw [hpl] at hq; cases hq
      · rw [hoth q hqp] at hq; exact hL.writers q s j b hq hb
    · intro q s k view hq hT
      by_cases hqp : q = p
      · subst hqp; rw [hpl] at hq; simp only [Loc.collect.injEq] at hq
        obtain ⟨-, rfl, -⟩ := hq
        rw [hmem, mixed_zero _ _ _ _ rfl, nbad_comp]; exact hL.mem
      · rw [hoth q hqp] at hq; rw [hmem]; exact hL.collectors q s k view hq hT
    · rw [hmem]; exact hL.mem
    · intro r; rw [hmem]; exact hL.memHi r
    · intro q s hq
      by_cases hqp : q = p
      · subst hqp; rw [hpl] at hq; simp only [stOf_collect, Option.some.injEq] at hq; subst hq
        intro h1; simp only [rdOf_some] at h1; have := hL.pos; omega
      · rw [hoth q hqp] at hq; exact hL.locHi q s hq
    · intro q s k view j hq
      by_cases hqp : q = p
      · subst hqp; rw [hpl] at hq; simp only [Loc.collect.injEq] at hq
        obtain ⟨-, -, rfl⟩ := hq; simp
      · rw [hoth q hqp] at hq; exact hL.viewHi q s k view j hq
  | ret p r =>
    obtain ⟨-, -, -, hmem, hloc⟩ := ret_cases h
    have hpl : C'.loc p = .idle := by rw [hloc]; simp
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    refine ⟨T, ⟨hL.pos, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro q s j b hq hb
      by_cases hqp : q = p
      · subst hqp; rw [hpl] at hq; cases hq
      · rw [hoth q hqp] at hq; exact hL.writers q s j b hq hb
    · intro q s k view hq hT
      by_cases hqp : q = p
      · subst hqp; rw [hpl] at hq; cases hq
      · rw [hoth q hqp] at hq; rw [hmem]; exact hL.collectors q s k view hq hT
    · rw [hmem]; exact hL.mem
    · intro r; rw [hmem]; exact hL.memHi r
    · intro q s hq
      by_cases hqp : q = p
      · subst hqp; rw [hpl] at hq; cases hq
      · rw [hoth q hqp] at hq; exact hL.locHi q s hq
    · intro q s k view j hq
      by_cases hqp : q = p
      · subst hqp; rw [hpl] at hq; cases hq
      · rw [hoth q hqp] at hq; exact hL.viewHi q s k view j hq
  | tau p =>
    obtain ⟨-, -, hcase⟩ := tau_cases h
    rcases hcase with ⟨s, k, view, hl, hmem, hloc⟩ | ⟨s, j, b, hl, hmem, hloc⟩
    · -- a read
      have hpl : C'.loc p = afterRead n S p s k view (C.mem (π p k)) := by rw [hloc]; simp
      have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hsHi := hL.locHi p s (by rw [hl]; rfl)
      have hVHi : ∀ i, Hi v t (mixed (π p) k view C.mem i) :=
        hi_mixed _ _ (fun i => hL.viewHi p s k view i hl) hL.memHi
      refine ⟨T, ⟨hL.pos, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro q s' j' b' hq hb
        by_cases hqp : q = p
        · subst hqp
          by_contra hT
          rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq with hk
          rw [mixed_last _ _ _ _ hk] at hq
          rcases finish_cases n S q s (mixed (π q) k view C.mem) with ⟨a, ha, -⟩ | ⟨-, hw⟩
          · rw [ha] at hq; cases hq
          · rw [hw] at hq; simp only [Loc.write.injEq] at hq
            obtain ⟨rfl, -, -⟩ := hq
            have := hL.collectors q s k view hl hT
            exact finish_good hm hS (by omega) hb
        · rw [hoth q hqp] at hq; exact hL.writers q s' j' b' hq hb
      · intro q s' k' view' hq hT
        by_cases hqp : q = p
        · subst hqp
          rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq with hk
          · simp only [Loc.collect.injEq] at hq
            obtain ⟨rfl, rfl, rfl⟩ := hq
            rw [hmem, mixed_read _ _ _ _ hk]
            exact hL.collectors q _ k view hl hT
          · rcases finish_cases n S q s (Function.update view k (C.mem (π q k))) with
              ⟨a, ha, -⟩ | ⟨-, hw⟩
            · rw [ha] at hq; cases hq
            · rw [hw] at hq; cases hq
        · rw [hoth q hqp] at hq; rw [hmem]; exact hL.collectors q s' k' view' hq hT
      · rw [hmem]; exact hL.mem
      · intro r; rw [hmem]; exact hL.memHi r
      · intro q s' hq
        by_cases hqp : q = p
        · subst hqp
          rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq with hk
          · simp only [stOf_collect, Option.some.injEq] at hq; subst hq; exact hsHi
          · rw [mixed_last _ _ _ _ hk] at hq
            rcases finish_cases n S q s (mixed (π q) k view C.mem) with ⟨a, ha, -⟩ | ⟨-, hw⟩
            · rw [ha] at hq; cases hq
            · rw [hw] at hq; simp only [stOf_write, Option.some.injEq] at hq; subst hq
              exact finish_hi hVHi hsHi S n
        · rw [hoth q hqp] at hq; exact hL.locHi q s' hq
      · intro q s' k' view' i hq
        by_cases hqp : q = p
        · subst hqp
          rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq with hk
          · simp only [Loc.collect.injEq] at hq
            obtain ⟨rfl, rfl, rfl⟩ := hq
            rw [Function.update_apply]; split_ifs
            · exact hL.memHi _
            · exact hL.viewHi q _ k view i hl
          · rcases finish_cases n S q s (Function.update view k (C.mem (π q k))) with
              ⟨a, ha, -⟩ | ⟨-, hw⟩
            · rw [ha] at hq; cases hq
            · rw [hw] at hq; cases hq
        · rw [hoth q hqp] at hq; exact hL.viewHi q s' k' view' i hq
    · -- a write of `(p, s)`
      have hpl : C'.loc p = afterWrite n p s b := by rw [hloc]; simp
      have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hsHi := hL.locHi p s (by rw [hl]; rfl)
      have hT : (T.erase p).card + (if Bad v t (some (p, s)) then 1 else 0) ≤ T.card := by
        split_ifs with hx
        · rw [Finset.card_erase_add_one (hL.writers p s j b hl hx)]
        · simpa using Finset.card_erase_le
      have hmemle : nbad v t C'.mem ≤
          nbad v t C.mem + (if Bad v t (some (p, s)) then 1 else 0) := by
        rw [hmem]
        apply nbad_write_le (π p j)
        intro i; simp only [Function.update_apply]; split_ifs with hi
        · exact Or.inr ⟨rfl, hi⟩
        · exact Or.inl rfl
      have hmem' := hL.mem
      -- the new local state of `p`
      have hnew : C'.loc p = .done 0 ∨ (∃ a, C'.loc p = .done a) ∨
          ∃ s', C'.loc p = .collect s' ⟨0, hm0⟩ (fun _ => none) ∧ Hi v t (some (p, s')) := by
        rw [hpl]; unfold afterWrite
        split_ifs with hb hv hn
        · exact Or.inr (Or.inl ⟨_, rfl⟩)
        · exact Or.inr (Or.inl ⟨_, rfl⟩)
        · right; right
          refine ⟨_, startCollect_eq hm0 _, ?_⟩
          intro h1
          simp only [rdOf_some, nextRound, histOf_some] at h1 ⊢
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
          · exact Finset.mem_insert_of_mem (hsHi h1)
          · rw [← h1, hW p s j (by rw [hl, hb]) h1.symm]; exact Finset.mem_insert_self _ _
        · right; right; exact ⟨_, startCollect_eq hm0 _, hsHi⟩
      refine ⟨T.erase p, ⟨hL.pos, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro q s' j' b' hq hb
        by_cases hqp : q = p
        · subst hqp
          rcases hnew with h' | ⟨a, h'⟩ | ⟨s'', h', -⟩ <;> rw [h'] at hq <;> cases hq
        · rw [hoth q hqp] at hq
          exact Finset.mem_erase.2 ⟨hqp, hL.writers q s' j' b' hq hb⟩
      · intro q s' k' view' hq hTq
        by_cases hqp : q = p
        · subst hqp
          rcases hnew with h' | ⟨a, h'⟩ | ⟨s'', h', -⟩ <;> rw [h'] at hq <;> try (cases hq; done)
          simp only [Loc.collect.injEq] at hq
          obtain ⟨-, rfl, -⟩ := hq
          rw [mixed_zero _ _ _ _ rfl, nbad_comp]
          omega
        · have hqT : q ∉ T := fun h => hTq (Finset.mem_erase.2 ⟨hqp, h⟩)
          rw [hoth q hqp] at hq
          have h1 := hL.collectors q s' k' view' hq hqT
          have h2 : nbad v t (mixed (π q) k' view' C'.mem) ≤
              nbad v t (mixed (π q) k' view' C.mem) +
                (if Bad v t (some (p, s)) then 1 else 0) := by
            rw [hmem]
            apply nbad_write_le ((π q).symm (π p j))
            intro i
            rcases mixed_write (π q) k' view' C.mem (π p j) (some (p, s)) i with h | ⟨h, hi⟩
            · exact Or.inl h
            · exact Or.inr ⟨h, by rw [← hi]; simp⟩
          omega
      · omega
      · intro r; rw [hmem, Function.update_apply]; split_ifs
        · exact hsHi
        · exact hL.memHi r
      · intro q s' hq
        by_cases hqp : q = p
        · subst hqp
          rcases hnew with h' | ⟨a, h'⟩ | ⟨s'', h', h''⟩ <;> rw [h'] at hq <;> try (cases hq; done)
          simp only [stOf_collect, Option.some.injEq] at hq; subst hq; exact h''
        · rw [hoth q hqp] at hq; exact hL.locHi q s' hq
      · intro q s' k' view' i hq
        by_cases hqp : q = p
        · subst hqp
          rcases hnew with h' | ⟨a, h'⟩ | ⟨s'', h', -⟩ <;> rw [h'] at hq <;> try (cases hq; done)
          simp only [Loc.collect.injEq] at hq
          obtain ⟨-, -, rfl⟩ := hq; simp
        · rw [hoth q hqp] at hq; exact hL.viewHi q s' k' view' i hq

/-! ### Establishing a lock -/

/-- A lock of round `t` in a memory full of the same record of round `t` is for its val. -/
lemma Lock.eq_of_all (hm : m + 1 = 2 * n) {C : Cfg P m} {u : P} {t : ℕ} {T : Finset P}
    (hL : Lock π n u t C T) {p : P} {s : St P} (hall : ∀ r, C.mem r = some (p, s))
    (ht : s.rd = t) : u = s.val := by
  by_contra hne
  have : nbad u t C.mem = m := by
    unfold nbad
    rw [Finset.filter_true_of_mem]
    · simp
    · intro r _
      rw [hall r]
      refine ⟨by simp [ht], ?_⟩
      simp only [rvOf_some, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
      exact fun h _ => hne h.symm
  have := hL.mem
  omega

/-- **Establishing the lock**: if all registers hold `(p, s)` and `p` is at the start of a
collect, then `s.val` is locked as the winner of round `s.rd`, with token holders all other
processes — provided every record of a later round names a locked winner of round `s.rd`. -/
lemma lock_establish [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n)
    {C : Cfg P m} {p : P} {s₀ : St P} {k : Fin m} {view : Fin m → Option (P × St P)}
    (hl : C.loc p = .collect s₀ k view) (hk : k.val = 0) {s : St P} (hpos : 1 ≤ s.rd)
    (hall : ∀ j, C.mem (π p j) = some (p, s))
    (hloc : ∀ q s', stOf (C.loc q) = some s' → s.rd < s'.rd →
      ∃ u, (u, s.rd) ∈ s'.hist ∧ Locked π n u s.rd C)
    (hview : ∀ q s' k' view' j, C.loc q = .collect s' k' view' → s.rd < rdOf (view' j) →
      ∃ u, (u, s.rd) ∈ histOf (view' j) ∧ Locked π n u s.rd C) :
    Lock π n s.val s.rd C (Finset.univ.erase p) := by
  have hc : (Finset.univ.erase p).card + 1 = Fintype.card P :=
    Finset.card_erase_add_one (Finset.mem_univ p)
  have hall' : ∀ r, C.mem r = some (p, s) := fun r => by
    have := hall ((π p).symm r); rwa [Equiv.apply_symm_apply] at this
  have h0 : nbad s.val s.rd C.mem = 0 := by
    unfold nbad
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r _; rw [hall' r]
    simp only [Bad, rdOf_some, rvOf_some]; exact fun ⟨_, h⟩ => h rfl
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q s' j b hq _
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ q⟩
    rintro rfl; rw [hl] at hq; cases hq
  · intro q s' k' view' hq hT
    have hqp : q = p := by simpa using hT
    subst hqp
    rw [hl] at hq; simp only [Loc.collect.injEq] at hq; obtain ⟨-, rfl, -⟩ := hq
    rw [mixed_zero _ _ _ _ hk, nbad_comp]
    omega
  · omega
  · intro r; rw [hall' r]; intro h; simp at h
  · intro q s' hq h
    simp only [rdOf_some] at h
    obtain ⟨u, hu, T, hT⟩ := hloc q s' hq h
    rw [hT.eq_of_all hm hall' rfl] at hu
    exact hu
  · intro q s' k' view' j hq h
    obtain ⟨u, hu, T, hT⟩ := hview q s' k' view' j hq h
    rw [hT.eq_of_all hm hall' rfl] at hu
    exact hu

end Podc.MemoryAnonymousCoordination.Renaming
