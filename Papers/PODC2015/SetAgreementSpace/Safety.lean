import Papers.PODC2015.SetAgreementSpace.Lemma3

/-!
# Safety of Figure 3: validity and `k`-agreement (Section 4.1 of [DFKR15])

We prove that the algorithm of Figure 3 (with or without the `fix` guard) solves one-shot
`k`-set agreement (`fig3_solves`): validity and `k`-agreement hold in every finite one-shot
execution, when `m ≤ k` and the snapshot has `r ≥ n + 2m - k` components (the paper takes
`r = n + 2m - k`).

## Proof

Validity is the invariant `ValInv`: every `pref`, every value in `A` and every decision is an
input.

`k`-agreement is the invariant `AgrInv`: either at most `k - m` processes have decided, or there
is a *ghost* configuration `C₀` (the one just after the deciding scan of the `(k-m+1)`-th
deciding process `q₀` of the paper), recorded by

* `X` — the set of pairs in `A` at `C₀` (at most `m`), `V = {values of X}` (`InV X`),
* `D0` — the processes decided at `C₀` (`k - m + 1` of them; they never update `A` again),
* `E` — the processes decided before `C₀` (at most `k - m`),

such that (`Post`): every decision is in `V` or by a process of `E`; `A` has no `⊥`; every pair
in `A` is in `X` or has the identifier of a process outside `D0`; every pair that occurs twice
in `A` has a value in `V` (**Lemma 4**); a process about to update either prefers a value in `V`
or all its pairs in `A` are in `X`; a process about to scan either prefers a value in `V` or has
no copy of `(pref, id)` outside its current component.

By Lemma 3 the pairs outside `X` have pairwise distinct identifiers outside `D0`, so `A` holds at
most `m + (n - (k - m + 1)) < r` distinct pairs (`Post.card_image_le`), hence always a duplicated
pair: this is the counting step of Case 2b of Lemma 4. The case analysis of the preservation
proof (`Post.step`) follows Lemma 4 (Case 1 = `upd` field with all pairs in `X`, Case 2a = adoption,
Case 2b = the advance branch). For `fix = true` the advance branch may also be taken because
`dupVal s = pref`; then `pref` is the value of a duplicated pair, hence in `V` as well.
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

variable {V : Type} [DecidableEq V] [Inhabited V] {n m r : ℕ} [NeZero r]

/-! ### Duplicated pairs -/

omit [Inhabited V] [NeZero r] in
/-- The value of the first duplicated pair is the value of a pair occurring twice. -/
lemma dupVal_eq_some {s : Fin r → Cell V n} {v : V} (h : dupVal s = some v) :
    ∃ j₁ j₂ p, j₁ ≠ j₂ ∧ s j₁ = some (v, p) ∧ s j₂ = some (v, p) := by
  unfold dupVal firstDup at h
  cases hf : (List.finRange r).find? (fun j => decide (IsDup s j)) with
  | none => rw [hf] at h; simp at h
  | some j =>
    rw [hf] at h
    have hd := List.find?_some hf
    simp only [decide_eq_true_eq] at hd
    obtain ⟨j₂, hlt, hj₂⟩ := hd
    simp only [Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨⟨v', p⟩, hj, rfl⟩ := h
    exact ⟨j, j₂, p, hlt.ne, hj, hj₂.trans hj⟩

omit [Inhabited V] [NeZero r] in
/-- Without `⊥`, a duplicated pair makes `dupVal` defined. -/
lemma exists_dupVal {s : Fin r → Cell V n} (hs : ∀ j, s j ≠ none)
    (hd : ∃ j₁ j₂, j₁ ≠ j₂ ∧ s j₁ = s j₂) : ∃ v, dupVal s = some v := by
  obtain ⟨j₁, j₂, hne, heq⟩ := hd
  have key : ∃ j, IsDup s j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨j₁, j₂, h, heq.symm⟩
    · exact ⟨j₂, j₁, h, heq⟩
  unfold dupVal firstDup
  cases hf : (List.finRange r).find? (fun j => decide (IsDup s j)) with
  | none =>
    obtain ⟨j, hj⟩ := key
    have := List.find?_eq_none.1 hf j (List.mem_finRange j)
    simp [hj] at this
  | some j =>
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (hs j)
    exact ⟨x.1, by simp [hx]⟩

omit [Inhabited V] [NeZero r] in
/-- Pigeonhole: fewer than `r` distinct entries give a duplicated entry. -/
lemma exists_dup_of_card {s : Fin r → Cell V n} (h : (Finset.univ.image s).card < r) :
    ∃ j₁ j₂, j₁ ≠ j₂ ∧ s j₁ = s j₂ := by
  classical
  obtain ⟨x, -, y, -, hxy, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image s) (by simpa using h)
    (fun a _ => Finset.mem_image_of_mem s (Finset.mem_univ a))
  exact ⟨x, y, hxy, h⟩

/-! ### Validity -/

/-- The inputs of the processes in `α`. -/
def ins (α : Exec V n) : Set V := {w | ∃ q, inputs α q = some w}

omit [DecidableEq V] in
lemma ins_mono (α : Exec V n) (ℓ : Label (Fin n) (saObj V)) : ins α ⊆ ins (α ++ [ℓ]) := by
  rintro w ⟨q, hq⟩
  exact ⟨q, by rw [inputs_append_of_ne_none _ (by simp [hq]), hq]⟩

/-- The validity invariant: preferences, values in `A` and decisions are inputs. -/
structure ValInv (α : Exec V n) (C : Cfg V n r) : Prop where
  pref : ∀ p, opsOf α p ≠ [] → (C.loc p).pref ∈ ins α
  out : ∀ p w, (C.loc p).out = some w → w ∈ ins α
  mem : ∀ j v p, C.mem () j = some (v, p) → v ∈ ins α

omit [DecidableEq V] in
lemma BasicInv.ops_ne_nil {α : Exec V n} {C : Cfg V n r} (hB : BasicInv α C) {p : Fin n}
    (hp : (C.loc p).pc ≠ .idle) : opsOf α p ≠ [] := fun h0 => by
  rw [(hB.fresh p h0).1] at hp; exact hp rfl

omit [Inhabited V] [NeZero r] in
lemma getD_dupVal_mem {s : Fin r → Cell V n} {S : Set V} {v : V} (hv : v ∈ S)
    (hs : ∀ j w p, s j = some (w, p) → w ∈ S) : (dupVal s).getD v ∈ S := by
  cases h : dupVal s with
  | none => simpa using hv
  | some w =>
    obtain ⟨j, -, p, -, hj, -⟩ := dupVal_eq_some h
    simpa using hs j w p hj

lemma ValInv.step {fix : Bool} {α : Exec V n} {C C' : Cfg V n r}
    {ℓ : Label (Fin n) (saObj V)} (hB : BasicInv α C) (hV : ValInv α C)
    (h1 : OneShot (α ++ [ℓ])) (h : (fig3 (V := V) fix n m r).step C ℓ = some C') :
    ValInv (α ++ [ℓ]) C' := by
  have hmono := ins_mono α ℓ
  rcases step_cases h with
    ⟨p, v, rfl, hp, hmem, hloc, hpend⟩ | ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ |
    ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ | ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ |
    ⟨p, rfl, hp, hpc, -, -, -⟩
  · have hops := opsOf_nil_of_oneShot h1
    refine ⟨fun q hq => ?_, fun q w hw => ?_, fun j w q hj => ?_⟩
    · by_cases hqp : q = p
      · subst hqp; refine ⟨q, ?_⟩; simp [hloc, inputs, hops]
      · have : opsOf α q ≠ [] := by simpa [opsOf_concat, Ne.symm hqp] using hq
        simpa [hloc, hqp] using hmono (hV.pref q this)
    · by_cases hqp : q = p
      · subst hqp; simp [hloc] at hw
      · simp only [hloc, Function.update_of_ne hqp] at hw; exact hmono (hV.out q w hw)
    · rw [hmem] at hj; exact hmono (hV.mem j w q hj)
  · have hops := hB.ops_ne_nil (p := p) (by rw [hpc]; simp)
    refine ⟨fun q hq => ?_, fun q w hw => ?_, fun j w q hj => ?_⟩
    · have hq' : opsOf α q ≠ [] := by simpa [opsOf_concat] using hq
      by_cases hqp : q = p
      · subst hqp; simpa [hloc] using hmono (hV.pref q hq')
      · simpa [hloc, hqp] using hmono (hV.pref q hq')
    · by_cases hqp : q = p
      · subst hqp; simp only [hloc, Function.update_self] at hw; exact hmono (hV.out q w hw)
      · simp only [hloc, Function.update_of_ne hqp] at hw; exact hmono (hV.out q w hw)
    · rw [hmem] at hj
      by_cases hji : j = (C.loc p).i
      · subst hji; simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
        rw [← hj.1]; exact hmono (hV.pref p hops)
      · rw [Function.update_of_ne hji] at hj; exact hmono (hV.mem j w q hj)
  · have hops := hB.ops_ne_nil (p := p) (by rw [hpc]; simp)
    have hval : ∀ j w q, C.mem () j = some (w, q) → w ∈ ins α := hV.mem
    have hd := getD_dupVal_mem (hV.pref p hops) hval
    refine ⟨fun q hq => ?_, fun q w hw => ?_, fun j w q hj => ?_⟩
    · have hq' : opsOf α q ≠ [] := by simpa [opsOf_concat] using hq
      by_cases hqp : q = p
      · subst hqp; simp only [hloc, Function.update_self]
        rcases afterScan_cases (fix := fix) (m := m) (C.loc q) (C.mem ()) q with
          ⟨-, h2⟩ | ⟨-, -, h2⟩ | ⟨-, -, h2⟩ <;> rw [h2]
        · exact hmono (hV.pref q hq')
        · exact hmono hd
        · exact hmono (hV.pref q hq')
      · simpa [hloc, hqp] using hmono (hV.pref q hq')
    · by_cases hqp : q = p
      · subst hqp; simp only [hloc, Function.update_self] at hw
        rcases afterScan_cases (fix := fix) (m := m) (C.loc q) (C.mem ()) q with
          ⟨-, h2⟩ | ⟨-, -, h2⟩ | ⟨-, -, h2⟩ <;> rw [h2] at hw
        · simp only [Option.some.injEq] at hw; rw [← hw]; exact hmono hd
        · exact hmono (hV.out q w hw)
        · exact hmono (hV.out q w hw)
      · simp only [hloc, Function.update_of_ne hqp] at hw; exact hmono (hV.out q w hw)
    · rw [hmem] at hj; exact hmono (hV.mem j w q hj)
  · refine ⟨fun q hq => ?_, fun q w hw => ?_, fun j w q hj => ?_⟩
    · have hq' : opsOf α q ≠ [] := by simpa [opsOf_concat] using hq
      by_cases hqp : q = p
      · subst hqp; simpa [hloc] using hmono (hV.pref q hq')
      · simpa [hloc, hqp] using hmono (hV.pref q hq')
    · by_cases hqp : q = p
      · subst hqp; simp only [hloc, Function.update_self] at hw; exact hmono (hV.out q w hw)
      · simp only [hloc, Function.update_of_ne hqp] at hw; exact hmono (hV.out q w hw)
    · rw [hmem] at hj; exact hmono (hV.mem j w q hj)
  · exact absurd ((hB.pend_none p).2 hpc) hp

/-! ### `k`-agreement -/

/-- `v` is the value of some pair of `X` (the set `V` of the paper). -/
def InV (X : Finset (Cell V n)) (v : V) : Prop := ∃ q, some (v, q) ∈ X

/-- The processes that have decided. -/
def decided (C : Cfg V n r) : Finset (Fin n) :=
  Finset.univ.filter fun p => (C.loc p).out ≠ none

/-- The invariant after the ghost configuration `C₀` (just after the final scan of `q₀`):
`X` = the pairs in `A` at `C₀`, `D0` = the processes decided at `C₀`, `E` = those decided before
`C₀`. The field `dup` is **Lemma 4 of [DFKR15]**. -/
structure Post (m k : ℕ) (C : Cfg V n r) (X : Finset (Cell V n)) (D0 E : Finset (Fin n)) :
    Prop where
  card_X : X.card ≤ m
  card_E : E.card ≤ k - m
  card_D0 : k - m + 1 ≤ D0.card
  dec_D0 : ∀ p ∈ D0, (C.loc p).out ≠ none
  out : ∀ p w, (C.loc p).out = some w → InV X w ∨ p ∈ E
  noBot : ∀ j, C.mem () j ≠ none
  inX : ∀ j v p, C.mem () j = some (v, p) → some (v, p) ∈ X ∨ p ∉ D0
  dup : ∀ j₁ j₂ v p, j₁ ≠ j₂ → C.mem () j₁ = some (v, p) → C.mem () j₂ = some (v, p) → InV X v
  upd : ∀ p, (C.loc p).pc = .upd →
    InV X (C.loc p).pref ∨ ∀ j v, C.mem () j = some (v, p) → some (v, p) ∈ X
  scan : ∀ p, (C.loc p).pc = .scan →
    InV X (C.loc p).pref ∨ ∀ j, j ≠ (C.loc p).i → C.mem () j ≠ some ((C.loc p).pref, p)

/-- The `k`-agreement invariant: at most `k - m` processes have decided, or `Post` holds for
some ghost data. -/
def AgrInv (m k : ℕ) (C : Cfg V n r) : Prop :=
  (decided C).card ≤ k - m ∨ ∃ X D0 E, Post m k C X D0 E

section Post

variable {k : ℕ} {α : Exec V n} {C : Cfg V n r} {X : Finset (Cell V n)} {D0 E : Finset (Fin n)}

/-- Counting (Case 2b of Lemma 4): by Lemma 3, `A` holds at most `m + (n - |D0|)` distinct
pairs. -/
lemma Post.card_image_le (hB : BasicInv α C) (hP : Post m k C X D0 E) :
    (Finset.univ.image (C.mem ())).card ≤ m + (n - D0.card) := by
  set S := Finset.univ.image (C.mem ())
  have h1 : S ⊆ X ∪ S.filter (· ∉ X) := by
    intro x hx; by_cases h : x ∈ X <;> simp [h, hx]
  have h2 : (S.filter (· ∉ X)).card ≤ (D0ᶜ.image some).card := by
    apply Finset.card_le_card_of_injOn (fun x => x.map Prod.snd)
    · intro x hx
      obtain ⟨hxS, hX⟩ := Finset.mem_filter.1 hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hxS
      obtain ⟨⟨v, p⟩, hvp⟩ := Option.ne_none_iff_exists'.1 (hP.noBot j)
      rcases hP.inX j v p hvp with h | h
      · rw [hvp] at hX; exact absurd h hX
      · simp [hvp, h]
    · intro x hx y hy hxy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1
      obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1
      obtain ⟨⟨v, p⟩, hvp⟩ := Option.ne_none_iff_exists'.1 (hP.noBot j)
      obtain ⟨⟨v', p'⟩, hvp'⟩ := Option.ne_none_iff_exists'.1 (hP.noBot j')
      simp only [hvp, hvp', Option.map_some, Option.some.injEq] at hxy ⊢
      subst hxy
      rw [hB.same_val hvp hvp']
  have h3 : (D0ᶜ.image some).card ≤ n - D0.card := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_compl, Fintype.card_fin]
  calc S.card ≤ (X ∪ S.filter (· ∉ X)).card := Finset.card_le_card h1
    _ ≤ X.card + (S.filter (· ∉ X)).card := Finset.card_union_le _ _
    _ ≤ m + (n - D0.card) := by have := hP.card_X; omega

omit [DecidableEq V] [NeZero r] in
lemma Post.count_lt (hP : Post m k C X D0 E) (hmk : m ≤ k) (hr : n + 2 * m - k ≤ r) :
    m + (n - D0.card) < r := by
  have h1 := hP.card_D0
  have h2 : D0.card ≤ n := by simpa using Finset.card_le_univ D0
  omega

/-- After `C₀`, `A` always contains a duplicated pair, and the first one has a value in `V`. -/
lemma Post.exists_dupVal (hB : BasicInv α C) (hP : Post m k C X D0 E) (hmk : m ≤ k)
    (hr : n + 2 * m - k ≤ r) : ∃ v, dupVal (C.mem ()) = some v ∧ InV X v := by
  obtain ⟨v, hv⟩ := SetAgreementSpace.exists_dupVal hP.noBot
    (exists_dup_of_card ((hP.card_image_le hB).trans_lt (hP.count_lt hmk hr)))
  obtain ⟨j₁, j₂, p, hne, h₁, h₂⟩ := dupVal_eq_some hv
  exact ⟨v, hv, hP.dup j₁ j₂ v p hne h₁ h₂⟩

omit [NeZero r] in
lemma Post.inV_of_dupVal (hP : Post m k C X D0 E) {v : V} (hv : dupVal (C.mem ()) = some v) :
    InV X v := by
  obtain ⟨j₁, j₂, p, hne, h₁, h₂⟩ := dupVal_eq_some hv
  exact hP.dup j₁ j₂ v p hne h₁ h₂

/-- **Lemma 4 of [DFKR15]** (and the decision part of the `k`-agreement argument): the invariant
`Post` is preserved by every step. -/
lemma Post.step {fix : Bool} {C' : Cfg V n r} {ℓ : Label (Fin n) (saObj V)}
    (hmk : m ≤ k) (hr : n + 2 * m - k ≤ r) (hB : BasicInv α C) (h1 : OneShot (α ++ [ℓ]))
    (h : (fig3 (V := V) fix n m r).step C ℓ = some C') (hP : Post m k C X D0 E) :
    Post m k C' X D0 E := by
  rcases step_cases h with
    ⟨p, v, rfl, hp, hmem, hloc, hpend⟩ | ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ |
    ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ | ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ |
    ⟨p, rfl, hp, hpc, -, -, -⟩
  · -- invocation
    obtain ⟨hl0, hno⟩ := hB.fresh p (opsOf_nil_of_oneShot h1)
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by simp [hloc, hq]
    refine ⟨hP.card_X, hP.card_E, hP.card_D0, fun q hq => ?_, fun q w hw => ?_,
      by simpa only [hmem] using hP.noBot, by simpa only [hmem] using hP.inX,
      by simpa only [hmem] using hP.dup, fun q hq => ?_, fun q hq => ?_⟩
    · by_cases hqp : q = p
      · subst hqp; have := hP.dec_D0 q hq; rw [hl0] at this; simp at this
      · rw [hoth q hqp]; exact hP.dec_D0 q hq
    · by_cases hqp : q = p
      · subst hqp; simp [hloc] at hw
      · rw [hoth q hqp] at hw; exact hP.out q w hw
    · by_cases hqp : q = p
      · subst hqp; right; intro j w hj; rw [hmem] at hj; exact absurd hj (hno j w)
      · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.upd q hq
    · by_cases hqp : q = p
      · subst hqp; simp [hloc] at hq
      · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.scan q hq
  · -- update (line 7)
    set l := C.loc p with hl
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by simp [hloc, hq]
    have hout : ∀ q, (C'.loc q).out = (C.loc q).out := fun q => by
      by_cases hq : q = p
      · subst hq; simp [hloc, hl]
      · rw [hoth q hq]
    have hpD0 : p ∉ D0 := fun hpD => by
      rcases hB.out_pc p (hP.dec_D0 p hpD) with h2 | h2 <;> rw [← hl] at h2 <;>
        rw [h2] at hpc <;> cases hpc
    have hcopy : ∀ j, C.mem () j = some (l.pref, p) → InV X l.pref := fun j hj =>
      (hP.upd p hpc).elim id (fun h => ⟨p, h j _ hj⟩)
    refine ⟨hP.card_X, hP.card_E, hP.card_D0, fun q hq => ?_, fun q w hw => ?_,
      fun j => ?_, fun j w q hj => ?_, fun j₁ j₂ w q hne h₁ h₂ => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · rw [hout]; exact hP.dec_D0 q hq
    · rw [hout] at hw; exact hP.out q w hw
    · rw [hmem]; by_cases hj : j = l.i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact hP.noBot j
    · rw [hmem] at hj
      by_cases hji : j = l.i
      · subst hji; simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
        rw [← hj.2]; exact Or.inr hpD0
      · rw [Function.update_of_ne hji] at hj; exact hP.inX j w q hj
    · rw [hmem] at h₁ h₂
      by_cases e1 : j₁ = l.i
      · subst e1
        have e2 : j₂ ≠ l.i := Ne.symm hne
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h₁
        rw [Function.update_of_ne e2, ← h₁.1, ← h₁.2] at h₂
        rw [← h₁.1]; exact hcopy j₂ h₂
      · by_cases e2 : j₂ = l.i
        · subst e2
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h₂
          rw [Function.update_of_ne e1, ← h₂.1, ← h₂.2] at h₁
          rw [← h₂.1]; exact hcopy j₁ h₁
        · rw [Function.update_of_ne e1] at h₁; rw [Function.update_of_ne e2] at h₂
          exact hP.dup j₁ j₂ w q hne h₁ h₂
    · by_cases hqp : q = p
      · subst hqp; simp [hloc] at hq
      · rw [hoth q hqp] at hq ⊢
        refine (hP.upd q hq).imp id (fun h j w hj => ?_)
        rw [hmem] at hj
        by_cases hji : j = l.i
        · subst hji; simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
          exact absurd hj.2 (Ne.symm hqp)
        · rw [Function.update_of_ne hji] at hj; exact h j w hj
    · by_cases hqp : q = p
      · subst hqp
        simp only [hloc, Function.update_self]
        by_cases hc : ∃ j, j ≠ l.i ∧ C.mem () j = some (l.pref, q)
        · obtain ⟨j, -, hj⟩ := hc; exact Or.inl (hcopy j hj)
        · push Not at hc
          right; intro j hj; rw [hmem, Function.update_of_ne hj]; exact hc j hj
      · rw [hoth q hqp] at hq ⊢
        refine (hP.scan q hq).imp id (fun h j hj => ?_)
        rw [hmem]
        by_cases hji : j = l.i
        · subst hji; simp [Ne.symm hqp]
        · rw [Function.update_of_ne hji]; exact h j hj
  · -- scan (lines 8–14)
    set l := C.loc p with hl
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by simp [hloc, hq]
    obtain ⟨v, hv, hvX⟩ := hP.exists_dupVal hB hmk hr
    have hp' : C'.loc p = afterScan fix m p l (C.mem ()) := by simp [hloc, hl]
    rcases afterScan_cases (fix := fix) (m := m) l (C.mem ()) p with
      ⟨-, h2⟩ | ⟨-, hA, h2⟩ | ⟨-, hA, h2⟩ <;> rw [h2] at hp'
    · -- decision
      refine ⟨hP.card_X, hP.card_E, hP.card_D0, fun q hq => ?_, fun q w hw => ?_,
        by simpa only [hmem] using hP.noBot, by simpa only [hmem] using hP.inX,
        by simpa only [hmem] using hP.dup, fun q hq => ?_, fun q hq => ?_⟩
      · by_cases hqp : q = p
        · subst hqp; simp [hp']
        · rw [hoth q hqp]; exact hP.dec_D0 q hq
      · by_cases hqp : q = p
        · subst hqp; simp only [hp', hv, Option.getD_some, Option.some.injEq] at hw
          rw [← hw]; exact Or.inl hvX
        · rw [hoth q hqp] at hw; exact hP.out q w hw
      · by_cases hqp : q = p
        · subst hqp; simp [hp'] at hq
        · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.upd q hq
      · by_cases hqp : q = p
        · subst hqp; simp [hp'] at hq
        · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.scan q hq
    · -- adoption (lines 11–13)
      refine ⟨hP.card_X, hP.card_E, hP.card_D0, fun q hq => ?_, fun q w hw => ?_,
        by simpa only [hmem] using hP.noBot, by simpa only [hmem] using hP.inX,
        by simpa only [hmem] using hP.dup, fun q hq => ?_, fun q hq => ?_⟩
      · by_cases hqp : q = p
        · subst hqp; rw [hp']; exact hP.dec_D0 q hq
        · rw [hoth q hqp]; exact hP.dec_D0 q hq
      · by_cases hqp : q = p
        · subst hqp; rw [hp'] at hw; exact hP.out q w hw
        · rw [hoth q hqp] at hw; exact hP.out q w hw
      · by_cases hqp : q = p
        · subst hqp; rw [hp']; left; simpa [hv] using hvX
        · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.upd q hq
      · by_cases hqp : q = p
        · subst hqp; simp [hp'] at hq
        · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.scan q hq
    · -- advance (line 14)
      have hpref : InV X l.pref := by
        rcases hP.scan p hpc with h3 | h3
        · exact h3
        · by_contra hn
          refine hA ⟨fun j hj => ⟨hP.noBot j, h3 j hj⟩,
            exists_dup_of_card ((hP.card_image_le hB).trans_lt (hP.count_lt hmk hr)),
            fun _ he => hn (hP.inV_of_dupVal he)⟩
      refine ⟨hP.card_X, hP.card_E, hP.card_D0, fun q hq => ?_, fun q w hw => ?_,
        by simpa only [hmem] using hP.noBot, by simpa only [hmem] using hP.inX,
        by simpa only [hmem] using hP.dup, fun q hq => ?_, fun q hq => ?_⟩
      · by_cases hqp : q = p
        · subst hqp; rw [hp']; exact hP.dec_D0 q hq
        · rw [hoth q hqp]; exact hP.dec_D0 q hq
      · by_cases hqp : q = p
        · subst hqp; rw [hp'] at hw; exact hP.out q w hw
        · rw [hoth q hqp] at hw; exact hP.out q w hw
      · by_cases hqp : q = p
        · subst hqp; rw [hp']; exact Or.inl hpref
        · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.upd q hq
      · by_cases hqp : q = p
        · subst hqp; simp [hp'] at hq
        · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.scan q hq
  · -- response
    set l := C.loc p with hl
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by simp [hloc, hq]
    have hp' : C'.loc p = { l with pc := .idle } := by simp [hloc, hl]
    refine ⟨hP.card_X, hP.card_E, hP.card_D0, fun q hq => ?_, fun q w hw => ?_,
      by simpa only [hmem] using hP.noBot, by simpa only [hmem] using hP.inX,
      by simpa only [hmem] using hP.dup, fun q hq => ?_, fun q hq => ?_⟩
    · by_cases hqp : q = p
      · subst hqp; rw [hp']; exact hP.dec_D0 q hq
      · rw [hoth q hqp]; exact hP.dec_D0 q hq
    · by_cases hqp : q = p
      · subst hqp; rw [hp'] at hw; exact hP.out q w hw
      · rw [hoth q hqp] at hw; exact hP.out q w hw
    · by_cases hqp : q = p
      · subst hqp; simp [hp'] at hq
      · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.upd q hq
    · by_cases hqp : q = p
      · subst hqp; simp [hp'] at hq
      · rw [hoth q hqp] at hq ⊢; simpa only [hmem] using hP.scan q hq
  · exact absurd ((hB.pend_none p).2 hpc) hp

end Post

omit [DecidableEq V] [NeZero r] in
lemma decided_eq_of_out {C C' : Cfg V n r} (h : ∀ q, (C'.loc q).out = (C.loc q).out) :
    decided C' = decided C := by
  simp [decided, h]

/-- The `k`-agreement invariant is preserved; when the `(k - m + 1)`-th process decides, the ghost
configuration `C₀` is fixed. -/
lemma AgrInv.step {fix : Bool} {k : ℕ} {α : Exec V n} {C C' : Cfg V n r}
    {ℓ : Label (Fin n) (saObj V)} (hmk : m ≤ k) (hr : n + 2 * m - k ≤ r) (hB : BasicInv α C)
    (h1 : OneShot (α ++ [ℓ])) (h : (fig3 (V := V) fix n m r).step C ℓ = some C')
    (hA : AgrInv m k C) : AgrInv m k C' := by
  rcases hA with hd | ⟨X, D0, E, hP⟩
  swap
  · exact Or.inr ⟨X, D0, E, hP.step hmk hr hB h1 h⟩
  by_cases hd' : (decided C').card ≤ k - m
  · exact Or.inl hd'
  right
  rcases step_cases h with
    ⟨p, v, rfl, hp, hmem, hloc, hpend⟩ | ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ |
    ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ | ⟨p, rfl, hp, hpc, hmem, hloc, hpend⟩ |
    ⟨p, rfl, hp, hpc, -, -, -⟩
  · obtain ⟨hl0, -⟩ := hB.fresh p (opsOf_nil_of_oneShot h1)
    refine absurd ?_ hd'
    rw [decided_eq_of_out (C := C) (C' := C') (fun q => by
      by_cases hq : q = p
      · subst hq; simp [hloc, hl0]
      · simp [hloc, hq])]
    exact hd
  · refine absurd ?_ hd'
    rw [decided_eq_of_out (C := C) (C' := C') (fun q => by
      by_cases hq : q = p
      · subst hq; simp [hloc]
      · simp [hloc, hq])]
    exact hd
  · set l := C.loc p with hl
    have hp' : C'.loc p = afterScan fix m p l (C.mem ()) := by simp [hloc, hl]
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by simp [hloc, hq]
    have hout : l.out = none := by
      by_contra hc
      rcases hB.out_pc p hc with h2 | h2 <;> rw [← hl] at h2 <;> rw [h2] at hpc <;> cases hpc
    rcases afterScan_cases (fix := fix) (m := m) l (C.mem ()) p with
      ⟨hdc, h2⟩ | ⟨-, -, h2⟩ | ⟨-, -, h2⟩ <;> rw [h2] at hp'
    · -- the ghost configuration `C₀`
      have hD : decided C' = insert p (decided C) := by
        ext q; by_cases hq : q = p
        · subst hq; simp [decided, hp']
        · simp [decided, hoth q hq, hq]
      have hpD : p ∉ decided C := by simp [decided, ← hl, hout]
      have hcard : (decided C').card = k - m + 1 := by
        rw [hD, Finset.card_insert_of_notMem hpD] at hd' ⊢; omega
      have hn : (decided C').card ≤ n := by simpa using Finset.card_le_univ (decided C')
      have hmr : (Finset.univ.image (C.mem ())).card < r := by have := hdc.1; omega
      obtain ⟨v, hv⟩ := exists_dupVal hdc.2 (exists_dup_of_card hmr)
      have hmemX : ∀ j, C.mem () j ∈ Finset.univ.image (C.mem ()) := fun j =>
        Finset.mem_image_of_mem _ (Finset.mem_univ j)
      have hinV : ∀ j w q, C.mem () j = some (w, q) → InV (Finset.univ.image (C.mem ())) w :=
        fun j w q hj => ⟨q, by rw [← hj]; exact hmemX j⟩
      refine ⟨Finset.univ.image (C.mem ()), decided C', decided C, hdc.1, hd, hcard.ge,
        fun q hq => by simpa [decided] using hq, fun q w hw => ?_,
        by simpa only [hmem] using hdc.2, fun j w q hj => ?_, fun j₁ j₂ w q _ h₁ _ => ?_,
        fun q hq => ?_, fun q hq => ?_⟩
      · by_cases hqp : q = p
        · subst hqp; simp only [hp', hv, Option.getD_some, Option.some.injEq] at hw
          obtain ⟨j, -, q', -, hj, -⟩ := dupVal_eq_some hv
          rw [← hw]; exact Or.inl (hinV j v q' hj)
        · rw [hoth q hqp] at hw; right; simp [decided, hw]
      · rw [hmem] at hj; left; rw [← hj]; exact hmemX j
      · rw [hmem] at h₁; exact hinV j₁ w q h₁
      · right; intro j w hj; rw [hmem] at hj; rw [← hj]; exact hmemX j
      · have hqp : q ≠ p := by rintro rfl; simp [hp'] at hq
        rw [hoth q hqp] at hq ⊢
        by_cases hc : ∃ j, j ≠ (C.loc q).i ∧ C.mem () j = some ((C.loc q).pref, q)
        · obtain ⟨j, -, hj⟩ := hc; exact Or.inl (hinV j _ q hj)
        · push Not at hc; right; intro j hj; rw [hmem]; exact hc j hj
    all_goals
      refine absurd ?_ hd'
      rw [decided_eq_of_out (C := C) (C' := C') (fun q => by
        by_cases hq : q = p
        · subst hq; rw [hp']
        · rw [hoth q hq])]
      exact hd
  · refine absurd ?_ hd'
    rw [decided_eq_of_out (C := C) (C' := C') (fun q => by
      by_cases hq : q = p
      · subst hq; simp [hloc]
      · simp [hloc, hq])]
    exact hd
  · exact absurd ((hB.pend_none p).2 hpc) hp

/-! ### Main theorem -/

/-- The safety invariants hold in every configuration reached by a one-shot execution. -/
theorem safety_inv {fix : Bool} {k : ℕ} (hmk : m ≤ k) (hr : n + 2 * m - k ≤ r) {α : Exec V n}
    {C : Cfg V n r} (h : (fig3 (V := V) fix n m r).run α = some C) (hα : OneShot α) :
    BasicInv α C ∧ ValInv α C ∧ AgrInv m k C :=
  Impl.run_induction (Q := fun α C => OneShot α → BasicInv α C ∧ ValInv α C ∧ AgrInv m k C)
    (fun _ => ⟨BasicInv.init, ⟨by simp [opsOf], by simp [Impl.initCfg, fig3],
      by simp [Impl.initCfg, fig3]⟩, Or.inl (by simp [decided, Impl.initCfg, fig3])⟩)
    (fun _ _ _ _ _ ih hs h1 => by
      obtain ⟨hB, hV, hA⟩ := ih h1.of_append
      exact ⟨hB.step h1 hs, hV.step hB h1 hs, hA.step hmk hr hB h1 hs⟩) h hα

/-- **Validity and `k`-agreement of Figure 3** (Section 4.1 of [DFKR15]), for any snapshot size
`r ≥ n + 2m - k` and `m ≤ k`, with or without the `fix` guard: in every finite one-shot execution,
every output is the input of some process and at most `k` distinct values are output. -/
theorem fig3_solves_of_le (fix : Bool) {k : ℕ} (hmk : m ≤ k) (hr : n + 2 * m - k ≤ r) :
    (fig3 (V := V) fix n m r).Solves (kSetAgreement (Fin n) V k) := by
  rintro α ⟨C, hC⟩ hα
  obtain ⟨hB, hV, hA⟩ := safety_inv hmk hr hC hα
  have hO : ∀ p w, outputs α p = some w → (C.loc p).out = some w := fun p w hw =>
    (hB.outputs_eq p w hw).1
  refine ⟨fun p w hw => hV.out p w (hO p w hw), ?_⟩
  set g : Fin n → V := fun p => ((C.loc p).out).getD default
  rcases hA with hd | ⟨X, D0, E, hP⟩
  · calc {w | ∃ p, outputs α p = some w}.encard ≤ (g '' ↑(decided C)).encard := by
          apply Set.encard_le_encard
          rintro w ⟨p, hp⟩
          exact ⟨p, by simp [decided, hO p w hp], by simp only [g, hO p w hp]; rfl⟩
      _ ≤ (↑(decided C) : Set (Fin n)).encard := Set.encard_image_le _ _
      _ = (decided C).card := Set.encard_coe_eq_coe_finsetCard _
      _ ≤ k := by exact_mod_cast hd.trans (Nat.sub_le k m)
  · let f : Cell V n → V := fun o => (o.map Prod.fst).getD default
    have h1 : (f '' ↑X).encard ≤ X.card :=
      (Set.encard_image_le _ _).trans (Set.encard_coe_eq_coe_finsetCard _).le
    have h2 : (g '' ↑E).encard ≤ E.card :=
      (Set.encard_image_le _ _).trans (Set.encard_coe_eq_coe_finsetCard _).le
    have h3 : X.card + E.card ≤ k := by have := hP.card_X; have := hP.card_E; omega
    calc {w | ∃ p, outputs α p = some w}.encard ≤ (f '' ↑X ∪ g '' ↑E).encard := by
          apply Set.encard_le_encard
          rintro w ⟨p, hp⟩
          rcases hP.out p w (hO p w hp) with ⟨q, hq⟩ | hpE
          · left; exact ⟨_, hq, by simp only [f, Option.map_some]; rfl⟩
          · right; exact ⟨p, hpE, by simp only [g, hO p w hp]; rfl⟩
      _ ≤ (f '' ↑X).encard + (g '' ↑E).encard := Set.encard_union_le _ _
      _ ≤ X.card + E.card := add_le_add h1 h2
      _ ≤ k := by exact_mod_cast h3

/-- **Validity and `k`-agreement of Figure 3** with the paper's snapshot size
`r = n + 2m - k` (Section 4.1 of [DFKR15]); holds both for the original algorithm (`fix = false`)
and for the guarded one (`fix = true`). -/
theorem fig3_solves (fix : Bool) {n k m : ℕ} (hmk : m ≤ k) [NeZero (n + 2 * m - k)] :
    (fig3 (V := V) fix n m (n + 2 * m - k)).Solves (kSetAgreement (Fin n) V k) :=
  fig3_solves_of_le fix hmk le_rfl

end Podc.SetAgreementSpace
