import Papers.PODC2014.WritableObjects.Calls

/-!
# Timestamps order the operations on each base object

The core of the proof of Lemma 4.5: on each base object `A[i]`, an operation whose call has a
smaller timestamp key returns before any operation with a larger key is invoked
(`ret_before_of_keyPos_lt`). Here the template's requirement that `A[f]` is not in use when
`A[f].SWrite` is invoked is essential (see `Counterexample.lean`).
-/

set_option linter.unusedSectionVars false

namespace Podc.WritableObjects

open Cslib.SharedMemory

variable {P ι : Type} {T : ObjSpec} {W : Writable T} {owner : ι → P}
  {α : List (Ev P ι T)} {σ : P → ℕ → PSt ι T} [DecidableEq P] [DecidableEq ι]

/-- The template requirement "`A[f]` is not in use when `A[f].SWrite` is invoked". -/
def NotInUse (α : List (Ev P ι T)) : Prop :=
  ∀ t p f v, α[t]? = some (.swinv p f v) → ptrAt α t ≠ some f

namespace IsCtrl

variable (h : IsCtrl W owner α σ) (hC : CondC α)
include h

/-- The `SWrite` heading the group of an `Exec`: the `SWrite` of the `Write` whose write to
`Ptr` is the last one before the chosen point `t*` (the paper's `W` in Claim 4.7, (4.4)). -/
lemma head_of_opinv (hC : CondC α) {t : ℕ} {q : P} {i : ι} {o : T.Op}
    (ht : α[t]? = some (.opinv q i o)) :
    ∃ a₀ p₀ v₀ b₀, α[a₀]? = some (.swinv p₀ i v₀) ∧ keyPos α a₀ = keyPos α t ∧ a₀ < b₀ ∧
      b₀ < t ∧ (∃ r, α[b₀]? = some (.aret p₀ i r)) ∧ Quiet α p₀ a₀ b₀ := by
  have hcpt := cpt_tsOf (h.exists_cpt hC ht)
  obtain ⟨-, hts, hptr, -⟩ := hcpt.facts ht
  obtain ⟨w₀, p₀, hw₀, hw, hn⟩ := exists_last_ptr hptr
  obtain ⟨a₀, han⟩ := h.exists_anchor_of_ptr hw
  have hkey := keyPos_anchor han
  obtain ⟨p', i', v₀, ha, hw', b₀, hab, hbw, hb, hq1, -⟩ := han
  rw [hw] at hw'
  simp only [Option.some.injEq, Ev.ptr.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  refine ⟨a₀, p₀, v₀, b₀, ha, ?_, hab, by omega, hb, hq1⟩
  rw [hkey, keyPos_opinv ht, hn]

lemma keyPos_ne_top_iff_anchor {a : ℕ} {p : P} {i : ι} {v : T.State}
    (ha : α[a]? = some (.swinv p i v)) (hne : keyPos α a ≠ ⊤) : ∃ w, WAnchor α a w := by
  by_contra hc
  exact hne (keyPos_top ha hc)

/-- **Order of operations on `A[i]` by timestamps.** If the call of the operation `y` invoked at
`ay` on `A[i]` has a smaller timestamp key than the call of the operation invoked at `ax` on
`A[i]`, then `y` returns before `ax`. -/
lemma ret_before_of_keyPos_lt (hN : NotInUse α) (hC : CondC α) {i : ι} {y : OpId P}
    {ay ax : ℕ} {px : P} (hy : IsInv (Ev.toLow W i) α y ay) (hx : LowInvAt α i px ax)
    (hlt : keyPos α ay < keyPos α ax) : ∃ r < ax, IsRet (Ev.toLow W i) α y r := by
  -- the `SWrite` heading the group of `ax`
  obtain ⟨as, p, v, has, hkeys, hasx⟩ : ∃ as p v, α[as]? = some (.swinv p i v) ∧
      keyPos α as = keyPos α ax ∧ as ≤ ax := by
    rcases hx with ⟨v, hx⟩ | ⟨o, hx⟩
    · exact ⟨ax, px, v, hx, rfl, le_rfl⟩
    · obtain ⟨a₀, p₀, v₀, b₀, ha, hk, hab, hbt, -⟩ := h.head_of_opinv hC hx
      exact ⟨a₀, p₀, v₀, ha, hk, by omega⟩
  rw [← hkeys] at hlt
  suffices hs : ∃ r < as, IsRet (Ev.toLow W i) α y r by
    obtain ⟨r, hr, hr'⟩ := hs
    exact ⟨r, by omega, hr'⟩
  have hown := (h.swinv_facts has).1
  obtain ⟨has', hasev⟩ := getElem_of_getElem? has
  rcases lowInvAt_of_isInv hy with ⟨v', hay⟩ | ⟨o, hay⟩
  · -- `y` is an `SWrite`: same process (the owner of `i`)
    have hown' := (h.swinv_facts hay).1
    have hp : y.1 = p := by rw [← hown', hown]
    obtain ⟨wy, hwy⟩ := keyPos_ne_top_iff_anchor h hay (ne_top_of_lt hlt)
    have hky := keyPos_anchor hwy
    rcases lt_trichotomy as ay with hlt' | heq | hlt'
    · exfalso
      have hwy0 := hwy
      obtain ⟨p', i', v'', ha'', hw'', -⟩ := hwy0
      rw [hay] at ha''
      simp only [Option.some.injEq, Ev.swinv.injEq] at ha''
      obtain ⟨rfl, rfl, rfl⟩ := ha''
      obtain ⟨ws, hws, hwsa⟩ := h.exists_anchor_of_later_ptr has (hp ▸ hw'') (by
        have := hwy.lt; omega)
      have hks := keyPos_anchor hwsa
      rcases Nat.lt_or_eq_of_le hws with hws | rfl
      · have h1 := nptr_mono (α := α) (show ws + 1 ≤ wy by omega)
        have h2 := (nptr_succ_of_ptr hw'').1
        rw [hks, hky] at hlt
        have := WithTop.coe_lt_coe.1 hlt
        omega
      · exact absurd (hwsa.unique_left hwy) (by omega)
    · subst heq; exact absurd hlt (lt_irrefl _)
    · obtain ⟨r, h1, h2, -, ⟨r', hr⟩, h3⟩ := h.low_ret hy has' hlt' (by rw [hasev, hp]; rfl)
      refine ⟨r, ?_, h3⟩
      rcases Nat.lt_or_eq_of_le h2 with h2 | rfl
      · exact h2
      · rw [hr] at has; simp at has
  · -- `y` is an `Oper` of an `Exec`
    have hcpt := cpt_tsOf (h.exists_cpt hC hay)
    obtain ⟨-, -, hptr, hno⟩ := hcpt.facts hay
    have hky := keyPos_opinv hay
    rcases hno as p v has with ⟨b, r, hab, hbt, hb⟩ | ⟨c, r, hc1, hc2, hc⟩
    · exfalso
      obtain ⟨w, p'', h1, h2, hw⟩ := exists_ptr_of_ne (α := α) (show as ≤ tsOf α ay by omega)
        (hN as p i v has) hptr
      have hown'' := h.owner_of_ptr hw
      rw [hown] at hown''
      subst hown''
      have hw1 : as < w := by
        rcases Nat.lt_or_eq_of_le h1 with h1 | rfl
        · exact h1
        · rw [hw] at has; simp at has
      obtain ⟨ws, hws, hwsa⟩ := h.exists_anchor_of_later_ptr has hw hw1
      have hks := keyPos_anchor hwsa
      have h3 := nptr_mono (α := α) (show ws + 1 ≤ w + 1 by omega)
      have h4 := nptr_mono (α := α) (show w + 1 ≤ tsOf α ay by omega)
      rw [hks, hky] at hlt
      have := WithTop.coe_lt_coe.1 hlt
      omega
    · obtain ⟨hc', hcev⟩ := getElem_of_getElem? hc
      obtain ⟨rr, h1, h2, -, -, h3⟩ := h.low_ret hy hc' hc1 (by rw [hcev]; rfl)
      exact ⟨rr, by omega, h3⟩

end IsCtrl

end Podc.WritableObjects
