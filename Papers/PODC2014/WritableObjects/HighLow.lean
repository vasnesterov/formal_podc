import Papers.PODC2014.WritableObjects.Order

/-!
# High-level calls and their operations on the base objects

Each operation on a base object `A[i]` (invoked at position `a` by `p`) belongs to exactly one
call of `WT` (`hidAt p a`, its instance in the high-level history); conversely every completed
call has invoked exactly one operation on a base object, with a matching response
(`completed_high`). We also prove that no `SWrite` overlaps another operation on the same base
object ((4.1) in the paper; `writesIsolated`).
-/

set_option linter.unusedSectionVars false

namespace Podc.WritableObjects

open Cslib.SharedMemory

variable {P ι : Type} {T : ObjSpec} {W : Writable T} {owner : ι → P}
  {α : List (Ev P ι T)} {σ : P → ℕ → PSt ι T} [DecidableEq P] [DecidableEq ι]

variable (W) in
/-- Number of high-level invocations of `p` before position `t`. -/
def cntH (α : List (Ev P ι T)) (p : P) (t : ℕ) : ℕ :=
  (opsOf ((α.take t).filterMap (Ev.toHigh W)) p).length

variable (W) in
/-- The high-level instance of the call of `p` that is open at position `a`. -/
def hidAt (α : List (Ev P ι T)) (p : P) (a : ℕ) : OpId P := (p, cntH W α p a - 1)

variable (W) in
/-- The instance of `A[i]` invoked by `p` at position `a`. -/
def lidAt (α : List (Ev P ι T)) (i : ι) (p : P) (a : ℕ) : OpId P :=
  (p, (opsOf ((α.take a).filterMap (Ev.toLow W i)) p).length)

lemma isInv_lidAt {i : ι} {p : P} {a : ℕ} (ha : LowInvAt α i p a) :
    IsInv (Ev.toLow W i) α (lidAt W α i p a) a := by
  rcases ha with ⟨v, ha⟩ | ⟨o, ha⟩
  · obtain ⟨ha', hev⟩ := getElem_of_getElem? ha
    exact ⟨ha', W.wr v, by simp [hev, Ev.toLow, lidAt], rfl⟩
  · obtain ⟨ha', hev⟩ := getElem_of_getElem? ha
    exact ⟨ha', o, by simp [hev, Ev.toLow, lidAt], rfl⟩

lemma lidAt_eq_of_isInv {i : ι} {y : OpId P} {a : ℕ} (hy : IsInv (Ev.toLow W i) α y a) :
    lidAt W α i y.1 a = y :=
  (isInv_lidAt (lowInvAt_of_isInv hy)).inj hy

/-- Two events of `p` that are both "the last event of `p` before `t`" coincide. -/
lemma eq_of_quiet {p : P} {e e' t : ℕ} (he : e < α.length) (he' : e' < α.length)
    (hp : α[e].proc = p) (hp' : α[e'].proc = p) (hq : Quiet α p e t) (hq' : Quiet α p e' t)
    (het : e < t) (het' : e' < t) : e = e' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hq e' he' hlt het' hp'
  · exact hq' e he hlt het hp

/-- Two events of `p` that are both "the first event of `p` after `e`" coincide. -/
lemma eq_of_quiet' {p : P} {e a a' : ℕ} (ha : a < α.length) (ha' : a' < α.length)
    (hp : α[a].proc = p) (hp' : α[a'].proc = p) (hq : Quiet α p e a) (hq' : Quiet α p e a')
    (hea : e < a) (hea' : e < a') : a = a' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hq' a ha hea hlt hp
  · exact hq a' ha' hea' hlt hp'

lemma proc_of_getElem? {t : ℕ} {ev : Ev P ι T} (h : α[t]? = some ev) :
    ∃ ht : t < α.length, α[t].proc = ev.proc := by
  obtain ⟨ht, hev⟩ := getElem_of_getElem? h
  exact ⟨ht, by rw [hev]⟩

lemma lowInvAt_proc {i : ι} {p : P} {a : ℕ} (ha : LowInvAt α i p a) :
    ∃ h : a < α.length, α[a].proc = p := by
  rcases ha with ⟨v, ha⟩ | ⟨o, ha⟩ <;> exact proc_of_getElem? ha

namespace IsCtrl

variable (h : IsCtrl W owner α σ)
include h

/-- The high-level invocation of the call of an operation on a base object: the previous event
of the process, with the same operation. -/
lemma high_inv {i : ι} {p : P} {a : ℕ} (ha : LowInvAt α i p a) :
    ∃ e < a, Quiet α p e a ∧ IsInv (Ev.toHigh W) α (hidAt W α p a) e ∧
      ∃ (ha' : a < α.length) (he : e < α.length) (o : T.Op),
        Ev.toLow W i α[a] = some (.inv p o) ∧ Ev.toHigh W α[e] = some (.inv p o) := by
  obtain ⟨e, hea, hq, ha', he', o, hlo, hhi⟩ : ∃ e < a, Quiet α p e a ∧
      ∃ (ha' : a < α.length) (he : e < α.length) (o : T.Op),
        Ev.toLow W i α[a] = some (.inv p o) ∧ Ev.toHigh W α[e] = some (.inv p o) := by
    rcases ha with ⟨v, ha⟩ | ⟨o, ha⟩
    · obtain ⟨-, -, -, e, hea, he, hq⟩ := h.swinv_facts ha
      obtain ⟨he', hev⟩ := getElem_of_getElem? he
      obtain ⟨ha', hev'⟩ := getElem_of_getElem? ha
      exact ⟨e, hea, hq, ha', he', W.wr v, by simp [hev', Ev.toLow], by simp [hev, Ev.toHigh]⟩
    · obtain ⟨-, -, -, e, hea, he, hq⟩ := h.opinv_facts ha
      obtain ⟨he', hev⟩ := getElem_of_getElem? he
      obtain ⟨ha', hev'⟩ := getElem_of_getElem? ha
      exact ⟨e, hea, hq, ha', he', o, by simp [hev', Ev.toLow], by simp [hev, Ev.toHigh]⟩
  refine ⟨e, hea, hq, ⟨he', o, by simpa [hidAt] using hhi, ?_⟩, ha', he', o, hlo, hhi⟩
  have h1 := opsOf_take_eq (Ev.toHigh W) α p (s := e + 1) (t := a) (by omega) (by omega)
    (fun k hk k1 k2 => Ev.toHigh_invOf_of_ne (hq k hk (by omega) k2))
  rw [opsOf_take_succ_of_inv _ he' hhi] at h1
  simp only [hidAt, cntH]
  omega

/-- The call of an operation on a base object determines it. -/
lemma eq_of_hidAt_eq {i i' : ι} {p p' : P} {a a' : ℕ} (ha : LowInvAt α i p a)
    (ha' : LowInvAt α i' p' a') (heq : hidAt W α p a = hidAt W α p' a') : a = a' := by
  have hp : p = p' := congrArg Prod.fst heq
  subst hp
  obtain ⟨e, hea, hq, hinv, -⟩ := h.high_inv ha
  obtain ⟨e', hea', hq', hinv', -⟩ := h.high_inv ha'
  rw [heq] at hinv
  have hee := hinv.unique hinv'
  subst hee
  obtain ⟨hal, hap⟩ := lowInvAt_proc ha
  obtain ⟨hal', hap'⟩ := lowInvAt_proc ha'
  exact eq_of_quiet' hal hal' hap hap' hq hq' hea hea'

/-- The response of the operation on `A[i]` invoked at `a` is at `b`, the next event of the
process, provided the next event of the process is at `b`. -/
lemma isRet_of_quiet {i : ι} {p : P} {a b : ℕ} (ha : LowInvAt α i p a) (hb : b < α.length)
    (hab : a < b) (hbp : α[b].proc = p) (hq : Quiet α p a b) :
    IsRet (Ev.toLow W i) α (lidAt W α i p a) b := by
  obtain ⟨b', h1, h2, -, -, h4⟩ := h.low_ret (isInv_lidAt ha) hb hab hbp
  rcases Nat.lt_or_eq_of_le h2 with h2 | rfl
  · exfalso
    obtain ⟨hb4, rv4, hrv4, -⟩ := h4
    have := Ev.toLow_eq_ret hrv4
    exact hq b' hb4 h1 h2 (by rw [this]; rfl)
  · exact h4

/-- **Completed calls.** A completed high-level instance `x` (returning at `r`) has invoked an
operation on some base object `A[i]` at a position `a` (`x = hidAt p a`), whose response comes
before `r`; its timestamp key is at most `TS_Ptr(r)`; a `Write(v)` returns `wresp v`, an `Exec`
returns the response of its `Oper`. -/
lemma completed_high {x : OpId P} {r : ℕ} (hr : IsRet (Ev.toHigh W) α x r) :
    ∃ i a c, LowInvAt α i x.1 a ∧ hidAt W α x.1 a = x ∧ a < c ∧ c < r ∧
      IsRet (Ev.toLow W i) α (lidAt W α i x.1 a) c ∧ keyPos α a ≤ nptr α r ∧
      (∀ v rv, α[a]? = some (.swinv x.1 i v) → respOf (highH W α) x = some rv →
        rv = W.wresp v) ∧
      (∀ o rv, α[a]? = some (.opinv x.1 i o) → respOf (highH W α) x = some rv →
        respOf (lowH W i α) (lidAt W α i x.1 a) = some rv) := by
  obtain ⟨hr', rv, hrev, hcnt⟩ := hr
  have hrev' := Ev.toHigh_eq_ret hrev
  have hrr : α[r]? = some (.hret x.1 rv) := by rw [List.getElem?_eq_getElem hr', hrev']
  have hresp : respOf (highH W α) x = some rv :=
    (respOf_iff (Ev.toHigh W) α x rv).2 ⟨r, hr', hrev, hcnt⟩
  have hcH := h.count_high x.1 (t := r) (by omega)
  obtain ⟨-, hcase⟩ := h.hret_facts hrr
  rcases hcase with ⟨v₀, hσr, hrv, w, hwr, f, hw, hqw⟩ | ⟨hσr, c, hcr, i, hc, hqc, hσc⟩
  · -- a `Write`
    obtain ⟨v, hσw, hσw1, b, hbw, ⟨rb, hb⟩, hqb, a, hab, ha, hqa⟩ := h.ptr_facts hw
    have hσeq : σ x.1 r = σ x.1 (w + 1) :=
      h.const (by omega) (by omega) (fun k hk k1 k2 => hqw k hk (by omega) k2)
    rw [hσr, hσw1] at hσeq
    cases hσeq
    have hanc : WAnchor α a w := ⟨x.1, f, v₀, ha, hw, b, hab, hbw, ⟨rb, hb⟩, hqa, hqb⟩
    have hlow : LowInvAt α f x.1 a := Or.inl ⟨v₀, ha⟩
    obtain ⟨hal, hev_a⟩ := getElem_of_getElem? ha
    obtain ⟨hbl, hev_b⟩ := getElem_of_getElem? hb
    obtain ⟨hwl, hev_w⟩ := getElem_of_getElem? hw
    refine ⟨f, a, b, hlow, ?_, hab, by omega, ?_, ?_, ?_, ?_⟩
    · -- the instance
      have h1 := opsOf_take_eq (Ev.toHigh W) α x.1 (s := a) (t := r) (by omega) (by omega)
        (fun k hk k1 k2 => by
          by_cases hp : α[k].proc = x.1
          · rcases lt_trichotomy k b with hkb | rfl | hkb
            · rcases Nat.lt_or_eq_of_le k1 with k1 | rfl
              · exact absurd hp (hqa k hk k1 hkb)
              · simp [hev_a, Ev.toHigh]
            · simp [hev_b, Ev.toHigh]
            · rcases lt_trichotomy k w with hkw | rfl | hkw
              · exact absurd hp (hqb k hk hkb hkw)
              · simp [hev_w, Ev.toHigh]
              · exact absurd hp (hqw k hk hkw k2)
          · exact Ev.toHigh_invOf_of_ne hp)
      have hb' : (σ x.1 r).busy = 1 := by rw [hσr]; rfl
      simp only [hidAt, cntH]
      ext
      · rfl
      · simp only; omega
    · exact h.isRet_of_quiet hlow hbl hab (by rw [hev_b]; rfl) hqa
    · rw [keyPos_anchor hanc]
      exact WithTop.coe_le_coe.2 (nptr_mono (by omega))
    · intro v' rv' ha' hrv'
      rw [ha] at ha'
      simp only [Option.some.injEq, Ev.swinv.injEq] at ha'
      obtain ⟨-, -, rfl⟩ := ha'
      rw [hresp] at hrv'
      cases hrv'
      exact hrv
    · intro o rv' ha' _
      rw [ha] at ha'; simp at ha'
  · -- an `Exec`
    obtain ⟨hcl, hev_c⟩ := getElem_of_getElem? hc
    obtain ⟨t, htc, htl, hqt, hs⟩ := h.prev (p := x.1) (t := c) (by omega) (by rw [hσc]; simp)
    rw [hσc] at hs
    generalize hev : α[t] = ev at hs
    generalize σ x.1 t = st at hs
    cases hs with
    | opinv o _ =>
    have ht : α[t]? = some (.opinv x.1 i o) := by rw [List.getElem?_eq_getElem htl, hev]
    have hlow : LowInvAt α i x.1 t := Or.inr ⟨o, ht⟩
    have hlr : IsRet (Ev.toLow W i) α (lidAt W α i x.1 t) c :=
      h.isRet_of_quiet hlow hcl htc (by rw [hev_c]; rfl) hqt
    refine ⟨i, t, c, hlow, ?_, htc, hcr, hlr, ?_,
      fun v rv' ht' _ => by rw [ht] at ht'; simp at ht', fun o' rv' _ hrv' => ?_⟩
    · have h1 := opsOf_take_eq (Ev.toHigh W) α x.1 (s := t) (t := r) (by omega) (by omega)
        (fun k hk k1 k2 => by
          by_cases hp : α[k].proc = x.1
          · rcases lt_trichotomy k c with hkc | rfl | hkc
            · rcases Nat.lt_or_eq_of_le k1 with k1 | rfl
              · exact absurd hp (hqt k hk k1 hkc)
              · simp [hev, Ev.toHigh]
            · simp [hev_c, Ev.toHigh]
            · exact absurd hp (hqc k hk hkc k2)
          · exact Ev.toHigh_invOf_of_ne hp)
      have hb' : (σ x.1 r).busy = 1 := by rw [hσr]; rfl
      simp only [hidAt, cntH]
      ext
      · rfl
      · simp only; omega
    · rw [keyPos_opinv ht]
      exact WithTop.coe_le_coe.2 (nptr_mono (by have := tsOf_le α t; omega))
    · rw [hresp] at hrv'
      cases hrv'
      obtain ⟨-, -, -, h2⟩ := hlr
      exact (respOf_iff (Ev.toLow W i) α _ rv).2 ⟨c, hcl, by simp [hev_c, Ev.toLow, lidAt], h2⟩

/-- The timestamp key of a call is not smaller than `TS_Ptr` at its invocation. -/
lemma nptr_le_keyPos (hC : CondC α) {i : ι} {p : P} {a e : ℕ} (ha : LowInvAt α i p a)
    (he : IsInv (Ev.toHigh W) α (hidAt W α p a) e) : (nptr α e : WithTop ℕ) ≤ keyPos α a := by
  obtain ⟨e₀, hea, hq, hinv, -⟩ := h.high_inv ha
  have hee := he.unique hinv
  subst hee
  rcases ha with ⟨v, ha⟩ | ⟨o, ha⟩
  · by_cases hw : ∃ w, WAnchor α a w
    · obtain ⟨w, hw⟩ := hw
      rw [keyPos_anchor hw]
      exact WithTop.coe_le_coe.2 (nptr_mono (by have := hw.lt; omega))
    · rw [keyPos_top ha hw]; exact le_top
  · rw [keyPos_opinv ha]
    have hcpt := cpt_tsOf (h.exists_cpt hC ha)
    obtain ⟨⟨e', o', he', hq', hts⟩, hle, -⟩ := hcpt.facts ha
    obtain ⟨hel, hep⟩ := proc_of_getElem? he'
    obtain ⟨hel0, o0, hlab0, -⟩ := he
    have hep0 : α[e].proc = p := by
      rcases Ev.toHigh_eq_inv hlab0 with ⟨v0, h1, -⟩ | h1 <;> rw [h1] <;> rfl
    have := eq_of_quiet hel hel0 hep hep0 hq' hq (by omega) hea
    subst this
    exact WithTop.coe_le_coe.2 (nptr_mono (by omega))

/-- (4.1) of the paper: no `SWrite` on `A[i]` overlaps any other operation on `A[i]`. -/
lemma writesIsolated (hC : CondC α) (i : ι) : WritesIsolated W (lowH W i α) := by
  intro x y hxy ⟨v, hx⟩ hy
  unfold lowH at hx hy ⊢
  obtain ⟨ax, hax, hlab, hcnt⟩ := (opOf_iff _ α x _).1 hx
  have hix : IsInv (Ev.toLow W i) α x ax := ⟨hax, _, hlab, hcnt⟩
  obtain ⟨ay, hiy⟩ := (invoked_iff _ α y).1 hy
  have hne : ax ≠ ay := by
    rintro rfl; exact hxy (hix.inj hiy)
  obtain ⟨v', hsx⟩ : ∃ v', α[ax]? = some (.swinv x.1 i v') := by
    rcases Ev.toLow_eq_inv hlab with ⟨v', h1, -⟩ | h1
    · exact ⟨v', by rw [List.getElem?_eq_getElem hax, h1]⟩
    · have := (h.opinv_facts (by rw [List.getElem?_eq_getElem hax, h1])).2.2.1 v
      exact absurd rfl this
  have hownx := (h.swinv_facts hsx).1
  rcases lowInvAt_of_isInv hiy with ⟨v'', hsy⟩ | ⟨o, hoy⟩
  · have hp : y.1 = x.1 := by rw [← (h.swinv_facts hsy).1, hownx]
    obtain ⟨hayl, hayp⟩ := proc_of_getElem? hsy
    obtain ⟨haxl, haxp⟩ := proc_of_getElem? hsx
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨r, h1, h2, -, ⟨r', hr⟩, h3⟩ := h.low_ret hix hayl hlt (by rw [hayp, hp]; rfl)
      have hr2 : r < ay := by
        rcases Nat.lt_or_eq_of_le h2 with h2 | rfl
        · exact h2
        · rw [hr] at hsy; simp at hsy
      exact Or.inl (precedes_of_lt h3 (fun e he => (he.unique hiy) ▸ hr2))
    · obtain ⟨r, h1, h2, -, ⟨r', hr⟩, h3⟩ := h.low_ret hiy haxl hlt (by rw [haxp, hp]; rfl)
      have hr2 : r < ax := by
        rcases Nat.lt_or_eq_of_le h2 with h2 | rfl
        · exact h2
        · rw [hr] at hsx; simp at hsx
      exact Or.inr (precedes_of_lt h3 (fun e he => (he.unique hix) ▸ hr2))
  · have hcpt := cpt_tsOf (h.exists_cpt hC hoy)
    obtain ⟨-, hts, -, hno⟩ := hcpt.facts hoy
    rcases hno ax x.1 v' hsx with ⟨b, r, h1, h2, hb⟩ | ⟨c, r, h1, h2, hc⟩
    · obtain ⟨hbl, hbp⟩ := proc_of_getElem? hb
      obtain ⟨r', h3, h4, -, -, h5⟩ := h.low_ret hix hbl h1 hbp
      exact Or.inl (precedes_of_lt h5 (fun e he => (he.unique hiy) ▸ (by omega)))
    · obtain ⟨hcl, hcp⟩ := proc_of_getElem? hc
      obtain ⟨r', h3, h4, -, -, h5⟩ := h.low_ret hiy hcl h1 hcp
      exact Or.inr (precedes_of_lt h5 (fun e he => (he.unique hix) ▸ (by omega)))

end IsCtrl

end Podc.WritableObjects
