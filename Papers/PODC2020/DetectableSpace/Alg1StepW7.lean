import Papers.PODC2020.DetectableSpace.Alg1Step

/-!
# Algorithm 1: preservation of the invariant by the write to `R` (line 7)

At the write of `R` by `r`, the writes that have executed line 1 since the last write to `R`
and have not written `R` (the *clean* ones, `s p = wc`) are linearized speculatively,
immediately before `r`'s write; a speculative entry of `r` itself (if `r`'s line-1 read was
followed by another write: ABA) is removed and `r` is linearized at its write.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

attribute [local simp] LC LCW LCR Ph Dec Kd vw valOf progOf at20b bitOf Loc.stage Loc.isDec
  Loc.prog Loc.kd Loc.is20b Loc.is12 Loc.info

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n] {v₀ : V}
variable {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}

/-- Running operations have distinct identifiers. -/
lemma Inv.run_inj (hI : Inv v₀ C g h L) {p q : Fin n} {a : ℕ} {o o' : RWOp V} {b b' : Bool}
    {l l' : Loc V n} (hp : C.ps p = .run a o b l) (hq : C.ps q = .run a o' b' l') : p = q :=
  (hI.uniq a p o q o' (hI.run p a o b l hp).1 (hI.run q a o' b' l' hq).1).1

/-- Committed responses of a write are its value. -/
lemma Inv.write_ok (hI : Inv v₀ C g h L) {p : Fin n} {a : ℕ} {v : V} {b : Bool} {l : Loc V n}
    (hp : C.ps p = .run a (.write v) b l) (x : V) (hx : rho v₀ C h a x) : x = v := by
  rcases hx with ⟨c, hc⟩ | ⟨q, o, b', l', hq, hx⟩
  · exact absurd hc ((hI.run p a _ b l hp).2 _ c)
  · have hpq := hI.run_inj hp hq
    subst hpq
    rw [hp] at hq
    simp only [PSt.run.injEq] at hq
    obtain ⟨-, rfl, rfl, rfl⟩ := hq
    have hlc := (hI.pi p).lc
    rw [hp] at hlc
    obtain ⟨hlcw, -, -, hres, -⟩ := hlc
    rcases hx with hx | hx
    · exact (hres x hx).1
    · subst hx; simp at hlcw

open Classical in
/-- Entry of a clean write of `p` (if any). -/
noncomputable def specF (C : Cfg1 V v₀ n) (g : Ghost V n) (r p : Fin n) : Option (ℕ × RWOp V) :=
  if p ≠ r ∧ Ph 1 (C.ps p) (C.pv p) ∧ g.wr p = false ∧ (C.pv p).cp ≤ 1 ∧ g.s p = g.wc then
    match C.ps p with
    | .run a o _ _ => some (a, o)
    | .idle => none
  else none

/-- The clean writes, linearized speculatively before the write of `r` to `R`. -/
noncomputable def specs (C : Cfg1 V v₀ n) (g : Ghost V n) (r : Fin n) : List (ℕ × RWOp V) :=
  (List.finRange n).filterMap (specF C g r)

lemma specF_some {r p : Fin n} {y : ℕ × RWOp V} : specF C g r p = some y ↔
    (p ≠ r ∧ Ph 1 (C.ps p) (C.pv p) ∧ g.wr p = false ∧ (C.pv p).cp ≤ 1 ∧ g.s p = g.wc) ∧
      ∃ b l, C.ps p = .run y.1 y.2 b l := by
  unfold specF
  by_cases hc : p ≠ r ∧ Ph 1 (C.ps p) (C.pv p) ∧ g.wr p = false ∧ (C.pv p).cp ≤ 1 ∧ g.s p = g.wc
  · rw [if_pos hc]
    constructor
    · intro hy
      refine ⟨hc, ?_⟩
      revert hy
      cases hps : C.ps p with
      | idle => intro hy; exact absurd hy (by simp only [reduceCtorEq, not_false_eq_true])
      | run a o b l =>
        intro hy
        simp only [Option.some.injEq] at hy
        subst hy
        exact ⟨b, l, rfl⟩
    · rintro ⟨-, b, l, hps⟩
      rw [hps]
  · rw [if_neg hc]
    simp only [reduceCtorEq, false_iff, not_and]
    intro h1 _
    exact absurd h1 hc

lemma mem_specs {r : Fin n} {y : ℕ × RWOp V} : y ∈ specs C g r ↔
    ∃ p, (p ≠ r ∧ Ph 1 (C.ps p) (C.pv p) ∧ g.wr p = false ∧ (C.pv p).cp ≤ 1 ∧ g.s p = g.wc) ∧
      ∃ b l, C.ps p = .run y.1 y.2 b l := by
  simp only [specs, List.mem_filterMap, List.mem_finRange, true_and, specF_some]

lemma specs_nodup (hI : Inv v₀ C g h L) (r : Fin n) : ((specs C g r).map Prod.fst).Nodup := by
  unfold specs
  rw [List.map_filterMap]
  refine (List.nodup_finRange n).filterMap ?_
  intro p p' x hx hx'
  simp only [Option.mem_def, Option.map_eq_some_iff] at hx hx'
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hx'
  obtain ⟨-, b, l, hq⟩ := specF_some.1 hy
  obtain ⟨-, b', l', hq'⟩ := specF_some.1 hy'
  rw [hyy] at hq'
  exact hI.run_inj hq hq'

lemma kd_of_wr {st : St V n} {m : Pv V n} {wr : Bool} (hlc : LC v₀ st m wr) (hw : wr = true)
    (hc : m.cp = 1) : Kd st m wr := by
  match st, hlc with
  | .idle, hlc => simp [LC] at hlc; simp [hlc] at hw
  | .run a .read b l, hlc => simp only [LC] at hlc; simp [hlc.2] at hw
  | .run a (.write v) b l, _ => simp only [Kd]; exact .inr ⟨hw, hc⟩

lemma legalG_writes {ρ : ℕ → V → Prop} : ∀ (M : List (ℕ × RWOp V)) (σ : V),
    (∀ x ∈ M, ∃ w, x.2 = .write w ∧ ∀ y, ρ x.1 y → y = w) → LegalG ρ σ M := by
  intro M
  induction M with
  | nil => intro _ _; trivial
  | cons x M ih =>
    intro σ hM
    obtain ⟨c, o⟩ := x
    obtain ⟨w, hw, hρ⟩ := hM (c, o) (by simp)
    simp only at hw
    subst hw
    exact ⟨hρ, ih w (fun y hy => hM y (by simp [hy]))⟩

/-- Removing the (speculative) entry of the writer `r`. -/
lemma Inv.rm_self (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {v : V} {b : Bool} {l : Loc V n}
    (hr : C.ps r = .run a (.write v) b l) (hwr : g.wr r = false) (hcp : (C.pv r).cp ≤ 1) :
    DL h (rho v₀ C h) v₀ (rmId a L) ∧ Good (SS v₀ C g) (rmId a L) ∧
      fin v₀ (rmId a L) = fin v₀ L := by
  by_cases ha : a ∈ L.map Prod.fst
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    obtain ⟨L₁, L₂, v₁, b', w, hL⟩ := hI.good.decomp hy ⟨r, v, b, l, hr, hwr, hcp⟩
    have hnd := hI.dl.nodup
    rw [hL] at hnd
    have e := rmId_split hnd
    have hgood := hI.good
    have hleg := hI.dl.legal
    rw [hL] at hgood hleg ⊢
    rw [e]
    refine ⟨?_, hgood.erase_ww, ?_⟩
    · have hd := hI.dl
      rw [hL] at hd
      have := hd.rm y.1 (hI.run r y.1 _ b l hr).2 (by rw [e]; exact hleg.erase_ww)
      rwa [e] at this
    · exact (fin_erase_ww v₀ L₁ L₂).symm
  · rw [rmId_of_not_mem ha]
    exact ⟨hI.dl, hI.good, rfl⟩

/-- Line 7: the write to `R`. -/
theorem step_w7 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v' : V}
    {tr : Trip V n} {mt : Bool} (hr : C.ps r = .run a o b (.w7 v' tr mt)) :
    StepOK C h (.step r) := by
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, -, -, -, hf1, hf1w, hf2a, hf2b, -, hcl1, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v =>
  obtain ⟨⟨rfl, rfl, hcp, hres, hwr⟩, hcp2, -, hres2, hrd, htt1, -⟩ := hlc
  have hT : (C.pv r).T = mt := by simpa [hcp] using htt1
  have hrd' : (C.pv r).rd = some (mt, tr) := by simpa [hcp] using hrd
  have hf2a' : g.s r ≤ g.wc ∧ g.rv (g.s r) = tr := by simpa [hcp] using hf2a
  have hf2b' : tr.2.1 = r → tr.2.2 ≠ mt := by simpa [hcp] using hf2b
  rw [StepOK, step1_sh hr rfl]
  set rv' := Function.update g.rv (g.wc + 1) (v', r, mt) with hrv'
  set g' : Ghost V n := ⟨g.wc + 1, rv', g.s, Function.update g.wr r true⟩ with hg'
  set L' := rmId a L ++ (specs C g r ++ [(a, .write v')]) with hL'
  refine ⟨g', L', ?_⟩
  rw [List.append_nil]
  dsimp only
  set C' : Cfg1 V v₀ n := ⟨{ C.sh with R := (v', r, mt) }, C.pv,
    Function.update C.ps r (.run a (.write v') false (.w8 v' tr mt)), C.cnt⟩ with hC'
  have hrvo : ∀ k, k ≤ g.wc → rv' k = g.rv k := by
    intro k hk; rw [hrv', Function.update_of_ne (by omega)]
  have hrvn : rv' (g.wc + 1) = (v', r, mt) := by rw [hrv', Function.update_self]
  obtain ⟨hdrm, hgrm, hfrm⟩ := hI.rm_self hr hwr (by omega)
  -- other processes' operations are not `a`
  have hne_a : ∀ p a' o' b' l', p ≠ r → C.ps p = .run a' o' b' l' → a' ≠ a := by
    intro p a' o' b' l' hp hps hpa
    subst hpa
    exact hp (hI.run_inj hps hr)
  have hspec_ne : ∀ y ∈ specs C g r, y.1 ≠ a := by
    intro y hy
    obtain ⟨p, ⟨hpr, -⟩, b', l', hps⟩ := mem_specs.1 hy
    exact hne_a p _ _ _ _ hpr hps
  have hspec_w : ∀ y ∈ specs C g r, ∃ w, y.2 = .write w ∧ ∀ x, rho v₀ C h y.1 x → x = w := by
    intro y hy
    obtain ⟨p, ⟨-, hph, -⟩, b', l', hps⟩ := mem_specs.1 hy
    obtain ⟨c, o⟩ := y
    cases o with
    | read => rw [hps] at hph; simp at hph
    | write w => exact ⟨w, rfl, hI.write_ok hps⟩
  have hspec_notL : ∀ y ∈ specs C g r, y.1 ∉ L.map Prod.fst := by
    intro y hy
    obtain ⟨p, ⟨-, hph, hwp, hcpp, hsp⟩, b', l', hps⟩ := mem_specs.1 hy
    obtain ⟨c, o⟩ := y
    cases o with
    | read => rw [hps] at hph; simp at hph
    | write w =>
      have := ((hI.pi p).m1 c w b' l' hps hph hwp hcpp)
      rw [this, hsp]; exact lt_irrefl _
  have hmemL' : ∀ x, x ∈ L'.map Prod.fst ↔
      (x ∈ L.map Prod.fst ∧ x ≠ a) ∨ x ∈ (specs C g r).map Prod.fst ∨ x = a := by
    intro x
    simp only [hL', List.map_append, List.mem_append, mem_ids_rmId, List.map_cons,
      List.map_nil, List.mem_singleton]
  have hrho' : ∀ c x, rho v₀ C' h c x → rho v₀ C h c x := by
    rintro c x (hx | ⟨p, o, b', l', hps, hx⟩)
    · exact .inl hx
    · by_cases hpr : p = r
      · subst hpr
        simp only [hC', Function.update_self, PSt.run.injEq] at hps
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hps
        simp [hC', hres] at hx
      · simp only [hC', Function.update_of_ne hpr] at hps
        exact .inr ⟨p, o, b', l', hps, hx⟩
  have hKQr : ∀ t (p : Fin n), KQ v₀ (.run a (.write v') false (.w8 v' tr mt) : St V n) (C.pv r)
      true t p := by
    intro t p
    exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => ⟨by simpa using hT, Nat.zero_le _⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.resid, ?_, ?_, ?_⟩
  · -- R
    show (v', r, mt) = rv' (g.wc + 1); rw [hrvn]
  · -- abs
    show fin v₀ L' = (rv' (g.wc + 1)).1
    rw [hrvn, hL', ← List.append_assoc, fin_write_last]
  · -- dl
    refine DL.weaken ?_ (fun c x hx => .inl (hrho' c x hx))
    refine hdrm.append_pending _ ?_ ?_ ?_ ?_
    · intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨p, -, b', l', hps⟩ := mem_specs.1 hy
        exact ⟨p, (hI.run p _ _ _ _ hps).1⟩
      · simp only [List.mem_singleton] at hy; subst hy
        exact ⟨r, (hI.run r _ _ _ _ hr).1⟩
    · intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨p, -, b', l', hps⟩ := mem_specs.1 hy
        exact (hI.run p _ _ _ _ hps).2
      · simp only [List.mem_singleton] at hy; subst hy
        exact (hI.run r _ _ _ _ hr).2
    · simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨hdrm.nodup, List.nodup_append.2 ⟨specs_nodup hI r, by simp, ?_⟩, ?_⟩
      · intro x hx y hy
        simp only [List.mem_singleton] at hy; subst hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
        exact hspec_ne z hz
      · intro x hx y hy
        rw [mem_ids_rmId] at hx
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
          intro he; subst he; exact hspec_notL z hz hx.1
        · exact hx.2
    · refine LegalG.append hdrm.legal (legalG_writes _ _ ?_)
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hspec_w y hy
      · simp only [List.mem_singleton] at hy; subst hy
        exact ⟨v', rfl, hI.write_ok hr⟩
  · -- good
    have hSS' : ∀ c, SS v₀ C' g' c → SS v₀ C g c := by
      rintro c ⟨p, w, b', l', hps, hw, hc⟩
      by_cases hpr : p = r
      · subst hpr; simp [hg'] at hw
      · simp only [hC', Function.update_of_ne hpr] at hps hc
        simp only [hg', Function.update_of_ne hpr] at hw
        exact ⟨p, w, b', l', hps, hw, hc⟩
    refine Good.append (hgrm.mono fun y _ hy => hSS' _ hy) (good_specs _ _ _ ?_ ?_)
    · intro y hy
      obtain ⟨w, hw, -⟩ := hspec_w y hy
      rw [hw]; trivial
    · rintro ⟨p, w, b', l', hps, hw, hc⟩
      by_cases hpr : p = r
      · subst hpr; simp [hg'] at hw
      · simp only [hC', Function.update_of_ne hpr] at hps
        exact hne_a p _ _ _ _ hpr hps rfl
  · exact hI.ids
  · exact hI.uniq
  · -- run
    intro p a' o' b' l' hps
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', Function.update_self, PSt.run.injEq] at hps
      obtain ⟨rfl, rfl, rfl, -⟩ := hps
      exact hI.run p _ _ _ _ hr
    · simp only [hC', Function.update_of_ne hpr] at hps
      exact hI.run p _ _ _ _ hps
  · exact hI.nf
  · -- pi
    intro p
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', hg', Function.update_self]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hcp, hres, hrd', hT]
      · simp
      · intro _ _ _ _ _ _ h3; simp at h3
      · intro a' v'' b' l' h1 _
        simp only [PSt.run.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        rw [hmemL']; exact .inr (.inr rfl)
      · simp
      · intro _ k hk1 hk2 hk3
        refine ⟨rfl, ?_⟩
        rcases Nat.lt_or_eq_of_le hk2 with hk2 | hk2
        · exfalso
          have := (hf1 (by simp [hcp]) k hk1 (by omega) (by rwa [hrvo k (by omega)] at hk3)).1
          simp [hwr] at this
        · subst hk2; rw [hrvn]; simp
      · intro _; omega
      · intro _; refine ⟨by omega, ?_⟩
        rw [hrvo _ hf2a'.1, hf2a'.2]; simp
      · intro _; simpa using hf2b'
      · intro _; omega
      · intro _ _; omega
      · intro _ _
        refine ⟨.inl ?_, by simp⟩
        simp only [vw, Loc.info]
        intro he
        have e1 : tr.2.1 = p := by rw [← he]
        have e2 : tr.2.2 = mt := by rw [← he]
        exact hf2b' e1 e2
    · have hpi := hI.pi p
      simp only [hC', hg', Function.update_of_ne hpr]
      refine ⟨hpi.lc, ?_, ?_, ?_, hpi.mr |> fun hmr => ?_, ?_, hpi.f1w |> fun h1 => ?_, ?_,
        hpi.f2b, fun h1 => by have := hpi.d h1; omega, fun h1 h2 => by have := hpi.cl1 h1 h2; omega,
        ?_⟩
      · intro a' w h1
        rw [hmemL']
        rintro (⟨h2, -⟩ | h2 | h2)
        · exact hpi.m0 a' w h1 h2
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h2
          obtain ⟨p', ⟨-, hph, -⟩, b', l', hps⟩ := mem_specs.1 hy
          have hpp := hI.run_inj hps h1
          subst hpp
          have hlc := hpi.lc
          rw [h1] at hlc hph
          simp only [LC, LCW] at hlc
          simp [hlc.1.2.2.1] at hph
        · exact hne_a p _ _ _ _ hpr h1 h2
      · intro a' w b' l' h1 h2 h3 h4
        rw [hmemL']
        have hs := (hpi.f2a h2).1
        constructor
        · intro _; omega
        · intro _
          rcases Nat.lt_or_eq_of_le hs with hs | hs
          · exact .inl ⟨(hpi.m1 a' w b' l' h1 h2 h3 h4).2 hs, hne_a p _ _ _ _ hpr h1⟩
          · refine .inr (.inl ?_)
            exact List.mem_map.2 ⟨(a', .write w), mem_specs.2 ⟨p, ⟨hpr, h2, h3, h4, hs⟩, b', l', h1⟩, rfl⟩
      · intro a' w b' l' h1 h2
        rw [hmemL']
        exact .inl ⟨hpi.m2 a' w b' l' h1 h2, hne_a p _ _ _ _ hpr h1⟩
      · intro a' b' l' h1 h2
        rw [hmemL']
        exact .inl ⟨hmr a' b' l' h1 h2, hne_a p _ _ _ _ hpr h1⟩
      · intro h1 k hk1 hk2 hk3
        rcases Nat.lt_or_eq_of_le hk2 with hk2 | hk2
        · rw [hrvo k (by omega)] at hk3 ⊢
          exact hpi.f1 h1 k hk1 (by omega) hk3
        · subst hk2; rw [hrvn] at hk3; exact absurd hk3.symm hpr
      · intro h2; have := h1 h2; omega
      · intro h1
        obtain ⟨h2, h3⟩ := hpi.f2a h1
        exact ⟨by omega, by rw [hrvo _ h2, h3]⟩
      · intro h1 h2
        obtain ⟨c1, c2⟩ := hpi.c2 h1 h2
        refine ⟨?_, c2⟩
        by_cases he : ((v', r, mt) : Trip V n) = (vw v₀ (C.ps p) (C.pv p)).1
        · right
          by_contra hb
          have hb' : bitOf v₀ C.sh p (C.ps p) (C.pv p) = false := by simpa using hb
          have hk := hI.kk p (by
            have hlc := hpi.lc
            exact kd_of_wr hlc h1 h2) hb'
          rw [← he] at hk
          obtain ⟨-, kb, -⟩ := hk
          rw [hr] at kb
          have := kb (by simp [hcp]) (by simp)
          simp [hwr] at this
        · exact .inl he
  · -- f3
    intro q hq hT'
    show Function.update g.wr r true q = true
    have : q = r := by
      have := hq
      simp only [hg', hrvn] at this
      exact this.symm
    subst this; simp
  · -- kk
    intro p hk hb
    have hb0 : bitOf v₀ C.sh p (C'.ps p) (C'.pv p) = false := hb
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', hg', Function.update_self] at hk hb0 ⊢
      have hk0 := hI.kk p (by rw [hr]; simp) (by rw [hr]; simpa using hb0)
      rw [hr] at hk0
      simp only [vw, Loc.info] at hk0 ⊢
      by_cases hq : tr.2.1 = p
      · rw [hq]; simp only [Function.update_self]; exact hKQr _ _
      · simp only [Function.update_of_ne hq]; exact hk0
    · simp only [hC', hg', Function.update_of_ne hpr] at hk hb0 ⊢
      have hk0 := hI.kk p hk hb0
      by_cases hq : (vw v₀ (C.ps p) (C.pv p)).1.2.1 = r
      · rw [hq]; simp only [Function.update_self]; exact hKQr _ _
      · simp only [Function.update_of_ne hq]; exact hk0

end Alg1

end Papers.PODC2020.DetectableSpace
