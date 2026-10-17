import Papers.PODC2020.DetectableSpace.Alg1Step

/-!
# Algorithm 1: preservation of the invariant by the writes to `A` (lines 2, 10 / 24)
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

attribute [local simp] LC LCW LCR Ph Dec Kd vw valOf progOf at20b bitOf Loc.stage Loc.isDec
  Loc.prog Loc.kd Loc.is20b Loc.is12 Loc.info

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n] {v₀ : V}
variable {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}

/-- Frame for the per-process invariant when bits of `p`'s row are only set. -/
lemma PI.frame_mono {p : Fin n} {st : St V n} {m : Pv V n} {s : ℕ} {wr : Bool} {wc : ℕ}
    {rv : ℕ → Trip V n} {sh sh' : Sh V n} {inL : ℕ → Prop}
    (h : PI v₀ p st m s wr wc rv sh inL) (hR : sh'.R = sh.R)
    (hA : ∀ x y, sh.A (p, x, y) = true → sh'.A (p, x, y) = true)
    (hcl : Ph 2 st m → bitOf v₀ sh' p st m = true → s < wc) :
    PI v₀ p st m s wr wc rv sh' inL where
  lc := h.lc
  m0 := h.m0
  m1 := h.m1
  m2 := h.m2
  mr := h.mr
  f1 := h.f1
  f1w := h.f1w
  f2a := h.f2a
  f2b := h.f2b
  d := h.d
  cl1 := hcl
  c2 h1 h2 := by
    obtain ⟨c1, c2⟩ := h.c2 h1 h2
    refine ⟨?_, fun h3 => hA _ _ (c2 h3)⟩
    rw [hR]
    rcases c1 with c1 | c1
    · exact .inl c1
    · exact .inr (hA _ _ c1)

lemma pv_selfA (C : Cfg1 V v₀ n) (r : Fin n) : C.pv = Function.update C.pv r (C.pv r) :=
  (Function.update_eq_self r C.pv).symm

/-- Line 2. -/
theorem step_w2 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} (hr : C.ps r = .run a o b (.w2 v tr)) : StepOK C h (.step r) := by
  rw [StepOK, step1_sh hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil, pv_selfA C r]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, hm1, -, -, hf1, hf1w, hf2a, hf2b, -, -, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, rfl, hcp, hres, hwr⟩, -⟩ := hlc
  have hrow : ∀ p, p ≠ r → ∀ x y,
      (Function.update C.sh.A (r, tr.2.1, !tr.2.2) false) (p, x, y) = C.sh.A (p, x, y) := by
    intro p hp x y
    rw [Function.update_of_ne]
    intro he; simp only [Prod.mk.injEq] at he; exact hp he.1
  apply hI.localSh r { C.sh with A := Function.update C.sh.A (r, tr.2.1, !tr.2.2) false } _ _
    (g.s r) rfl
  · rintro a' o' b' l' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hcp, hres, hwr]
    · simp
    · intro a' v'' b' l' h1 _ h3 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact hm1 _ _ _ _ rfl (by simp) h3 (by omega)
    · intro a' v'' b' l' _ h2
      simp [hcp, hwr] at h2
    · simp
    · intro _ k hk1 hk2 hk3
      simpa using hf1 (by simp) k hk1 hk2 hk3
    · exact hf1w
    · intro _
      simpa using hf2a (by simp)
    · intro _
      simpa using hf2b (by simp)
    · simp [hcp]
    · intro _ hb; simp at hb
    · simp [hwr]
  · intro p hp
    exact (hI.pi p).frame v₀ rfl (fun x y => hrow p hp x y) (fun _ _ _ _ _ => Iff.rfl)
  · rintro a' o' b' l' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    left; exact ⟨_, _, _, hr, by simpa using h2⟩
  · rintro a' v'' b' l' h1 _ h3 _
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, -, -, -⟩ := h1
    exact ⟨_, _, _, hr, h3⟩
  · exact hI.f3 r
  · intro p hp hk hb
    have hb0 : bitOf v₀ C.sh p (C.ps p) (C.pv p) = false := by
      simpa only [bitOf, hrow p hp] using hb
    have := hI.kk p hk hb0
    by_cases hq : (vw v₀ (C.ps p) (C.pv p)).1.2.1 = r
    · rw [hq] at this ⊢
      simp only [Function.update_self]
      rw [hr] at this
      obtain ⟨ka, -, -⟩ := this
      exact ⟨ka, by simp [hcp], by simp [hcp]⟩
    · simp only [Function.update_of_ne hq]
      exact this
  · intro hk; simp [hwr] at hk

/-- Line 10 (= 24), core: the next local state is `l'`. -/
theorem step_w9_core (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} {i : Fin n} (hr : C.ps r = .run a (.write v) b (.w9 v tr mt i))
    (l' : Loc V n) (hl' : LCW v (g.wr r) b (C.pv r) l') (hdec : l'.isDec) (hst : l'.stage = 0)
    (hinfo : ∀ m : Pv V n, l'.info (dflt v₀) m = (tr, mt)) (hkd : ¬ l'.kd) (h20 : ¬ l'.is20b)
    (h12 : ¬ l'.is12) (hprog : ∀ p : Fin n, i.val < p.val → l'.prog n ≤ p.val) :
    Inv v₀ ⟨{ C.sh with A := Function.update C.sh.A (i, r, mt) true },
      Function.update C.pv r (C.pv r), Function.update C.ps r (.run a (.write v) b l'), C.cnt⟩
      ⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩ h L := by
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -, -, hm2, -, hf1, hf1w, hf2a, hf2b, hd, hcl1, -⟩ := hp
  obtain ⟨⟨-, hcp, hres⟩, hcp2, hwrcp, hres2, hrd, htt1, htt2⟩ := hlc
  have hrd' : (C.pv r).rd = some (mt, tr) := by simpa [hcp] using hrd
  have hlt : g.s r < g.wc := hd (by simp)
  have hvw : ∀ m : Pv V n, vw v₀ (.run a (.write v) b l') m = (tr, mt) := fun m => by
    simp only [vw]; exact hinfo m
  have hph : ∀ k, Ph k (.run a (.write v) b l' : St V n) (C.pv r) := by
    intro k; simp only [Ph]; right; omega
  have hdec' : Dec (.run a (.write v) b l' : St V n) (C.pv r) := by simp only [Dec]; exact .inl hdec
  have hf1' := hf1 (by simp [hcp])
  simp only [valOf, vw, Loc.info] at hf1'
  -- bits are only set
  have hmono : ∀ x, C.sh.A x = true → (Function.update C.sh.A (i, r, mt) true) x = true := by
    intro x hx
    by_cases he : x = (i, r, mt)
    · subst he; simp
    · rw [Function.update_of_ne he]; exact hx
  apply hI.localSh r { C.sh with A := Function.update C.sh.A (i, r, mt) true } _ _ (g.s r) rfl
  · rintro a' o' b' l'' h1
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, -⟩ := h1
    exact ⟨_, _, hr⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [LC]
      refine ⟨hl', hcp2, hwrcp, hres2, ?_, ?_, ?_⟩
      · intro _; rw [hinfo]; exact hrd'
      · intro _ h2; omega
      · rintro (h3 | h3)
        · exact absurd h3 h12
        · simp [hres] at h3
    · intro a' v' h1
      simp only [PSt.run.injEq] at h1
      obtain ⟨-, -, -, rfl⟩ := h1
      simp [Loc.isDec] at hdec
    · intro _ _ _ _ _ _ _ h4; omega
    · intro a' v'' b' l'' h1 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      exact hm2 _ _ _ _ rfl (.inr (by simp))
    · intro _ _ _ h1; simp at h1
    · intro _ k hk1 hk2 hk3
      rw [hvw]; exact hf1' k hk1 hk2 hk3
    · exact hf1w
    · intro _; rw [hvw]; simpa [hcp] using hf2a (by simp [hcp])
    · intro _; rw [hvw]; simpa [hcp] using hf2b (by simp [hcp])
    · intro _; exact hlt
    · intro _ _; exact hlt
    · intro _ h2; omega
  · intro p hp
    refine (hI.pi p).frame_mono rfl (fun x y hx => hmono _ hx) ?_
    intro h2 hb
    by_cases he : (p, (vw v₀ (C.ps p) (C.pv p)).1.2.1, !(vw v₀ (C.ps p) (C.pv p)).1.2.2) =
      (i, r, mt)
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, hq, ht⟩ := he
      -- `p`'s line-1 read was of a write of `r` with the other toggle
      have hpi := hI.pi p
      obtain ⟨hs, hrv⟩ := hpi.f2a (ph21 h2)
      by_contra hcon
      have hle : g.s r < g.s p := by omega
      obtain ⟨-, he2⟩ := hf1' (g.s p) hle hs (by rw [hrv, hq])
      have : (vw v₀ (C.ps p) (C.pv p)).1.2.2 = mt := by rw [← hrv, he2]
      rw [this] at ht
      cases mt <;> simp at ht
    · have hb0 : bitOf v₀ C.sh p (C.ps p) (C.pv p) = true := by
        simp only [bitOf] at hb ⊢
        rwa [Function.update_of_ne he] at hb
      exact (hI.pi p).cl1 h2 hb0
  · rintro a' o' b' l'' x h1 h2
    simp only [PSt.run.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    rcases h2 with h2 | h2
    · simp [hres] at h2
    · subst h2; simp [Loc.isDec] at hdec
  · rintro a' v'' b' l'' _ _ h3 _
    omega
  · exact hI.f3 r
  · intro p hp hk hb
    have hb0 : bitOf v₀ C.sh p (C.ps p) (C.pv p) = false := by
      cases hc : bitOf v₀ C.sh p (C.ps p) (C.pv p)
      · rfl
      · have := hmono _ hc; simp only [bitOf] at this hb; rw [this] at hb; exact absurd hb (by simp)
    have := hI.kk p hk hb0
    by_cases hq : (vw v₀ (C.ps p) (C.pv p)).1.2.1 = r
    · rw [hq] at this ⊢
      simp only [Function.update_self]
      rw [hr] at this
      obtain ⟨ka, kb, kc⟩ := this
      refine ⟨ka, fun _ h2 => kb (by simp [hcp]) (by rw [← h2, hvw]; simp), fun _ h2 => ?_⟩
      have h2' : mt = !(vw v₀ (C.ps p) (C.pv p)).1.2.2 := by rw [hvw] at h2; exact h2
      obtain ⟨kc1, kc2⟩ := kc (by simp) (by simpa using h2')
      refine ⟨by rw [hvw]; simpa using kc1, ?_⟩
      have hne : i.val ≠ p.val := by
        intro hip
        have hip' : i = p := Fin.ext hip
        subst hip'
        have : bitOf v₀ { C.sh with A := Function.update C.sh.A (i, r, mt) true } i (C.ps i)
            (C.pv i) = true := by
          simp only [bitOf]
          rw [hq, h2']
          simp
        rw [this] at hb; exact absurd hb (by simp)
      simp only [progOf, Loc.prog] at kc2 ⊢
      exact hprog p (by omega)
    · simp only [Function.update_of_ne hq]
      exact this
  · intro hk
    simp only [Kd] at hk
    rcases hk with hk | hk
    · exact absurd hk hkd
    · omega

/-- Line 10 (= 24). -/
theorem step_w9 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {v : V}
    {tr : Trip V n} {mt : Bool} {i : Fin n} (hr : C.ps r = .run a o b (.w9 v tr mt i)) :
    StepOK C h (.step r) := by
  rw [StepOK, step1_sh hr rfl]
  refine ⟨⟨g.wc, g.rv, Function.update g.s r (g.s r), g.wr⟩, L, ?_⟩
  rw [List.append_nil, pv_selfA C r]
  dsimp only
  have hp := hI.pi r
  rw [hr] at hp
  obtain ⟨hlc, -⟩ := hp
  cases o with
  | read => simp at hlc
  | write v' =>
  obtain ⟨⟨rfl, hcp, hres⟩, -⟩ := hlc
  split_ifs with hi
  · refine step_w9_core hI hr _ ⟨rfl, hcp, hres⟩ (by simp [Loc.isDec]) rfl (fun _ => rfl)
      (by simp [Loc.kd]) (by simp [Loc.is20b]) (by simp [Loc.is12]) ?_
    intro p hp; simp [Loc.prog]; omega
  · refine step_w9_core hI hr _ ⟨rfl, hcp, hres⟩ (by simp [Loc.isDec]) rfl (fun _ => rfl)
      (by simp [Loc.kd]) (by simp [Loc.is20b]) (by simp [Loc.is12]) ?_
    intro p hp; exfalso; have := p.isLt; omega

end Alg1

end Papers.PODC2020.DetectableSpace
