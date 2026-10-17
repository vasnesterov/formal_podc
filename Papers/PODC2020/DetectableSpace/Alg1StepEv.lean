import Papers.PODC2020.DetectableSpace.Alg1StepW7

/-!
# Algorithm 1: preservation of the invariant by returns, `Read`'s read of `R`, invocations and
crashes
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

attribute [local simp] LC LCW LCR Ph Dec Kd vw valOf progOf at20b bitOf Loc.stage Loc.isDec
  Loc.prog Loc.kd Loc.is20b Loc.is12 Loc.info

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n] {v₀ : V}
variable {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}

/-- PI of an idle process. -/
lemma PI.idle (p : Fin n) (s : ℕ) (wc : ℕ) (rv : ℕ → Trip V n) (sh : Sh V n) (inL : ℕ → Prop) :
    PI v₀ p .idle m s false wc rv sh inL :=
  ⟨rfl, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp⟩

/-- Generic return step. -/
theorem Inv.ret (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool}
    {x : Option V} (hr : C.ps r = .run a o b (.ret x)) (L' : LinL V)
    (hL' : ∀ c, c ≠ a → (c ∈ L'.map Prod.fst ↔ c ∈ L.map Prod.fst))
    (hdl : DL (h ++ [.res a x b]) (rho v₀ (⟨C.sh, C.pv, Function.update C.ps r .idle, C.cnt⟩ :
      Cfg1 V v₀ n) (h ++ [.res a x b])) v₀ L')
    (hgood : Good (SS v₀ (⟨C.sh, C.pv, Function.update C.ps r .idle, C.cnt⟩ : Cfg1 V v₀ n)
      ⟨g.wc, g.rv, g.s, Function.update g.wr r false⟩) L')
    (habs : fin v₀ L' = (g.rv g.wc).1) (hnf : x = none → b = true)
    (hT : (g.rv g.wc).2.1 = r → (C.pv r).T ≠ (g.rv g.wc).2.2)
    (hTk : ∀ t p, KQ v₀ (C.ps r) (C.pv r) (g.wr r) t p → (C.pv r).T ≠ t) :
    Inv v₀ (⟨C.sh, C.pv, Function.update C.ps r .idle, C.cnt⟩ : Cfg1 V v₀ n)
      ⟨g.wc, g.rv, g.s, Function.update g.wr r false⟩ (h ++ [.res a x b]) L' where
  R := hI.R
  abs := habs
  dl := hdl
  good := hgood
  ids c p o' hc := by
    rcases List.mem_append.1 hc with hc | hc
    · exact hI.ids c p o' hc
    · simp at hc
  uniq c p o' p' o'' h1 h2 := by
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h1 h2
    exact hI.uniq c p o' p' o'' h1 h2
  run p c o' b' l' hp := by
    by_cases hpr : p = r
    · subst hpr; simp at hp
    · simp only [Function.update_of_ne hpr] at hp
      obtain ⟨h1, h2⟩ := hI.run p c o' b' l' hp
      refine ⟨List.mem_append_left _ h1, fun r' c' hc => ?_⟩
      rcases List.mem_append.1 hc with hc | hc
      · exact h2 r' c' hc
      · simp only [List.mem_singleton, HEv.res.injEq] at hc
        obtain ⟨rfl, -, -⟩ := hc
        exact hpr (hI.run_inj hp hr)
  nf c hc := by
    rcases List.mem_append.1 hc with hc | hc
    · exact hI.nf c hc
    · simp only [List.mem_singleton, HEv.res.injEq] at hc
      obtain ⟨-, rfl, rfl⟩ := hc
      simp at hnf
  resid c r' c' hc := by
    rcases List.mem_append.1 hc with hc | hc
    · exact hI.resid c r' c' hc
    · simp only [List.mem_singleton, HEv.res.injEq] at hc
      obtain ⟨rfl, -, -⟩ := hc
      exact hI.ids _ _ _ (hI.run r _ _ _ _ hr).1
  pi p := by
    by_cases hpr : p = r
    · subst hpr
      simp only [Function.update_self]
      exact PI.idle p _ _ _ _ _
    · simp only [Function.update_of_ne hpr]
      refine (hI.pi p).frame v₀ rfl (fun _ _ => rfl) ?_
      intro c o' b' l' hp
      exact hL' c (fun e => by subst e; exact hpr (hI.run_inj hp hr))
  f3 q hq hT' := by
    by_cases hqr : q = r
    · subst hqr; exact absurd hT' (hT hq)
    · simp only [Function.update_of_ne hqr]; exact hI.f3 q hq hT'
  kk p hk hb := by
    by_cases hpr : p = r
    · subst hpr; simp at hk
    · simp only [Function.update_of_ne hpr] at hk hb ⊢
      have := hI.kk p hk hb
      by_cases hq : (vw v₀ (C.ps p) (C.pv p)).1.2.1 = r
      · rw [hq] at this ⊢
        simp only [Function.update_self]
        refine ⟨fun h1 => absurd h1 (hTk _ _ this), by simp, by simp⟩
      · simp only [Function.update_of_ne hq]
        exact this

/-- Weakening of committed responses at a return. -/
lemma rho_ret (_hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {x : Option V}
    (hr : C.ps r = .run a o b (.ret x)) (hres : ∀ y, x = some y → (C.pv r).res = some y) :
    ∀ c y, rho v₀ (⟨C.sh, C.pv, Function.update C.ps r .idle, C.cnt⟩ : Cfg1 V v₀ n)
      (h ++ [.res a x b]) c y → rho v₀ C h c y := by
  rintro c y (⟨c', hc⟩ | ⟨p, o', b', l', hp, hy⟩)
  · rcases List.mem_append.1 hc with hc | hc
    · exact .inl ⟨c', hc⟩
    · simp only [List.mem_singleton, HEv.res.injEq] at hc
      obtain ⟨rfl, rfl, -⟩ := hc
      exact .inr ⟨r, o, b, _, hr, .inl (hres y rfl)⟩
  · by_cases hpr : p = r
    · subst hpr; simp at hp
    · simp only [Function.update_of_ne hpr] at hp
      exact .inr ⟨p, o', b', l', hp, hy⟩

/-- Return. -/
theorem step_ret (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool}
    {x : Option V} (hr : C.ps r = .run a o b (.ret x)) : StepOK C h (.step r) := by
  rw [StepOK, step1_ret hr rfl]
  have hp := hI.pi r
  rw [hr] at hp
  have hSS : ∀ c, SS v₀ (⟨C.sh, C.pv, Function.update C.ps r .idle, C.cnt⟩ : Cfg1 V v₀ n)
      ⟨g.wc, g.rv, g.s, Function.update g.wr r false⟩ c → SS v₀ C g c := by
    rintro c ⟨p, w, b', l', hps, hw, hc⟩
    by_cases hpr : p = r
    · subst hpr; simp at hps
    · simp only [Function.update_of_ne hpr] at hps hw
      exact ⟨p, w, b', l', hps, hw, hc⟩
  cases o with
  | read =>
    obtain ⟨⟨y, rfl, hres⟩, hwr⟩ := hp.lc
    refine ⟨_, L, hI.ret hr L (fun _ _ => Iff.rfl) ?_ (hI.good.mono fun _ _ h => hSS _ h)
      hI.abs (by simp) ?_ ?_⟩
    · refine DL.weaken ?_ (fun c y' h1 => .inl (rho_ret hI hr (by simp [hres]) c y' h1))
      exact hI.dl.append_res a _ b (by simpa using hp.mr a b _ rfl (.inr (by simp [hres])))
    · intro h1 h2; have := hI.f3 r h1 h2; simp [hwr] at this
    · intro t p hk h1; have := hk.1 h1; simp [hwr] at this
  | write v =>
    obtain ⟨hlcw, hcp2, hwrcp, hres2, hrd, htt1, htt2⟩ := hp.lc
    simp only [LCW] at hlcw
    rcases hlcw with ⟨rfl, hres⟩ | ⟨rfl, rfl, hres, hwr, hcp⟩
    · obtain ⟨-, hcp⟩ := hres2 v hres
      have hrd' := hrd (by omega)
      have hT : (C.pv r).T = !(Loc.info (dflt v₀) (C.pv r) (.ret (some v))).2 := htt2 (by simp [hres])
      refine ⟨_, L, hI.ret hr L (fun _ _ => Iff.rfl) ?_ (hI.good.mono fun _ _ h => hSS _ h)
        hI.abs (by simp) ?_ ?_⟩
      · refine DL.weaken ?_ (fun c y' h1 => .inl (rho_ret hI hr (by simp [hres]) c y' h1))
        exact hI.dl.append_res a _ b (by simpa using hp.m2 a v b _ rfl (.inr (by simp [hcp])))
      · intro h1 h2
        obtain ⟨-, he⟩ := hp.f1 (by simp [hcp]) g.wc (hp.d (by simp [hcp])) le_rfl h1
        rw [he] at h2
        simp only [vw] at h2 hT
        rw [hT] at h2
        cases (Loc.info (dflt v₀) (C.pv r) (.ret (some v))).2 <;> simp at h2
      · intro t p hk h1
        obtain ⟨-, -, kc⟩ := hk
        rw [hr] at kc
        simp only [vw] at kc
        rw [h1] at hT
        have := (kc (by simp [hcp]) (by rw [hT]; cases t <;> simp)).1
        rw [h1, hT] at this
        cases t <;> simp at this
    · obtain ⟨hdrm, hgrm, hfrm⟩ := hI.rm_self hr hwr hcp
      refine ⟨_, rmId a L, hI.ret hr _ (fun c hc => by rw [mem_ids_rmId]; simp [hc]) ?_
        (hgrm.mono fun _ _ h => hSS _ h) (by rw [hfrm, hI.abs]) (fun _ => rfl) ?_ ?_⟩
      · refine DL.weaken ?_ (fun c y' h1 => .inl (rho_ret hI hr (by simp) c y' h1))
        exact hdrm.append_res a _ true (by simp [mem_ids_rmId])
      · intro h1 h2; have := hI.f3 r h1 h2; simp [hwr] at this
      · intro t p hk h1; have := hk.1 h1; simp [hwr] at this

/-- Removing the entry of a pending `Read`. -/
lemma Inv.rm_read (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {b : Bool} {l : Loc V n}
    (hr : C.ps r = .run a .read b l) :
    DL h (rho v₀ C h) v₀ (rmId a L) ∧ Good (SS v₀ C g) (rmId a L) ∧
      fin v₀ (rmId a L) = fin v₀ L := by
  by_cases ha : a ∈ L.map Prod.fst
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    have hy2 := hI.entry hr y hy rfl
    obtain ⟨L₁, L₂, hL⟩ := List.mem_iff_append.1 hy
    obtain ⟨c, o⟩ := y
    simp only at hy2
    subst hy2
    have hnd := hI.dl.nodup
    rw [hL] at hnd
    have e := rmId_split hnd
    have hgood := hI.good
    have hleg := hI.dl.legal
    rw [hL] at hgood hleg ⊢
    rw [e]
    refine ⟨?_, hgood.erase_r, (fin_erase_r v₀ L₁ L₂).symm⟩
    have hd := hI.dl
    rw [hL] at hd
    have := hd.rm c (hI.run r c _ b l hr).2 (by rw [e]; exact hleg.erase_r)
    rwa [e] at this
  · rw [rmId_of_not_mem ha]
    exact ⟨hI.dl, hI.good, rfl⟩

/-- `Read`: the read of `R` (linearization point). -/
theorem step_d1 (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool}
    (hr : C.ps r = .run a o b .d1) : StepOK C h (.step r) := by
  rw [StepOK, step1_sh hr rfl]
  have hp := hI.pi r
  rw [hr] at hp
  cases o with
  | write v => have := hp.lc; simp at this
  | read =>
  obtain ⟨hres, hwr⟩ := hp.lc
  simp only [LCR] at hres
  obtain ⟨hdrm, hgrm, hfrm⟩ := hI.rm_read hr
  set C' : Cfg1 V v₀ n := ⟨C.sh, C.pv, Function.update C.ps r (.run a .read b (.d2 C.sh.R.1)),
    C.cnt⟩ with hC'
  set L' := rmId a L ++ [(a, .read)] with hL'
  refine ⟨g, L', ?_⟩
  rw [List.append_nil]
  dsimp only
  have hmem : ∀ c, c ≠ a → (c ∈ L'.map Prod.fst ↔ c ∈ L.map Prod.fst) := by
    intro c hc
    simp [hL', mem_ids_rmId, hc]
  have hrho : ∀ c y, rho v₀ C' h c y → c ≠ a → rho v₀ C h c y := by
    rintro c y (hx | ⟨p, o', b', l', hps, hx⟩) hc
    · exact .inl hx
    · by_cases hpr : p = r
      · subst hpr
        simp only [hC', Function.update_self, PSt.run.injEq] at hps
        exact absurd hps.1.symm hc
      · simp only [hC', Function.update_of_ne hpr] at hps
        exact .inr ⟨p, o', b', l', hps, hx⟩
  have hrhoa : ∀ y, rho v₀ C' h a y → y = (g.rv g.wc).1 := by
    rintro y (⟨c, hc⟩ | ⟨p, o', b', l', hps, hx⟩)
    · exact absurd hc ((hI.run r _ _ _ _ hr).2 _ c)
    · by_cases hpr : p = r
      · subst hpr
        simp only [hC', Function.update_self, PSt.run.injEq] at hps
        obtain ⟨-, rfl, rfl, rfl⟩ := hps
        rcases hx with hx | hx
        · simp [hC', hres] at hx
        · obtain rfl : C.sh.R.1 = y := by simpa using hx
          rw [hI.R]
      · simp only [hC', Function.update_of_ne hpr] at hps
        exact absurd (hI.run_inj hps hr) hpr
  have hSS : ∀ c, SS v₀ C' g c → SS v₀ C g c := by
    rintro c ⟨p, w, b', l', hps, hw, hcc⟩
    by_cases hpr : p = r
    · subst hpr; simp [hC'] at hps
    · simp only [hC', Function.update_of_ne hpr] at hps
      exact ⟨p, w, b', l', hps, hw, hcc⟩
  refine ⟨hI.R, ?_, ?_, ?_, hI.ids, hI.uniq, ?_, hI.nf, hI.resid, ?_, hI.f3, ?_⟩
  · rw [hL', fin_read_last, hfrm, hI.abs]
  · have hd1 : DL h (rho v₀ C' h) v₀ (rmId a L) := by
      refine hdrm.weaken fun c y hc => ?_
      by_cases hca : c = a
      · subst hca
        right
        intro z hz hza
        exact absurd hza (mem_rmId.1 hz).2
      · exact .inl (hrho c y hc hca)
    refine hd1.append_pending _ (by simpa using ⟨r, (hI.run r _ _ _ _ hr).1⟩)
      (by simpa using (hI.run r _ _ _ _ hr).2) ?_ ?_
    · simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨hd1.nodup, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact (mem_ids_rmId.1 hx).2
    · refine LegalG.append hd1.legal ⟨fun y hy => ?_, trivial⟩
      rw [hrhoa y hy, hfrm, hI.abs]
  · refine Good.append (hgrm.mono fun _ _ h => hSS _ h) ⟨fun hs => ?_, trivial⟩
    obtain ⟨p, w, b', l', hps, -, -⟩ := hs
    by_cases hpr : p = r
    · subst hpr; simp [hC'] at hps
    · simp only [hC', Function.update_of_ne hpr] at hps
      exact absurd (hI.run_inj hps hr) hpr
  · intro p c o' b' l' hps
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', Function.update_self, PSt.run.injEq] at hps
      obtain ⟨rfl, rfl, rfl, -⟩ := hps
      exact hI.run p _ _ _ _ hr
    · simp only [hC', Function.update_of_ne hpr] at hps
      exact hI.run p _ _ _ _ hps
  · intro p
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', Function.update_self]
      refine ⟨by simp [hres, hwr], by simp, by simp, by simp, ?_, by simp, by simp [hwr], by simp,
        by simp, by simp, by simp, by simp [hwr]⟩
      intro c b' l' h1 _
      simp only [PSt.run.injEq] at h1
      obtain ⟨rfl, -⟩ := h1
      simp [hL']
    · simp only [hC', Function.update_of_ne hpr]
      refine (hI.pi p).frame v₀ rfl (fun _ _ => rfl) ?_
      intro c o' b' l' hps
      exact hmem c (fun e => by subst e; exact hpr (hI.run_inj hps hr))
  · intro p hk hb
    by_cases hpr : p = r
    · subst hpr; simp [hC'] at hk
    · simp only [hC', Function.update_of_ne hpr] at hk hb ⊢
      have := hI.kk p hk hb
      by_cases hq : (vw v₀ (C.ps p) (C.pv p)).1.2.1 = r
      · rw [hq] at this ⊢
        simp only [Function.update_self]
        exact ⟨this.1, by simp, by simp⟩
      · simp only [Function.update_of_ne hq]
        exact this

/-- Invocation. -/
theorem step_inv (hI : Inv v₀ C g h L) (r : Fin n) (o : RWOp V) : StepOK C h (.inv r o) := by
  rw [StepOK]
  cases hr : C.ps r with
  | run a o' b l =>
    refine ⟨g, L, ?_⟩
    simp only [RImpl.step1, hr, List.append_nil]
    exact hI
  | idle =>
  have hwr : g.wr r = false := by have := (hI.pi r).lc; rw [hr] at this; exact this
  simp only [RImpl.step1, hr]
  set C' : Cfg1 V v₀ n := ⟨C.sh, Function.update C.pv r (aux (C.pv r)),
    Function.update C.ps r (.run C.cnt o false (start o)), C.cnt + 1⟩ with hC'
  refine ⟨g, L, ?_⟩
  have hLlt : ∀ c, c ∈ L.map Prod.fst → c < C.cnt := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
    obtain ⟨p, hp⟩ := hI.dl.inv_of_mem y hy
    exact hI.ids _ _ _ hp
  have hcntL : C.cnt ∉ L.map Prod.fst := fun h1 => lt_irrefl _ (hLlt _ h1)
  refine ⟨hI.R, hI.abs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine DL.weaken (hI.dl.append_noRes _ (by simp) ?_) ?_
    · intro c q o' hc; simp only [List.mem_singleton, HEv.inv.injEq] at hc
      obtain ⟨rfl, -, -⟩ := hc; exact hcntL
    · rintro c y (⟨c', hc⟩ | ⟨p, o', b', l', hps, hx⟩)
      · rcases List.mem_append.1 hc with hc | hc
        · exact .inl (.inl ⟨c', hc⟩)
        · simp at hc
      · by_cases hpr : p = r
        · subst hpr
          simp only [hC', Function.update_self, PSt.run.injEq] at hps
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hps
          cases o <;> simp [hC', aux, start] at hx
        · simp only [hC', Function.update_of_ne hpr] at hps hx
          exact .inl (.inr ⟨p, o', b', l', hps, hx⟩)
  · refine hI.good.mono fun y hy hs => ?_
    obtain ⟨p, w, b', l', hps, hw, hcc⟩ := hs
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', Function.update_self, PSt.run.injEq] at hps
      exact absurd (hps.1 ▸ List.mem_map_of_mem hy) hcntL
    · simp only [hC', Function.update_of_ne hpr] at hps hcc
      exact ⟨p, w, b', l', hps, hw, hcc⟩
  · intro c p o' hc
    rcases List.mem_append.1 hc with hc | hc
    · have := hI.ids c p o' hc; show c < C.cnt + 1; omega
    · simp only [List.mem_singleton, HEv.inv.injEq] at hc
      obtain ⟨rfl, -, -⟩ := hc; show C.cnt < C.cnt + 1; omega
  · intro c p o' p' o'' h1 h2
    rcases List.mem_append.1 h1 with h1 | h1 <;> rcases List.mem_append.1 h2 with h2 | h2
    · exact hI.uniq c p o' p' o'' h1 h2
    · simp only [List.mem_singleton, HEv.inv.injEq] at h2
      obtain ⟨rfl, -, -⟩ := h2; exact absurd (hI.ids _ _ _ h1) (lt_irrefl _)
    · simp only [List.mem_singleton, HEv.inv.injEq] at h1
      obtain ⟨rfl, -, -⟩ := h1; exact absurd (hI.ids _ _ _ h2) (lt_irrefl _)
    · simp only [List.mem_singleton, HEv.inv.injEq] at h1 h2
      obtain ⟨-, rfl, rfl⟩ := h1; obtain ⟨-, rfl, rfl⟩ := h2; exact ⟨rfl, rfl⟩
  · intro p c o' b' l' hps
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', Function.update_self, PSt.run.injEq] at hps
      obtain ⟨rfl, rfl, -, -⟩ := hps
      refine ⟨by simp, fun r' c' hc => ?_⟩
      rcases List.mem_append.1 hc with hc | hc
      · exact lt_irrefl _ (hI.resid _ _ _ hc)
      · simp at hc
    · simp only [hC', Function.update_of_ne hpr] at hps
      obtain ⟨h1, h2⟩ := hI.run p c o' b' l' hps
      refine ⟨List.mem_append_left _ h1, fun r' c' hc => ?_⟩
      rcases List.mem_append.1 hc with hc | hc
      · exact h2 r' c' hc
      · simp at hc
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hI.nf c hc
    · simp at hc
  · intro c r' c' hc
    rcases List.mem_append.1 hc with hc | hc
    · have := hI.resid c r' c' hc; show c < C.cnt + 1; omega
    · simp at hc
  · intro p
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', Function.update_self]
      cases o with
      | read =>
        exact ⟨by simp [aux, start, hwr], by simp [start], by simp [start], by simp [start],
          by simp [start, aux], by simp [start], by simp [hwr], by simp [start], by simp [start],
          by simp [start], by simp [start], by simp [hwr]⟩
      | write v =>
        refine ⟨by simp [aux, start, hwr], ?_, by simp [start, aux], by simp [start, aux, hwr],
          by simp [start], by simp [start, aux], by simp [hwr], by simp [start, aux],
          by simp [start, aux], by simp [start, aux], by simp [start, aux], by simp [hwr]⟩
        intro c w hc
        simp only [start, PSt.run.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        exact hcntL
    · simp only [hC', Function.update_of_ne hpr]
      exact hI.pi p
  · intro q hq hT
    by_cases hqr : q = r
    · subst hqr
      simp only [hC', Function.update_self, aux] at hT
      exact hI.f3 q hq hT
    · simp only [hC', Function.update_of_ne hqr] at hT
      exact hI.f3 q hq hT
  · intro p hk hb
    by_cases hpr : p = r
    · subst hpr
      simp only [hC', Function.update_self] at hk
      cases o <;> simp [start, aux] at hk
    · simp only [hC', Function.update_of_ne hpr] at hk hb ⊢
      have := hI.kk p hk hb
      by_cases hq : (vw v₀ (C.ps p) (C.pv p)).1.2.1 = r
      · rw [hq] at this ⊢
        simp only [Function.update_self]
        refine ⟨by simpa [aux] using this.1, ?_, ?_⟩ <;> cases o <;> simp [start, aux]
      · simp only [Function.update_of_ne hq]
        exact this

end Alg1

end Papers.PODC2020.DetectableSpace
