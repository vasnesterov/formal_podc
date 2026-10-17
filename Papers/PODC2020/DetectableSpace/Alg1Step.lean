import Papers.PODC2020.DetectableSpace.Alg1Inv

/-!
# Algorithm 1: preservation of the invariant — generic frame lemmas
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n] (v₀ : V)

/-- Frame for the per-process invariant: shared memory as seen by `p`, membership of `p`'s
operation. -/
lemma PI.frame {p : Fin n} {st : St V n} {m : Pv V n} {s : ℕ} {wr : Bool} {wc : ℕ}
    {rv : ℕ → Trip V n} {sh sh' : Sh V n} {inL inL' : ℕ → Prop}
    (h : PI v₀ p st m s wr wc rv sh inL) (hR : sh'.R = sh.R)
    (hA : ∀ x y, sh'.A (p, x, y) = sh.A (p, x, y))
    (hL : ∀ a o b l, st = .run a o b l → (inL' a ↔ inL a)) :
    PI v₀ p st m s wr wc rv sh' inL' where
  lc := h.lc
  m0 a v hst := by rw [hL _ _ _ _ hst]; exact h.m0 a v hst
  m1 a v b l hst h1 h2 h3 := by rw [hL _ _ _ _ hst]; exact h.m1 a v b l hst h1 h2 h3
  m2 a v b l hst h1 := by rw [hL _ _ _ _ hst]; exact h.m2 a v b l hst h1
  mr a b l hst h1 := by rw [hL _ _ _ _ hst]; exact h.mr a b l hst h1
  f1 := h.f1
  f1w := h.f1w
  f2a := h.f2a
  f2b := h.f2b
  d := h.d
  cl1 h1 h2 := h.cl1 h1 (by simpa [bitOf, hA] using h2)
  c2 h1 h2 := by
    have := h.c2 h1 h2
    simp only [bitOf, hA, hR] at this ⊢
    exact this

variable {v₀}

lemma update_ps_ne {C : Cfg1 V v₀ n} {r p : Fin n} {st : St V n} (hp : p ≠ r) :
    Function.update C.ps r st p = C.ps p := Function.update_of_ne hp _ _

/-- **Generic local step** of process `r`: only `r`'s state, private memory and `s r` change. -/
theorem Inv.local {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}
    (hI : Inv v₀ C g h L) (r : Fin n) (st' : St V n) (m' : Pv V n) (s' : ℕ)
    (hrun : ∀ a o b l, st' = .run a o b l → ∃ b₀ l₀, C.ps r = .run a o b₀ l₀)
    (hpi : PI v₀ r st' m' s' (g.wr r) g.wc g.rv C.sh (· ∈ L.map Prod.fst))
    (hrho : ∀ a o b l x, st' = .run a o b l → (m'.res = some x ∨ l = .d2 x) →
      (∃ o b l, C.ps r = .run a o b l ∧ ((C.pv r).res = some x ∨ l = .d2 x)) ∨
        ∀ y ∈ L, y.1 = a → y.2 = .write x)
    (hSS : ∀ a v b l, st' = .run a (.write v) b l → g.wr r = false → m'.cp ≤ 1 →
      a ∈ L.map Prod.fst → ∃ v b l, C.ps r = .run a (.write v) b l ∧ (C.pv r).cp ≤ 1)
    (hf3 : (g.rv g.wc).2.1 = r → m'.T = (g.rv g.wc).2.2 → g.wr r = true)
    (hkq : ∀ t (p : Fin n), KQ v₀ (C.ps r) (C.pv r) (g.wr r) t p → KQ v₀ st' m' (g.wr r) t p)
    (hkk : Kd st' m' (g.wr r) → bitOf v₀ C.sh r st' m' = false →
      KQ v₀ (Function.update C.ps r st' (vw v₀ st' m').1.2.1)
        (Function.update C.pv r m' (vw v₀ st' m').1.2.1) (g.wr (vw v₀ st' m').1.2.1)
        (vw v₀ st' m').1.2.2 r) :
    Inv v₀ (⟨C.sh, Function.update C.pv r m', Function.update C.ps r st', C.cnt⟩ : Cfg1 V v₀ n)
      ⟨g.wc, g.rv, Function.update g.s r s', g.wr⟩ h L where
  R := hI.R
  abs := hI.abs
  dl := by
    refine hI.dl.weaken ?_
    rintro a x (hx | ⟨p, o, b, l, hp, hx⟩)
    · exact .inl (.inl hx)
    · by_cases hpr : p = r
      · subst hpr
        simp only [Function.update_self] at hp hx
        rcases hrho a o b l x hp hx with ⟨o', b', l', h1, h2⟩ | h
        · exact .inl (.inr ⟨p, o', b', l', h1, h2⟩)
        · exact .inr h
      · simp only [Function.update_of_ne hpr] at hp hx
        exact .inl (.inr ⟨p, o, b, l, hp, hx⟩)
  good := by
    refine hI.good.mono ?_
    rintro y hy ⟨p, v, b, l, hp, hw, hc⟩
    by_cases hpr : p = r
    · subst hpr
      simp only [Function.update_self] at hp hc
      obtain ⟨v', b', l', h1, h2⟩ := hSS _ v b l hp hw hc (List.mem_map_of_mem hy)
      exact ⟨p, v', b', l', h1, hw, h2⟩
    · simp only [Function.update_of_ne hpr] at hp hc
      exact ⟨p, v, b, l, hp, hw, hc⟩
  ids := hI.ids
  uniq := hI.uniq
  run p a o b l hp := by
    by_cases hpr : p = r
    · subst hpr
      simp only [Function.update_self] at hp
      obtain ⟨b₀, l₀, hl₀⟩ := hrun a o b l hp
      exact hI.run p a o b₀ l₀ hl₀
    · simp only [Function.update_of_ne hpr] at hp
      exact hI.run p a o b l hp
  nf := hI.nf
  resid := hI.resid
  pi p := by
    by_cases hpr : p = r
    · subst hpr; simpa using hpi
    · simpa [Function.update_of_ne hpr] using hI.pi p
  f3 q hq hT := by
    by_cases hqr : q = r
    · subst hqr; simp only [Function.update_self] at hT; exact hf3 hq hT
    · simp only [Function.update_of_ne hqr] at hT; exact hI.f3 q hq hT
  kk p hk hb := by
    by_cases hpr : p = r
    · subst hpr
      simp only [Function.update_self] at hk hb ⊢
      exact hkk hk hb
    · simp only [Function.update_of_ne hpr] at hk hb ⊢
      have := hI.kk p hk hb
      by_cases hq : (vw v₀ (C.ps p) (C.pv p)).1.2.1 = r
      · rw [hq] at this ⊢
        simp only [Function.update_self]
        exact hkq _ _ this
      · simp only [Function.update_of_ne hq]
        exact this

/-- `hkk` of `Inv.local` when `r` was already in `Kd` with the same view (or is not in `Kd`). -/
lemma Inv.hkk_of {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}
    (hI : Inv v₀ C g h L) (r : Fin n) (st' : St V n) (m' : Pv V n)
    (hkq : ∀ t (p : Fin n), KQ v₀ (C.ps r) (C.pv r) (g.wr r) t p → KQ v₀ st' m' (g.wr r) t p)
    (hkd : Kd st' m' (g.wr r) → Kd (C.ps r) (C.pv r) (g.wr r) ∧
      vw v₀ st' m' = vw v₀ (C.ps r) (C.pv r)) :
    Kd st' m' (g.wr r) → bitOf v₀ C.sh r st' m' = false →
      KQ v₀ (Function.update C.ps r st' (vw v₀ st' m').1.2.1)
        (Function.update C.pv r m' (vw v₀ st' m').1.2.1) (g.wr (vw v₀ st' m').1.2.1)
        (vw v₀ st' m').1.2.2 r := by
  intro hk hb
  obtain ⟨hk0, hvw⟩ := hkd hk
  have hb0 : bitOf v₀ C.sh r (C.ps r) (C.pv r) = false := by
    simpa [bitOf, hvw] using hb
  have := hI.kk r hk0 hb0
  rw [hvw]
  by_cases hq : (vw v₀ (C.ps r) (C.pv r)).1.2.1 = r
  · rw [hq] at this ⊢
    simp only [Function.update_self]
    exact hkq _ _ this
  · simp only [Function.update_of_ne hq]
    exact this

/-! ### Helper facts -/

lemma ph31 {st : St V n} {m : Pv V n} (h : Ph 3 st m) : Ph 1 st m := by
  unfold Ph at *; split at h <;> omega

lemma ph21 {st : St V n} {m : Pv V n} (h : Ph 2 st m) : Ph 1 st m := by
  unfold Ph at *; split at h <;> omega

lemma ph32 {st : St V n} {m : Pv V n} (h : Ph 3 st m) : Ph 2 st m := by
  unfold Ph at *; split at h <;> omega

/-- A decided write is past line 3. -/
lemma dec_ph3 {st : St V n} {m : Pv V n} {wr : Bool} (hlc : LC v₀ st m wr) (h : Dec st m) :
    Ph 3 st m := by
  match st, hlc, h with
  | .run a (.write v) b l, hlc, h =>
    simp only [Dec] at h
    simp only [Ph]
    rcases h with h | h
    · cases l <;> simp_all [Loc.isDec, Loc.stage, LC, LCW]
    · right; omega

lemma kd_ph1 {st : St V n} {m : Pv V n} {wr : Bool} (hlc : LC v₀ st m wr) (h : Kd st m wr) :
    Ph 1 st m := by
  match st, hlc, h with
  | .run a (.write v) b l, hlc, h =>
    simp only [Kd] at h
    simp only [Ph]
    rcases h with h | h
    · cases l <;> simp_all [Loc.kd, Loc.stage, LC, LCW]
    · right; omega

/-- Entries of `L` with the identifier of a running operation are that operation. -/
lemma Inv.entry {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}
    (hI : Inv v₀ C g h L) {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {l : Loc V n}
    (hr : C.ps r = .run a o b l) : ∀ y ∈ L, y.1 = a → y.2 = o := by
  intro y hy hya
  obtain ⟨p, hp⟩ := hI.dl.inv_of_mem y hy
  rw [hya] at hp
  exact (hI.uniq a p y.2 r o hp (hI.run r a o b l hr).1).2

/-- The conditions `KQ` hold for the last writer of `R` and the toggle of the last write. -/
lemma Inv.kq_last {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}
    (hI : Inv v₀ C g h L) (p : Fin n) :
    KQ v₀ (C.ps (g.rv g.wc).2.1) (C.pv (g.rv g.wc).2.1) (g.wr (g.rv g.wc).2.1)
      (g.rv g.wc).2.2 p := by
  set q := (g.rv g.wc).2.1 with hq
  have hpi := hI.pi q
  refine ⟨fun hT => hI.f3 q rfl hT, fun h3 hmt => ?_, fun hd hmt => ?_⟩
  · by_contra hwr
    have hwr' : g.wr q = false := by simpa using hwr
    have h1 := ph31 h3
    obtain ⟨hs, hrv⟩ := hpi.f2a h1
    rcases Nat.lt_or_eq_of_le hs with hs | hs
    · exact hwr (hpi.f1 h1 g.wc hs le_rfl rfl).1
    · rw [hs] at hrv
      have := hpi.f2b h1 (by rw [← hrv]) 
      apply this
      rw [← hrv, hmt]
  · exfalso
    have h1 := ph31 (dec_ph3 hpi.lc hd)
    obtain ⟨-, he⟩ := hpi.f1 h1 g.wc (hpi.d hd) le_rfl rfl
    have : (g.rv g.wc).2.2 = (vw v₀ (C.ps q) (C.pv q)).2 := by rw [he]
    rw [this] at hmt
    cases h : (vw v₀ (C.ps q) (C.pv q)).2 <;> simp [h] at hmt

/-! ### Steps -/

lemma step1_pv {C : Cfg1 V v₀ n} {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {l : Loc V n}
    {f : Pv V n → Loc V n × Pv V n} (hr : C.ps r = .run a o b l) (hf : act r l = .pv f) :
    (alg1 V v₀ n true).step1 C (.step r) = (⟨C.sh, Function.update C.pv r (f (C.pv r)).2,
      Function.update C.ps r (.run a o b (f (C.pv r)).1), C.cnt⟩, []) := by
  simp only [RImpl.step1, hr]
  rw [hf]

lemma step1_sh {C : Cfg1 V v₀ n} {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {l : Loc V n}
    {f : Sh V n → Loc V n × Sh V n} (hr : C.ps r = .run a o b l) (hf : act r l = .sh f) :
    (alg1 V v₀ n true).step1 C (.step r) = (⟨(f C.sh).2, C.pv,
      Function.update C.ps r (.run a o b (f C.sh).1), C.cnt⟩, []) := by
  simp only [RImpl.step1, hr]
  rw [hf]

lemma step1_ret {C : Cfg1 V v₀ n} {r : Fin n} {a : ℕ} {o : RWOp V} {b : Bool} {l : Loc V n}
    {x : Option V} (hr : C.ps r = .run a o b l) (hf : act r l = .ret x) :
    (alg1 V v₀ n true).step1 C (.step r) = (⟨C.sh, C.pv,
      Function.update C.ps r .idle, C.cnt⟩, [.res a x b]) := by
  simp only [RImpl.step1, hr]
  rw [hf]

/-- The invariant can be re-established after event `e`. -/
def StepOK (C : Cfg1 V v₀ n) (h : Hist V n) (e : Ev (Fin n) (RWOp V)) : Prop :=
  ∃ g' L', Inv v₀ ((alg1 V v₀ n true).step1 C e).1 g' (h ++ ((alg1 V v₀ n true).step1 C e).2) L'

/-- **Generic local step with a change of `A`** (shared `R` unchanged). -/
theorem Inv.localSh {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}
    (hI : Inv v₀ C g h L) (r : Fin n) (sh' : Sh V n) (st' : St V n) (m' : Pv V n) (s' : ℕ)
    (hR : sh'.R = C.sh.R)
    (hrun : ∀ a o b l, st' = .run a o b l → ∃ b₀ l₀, C.ps r = .run a o b₀ l₀)
    (hpi : PI v₀ r st' m' s' (g.wr r) g.wc g.rv sh' (· ∈ L.map Prod.fst))
    (hpiO : ∀ p, p ≠ r →
      PI v₀ p (C.ps p) (C.pv p) (g.s p) (g.wr p) g.wc g.rv sh' (· ∈ L.map Prod.fst))
    (hrho : ∀ a o b l x, st' = .run a o b l → (m'.res = some x ∨ l = .d2 x) →
      (∃ o b l, C.ps r = .run a o b l ∧ ((C.pv r).res = some x ∨ l = .d2 x)) ∨
        ∀ y ∈ L, y.1 = a → y.2 = .write x)
    (hSS : ∀ a v b l, st' = .run a (.write v) b l → g.wr r = false → m'.cp ≤ 1 →
      a ∈ L.map Prod.fst → ∃ v b l, C.ps r = .run a (.write v) b l ∧ (C.pv r).cp ≤ 1)
    (hf3 : (g.rv g.wc).2.1 = r → m'.T = (g.rv g.wc).2.2 → g.wr r = true)
    (hkkO : ∀ p, p ≠ r → Kd (C.ps p) (C.pv p) (g.wr p) →
      bitOf v₀ sh' p (C.ps p) (C.pv p) = false →
      KQ v₀ (Function.update C.ps r st' (vw v₀ (C.ps p) (C.pv p)).1.2.1)
        (Function.update C.pv r m' (vw v₀ (C.ps p) (C.pv p)).1.2.1)
        (g.wr (vw v₀ (C.ps p) (C.pv p)).1.2.1) (vw v₀ (C.ps p) (C.pv p)).1.2.2 p)
    (hkk : Kd st' m' (g.wr r) → bitOf v₀ sh' r st' m' = false →
      KQ v₀ (Function.update C.ps r st' (vw v₀ st' m').1.2.1)
        (Function.update C.pv r m' (vw v₀ st' m').1.2.1) (g.wr (vw v₀ st' m').1.2.1)
        (vw v₀ st' m').1.2.2 r) :
    Inv v₀ (⟨sh', Function.update C.pv r m', Function.update C.ps r st', C.cnt⟩ : Cfg1 V v₀ n)
      ⟨g.wc, g.rv, Function.update g.s r s', g.wr⟩ h L where
  R := by rw [← hI.R]; exact hR
  abs := hI.abs
  dl := by
    refine hI.dl.weaken ?_
    rintro a x (hx | ⟨p, o, b, l, hp, hx⟩)
    · exact .inl (.inl hx)
    · by_cases hpr : p = r
      · subst hpr
        simp only [Function.update_self] at hp hx
        rcases hrho a o b l x hp hx with ⟨o', b', l', h1, h2⟩ | h
        · exact .inl (.inr ⟨p, o', b', l', h1, h2⟩)
        · exact .inr h
      · simp only [Function.update_of_ne hpr] at hp hx
        exact .inl (.inr ⟨p, o, b, l, hp, hx⟩)
  good := by
    refine hI.good.mono ?_
    rintro y hy ⟨p, v, b, l, hp, hw, hc⟩
    by_cases hpr : p = r
    · subst hpr
      simp only [Function.update_self] at hp hc
      obtain ⟨v', b', l', h1, h2⟩ := hSS _ v b l hp hw hc (List.mem_map_of_mem hy)
      exact ⟨p, v', b', l', h1, hw, h2⟩
    · simp only [Function.update_of_ne hpr] at hp hc
      exact ⟨p, v, b, l, hp, hw, hc⟩
  ids := hI.ids
  uniq := hI.uniq
  run p a o b l hp := by
    by_cases hpr : p = r
    · subst hpr
      simp only [Function.update_self] at hp
      obtain ⟨b₀, l₀, hl₀⟩ := hrun a o b l hp
      exact hI.run p a o b₀ l₀ hl₀
    · simp only [Function.update_of_ne hpr] at hp
      exact hI.run p a o b l hp
  nf := hI.nf
  resid := hI.resid
  pi p := by
    by_cases hpr : p = r
    · subst hpr; simpa using hpi
    · simpa [Function.update_of_ne hpr] using hpiO p hpr
  f3 q hq hT := by
    by_cases hqr : q = r
    · subst hqr; simp only [Function.update_self] at hT; exact hf3 hq hT
    · simp only [Function.update_of_ne hqr] at hT; exact hI.f3 q hq hT
  kk p hk hb := by
    by_cases hpr : p = r
    · subst hpr
      simp only [Function.update_self] at hk hb ⊢
      exact hkk hk hb
    · simp only [Function.update_of_ne hpr] at hk hb ⊢
      exact hkkO p hpr hk hb

end Alg1

end Papers.PODC2020.DetectableSpace
