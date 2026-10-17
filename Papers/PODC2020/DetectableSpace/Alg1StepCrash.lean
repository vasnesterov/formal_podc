import Papers.PODC2020.DetectableSpace.Alg1Step

/-!
# Algorithm 1: preservation of the invariant by a system-wide crash
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

attribute [local simp] LC LCW LCR Ph Dec Kd vw valOf progOf at20b bitOf Loc.stage Loc.isDec
  Loc.prog Loc.kd Loc.is20b Loc.is12 Loc.info

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n] {v₀ : V}
variable {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}

/-- Effect of a crash on a process. -/
def cr : St V n → St V n
  | .idle => .idle
  | .run a o _ _ => .run a o true (recov o)

lemma crashPS_eq (p : Fin n) (st : St V n) : (alg1 V v₀ n true).crashPS p st = cr st := by
  cases st <;> rfl

/-- After a crash the view of a write past line 3 (`CP ≥ 1`) is unchanged. -/
lemma cr_vw {st : St V n} {m : Pv V n} {wr : Bool} (hlc : LC v₀ st m wr) (hc : 1 ≤ m.cp) :
    vw v₀ (cr st) m = vw v₀ st m := by
  match st, hlc with
  | .idle, _ => rfl
  | .run a .read b l, _ => rfl
  | .run a (.write v) b l, hlc =>
    obtain ⟨-, -, -, -, hrd, -⟩ := hlc
    simp only [cr, recov, vw]
    show (match m.rd with | some (mt, tr) => (tr, mt) | none => dflt v₀) = Loc.info (dflt v₀) m l
    rw [hrd hc]

lemma cr_ph {st : St V n} {m : Pv V n} {k : ℕ} (hk : 1 ≤ k) (h : Ph k (cr st) m) :
    Ph k st m ∧ 1 ≤ m.cp := by
  match st, h with
  | .run a (.write v) b l, h =>
    simp only [cr, recov, Ph, Loc.stage] at h
    refine ⟨?_, by omega⟩
    simp only [Ph]; right; omega

lemma cr_dec {st : St V n} {m : Pv V n} (h : Dec (cr st) m) : Dec st m ∧ m.cp = 2 := by
  match st, h with
  | .run a (.write v) b l, h =>
    simp only [cr, recov, Dec, Loc.isDec, false_or] at h
    exact ⟨by simp only [Dec]; right; exact h, h⟩

lemma cr_kd {st : St V n} {m : Pv V n} {wr : Bool} (h : Kd (cr st) m wr) :
    Kd st m wr ∧ m.cp = 1 := by
  match st, h with
  | .run a (.write v) b l, h =>
    simp only [cr, recov, Kd, Loc.kd, false_or] at h
    exact ⟨by simp only [Kd]; right; exact h, h.2⟩

lemma KQ.crash {st : St V n} {m : Pv V n} {wr t : Bool} {p : Fin n} (hlc : LC v₀ st m wr)
    (hk : KQ v₀ st m wr t p) : KQ v₀ (cr st) m wr t p := by
  obtain ⟨ka, kb, kc⟩ := hk
  refine ⟨ka, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨h3, hc⟩ := cr_ph (by omega) h1
    rw [cr_vw hlc hc] at h2
    exact kb h3 h2
  · obtain ⟨h3, hc⟩ := cr_dec h1
    rw [cr_vw hlc (by omega)] at h2 ⊢
    refine ⟨(kc h3 h2).1, ?_⟩
    match st with
    | .run a (.write v) b l => simp [cr, recov, progOf, Loc.prog]

lemma PI.crash {p : Fin n} {st : St V n} {m : Pv V n} {s : ℕ} {wr : Bool} {wc : ℕ}
    {rv : ℕ → Trip V n} {sh : Sh V n} {inL : ℕ → Prop}
    (h : PI v₀ p st m s wr wc rv sh inL) : PI v₀ p (cr st) m s wr wc rv sh inL := by
  have hlc := h.lc
  match st, hlc with
  | .idle, _ => exact h
  | .run a .read b l, hlc =>
    obtain ⟨-, hwr⟩ := hlc
    refine ⟨by simp [cr, recov, hwr], by simp [cr], by simp [cr], by simp [cr], ?_, by simp [cr],
      by simp [hwr], by simp [cr], by simp [cr], by simp [cr], by simp [cr], by simp [hwr]⟩
    intro a' b' l' h1 h2
    simp only [cr, recov, PSt.run.injEq] at h1
    obtain ⟨rfl, -, -, rfl⟩ := h1
    rcases h2 with ⟨x, hx⟩ | h2
    · cases hx
    · exact h.mr a b l rfl (.inr h2)
  | .run a (.write v) b l, hlc =>
    obtain ⟨hlcw, hcp2, hwrcp, hres, hrd, htt1, htt2⟩ := hlc
    have hvw : 1 ≤ m.cp → vw v₀ (cr (.run a (.write v) b l)) m = vw v₀ (.run a (.write v) b l) m :=
      cr_vw h.lc
    have hph : ∀ k, 1 ≤ k → Ph k (cr (.run a (.write v) b l)) m →
        Ph k (.run a (.write v) b l) m ∧ 1 ≤ m.cp := fun k hk h1 => cr_ph hk h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.f1w, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [cr, recov, LC, LCW, true_and]
      have hvw' : 1 ≤ m.cp → Loc.info (dflt v₀) m (.r14 v) = Loc.info (dflt v₀) m l := by
        intro hc; have := hvw hc; simpa [cr, recov] using this
      refine ⟨hcp2, hwrcp, hres, fun hc => by rw [hvw' hc]; exact hrd hc, fun h1 h2 => ?_,
        fun h1 => ?_⟩
      · have hc : 1 ≤ m.cp := by simpa using h1
        rw [hvw' hc]; exact htt1 (by simp; right; exact hc) h2
      · rcases h1 with h1 | h1
        · simp at h1
        · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h1
          have hc := (hres x hx).2
          rw [hvw' (by omega)]; exact htt2 (.inr h1)
    · intro a' v' h1; simp [cr] at h1
    · intro a' v' b' l' h1 h2 h3 h4
      simp only [cr, recov, PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      exact h.m1 a v b l rfl (hph 1 le_rfl h2).1 h3 h4
    · intro a' v' b' l' h1 h2
      simp only [cr, recov, PSt.run.injEq] at h1
      obtain ⟨rfl, -, -, -⟩ := h1
      rcases h2 with h2 | h2
      · exact h.m2 a v b l rfl (.inl h2)
      · exact h.m2 a v b l rfl (.inr (cr_dec h2).1)
    · intro a' b' l' h1; simp [cr] at h1
    · intro h1 k hk1 hk2 hk3
      obtain ⟨h2, hc⟩ := hph 1 le_rfl h1
      rw [hvw hc]
      simpa [cr] using h.f1 h2 k hk1 hk2 hk3
    · intro h1
      obtain ⟨h2, hc⟩ := hph 1 le_rfl h1
      rw [hvw hc]; exact h.f2a h2
    · intro h1
      obtain ⟨h2, hc⟩ := hph 1 le_rfl h1
      rw [hvw hc]; exact h.f2b h2
    · intro h1; exact h.d (cr_dec h1).1
    · intro h1 h2
      obtain ⟨h3, hc⟩ := hph 2 (by omega) h1
      simp only [bitOf] at h2
      rw [hvw hc] at h2
      exact h.cl1 h3 h2
    · intro h1 h2
      obtain ⟨c1, -⟩ := h.c2 h1 h2
      simp only [bitOf] at c1 ⊢
      rw [hvw (by omega)]
      exact ⟨c1, by simp [cr, recov]⟩

/-- A system-wide crash. -/
theorem step_crash (hI : Inv v₀ C g h L) : StepOK C h .crash := by
  rw [StepOK]
  simp only [RImpl.step1, crashPS_eq]
  set C' : Cfg1 V v₀ n := ⟨C.sh, C.pv, fun p => cr (C.ps p), C.cnt⟩ with hC'
  refine ⟨g, L, ?_⟩
  have hcrun : ∀ p a o b l, cr (C.ps p) = .run a o b l → ∃ b₀ l₀, C.ps p = .run a o b₀ l₀ ∧
      b = true ∧ l = recov o := by
    intro p a o b l h1
    cases hp : C.ps p with
    | idle => rw [hp] at h1; simp [cr] at h1
    | run a' o' b' l' =>
      rw [hp] at h1
      simp only [cr, PSt.run.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact ⟨b', l', rfl, rfl, rfl⟩
  refine ⟨hI.R, hI.abs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine DL.weaken (hI.dl.append_noRes _ (by simp) (by simp)) ?_
    rintro c y (⟨c', hc⟩ | ⟨p, o', b', l', hps, hx⟩)
    · rcases List.mem_append.1 hc with hc | hc
      · exact .inl (.inl ⟨c', hc⟩)
      · simp at hc
    · obtain ⟨b₀, l₀, h1, -, rfl⟩ := hcrun p _ _ _ _ hps
      refine .inl (.inr ⟨p, o', b₀, l₀, h1, ?_⟩)
      rcases hx with hx | hx
      · exact .inl hx
      · cases o' <;> simp [recov] at hx
  · refine hI.good.mono fun y _ hs => ?_
    obtain ⟨p, w, b', l', hps, hw, hcc⟩ := hs
    obtain ⟨b₀, l₀, h1, -, -⟩ := hcrun p _ _ _ _ hps
    exact ⟨p, w, b₀, l₀, h1, hw, hcc⟩
  · intro c p o hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hI.ids c p o hc
    · simp at hc
  · intro c p o p' o' h1 h2
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h1 h2
    exact hI.uniq c p o p' o' h1 h2
  · intro p a o b l hps
    obtain ⟨b₀, l₀, h1, -, -⟩ := hcrun p _ _ _ _ hps
    obtain ⟨h2, h3⟩ := hI.run p a o b₀ l₀ h1
    refine ⟨List.mem_append_left _ h2, fun r c hc => ?_⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact h3 r c hc
    · simp at hc
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hI.nf c hc
    · simp at hc
  · intro c r c' hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hI.resid c r c' hc
    · simp at hc
  · intro p; exact (hI.pi p).crash
  · exact hI.f3
  · intro p hk hb
    simp only [hC'] at hk hb ⊢
    obtain ⟨hk0, hc⟩ := cr_kd hk
    have hvw := cr_vw (hI.pi p).lc (by omega)
    simp only [bitOf] at hb
    rw [hvw] at hb ⊢
    exact (hI.kk p hk0 hb).crash (hI.pi _).lc

end Alg1

end Papers.PODC2020.DetectableSpace
