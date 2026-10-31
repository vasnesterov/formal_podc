import Papers.PODC2018.PartialReplicationCausal.Necessity.Frozen

/-!
# Theorem 1: phases of the constructed executions

A *phase* is a list of pairs `(p, x)`; each pair means "replica `p` closes (applies everything it
can), then writes register `x`". Labels of the writes are `c + n` (for a fixed offset `c`), which
are fresh as long as `LabBound c` holds.
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg M : Type*} {X : ι → Set Reg} {A : Alg ι Reg M}

namespace T1

variable (X A) in
/-- Run a phase: for each `(p, x)`, close `p`, then `p` writes `x` with label `c + n`. -/
noncomputable def phase (c : ℕ) : List (ι × Reg) → St ι Reg M → St ι Reg M
  | [], s => s
  | (p, x) :: L, s => phase c L ((close X A p s).write A p x (c + (close X A p s).n))

@[simp] lemma phase_nil (c : ℕ) (s : St ι Reg M) : phase X A c [] s = s := rfl

lemma phase_cons (c : ℕ) (p : ι) (x : Reg) (L : List (ι × Reg)) (s : St ι Reg M) :
    phase X A c ((p, x) :: L) s = phase X A c L ((close X A p s).write A p x (c + s.n)) := by
  simp only [phase, close_n]

lemma phase_append (c : ℕ) (L₁ L₂ : List (ι × Reg)) (s : St ι Reg M) :
    phase X A c (L₁ ++ L₂) s = phase X A c L₂ (phase X A c L₁ s) := by
  induction L₁ generalizing s with
  | nil => rfl
  | cons q L ih => obtain ⟨p, x⟩ := q; simp only [List.cons_append, phase_cons, ih]

lemma phase_n (c : ℕ) (L : List (ι × Reg)) (s : St ι Reg M) :
    (phase X A c L s).n = s.n + L.length := by
  induction L generalizing s with
  | nil => rfl
  | cons q L ih =>
    obtain ⟨p, x⟩ := q
    rw [phase_cons, ih]; simp [close_n]; omega

lemma ext_phase (c : ℕ) (L : List (ι × Reg)) (s : St ι Reg M) : Ext s (phase X A c L s) := by
  induction L generalizing s with
  | nil => exact Ext.refl _
  | cons q L ih =>
    obtain ⟨p, x⟩ := q
    rw [phase_cons]
    exact ((ext_close s).trans (ext_write _ _ _ _)).trans (ih _)

lemma phase_frame (c : ℕ) (L : List (ι × Reg)) (s : St ι Reg M) {r : ι}
    (hr : ∀ q ∈ L, q.1 ≠ r) : (phase X A c L s).md r = s.md r ∧ (phase X A c L s).app r = s.app r := by
  induction L generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons q L ih =>
    obtain ⟨p, x⟩ := q
    have hp : r ≠ p := fun h => hr (p, x) (by simp) h.symm
    rw [phase_cons]
    obtain ⟨h1, h2⟩ := ih _ (fun q hq => hr q (by simp [hq]))
    rw [h1, h2, write_md_ne _ _ _ _ hp, write_app_ne _ _ _ _ hp, close_md_ne _ hp,
      close_app_ne _ hp]
    exact ⟨rfl, rfl⟩

/-- All labels are below `c + n`, so `c + n` is a fresh label. -/
def LabBound (c : ℕ) (s : St ι Reg M) : Prop := ∀ a < s.n, (s.log a).lab < c + s.n

lemma reach_phase (c : ℕ) (L : List (ι × Reg)) (hL : ∀ q ∈ L, q.2 ∈ X q.1) (s : St ι Reg M)
    (hs : Reachable X A s) (hc : LabBound c s) :
    Relation.ReflTransGen (Step X A) s (phase X A c L s) ∧ LabBound c (phase X A c L s) := by
  induction L generalizing s with
  | nil => exact ⟨.refl, hc⟩
  | cons q L ih =>
    obtain ⟨p, x⟩ := q
    rw [phase_cons]
    set s₁ := close X A p s
    have h1 : Relation.ReflTransGen (Step X A) s s₁ := rtg_close s
    have hn : s₁.n = s.n := close_n s
    have hlog : s₁.log = s.log := close_log s
    have hstep : Step X A s₁ (s₁.write A p x (c + s.n)) :=
      Step.write _ _ _ _ (hL (p, x) (by simp)) (fun a ha => by
        rw [hlog]; rw [hn] at ha; exact (hc a ha).ne)
    have hc' : LabBound c (s₁.write A p x (c + s.n)) := by
      intro a ha
      simp only [write_n] at ha ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · rw [write_log_lt _ _ _ _ ha, hlog]; rw [hn] at ha ⊢; have := hc a ha; omega
      · rw [← hn]; simp
    obtain ⟨h2, h3⟩ := ih (fun q hq => hL q (by simp [hq])) _
      (Reachable.rtg hs (h1.tail hstep)) hc'
    exact ⟨(h1.tail hstep).trans h2, h3⟩

/-- Every issued update on a register of `X t` is applied at `t`. -/
def AllApplied (t : ι) (s : St ι Reg M) : Prop := ∀ a < s.n, (s.log a).reg ∈ X t → a ∈ s.app t

lemma AllApplied.ext_same {t : ι} {s s' : St ι Reg M} (h : AllApplied (X := X) t s) (he : Ext s s')
    (hn : s'.n = s.n) : AllApplied (X := X) t s' := by
  intro a ha hreg
  rw [hn] at ha
  rw [he.log_eq a ha] at hreg
  exact he.app_sub t (h a ha hreg)

lemma AllApplied.close {t p : ι} {s : St ι Reg M} (h : AllApplied (X := X) t s) :
    AllApplied (X := X) t (close X A p s) := h.ext_same (ext_close s) (close_n s)

lemma AllApplied.write {t p : ι} {x : Reg} {ℓ : ℕ} {s : St ι Reg M}
    (h : AllApplied (X := X) t s) (hx : x ∉ X t ∨ p = t) :
    AllApplied (X := X) t (s.write A p x ℓ) := by
  intro a ha hreg
  simp only [write_n] at ha
  rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
  · rw [write_log_lt _ _ _ _ ha] at hreg
    exact subset_write_app _ _ _ _ _ (h a ha hreg)
  · simp only [write_log_n] at hreg
    rcases hx with hx | rfl
    · exact absurd hreg hx
    · simp

lemma AllApplied.phase {t : ι} {c : ℕ} {L : List (ι × Reg)} {s : St ι Reg M}
    (h : AllApplied (X := X) t s) (hL : ∀ q ∈ L, q.2 ∉ X t ∨ q.1 = t) :
    AllApplied (X := X) t (phase X A c L s) := by
  induction L generalizing s with
  | nil => exact h
  | cons q L ih =>
    obtain ⟨p, x⟩ := q
    rw [phase_cons]
    exact ih (h.close.write (hL (p, x) (by simp))) (fun q hq => hL q (by simp [hq]))

variable (X) in
/-- `Linked X z L t`: register `z` is stored at the first replica of `L`, the register written by
each replica of `L` is stored at the next one, and the last register is stored at `t`. -/
def Linked : Reg → List (ι × Reg) → ι → Prop
  | z, [], t => z ∈ X t
  | z, (p, x) :: L, t => z ∈ X p ∧ Linked x L t

/-- A causal chain carried along a phase: if `c₀` happened after `b` (or is `b`) and its register
links through `L` to `t`, then the last update of the phase happened after `b`. -/
theorem carrier [Fintype ι] (hA : Implements X A) {c b : ℕ} {t : ι} :
    ∀ (L : List (ι × Reg)) (s : St ι Reg M) (c₀ : ℕ), L ≠ [] → (∀ q ∈ L, q.2 ∈ X q.1) →
      Reachable X A s → LabBound c s → c₀ < s.n → (c₀ = b ∨ HB s b c₀) →
      Linked X (s.log c₀).reg L t →
      HB (phase X A c L s) b ((phase X A c L s).n - 1) ∧
        ((phase X A c L s).log ((phase X A c L s).n - 1)).reg ∈ X t := by
  intro L
  induction L with
  | nil => intro _ _ h; exact absurd rfl h
  | cons q L ih =>
    obtain ⟨p, x⟩ := q
    intro s c₀ _ hL hs hc hc₀ hb hlink
    rw [phase_cons]
    set s₁ := close X A p s
    set s₂ := s₁.write A p x (c + s.n)
    have hstep : Step X A s₁ s₂ :=
      Step.write _ _ _ _ (hL (p, x) (by simp)) (fun a ha => by
        rw [close_log]; rw [close_n] at ha; exact (hc a ha).ne)
    have hs₂ : Reachable X A s₂ := Reachable.rtg hs ((rtg_close s).tail hstep)
    have hc₂ : LabBound c s₂ := by
      have := (reach_phase (X := X) (A := A) c [(p, x)] (fun q hq => hL q (by simp_all)) s hs hc).2
      rwa [phase_cons] at this
    have hn₁ : s₁.n = s.n := close_n s
    have happ : c₀ ∈ s₁.app p := close_all hA hs c₀ hc₀ hlink.1
    have hlink₂ : HB s₂ c₀ s₁.n := hb_single (by simp [s₂]) (by simpa [s₂] using happ)
    have hext : Ext s s₂ := (ext_close s).trans (ext_write _ _ _ _)
    have hb₂ : HB s₂ b s₁.n := by
      rcases hb with rfl | hb
      · exact hlink₂
      · exact (hext.hb hb).trans hlink₂
    have hreg₂ : (s₂.log s₁.n).reg = x := by simp [s₂]
    by_cases hne : L = []
    · subst hne
      have hn₂ : s₂.n - 1 = s₁.n := by simp [s₂]
      simp only [phase_nil]
      rw [hn₂, hreg₂]
      exact ⟨hb₂, hlink.2⟩
    · exact ih s₂ s₁.n hne (fun q hq => hL q (by simp [hq])) hs₂ hc₂ (by simp [s₂]) (.inr hb₂)
        (by rw [hreg₂]; exact hlink.2)

/-- At the end of a phase whose last write is the only one on a register of `X k` (and `k` is not
among the writers), the last update is enabled at `k`. -/
theorem last_enabled [Fintype ι] (hA : Implements X A) {c : ℕ} {k : ι} {s : St ι Reg M}
    (hs : Reachable X A s) (hc : LabBound c s) (hJ : AllApplied (X := X) k s)
    (La : List (ι × Reg)) (pf : ι) (xf : Reg)
    (hLa : ∀ q ∈ La, q.2 ∈ X q.1 ∧ q.2 ∉ X k) (hpf : pf ≠ k) (hxf : xf ∈ X pf) (hxk : xf ∈ X k) :
    Enabled X A (phase X A c (La ++ [(pf, xf)]) s) k
      ((phase X A c (La ++ [(pf, xf)]) s).n - 1) := by
  rw [phase_append, phase_cons, phase_nil]
  set s₁ := phase X A c La s
  obtain ⟨h1, hc1⟩ := reach_phase c La (fun q hq => (hLa q hq).1) s hs hc
  have hs₁ : Reachable X A s₁ := Reachable.rtg hs h1
  have hJ₁ : AllApplied (X := X) k s₁ := hJ.phase (fun q hq => .inl (hLa q hq).2)
  set s₂ := close X A pf s₁
  have hs₂ : Reachable X A s₂ := Reachable.rtg hs₁ (rtg_close s₁)
  have hJ₂ : AllApplied (X := X) k s₂ := hJ₁.close
  set s₃ := s₂.write A pf xf (c + s₁.n)
  have hstep : Step X A s₂ s₃ :=
    Step.write _ _ _ _ hxf (fun a ha => by
      rw [close_log]; rw [close_n] at ha; exact (hc1 a ha).ne)
  have hs₃ : Reachable X A s₃ := Reachable.step hs₂ hstep
  have hinv₂ := Reachable.inv hs₂
  have hinv₃ := Reachable.inv hs₃
  have hn : s₃.n - 1 = s₂.n := by simp [s₃]
  have happ : s₃.app k = s₂.app k := write_app_ne _ _ _ _ (Ne.symm hpf)
  rw [hn]
  refine enabled_of_unique hA hs₃ (by simp [s₃]) (by simp [s₃, hxk]) ?_ ?_ ?_
  · rw [happ]; exact fun h => lt_irrefl _ (hinv₂.app_lt _ _ h)
  · intro a ha hab
    have hlt := hinv₃.hb_lt hab
    rw [happ]
    rw [write_log_lt _ _ _ _ hlt] at ha
    exact hJ₂ a hlt ha
  · intro a hne ha
    obtain ⟨ha1, -, ha3, ha4, -⟩ := ha
    have hlt : a < s₂.n := by simp [s₃] at ha1; omega
    rw [write_log_lt _ _ _ _ hlt] at ha3
    rw [happ] at ha4
    exact ha4 (hJ₂ a hlt ha3)

end T1

end Podc.PartialReplicationCausal.Necessity
