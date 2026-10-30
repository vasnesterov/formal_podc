import Podc.Computability.Distributed.NIS.Model

/-!
# Composing an IS protocol with an NIS protocol

Brusse–Ellen, PODC 2021, Section 6 (special case "`A₁` is an IS protocol") and Section 7.

Let `A₁` (decision function `δ₁`) be an IS protocol in which every process terminates exactly after its
`t`-th scan (`IsIS δ₁ t`), and `A` (decision function `δA`) any NIS protocol whose inputs are the outputs
of `A₁`. The composition `A ∘ A₁` (here with an additional local post-processing `h` of the outputs
of `A`) is the full-information protocol in which a process first runs `A₁` on the objects `S₁, …, S_t`
and then runs `A`, with input its output from `A₁`, on `S_{t+1}, S_{t+2}, …`: object `S_{t+ℓ}` plays the
role of the `ℓ`-th object of `A`. Its decision function `compP` reads the state in `A` off the
full-information state (`toAS`).

Main facts:
* `Ycfg C₁ CA`: the configuration of `A ∘ A₁` determined by an `A₁`-configuration `C₁` (states up to
  round `t`) and an `A`-configuration `CA` (states of the processes that finished `A₁`);
* `stepY_A1`, `stepY_A`: a step of the composition is a step of `A₁` or a step of `A`;
* `reach_decomp`: every reachable configuration of `A ∘ A₁` is of this form.
-/

namespace Podc.ExtensionBasedReductions

open Cslib.NIS

open St

variable {P XT M ZS ZT : Type} [DecidableEq P] [Inhabited M]

section Defs
variable (δ1 : Protocol P XT M) (t : ℕ)

mutual
/-- The `A`-state encoded in a full-information state of `A ∘ A₁` of a process that finished `A₁`. -/
def toAS : St P XT → St P M
  | init i _ => init i default
  | upd s => upd (toAS s)
  | scan s v => if (scan s v).rounds ≤ t then init s.pid ((δ1 (scan s v)).getD default)
      else scan (toAS s) (fun j => toASO (v j))
/-- `toAS` on optional states. -/
def toASO : Option (St P XT) → Option (St P M)
  | none => none
  | some s => some (toAS s)
end

/-- The composed protocol `h ∘ A ∘ A₁`. -/
def compP (δA : Protocol P M ZS) (h : P → ZS → ZT) : Protocol P XT ZT :=
  fun s => if s.rounds ≤ t then none else (δA (toAS δ1 t s)).map (h s.pid)

end Defs

mutual
/-- Lift an `A`-state to a state of `A ∘ A₁`, given the final `A₁`-states `C₁`. -/
def lift (C1 : Config P XT) : St P M → St P XT
  | init i _ => C1 i
  | upd s => upd (lift C1 s)
  | scan s v => scan (lift C1 s) (fun j => liftO C1 (v j))
/-- `lift` on optional states. -/
def liftO (C1 : Config P XT) : Option (St P M) → Option (St P XT)
  | none => none
  | some s => some (lift C1 s)
end

section Good
variable (δ1 : Protocol P XT M)

mutual
/-- All initial states occurring in an `A`-state are `init k y` with `k` terminated in `C₁` with
output `y`. -/
def Good (C1 : Config P XT) : St P M → Prop
  | init k y => decided δ1 (C1 k) = some y
  | upd s => Good C1 s
  | scan s v => Good C1 s ∧ ∀ j, GoodO C1 (v j)
/-- `Good` on optional states. -/
def GoodO (C1 : Config P XT) : Option (St P M) → Prop
  | none => True
  | some s => Good C1 s
end

/-- The configuration of `A ∘ A₁` given by `C₁` and `CA`. -/
def Ycfg (C1 : Config P XT) (CA : Config P M) : Config P XT :=
  fun j => if (decided δ1 (C1 j)).isSome then lift C1 (CA j) else C1 j

/-- Invariant relating `C₁` and `CA`: `C₁` is reachable in `A₁`; processes that have not finished
`A₁` are in the initial state with input `u j` in `CA`; those that finished have output `u j` and an
`A`-state starting from `init j (u j)`. -/
structure Inv (C1 : Config P XT) (CA : Config P M) (u : P → M) : Prop where
  reach : Reach δ1 C1
  unfin : ∀ j, decided δ1 (C1 j) = none → CA j = init j (u j)
  fin : ∀ j y, decided δ1 (C1 j) = some y → y = u j ∧ Good δ1 C1 (CA j) ∧ (CA j).pid = j

end Good

/-! ## Structure of reachable states -/

section Structure
variable {X Y : Type} {δ : Protocol P X Y}

lemma depth_eq (s : St P X) : s.depth = s.hist.length + s.rounds := by
  match s with
  | init _ _ => rfl
  | upd s => simp [St.depth, St.hist, St.rounds, depth_eq s]; omega
  | scan s _ => simp [St.depth, St.hist, St.rounds, depth_eq s]; omega

/-- `s` is an update state. -/
def IsUpd : St P X → Bool
  | upd _ => true
  | _ => false

/-- In reachable states, updates and scans alternate. -/
def HL (s : St P X) : Prop := s.hist.length = s.rounds + if IsUpd s then 1 else 0

lemma _root_.Cslib.NIS.Reach.hl {C : Config P X} (hC : Reach δ C) (j : P) : HL (C j) := by
  obtain ⟨x, α, -, rfl⟩ := hC
  induction α using List.reverseRecOn with
  | nil => simp [HL, initC, St.hist, St.rounds, IsUpd]
  | append_singleton α q ih =>
    rw [exec_append]; simp only [exec_cons, exec_nil]
    by_cases hj : j = q
    · subst hj; simp only [step_self]
      rcases stepState_cases (exec (initC x) α) j with ⟨s, h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; have := ih; rw [h1] at this
        simp [HL, IsUpd, St.hist, St.rounds] at this ⊢; omega
      · rw [h2]; have := ih
        have hnu : ¬ IsUpd (exec (initC x) α j) := by
          intro hu; cases h : exec (initC x) α j <;> simp_all [IsUpd]
        simp [HL, IsUpd, St.hist, St.rounds, hnu] at this ⊢; omega
    · rw [step_ne _ hj]; exact ih

end Structure

section IS
variable {δ1 : Protocol P XT M} {t : ℕ} (hIS : IsIS δ1 t) (ht : 0 < t)
include hIS

lemma decided_isSome_iff (s : St P XT) : (decided δ1 s).isSome ↔ s.IsScan ∧ s.rounds = t := by
  cases s with
  | init i x => simp [St.IsScan]
  | upd s => simp [St.IsScan]
  | scan s v => simp [St.IsScan, hIS s v]

lemma decided_fin_scan {C1 : Config P XT} {k : P} {y : M} (h : decided δ1 (C1 k) = some y) :
    (C1 k).IsScan ∧ (C1 k).rounds = t :=
  (decided_isSome_iff hIS _).1 (by rw [h]; rfl)

include ht

/-- In a reachable configuration of an IS protocol, every process is at most in round `t`, and is
poised to update only before round `t`. -/
lemma _root_.Cslib.NIS.Reach.is_rounds {C : Config P XT} (hC : Reach δ1 C) (j : P) :
    (C j).rounds ≤ t ∧ (IsUpd (C j) = true → (C j).rounds < t) := by
  obtain ⟨x, α, hα, rfl⟩ := hC
  induction α using List.reverseRecOn with
  | nil => simp [initC, St.rounds, IsUpd]
  | append_singleton α q ih =>
    rw [isSched_concat] at hα
    have ih := ih hα.1
    rw [exec_append]; simp only [exec_cons, exec_nil]
    by_cases hj : j = q
    · subst hj; simp only [step_self]
      rcases stepState_cases (exec (initC x) α) j with ⟨s, h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; rw [h1] at ih; simp [IsUpd, St.rounds] at ih ⊢; omega
      · rw [h2]
        simp only [IsUpd, St.rounds, true_implies]
        refine ⟨ih.1, lt_of_le_of_ne ih.1 fun heq => ?_⟩
        have hact := hα.2
        unfold Active at hact
        cases hs : exec (initC x) α j with
        | init i y => rw [hs] at heq; simp [St.rounds] at heq; omega
        | upd s => exact h1 s hs
        | scan s v =>
          rw [hs] at hact heq
          have := (decided_isSome_iff hIS (scan s v)).2 ⟨trivial, heq⟩
          rw [hact] at this; simp at this
    · rw [step_ne _ hj]; exact ih

lemma _root_.Cslib.NIS.Reach.hist_length_le {C : Config P XT} (hC : Reach δ1 C) (j : P) :
    (C j).hist.length ≤ t := by
  have h1 := hC.hl j
  have h2 := hC.is_rounds hIS ht j
  unfold HL at h1
  split_ifs at h1 with hu
  · have := h2.2 hu; omega
  · omega

lemma _root_.Cslib.NIS.Reach.hist_length_fin {C : Config P XT} (hC : Reach δ1 C) {j : P}
    (hj : (decided δ1 (C j)).isSome) : (C j).hist.length = t := by
  have h1 := hC.hl j
  obtain ⟨hs, hr⟩ := (decided_isSome_iff hIS _).1 hj
  unfold HL at h1
  have : ¬ IsUpd (C j) := by
    intro hu; cases h : C j <;> simp_all [IsUpd, St.IsScan]
  simp [this] at h1; omega

lemma _root_.Cslib.NIS.Reach.depth_fin {C : Config P XT} (hC : Reach δ1 C) {j : P}
    (hj : (decided δ1 (C j)).isSome) : (C j).depth = 2 * t := by
  rw [depth_eq, hC.hist_length_fin hIS ht hj, ((decided_isSome_iff hIS _).1 hj).2]; ring

lemma _root_.Cslib.NIS.Reach.depth_unfin {C : Config P XT} (hC : Reach δ1 C) {j : P}
    (hj : decided δ1 (C j) = none) : (C j).depth < 2 * t := by
  have h1 := hC.hl j
  have h2 := hC.is_rounds hIS ht j
  rw [depth_eq]
  unfold HL at h1
  split_ifs at h1 with hu
  · have := h2.2 hu; omega
  · have hne : (C j).rounds ≠ t := by
      intro heq
      have hsc : (C j).IsScan := by
        cases h : C j with
        | init i x => rw [h] at heq; simp [St.rounds] at heq; omega
        | upd s => rw [h] at hu; exact absurd rfl hu
        | scan s v => trivial
      have := (decided_isSome_iff hIS _).2 ⟨hsc, heq⟩
      rw [hj] at this; simp at this
    have := h2.1; omega


end IS

/-! ## Lifting `A`-states -/

section Lift
variable {δ1 : Protocol P XT M} {t : ℕ} (hIS : IsIS δ1 t) {C1 : Config P XT} (hC1 : Reach δ1 C1)

include hC1 in
lemma pid_lift (s : St P M) : (lift C1 s).pid = s.pid := by
  match s with
  | init k y => exact hC1.pid k
  | upd s => simp [lift, St.pid, pid_lift s]
  | scan s v => simp [lift, St.pid, pid_lift s]

lemma hist_lift (s : St P M) : (lift C1 s).hist = (C1 s.pid).hist ++ s.hist.map (lift C1) := by
  match s with
  | init k y => simp [lift, St.hist, St.pid]
  | upd s => simp [lift, St.hist, St.pid, hist_lift s]
  | scan s v => simp [lift, St.hist, St.pid, hist_lift s]

include hIS

lemma rounds_lift : ∀ (s : St P M), Good δ1 C1 s → (lift C1 s).rounds = t + s.rounds
  | init k y, hg => by simp [lift, St.rounds, (decided_fin_scan hIS hg).2]
  | upd s, hg => by simp [lift, St.rounds, rounds_lift s hg]
  | scan s v, hg => by simp [lift, St.rounds, rounds_lift s hg.1]; omega

lemma isUpd_lift : ∀ (s : St P M), Good δ1 C1 s → IsUpd (lift C1 s) = IsUpd s
  | init k y, hg => by
    have := (decided_fin_scan hIS hg).1
    simp only [lift, IsUpd]
    cases h : C1 k <;> simp_all [St.IsScan, IsUpd]
  | upd s, _ => rfl
  | scan s v, _ => rfl

lemma good_hist : ∀ (s : St P M), Good δ1 C1 s → ∀ s' ∈ s.hist, Good δ1 C1 s'
  | init k y, _, s', h => by simp [St.hist] at h
  | upd s, hg, s', h => by
    simp only [St.hist, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact good_hist s hg s' h
    · exact hg
  | scan s v, hg, s', h => good_hist s hg.1 s' h

include hC1

lemma depth_lift (ht : 0 < t) : ∀ (s : St P M), Good δ1 C1 s → (lift C1 s).depth = 2 * t + s.depth
  | init k y, hg => by
    simp only [lift, St.depth]; rw [hC1.depth_fin hIS ht (by rw [hg]; rfl)]; rfl
  | upd s, hg => by simp [lift, St.depth, depth_lift ht s hg]; omega
  | scan s v, hg => by simp [lift, St.depth, depth_lift ht s hg.1]; omega

mutual
lemma toAS_lift : ∀ (s : St P M), Good δ1 C1 s → toAS δ1 t (lift C1 s) = s
  | init k y, hg => by
    have hs := decided_fin_scan hIS hg
    simp only [lift]
    cases h : C1 k with
    | init i x => rw [h] at hs; exact absurd hs.1 id
    | upd s => rw [h] at hs; exact absurd hs.1 id
    | scan s v =>
      have hg' : decided δ1 (C1 k) = some y := hg
      rw [h] at hg'
      have hr : (scan s v).rounds = t := by rw [← h]; exact hs.2
      have hp : s.pid = k := by have := hC1.pid k; rw [h] at this; simpa [St.pid] using this
      simp only [decided_scan] at hg'
      simp only [toAS, if_pos hr.le, hp, hg']; rfl
  | upd s, hg => by simp only [lift, toAS]; rw [toAS_lift s hg]
  | scan s v, hg => by
    have hr := rounds_lift hIS (scan s v) hg
    simp only [lift] at hr ⊢
    simp only [toAS, hr]
    rw [if_neg (by simp [St.rounds])]
    rw [toAS_lift s hg.1]
    congr 1; funext j; exact toASO_liftO (v j) (hg.2 j)
lemma toASO_liftO : ∀ (o : Option (St P M)), GoodO δ1 C1 o → toASO δ1 t (liftO C1 o) = o
  | none, _ => rfl
  | some s, hg => by simp only [liftO, toASO]; rw [toAS_lift s hg]
end

end Lift

section Congr
variable {δ1 : Protocol P XT M} {C1 C1' : Config P XT}
  (hag : ∀ k, (decided δ1 (C1 k)).isSome → C1' k = C1 k)
include hag

mutual
lemma lift_congr : ∀ (s : St P M), Good δ1 C1 s → lift C1' s = lift C1 s
  | init k y, hg => by simp only [lift]; exact hag k (by rw [hg]; rfl)
  | upd s, hg => by simp only [lift]; rw [lift_congr s hg]
  | scan s v, hg => by
    simp only [lift]; rw [lift_congr s hg.1]; congr 1; funext j; exact liftO_congr (v j) (hg.2 j)
lemma liftO_congr : ∀ (o : Option (St P M)), GoodO δ1 C1 o → liftO C1' o = liftO C1 o
  | none, _ => rfl
  | some s, hg => by simp only [liftO]; rw [lift_congr s hg]
end

mutual
lemma good_mono : ∀ (s : St P M), Good δ1 C1 s → Good δ1 C1' s
  | init k y, hg => by simp only [Good] at hg ⊢; rw [hag k (by rw [hg]; rfl)]; exact hg
  | upd s, hg => good_mono s hg
  | scan s v, hg => ⟨good_mono s hg.1, fun j => goodO_mono (v j) (hg.2 j)⟩
lemma goodO_mono : ∀ (o : Option (St P M)), GoodO δ1 C1 o → GoodO δ1 C1' o
  | none, _ => trivial
  | some s, hg => good_mono s hg
end

end Congr

lemma liftO_eq_map (C1 : Config P XT) (o : Option (St P M)) : liftO C1 o = o.map (lift C1) := by
  cases o <;> rfl

/-! ## Steps of the composition -/

section Steps
variable {δ1 : Protocol P XT M} {t : ℕ} (hIS : IsIS δ1 t) (ht : 0 < t)
  {δA : Protocol P M ZS} {h : P → ZS → ZT} {C1 : Config P XT} {CA : Config P M} {u : P → M}
include hIS ht

lemma hist_Ycfg_lt (hI : Inv δ1 C1 CA u) (k : P) {r : ℕ} (hr : r < t) :
    (Ycfg δ1 C1 CA k).hist[r]? = (C1 k).hist[r]? := by
  unfold Ycfg; split_ifs with hk
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
    obtain ⟨-, hg, hp⟩ := hI.fin k y hy
    rw [hist_lift, hp, List.getElem?_append_left]
    rw [hI.reach.hist_length_fin hIS ht hk]; exact hr
  · rfl

lemma hist_Ycfg_ge (hI : Inv δ1 C1 CA u) (k : P) (r : ℕ) :
    (Ycfg δ1 C1 CA k).hist[t + r]? = liftO C1 ((CA k).hist[r]?) := by
  unfold Ycfg; split_ifs with hk
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
    obtain ⟨-, hg, hp⟩ := hI.fin k y hy
    rw [hist_lift, hp, List.getElem?_append_right]
    · rw [hI.reach.hist_length_fin hIS ht hk, Nat.add_sub_cancel_left, List.getElem?_map,
        liftO_eq_map]
    · rw [hI.reach.hist_length_fin hIS ht hk]; omega
  · have hk' : decided δ1 (C1 k) = none := by simpa using hk
    rw [hI.unfin k hk', List.getElem?_eq_none, List.getElem?_eq_none]
    · rfl
    · simp [St.hist]
    · have := hI.reach.hist_length_le hIS ht k; omega

lemma decided_lift : ∀ (s : St P M), Good δ1 C1 s → Reach δ1 C1 →
    decided (compP δ1 t δA h) (lift C1 s) = (decided δA s).map (h s.pid)
  | init k y, hg, hC1 => by
    have hs := decided_fin_scan hIS hg
    simp only [lift, decided_init, Option.map_none]
    cases hc : C1 k with
    | init i x => rfl
    | upd s => rfl
    | scan s v =>
      rw [hc] at hs
      simp [compP, hs.2]
  | upd s, _, _ => rfl
  | scan s v, hg, hC1 => by
    have hr := rounds_lift hIS (scan s v) hg
    have hp := pid_lift hC1 (scan s v)
    simp only [lift] at hr hp ⊢
    simp only [decided_scan, compP, hr, hp]
    have hta := toAS_lift hIS hC1 (scan s v) hg
    simp only [lift] at hta
    rw [if_neg (by simp [St.rounds]), hta]

lemma outs_Ycfg (hI : Inv δ1 C1 CA u) (j : P) :
    outs (compP δ1 t δA h) (Ycfg δ1 C1 CA) j = (outs δA CA j).map (h j) := by
  unfold outs Ycfg; split_ifs with hk
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
    obtain ⟨-, hg, hp⟩ := hI.fin j y hy
    rw [decided_lift hIS ht _ hg hI.reach, hp]
  · have hk' : decided δ1 (C1 j) = none := by simpa using hk
    rw [hI.unfin j hk']
    have := (hI.reach.is_rounds hIS ht j).1
    cases hc : C1 j with
    | init i x => rfl
    | upd s => rfl
    | scan s v => rw [hc] at this; simp [compP, this]

lemma active_Ycfg_of_unfin (hI : Inv δ1 C1 CA u) {p : P} (hp : decided δ1 (C1 p) = none) :
    Active (compP δ1 t δA h) (Ycfg δ1 C1 CA) p := by
  have := outs_Ycfg (δA := δA) (h := h) hIS ht hI p
  unfold outs at this; unfold Active; rw [this, hI.unfin p hp]; rfl

lemma active_Ycfg_iff_of_fin (hI : Inv δ1 C1 CA u) {p : P} (hp : (decided δ1 (C1 p)).isSome) :
    Active (compP δ1 t δA h) (Ycfg δ1 C1 CA) p ↔ Active δA CA p := by
  have := outs_Ycfg (δA := δA) (h := h) hIS ht hI p
  unfold outs at this; unfold Active; rw [this]; simp

/-- A step of a process that has not finished `A₁` is a step of `A₁`. -/
lemma stepY_A1 (hI : Inv δ1 C1 CA u) {p : P} (hp : decided δ1 (C1 p) = none)
    (hu : ∀ y, decided δ1 (stepState C1 p) = some y → y = u p) :
    step (Ycfg δ1 C1 CA) p = Ycfg δ1 (step C1 p) CA ∧ Inv δ1 (step C1 p) CA u := by
  have hYp : Ycfg δ1 C1 CA p = C1 p := by simp [Ycfg, hp]
  have hss : stepState (Ycfg δ1 C1 CA) p = stepState C1 p := by
    rcases stepState_cases C1 p with ⟨s, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]; unfold stepState; rw [hYp, h1]; simp only
      congr 1; funext j
      have hr := (hI.reach.is_rounds hIS ht p).2 (by rw [h1]; rfl)
      rw [h1] at hr; simp only [St.rounds] at hr
      exact hist_Ycfg_lt hIS ht hI j hr
    · rw [h2]; unfold stepState; rw [hYp]
      split
      · next s hs => exact absurd hs (h1 s)
      · rfl
  have hag : ∀ k, (decided δ1 (C1 k)).isSome → step C1 p k = C1 k := fun k hk => by
    apply step_ne; rintro rfl; rw [hp] at hk; simp at hk
  refine ⟨funext fun j => ?_, ⟨hI.reach.step hp, fun j hj => ?_, fun j y hj => ?_⟩⟩
  · by_cases hj : j = p
    · subst hj
      rw [step_self, hss]
      unfold Ycfg; rw [step_self, hI.unfin j hp]
      split_ifs <;> simp [lift]
    · rw [step_ne _ hj]
      unfold Ycfg; rw [step_ne _ hj]
      split_ifs with hk
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
        exact (lift_congr hag _ (hI.fin j y hy).2.1).symm
      · rfl
  · by_cases hjp : j = p
    · subst hjp; exact hI.unfin j hp
    · rw [step_ne _ hjp] at hj; exact hI.unfin j hj
  · by_cases hjp : j = p
    · subst hjp
      rw [step_self] at hj
      have hy := hu y hj
      subst hy
      refine ⟨rfl, ?_, ?_⟩
      · rw [hI.unfin j hp]; simp only [Good]; rw [step_self]; exact hj
      · rw [hI.unfin j hp]; rfl
    · rw [step_ne _ hjp] at hj
      obtain ⟨h1, h2, h3⟩ := hI.fin j y hj
      exact ⟨h1, good_mono hag _ h2, h3⟩

/-- A step of a process that finished `A₁` is a step of `A`. -/
lemma stepY_A (hI : Inv δ1 C1 CA u) {p : P} (hp : (decided δ1 (C1 p)).isSome) :
    step (Ycfg δ1 C1 CA) p = Ycfg δ1 C1 (step CA p) ∧ Inv δ1 C1 (step CA p) u := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hp
  obtain ⟨-, hg, hpid⟩ := hI.fin p y hy
  have hYp : Ycfg δ1 C1 CA p = lift C1 (CA p) := by simp [Ycfg, hp]
  have hss : stepState (Ycfg δ1 C1 CA) p = lift C1 (stepState CA p) := by
    rcases stepState_cases CA p with ⟨s, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]; unfold stepState; rw [hYp, h1]; simp only [lift]
      congr 1; funext j
      rw [h1] at hg
      rw [rounds_lift hIS s hg]
      exact hist_Ycfg_ge hIS ht hI j s.rounds
    · rw [h2]; unfold stepState; rw [hYp]
      split
      · next s hs =>
        have := isUpd_lift hIS (CA p) hg
        rw [hs] at this
        cases hc : CA p <;> simp_all [IsUpd]
      · rfl
  have hgood : Good δ1 C1 (stepState CA p) := by
    rcases stepState_cases CA p with ⟨s, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]; rw [h1] at hg
      refine ⟨hg, fun k => ?_⟩
      show GoodO δ1 C1 ((CA k).hist[s.rounds]?)
      by_cases hk : (decided δ1 (C1 k)).isSome
      · obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 hk
        cases he : (CA k).hist[s.rounds]? with
        | none => trivial
        | some e =>
          exact good_hist hIS _ (hI.fin k y' hy').2.1 e (List.mem_of_getElem? he)
      · rw [hI.unfin k (by simpa using hk)]; simp [St.hist, GoodO]
    · rw [h2]; exact hg
  refine ⟨funext fun j => ?_, ⟨hI.reach, fun j hj => ?_, fun j y' hj => ?_⟩⟩
  · by_cases hj : j = p
    · subst hj
      rw [step_self, hss]
      simp [Ycfg, hp]
    · rw [step_ne _ hj]; unfold Ycfg; rw [step_ne _ hj]
  · have hjp : j ≠ p := by rintro rfl; rw [hj] at hp; simp at hp
    rw [step_ne _ hjp]; exact hI.unfin j hj
  · by_cases hjp : j = p
    · subst hjp
      refine ⟨(hI.fin j y' hj).1, ?_, ?_⟩
      · rw [step_self]; exact hgood
      · rw [step_self, pid_stepState]; exact hpid
    · rw [step_ne _ hjp]; exact hI.fin j y' hj


omit hIS ht in
lemma Inv.init (x : P → XT) (u : P → M) : Inv δ1 (initC x) (initC u) u :=
  ⟨reach_initC x, fun j _ => rfl, fun j y hj => by simp [initC] at hj⟩

omit hIS ht in
lemma Ycfg_initC (x : P → XT) (CA : Config P M) : Ycfg δ1 (initC x) CA = initC x := by
  funext j; simp [Ycfg, initC]

omit ht in
/-- Under the invariant, re-initialising the processes that took no step of `A` with inputs that
agree with the `A₁`-outputs changes nothing relevant. -/
lemma inv_reinit (hI : Inv δ1 C1 CA u) {u' : P → M}
    (hu : ∀ j, (decided δ1 (C1 j)).isSome → u' j = u j) :
    Inv δ1 C1 (reinit CA u') u' ∧ Ycfg δ1 C1 (reinit CA u') = Ycfg δ1 C1 CA ∧
      ∀ j, (decided δ1 (C1 j)).isSome → reinit CA u' j = CA j := by
  have hfin : ∀ j, (decided δ1 (C1 j)).isSome → reinit CA u' j = CA j := by
    intro j hj
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hj
    obtain ⟨h1, h2, h3⟩ := hI.fin j y hy
    unfold Cslib.NIS.reinit
    split_ifs with hi
    · obtain ⟨k, z, hk⟩ := (St.isInit_iff _).1 hi
      rw [hk] at h2 h3
      simp only [St.pid] at h3; subst h3
      simp only [Good] at h2
      rw [hy] at h2; cases h2
      rw [hk, hu k hj, ← h1]
    · rfl
  refine ⟨⟨hI.reach, fun j hj => ?_, fun j y hj => ?_⟩, ?_, hfin⟩
  · rw [reinit_of_isInit (by rw [hI.unfin j hj]; trivial)]
  · have hs : (decided δ1 (C1 j)).isSome := by rw [hj]; rfl
    rw [hfin j hs, hu j hs]; exact hI.fin j y hj
  · funext j; unfold Ycfg; split_ifs with hj
    · rw [hfin j hj]
    · rfl

/-- Every reachable configuration of the composition is `Ycfg C₁ CA` for some `C₁`, `CA`. -/
lemma reach_decomp {C : Config P XT} (hC : Reach (compP δ1 t δA h) C) :
    ∃ C1 CA u, Inv δ1 C1 CA u ∧ C = Ycfg δ1 C1 CA := by
  obtain ⟨x, α, hα, rfl⟩ := hC
  induction α using List.reverseRecOn with
  | nil => exact ⟨initC x, initC default, default, Inv.init x default, (Ycfg_initC x _).symm⟩
  | append_singleton α q ih =>
    rw [isSched_concat] at hα
    obtain ⟨C1, CA, u, hI, hE⟩ := ih hα.1
    rw [exec_append]; simp only [exec_cons, exec_nil]
    rw [hE]
    by_cases hq : (decided δ1 (C1 q)).isSome
    · obtain ⟨h1, h2⟩ := stepY_A hIS ht hI hq
      exact ⟨C1, step CA q, u, h2, h1⟩
    · have hq' : decided δ1 (C1 q) = none := by simpa using hq
      let u' := Function.update u q ((decided δ1 (stepState C1 q)).getD (u q))
      have hu' : ∀ j, (decided δ1 (C1 j)).isSome → u' j = u j := fun j hj => by
        have : j ≠ q := by rintro rfl; exact hq hj
        simp [u', Function.update_of_ne this]
      obtain ⟨hI', hY', -⟩ := inv_reinit hIS hI hu'
      obtain ⟨h1, h2⟩ := stepY_A1 hIS ht hI' hq' (fun y hy => by simp [u', hy])
      exact ⟨step C1 q, reinit CA u', u', h2, by rw [← hY', h1]⟩

/-! ### Reading `C₁` and `CA` off a configuration -/

/-- The state at depth `2t` (the end of `A₁`), or the state itself if it is not deeper. -/
def truncS (t : ℕ) : St P XT → St P XT
  | init i x => init i x
  | upd s => if (upd s).depth ≤ 2 * t then upd s else truncS t s
  | scan s v => if (scan s v).depth ≤ 2 * t then scan s v else truncS t s

omit [Inhabited M] hIS ht in
lemma truncS_of_le {s : St P XT} (hs : s.depth ≤ 2 * t) : truncS t s = s := by
  cases s with
  | init i x => rfl
  | upd s => simp [truncS, hs]
  | scan s v => simp [truncS, hs]

omit ht in
lemma truncS_lift (ht : 0 < t) (hC1 : Reach δ1 C1) :
    ∀ (s : St P M), Good δ1 C1 s → truncS t (lift C1 s) = C1 s.pid
  | init k y, hg => by
    simp only [lift, St.pid]
    exact truncS_of_le (le_of_eq (hC1.depth_fin hIS ht (by rw [hg]; rfl)))
  | upd s, hg => by
    have := depth_lift hIS hC1 ht (upd s) hg
    simp only [lift] at this ⊢
    rw [truncS, if_neg (by rw [this]; simp [St.depth]), truncS_lift ht hC1 s hg]; rfl
  | scan s v, hg => by
    have := depth_lift hIS hC1 ht (scan s v) hg
    simp only [lift] at this ⊢
    rw [truncS, if_neg (by rw [this]; simp [St.depth]), truncS_lift ht hC1 s hg.1]; rfl

/-- The `A₁`-part of a configuration of the composition. -/
def trunc (t : ℕ) (C : Config P XT) : Config P XT := fun j => truncS t (C j)

/-- The `A`-part of a configuration of the composition, with inputs `u` for the processes that have
not finished `A₁`. -/
def toAC (δ1 : Protocol P XT M) (t : ℕ) (C : Config P XT) (u : P → M) : Config P M :=
  fun j => if (decided δ1 (truncS t (C j))).isSome then toAS δ1 t (C j) else init j (u j)

lemma trunc_Ycfg (hI : Inv δ1 C1 CA u) : trunc t (Ycfg δ1 C1 CA) = C1 := by
  funext j; unfold trunc Ycfg; split_ifs with hj
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hj
    obtain ⟨-, hg, hp⟩ := hI.fin j y hy
    rw [truncS_lift hIS ht hI.reach _ hg, hp]
  · exact truncS_of_le (hI.reach.depth_unfin hIS ht (by simpa using hj)).le

lemma toAC_Ycfg (hI : Inv δ1 C1 CA u) {j : P} (hj : (decided δ1 (C1 j)).isSome) (u' : P → M) :
    toAC δ1 t (Ycfg δ1 C1 CA) u' j = CA j := by
  have := congrFun (trunc_Ycfg hIS ht hI) j
  unfold trunc at this
  unfold toAC; rw [this, if_pos hj]
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hj
  simp only [Ycfg, if_pos hj]
  exact toAS_lift hIS hI.reach _ (hI.fin j y hy).2.1

lemma toAC_Ycfg_unfin (hI : Inv δ1 C1 CA u) {j : P} (hj : ¬ (decided δ1 (C1 j)).isSome)
    (u' : P → M) : toAC δ1 t (Ycfg δ1 C1 CA) u' j = init j (u' j) := by
  have := congrFun (trunc_Ycfg hIS ht hI) j
  unfold trunc at this
  unfold toAC; rw [this, if_neg hj]

/-- Canonical decomposition: with inputs `u` agreeing with the `A₁`-outputs. -/
lemma canonical (hI : Inv δ1 C1 CA u) (u' : P → M)
    (hu : ∀ j y, decided δ1 (C1 j) = some y → u' j = y) :
    Inv δ1 (trunc t (Ycfg δ1 C1 CA)) (toAC δ1 t (Ycfg δ1 C1 CA) u') u' ∧
      Ycfg δ1 C1 CA = Ycfg δ1 (trunc t (Ycfg δ1 C1 CA)) (toAC δ1 t (Ycfg δ1 C1 CA) u') := by
  rw [trunc_Ycfg hIS ht hI]
  refine ⟨⟨hI.reach, fun j hj => ?_, fun j y hj => ?_⟩, ?_⟩
  · exact toAC_Ycfg_unfin hIS ht hI (by simp [hj]) u'
  · have hs : (decided δ1 (C1 j)).isSome := by rw [hj]; rfl
    rw [toAC_Ycfg hIS ht hI hs]
    obtain ⟨-, h2, h3⟩ := hI.fin j y hj
    exact ⟨(hu j y hj).symm, h2, h3⟩
  · funext j
    by_cases hj : (decided δ1 (C1 j)).isSome
    · have e := toAC_Ycfg hIS ht hI hj u'
      have l : Ycfg δ1 C1 (toAC δ1 t (Ycfg δ1 C1 CA) u') j =
          lift C1 (toAC δ1 t (Ycfg δ1 C1 CA) u' j) := if_pos hj
      rw [l, e]; exact if_pos hj
    · have l : ∀ CA', Ycfg δ1 C1 CA' j = C1 j := fun _ => if_neg hj
      rw [l, l]

lemma depth_Ycfg (hI : Inv δ1 C1 CA u) (j : P) :
    (Ycfg δ1 C1 CA j).depth = (C1 j).depth + (CA j).depth ∧ (C1 j).depth ≤ 2 * t := by
  unfold Ycfg; split_ifs with hj
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hj
    rw [depth_lift hIS hI.reach ht _ (hI.fin j y hy).2.1, hI.reach.depth_fin hIS ht hj]
    exact ⟨rfl, le_rfl⟩
  · have hj' : decided δ1 (C1 j) = none := by simpa using hj
    rw [hI.unfin j hj']
    exact ⟨by simp [St.depth], (hI.reach.depth_unfin hIS ht hj').le⟩

/-! ### Schedules of the composition -/

/-- A schedule of `A₁` (whose outputs agree with `u`) is a schedule of the composition. -/
lemma execY_A1 : ∀ (μ : List P) {C1 : Config P XT}, Inv δ1 C1 CA u → IsSched δ1 C1 μ →
    (∀ j y, decided δ1 (exec C1 μ j) = some y → y = u j) →
    IsSched (compP δ1 t δA h) (Ycfg δ1 C1 CA) μ ∧ exec (Ycfg δ1 C1 CA) μ = Ycfg δ1 (exec C1 μ) CA ∧
      Inv δ1 (exec C1 μ) CA u
  | [], C1, hI, _, _ => ⟨trivial, rfl, hI⟩
  | q :: μ, C1, hI, hμ, hu => by
    obtain ⟨hq, hμ⟩ := hμ
    have hu1 : ∀ y, decided δ1 (stepState C1 q) = some y → y = u q := fun y hy => by
      have : exec (step C1 q) μ q = step C1 q q :=
        exec_of_terminated hμ (by rw [step_self, hy]; simp)
      exact hu q y (by rw [exec_cons, this, step_self, hy])
    obtain ⟨h1, h2⟩ := stepY_A1 hIS ht hI hq hu1
    obtain ⟨h3, h4, h5⟩ := execY_A1 μ h2 hμ hu
    exact ⟨⟨active_Ycfg_of_unfin hIS ht hI hq, by rw [h1]; exact h3⟩, by
      rw [exec_cons, h1, h4]; rfl, h5⟩

/-- A schedule of `A` by processes that finished `A₁` is a schedule of the composition. -/
lemma execY_A : ∀ (μ : List P) {CA : Config P M}, Inv δ1 C1 CA u → IsSched δA CA μ →
    (∀ p ∈ μ, (decided δ1 (C1 p)).isSome) →
    IsSched (compP δ1 t δA h) (Ycfg δ1 C1 CA) μ ∧ exec (Ycfg δ1 C1 CA) μ = Ycfg δ1 C1 (exec CA μ) ∧
      Inv δ1 C1 (exec CA μ) u
  | [], CA, hI, _, _ => ⟨trivial, rfl, hI⟩
  | q :: μ, CA, hI, hμ, hf => by
    obtain ⟨hq, hμ⟩ := hμ
    have hfq := hf q (by simp)
    obtain ⟨h1, h2⟩ := stepY_A hIS ht hI hfq
    obtain ⟨h3, h4, h5⟩ := execY_A μ h2 hμ (fun p hp => hf p (by simp [hp]))
    exact ⟨⟨(active_Ycfg_iff_of_fin hIS ht hI hfq).2 hq, by rw [h1]; exact h3⟩, by
      rw [exec_cons, h1, h4]; rfl, h5⟩

/-- Decomposition of a schedule of the composition into a schedule of `A₁` and a schedule of `A`
(by processes that have finished `A₁`), the inputs of `A` being updated to the new outputs of
`A₁`. -/
lemma decompY : ∀ (μ : List P), Inv δ1 C1 CA u → IsSched (compP δ1 t δA h) (Ycfg δ1 C1 CA) μ →
    ∃ μ1 μ' u', (∀ p ∈ μ1, p ∈ μ) ∧ (∀ p ∈ μ', p ∈ μ) ∧ IsSched δ1 C1 μ1 ∧
      IsSched δA (reinit CA u') μ' ∧ (∀ p ∈ μ', (decided δ1 (exec C1 μ1 p)).isSome) ∧
      Inv δ1 (exec C1 μ1) (exec (reinit CA u') μ') u' ∧
      exec (Ycfg δ1 C1 CA) μ = Ycfg δ1 (exec C1 μ1) (exec (reinit CA u') μ') ∧
      (∀ j, (decided δ1 (C1 j)).isSome → u' j = u j) := by
  intro μ hI hμ
  induction μ using List.reverseRecOn with
  | nil =>
    obtain ⟨h1, h2, -⟩ := inv_reinit hIS hI (u' := u) (fun _ _ => rfl)
    exact ⟨[], [], u, by simp, by simp, trivial, trivial, by simp, h1, by simpa using h2.symm,
      fun _ _ => rfl⟩
  | append_singleton μ q ih =>
    rw [isSched_concat] at hμ
    obtain ⟨μ1, μ', u', hm1, hm', hs1, hs', hfin, hI', hE, hu'⟩ := ih hμ.1
    have hq := hμ.2
    rw [hE] at hq
    rw [exec_append, hE]; simp only [exec_cons, exec_nil]
    have hmono : ∀ j, (decided δ1 (C1 j)).isSome → exec C1 μ1 j = C1 j := fun j hj =>
      exec_of_terminated hs1 (Option.isSome_iff_ne_none.1 hj)
    by_cases hqf : (decided δ1 (exec C1 μ1 q)).isSome
    · obtain ⟨h1, h2⟩ := stepY_A hIS ht hI' hqf
      refine ⟨μ1, μ' ++ [q], u', fun p hp => by simp [hm1 p hp], ?_, hs1, ?_, ?_, ?_, ?_, hu'⟩
      · intro p hp; simp at hp; rcases hp with hp | rfl
        · simp [hm' p hp]
        · simp
      · rw [isSched_concat]; exact ⟨hs', (active_Ycfg_iff_of_fin hIS ht hI' hqf).1 hq⟩
      · intro p hp; simp at hp; rcases hp with hp | rfl
        · exact hfin p hp
        · exact hqf
      · rw [exec_append]; exact h2
      · rw [h1, exec_append]; rfl
    · have hq' : decided δ1 (exec C1 μ1 q) = none := by simpa using hqf
      let u'' := Function.update u' q ((decided δ1 (stepState (exec C1 μ1) q)).getD (u' q))
      have hqμ' : q ∉ μ' := fun hm => hqf (hfin q hm)
      have hu'' : ∀ j, (decided δ1 (exec C1 μ1 j)).isSome → u'' j = u' j := fun j hj => by
        have : j ≠ q := by rintro rfl; exact hqf hj
        simp [u'', Function.update_of_ne this]
      obtain ⟨hI'', hY'', -⟩ := inv_reinit hIS hI' hu''
      -- re-initialising before or after `μ'` is the same
      have hre := exec_reinit (δ := δA) (reinit CA u') u'' (α := μ') (fun j hj hi => by
        rw [reinit_of_isInit ((isInit_reinit_iff _ _ _).1 hi)]
        have : j ≠ q := by rintro rfl; exact hqμ' hj
        simp [u'', Function.update_of_ne this])
      rw [reinit_reinit] at hre
      obtain ⟨h1, h2⟩ := stepY_A1 hIS ht hI'' hq' (fun y hy => by simp [u'', hy])
      refine ⟨μ1 ++ [q], μ', u'', ?_, fun p hp => by simp [hm' p hp], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp; simp at hp; rcases hp with hp | rfl
        · simp [hm1 p hp]
        · simp
      · rw [isSched_concat]; exact ⟨hs1, hq'⟩
      · rw [hre.2]; exact hs'
      · intro p hp
        rw [exec_append]; simp only [exec_cons, exec_nil]
        have : p ≠ q := by rintro rfl; exact hqμ' hp
        rw [step_ne _ this]; exact hfin p hp
      · rw [exec_append, hre.1]; exact h2
      · rw [← hY'', h1, exec_append, hre.1]; rfl
      · intro j hj
        have : j ≠ q := by intro hjq; rw [← hjq, hmono j hj] at hqf; exact hqf hj
        simp [u'', Function.update_of_ne this, hu' j hj]

end Steps

/-- In an IS protocol every set of processes can run to completion. -/
lemma exists_complete {δ1 : Protocol P XT M} {t : ℕ} (hIS : IsIS δ1 t) (ht : 0 < t)
    {C : Config P XT} (hC : Reach δ1 C) (Ps : Finset P) :
    ∃ μ, (∀ p ∈ μ, p ∈ Ps) ∧ IsSched δ1 C μ ∧ ∀ p ∈ Ps, (decided δ1 (exec C μ p)).isSome := by
  suffices ∀ n, ∀ C : Config P XT, Reach δ1 C → ∑ p ∈ Ps, (2 * t - (C p).depth) = n →
      ∃ μ, (∀ p ∈ μ, p ∈ Ps) ∧ IsSched δ1 C μ ∧ ∀ p ∈ Ps, (decided δ1 (exec C μ p)).isSome from
    this _ C hC rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hC hn
    by_cases hall : ∀ p ∈ Ps, (decided δ1 (C p)).isSome
    · exact ⟨[], by simp, trivial, hall⟩
    · push_neg at hall
      obtain ⟨p, hp, hpu⟩ := hall
      have hpu' : decided δ1 (C p) = none := by simpa using hpu
      have hd := hC.depth_unfin hIS ht hpu'
      have hlt : ∑ q ∈ Ps, (2 * t - (step C p q).depth) < n := by
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro q _
          by_cases hq : q = p
          · subst hq; simp; omega
          · rw [step_ne _ hq]
        · exact ⟨p, hp, by simp; omega⟩
      obtain ⟨μ, h1, h2, h3⟩ := ih _ hlt (step C p) (hC.step hpu') rfl
      refine ⟨p :: μ, fun q hq => ?_, ⟨hpu', h2⟩, h3⟩
      simp at hq; rcases hq with rfl | hq
      · exact hp
      · exact h1 q hq

end Podc.ExtensionBasedReductions
