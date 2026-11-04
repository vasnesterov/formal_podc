import Papers.PODC2011.HomonymsBA.Basic
import Papers.PODC2011.HomonymsBA.ClassicalBA

/-!
# Proposition 2: synchronous BA is solvable with innumerate processes if `ℓ > 3t`

The transformation `T(A)` of Figure 3 of the paper. Given a classical synchronous Byzantine
agreement algorithm `A` for `ℓ` processes with unique identifiers (here: an algorithm of CSLib's
classical model `Cslib.Byzantine.PartialSync` with lock-step runs, `gst = 0`, `δ = 0`), the
processes with identifier `i` (the *group* `G(i)`) cooperatively simulate process `i` of `A`.
Each phase has three rounds:

* *selection* (`rnd ≡ 0 mod 3`): send the simulated state; adopt a deterministic choice among the
  states received from identifier `i` (`pick`);
* *deciding* (`rnd ≡ 1`): send the (latched) decision of the simulated process; decide `v` if
  `(j, v)` was received from `t + 1` different identifiers `j` (`decRule`);
* *running* (`rnd ≡ 2`): send `A`'s message of the selected state; from each identifier keep the
  message only if it is the unique one received from it (`filt`); take `A`'s step.

The algorithm depends on the received pairs only through membership: innumerate.

Correctness (`TA_solves`): from a run `α_H` of `T(A)` we build a run `α_S` of `A` (`simRun`) in
which identifier `i` is correct iff its group is correct, the correct groups' selected states are
the states of `α_S` (`st_simRun`) and the Byzantine simulated processes deliver what the selected
process of the receiving group kept from them.

Deviations: `A` may send different messages to different identifiers (the paper assumes
broadcast WLOG); the decision of the simulated process is latched (`lat`) so that a correct group
keeps announcing it; a process decides at most once (`out` is latched).

Main results: `TA_solves`, `TA_innumerate`, `prop2`, `thm3`.
-/

namespace Podc.HomonymsBA

open Finset

local notation "CAlg" => Cslib.Byzantine.PartialSync.Algorithm
local notation "CRun" => Cslib.Byzantine.PartialSync.Run

namespace Sim

/-- Messages of `T(A)`. -/
inductive TMsg (S M V : Type*)
  | sel (a : S)
  | dec (o : Option V)
  | run (m : List M)

/-- States of `T(A)`: identifier, round counter, simulated state, latched decision of the
simulated process, own decision. -/
structure TSt (ℓ : ℕ) (S V : Type*) where
  id : Fin ℓ
  rnd : ℕ
  a : S
  lat : Option V
  out : Option V

/-- Keep the first decision. -/
def latch {V : Type*} (o o' : Option V) : Option V :=
  match o with
  | some x => some x
  | none => o'

@[simp] lemma latch_some {V : Type*} (x : V) (o' : Option V) : latch (some x) o' = some x := rfl
@[simp] lemma latch_none {V : Type*} (o' : Option V) : latch none o' = o' := rfl

open Classical in
/-- Deterministic choice in a set. -/
noncomputable def pick {S : Type*} (X : Set S) (d : S) : S := if h : X.Nonempty then h.some else d

lemma pick_of_nonempty {S : Type*} {X : Set S} (h : X.Nonempty) (d : S) : pick X d = h.some := by
  simp [pick, h]

variable {ℓ : ℕ} {S M V : Type*}

open Classical in
/-- The deciding rule: a value announced by `t + 1` different identifiers. -/
noncomputable def decRule (t : ℕ) (R : Multiset (Fin ℓ × TMsg S M V)) : Option V :=
  if h : ∃ v, t + 1 ≤ (univ.filter fun j => (j, TMsg.dec (some v)) ∈ R).card then
    some (Classical.choose h) else none

open Classical in
/-- From identifier `j`, the running-round message if it is unique, else nothing (`[]`). -/
noncomputable def filt (R : Multiset (Fin ℓ × TMsg S M V)) (j : Fin ℓ) : List M :=
  if h : ∃ m, (j, TMsg.run m) ∈ R ∧ ∀ m', (j, TMsg.run m') ∈ R → m' = m then Classical.choose h
  else []

/-- **The algorithm `T(A)`** (Figure 3). -/
noncomputable def TA (t : ℕ) (A : CAlg (Fin ℓ) M S V V) : Algorithm ℓ V (TMsg S M V) (TSt ℓ S V) where
  init i v := ⟨i, 0, A.init i v, none, none⟩
  send s j := if s.rnd % 3 = 0 then some (.sel s.a) else if s.rnd % 3 = 1 then some (.dec s.lat)
    else some (.run (A.send s.id s.a j))
  step s R :=
    if s.rnd % 3 = 0 then
      ⟨s.id, s.rnd + 1, pick {x | (s.id, TMsg.sel x) ∈ R} s.a,
        latch s.lat (A.decide s.id (pick {x | (s.id, TMsg.sel x) ∈ R} s.a)), s.out⟩
    else if s.rnd % 3 = 1 then ⟨s.id, s.rnd + 1, s.a, s.lat, latch s.out (decRule t R)⟩
    else ⟨s.id, s.rnd + 1, A.step s.id s.a (filt R), s.lat, s.out⟩
  decide s := s.out

open Classical in
lemma decRule_congr (t : ℕ) {m m' : Multiset (Fin ℓ × TMsg S M V)} (h : ∀ x, x ∈ m ↔ x ∈ m') :
    decRule t m = decRule t m' := by
  have e : ∀ v, (univ.filter fun j => (j, TMsg.dec (some v)) ∈ m) =
      univ.filter fun j => (j, TMsg.dec (some v)) ∈ m' := fun v => by ext j; simp [h]
  unfold decRule; simp only [e]

/-- `T(A)` is innumerate. -/
theorem TA_innumerate (t : ℕ) (A : CAlg (Fin ℓ) M S V V) : (TA t A).Innumerate := by
  intro s m m' h
  have e : ∀ x, (x ∈ m) = (x ∈ m') := fun x => propext (h x)
  have hd := decRule_congr (S := S) (M := M) (V := V) t h
  have hf : filt m = filt m' := by
    funext j
    have hp : (fun mm => (j, TMsg.run mm) ∈ m ∧ ∀ m'', (j, TMsg.run m'') ∈ m → m'' = mm) =
        (fun mm => (j, TMsg.run mm) ∈ m' ∧ ∀ m'', (j, TMsg.run m'') ∈ m' → m'' = mm) := by
      funext mm; simp only [e]
    unfold filt
    rw [hp]
  simp only [TA, e, hd, hf]

/-! ### Equations of `T(A)` -/

variable {t : ℕ} (A : CAlg (Fin ℓ) M S V V)

lemma TA_step_sel {s : TSt ℓ S V} (h : s.rnd % 3 = 0) (m : Multiset (Fin ℓ × TMsg S M V)) :
    (TA t A).step s m = ⟨s.id, s.rnd + 1, pick {x | (s.id, TMsg.sel x) ∈ m} s.a,
      latch s.lat (A.decide s.id (pick {x | (s.id, TMsg.sel x) ∈ m} s.a)), s.out⟩ := by
  simp [TA, h]

lemma TA_step_dec {s : TSt ℓ S V} (h : s.rnd % 3 = 1) (m : Multiset (Fin ℓ × TMsg S M V)) :
    (TA t A).step s m = ⟨s.id, s.rnd + 1, s.a, s.lat, latch s.out (decRule t m)⟩ := by
  simp [TA, h]

lemma TA_step_run {s : TSt ℓ S V} (h : s.rnd % 3 = 2) (m : Multiset (Fin ℓ × TMsg S M V)) :
    (TA t A).step s m = ⟨s.id, s.rnd + 1, A.step s.id s.a (filt m), s.lat, s.out⟩ := by
  simp [TA, h]

lemma TA_send_sel {s : TSt ℓ S V} (h : s.rnd % 3 = 0) (j : Fin ℓ) :
    (TA t A).send s j = some (.sel s.a) := by simp [TA, h]

lemma TA_send_dec {s : TSt ℓ S V} (h : s.rnd % 3 = 1) (j : Fin ℓ) :
    (TA t A).send s j = some (.dec s.lat) := by simp [TA, h]

lemma TA_send_run {s : TSt ℓ S V} (h : s.rnd % 3 = 2) (j : Fin ℓ) :
    (TA t A).send s j = some (.run (A.send s.id s.a j)) := by simp [TA, h]

lemma TA_step_id_rnd (s : TSt ℓ S V) (m : Multiset (Fin ℓ × TMsg S M V)) :
    ((TA t A).step s m).id = s.id ∧ ((TA t A).step s m).rnd = s.rnd + 1 := by
  unfold TA; dsimp only; split_ifs <;> simp

/-! ### Runs of `T(A)` -/

variable {P : Type*} [Fintype P] [DecidableEq P] (R : Run P ℓ V (TMsg S M V))

lemma st_id_rnd : ∀ r q, (R.st (TA t A) r q).id = R.id q ∧ (R.st (TA t A) r q).rnd = r := by
  intro r
  induction r with
  | zero => intro q; exact ⟨rfl, rfl⟩
  | succ r ih =>
    intro q
    rw [Run.st_succ]
    obtain ⟨h1, h2⟩ := ih q
    obtain ⟨e1, e2⟩ := TA_step_id_rnd A (R.st (TA t A) r q) (R.inbox (TA t A) r q)
    exact ⟨e1.trans h1, e2.trans (by rw [h2])⟩

lemma st_id (r : ℕ) (q : P) : (R.st (TA t A) r q).id = R.id q := (st_id_rnd A R r q).1
lemma st_rnd (r : ℕ) (q : P) : (R.st (TA t A) r q).rnd = r := (st_id_rnd A R r q).2

lemma rnd0 (k : ℕ) (q : P) : (R.st (TA t A) (3 * k) q).rnd % 3 = 0 := by rw [st_rnd]; omega
lemma rnd1 (k : ℕ) (q : P) : (R.st (TA t A) (3 * k + 1) q).rnd % 3 = 1 := by rw [st_rnd]; omega
lemma rnd2 (k : ℕ) (q : P) : (R.st (TA t A) (3 * k + 2) q).rnd % 3 = 2 := by rw [st_rnd]; omega

lemma sel_a (k : ℕ) (q : P) : (R.st (TA t A) (3 * k + 1) q).a =
    pick {x | (R.id q, TMsg.sel x) ∈ R.inbox (TA t A) (3 * k) q} (R.st (TA t A) (3 * k) q).a := by
  rw [Run.st_succ, TA_step_sel A (rnd0 A R k q), st_id]

lemma sel_lat (k : ℕ) (q : P) : (R.st (TA t A) (3 * k + 1) q).lat =
    latch (R.st (TA t A) (3 * k) q).lat (A.decide (R.id q) (R.st (TA t A) (3 * k + 1) q).a) := by
  rw [sel_a]
  rw [Run.st_succ, TA_step_sel A (rnd0 A R k q), st_id]

lemma sel_out (k : ℕ) (q : P) : (R.st (TA t A) (3 * k + 1) q).out = (R.st (TA t A) (3 * k) q).out := by
  rw [Run.st_succ, TA_step_sel A (rnd0 A R k q)]

lemma dec_a (k : ℕ) (q : P) : (R.st (TA t A) (3 * k + 2) q).a = (R.st (TA t A) (3 * k + 1) q).a := by
  rw [Run.st_succ, TA_step_dec A (rnd1 A R k q)]

lemma dec_lat (k : ℕ) (q : P) :
    (R.st (TA t A) (3 * k + 2) q).lat = (R.st (TA t A) (3 * k + 1) q).lat := by
  rw [Run.st_succ, TA_step_dec A (rnd1 A R k q)]

lemma dec_out (k : ℕ) (q : P) : (R.st (TA t A) (3 * k + 2) q).out =
    latch (R.st (TA t A) (3 * k + 1) q).out (decRule t (R.inbox (TA t A) (3 * k + 1) q)) := by
  rw [Run.st_succ, TA_step_dec A (rnd1 A R k q)]

lemma run_a (k : ℕ) (q : P) : (R.st (TA t A) (3 * k + 3) q).a =
    A.step (R.id q) (R.st (TA t A) (3 * k + 2) q).a (filt (R.inbox (TA t A) (3 * k + 2) q)) := by
  rw [Run.st_succ, TA_step_run A (rnd2 A R k q), st_id]

lemma run_lat (k : ℕ) (q : P) :
    (R.st (TA t A) (3 * k + 3) q).lat = (R.st (TA t A) (3 * k + 2) q).lat := by
  rw [Run.st_succ, TA_step_run A (rnd2 A R k q)]

lemma run_out (k : ℕ) (q : P) :
    (R.st (TA t A) (3 * k + 3) q).out = (R.st (TA t A) (3 * k + 2) q).out := by
  rw [Run.st_succ, TA_step_run A (rnd2 A R k q)]

lemma send_sel (k : ℕ) (q : P) (j : Fin ℓ) :
    (TA t A).send (R.st (TA t A) (3 * k) q) j = some (.sel (R.st (TA t A) (3 * k) q).a) :=
  TA_send_sel A (rnd0 A R k q) j

lemma send_dec (k : ℕ) (q : P) (j : Fin ℓ) :
    (TA t A).send (R.st (TA t A) (3 * k + 1) q) j = some (.dec (R.st (TA t A) (3 * k + 1) q).lat) :=
  TA_send_dec A (rnd1 A R k q) j

lemma send_run (k : ℕ) (q : P) (j : Fin ℓ) :
    (TA t A).send (R.st (TA t A) (3 * k + 2) q) j =
      some (.run (A.send (R.id q) (R.st (TA t A) (3 * k + 2) q).a j)) := by
  rw [TA_send_run A (rnd2 A R k q), st_id]

/-! ### Admissible synchronous runs -/

variable {R}

/-- Identifiers of Byzantine processes. -/
def Fids (R : Run P ℓ V (TMsg S M V)) : Finset (Fin ℓ) := R.byz.image R.id

lemma notMem_byz_of_id {i : Fin ℓ} (hi : i ∉ Fids R) {q : P} (hq : R.id q = i) : q ∉ R.byz := by
  intro h; exact hi (Finset.mem_image.2 ⟨q, h, hq⟩)

variable (hR : R.Admissible t .sync .unrestricted)
include hR

/-- Membership in the inbox of a correct process. -/
lemma mem_inbox {r : ℕ} {q : P} (hq : q ∉ R.byz) {x : Fin ℓ × TMsg S M V} :
    x ∈ R.inbox (TA t A) r q ↔ (∃ q' ∉ R.byz, x.1 = R.id q' ∧
      (TA t A).send (R.st (TA t A) r q') (R.id q) = some x.2) ∨ x ∈ R.adv r q := by
  classical
  rw [Run.inbox_eq, Multiset.mem_add, Multiset.mem_sum]
  have hdrop : ∀ q', q' ∉ R.byz → ¬ R.drop r q' q :=
    fun q' hq' => hR.1.no_drop r q' q (by rw [hR.2.1 rfl]; omega) hq' hq
  constructor
  · rintro (⟨q', hq', hx⟩ | hx)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq'
      rw [Run.mem_msgFrom] at hx
      exact Or.inl ⟨q', hq'.1, hx.1, hx.2⟩
    · exact Or.inr hx
  · rintro (⟨q', hq', h1, h2⟩ | hx)
    · exact Or.inl ⟨q', by simp [hq', hdrop q' hq'], (Run.mem_msgFrom (TA t A) R).2 ⟨h1, h2⟩⟩
    · exact Or.inr hx

/-- Pairs tagged with the identifier of a correct group come from that group. -/
lemma mem_inbox_good {r : ℕ} {q : P} (hq : q ∉ R.byz) {j : Fin ℓ} (hj : j ∉ Fids R)
    {m : TMsg S M V} : (j, m) ∈ R.inbox (TA t A) r q ↔
      ∃ q', R.id q' = j ∧ (TA t A).send (R.st (TA t A) r q') (R.id q) = some m := by
  rw [mem_inbox A hR hq]
  constructor
  · rintro (⟨q', _, h1, h2⟩ | hx)
    · exact ⟨q', h1.symm, h2⟩
    · obtain ⟨b, hb, e⟩ := hR.1.adv_id r q _ hx
      exact absurd (Finset.mem_image.2 ⟨b, hb, e⟩) hj
  · rintro ⟨q', h1, h2⟩
    exact Or.inl ⟨q', notMem_byz_of_id hj h1, h1.symm, h2⟩

omit hR in
variable (t) in
/-- The states group `i` selects from in phase `k`. -/
def selSet (R : Run P ℓ V (TMsg S M V)) (i : Fin ℓ) (k : ℕ) : Set S :=
  {x | ∃ q', R.id q' = i ∧ x = (R.st (TA t A) (3 * k) q').a}

lemma selSet_eq {k : ℕ} {q : P} (hq : q ∉ R.byz) (hi : R.id q ∉ Fids R) :
    {x | (R.id q, TMsg.sel x) ∈ R.inbox (TA t A) (3 * k) q} = selSet t A R (R.id q) k := by
  ext x
  simp only [Set.mem_setOf_eq, selSet]
  rw [mem_inbox_good A hR hq hi]
  constructor
  · rintro ⟨q', h1, h2⟩; rw [send_sel] at h2; exact ⟨q', h1, by cases h2; rfl⟩
  · rintro ⟨q', h1, rfl⟩; exact ⟨q', h1, by rw [send_sel]⟩

lemma selSet_nonempty (i : Fin ℓ) (k : ℕ) : (selSet t A R i k).Nonempty := by
  obtain ⟨q, hq⟩ := hR.1.surj i
  exact ⟨_, q, hq, rfl⟩

/-- A representative of each identifier. -/
noncomputable def rep (i : Fin ℓ) : P := Classical.choose (hR.1.surj i)

lemma rep_id (i : Fin ℓ) : R.id (rep hR i) = i := Classical.choose_spec (hR.1.surj i)

/-- The selected state of group `i` in phase `k`. -/
noncomputable def σ (k : ℕ) (i : Fin ℓ) : S := (R.st (TA t A) (3 * k + 1) (rep hR i)).a

/-- The latched decision of group `i` in phase `k`. -/
noncomputable def Lat (k : ℕ) (i : Fin ℓ) : Option V := (R.st (TA t A) (3 * k + 1) (rep hR i)).lat

lemma sel_a_some {k : ℕ} {i : Fin ℓ} (hi : i ∉ Fids R) {q : P} (hq : R.id q = i) :
    (R.st (TA t A) (3 * k + 1) q).a = (selSet_nonempty A hR i k).some := by
  rw [sel_a, selSet_eq A hR (notMem_byz_of_id hi hq) (hq ▸ hi), hq,
    pick_of_nonempty (selSet_nonempty A hR i k)]

/-- Correct groups agree on their selected state. -/
lemma group_a {k : ℕ} {i : Fin ℓ} (hi : i ∉ Fids R) {q : P} (hq : R.id q = i) :
    (R.st (TA t A) (3 * k + 1) q).a = σ A hR k i :=
  (sel_a_some A hR hi hq).trans (sel_a_some A hR hi (rep_id hR i)).symm

lemma group_a' {k : ℕ} {i : Fin ℓ} (hi : i ∉ Fids R) {q : P} (hq : R.id q = i) :
    (R.st (TA t A) (3 * k + 2) q).a = σ A hR k i := by
  rw [dec_a]; exact group_a A hR hi hq

/-- Correct groups agree on their latched decision. -/
lemma group_lat (k : ℕ) {i : Fin ℓ} (hi : i ∉ Fids R) {q : P} (hq : R.id q = i) :
    (R.st (TA t A) (3 * k + 1) q).lat = Lat A hR k i := by
  have key : ∀ k, ∀ q q', R.id q = i → R.id q' = i →
      (R.st (TA t A) (3 * k + 1) q).lat = (R.st (TA t A) (3 * k + 1) q').lat := by
    intro k
    induction k with
    | zero =>
      intro q q' hq hq'
      rw [sel_lat, sel_lat, group_a A hR hi hq, group_a A hR hi hq', hq, hq']
      rfl
    | succ k ih =>
      intro q q' hq hq'
      rw [sel_lat, sel_lat, group_a A hR hi hq, group_a A hR hi hq', hq, hq',
        show 3 * (k + 1) = 3 * k + 3 by ring, run_lat, run_lat, dec_lat, dec_lat, ih q q' hq hq']
  exact key k q (rep hR i) hq (rep_id hR i)

lemma Lat_zero {i : Fin ℓ} (hi : i ∉ Fids R) : Lat A hR 0 i = A.decide i (σ A hR 0 i) := by
  unfold Lat
  rw [sel_lat, rep_id hR]
  rfl

lemma Lat_succ (k : ℕ) {i : Fin ℓ} (hi : i ∉ Fids R) :
    Lat A hR (k + 1) i = latch (Lat A hR k i) (A.decide i (σ A hR (k + 1) i)) := by
  unfold Lat
  rw [sel_lat, rep_id hR, show 3 * (k + 1) = 3 * k + 3 by ring, run_lat, dec_lat]
  rfl

/-- The latched decision is some decision of the selected states. -/
lemma Lat_spec {i : Fin ℓ} (hi : i ∉ Fids R) : ∀ k v, Lat A hR k i = some v →
    ∃ k' ≤ k, A.decide i (σ A hR k' i) = some v := by
  intro k
  induction k with
  | zero => intro v h; rw [Lat_zero A hR hi] at h; exact ⟨0, le_rfl, h⟩
  | succ k ih =>
    intro v h
    rw [Lat_succ A hR k hi] at h
    cases hL : Lat A hR k i with
    | some w =>
      rw [hL] at h; simp only [latch_some, Option.some.injEq] at h; subst h
      obtain ⟨k', hk', e⟩ := ih w hL; exact ⟨k', by omega, e⟩
    | none => rw [hL] at h; exact ⟨k + 1, le_rfl, h⟩

/-- Once some selected state decided, the latch is set. -/
lemma Lat_isSome {i : Fin ℓ} (hi : i ∉ Fids R) {k' : ℕ} {v : V}
    (h : A.decide i (σ A hR k' i) = some v) : ∀ k ≥ k', ∃ w, Lat A hR k i = some w := by
  intro k hk
  induction k with
  | zero =>
    obtain rfl : k' = 0 := by omega
    exact ⟨v, by rw [Lat_zero A hR hi, h]⟩
  | succ k ih =>
    rw [Lat_succ A hR k hi]
    rcases Nat.lt_or_ge k k' with hlt | hge
    · obtain rfl : k' = k + 1 := by omega
      cases Lat A hR k i with
      | some w => exact ⟨w, rfl⟩
      | none => exact ⟨v, h⟩
    · obtain ⟨w, hw⟩ := ih hge
      exact ⟨w, by rw [hw]; rfl⟩

/-- The unique message a correct group sends in a running round. -/
lemma filt_good {k : ℕ} {q : P} (hq : q ∉ R.byz) {j : Fin ℓ} (hj : j ∉ Fids R) :
    filt (R.inbox (TA t A) (3 * k + 2) q) j = A.send j (σ A hR k j) (R.id q) := by
  classical
  have hmem : ∀ m, (j, TMsg.run m) ∈ R.inbox (TA t A) (3 * k + 2) q ↔
      m = A.send j (σ A hR k j) (R.id q) := by
    intro m
    rw [mem_inbox_good A hR hq hj]
    constructor
    · rintro ⟨q', h1, h2⟩
      rw [send_run, group_a' A hR hj h1, h1] at h2
      cases h2; rfl
    · rintro rfl
      exact ⟨rep hR j, rep_id hR j, by rw [send_run, group_a' A hR hj (rep_id hR j), rep_id hR]⟩
  have hex : ∃ m, (j, TMsg.run m) ∈ R.inbox (TA t A) (3 * k + 2) q ∧
      ∀ m', (j, TMsg.run m') ∈ R.inbox (TA t A) (3 * k + 2) q → m' = m :=
    ⟨_, (hmem _).2 rfl, fun m' h => (hmem m').1 h⟩
  unfold filt
  rw [dif_pos hex]
  exact (hmem _).1 (Classical.choose_spec hex).1

/-! ### The simulated run -/

/-- The process of group `i` whose state is selected in phase `k + 1`. -/
noncomputable def qstar (k : ℕ) (i : Fin ℓ) : P :=
  @Classical.epsilon P ⟨rep hR i⟩ fun q =>
    R.id q = i ∧ (R.st (TA t A) (3 * k + 3) q).a = σ A hR (k + 1) i

lemma qstar_spec (k : ℕ) {i : Fin ℓ} (hi : i ∉ Fids R) :
    R.id (qstar A hR k i) = i ∧ (R.st (TA t A) (3 * k + 3) (qstar A hR k i)).a = σ A hR (k + 1) i := by
  have hex : ∃ q, R.id q = i ∧ (R.st (TA t A) (3 * k + 3) q).a = σ A hR (k + 1) i := by
    have hσ : σ A hR (k + 1) i = (selSet_nonempty A hR i (k + 1)).some :=
      sel_a_some A hR hi (rep_id hR i)
    obtain ⟨q', h1, h2⟩ := (selSet_nonempty A hR i (k + 1)).some_mem
    exact ⟨q', h1, by rw [hσ, h2, show 3 * (k + 1) = 3 * k + 3 by ring]⟩
  exact Classical.epsilon_spec hex

/-- The input of simulated process `i`: the input of a process of group `i` whose initial state
is selected. -/
noncomputable def inpS (i : Fin ℓ) : V :=
  R.inp (@Classical.epsilon P ⟨rep hR i⟩ fun q => R.id q = i ∧ A.init i (R.inp q) = σ A hR 0 i)

lemma inpS_spec {i : Fin ℓ} (hi : i ∉ Fids R) : ∃ q, R.id q = i ∧ R.inp q = inpS A hR i ∧
    A.init i (inpS A hR i) = σ A hR 0 i := by
  have hex : ∃ q, R.id q = i ∧ A.init i (R.inp q) = σ A hR 0 i := by
    have hσ : σ A hR 0 i = (selSet_nonempty A hR i 0).some := sel_a_some A hR hi (rep_id hR i)
    obtain ⟨q', h1, h2⟩ := (selSet_nonempty A hR i 0).some_mem
    refine ⟨q', h1, ?_⟩
    rw [hσ, h2]
    simp [TA, h1]
  have := Classical.epsilon_spec hex
  exact ⟨_, this.1, rfl, this.2⟩

/-- **The simulated run `α_S`** of the classical algorithm: identifier `i` is faulty iff its group
contains a Byzantine process; synchronous lock-step delivery. -/
noncomputable def simRun : CRun (Fin ℓ) M V where
  faulty := Fids R
  inp := inpS A hR
  gst := 0
  byz j k i := filt (R.inbox (TA t A) (3 * k + 2) (qstar A hR k i)) j
  dl _ τ _ := τ

lemma simRun_valid : (simRun A hR).Valid t 0 where
  card_faulty := by
    have h1 : (Fids R).card ≤ R.byz.card := Finset.card_image_le
    have h2 : R.byz.card ≤ t := hR.1.card_byz
    exact h1.trans h2
  dl_ge _ _ _ _ _ := le_rfl
  dl_le _ τ _ _ _ := by simp [simRun]

/-- **The simulation**: the selected states of the correct groups are the states of `α_S`. -/
theorem st_simRun : ∀ k, ∀ i ∉ Fids R, (simRun A hR).st A k i = σ A hR k i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    rw [Cslib.Byzantine.PartialSync.Run.st_zero]
    obtain ⟨_, _, _, h⟩ := inpS_spec A hR hi
    exact h
  | succ k ih =>
    intro i hi
    obtain ⟨hq1, hq2⟩ := qstar_spec A hR k hi
    rw [Cslib.Byzantine.PartialSync.Run.st_succ, ih i hi, ← hq2, run_a,
      group_a' A hR hi hq1, hq1]
    congr 1
    funext j
    rw [Cslib.Byzantine.PartialSync.Run.inbox_of_dl_eq A (fun _ _ _ => rfl)]
    by_cases hj : j ∈ Fids R
    · rw [Cslib.Byzantine.PartialSync.Run.out_of_faulty A _ hj]
      rfl
    · rw [Cslib.Byzantine.PartialSync.Run.out_of_correct A _ hj, ih j hj,
        filt_good A hR (notMem_byz_of_id hi hq1) hj, hq1]

/-! ### Decisions -/

omit hR in
lemma latch_eq_some {o d : Option V} {v : V} (h : latch o d = some v) : o = some v ∨ d = some v := by
  cases o with
  | some x => left; simpa using h
  | none => right; simpa using h

omit hR in
lemma st_zero_out (q : P) : (R.st (TA t A) 0 q).out = none := rfl

/-- A value latched by a correct group is decided in `α_S` by a correct process. -/
lemma decides_of_Lat {k : ℕ} {i : Fin ℓ} (hi : i ∉ Fids R) {v : V} (h : Lat A hR k i = some v) :
    (simRun A hR).Decides A i v := by
  obtain ⟨k', -, e⟩ := Lat_spec A hR hi k v h
  exact ⟨k', by rw [st_simRun A hR k' i hi]; exact e⟩

lemma card_Fids_le : (Fids R).card ≤ t := Finset.card_image_le.trans hR.1.card_byz

/-- What the deciding rule returns was latched by a correct group. -/
lemma decRule_good {k : ℕ} {q : P} (hq : q ∉ R.byz) {v : V}
    (h : decRule t (R.inbox (TA t A) (3 * k + 1) q) = some v) :
    ∃ i ∉ Fids R, Lat A hR k i = some v := by
  classical
  unfold decRule at h
  split_ifs at h with hex
  have hv := Classical.choose_spec hex
  rw [Option.some.injEq] at h
  rw [h] at hv
  obtain ⟨i, hi1, hi2⟩ : ∃ i ∈ univ.filter
      (fun j => (j, TMsg.dec (some v)) ∈ R.inbox (TA t A) (3 * k + 1) q), i ∉ Fids R := by
    by_contra hno
    push Not at hno
    have := Finset.card_le_card (show _ ⊆ Fids R from fun j hj => hno j hj)
    have := card_Fids_le hR
    omega
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1
  rw [mem_inbox_good A hR hq hi2] at hi1
  obtain ⟨q', h1, h2⟩ := hi1
  rw [send_dec] at h2
  simp only [Option.some.injEq, TMsg.dec.injEq] at h2
  exact ⟨i, hi2, by rw [← group_lat A hR k hi2 h1, h2]⟩

/-- Every decision of a correct process comes from the deciding rule. -/
lemma out_spec {q : P} : ∀ r v, (R.st (TA t A) r q).out = some v →
    ∃ k, decRule t (R.inbox (TA t A) (3 * k + 1) q) = some v := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro v h
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 ∧ r = 3 * k + j :=
      ⟨r / 3, r % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 3).symm⟩
    interval_cases j
    · cases k with
      | zero => rw [st_zero_out] at h; cases h
      | succ k =>
        rw [show 3 * (k + 1) + 0 = 3 * k + 3 by ring, run_out] at h
        exact ih (3 * k + 2) (by omega) v h
    · rw [sel_out] at h
      exact ih (3 * k) (by omega) v h
    · rw [dec_out] at h
      rcases latch_eq_some h with h' | h'
      · exact ih (3 * k + 1) (by omega) v h'
      · exact ⟨k, h'⟩

/-- A decision of a correct process of `T(A)` is a decision of a correct process of `α_S`. -/
lemma decides_good {q : P} (hq : q ∉ R.byz) {v : V} (h : R.Decides (TA t A) q v) :
    ∃ i ∉ Fids R, (simRun A hR).Decides A i v := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨k, hk⟩ := out_spec A hR r v hr
  obtain ⟨i, hi, hL⟩ := decRule_good A hR hq hk
  exact ⟨i, hi, decides_of_Lat A hR hi hL⟩

/-- **`T(A)` satisfies Byzantine agreement** in every admissible synchronous run, if `A` solves
classical synchronous Byzantine agreement among `ℓ > 3t` processes. -/
theorem TA_BA (hℓ : 3 * t < ℓ) (hA : Cslib.Byzantine.PartialSync.SolvesConsensusSync t 0 A
    (baValidity (Fin ℓ) V)) : R.BA (TA t A) := by
  classical
  have hv := simRun_valid A hR
  have hauth := Cslib.Byzantine.PartialSync.Run.authValid_none A (simRun A hR)
  refine ⟨?_, ?_, ?_⟩
  · -- termination
    intro p hp
    have hterm : ∀ i, i ∉ Fids R → ∃ τ, ∃ v, A.decide i ((simRun A hR).st A τ i) = some v := by
      intro i hi
      obtain ⟨v, τ, h⟩ := hA.termination _ hv hauth rfl i hi
      exact ⟨τ, v, h⟩
    choose! tau val htau using hterm
    set K := (univ.filter (· ∉ Fids R)).sup tau
    obtain ⟨i₀, hi₀⟩ : ∃ i, i ∉ Fids R := by
      by_contra h
      push Not at h
      have h1 := Finset.card_le_card (show (univ : Finset (Fin ℓ)) ⊆ Fids R from fun i _ => h i)
      have := card_Fids_le hR
      simp at h1
      omega
    have hlat : ∀ i, i ∉ Fids R → ∃ w, Lat A hR K i = some w := fun i hi =>
      Lat_isSome A hR hi (by rw [← st_simRun A hR _ i hi]; exact htau i hi) K
        (Finset.le_sup (f := tau) (by simpa using hi))
    obtain ⟨u, hu⟩ := hlat i₀ hi₀
    have hall : ∀ i, i ∉ Fids R → Lat A hR K i = some u := by
      intro i hi
      obtain ⟨w, hw⟩ := hlat i hi
      rw [hw, hA.agreement _ hv hauth rfl i hi i₀ hi₀ w u (decides_of_Lat A hR hi hw)
        (decides_of_Lat A hR hi₀ hu)]
    have hcount : t + 1 ≤ (univ.filter fun j =>
        (j, TMsg.dec (some u)) ∈ R.inbox (TA t A) (3 * K + 1) p).card := by
      have hsub : univ.filter (· ∉ Fids R) ⊆ univ.filter fun j =>
          (j, TMsg.dec (some u)) ∈ R.inbox (TA t A) (3 * K + 1) p := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        rw [mem_inbox_good A hR hp hj]
        exact ⟨rep hR j, rep_id hR j, by rw [send_dec, group_lat A hR K hj (rep_id hR j), hall j hj]⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin ℓ)))
        (fun j => j ∈ Fids R)
      have h3 : univ.filter (fun j => j ∈ Fids R) = Fids R := by ext; simp
      rw [h3] at h2
      have := card_Fids_le hR
      simp only [Finset.card_univ, Fintype.card_fin] at h2
      omega
    have hd : ∃ w, decRule t (R.inbox (TA t A) (3 * K + 1) p) = some w := by
      unfold decRule; rw [dif_pos ⟨u, hcount⟩]; exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hd
    cases ho : (R.st (TA t A) (3 * K + 1) p).out with
    | some x => exact ⟨x, 3 * K + 1, ho⟩
    | none => exact ⟨w, 3 * K + 2, by
        show (R.st (TA t A) (3 * K + 2) p).out = some w
        rw [dec_out, ho, hw]; rfl⟩
  · -- agreement
    intro p hp q hq v w hpv hqw
    obtain ⟨i, hi, hiv⟩ := decides_good A hR hp hpv
    obtain ⟨j, hj, hjw⟩ := decides_good A hR hq hqw
    exact hA.agreement _ hv hauth rfl i hi j hj v w hiv hjw
  · -- validity
    intro v hall p hp w hpw
    obtain ⟨i, hi, hiw⟩ := decides_good A hR hp hpw
    have hval := hA.validity _ hv hauth rfl i hi w hiw
    apply hval v
    intro j hj
    simp only [Cslib.Byzantine.PartialSync.Run.inputConf] at hj ⊢
    split_ifs at hj ⊢ with hjF
    · exact absurd rfl hj
    · obtain ⟨q', h1, h2, -⟩ := inpS_spec A hR hjF
      show some (inpS A hR j) = some v
      rw [← h2, hall q' (notMem_byz_of_id hjF h1)]

end Sim

open Sim

/-- `T(A)` solves synchronous Byzantine agreement (unrestricted Byzantine processes) for any `n`. -/
theorem TA_solves {ℓ t : ℕ} {M S V : Type} (A : CAlg (Fin ℓ) M S V V) (hℓ : 3 * t < ℓ)
    (hA : Cslib.Byzantine.PartialSync.SolvesConsensusSync t 0 A (baValidity (Fin ℓ) V)) (n : ℕ) :
    Solves .sync .unrestricted n t (TA t A) :=
  fun _ _ _ _ _ hR => TA_BA A hR hℓ hA

/-- **Proposition 2.** Synchronous Byzantine agreement is solvable even with innumerate processes
if `ℓ > 3t` (any `n`; nonempty value set). -/
theorem prop2 {n ℓ t : ℕ} (hℓ : 3 * t < ℓ) (V : Type) [Nonempty V] :
    Solvable .sync .unrestricted .innumerate n ℓ t V := by
  obtain ⟨M, S, A, hA⟩ := classicalBA_exists (P := Fin ℓ) (V := V) (t := t) (by simpa using hℓ)
  exact ⟨_, _, TA t A, TA_innumerate t A, TA_solves A hℓ hA n⟩

end Podc.HomonymsBA
