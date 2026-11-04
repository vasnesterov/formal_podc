import Papers.PODC2018.PPNaming.Sink
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Theorem 11: no `P`-state symmetric naming of non-initialized agents under weak fairness

Setting of Section 3.1: a symmetric leader protocol `Name`, `P` states per mobile agent,
initialized leader, arbitrarily initialized mobile agents, weak fairness. By Lemma 2 and
Proposition 6 the mobile-mobile rules are null except between homonyms, and homonyms reduce to the
sink `m`.

We work in a population of `P` mobile agents with *reduced* configurations (`Red`: no homonyms
except in `m`) and *reduced steps* (`rstep`: the leader meets an agent, and a homonym pair it
creates is immediately reduced to `(m, m)`).

**Proof (repaired).** Fix `s ≠ m`. Two worlds with the same leader state are related (`Rel`) if
the *plus* world has exactly one `s`-agent where the *minus* world has an extra `m`-agent
(multisets: `plus + {m} = minus + {s}`, no `s` in minus). Every reduced step of the minus world
can be mirrored in the plus world (`mirror`): the relation is kept, with roles exchanged exactly
when the minus world creates an `s`-agent (then the plus world gets a second `s`-agent and
reduces it). By weak fairness every reachable reduced configuration reaches a named one by
reduced steps (`exists_rreach_injective`); in particular a minus world eventually creates `s`
(`drive`). Our adversary always lets the *minus* world drive: the actual execution makes the
interaction required by weak fairness when it is the minus world, and otherwise follows the
other world until it creates `s`, after which it is the minus world again. Hence the actual
execution is weakly fair and has two `m`-agents infinitely often — it never names the agents.

The paper's proof instead fixes one execution `e` from `C₁⁻ˢ` and claims (Theorem 11, "e is
chosen such that ... a particular s-state agent y_i does not interact") that the plus phases of
`e` can avoid the `s`-agent; this step is not justified (it fails for Protocol 1 under global
fairness, where the leader must meet the `s`-agent). The argument above replaces it.
-/

namespace Podc.PPNaming

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Function

variable {L Q N : Type*} [Fintype Q] [DecidableEq Q] {A : Type*} [Fintype A] [DecidableEq A]

/-! ### Counting states -/

/-- Number of agents in state `q`. -/
def cnt (c : A → Q) (q : Q) : ℕ := (Finset.univ.filter (fun a => c a = q)).card

lemma cnt_update (c : A → Q) (a : A) (v q : Q) :
    cnt (update c a v) q + (if q = c a then 1 else 0) = cnt c q + (if q = v then 1 else 0) := by
  unfold cnt
  have e1 := Finset.add_sum_erase Finset.univ (fun x => if update c a v x = q then 1 else 0)
    (Finset.mem_univ a)
  have e2 := Finset.add_sum_erase Finset.univ (fun x => if c x = q then 1 else 0)
    (Finset.mem_univ a)
  rw [Finset.card_filter, Finset.card_filter, ← e1, ← e2]
  have : ∑ x ∈ Finset.univ.erase a, (if update c a v x = q then 1 else 0) =
      ∑ x ∈ Finset.univ.erase a, (if c x = q then 1 else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, update_self]
  simp only [eq_comm (a := q)]
  split_ifs <;> omega

lemma cnt_pos_iff (c : A → Q) (q : Q) : 0 < cnt c q ↔ ∃ a, c a = q := by
  unfold cnt; rw [Finset.card_pos]; simp [Finset.Nonempty]

lemma exists_other_iff (c : A → Q) (a : A) (v : Q) :
    (∃ b, b ≠ a ∧ c b = v) ↔ (if c a = v then 1 else 0) < cnt c v := by
  unfold cnt
  by_cases h : c a = v
  · rw [if_pos h, ← Finset.card_erase_add_one (by simpa using h : a ∈ _)]
    simp only [Nat.lt_add_left_iff_pos, Finset.card_pos, Finset.Nonempty, Finset.mem_erase,
      Finset.mem_filter, Finset.mem_univ, true_and]
  · rw [if_neg h, Finset.card_pos]
    simp only [Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨b, -, hb⟩; exact ⟨b, hb⟩
    · rintro ⟨b, hb⟩; exact ⟨b, fun h' => h (h' ▸ hb), hb⟩

lemma sum_cnt (c : A → Q) : ∑ q, cnt c q = Fintype.card A := by
  unfold cnt
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := c) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]

lemma two_le_cnt {c : A → Q} {a b : A} (hab : a ≠ b) (he : c a = c b) : 2 ≤ cnt c (c a) := by
  unfold cnt
  have hsub : ({a, b} : Finset A) ⊆ Finset.univ.filter (fun x => c x = c a) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with rfl | rfl
    · exact ⟨Finset.mem_univ _, rfl⟩
    · exact ⟨Finset.mem_univ _, he.symm⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at hle
  exact hle

/-! ### Reduced configurations and the relation between the two worlds -/

/-- Reduced: no homonyms except in the sink `m`. -/
def Red (m : Q) (c : A → Q) : Prop := ∀ q, q ≠ m → cnt c q ≤ 1

/-- `cp` (plus world) and `cm` (minus world) differ by one agent in state `s` versus `m`:
as multisets `cp + {m} = cm + {s}`, and there is no `s`-agent in `cm`. -/
def Rel (m s : Q) (cp cm : A → Q) : Prop :=
  cnt cm s = 0 ∧ ∀ q, cnt cp q + (if q = m then 1 else 0) = cnt cm q + (if q = s then 1 else 0)

lemma cnt_sink_pos (hA : Fintype.card A = Fintype.card Q) {m : Q} {c : A → Q} (hc : Red m c) :
    1 ≤ cnt c m := by
  by_contra h0
  have hsum := sum_cnt c
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at hsum
  have hle : ∑ q ∈ Finset.univ.erase m, cnt c q ≤ ∑ _q ∈ Finset.univ.erase m, 1 :=
    Finset.sum_le_sum fun q hq => hc q (Finset.ne_of_mem_erase hq)
  rw [← Finset.card_eq_sum_ones, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ] at hle
  have : 0 < Fintype.card Q := Fintype.card_pos_iff.2 ⟨m⟩
  omega

lemma Rel.two_le_cnt (hA : Fintype.card A = Fintype.card Q) {m s : Q} (hsm : s ≠ m)
    {cp cm : A → Q} (h : Rel m s cp cm) (hp : Red m cp) : 2 ≤ cnt cm m := by
  have h1 := h.2 m
  have h2 := cnt_sink_pos hA hp
  rw [if_pos rfl, if_neg (Ne.symm hsm)] at h1
  omega

lemma not_injective_of_two_le_cnt {name : Q → N} {l : L} {c : A → Q} {q : Q}
    (h : 2 ≤ cnt c q) : ¬ Injective (leaderNames name (ofLM l c)) := by
  intro hi
  unfold cnt at h
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.1 (show 1 < (Finset.univ.filter (fun a => c a = q)).card by omega)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hab (hi (by simp [ha, hb]))

/-! ### Reduced steps -/

variable (LP : LeaderProtocol L Q)

/-- The reduced step: the leader (in state `l`) meets agent `a`; if this creates a pair of
homonyms outside the sink `m`, they are reduced to `(m, m)`. -/
noncomputable def rstep (m : Q) (l : L) (c : A → Q) (a : A) : L × (A → Q) :=
  if h : (LP.lm l (c a)).2 ≠ m ∧ ∃ b, b ≠ a ∧ c b = (LP.lm l (c a)).2 then
    ((LP.lm l (c a)).1, update (update c a m) h.2.choose m)
  else ((LP.lm l (c a)).1, update c a (LP.lm l (c a)).2)

variable {LP}

@[simp] lemma rstep_fst (m : Q) (l : L) (c : A → Q) (a : A) :
    (rstep LP m l c a).1 = (LP.lm l (c a)).1 := by
  unfold rstep; split_ifs <;> rfl

lemma rstep_cnt_nocol {m : Q} {l : L} {c : A → Q} {a : A}
    (h : ¬ ((LP.lm l (c a)).2 ≠ m ∧ ∃ b, b ≠ a ∧ c b = (LP.lm l (c a)).2)) (q : Q) :
    cnt (rstep LP m l c a).2 q + (if q = c a then 1 else 0) =
      cnt c q + (if q = (LP.lm l (c a)).2 then 1 else 0) := by
  unfold rstep; rw [dif_neg h]; exact cnt_update _ _ _ _

lemma rstep_cnt_col {m : Q} {l : L} {c : A → Q} {a : A}
    (h : (LP.lm l (c a)).2 ≠ m ∧ ∃ b, b ≠ a ∧ c b = (LP.lm l (c a)).2) (q : Q) :
    cnt (rstep LP m l c a).2 q + (if q = c a then 1 else 0) +
        (if q = (LP.lm l (c a)).2 then 1 else 0) =
      cnt c q + (if q = m then 1 else 0) + (if q = m then 1 else 0) := by
  unfold rstep; rw [dif_pos h]; dsimp only
  have hb := h.2.choose_spec
  have h1 := cnt_update (update c a m) h.2.choose m q
  have h2 := cnt_update c a m q
  rw [update_of_ne hb.1, hb.2] at h1
  omega

lemma rstep_red {m : Q} {c : A → Q} (hc : Red m c) (l : L) (a : A) :
    Red m (rstep LP m l c a).2 := by
  intro q hq
  have hcq := hc q hq
  by_cases hcol : (LP.lm l (c a)).2 ≠ m ∧ ∃ b, b ≠ a ∧ c b = (LP.lm l (c a)).2
  · have h := rstep_cnt_col (LP := LP) hcol q
    rw [if_neg hq] at h; omega
  · have h := rstep_cnt_nocol (LP := LP) hcol q
    by_cases hv : q = (LP.lm l (c a)).2
    · have hno : ¬ ∃ b, b ≠ a ∧ c b = (LP.lm l (c a)).2 := fun hex => hcol ⟨hv ▸ hq, hex⟩
      rw [exists_other_iff, not_lt] at hno
      rw [if_pos hv] at h
      subst hv
      by_cases hu : c a = (LP.lm l (c a)).2
      · rw [if_pos hu] at hno; rw [if_pos hu.symm] at h; omega
      · rw [if_neg hu] at hno; rw [if_neg (Ne.symm hu)] at h; omega
    · rw [if_neg hv] at h; omega

/-- In a reduced configuration, interactions of two mobile agents are null. -/
lemma mmUpd_red {m : Q} (hnull : ∀ p q, p ≠ q → LP.mm p q = (p, q))
    (hdiag : ∀ s, (LP.mm s s).2 = (LP.mm s s).1) (hm : LP.hom m = m) {c : A → Q} (hc : Red m c)
    {a b : A} (hab : a ≠ b) : LP.mmUpd c a b = c := by
  unfold LeaderProtocol.mmUpd
  by_cases he : c a = c b
  · have hcm : c a = m := by
      by_contra h; have := hc _ h; have := two_le_cnt hab he; omega
    have hbm : c b = m := he ▸ hcm
    have h1 : (LP.mm m m).1 = m := hm
    have h2 : (LP.mm m m).2 = m := by rw [hdiag]; exact hm
    rw [hcm, hbm, h1, h2]
    funext x
    by_cases hxb : x = b
    · subst hxb; simp [hbm]
    · by_cases hxa : x = a
      · subst hxa; simp [hxb, hcm]
      · simp [hxa, hxb]
  · rw [hnull _ _ he, update_eq_self, update_eq_self]

lemma rstep_reach (hdiag : ∀ s, (LP.mm s s).2 = (LP.mm s s).1) {m : Q}
    (hsink : ∀ s, ∃ k, LP.hom^[k] s = m) (l : L) (c : A → Q) (a : A) :
    LP.toProtocol.Reachable (LP.toProtocol.interact (ofLM l c) none (some a))
      (ofLM (rstep LP m l c a).1 (rstep LP m l c a).2) := by
  rw [interact_leader_mobile]
  unfold rstep
  split_ifs with hcol
  · obtain ⟨hvm, hex⟩ := hcol
    have hb := hex.choose_spec
    obtain ⟨k, hk⟩ := hsink (LP.lm l (c a)).2
    have := homonym_reach hdiag (LP.lm l (c a)).1 (update c a (LP.lm l (c a)).2) hb.1.symm
      (by rw [update_self, update_of_ne hb.1, hb.2]) k
    rw [update_self, hk] at this
    convert this using 3
    funext x
    by_cases hx : x = a
    · subst hx; simp [hb.1.symm]
    · simp [update, hx]
  · exact .refl

/-- One reduced step (the leader meets some agent). -/
def RS (m : Q) (x y : L × (A → Q)) : Prop := ∃ a, y = rstep LP m x.1 x.2 a

/-- Reachability by reduced steps. -/
abbrev RReach (m : Q) : L × (A → Q) → L × (A → Q) → Prop := Relation.ReflTransGen (RS (LP := LP) m)

lemma RReach.reachable (hdiag : ∀ s, (LP.mm s s).2 = (LP.mm s s).1) {m : Q}
    (hsink : ∀ s, ∃ k, LP.hom^[k] s = m) {x y : L × (A → Q)} (h : RReach (LP := LP) m x y) :
    LP.toProtocol.Reachable (ofLM x.1 x.2) (ofLM y.1 y.2) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨a, rfl⟩ := hst
    exact (ih.tail ⟨none, some a, by simp, rfl⟩).trans (rstep_reach hdiag hsink _ _ a)

lemma RReach.red {m : Q} {x y : L × (A → Q)} (h : RReach (LP := LP) m x y) (hx : Red m x.2) :
    Red m y.2 := by
  induction h with
  | refl => exact hx
  | tail _ hst ih => obtain ⟨a, rfl⟩ := hst; exact rstep_red ih _ _

/-! ### The mirror lemma -/

/-- **Mirroring a reduced step of the minus world in the plus world.** -/
lemma mirror (hA : Fintype.card A = Fintype.card Q) {m s : Q} (hsm : s ≠ m) {cp cm : A → Q}
    (hrp : Red m cp) (hrel : Rel m s cp cm) (l : L) (a : A) :
    ∃ a', (rstep LP m l cp a').1 = (rstep LP m l cm a).1 ∧
      (cnt (rstep LP m l cm a).2 s = 0 → Rel m s (rstep LP m l cp a').2 (rstep LP m l cm a).2) ∧
      (cnt (rstep LP m l cm a).2 s ≠ 0 →
        Rel m s (rstep LP m l cm a).2 (rstep LP m l cp a').2) := by
  obtain ⟨hrel1, hrelq⟩ := hrel
  have hus : cm a ≠ s := fun h => by have := (cnt_pos_iff cm s).2 ⟨a, h⟩; omega
  -- an agent of the plus world in the state of `a`
  obtain ⟨a', ha'⟩ : ∃ a', cp a' = cm a := by
    rw [← cnt_pos_iff]
    by_cases hum : cm a = m
    · rw [hum]; exact cnt_sink_pos hA hrp
    · have h1 := hrelq (cm a)
      have h2 : 0 < cnt cm (cm a) := (cnt_pos_iff cm _).2 ⟨a, rfl⟩
      rw [if_neg hum, if_neg hus] at h1; omega
  refine ⟨a', by simp [ha'], ?_⟩
  have hlp : LP.lm l (cp a') = LP.lm l (cm a) := by rw [ha']
  by_cases hvs : (LP.lm l (cm a)).2 = s
  · -- the minus world creates `s`: roles are exchanged
    have hnm : ¬ ((LP.lm l (cm a)).2 ≠ m ∧ ∃ b, b ≠ a ∧ cm b = (LP.lm l (cm a)).2) := by
      rintro ⟨-, b, -, hb⟩; have := (cnt_pos_iff cm s).2 ⟨b, hb.trans hvs⟩; omega
    have hpc : (LP.lm l (cp a')).2 ≠ m ∧ ∃ b, b ≠ a' ∧ cp b = (LP.lm l (cp a')).2 := by
      rw [hlp, hvs]
      refine ⟨hsm, ?_⟩
      rw [exists_other_iff, ha', if_neg hus]
      have := hrelq s; rw [if_neg hsm, if_pos rfl, hrel1] at this; omega
    have hm' := rstep_cnt_nocol (LP := LP) hnm
    have hp' := rstep_cnt_col (LP := LP) hpc
    simp only [ha', hvs] at hm' hp'
    have hds : cnt (rstep LP m l cm a).2 s ≠ 0 := by
      have := hm' s; rw [if_neg (Ne.symm hus), if_pos rfl] at this; omega
    refine ⟨fun h => absurd h hds, fun _ => ⟨?_, fun q => ?_⟩⟩
    · have h1 := hp' s; have h2 := hrelq s
      rw [if_neg (Ne.symm hus), if_pos rfl, if_neg hsm] at h1
      rw [if_neg hsm, if_pos rfl, hrel1] at h2
      omega
    · have h1 := hp' q; have h2 := hm' q; have h3 := hrelq q
      omega
  · have hiff : ((LP.lm l (cm a)).2 ≠ m ∧ ∃ b, b ≠ a ∧ cm b = (LP.lm l (cm a)).2) ↔
        ((LP.lm l (cp a')).2 ≠ m ∧ ∃ b, b ≠ a' ∧ cp b = (LP.lm l (cp a')).2) := by
      rw [hlp, exists_other_iff, exists_other_iff, ha']
      by_cases hvm : (LP.lm l (cm a)).2 = m
      · simp [hvm]
      · have := hrelq (LP.lm l (cm a)).2
        rw [if_neg hvm, if_neg hvs] at this
        simp only [add_zero] at this
        rw [this]
    have hds : cnt (rstep LP m l cm a).2 s = 0 := by
      by_cases hc : (LP.lm l (cm a)).2 ≠ m ∧ ∃ b, b ≠ a ∧ cm b = (LP.lm l (cm a)).2
      · have := rstep_cnt_col (LP := LP) hc s
        rw [if_neg (Ne.symm hus), if_neg (Ne.symm hvs), if_neg hsm, hrel1] at this; omega
      · have := rstep_cnt_nocol (LP := LP) hc s
        rw [if_neg (Ne.symm hus), if_neg (Ne.symm hvs), hrel1] at this; omega
    refine ⟨fun _ => ⟨hds, fun q => ?_⟩, fun h => absurd hds h⟩
    have h3 := hrelq q
    by_cases hc : (LP.lm l (cm a)).2 ≠ m ∧ ∃ b, b ≠ a ∧ cm b = (LP.lm l (cm a)).2
    · have h1 := rstep_cnt_col (LP := LP) (hiff.1 hc) q
      have h2 := rstep_cnt_col (LP := LP) hc q
      rw [ha'] at h1
      omega
    · have h1 := rstep_cnt_nocol (LP := LP) (fun h => hc (hiff.2 h)) q
      have h2 := rstep_cnt_nocol (LP := LP) hc q
      rw [ha'] at h1
      omega

/-! ### Driving the minus world until it creates `s` -/

/-- If the minus world `x` (driver) reaches by reduced steps a configuration with an `s`-agent,
then, mirroring, driver and follower reach configurations where the follower is the minus world
again. -/
lemma drive (hA : Fintype.card A = Fintype.card Q) {m s : Q} (hsm : s ≠ m)
    {x z : L × (A → Q)} (h : RReach (LP := LP) m x z) (hz : cnt z.2 s ≠ 0) :
    ∀ cF, Red m cF → Red m x.2 → Rel m s cF x.2 →
      ∃ l₃ gD gF, RReach (LP := LP) m x (l₃, gD) ∧ RReach (LP := LP) m (x.1, cF) (l₃, gF) ∧
        Rel m s gD gF ∧ Red m gD ∧ Red m gF := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro cF _ _ hrel; exact absurd hrel.1 hz
  | @head x y hxy hyz ih =>
    intro cF hF hD hrel
    obtain ⟨a, rfl⟩ := hxy
    obtain ⟨a', hl, h0, h1⟩ := mirror (LP := LP) hA hsm hF hrel x.1 a
    have hstepD : RReach (LP := LP) m x (rstep LP m x.1 x.2 a) := .single ⟨a, rfl⟩
    have hstepF : RReach (LP := LP) m (x.1, cF)
        ((rstep LP m x.1 x.2 a).1, (rstep LP m x.1 cF a').2) := by
      refine .single ⟨a', ?_⟩
      rw [← hl]
    by_cases hs : cnt (rstep LP m x.1 x.2 a).2 s = 0
    · obtain ⟨l₃, gD, gF, h₁, h₂, h₃, h₄, h₅⟩ := ih _ (rstep_red hF _ _) (rstep_red hD _ _) (h0 hs)
      exact ⟨l₃, gD, gF, hstepD.trans h₁, hstepF.trans h₂, h₃, h₄, h₅⟩
    · exact ⟨_, _, _, hstepD, hstepF, h1 hs, rstep_red hD _ _, rstep_red hF _ _⟩

/-! ### Theorem 11 -/

section Main

variable {name : Q → N} {l₀ : L} {m : Q}

/-- Configurations reachable from an initial configuration (initialized leader). -/
def RI (LP : LeaderProtocol L Q) (l₀ : L) (X : Config (Option A) (L ⊕ Q)) : Prop :=
  ∃ c₀ : A → Q, LP.toProtocol.Reachable (ofLM l₀ c₀) X

/-- **Weak fairness ⇒ reduced reachability of naming.** From every reachable reduced
configuration, a configuration with pairwise distinct states is reachable by reduced steps. -/
theorem exists_rreach_injective (hs : LP.Symmetric) (hnull : ∀ p q, p ≠ q → LP.mm p q = (p, q))
    (hm : LP.hom m = m) (hsink : ∀ s, ∃ k, LP.hom^[k] s = m) [Nonempty A]
    (hP : SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option A) (L ⊕ Q)))
      (leaderNames name))
    {l : L} {c : A → Q} (hred : Red m c) (hreach : RI LP l₀ (ofLM l c)) :
    ∃ y, RReach (LP := LP) m (l, c) y ∧ Injective y.2 := by
  have hdiag : ∀ s, (LP.mm s s).2 = (LP.mm s s).1 := fun s => by
    have := congrArg Prod.fst (hs.1 s s); simpa using this.symm
  by_contra hno
  push_neg at hno
  let G : Config (Option A) (L ⊕ Q) → Prop := fun Y =>
    ∃ y, RReach (LP := LP) m (l, c) y ∧ Y = ofLM y.1 y.2
  have hnotinj : ∀ y, RReach (LP := LP) m (l, c) y →
      ¬ Injective (leaderNames name (ofLM y.1 y.2)) := by
    intro y hy hi
    exact hno y hy (fun a b h => (leaderNames_ofLM_injective_iff name y.1 y.2).1 hi (by simp [h]))
  have hleader : ∀ y, RReach (LP := LP) m (l, c) y → ∀ a, ∃ Y₂,
      LP.toProtocol.Reachable (LP.toProtocol.interact (ofLM y.1 y.2) none (some a)) Y₂ ∧ G Y₂ :=
    fun y hy a => ⟨_, rstep_reach hdiag hsink y.1 y.2 a, _, hy.tail ⟨a, rfl⟩, rfl⟩
  have hph : ∀ Y, G Y → ∀ u v, u ≠ v → ∃ Y₁ Y₂, LP.toProtocol.Reachable Y Y₁ ∧
      LP.toProtocol.Reachable (LP.toProtocol.interact Y₁ u v) Y₂ ∧ G Y₂ ∧
      ¬ Injective (leaderNames name Y) := by
    rintro Y ⟨y, hy, rfl⟩ u v huv
    suffices H : ∃ Y₂, LP.toProtocol.Reachable (LP.toProtocol.interact (ofLM y.1 y.2) u v) Y₂ ∧
        G Y₂ ∧ ¬ Injective (leaderNames name (ofLM y.1 y.2)) by
      obtain ⟨Y₂, h1, h2, h3⟩ := H
      exact ⟨_, Y₂, Relation.ReflTransGen.refl, h1, h2, h3⟩
    rcases u with _ | a <;> rcases v with _ | b
    · exact absurd rfl huv
    · obtain ⟨Y₂, h1, h2⟩ := hleader y hy b; exact ⟨Y₂, h1, h2, hnotinj y hy⟩
    · rw [← hs.isSymmetric.interact_comm _ huv]
      obtain ⟨Y₂, h1, h2⟩ := hleader y hy a; exact ⟨Y₂, h1, h2, hnotinj y hy⟩
    · have hab : a ≠ b := fun h => huv (by rw [h])
      refine ⟨_, ?_, ⟨y, hy, rfl⟩, hnotinj y hy⟩
      rw [interact_mobile_mobile LP _ _ hab, mmUpd_red hnull hdiag hm (hy.red hred) hab]
      exact Relation.ReflTransGen.refl
  obtain ⟨c₀, hc₀⟩ := hreach
  obtain ⟨a₀⟩ := ‹Nonempty A›
  exact hP.false_of_phases G hph ⟨c₀, rfl⟩ hc₀
    (show G (ofLM l c) from ⟨(l, c), Relation.ReflTransGen.refl, rfl⟩)
    (show (none : Option A) ≠ some a₀ by simp)

/-- **Theorem 11 (core).** In a population of `P` mobile agents (`card A = card Q = P ≥ 2`), a
symmetric protocol whose mobile-mobile rules are null except between homonyms, with a sink `m`
attracting all homonym pairs, does not solve naming under weak fairness with an initialized
leader and arbitrarily initialized mobile agents. -/
theorem thm11_core (hA : Fintype.card A = Fintype.card Q) (h2 : 2 ≤ Fintype.card Q)
    (hs : LP.Symmetric) (hnull : ∀ p q, p ≠ q → LP.mm p q = (p, q)) (hm : LP.hom m = m)
    (hsink : ∀ s, ∃ k, LP.hom^[k] s = m)
    (hP : SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option A) (L ⊕ Q)))
      (leaderNames name)) : False := by
  have hdiag : ∀ s, (LP.mm s s).2 = (LP.mm s s).1 := fun s => by
    have := congrArg Prod.fst (hs.1 s s); simpa using this.symm
  haveI : Nonempty A := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨s, hsm⟩ := Fintype.exists_ne_of_one_lt_card (lt_of_lt_of_le one_lt_two h2) m
  -- the two initial worlds
  let e : A ≃ Q := Fintype.equivOfCardEq hA
  have hcnte : ∀ q, cnt e q = 1 := by
    intro q; unfold cnt
    rw [Finset.card_eq_one]; refine ⟨e.symm q, ?_⟩
    ext x; simp [Equiv.apply_eq_iff_eq_symm_apply]
  let cp₀ : A → Q := e
  let cm₀ : A → Q := update e (e.symm s) m
  have hcm₀ : ∀ q, cnt cm₀ q + (if q = s then 1 else 0) = 1 + (if q = m then 1 else 0) := by
    intro q; have := cnt_update e (e.symm s) m q
    simp only [Equiv.apply_symm_apply, hcnte] at this; exact this
  have hrel₀ : Rel m s cp₀ cm₀ := by
    refine ⟨?_, fun q => ?_⟩
    · have := hcm₀ s; rw [if_pos rfl, if_neg hsm] at this; omega
    · have := hcm₀ q; have := hcnte q
      show cnt e q + _ = _
      omega
  have hrp₀ : Red m cp₀ := fun q _ => (hcnte q).le
  have hrm₀ : Red m cm₀ := fun q hq => by
    have := hcm₀ q; rw [if_neg hq] at this; omega
  -- the invariant: the actual world is a minus world with a reachable plus partner
  let G : Config (Option A) (L ⊕ Q) → Prop := fun Y => ∃ l cp cm, Y = ofLM l cm ∧ Red m cp ∧
    Red m cm ∧ Rel m s cp cm ∧ RI LP l₀ (ofLM l cp) ∧ RI LP l₀ (ofLM l cm)
  have hnotinj : ∀ Y, G Y → ¬ Injective (leaderNames name Y) := by
    rintro Y ⟨l, cp, cm, rfl, hrp, -, hrel, -⟩
    exact not_injective_of_two_le_cnt (hrel.two_le_cnt hA hsm hrp)
  have hRIstep : ∀ (l : L) (c : A → Q) (a : A), RI LP l₀ (ofLM l c) →
      RI LP l₀ (ofLM (rstep LP m l c a).1 (rstep LP m l c a).2) := by
    rintro l c a ⟨c₀, h⟩
    exact ⟨c₀, (h.tail ⟨none, some a, by simp, rfl⟩).trans (rstep_reach hdiag hsink l c a)⟩
  have hRIrr : ∀ x y : L × (A → Q), RReach (LP := LP) m x y → RI LP l₀ (ofLM x.1 x.2) →
      RI LP l₀ (ofLM y.1 y.2) := by
    rintro x y hxy ⟨c₀, h⟩
    exact ⟨c₀, h.trans (hxy.reachable hdiag hsink)⟩
  have hleader : ∀ Y, G Y → ∀ a, ∃ Y₂,
      LP.toProtocol.Reachable (LP.toProtocol.interact Y none (some a)) Y₂ ∧ G Y₂ := by
    rintro Y ⟨l, cp, cm, rfl, hrp, hrm, hrel, hRp, hRm⟩ a
    obtain ⟨a', hl, h0, h1⟩ := mirror (LP := LP) hA hsm hrp hrel l a
    set dm := (rstep LP m l cm a).2
    set dp := (rstep LP m l cp a').2
    set l' := (rstep LP m l cm a).1
    have hstep : LP.toProtocol.Reachable (LP.toProtocol.interact (ofLM l cm) none (some a))
        (ofLM l' dm) := rstep_reach hdiag hsink l cm a
    have hRdm : RI LP l₀ (ofLM l' dm) := hRIstep l cm a hRm
    have hRdp : RI LP l₀ (ofLM l' dp) := by rw [← hl]; exact hRIstep l cp a' hRp
    by_cases hds : cnt dm s = 0
    · exact ⟨_, hstep, l', dp, dm, rfl, rstep_red hrp _ _, rstep_red hrm _ _, h0 hds, hRdp, hRdm⟩
    · -- the other world (now minus) drives until it creates `s`
      have hrel' := h1 hds
      obtain ⟨z, hz, hzi⟩ := exists_rreach_injective hs hnull hm hsink hP
        (rstep_red hrp _ _ : Red m dp) hRdp
      have hzs : cnt z.2 s ≠ 0 := by
        have hb := (Fintype.bijective_iff_injective_and_card z.2).2 ⟨hzi, hA⟩
        obtain ⟨b, hb⟩ := hb.2 s
        exact Nat.pos_iff_ne_zero.1 ((cnt_pos_iff _ _).2 ⟨b, hb⟩)
      obtain ⟨l₃, gD, gF, hD, hF, hrel₃, hrD, hrF⟩ :=
        drive (LP := LP) hA hsm (x := (l', dp)) hz hzs dm (rstep_red hrm _ _)
          (rstep_red hrp _ _) hrel'
      exact ⟨_, hstep.trans (hF.reachable hdiag hsink), l₃, gD, gF, rfl, hrD, hrF, hrel₃,
        hRIrr _ _ hD hRdp, hRIrr _ _ hF hRdm⟩
  have hph : ∀ Y, G Y → ∀ u v, u ≠ v → ∃ Y₁ Y₂, LP.toProtocol.Reachable Y Y₁ ∧
      LP.toProtocol.Reachable (LP.toProtocol.interact Y₁ u v) Y₂ ∧ G Y₂ ∧
      ¬ Injective (leaderNames name Y) := by
    intro Y hY u v huv
    suffices H : ∃ Y₂, LP.toProtocol.Reachable (LP.toProtocol.interact Y u v) Y₂ ∧
        G Y₂ ∧ ¬ Injective (leaderNames name Y) by
      obtain ⟨Y₂, h1, h2, h3⟩ := H
      exact ⟨_, Y₂, Relation.ReflTransGen.refl, h1, h2, h3⟩
    rcases u with _ | a <;> rcases v with _ | b
    · exact absurd rfl huv
    · obtain ⟨Y₂, h1, h2⟩ := hleader Y hY b; exact ⟨Y₂, h1, h2, hnotinj Y hY⟩
    · rw [← hs.isSymmetric.interact_comm _ huv]
      obtain ⟨Y₂, h1, h2⟩ := hleader Y hY a; exact ⟨Y₂, h1, h2, hnotinj Y hY⟩
    · have hab : a ≠ b := fun h => huv (by rw [h])
      refine ⟨Y, ?_, hY, hnotinj Y hY⟩
      obtain ⟨l, cp, cm, rfl, -, hrm, -⟩ := hY
      rw [interact_mobile_mobile LP _ _ hab, mmUpd_red hnull hdiag hm hrm hab]
      exact Relation.ReflTransGen.refl
  obtain ⟨a₀⟩ := ‹Nonempty A›
  exact hP.false_of_phases G hph ⟨cm₀, rfl⟩ .refl
    ⟨l₀, cp₀, cm₀, rfl, hrp₀, hrm₀, hrel₀, ⟨cp₀, Relation.ReflTransGen.refl⟩,
      ⟨cm₀, Relation.ReflTransGen.refl⟩⟩
    (show (none : Option A) ≠ some a₀ by simp)

end Main

omit [DecidableEq Q] [Fintype A] [DecidableEq A] in
/-- **Theorem 11.** Under weak fairness, with an initialized leader (state `l₀`) but without
initialization of the mobile agents, no symmetric protocol with `P = card Q ≥ 2` states per mobile
agent solves naming for both population sizes `P - 1` (mobile agents `B`) and `P` (mobile agents
`Option B`). The leader may have any (even infinite) set of states `L`. -/
theorem thm11 {B : Type*} [Fintype B] [DecidableEq B] (h2 : 2 ≤ Fintype.card Q)
    (hcard : Fintype.card B + 1 = Fintype.card Q) (LP : LeaderProtocol L Q) (hs : LP.Symmetric)
    (name : Q → N) (l₀ : L) :
    ¬ (SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option B) (L ⊕ Q)))
        (leaderNames name) ∧
      SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option (Option B)) (L ⊕ Q)))
        (leaderNames name)) := by
  classical
  rintro ⟨hP1, hP⟩
  obtain ⟨m, hm, hsink, -⟩ := prop6 hs h2 hcard hP hP1
  obtain ⟨-, hnull⟩ := lemma2_sec31 hcard hP
  exact thm11_core (A := Option B) (by simp [hcard]) h2 hs hnull hm hsink hP

omit [DecidableEq Q] [Fintype A] [DecidableEq A] in
/-- **Theorem 11** (as stated in the paper): no symmetric protocol with `P ≥ 2` states per mobile
agent and an initialized leader names arbitrarily initialized mobile agents for every population
size `n ≤ P` under weak fairness. -/
theorem thm11_paper (h2 : 2 ≤ Fintype.card Q) (LP : LeaderProtocol L Q) (hs : LP.Symmetric)
    (name : Q → N) (l₀ : L) :
    ¬ ∀ (A : Type) [Fintype A] [DecidableEq A], Fintype.card A ≤ Fintype.card Q →
      SolvesWeak LP.toProtocol (initLeader l₀ : Set (Config (Option A) (L ⊕ Q)))
        (leaderNames name) := by
  intro h
  exact thm11 (B := Fin (Fintype.card Q - 1)) h2 (by simp; omega) LP hs name l₀
    ⟨h _ (by simp), h _ (by simp; omega)⟩

end Podc.PPNaming
