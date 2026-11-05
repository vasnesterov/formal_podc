import Papers.PODC2020.WhyExtensionBased.Defs

/-!
# Basic actions of the adversary: subdividing and terminating a vertex

* `subdivide`: the paper's "define `δ(v) = ⊥` for all undefined `v ∈ V_t`, subdivide, increment `t`".
  In our encoding undecided states are already active, so only `t` changes.
* `setTerm`: terminate a vertex of `V_t` (Lemma: `terminate_inv`, for a *safe* vertex).
* `qstep`: the adversary's reaction to a query `(C, q)` in phase 1.
* `Le`: the adversary state only grows.
-/

namespace Podc.WhyExtensionBased

open Cslib.NIS Cslib.NIS.Subdiv St
open scoped Classical

variable {P X : Type} [DecidableEq P]

/-- Subdivide: increment `t`. -/
def subdivide (A : AState P X) : AState P X := { A with t := A.t + 1 }

/-- Terminate `s` with output `a`. -/
noncomputable def setTerm (δ : Protocol P X X) (s : St P X) (a : X) : Protocol P X X :=
  fun s' => if s' = s then some a else δ s'

/-- States decided by the adversary: fewer than `t` rounds, or terminated. -/
def Fixd (A : AState P X) (s : St P X) : Prop := s.rounds < A.t ∨ decided A.term s ≠ none

/-- The adversary state only grows. -/
def Le (A A' : AState P X) : Prop :=
  A.t ≤ A'.t ∧ A.recs ⊆ A'.recs ∧ ∀ s, Fixd A s → decided A'.term s = decided A.term s

lemma Le.refl (A : AState P X) : Le A A := ⟨le_rfl, fun _ h => h, fun _ _ => rfl⟩

lemma Le.fixd {A A' : AState P X} (h : Le A A') {s : St P X} (hs : Fixd A s) : Fixd A' s := by
  rcases hs with hs | hs
  · exact Or.inl (lt_of_lt_of_le hs h.1)
  · exact Or.inr (by rw [h.2.2 s (Or.inr hs)]; exact hs)

lemma Le.trans {A B C : AState P X} (h1 : Le A B) (h2 : Le B C) : Le A C :=
  ⟨h1.1.trans h2.1, fun _ h => h2.2.1 (h1.2.1 h), fun s hs => by
    rw [h2.2.2 s (h1.fixd hs), h1.2.2 s hs]⟩

lemma Le.dec_none {A A' : AState P X} (h : Le A A') {s : St P X} (hs : decided A'.term s = none) :
    decided A.term s = none := by
  by_contra hne
  rw [h.2.2 s (Or.inr hne)] at hs; exact hne hs

lemma decided_setTerm {δ : Protocol P X X} {s : St P X} (hs : s.Settled) (hs0 : ¬ s.IsInit)
    (a : X) (z : St P X) :
    decided (setTerm δ s a) z = if z = s then some a else decided δ z := by
  cases z with
  | init i x =>
    have : init i x ≠ s := by rintro rfl; exact hs0 trivial
    simp [decided, this]
  | upd w =>
    have : upd w ≠ s := by rintro rfl; exact hs
    simp [decided, this]
  | scan w v => simp [decided, setTerm]

lemma Settled.not_isInit_of_rounds {s : St P X} (h : 1 ≤ s.rounds) : ¬ s.IsInit := by
  cases s <;> simp_all [IsInit, rounds]

lemma far_empty_left {G : St P X → St P X → Prop} {A B : Set (St P X)} {d : ℕ}
    (h : ∀ z, z ∉ A) : Far G A B d := fun _ _ a _ ha => absurd ha (h a)

lemma far_empty_right {G : St P X → St P X → Prop} {A B : Set (St P X)} {d : ℕ}
    (h : ∀ z, z ∉ B) : Far G A B d := fun _ _ _ _ _ b _ hb => absurd hb (h b)

/-! ## Facts about strict pasts -/

lemma Occ.past_rounds {δ : Protocol P X X} {w z : St P X} (hw : Occ δ w) (hz : InPast z w)
    (hne : z ≠ w) (hzs : z.Settled) (hws : w.Settled) : z.rounds < w.rounds := by
  obtain ⟨E, hE, hEw⟩ := hw
  have hmem : w ∈ (E w.pid).anc := by rw [hEw]; exact St.mem_anc_self _
  exact (Rch.past_rounds hE.rch hmem hz).2 hne hzs hws

/-- Low configurations: all processes did at most `t` rounds, and those between an update and a
scan fewer than `t`. Their strict pasts contain no settled state of `t` rounds. -/
def Low (t : ℕ) (C : Config P X) : Prop :=
  ∀ i, (C i).rounds ≤ t ∧ ((C i).rounds = t → (C i).Settled)

lemma Low.past {t : ℕ} {C : Config P X} (hC : Rch C) (hL : Low t C) {i : P} {z : St P X}
    (hz : InPast z (C i)) (hne : z ≠ C i) (hzs : z.Settled) : z.rounds < t := by
  have h := Rch.past_rounds hC (St.mem_anc_self (C i)) hz
  by_cases hs : (C i).Settled
  · have := h.2 hne hzs hs; have := (hL i).1; omega
  · have h1 := (hL i).1
    have h2 : (C i).rounds ≠ t := fun h' => hs ((hL i).2 h')
    omega

lemma RC.low {δ : Protocol P X X} {t : ℕ} {C : Config P X} (hC : RC δ t C) : Low t C := by
  intro i
  rcases hC.2 i with h | ⟨h, hd⟩
  · exact ⟨h.le, fun h' => by omega⟩
  · refine ⟨h.le, fun _ => ?_⟩
    cases hci : C i with
    | init => trivial
    | upd w => rw [hci] at hd; simp at hd
    | scan => trivial

/-- Terminating a settled state of `t` rounds keeps every low configuration reachable. -/
lemma reach_setTerm {δ : Protocol P X X} {t : ℕ} {C : Config P X} (hC : Reach δ C) (hL : Low t C)
    {s : St P X} (hs : s.Settled) (hst : s.rounds = t) (a : X) : Reach (setTerm δ s a) C := by
  obtain ⟨E', hE', h⟩ := hC.rch.exists_reach (δ' := setTerm δ s a) Set.univ fun i _ z hz hne => by
    have h1 := hC.past_active hz hne
    have hzs : z ≠ s := by
      rintro rfl
      have := Low.past hC.rch hL hz hne hs
      omega
    simp [setTerm, decided] at h1 ⊢
    cases z <;> simp_all [decided, setTerm]
  have : E' = C := funext fun i => h i (Set.mem_univ _)
  rwa [this] at hE'

/-! ## Subdivision -/

lemma RC.mono_t {δ : Protocol P X X} {t t' : ℕ} {C : Config P X} (h : RC δ t C) (ht : t ≤ t') :
    RC δ t' C := by
  refine ⟨h.1, fun j => ?_⟩
  rcases h.2 j with h | ⟨h, hd⟩
  · exact Or.inl (by omega)
  · rcases Nat.lt_or_ge t t' with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hd⟩

lemma RecOK.mono_t {δ : Protocol P X X} {t t' : ℕ} {rec : Config P X × Finset P × X}
    (h : RecOK δ t rec) (ht : t ≤ t') : RecOK δ t' rec :=
  ⟨h.1.mono_t ht, fun x hx => ⟨(h.2 x hx).1, fun h1 h2 h3 => (h.2 x hx).2 (by omega) h2 h3⟩⟩

/-- **Lemma 5.5**: subdividing keeps the invariants. -/
lemma AInv.subdiv {A : AState P X} (hA : AInv A) : AInv (subdivide A) := by
  obtain ⟨h4, h5⟩ := subdiv_far hA.dec_le hA.far4 hA.far5 le_rfl le_rfl
  exact ⟨by simp [subdivide],
    fun s hs => by have := hA.dec_le s hs; simp [subdivide]; omega,
    fun a => (h4 a).mono le_rfl le_rfl (by omega),
    fun a b hab => (h5 a b hab).mono le_rfl le_rfl (by omega),
    fun rec hrec => (hA.recs rec hrec).mono_t (by simp [subdivide])⟩

lemma Le.subdiv (A : AState P X) : Le A (subdivide A) :=
  ⟨by simp [subdivide], fun _ h => h, fun _ _ => rfl⟩

lemma AInv.subdiv_iter {A : AState P X} (hA : AInv A) (m : ℕ) : AInv (subdivide^[m] A) := by
  induction m generalizing A with
  | zero => exact hA
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih hA.subdiv

@[simp] lemma subdivide_iter_term (A : AState P X) (m : ℕ) : (subdivide^[m] A).term = A.term := by
  induction m generalizing A with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih]; rfl

@[simp] lemma subdivide_iter_recs (A : AState P X) (m : ℕ) : (subdivide^[m] A).recs = A.recs := by
  induction m generalizing A with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih]; rfl

@[simp] lemma subdivide_iter_t (A : AState P X) (m : ℕ) : (subdivide^[m] A).t = A.t + m := by
  induction m generalizing A with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih]; simp [subdivide]; omega

lemma Le.subdiv_iter (A : AState P X) (m : ℕ) : Le A (subdivide^[m] A) :=
  ⟨by simp, by simp, fun s _ => by simp⟩

/-! ## Terminating a safe vertex -/

section Terminate
variable {A : AState P X} {s : St P X} {a : X}

/-- Terminating a state of `t` rounds does not change the graph `G_t`. -/
lemma adj_setTerm (hst : s.rounds = A.t) {r : ℕ} (hr : r ≤ A.t) {u v : St P X} :
    Adj (setTerm A.term s a) r u v ↔ Adj A.term r u v := by
  refine adj_congr fun z hz => ?_
  cases z <;> simp [decided, setTerm] <;> rintro rfl <;> simp_all [rounds] <;> omega

lemma agree_setTerm (hst : s.rounds = A.t) {z : St P X} (hz : z.rounds < A.t) :
    decided (setTerm A.term s a) z = decided A.term z := by
  cases z <;> simp [decided, setTerm] <;> rintro rfl <;> simp_all [rounds] <;> omega

lemma uset_setTerm (hst : s.rounds = A.t) (b : X) :
    Uset (setTerm A.term s a) A.t b = Uset A.term A.t b := by
  ext u
  simp only [Uset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hv, ho, hn⟩
    have hv' : Vtx A.term A.t u := (vtx_congr fun z hz => agree_setTerm hst hz).1 hv
    exact ⟨hv', (occ_congr hv.1 fun z hz => agree_setTerm hst (by
      rcases hv.2 with h | h <;> omega)).1 ho, hn⟩
  · rintro ⟨hv, ho, hn⟩
    have hv' : Vtx (setTerm A.term s a) A.t u := (vtx_congr fun z hz => agree_setTerm hst hz).2 hv
    exact ⟨hv', (occ_congr hv.1 fun z hz => agree_setTerm hst (by
      rcases hv.2 with h | h <;> omega)).2 ho, hn⟩

lemma tset_setTerm (hss : s.Settled) (hs0 : ¬ s.IsInit) (hst : s.rounds = A.t)
    (hsd : decided A.term s = none) (b : X) :
    Tset (setTerm A.term s a) A.t b ⊆ Tset A.term A.t b ∪ {z | z = s ∧ b = a} := by
  rintro u ⟨hv, ho, hd⟩
  rw [decided_setTerm hss hs0] at hd
  by_cases hus : u = s
  · exact Or.inr ⟨hus, by simp [hus] at hd; exact hd.symm⟩
  · simp [hus] at hd
    have hv' : Vtx A.term A.t u := (vtx_congr fun z hz => agree_setTerm hst hz).1 hv
    exact Or.inl ⟨hv', (occ_congr hv.1 fun z hz => agree_setTerm hst (by
      rcases hv.2 with h | h <;> omega)).1 ho, hd⟩

/-- A safe vertex is not protected against its output. -/
lemma Safe.not_prot {δ : Protocol P X X} {t : ℕ} (hsafe : Safe δ t s a) (hss : s.Settled)
    (hst : s.rounds = t) (ho : Occ δ s) : ¬ Prot δ a s := by
  rintro (h | ⟨w, b, hb, hw, hadj⟩)
  · exact far_not_mem hsafe.1 (by norm_num) rfl ⟨⟨hss, Or.inl hst⟩, ho, h⟩
  · rw [hst] at hadj
    exact far_not_adj (hsafe.2 b hb) (by omega) rfl (mem_Tset_of_adj hadj hw) hadj

lemma prot_transfer {δ δ' : Protocol P X X} {y : X} {x : St P X} (hp : Prot δ y x)
    (hx : Occ δ' x) (hxs : x.Settled)
    (hw : ∀ w b, decided δ w = some b → Occ δ w → decided δ' w = some b ∧
      ∀ z, InPast z w → z ≠ w → decided δ' z = none) :
    Prot δ' y x := by
  rcases hp with h | ⟨w, b, hb, hwb, hadj⟩
  · exact Or.inl h
  · obtain ⟨hwb', hpast⟩ := hw w b hwb hadj.occ_right
    refine Or.inr ⟨w, b, hb, hwb', adj_transfer hadj hx hpast ⟨hxs, Or.inl rfl⟩ ?_⟩
    rcases hadj.2.2.1 with ⟨h1, h2 | ⟨h2, _⟩⟩
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr ⟨h2, by rw [hwb']; simp⟩⟩

lemma QDesc.mono {δ δ' : Protocol P X X} (h : ∀ z, decided δ' z = none → decided δ z = none)
    {C : Config P X} {Q : Finset P} {x : St P X} (hx : QDesc δ' C Q x) : QDesc δ C Q x := by
  obtain ⟨μ, hμQ, hμ, p, hp, rfl⟩ := hx
  exact ⟨μ, hμQ, hμ.mono h, p, hp, rfl⟩

lemma QDesc.occ {δ : Protocol P X X} {C : Config P X} {Q : Finset P} {x : St P X}
    (hC : Reach δ C) (hx : QDesc δ C Q x) : Occ δ x := by
  obtain ⟨μ, -, hμ, p, -, rfl⟩ := hx
  have hR := hC.run hμ
  exact ⟨_, hR, by rw [hR.pid]⟩

/-- **Terminating a safe vertex keeps the invariants** (the case "setting `δ(s') = a` maintains all
the invariants" of the paper; with our protected-descendant invariant replacing invariant 6). -/
lemma AInv.terminate (hA : AInv A) (hss : s.Settled) (hst : s.rounds = A.t)
    (hsd : decided A.term s = none) (ho : Occ A.term s) (hsafe : Safe A.term A.t s a) :
    AInv { A with term := setTerm A.term s a } := by
  have hs0 : ¬ s.IsInit := Settled.not_isInit_of_rounds (by have := hA.one_le; omega)
  have hdec := decided_setTerm (δ := A.term) hss hs0 a
  have hG : Adj (setTerm A.term s a) A.t = Adj A.term A.t := by
    funext u v; exact propext (adj_setTerm hst le_rfl)
  have hfar5s : ∀ b, b ≠ a → Far (Adj A.term A.t) (Tset A.term A.t b) {s} 3 :=
    fun b hb => (hsafe.2 b hb).symm adj_symm
  refine ⟨hA.one_le, fun z hz => ?_, fun b => ?_, fun b c hbc => ?_, fun rec hrec => ?_⟩
  · rw [hdec] at hz
    split_ifs at hz with h
    · rw [h, hst]
    · exact hA.dec_le z hz
  · simp only [hG, uset_setTerm hst]
    refine Far.mono ?_ (tset_setTerm hss hs0 hst hsd b) subset_rfl le_rfl
    refine far_union_left (hA.far4 b) ?_
    by_cases hba : b = a
    · subst hba; exact hsafe.1.mono (fun z hz => hz.1) subset_rfl le_rfl
    · exact far_empty_left fun z hz => hba hz.2
  · simp only [hG]
    refine Far.mono ?_ (tset_setTerm hss hs0 hst hsd b) (tset_setTerm hss hs0 hst hsd c) le_rfl
    refine far_union_left (far_union_right (hA.far5 b c hbc) ?_) (far_union_right ?_ ?_)
    · by_cases hca : c = a
      · subst hca; exact (hfar5s b hbc).mono subset_rfl (fun z hz => hz.1) le_rfl
      · exact far_empty_right fun z hz => hca hz.2
    · by_cases hba : b = a
      · subst hba; exact (hsafe.2 c (Ne.symm hbc)).mono (fun z hz => hz.1) subset_rfl le_rfl
      · exact far_empty_left fun z hz => hba hz.2
    · by_cases hba : b = a
      · subst hba; exact far_empty_right fun z hz => hbc hz.2.symm
      · exact far_empty_left fun z hz => hba hz.2
  · have hok := hA.recs rec hrec
    obtain ⟨⟨hCr, hCl⟩, hrest⟩ := hok
    have hCr' : Reach (setTerm A.term s a) rec.1 := reach_setTerm hCr (RC.low ⟨hCr, hCl⟩) hss hst a
    have hmono : ∀ z, decided (setTerm A.term s a) z = none → decided A.term z = none := by
      intro z hz; rw [hdec] at hz; split_ifs at hz; exact hz
    refine ⟨⟨hCr', fun j => ?_⟩, fun x hx => ?_⟩
    · rcases hCl j with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_⟩
        rw [hdec]; split_ifs with h
        · simp
        · exact h2
    · have hx' := hx.mono hmono
      obtain ⟨hr1, hr2⟩ := hrest x hx'
      refine ⟨?_, fun h1 h2 h3 => ?_⟩
      · rw [hdec]
        split_ifs with hxs
        · subst hxs
          intro hya
          simp at hya; subst hya
          exact hsafe.not_prot hss hst ho (hr2 (by omega) hss hsd)
        · exact hr1
      · have hxs : x ≠ s := by rintro rfl; rw [hdec] at h3; simp at h3
        have h3' : decided A.term x = none := hmono x h3
        refine prot_transfer (hr2 h1 h2 h3') (hx.occ hCr') h2 fun w b hwb hwo => ?_
        have hws : w ≠ s := by rintro rfl; rw [hsd] at hwb; simp at hwb
        refine ⟨by rw [hdec]; simp [hws, hwb], fun z hz hne => ?_⟩
        have hwset : w.Settled := by cases w <;> simp_all [decided]
        have hz1 := hwo.past_active hz hne
        have hzs : z ≠ s := by
          rintro rfl
          have := Occ.past_rounds hwo hz hne hss hwset
          have := hA.dec_le w (by rw [hwb]; simp)
          omega
        rw [hdec]; simp [hzs, hz1]


lemma Le.terminate {A : AState P X} {s : St P X} {a : X} (hst : s.rounds = A.t)
    (hsd : decided A.term s = none) (hss : s.Settled) (hs0 : ¬ s.IsInit) :
    Le A { A with term := setTerm A.term s a } := by
  refine ⟨le_rfl, fun _ h => h, fun z hz => ?_⟩
  show decided (setTerm A.term s a) z = decided A.term z
  rw [decided_setTerm hss hs0]
  split_ifs with h
  · subst h; rcases hz with hz | hz
    · omega
    · exact absurd hsd hz
  · rfl

lemma RC.setTerm {A : AState P X} {s : St P X} {a : X} {C : Config P X} (hC : RC A.term A.t C)
    (hss : s.Settled) (hst : s.rounds = A.t) (hs0 : ¬ s.IsInit) :
    RC (setTerm A.term s a) A.t C := by
  refine ⟨reach_setTerm hC.1 hC.low hss hst a, fun j => ?_⟩
  rcases hC.2 j with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, ?_⟩
    rw [decided_setTerm hss hs0]; split_ifs
    · simp
    · exact h2

/-! ## The adversary's reaction to a query `(C, q)` in phase 1 -/

/-- If the new state of `q` is an undecided vertex of `G_t`, terminate it with a safe value if there
is one; otherwise subdivide. -/
noncomputable def qstep (A : AState P X) (C : Config P X) (q : P) : AState P X :=
  if (stepState C q).Settled ∧ (stepState C q).rounds = A.t ∧
      decided A.term (stepState C q) = none then
    if h : ∃ a, Safe A.term A.t (stepState C q) a then
      { A with term := setTerm A.term (stepState C q) (Classical.choose h) }
    else subdivide A
  else A

lemma rounds_stepState_of_active {δ : Protocol P X X} {t : ℕ} {C : Config P X}
    (hC : RC δ t C) {q : P} (hq : Active δ C q) :
    (stepState C q).rounds ≤ t ∧ ((stepState C q).rounds = t → (stepState C q).Settled) := by
  have hlow := (hC.2 q)
  have hlt : (C q).rounds < t := by
    rcases hlow with h | ⟨_, h⟩
    · exact h
    · exact absurd hq h
  rcases stepState_cases C q with ⟨s, h1, h2⟩ | ⟨_, h2⟩
  · rw [h2]; rw [h1] at hlt; simp [rounds] at hlt ⊢; omega
  · rw [h2]; simp [rounds]; omega

/-- The query step keeps all invariants. -/
lemma qstep_spec {A : AState P X} (hA : AInv A) {C : Config P X} (hC : RC A.term A.t C) {q : P}
    (hq : Active A.term C q) :
    AInv (qstep A C q) ∧ Le A (qstep A C q) ∧ RC (qstep A C q).term (qstep A C q).t (step C q) ∧
      ∀ C', RC A.term A.t C' → RC (qstep A C q).term (qstep A C q).t C' := by
  have hR : Reach A.term (step C q) := hC.1.step hq
  obtain ⟨hr1, hr2⟩ := rounds_stepState_of_active hC hq
  have hlow : Low A.t (step C q) := fun j => by
    by_cases hj : j = q
    · subst hj; rw [step_self]; exact ⟨hr1, hr2⟩
    · rw [step_ne _ hj]; exact hC.low j
  unfold qstep
  split_ifs with h1 h2
  · obtain ⟨hss, hst, hsd⟩ := h1
    have hs0 : ¬ (stepState C q).IsInit := Settled.not_isInit_of_rounds (by have := hA.one_le; omega)
    have hpid : (stepState C q).pid = q := by rw [pid_stepState, hC.1.pid]
    have ho : Occ A.term (stepState C q) := ⟨step C q, hR, by rw [hpid]; simp⟩
    refine ⟨hA.terminate hss hst hsd ho (Classical.choose_spec h2), Le.terminate hst hsd hss hs0,
      ⟨reach_setTerm hR hlow hss hst _, fun j => ?_⟩, fun C' hC' => RC.setTerm hC' hss hst hs0⟩
    by_cases hj : j = q
    · subst hj; rw [step_self]; right
      refine ⟨hst, ?_⟩
      show decided (setTerm A.term _ _) _ ≠ none
      rw [decided_setTerm hss hs0]; simp
    · rw [step_ne _ hj]
      rcases hC.2 j with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_⟩
        show decided (setTerm A.term _ _) _ ≠ none
        rw [decided_setTerm hss hs0]; split_ifs
        · simp
        · exact h2
  · refine ⟨hA.subdiv, Le.subdiv A, ⟨hR, fun j => Or.inl ?_⟩, fun C' hC' => hC'.mono_t (by
      simp [subdivide])⟩
    show _ < A.t + 1
    by_cases hj : j = q
    · subst hj; rw [step_self]; omega
    · rw [step_ne _ hj]; have := (hC.low j).1; omega
  · refine ⟨hA, Le.refl A, ⟨hR, fun j => ?_⟩, fun C' hC' => hC'⟩
    by_cases hj : j = q
    · rw [hj, step_self]
      rcases Nat.lt_or_ge (stepState C q).rounds A.t with h | h
      · exact Or.inl h
      · have heq : (stepState C q).rounds = A.t := le_antisymm hr1 h
        refine Or.inr ⟨heq, fun hd => h1 ⟨hr2 heq, heq, hd⟩⟩
    · rw [step_ne _ hj]; exact hC.2 j

end Terminate

end Podc.WhyExtensionBased
