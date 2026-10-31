import Papers.PODC2015.EventualConsistencyLimits.Basic

/-!
# Late reads and Lemma 3

The basic tool of the paper: in a quiescent execution, appending reads forever gives an
infinite, sufficiently connected execution; in an eventually consistent abstract execution of it,
late reads of `o` see *all* writes to `o`, so their responses coincide (Lemma 3 of [AEM15]).
-/

namespace Podc.EventualConsistencyLimits

variable {ι Obj V M St : Type*}

namespace AE

variable {A : AE ι Obj V}

lemma WF.vis_dom (hA : A.WF) {a b : ℕ} (h : A.vis a b) : A.dom a ∧ A.dom b :=
  hA.ord_dom (hA.vis_ord h)

lemma WF.transGen_ord (hA : A.WF) {a b : ℕ} (h : Relation.TransGen A.vis a b) : A.ord a b := by
  induction h with
  | single h => exact hA.vis_ord h
  | tail _ h ih => exact hA.ord_trans ih (hA.vis_ord h)

lemma WF.ctxW_finite (hA : A.WF) (e : ℕ) : (A.ctxW e).Finite :=
  (hA.ord_fin e).subset fun _ h => hA.vis_ord h.1

/-- Number of predecessors in `H`. -/
noncomputable def rank (A : AE ι Obj V) (b : ℕ) : ℕ := {a | A.ord a b}.ncard

lemma WF.rank_lt (hA : A.WF) {a b : ℕ} (h : A.ord a b) : A.rank a < A.rank b := by
  apply Set.ncard_lt_ncard _ (hA.ord_fin b)
  refine ⟨fun x hx => hA.ord_trans hx h, fun hsub => hA.ord_irrefl a (hsub h)⟩

/-- Every write in a context lies below a maximal one. -/
lemma WF.exists_max_above (hA : A.WF) {e a : ℕ} (ha : a ∈ A.ctxW e) :
    ∃ c ∈ A.ctxW e, Relation.ReflTransGen A.vis a c ∧ ∀ b ∈ A.ctxW e, ¬ A.vis c b := by
  set T := {c | c ∈ A.ctxW e ∧ Relation.ReflTransGen A.vis a c}
  have hT : T.Finite := (hA.ctxW_finite e).subset fun _ h => h.1
  obtain ⟨c, hc, hmax⟩ := Set.exists_max_image T A.rank hT ⟨a, ha, .refl⟩
  refine ⟨c, hc.1, hc.2, fun b hb hcb => ?_⟩
  have := hmax b ⟨hb, hc.2.tail hcb⟩
  exact absurd (hA.rank_lt (hA.vis_ord hcb)) (not_lt.2 this)

lemma mvr_of_read {e : ℕ} (h : (A.ev e).op = .read) :
    A.mvr e = .vals {v | ∃ a ∈ A.ctxW e, (A.ev a).op = .write v ∧ ∀ b ∈ A.ctxW e, ¬ A.vis a b} := by
  simp [mvr, h]

/-- The response of a read `e` in a correct abstract execution. -/
lemma Correct.read {hA : A.Correct} {e : ℕ} {o : Obj} {S : Set V} (he : A.dom e)
    (hev : A.ev e = ⟨o, .read, .vals S⟩) :
    S = {v | ∃ a ∈ A.ctxW e, (A.ev a).op = .write v ∧ ∀ b ∈ A.ctxW e, ¬ A.vis a b} := by
  have := hA e he
  rw [mvr_of_read (by simp [hev]), hev] at this
  exact Resp.vals.inj this

/-- The response of a read `e` in a correct abstract execution (any response). -/
lemma Correct.read' {hA : A.Correct} {e : ℕ} {o : Obj} {r : Resp V} (he : A.dom e)
    (hev : A.ev e = ⟨o, .read, r⟩) :
    r = .vals {v | ∃ a ∈ A.ctxW e, (A.ev a).op = .write v ∧ ∀ b ∈ A.ctxW e, ¬ A.vis a b} := by
  have := hA e he
  rwa [mvr_of_read (by simp [hev]), hev] at this

lemma On.at {M : Type*} {s : ℕ → ι × Ev Obj V M} (h : A.On fun p => some (s p)) {p : ℕ} {i : ι}
    {d : DoEv Obj V} (hp : s p = (i, .do_ d)) : A.dom p ∧ A.rep p = i ∧ A.ev p = d :=
  ⟨(h.1 p).2 ⟨i, d, by simp [hp]⟩, h.2.1 p i d (by simp [hp])⟩

lemma On.of_dom {M : Type*} {s : ℕ → ι × Ev Obj V M} (h : A.On fun p => some (s p)) {p : ℕ}
    (hp : A.dom p) : ∃ i d, s p = (i, .do_ d) ∧ A.rep p = i ∧ A.ev p = d := by
  obtain ⟨i, d, hd⟩ := (h.1 p).1 hp
  have hd' : s p = (i, .do_ d) := by simpa using hd
  exact ⟨i, d, hd', h.2.1 p i d hd⟩

lemma On.atL {M : Type*} {α : List (ι × Ev Obj V M)} (h : A.On fun p => α[p]?) {p : ℕ}
    (hp : p < α.length) {i : ι} {d : DoEv Obj V} (he : α[p] = (i, .do_ d)) :
    A.dom p ∧ A.rep p = i ∧ A.ev p = d :=
  ⟨(h.1 p).2 ⟨i, d, by simp [hp, he]⟩, h.2.1 p i d (by simp [hp, he])⟩

lemma On.of_domL {M : Type*} {α : List (ι × Ev Obj V M)} (h : A.On fun p => α[p]?) {p : ℕ}
    (hp : A.dom p) : ∃ (hlt : p < α.length) (i : ι) (d : DoEv Obj V),
      α[p] = (i, .do_ d) ∧ A.rep p = i ∧ A.ev p = d := by
  obtain ⟨i, d, hd⟩ := (h.1 p).1 hp
  have hlt : p < α.length := by
    by_contra hc; simp [not_lt.1 hc] at hd
  refine ⟨hlt, i, d, by simpa [hlt] using hd, h.2.1 p i d hd⟩

/-- Eventually, reads of `o` see all the (finitely many) writes to `o`. -/
lemma exists_late (hA : A.WF) (hEC : A.EC) (o : Obj) (N : ℕ)
    (hN : ∀ q, A.dom q → (A.ev q).obj = o → A.IsWrite q → q < N) :
    ∃ N', ∀ p, N' ≤ p → A.dom p → (A.ev p).obj = o →
      A.ctxW p = {a | A.dom a ∧ (A.ev a).obj = o ∧ A.IsWrite a} := by
  set W := {a | A.dom a ∧ (A.ev a).obj = o ∧ A.IsWrite a}
  have hW : W.Finite := (Set.finite_lt_nat N).subset fun q hq => hN q hq.1 hq.2.1 hq.2.2
  set U := ⋃ a ∈ W, {e' | A.dom e' ∧ (A.ev e').obj = (A.ev a).obj ∧ ¬ A.vis a e'}
  have hU : U.Finite := hW.biUnion fun a ha => hEC a ha.1
  obtain ⟨B, hB⟩ := hU.bddAbove
  refine ⟨B + 1, fun p hp hdp hop => ?_⟩
  ext a
  constructor
  · rintro ⟨hv, hoa, hwa⟩
    exact ⟨(hA.vis_dom hv).1, hoa.trans hop, hwa⟩
  · rintro ⟨hda, hoa, hwa⟩
    refine ⟨?_, hoa.trans hop.symm, hwa⟩
    by_contra hv
    have : p ∈ U := Set.mem_biUnion (x := a) ⟨hda, hoa, hwa⟩ ⟨hdp, hop.trans hoa.symm, hv⟩
    have := hB this
    omega

end AE

namespace Store

variable (D : Store ι Obj V M St) [DecidableEq ι]

/-- Definition 17: quiescent finite executions. -/
def Quiescent (α : List (ι × Ev Obj V M)) : Prop :=
  (∀ i σ, D.state i α = some σ → ¬ D.Pending i σ) ∧
  ∀ j m, (j, .send m) ∈ α → ∀ i, i ≠ j → (i, .recv m) ∈ α

/-- `α` followed by the events `e₁` at `R₁` and `e₂` at `R₂`, alternating forever. -/
def ext2 (α : List (ι × Ev Obj V M)) (R₁ : ι) (e₁ : Ev Obj V M) (R₂ : ι) (e₂ : Ev Obj V M) :
    ℕ → ι × Ev Obj V M := fun p =>
  if h : p < α.length then α[p] else if (p - α.length) % 2 = 0 then (R₁, e₁) else (R₂, e₂)

variable {D}

section ext2

variable {α : List (ι × Ev Obj V M)} {R₁ R₂ : ι} {e₁ e₂ : Ev Obj V M}

lemma ext2_lt {p : ℕ} (hp : p < α.length) : ext2 α R₁ e₁ R₂ e₂ p = α[p] := by
  simp [ext2, hp]

lemma ext2_ge {p : ℕ} (hp : α.length ≤ p) :
    ext2 α R₁ e₁ R₂ e₂ p = (R₁, e₁) ∨ ext2 α R₁ e₁ R₂ e₂ p = (R₂, e₂) := by
  simp only [ext2, not_lt.2 hp, dite_false]
  split_ifs <;> simp

lemma ext2_even (k : ℕ) : ext2 α R₁ e₁ R₂ e₂ (α.length + 2 * k) = (R₁, e₁) := by
  simp [ext2]

lemma ext2_odd (k : ℕ) : ext2 α R₁ e₁ R₂ e₂ (α.length + 2 * k + 1) = (R₂, e₂) := by
  simp only [ext2]
  rw [dif_neg (by omega), if_neg (by omega)]

lemma pre_ext2_le {n : ℕ} (hn : n ≤ α.length) : pre (ext2 α R₁ e₁ R₂ e₂) n = α.take n := by
  apply List.ext_getElem (by simp [pre]; omega)
  intro k h1 h2
  simp only [pre, List.getElem_map, List.getElem_range, List.getElem_take]
  rw [ext2_lt]

lemma pre_succ (s : ℕ → ι × Ev Obj V M) (n : ℕ) : pre s (n + 1) = pre s n ++ [s n] := by
  simp [pre, List.range_succ]

/-- After `α`, the states do not change. -/
lemma state_pre_ext2 {σ₁ σ₂ : St} (h₁ : D.state R₁ α = some σ₁)
    (h₁' : D.step R₁ σ₁ e₁ = some σ₁) (h₂ : D.state R₂ α = some σ₂)
    (h₂' : D.step R₂ σ₂ e₂ = some σ₂) (i : ι) :
    ∀ n, α.length ≤ n → D.state i (pre (ext2 α R₁ e₁ R₂ e₂) n) = D.state i α := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [pre_ext2_le le_rfl, List.take_length]
  | succ n hn ih =>
    rw [pre_succ, state_snoc]
    rcases ext2_ge (R₁ := R₁) (e₁ := e₁) (R₂ := R₂) (e₂ := e₂) hn with h | h <;> rw [h] <;>
      dsimp only <;> split_ifs with hi
    · subst hi; rw [ih, h₁]; exact h₁'
    · exact ih
    · subst hi; rw [ih, h₂]; exact h₂'
    · exact ih

lemma isInfExec_ext2 (hα : D.IsExec α) {σ₁ σ₂ : St} (h₁ : D.state R₁ α = some σ₁)
    (h₁' : D.step R₁ σ₁ e₁ = some σ₁) (h₂ : D.state R₂ α = some σ₂)
    (h₂' : D.step R₂ σ₂ e₂ = some σ₂) (hr₁ : ∀ m, e₁ ≠ .recv m) (hr₂ : ∀ m, e₂ ≠ .recv m) :
    D.IsInfExec (ext2 α R₁ e₁ R₂ e₂) := by
  intro n
  rcases le_or_gt n α.length with hn | hn
  · rw [pre_ext2_le hn]
    rw [← List.take_append_drop n α] at hα
    exact hα.of_append
  · induction n, hn using Nat.le_induction with
    | base =>
      rw [pre_succ, pre_ext2_le le_rfl, List.take_length]
      rcases ext2_ge (R₁ := R₁) (e₁ := e₁) (R₂ := R₂) (e₂ := e₂) (le_refl α.length) with h | h <;>
        rw [h]
      · exact .snoc hα h₁ h₁' fun m hm => absurd hm (hr₁ m)
      · exact .snoc hα h₂ h₂' fun m hm => absurd hm (hr₂ m)
    | succ n hn ih =>
      rw [pre_succ]
      have hs := state_pre_ext2 h₁ h₁' h₂ h₂'
      rcases ext2_ge (R₁ := R₁) (e₁ := e₁) (R₂ := R₂) (e₂ := e₂) (le_of_lt hn) with h | h <;>
        rw [h]
      · exact .snoc ih (by rw [hs R₁ n (by omega), h₁]) h₁' fun m hm => absurd hm (hr₁ m)
      · exact .snoc ih (by rw [hs R₂ n (by omega), h₂]) h₂' fun m hm => absurd hm (hr₂ m)

lemma suffConnected_ext2 (hq : D.Quiescent α) {σ₁ σ₂ : St} (h₁ : D.state R₁ α = some σ₁)
    (h₁' : D.step R₁ σ₁ e₁ = some σ₁) (h₂ : D.state R₂ α = some σ₂)
    (h₂' : D.step R₂ σ₂ e₂ = some σ₂) (hs₁ : ∀ m, e₁ ≠ .send m) (hs₂ : ∀ m, e₂ ≠ .send m) :
    D.SuffConnected (ext2 α R₁ e₁ R₂ e₂) := by
  constructor
  · intro i N
    refine ⟨max N α.length, le_max_left _ _, fun σ hσ => ?_⟩
    rw [state_pre_ext2 h₁ h₁' h₂ h₂' i _ (by omega)] at hσ
    exact hq.1 i σ hσ
  · intro p i m hp j hj
    rcases lt_or_ge p α.length with hlt | hge
    · rw [ext2_lt hlt] at hp
      have hmem : (i, Ev.send m) ∈ α := hp ▸ List.getElem_mem hlt
      obtain ⟨q, hq', hqe⟩ := List.mem_iff_getElem.1 (hq.2 i m hmem j hj)
      exact ⟨q, by rw [ext2_lt hq', hqe]⟩
    · rcases ext2_ge (R₁ := R₁) (e₁ := e₁) (R₂ := R₂) (e₂ := e₂) hge with h | h <;>
        rw [h] at hp <;> cases hp
      · exact absurd rfl (hs₁ m)
      · exact absurd rfl (hs₂ m)

end ext2

/-- The read event `do(o, read, S)`. -/
abbrev rd (o : Obj) (r : Resp V) : Ev Obj V M := .do_ ⟨o, .read, r⟩

/-- In a quiescent execution, append reads of `o` at `R₁` and `R₂` forever. In a correct,
eventually consistent abstract execution of this infinite execution, some late read at each of
`R₁`, `R₂` sees exactly all the writes to `o`. -/
theorem exists_late_ae {P : AE ι Obj V → Prop} (hEC : D.EventuallyConsistent P)
    {α : List (ι × Ev Obj V M)} (hα : D.IsExec α) (hq : D.Quiescent α) {R₁ R₂ : ι} {o : Obj}
    {S₁ S₂ : Resp V} {σ₁ σ₂ : St} (h₁ : D.state R₁ α = some σ₁)
    (h₁' : D.step R₁ σ₁ (rd o S₁) = some σ₁) (h₂ : D.state R₂ α = some σ₂)
    (h₂' : D.step R₂ σ₂ (rd o S₂) = some σ₂) :
    ∃ A : AE ι Obj V, A.On (fun p => some (ext2 α R₁ (rd o S₁) R₂ (rd o S₂) p)) ∧ A.WF ∧
      A.Correct ∧ P A ∧ (∀ q, A.dom q → A.IsWrite q → q < α.length) ∧
      ∃ p₁ p₂, α.length ≤ p₁ ∧ α.length ≤ p₂ ∧
        A.dom p₁ ∧ A.dom p₂ ∧ A.rep p₁ = R₁ ∧ A.rep p₂ = R₂ ∧
        A.ev p₁ = ⟨o, .read, S₁⟩ ∧ A.ev p₂ = ⟨o, .read, S₂⟩ ∧
        A.ctxW p₁ = {a | A.dom a ∧ (A.ev a).obj = o ∧ A.IsWrite a} ∧
        A.ctxW p₂ = {a | A.dom a ∧ (A.ev a).obj = o ∧ A.IsWrite a} := by
  set s := ext2 α R₁ (rd o S₁) R₂ (rd o S₂)
  have hinf := isInfExec_ext2 hα h₁ h₁' h₂ h₂' (fun m h => by cases h) (fun m h => by cases h)
  have hsc := suffConnected_ext2 hq h₁ h₁' h₂ h₂' (fun m h => by cases h) (fun m h => by cases h)
  obtain ⟨A, hOn, hWF, hC, hEC', hP⟩ := hEC s hinf hsc
  -- writes only occur in `α`
  have hN : ∀ q, A.dom q → A.IsWrite q → q < α.length := by
    intro q hdq hwq
    by_contra hge
    obtain ⟨i, d, hsd⟩ := (hOn.1 q).1 hdq
    have hev := ((hOn.2.1 q i d hsd).2)
    obtain ⟨v, hv⟩ := hwq
    have hsd' : s q = (i, .do_ d) := by simpa using hsd
    rcases ext2_ge (R₁ := R₁) (e₁ := rd o S₁) (R₂ := R₂) (e₂ := rd o S₂) (not_lt.1 hge)
      with h | h <;> have h' := hsd'.symm.trans h <;> cases h' <;> rw [hev] at hv <;> cases hv
  obtain ⟨N', hN'⟩ := AE.exists_late hWF hEC' o _ fun q hq _ hw => hN q hq hw
  have key : ∀ p R S, s p = (R, rd o S) →
      A.dom p ∧ A.rep p = R ∧ A.ev p = ⟨o, .read, S⟩ := by
    intro p R S hp
    have hd : A.dom p := (hOn.1 p).2 ⟨R, ⟨o, .read, S⟩, by simp [hp]⟩
    obtain ⟨h1, h2⟩ := hOn.2.1 p R ⟨o, .read, S⟩ (by simp [hp])
    exact ⟨hd, h1, h2⟩
  have e1 : s (α.length + 2 * N') = (R₁, rd o S₁) := ext2_even N'
  have e2 : s (α.length + 2 * N' + 1) = (R₂, rd o S₂) := ext2_odd N'
  obtain ⟨d1, r1, v1⟩ := key _ _ _ e1
  obtain ⟨d2, r2, v2⟩ := key _ _ _ e2
  refine ⟨A, hOn, hWF, hC, hP, hN, _, _, by omega, by omega, d1, d2, r1, r2, v1, v2,
    hN' _ (by omega) d1 (by rw [v1]), hN' _ (by omega) d2 (by rw [v2])⟩

/-- **Lemma 3 of [AEM15].** In a quiescent execution of an eventually consistent data store,
reads of the same MVR at any two replicas return the same response. (Invisible reads enter
through `h₁'`, `h₂'`: the read leaves the state unchanged.) -/
theorem lemma3 {P : AE ι Obj V → Prop} (hEC : D.EventuallyConsistent P)
    (hIR : D.InvisibleReads) {α : List (ι × Ev Obj V M)} (hα : D.IsExec α)
    (hq : D.Quiescent α) {R₁ R₂ : ι} {o : Obj} {S₁ S₂ : Resp V} {σ₁ σ₂ σ₁' σ₂' : St}
    (h₁ : D.state R₁ α = some σ₁) (h₁' : D.step R₁ σ₁ (rd o S₁) = some σ₁')
    (h₂ : D.state R₂ α = some σ₂) (h₂' : D.step R₂ σ₂ (rd o S₂) = some σ₂') : S₁ = S₂ := by
  have e1 := hIR _ _ _ _ _ h₁'
  have e2 := hIR _ _ _ _ _ h₂'
  subst e1 e2
  obtain ⟨A, -, -, hC, -, -, p₁, p₂, -, -, d1, d2, -, -, v1, v2, c1, c2⟩ :=
    exists_late_ae hEC hα hq h₁ h₁' h₂ h₂'
  rw [AE.Correct.read' (hA := hC) d1 v1, AE.Correct.read' (hA := hC) d2 v2, c1, c2]

end Store

end Podc.EventualConsistencyLimits
