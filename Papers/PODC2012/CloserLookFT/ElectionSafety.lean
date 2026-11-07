import Papers.PODC2012.CloserLookFT.ElectionCore

/-!
# Safety of the election algorithm (Theorem 2.4): at most one leader

The paper proves Theorem 2.4 with an informal "accounting system of credits". We make it
precise with ghost state (`Ghost`):

* `age p`: the order in which processes wrote `turn` (`0` = not yet); since every process writes
  `turn` exactly once, `turn` always holds the youngest started process;
* `cr p`: the credits of `p`; register `V[j]` holds `2^j` credits while it is `0`;
* `own j`: the process holding the `2^j` credits taken from `V[j]` (while `V[j] ≠ 0`).

Credits move as in the paper: writing `p` over `0` into `V[j]` moves `2^j` credits from the
register to `p`; writing `0` over a non-zero value moves `2^j` credits from the writer to the
register; when `p` overwrites a non-zero `V[j]` and is *younger* than `own j`, the owner hands its
`2^j` credits to `p` (the paper's Rule 3/4 transfer "from `q` to `p`", made state-based by
comparing ages instead of referring to maximal groups of processes that "noticed together").

The invariant `Inv` says that credits are conserved (`n + 2^L - 1` in total), every process holds
at least its requirement `req` (`2^k` at level `k`, `2^L` once elected, otherwise what it may
still have to pay back), plus the structural facts `c1`, `c2` that replace the paper's
Lemma 2.3. An elected process holds `2^L` credits, so two of them would need
`2^(L+1) > n + 2^L - 1` credits when `n ≤ 2^L`.
-/

set_option linter.unusedSectionVars false

namespace Podc.CloserLookFT

open Finset

variable {P : Type} [DecidableEq P] [Fintype P]

/-- Ghost state for the credit argument. -/
structure Ghost (P : Type) where
  /-- order of the `turn` writes (`0` = not written yet) -/
  age : P → ℕ
  /-- credits of each process -/
  cr : P → ℤ
  /-- owner of the credits taken from `V[j]` -/
  own : ℕ → Option P

section Defs

variable (L : ℕ)

/-- Credits of the free registers: `V[j]` holds `2^j` while it is `0`. -/
def free (m : EMem P) : ℤ := ∑ j ∈ range L, if m.V j = none then (2 : ℤ) ^ j else 0

/-- What a doomed process `x` (in local state `l`) may still have to pay: `2^j` for every
register `V[j]` it may still write `0` into. -/
def cost (m : EMem P) (x : P) (l : ELoc) : ℤ :=
  ∑ j ∈ range L, if l.lo ≤ j ∧ j < l.written L ∧ (m.V j = some x ∨ l.clwAt j) then (2 : ℤ) ^ j
    else 0

/-- Credits that the owner `x` of `V[j]` must keep in reserve because a younger process is
about to overwrite `V[j]` (and will then claim them). -/
def rsv (s : ESys P) (g : Ghost P) (x : P) : ℤ :=
  ∑ j ∈ range L, if g.own j = some x ∧ ∃ y, g.age x < g.age y ∧ s.loc y = .wv j then (2 : ℤ) ^ j
    else 0

/-- The credits process `x` must hold. -/
def req (s : ESys P) (g : Ghost P) (x : P) : ℤ :=
  match s.loc x with
  | .idle | .start => 1
  | .rdone k | .rturn k | .rv k | .wv k => 2 ^ k
  | .rturn2 k => if s.m.turn = some x then 2 ^ (k + 1)
      else cost L s.m x (s.loc x) + rsv L s g x
  | .wdone => 2 ^ L
  | .out true _ _ _ => 2 ^ L
  | .clr .. | .clw .. | .out false .. => cost L s.m x (s.loc x) + rsv L s g x

/-- The invariant of the credit argument. -/
structure Inv (s : ESys P) (g : Ghost P) : Prop where
  wf : ∀ x, (s.loc x).WF L
  age0 : ∀ x, g.age x = 0 ↔ ¬ (s.loc x).Started
  ageInj : ∀ x y, g.age x = g.age y → g.age x ≠ 0 → x = y
  turnSome : ∀ x, s.m.turn = some x → g.age x ≠ 0 ∧ ∀ y, g.age y ≤ g.age x
  turnNone : s.m.turn = none → ∀ y, g.age y = 0
  hold : ∀ j x, s.m.V j = some x → (s.loc x).lo ≤ j ∧ j < (s.loc x).written L
  ownNone : ∀ j, g.own j = none ↔ s.m.V j = none
  ownW : ∀ j o, g.own j = some o → j < (s.loc o).written L
  c1 : ∀ x y j, s.m.V j = some x → j < (s.loc x).passed L → g.age x < g.age y →
    (s.loc y).written L ≤ j ∧ (s.loc y).passed L ≤ j ∧ s.loc y ≠ .wv j
  c2 : ∀ x y k, g.own k = some x → k < (s.loc x).passed L → g.age x < g.age y →
    s.loc y ≠ .wv k
  cons : ∑ x, g.cr x + free L s.m = Fintype.card P + 2 ^ L - 1
  reqLe : ∀ x, req L s g x ≤ g.cr x
  unst : ∀ x, ¬ (s.loc x).Started → g.cr x = 1

end Defs

/-! ### Sum lemmas -/

section Sums

lemma sum_ite_le_sum_ite {s : Finset ℕ} {c c' : ℕ → Prop} [DecidablePred c] [DecidablePred c']
    {f : ℕ → ℤ} (hf : ∀ j, 0 ≤ f j) (h : ∀ j ∈ s, c' j → c j) :
    (∑ j ∈ s, if c' j then f j else 0) ≤ ∑ j ∈ s, if c j then f j else 0 := by
  apply Finset.sum_le_sum
  intro j hj
  by_cases h1 : c' j
  · simp [h1, h j hj h1]
  · simp only [h1, ite_false]; split_ifs <;> simp [hf]

lemma sum_ite_nonneg {s : Finset ℕ} {c : ℕ → Prop} [DecidablePred c] {f : ℕ → ℤ}
    (hf : ∀ j, 0 ≤ f j) : 0 ≤ ∑ j ∈ s, if c j then f j else 0 :=
  Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hf]

lemma sum_pow_two_range (n : ℕ) : ∑ j ∈ range n, (2 : ℤ) ^ j = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- A sum of distinct powers `2^j` with `j < w` is at most `2^w - 1`. -/
lemma sum_ite_pow_le {L w : ℕ} {c : ℕ → Prop} [DecidablePred c] (hc : ∀ j, c j → j < w) :
    (∑ j ∈ range L, if c j then (2 : ℤ) ^ j else 0) ≤ 2 ^ w - 1 := by
  rw [← sum_pow_two_range]
  calc (∑ j ∈ range L, if c j then (2 : ℤ) ^ j else 0)
      = ∑ j ∈ (range L).filter c, (2 : ℤ) ^ j := by rw [Finset.sum_filter]
    _ ≤ ∑ j ∈ range w, (2 : ℤ) ^ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj; simp only [mem_filter] at hj; simpa using hc j hj.2
        · intro j _ _; positivity

/-- Changing a sum at one index. -/
lemma sum_eq_add_sub_of_eq_off {s : Finset ℕ} {f g : ℕ → ℤ} {k : ℕ} (hk : k ∈ s)
    (h : ∀ j ∈ s, j ≠ k → g j = f j) : ∑ j ∈ s, g j = ∑ j ∈ s, f j + (g k - f k) := by
  rw [← Finset.add_sum_erase s g hk, ← Finset.add_sum_erase s f hk,
    Finset.sum_congr rfl fun j hj => h j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)]
  ring

lemma sum_univ_update (f : P → ℤ) (p : P) (v : ℤ) :
    ∑ x, Function.update f p v x = ∑ x, f x + (v - f p) := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ p), ← Finset.add_sum_erase _ f (Finset.mem_univ p),
    Finset.sdiff_singleton_eq_erase]
  ring

end Sums

/-! ### Monotonicity of the requirements -/

section Mono

variable {L : ℕ}

@[simp] lemma ESys.step_m (p : P) (s : ESys P) : (s.step L p).m = (estep L p s.m (s.loc p)).1 := rfl
@[simp] lemma ESys.step_loc (p : P) (s : ESys P) :
    (s.step L p).loc = Function.update s.loc p (estep L p s.m (s.loc p)).2 := rfl

lemma cost_mono {m m' : EMem P} {x : P} {l : ELoc} (h : ∀ j, m'.V j = some x → m.V j = some x) :
    cost L m' x l ≤ cost L m x l := by
  unfold cost
  exact sum_ite_le_sum_ite (fun j => by positivity) fun j _ hj =>
    ⟨hj.1, hj.2.1, hj.2.2.imp_left (h j)⟩

lemma rsv_mono {s s' : ESys P} {g g' : Ghost P} {x : P}
    (h : ∀ j, (g'.own j = some x ∧ ∃ y, g'.age x < g'.age y ∧ s'.loc y = .wv j) →
      (g.own j = some x ∧ ∃ y, g.age x < g.age y ∧ s.loc y = .wv j)) :
    rsv L s' g' x ≤ rsv L s g x := by
  unfold rsv
  exact sum_ite_le_sum_ite (fun j => by positivity) fun j _ hj => h j hj

lemma cost_nonneg (m : EMem P) (x : P) (l : ELoc) : 0 ≤ cost L m x l :=
  sum_ite_nonneg fun j => by positivity

lemma rsv_nonneg (s : ESys P) (g : Ghost P) (x : P) : 0 ≤ rsv L s g x :=
  sum_ite_nonneg fun j => by positivity

lemma cost_le (m : EMem P) (x : P) (l : ELoc) : cost L m x l ≤ 2 ^ (l.written L) - 1 :=
  sum_ite_pow_le fun _ hj => hj.2.1

lemma req_nonneg (s : ESys P) (g : Ghost P) (x : P) : 0 ≤ req L s g x := by
  have h1 := cost_nonneg (L := L) s.m x (s.loc x)
  have h2 := rsv_nonneg (L := L) s g x
  unfold req
  split <;> (try split) <;> positivity

lemma req_le_req {s s' : ESys P} {g g' : Ghost P} {x : P} (hloc : s'.loc x = s.loc x)
    (hturn : (∃ k, s.loc x = .rturn2 k) → (s'.m.turn = some x ↔ s.m.turn = some x))
    (hcost : cost L s'.m x (s.loc x) ≤ cost L s.m x (s.loc x))
    (hrsv : rsv L s' g' x ≤ rsv L s g x) : req L s' g' x ≤ req L s g x := by
  unfold req
  rw [hloc]
  cases hl : s.loc x with
  | rturn2 k =>
    rw [hl] at hcost
    simp only [hturn ⟨k, hl⟩]
    split_ifs <;> linarith
  | clr k b j => rw [hl] at hcost; simp only; linarith
  | clw k b j => rw [hl] at hcost; simp only; linarith
  | out r a w c => rw [hl] at hcost; cases r <;> simp only <;> linarith
  | _ => simp


/-- Local states whose requirement is `cost + rsv`. -/
def ELoc.CostForm (l : ELoc) : Prop :=
  (∃ k b j, l = .clr k b j) ∨ (∃ k b j, l = .clw k b j) ∨ (∃ a w c, l = .out false a w c)

omit [DecidableEq P] in
lemma ELoc.costForm_nextClr (k b j : ℕ) : (nextClr k b j).CostForm := by
  unfold nextClr; split_ifs
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)

lemma req_eq_of_costForm {s : ESys P} {g : Ghost P} {x : P} (h : (s.loc x).CostForm) :
    req L s g x = cost L s.m x (s.loc x) + rsv L s g x := by
  unfold req
  rcases h with ⟨k, b, j, h⟩ | ⟨k, b, j, h⟩ | ⟨a, w, c, h⟩ <;> rw [h]


lemma req_eq_costRsv {s : ESys P} {g : Ghost P} {x : P}
    (h : (s.loc x).CostForm ∨ ∃ k, s.loc x = .rturn2 k ∧ s.m.turn ≠ some x) :
    req L s g x = cost L s.m x (s.loc x) + rsv L s g x := by
  rcases h with h | ⟨k, hk, ht⟩
  · exact req_eq_of_costForm h
  · unfold req; rw [hk]; simp [ht]

lemma cost_le_single {m : EMem P} {x : P} {l : ELoc} {k : ℕ} (hk : k < L)
    (hc : ∀ j, l.lo ≤ j → j < l.written L → (m.V j = some x ∨ l.clwAt j) → j = k) :
    cost L m x l ≤ 2 ^ k := by
  unfold cost
  calc (∑ j ∈ range L, if l.lo ≤ j ∧ j < l.written L ∧ (m.V j = some x ∨ l.clwAt j)
          then (2 : ℤ) ^ j else 0)
      ≤ ∑ j ∈ range L, if j = k then (2 : ℤ) ^ j else 0 :=
        sum_ite_le_sum_ite (fun j => by positivity) fun j _ hj => hc j hj.1 hj.2.1 hj.2.2
    _ = 2 ^ k := by rw [Finset.sum_ite_eq']; simp [hk]

lemma sum_add_le_of {s : Finset ℕ} {f g : ℕ → ℤ} {k : ℕ} {a : ℤ} (hk : k ∈ s)
    (h0 : g k + a ≤ f k) (h : ∀ i ∈ s, i ≠ k → g i ≤ f i) : ∑ i ∈ s, g i + a ≤ ∑ i ∈ s, f i := by
  rw [← Finset.add_sum_erase s g hk, ← Finset.add_sum_erase s f hk]
  have := Finset.sum_le_sum fun i hi => h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  linarith

/-- `rsv` vanishes for a process all of whose owned registers lie below its passed levels. -/
lemma rsv_eq_zero {s : ESys P} {g : Ghost P} {x : P} (hc2 : ∀ y k, g.own k = some x →
      k < (s.loc x).passed L → g.age x < g.age y → s.loc y ≠ .wv k)
    (h : ∀ j, g.own j = some x → j < (s.loc x).passed L) : rsv L s g x = 0 := by
  unfold rsv
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hj
  · obtain ⟨hj, y, hy, hwv⟩ := hj
    exact absurd hwv (hc2 y j hj (h j hj) hy)
  · rfl

end Mono

/-! ### Read steps -/

section Read

variable {L : ℕ}

/-- A step of `p` that does not change the memory (a read): only `p`'s local state changes, from
`s.loc p` to `l'`, keeping the ghost state. -/
lemma Inv.read {s : ESys P} {g : Ghost P} {p : P} {l' : ELoc} (h : Inv L s g)
    (hwf : l'.WF L) (hst : (s.loc p).Started) (hst' : l'.Started)
    (hw : l'.written L = (s.loc p).written L)
    (hlo : ∀ i, s.m.V i = some p → l'.lo ≤ i)
    (hpa : l'.passed L = (s.loc p).passed L ∨
      (s.m.turn = some p ∧ l'.passed L ≤ (s.loc p).written L))
    (hwv : ∀ j, l' = .wv j → s.m.V j = none)
    (hreq : req L ⟨s.m, Function.update s.loc p l'⟩ g p ≤ g.cr p) :
    Inv L ⟨s.m, Function.update s.loc p l'⟩ g := by
  have hap : g.age p ≠ 0 := fun h0 => ((h.age0 p).1 h0) hst
  -- `p` is younger than everybody if its `passed` grew
  have hyoung : l'.passed L ≠ (s.loc p).passed L → ∀ y, g.age y ≤ g.age p := by
    intro hne y
    rcases hpa with h1 | ⟨h1, -⟩
    · exact absurd h1 hne
    · exact (h.turnSome p h1).2 y
  constructor
  · intro x
    by_cases hx : x = p
    · subst hx; simpa using hwf
    · simpa [hx] using h.wf x
  · intro x
    by_cases hx : x = p
    · subst hx; simp [hap, hst']
    · simpa [hx] using h.age0 x
  · exact h.ageInj
  · exact h.turnSome
  · exact h.turnNone
  · intro j x hj
    by_cases hx : x = p
    · subst hx; simp only [Function.update_self]
      exact ⟨hlo j hj, hw ▸ (h.hold j x hj).2⟩
    · simpa [hx] using h.hold j x hj
  · exact h.ownNone
  · intro j o ho
    by_cases hx : o = p
    · subst hx; simpa [hw] using h.ownW j o ho
    · simpa [hx] using h.ownW j o ho
  · intro x y j hj hpx hxy
    simp only at hj
    by_cases hx : x = p
    · subst hx
      simp only [Function.update_self] at hpx
      by_cases hpe : l'.passed L = (s.loc x).passed L
      · have hyx : y ≠ x := by rintro rfl; exact lt_irrefl _ hxy
        simpa [hyx] using h.c1 x y j hj (hpe ▸ hpx) hxy
      · exact absurd (hyoung hpe y) (not_le.2 hxy)
    · simp only [Function.update_of_ne hx] at hpx
      obtain ⟨h1, h2, h3⟩ := h.c1 x y j hj hpx hxy
      by_cases hy : y = p
      · subst hy
        simp only [Function.update_self]
        refine ⟨hw ▸ h1, ?_, fun he => by simp [hwv j he] at hj⟩
        rcases hpa with e | ⟨-, e⟩
        · omega
        · omega
      · simpa [hy] using ⟨h1, h2, h3⟩
  · intro x y k hk hpx hxy
    by_cases hx : x = p
    · subst hx
      simp only [Function.update_self] at hpx
      by_cases hpe : l'.passed L = (s.loc x).passed L
      · have hyx : y ≠ x := by rintro rfl; exact lt_irrefl _ hxy
        simpa [hyx] using h.c2 x y k hk (hpe ▸ hpx) hxy
      · exact absurd (hyoung hpe y) (not_le.2 hxy)
    · simp only [Function.update_of_ne hx] at hpx
      by_cases hy : y = p
      · subst hy
        simp only [Function.update_self]
        intro he
        have := (h.ownNone k).2 (hwv k he)
        rw [this] at hk; cases hk
      · simpa [hy] using h.c2 x y k hk hpx hxy
  · exact h.cons
  · intro x
    by_cases hx : x = p
    · subst hx; exact hreq
    · refine le_trans (req_le_req (s := s) (s' := ⟨s.m, Function.update s.loc p l'⟩) (g := g)
        (by simp [hx]) (fun _ => Iff.rfl) le_rfl (rsv_mono ?_)) (h.reqLe x)
      rintro j ⟨hj, y, hy, hwvy⟩
      refine ⟨hj, y, hy, ?_⟩
      by_cases hyp : y = p
      · subst hyp
        simp only [Function.update_self] at hwvy
        have := (h.ownNone j).2 (hwv j hwvy)
        rw [this] at hj; cases hj
      · simpa [hyp] using hwvy
  · intro x hx'
    by_cases hx : x = p
    · subst hx; simp [hst'] at hx'
    · exact h.unst x (by simpa [hx] using hx')

end Read

section ReadCases

variable {L : ℕ}

omit [DecidableEq P] in
lemma ELoc.started_of_ne {l : ELoc} (h1 : l ≠ .idle) (h2 : l ≠ .start) : l.Started := ⟨h1, h2⟩

lemma rsv_read_self {s : ESys P} {g : Ghost P} {p : P} {l' : ELoc} :
    rsv L ⟨s.m, Function.update s.loc p l'⟩ g p ≤ rsv L s g p := by
  refine rsv_mono ?_
  rintro j ⟨hj, y, hy, hwv⟩
  have hyp : y ≠ p := by rintro rfl; exact lt_irrefl _ hy
  exact ⟨hj, y, hy, by simpa [hyp] using hwv⟩

lemma cost_le_cost {m : EMem P} {p : P} {l l' : ELoc}
    (h : ∀ i, l'.lo ≤ i → i < l'.written L → (m.V i = some p ∨ l'.clwAt i) →
      l.lo ≤ i ∧ i < l.written L ∧ (m.V i = some p ∨ l.clwAt i)) :
    cost L m p l' ≤ cost L m p l := by
  unfold cost
  exact sum_ite_le_sum_ite (fun j => by positivity) fun j _ hj => h j hj.1 hj.2.1 hj.2.2

/-- `rsv` of a process at a "pre-write" level `k` vanishes. -/
lemma Inv.rsv_pre {s : ESys P} {g : Ghost P} {p : P} (h : Inv L s g)
    (hpw : (s.loc p).written L ≤ (s.loc p).passed L) : rsv L s g p = 0 :=
  rsv_eq_zero (fun y k hk hkp hy => h.c2 p y k hk hkp hy)
    fun j hj => lt_of_lt_of_le (h.ownW j p hj) hpw

/-- The requirement of a doomed process that leaves a pre-write state at level `k` towards a
state with requirement `cost + rsv`. -/
lemma Inv.costRsv_le_of_pre {s : ESys P} {g : Ghost P} {p : P} {l' : ELoc} (h : Inv L s g)
    {k : ℕ} (hpre : (s.loc p).written L = k) (hpa : (s.loc p).passed L = k)
    (hw : l'.written L = k) (hreq : (2 : ℤ) ^ k ≤ g.cr p) :
    cost L s.m p l' + rsv L ⟨s.m, Function.update s.loc p l'⟩ g p ≤ g.cr p := by
  have h1 := cost_le (L := L) s.m p l'
  have h2 := rsv_read_self (L := L) (s := s) (g := g) (p := p) (l' := l')
  have h3 := h.rsv_pre (p := p) (by omega)
  rw [hw] at h1
  linarith

lemma Inv.cr_ge_of_req {s : ESys P} {g : Ghost P} {p : P} (h : Inv L s g) {k : ℕ}
    (hl : s.loc p = .rdone k ∨ s.loc p = .rturn k ∨ s.loc p = .rv k ∨ s.loc p = .wv k) :
    (2 : ℤ) ^ k ≤ g.cr p := by
  have := h.reqLe p
  unfold req at this
  rcases hl with hl | hl | hl | hl <;> rw [hl] at this <;> exact this

end ReadCases

section Steps

variable {L : ℕ}

lemma Inv.step_rdone {s : ESys P} {g : Ghost P} {p : P} {k : ℕ} (h : Inv L s g)
    (hl : s.loc p = .rdone k) : ∃ g', Inv L (s.step L p) g' := by
  have hk : k < L := by have := h.wf p; rw [hl] at this; exact this
  have hcr := h.cr_ge_of_req (Or.inl hl)
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  by_cases hd : s.m.done = true
  · have e : s.step L p = ⟨s.m, Function.update s.loc p (.out false k k 0)⟩ := by
      simp [ESys.step, estep, hl, hd]
    rw [e]
    refine ⟨g, h.read (by simp [ELoc.WF]; omega) hst (by simp [ELoc.Started])
      (by simp [ELoc.written, hl]) (by simp [ELoc.lo]) (Or.inl (by simp [ELoc.passed, hl]))
      (by simp) ?_⟩
    simp only [req, Function.update_self]
    exact h.costRsv_le_of_pre (by simp [hl, ELoc.written]) (by simp [hl, ELoc.passed])
      (by simp [ELoc.written]) hcr
  · have e : s.step L p = ⟨s.m, Function.update s.loc p (.rturn k)⟩ := by
      simp [ESys.step, estep, hl, hd]
    rw [e]
    refine ⟨g, h.read (by simpa [ELoc.WF] using hk) hst (by simp [ELoc.Started])
      (by simp [ELoc.written, hl]) (by simp [ELoc.lo]) (Or.inl (by simp [ELoc.passed, hl]))
      (by simp) ?_⟩
    simpa [req] using hcr

lemma costRsv_read {s : ESys P} {g : Ghost P} {p : P} {l' : ELoc}
    (h0 : cost L s.m p (s.loc p) + rsv L s g p ≤ g.cr p)
    (hc : ∀ i, l'.lo ≤ i → i < l'.written L → (s.m.V i = some p ∨ l'.clwAt i) →
      (s.loc p).lo ≤ i ∧ i < (s.loc p).written L ∧ (s.m.V i = some p ∨ (s.loc p).clwAt i)) :
    cost L s.m p l' + rsv L ⟨s.m, Function.update s.loc p l'⟩ g p ≤ g.cr p := by
  have h1 := cost_le_cost (L := L) hc
  have h2 := rsv_read_self (L := L) (s := s) (g := g) (p := p) (l' := l')
  linarith

lemma Inv.step_rturn {s : ESys P} {g : Ghost P} {p : P} {k : ℕ} (h : Inv L s g)
    (hl : s.loc p = .rturn k) : ∃ g', Inv L (s.step L p) g' := by
  have hk : k < L := by have := h.wf p; rw [hl] at this; exact this
  have hcr := h.cr_ge_of_req (Or.inr (Or.inl hl))
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  by_cases ht : s.m.turn = some p
  · have e : s.step L p = ⟨s.m, Function.update s.loc p (.rv k)⟩ := by
      simp [ESys.step, estep, hl, ht]
    rw [e]
    refine ⟨g, h.read (by simpa [ELoc.WF] using hk) hst (by simp [ELoc.Started])
      (by simp [ELoc.written, hl]) (by simp [ELoc.lo]) (Or.inl (by simp [ELoc.passed, hl]))
      (by simp) ?_⟩
    simpa [req] using hcr
  · by_cases hk0 : 0 < k
    · have e : s.step L p = ⟨s.m, Function.update s.loc p (.clr k k 0)⟩ := by
        simp [ESys.step, estep, hl, ht, nextClr, hk0]
      rw [e]
      refine ⟨g, h.read (by simp [ELoc.WF]; omega) hst (by simp [ELoc.Started])
        (by simp [ELoc.written, hl]) (by simp [ELoc.lo]) (Or.inl (by simp [ELoc.passed, hl]))
        (by simp) ?_⟩
      simp only [req, Function.update_self]
      exact h.costRsv_le_of_pre (by simp [hl, ELoc.written]) (by simp [hl, ELoc.passed])
        (by simp [ELoc.written]) hcr
    · have e : s.step L p = ⟨s.m, Function.update s.loc p (.out false k k k)⟩ := by
        simp [ESys.step, estep, hl, ht, nextClr, hk0]
      rw [e]
      refine ⟨g, h.read (by simp [ELoc.WF]; omega) hst (by simp [ELoc.Started])
        (by simp [ELoc.written, hl]) (fun i hi => ?_) (Or.inl (by simp [ELoc.passed, hl]))
        (by simp) ?_⟩
      · have := (h.hold i p hi).2; simp [hl, ELoc.written] at this; omega
      · simp only [req, Function.update_self]
        exact h.costRsv_le_of_pre (by simp [hl, ELoc.written]) (by simp [hl, ELoc.passed])
          (by simp [ELoc.written]) hcr

lemma Inv.step_rv {s : ESys P} {g : Ghost P} {p : P} {k : ℕ} (h : Inv L s g)
    (hl : s.loc p = .rv k) : ∃ g', Inv L (s.step L p) g' := by
  have hk : k < L := by have := h.wf p; rw [hl] at this; exact this
  have hcr := h.cr_ge_of_req (Or.inr (Or.inr (Or.inl hl)))
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  by_cases hv : s.m.V k = none
  · have e : s.step L p = ⟨s.m, Function.update s.loc p (.wv k)⟩ := by
      simp [ESys.step, estep, hl, hv]
    rw [e]
    refine ⟨g, h.read (by simpa [ELoc.WF] using hk) hst (by simp [ELoc.Started])
      (by simp [ELoc.written, hl]) (by simp [ELoc.lo]) (Or.inl (by simp [ELoc.passed, hl]))
      (by rintro j ⟨⟩; exact hv) ?_⟩
    simpa [req] using hcr
  · have e : s.step L p = ⟨s.m, Function.update s.loc p (.rdone k)⟩ := by
      simp [ESys.step, estep, hl, hv]
    rw [e]
    refine ⟨g, h.read (by simpa [ELoc.WF] using hk) hst (by simp [ELoc.Started])
      (by simp [ELoc.written, hl]) (by simp [ELoc.lo]) (Or.inl (by simp [ELoc.passed, hl]))
      (by simp) ?_⟩
    simpa [req] using hcr

lemma Inv.step_rturn2 {s : ESys P} {g : Ghost P} {p : P} {k : ℕ} (h : Inv L s g)
    (hl : s.loc p = .rturn2 k) : ∃ g', Inv L (s.step L p) g' := by
  have hk : k < L := by have := h.wf p; rw [hl] at this; exact this
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  have hr := h.reqLe p
  simp only [req, hl] at hr
  by_cases ht : s.m.turn = some p
  · simp only [ht, ite_true] at hr
    by_cases hk1 : k + 1 < L
    · have e : s.step L p = ⟨s.m, Function.update s.loc p (.rdone (k + 1))⟩ := by
        simp [ESys.step, estep, hl, ht, hk1]
      rw [e]
      refine ⟨g, h.read (by simpa [ELoc.WF] using hk1) hst (by simp [ELoc.Started])
        (by simp [ELoc.written, hl]) (by simp [ELoc.lo])
        (Or.inr ⟨ht, by simp [ELoc.passed, ELoc.written, hl]⟩) (by simp) ?_⟩
      simpa [req] using hr
    · have e : s.step L p = ⟨s.m, Function.update s.loc p .wdone⟩ := by
        simp [ESys.step, estep, hl, ht, hk1]
      have hL : L = k + 1 := by omega
      rw [e]
      refine ⟨g, h.read (by simp [ELoc.WF]) hst (by simp [ELoc.Started])
        (by simp [ELoc.written, hl, hL]) (by simp [ELoc.lo])
        (Or.inr ⟨ht, by simp [ELoc.passed, ELoc.written, hl, hL]⟩) (by simp) ?_⟩
      simpa [req, hL] using hr
  · simp only [ht, ite_false] at hr
    have e : s.step L p = ⟨s.m, Function.update s.loc p (.clr k (k + 1) 0)⟩ := by
      simp [ESys.step, estep, hl, ht, nextClr]
    rw [e]
    refine ⟨g, h.read (by simp [ELoc.WF]; omega) hst (by simp [ELoc.Started])
      (by simp [ELoc.written, hl]) (by simp [ELoc.lo]) (Or.inl (by simp [ELoc.passed, hl]))
      (by simp) ?_⟩
    simp only [req, Function.update_self]
    rw [← hl] at hr
    exact costRsv_read hr fun i h1 h2 h3 => by
      rw [hl]; simp only [ELoc.lo, ELoc.written, ELoc.clwAt] at h1 h2 h3 ⊢; exact ⟨h1, h2, h3⟩

lemma Inv.step_clr {s : ESys P} {g : Ghost P} {p : P} {k b j : ℕ} (h : Inv L s g)
    (hl : s.loc p = .clr k b j) : ∃ g', Inv L (s.step L p) g' := by
  have hwf : k < L ∧ (b = k ∨ b = k + 1) ∧ j < b := by
    have := h.wf p; rw [hl] at this; exact this
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  have hr := h.reqLe p
  simp only [req, hl] at hr
  rw [← hl] at hr
  have hhold : ∀ i, s.m.V i = some p → j ≤ i ∧ i < b := fun i hi => by
    simpa [hl, ELoc.lo, ELoc.written] using h.hold i p hi
  by_cases hv : s.m.V j = some p
  · have e : s.step L p = ⟨s.m, Function.update s.loc p (.clw k b j)⟩ := by
      simp [ESys.step, estep, hl, hv]
    rw [e]
    refine ⟨g, h.read (by simpa [ELoc.WF] using hwf) hst (by simp [ELoc.Started])
      (by simp [ELoc.written, hl]) (fun i hi => by simpa [ELoc.lo] using (hhold i hi).1)
      (Or.inl (by simp [ELoc.passed, hl])) (by simp) ?_⟩
    simp only [req, Function.update_self]
    refine costRsv_read hr fun i h1 h2 h3 => ?_
    rw [hl]
    simp only [ELoc.lo, ELoc.written, ELoc.clwAt] at h1 h2 h3 ⊢
    refine ⟨h1, h2, Or.inl ?_⟩
    rcases h3 with h3 | h3
    · exact h3
    · exact h3 ▸ hv
  · by_cases hj1 : j + 1 < b
    · have e : s.step L p = ⟨s.m, Function.update s.loc p (.clr k b (j + 1))⟩ := by
        simp [ESys.step, estep, hl, hv, nextClr, hj1]
      rw [e]
      refine ⟨g, h.read (by simp [ELoc.WF]; omega) hst (by simp [ELoc.Started])
        (by simp [ELoc.written, hl]) (fun i hi => ?_)
        (Or.inl (by simp [ELoc.passed, hl])) (by simp) ?_⟩
      · have := hhold i hi
        have : i ≠ j := by rintro rfl; exact hv hi
        simp [ELoc.lo]; omega
      · simp only [req, Function.update_self]
        refine costRsv_read hr fun i h1 h2 h3 => ?_
        rw [hl]
        simp only [ELoc.lo, ELoc.written, ELoc.clwAt, or_false] at h1 h2 h3 ⊢
        exact ⟨by omega, h2, h3⟩
    · have e : s.step L p = ⟨s.m, Function.update s.loc p (.out false k b b)⟩ := by
        simp [ESys.step, estep, hl, hv, nextClr, hj1]
      rw [e]
      refine ⟨g, h.read (by simp [ELoc.WF]; omega) hst (by simp [ELoc.Started])
        (by simp [ELoc.written, hl]) (fun i hi => ?_)
        (Or.inl (by simp [ELoc.passed, hl])) (by simp) ?_⟩
      · have := hhold i hi
        have : i ≠ j := by rintro rfl; exact hv hi
        simp [ELoc.lo]; omega
      · simp only [req, Function.update_self]
        refine costRsv_read hr fun i h1 h2 h3 => ?_
        simp only [ELoc.lo, ELoc.written] at h1 h2
        omega

/-- The invariant only depends on `turn` and `V`. -/
lemma Inv.congr_m {m m' : EMem P} {loc : P → ELoc} {g : Ghost P} (h : Inv L ⟨m, loc⟩ g)
    (ht : m'.turn = m.turn) (hV : m'.V = m.V) : Inv L ⟨m', loc⟩ g := by
  obtain ⟨m₁, m₂, m₃⟩ := m
  obtain ⟨m₁', m₂', m₃'⟩ := m'
  simp only at ht hV
  subst ht hV
  exact ⟨h.wf, h.age0, h.ageInj, h.turnSome, h.turnNone, h.hold, h.ownNone, h.ownW, h.c1, h.c2,
    h.cons, h.reqLe, h.unst⟩

lemma Inv.step_wdone {s : ESys P} {g : Ghost P} {p : P} (h : Inv L s g)
    (hl : s.loc p = .wdone) : ∃ g', Inv L (s.step L p) g' := by
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  have hr := h.reqLe p
  simp only [req, hl] at hr
  have e : s.step L p = ⟨{ s.m with done := true }, Function.update s.loc p (.out true L L 0)⟩ := by
    simp [ESys.step, estep, hl]
  rw [e]
  refine ⟨g, Inv.congr_m (m := s.m) ?_ rfl rfl⟩
  refine h.read (by simp [ELoc.WF]) hst (by simp [ELoc.Started])
    (by simp [ELoc.written, hl]) (by simp [ELoc.lo]) (Or.inl (by simp [ELoc.passed, hl]))
    (by simp) ?_
  simpa [req] using hr

lemma Inv.step_start {s : ESys P} {g : Ghost P} {p : P} (h : Inv L s g)
    (hl : s.loc p = .start) : ∃ g', Inv L (s.step L p) g' := by
  set l' : ELoc := if 0 < L then .rdone 0 else .wdone with hl'
  have e : s.step L p = ⟨{ s.m with turn := some p }, Function.update s.loc p l'⟩ := by
    simp [ESys.step, estep, hl, hl']
  rw [e]
  have hns : ¬ (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  have hap : g.age p = 0 := (h.age0 p).2 hns
  have hcrp : g.cr p = 1 := h.unst p hns
  have hVp : ∀ j, s.m.V j ≠ some p := fun j hj => by
    have := (h.hold j p hj).2; simp [hl, ELoc.written] at this
  have hOp : ∀ j, g.own j ≠ some p := fun j hj => by
    have := h.ownW j p hj; simp [hl, ELoc.written] at this
  have hl'w : l'.written L = 0 ∧ l'.passed L = 0 ∧ (∀ j, l' ≠ .wv j) ∧ l'.Started ∧ l'.WF L ∧
      ∀ g'' : Ghost P,
        req L ⟨{ s.m with turn := some p }, Function.update s.loc p l'⟩ g'' p = 1 := by
    by_cases hL : 0 < L
    · simp [hl', hL, ELoc.written, ELoc.passed, ELoc.Started, ELoc.WF, req]
    · have : L = 0 := by omega
      subst this
      simp [hl', ELoc.written, ELoc.passed, ELoc.Started, ELoc.WF, req]
  obtain ⟨hw0, hp0, hnwv, hst', hwf', hreq'⟩ := hl'w
  set M := Finset.univ.sup g.age
  have hM : ∀ x, g.age x ≤ M := fun x => Finset.le_sup (f := g.age) (Finset.mem_univ x)
  let g' : Ghost P := { g with age := Function.update g.age p (M + 1) }
  have hage : ∀ x, x ≠ p → g'.age x = g.age x := fun x hx => by simp [g', hx]
  have hagep : g'.age p = M + 1 := by simp [g']
  refine ⟨g', ?_⟩
  constructor
  · intro x
    by_cases hx : x = p
    · subst hx; simpa using hwf'
    · simpa [hx] using h.wf x
  · intro x
    by_cases hx : x = p
    · subst hx; simp [hagep, hst']
    · simpa [hx, hage x hx] using h.age0 x
  · intro x y hxy hx0
    by_cases hx : x = p
    · subst hx
      by_cases hy : y = x
      · exact hy.symm
      · rw [hagep, hage y hy] at hxy; have := hM y; omega
    · by_cases hy : y = p
      · subst hy; rw [hagep, hage x hx] at hxy; have := hM x; omega
      · exact h.ageInj x y (by simpa [g', hx, hy] using hxy) (by simpa [g', hx] using hx0)
  · intro x hx
    have hxp : x = p := by simpa using hx.symm
    subst hxp
    refine ⟨by rw [hagep]; omega, fun y => ?_⟩
    by_cases hy : y = x
    · subst hy; rfl
    · rw [hage y hy, hagep]; have := hM y; omega
  · intro hx; simp at hx
  · intro j x hj
    have hx : x ≠ p := by rintro rfl; exact hVp j hj
    simpa [hx] using h.hold j x hj
  · exact h.ownNone
  · intro j o ho
    have hx : o ≠ p := by rintro rfl; exact hOp j ho
    simpa [hx] using h.ownW j o ho
  · intro x y j hj hpx hxy
    have hx : x ≠ p := by rintro rfl; exact hVp j hj
    simp only [Function.update_of_ne hx] at hpx
    rw [hage x hx] at hxy
    by_cases hy : y = p
    · subst hy; simp only [Function.update_self]
      exact ⟨by omega, by omega, hnwv j⟩
    · rw [hage y hy] at hxy
      simpa [hy] using h.c1 x y j hj hpx hxy
  · intro x y k hk hpx hxy
    have hx : x ≠ p := by rintro rfl; exact hOp k hk
    simp only [Function.update_of_ne hx] at hpx
    rw [hage x hx] at hxy
    by_cases hy : y = p
    · subst hy; simp only [Function.update_self]; exact hnwv k
    · rw [hage y hy] at hxy
      simpa [hy] using h.c2 x y k hk hpx hxy
  · exact h.cons
  · intro x
    by_cases hx : x = p
    · subst hx; rw [hreq' g']; exact hcrp.ge
    · -- the requirement of `x` can only decrease
      have hrsv : rsv L ⟨{ s.m with turn := some p }, Function.update s.loc p l'⟩ g' x ≤
          rsv L s g x := by
        refine rsv_mono ?_
        rintro j ⟨hj, y, hy, hwv⟩
        have hyp : y ≠ p := by rintro rfl; simp at hwv; exact hnwv j hwv
        rw [hage x hx, hage y hyp] at hy
        exact ⟨hj, y, hy, by simpa [hyp] using hwv⟩
      by_cases htx : s.m.turn = some x ∧ ∃ k, s.loc x = .rturn2 k
      · -- `x` was the youngest process at line 10; it is now doomed
        obtain ⟨htx, k, hk⟩ := htx
        have hr := h.reqLe x
        simp only [req, hk, htx, ite_true] at hr
        have hrsv0 : rsv L ⟨{ s.m with turn := some p }, Function.update s.loc p l'⟩ g' x = 0 := by
          unfold rsv
          refine Finset.sum_eq_zero fun j _ => ?_
          split_ifs with hj
          · obtain ⟨-, y, hy, hwv⟩ := hj
            have hyp : y ≠ p := by rintro rfl; simp at hwv; exact hnwv j hwv
            rw [hage x hx, hage y hyp] at hy
            exact absurd ((h.turnSome x htx).2 y) (not_le.2 hy)
          · rfl
        have hc := cost_le (L := L) s.m x (s.loc x)
        simp only [hk, ELoc.written] at hc
        simp only [req, Function.update_of_ne hx, hk]
        have hne : (some p = some x) = False := by simp [Ne.symm hx]
        simp only [hne, ite_false, hrsv0]
        change cost L s.m x (ELoc.rturn2 k) + 0 ≤ g.cr x
        linarith
      · refine le_trans (req_le_req (s := s) (g := g) (by simp [hx]) (fun hk => ?_) le_rfl hrsv)
          (h.reqLe x)
        have : ¬ s.m.turn = some x := fun h' => htx ⟨h', hk⟩
        simp [this, Ne.symm hx]
  · intro x hx'
    by_cases hx : x = p
    · subst hx; simp [hst'] at hx'
    · exact h.unst x (by simpa [hx] using hx')

lemma Inv.step_clw {s : ESys P} {g : Ghost P} {p : P} {k b j : ℕ} (h : Inv L s g)
    (hl : s.loc p = .clw k b j) : ∃ g', Inv L (s.step L p) g' := by
  have hwf : k < L ∧ (b = k ∨ b = k + 1) ∧ j < b := by
    have := h.wf p; rw [hl] at this; exact this
  have hjL : j < L := by omega
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  have hap : g.age p ≠ 0 := fun h0 => ((h.age0 p).1 h0) hst
  have hr := h.reqLe p
  simp only [req, hl] at hr
  rw [← hl] at hr
  have hhold : ∀ i, s.m.V i = some p → j ≤ i ∧ i < b := fun i hi => by
    simpa [hl, ELoc.lo, ELoc.written] using h.hold i p hi
  set l' := nextClr k b (j + 1) with hl'
  have hl'wf : l'.WF L := by
    simp only [hl', nextClr]; split_ifs <;> simp [ELoc.WF] <;> omega
  have hl'st : l'.Started := by simp only [hl', nextClr]; split_ifs <;> simp [ELoc.Started]
  have hl'w : l'.written L = b := by simp only [hl', nextClr]; split_ifs <;> simp [ELoc.written]
  have hl'p : l'.passed L = k := by simp only [hl', nextClr]; split_ifs <;> simp [ELoc.passed]
  have hl'lo : j + 1 ≤ l'.lo := by
    simp only [hl', nextClr]; split_ifs <;> simp [ELoc.lo] <;> omega
  have hl'lo2 : ∀ i, j + 1 ≤ i → i < b → l'.lo ≤ i := by
    intro i h1 h2; simp only [hl', nextClr]; split_ifs <;> simp [ELoc.lo] <;> omega
  have hl'wv : ∀ i, l' ≠ .wv i := by
    intro i; simp only [hl', nextClr]; split_ifs <;> simp
  have hl'clw : ∀ i, ¬ l'.clwAt i := by
    intro i; simp only [hl', nextClr]; split_ifs <;> simp [ELoc.clwAt]
  have hlo' : ∀ i, s.m.V i = some p → i ≠ j → l'.lo ≤ i := fun i hi hij => by
    have := hhold i hi; exact hl'lo2 i (by omega) this.2
  -- the new cost of `p` lacks the term for index `j`
  have hcost : ∀ m' : EMem P, (∀ i, i ≠ j → m'.V i = s.m.V i) →
      cost L m' p l' + 2 ^ j ≤ cost L s.m p (s.loc p) := by
    intro m' hm'
    unfold cost
    refine sum_add_le_of (Finset.mem_range.2 hjL) ?_ fun i _ hij => ?_
    · rw [if_neg (by omega), hl]; simp [ELoc.lo, ELoc.written, ELoc.clwAt, hwf.2.2]
    · rw [hm' i hij]
      by_cases hc : l'.lo ≤ i ∧ i < l'.written L ∧ (s.m.V i = some p ∨ l'.clwAt i)
      · rw [if_pos hc, if_pos]
        rw [hl]; simp only [ELoc.lo, ELoc.written, ELoc.clwAt]
        exact ⟨by omega, hl'w ▸ hc.2.1, hc.2.2.imp_right fun h => absurd h (hl'clw _)⟩
      · rw [if_neg hc]; split_ifs <;> positivity
  have hrsvp : ∀ (m' : EMem P) (g' : Ghost P), g'.age = g.age →
      (∀ i, g'.own i = some p → g.own i = some p) →
      rsv L ⟨m', Function.update s.loc p l'⟩ g' p ≤ rsv L s g p := by
    intro m' g' ha ho
    refine rsv_mono ?_
    rintro i ⟨hi, y, hy, hwv⟩
    have hyp : y ≠ p := by rintro rfl; exact lt_irrefl _ hy
    rw [ha] at hy
    exact ⟨ho i hi, y, hy, by simpa [hyp] using hwv⟩
  by_cases hv : s.m.V j = none
  · have e : s.step L p = ⟨s.m, Function.update s.loc p l'⟩ := by
      simp only [ESys.step, estep, hl, ← hl']
      congr 1
      have : Function.update s.m.V j none = s.m.V := by
        rw [← hv]; exact Function.update_eq_self j s.m.V
      rw [this]
    rw [e]
    refine ⟨g, h.read hl'wf hst hl'st (by rw [hl'w, hl]; rfl)
      (fun i hi => hlo' i hi (by rintro rfl; rw [hv] at hi; cases hi))
      (Or.inl (by rw [hl'p, hl]; rfl)) (fun i hi => absurd hi (hl'wv i)) ?_⟩
    rw [req_eq_of_costForm (by simpa using ELoc.costForm_nextClr k b (j + 1))]
    simp only [Function.update_self]
    have h1 := hcost s.m (fun _ _ => rfl)
    have h2 := hrsvp s.m g rfl (fun _ h => h)
    have : (0 : ℤ) < 2 ^ j := by positivity
    linarith
  · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hv
    let m' : EMem P := { s.m with V := Function.update s.m.V j none }
    let g' : Ghost P := { g with cr := Function.update g.cr p (g.cr p - 2 ^ j),
                                 own := Function.update g.own j none }
    have e : s.step L p = ⟨m', Function.update s.loc p l'⟩ := by
      simp [ESys.step, estep, hl, ← hl', m']
    rw [e]
    have hV' : ∀ i x, m'.V i = some x → i ≠ j ∧ s.m.V i = some x := fun i x hi => by
      by_cases hij : i = j
      · subst hij; simp [m'] at hi
      · exact ⟨hij, by simpa [m', hij] using hi⟩
    have hO' : ∀ i x, g'.own i = some x → i ≠ j ∧ g.own i = some x := fun i x hi => by
      by_cases hij : i = j
      · subst hij; simp [g'] at hi
      · exact ⟨hij, by simpa [g', hij] using hi⟩
    refine ⟨g', ?_⟩
    constructor
    · intro x
      by_cases hx : x = p
      · subst hx; simpa using hl'wf
      · simpa [hx] using h.wf x
    · intro x
      by_cases hx : x = p
      · subst hx; simp [g', hap, hl'st]
      · simpa [hx] using h.age0 x
    · exact h.ageInj
    · exact h.turnSome
    · exact h.turnNone
    · intro i x hi
      obtain ⟨hij, hi2⟩ := hV' i x hi
      by_cases hx : x = p
      · subst hx; simp only [Function.update_self]
        exact ⟨hlo' i hi2 hij, hl'w ▸ (hhold i hi2).2⟩
      · simpa [hx] using h.hold i x hi2
    · intro i
      by_cases hij : i = j
      · subst hij; simp [g', m']
      · simpa [g', m', hij] using h.ownNone i
    · intro i o ho
      obtain ⟨-, ho2⟩ := hO' i o ho
      by_cases hx : o = p
      · subst hx; have := h.ownW i o ho2
        simp only [Function.update_self, hl'w]; rw [hl] at this; exact this
      · simpa [hx] using h.ownW i o ho2
    · intro x y i hi hpx hxy
      obtain ⟨-, hi2⟩ := hV' i x hi
      have hpx' : i < (s.loc x).passed L := by
        by_cases hx : x = p
        · subst hx; simp only [Function.update_self, hl'p] at hpx; rw [hl]; exact hpx
        · simpa [hx] using hpx
      obtain ⟨h1, h2, h3⟩ := h.c1 x y i hi2 hpx' hxy
      by_cases hy : y = p
      · subst hy; simp only [Function.update_self]
        simp only [hl, ELoc.written, ELoc.passed] at h1 h2
        exact ⟨by omega, by omega, hl'wv i⟩
      · simpa [hy] using ⟨h1, h2, h3⟩
    · intro x y i hi hpx hxy
      obtain ⟨-, hi2⟩ := hO' i x hi
      have hpx' : i < (s.loc x).passed L := by
        by_cases hx : x = p
        · subst hx; simp only [Function.update_self, hl'p] at hpx; rw [hl]; exact hpx
        · simpa [hx] using hpx
      by_cases hy : y = p
      · subst hy; simp only [Function.update_self]; exact hl'wv i
      · simpa [hy] using h.c2 x y i hi2 hpx' hxy
    · have hc := h.cons
      have hfree : free L m' = free L s.m + 2 ^ j := by
        unfold free
        rw [sum_eq_add_sub_of_eq_off (f := fun i => if s.m.V i = none then (2 : ℤ) ^ i else 0)
          (Finset.mem_range.2 hjL) (fun i _ hij => by simp [m', hij])]
        simp [m', hw]
      have hsum := sum_univ_update g.cr p (g.cr p - 2 ^ j)
      simp only [g']
      rw [hsum, hfree]; rw [← hc]; ring
    · intro x
      by_cases hx : x = p
      · subst hx
        rw [req_eq_of_costForm (by simpa using ELoc.costForm_nextClr k b (j + 1))]
        simp only [Function.update_self]
        have h1 := hcost m' (fun i hij => by simp [m', hij])
        have h2 := hrsvp m' g' rfl (fun i hi => (hO' i x hi).2)
        simp only [g', Function.update_self]
        linarith
      · have hcx : g'.cr x = g.cr x := by simp [g', hx]
        rw [hcx]
        refine le_trans (req_le_req (s := s) (g := g) (by simp [hx]) (fun _ => Iff.rfl)
          (cost_mono fun i hi => (hV' i x hi).2) (rsv_mono ?_)) (h.reqLe x)
        rintro i ⟨hi, y, hy, hwvy⟩
        refine ⟨(hO' i x hi).2, y, hy, ?_⟩
        by_cases hyp : y = p
        · subst hyp; simp only [Function.update_self] at hwvy; exact absurd hwvy (hl'wv i)
        · simpa [hyp] using hwvy
    · intro x hx'
      by_cases hx : x = p
      · subst hx; simp [hl'st] at hx'
      · simpa [g', hx] using h.unst x (by simpa [hx] using hx')

/-- Structural part of the invariant after a write `V[k] := p` (line 9). -/
lemma Inv.wv_mk {s : ESys P} {g g' : Ghost P} {p : P} {k : ℕ} (h : Inv L s g)
    (hl : s.loc p = .wv k) (hage : g'.age = g.age)
    (hown : ∀ i x, g'.own i = some x → (i = k ∧ x = p) ∨ g.own i = some x)
    (hownk : g'.own k ≠ none) (hownne : ∀ i, i ≠ k → g'.own i = g.own i)
    (hcons : ∑ x, g'.cr x + free L { s.m with V := Function.update s.m.V k (some p) } =
      Fintype.card P + 2 ^ L - 1)
    (hreq : ∀ x, req L ⟨{ s.m with V := Function.update s.m.V k (some p) },
      Function.update s.loc p (.rturn2 k)⟩ g' x ≤ g'.cr x)
    (hunst : ∀ x, x ≠ p → g'.cr x = g.cr x ∨ (s.loc x).Started) :
    Inv L ⟨{ s.m with V := Function.update s.m.V k (some p) },
      Function.update s.loc p (.rturn2 k)⟩ g' := by
  have hk : k < L := by have := h.wf p; rw [hl] at this; exact this
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  have hap : g.age p ≠ 0 := fun h0 => ((h.age0 p).1 h0) hst
  have hVp : ∀ i, s.m.V i = some p → i < k := fun i hi => by
    simpa [hl, ELoc.written] using (h.hold i p hi).2
  have hOp : ∀ i, g.own i = some p → i < k := fun i hi => by
    simpa [hl, ELoc.written] using h.ownW i p hi
  have hV' : ∀ i x, Function.update s.m.V k (some p) i = some x →
      (i = k ∧ x = p) ∨ (i ≠ k ∧ s.m.V i = some x) := fun i x hi => by
    by_cases hik : i = k
    · subst hik; simp at hi; exact Or.inl ⟨rfl, hi.symm⟩
    · exact Or.inr ⟨hik, by simpa [hik] using hi⟩
  constructor
  · intro x
    by_cases hx : x = p
    · subst hx; simpa [ELoc.WF] using hk
    · simpa [hx] using h.wf x
  · intro x
    by_cases hx : x = p
    · subst hx; simp [hage, hap, ELoc.Started]
    · simpa [hx, hage] using h.age0 x
  · rw [hage]; exact h.ageInj
  · rw [hage]; exact h.turnSome
  · rw [hage]; exact h.turnNone
  · intro i x hi
    rcases hV' i x hi with ⟨rfl, rfl⟩ | ⟨-, hi2⟩
    · simp [ELoc.lo, ELoc.written]
    · by_cases hx : x = p
      · subst hx; have := hVp i hi2; simp [ELoc.lo, ELoc.written]; omega
      · simpa [hx] using h.hold i x hi2
  · intro i
    by_cases hik : i = k
    · subst hik; simp [hownk]
    · rw [hownne i hik]; simpa [hik] using h.ownNone i
  · intro i o ho
    rcases hown i o ho with ⟨rfl, rfl⟩ | ho2
    · simp [ELoc.written]
    · by_cases hx : o = p
      · subst hx; have := hOp i ho2; simp [ELoc.written]; omega
      · simpa [hx] using h.ownW i o ho2
  · intro x y i hi hpx hxy
    rw [hage] at hxy
    rcases hV' i x hi with ⟨rfl, rfl⟩ | ⟨hik, hi2⟩
    · simp [ELoc.passed] at hpx
    · have hpx' : i < (s.loc x).passed L := by
        by_cases hx : x = p
        · subst hx; simpa [hl, ELoc.passed] using hpx
        · simpa [hx] using hpx
      obtain ⟨h1, h2, h3⟩ := h.c1 x y i hi2 hpx' hxy
      by_cases hy : y = p
      · subst hy
        simp only [hl, ELoc.written, ELoc.passed, ne_eq, ELoc.wv.injEq] at h1 h2 h3
        simp [ELoc.written, ELoc.passed]; omega
      · simpa [hy] using ⟨h1, h2, h3⟩
  · intro x y i hi hpx hxy
    rw [hage] at hxy
    rcases hown i x hi with ⟨rfl, rfl⟩ | hi2
    · simp [ELoc.passed] at hpx
    · have hpx' : i < (s.loc x).passed L := by
        by_cases hx : x = p
        · subst hx; simpa [hl, ELoc.passed] using hpx
        · simpa [hx] using hpx
      by_cases hy : y = p
      · subst hy; simp
      · simpa [hy] using h.c2 x y i hi2 hpx' hxy
  · exact hcons
  · exact hreq
  · intro x hx'
    by_cases hx : x = p
    · subst hx; simp [ELoc.Started] at hx'
    · have hx'' : ¬ (s.loc x).Started := by simpa [hx] using hx'
      rcases hunst x hx with e | e
      · rw [e]; exact h.unst x hx''
      · exact absurd e hx''

lemma sum_ite_le_single {L k : ℕ} {c : ℕ → Prop} [DecidablePred c] (hk : k < L)
    (hc : ∀ j, c j → j = k) : (∑ j ∈ range L, if c j then (2 : ℤ) ^ j else 0) ≤ 2 ^ k :=
  calc (∑ j ∈ range L, if c j then (2 : ℤ) ^ j else 0)
      ≤ ∑ j ∈ range L, if j = k then (2 : ℤ) ^ j else 0 :=
        sum_ite_le_sum_ite (fun j => by positivity) fun j _ hj => hc j hj
    _ = 2 ^ k := by rw [Finset.sum_ite_eq']; simp [hk]

lemma Inv.step_wv {s : ESys P} {g : Ghost P} {p : P} {k : ℕ} (h : Inv L s g)
    (hl : s.loc p = .wv k) : ∃ g', Inv L (s.step L p) g' := by
  have hk : k < L := by have := h.wf p; rw [hl] at this; exact this
  have hcr := h.cr_ge_of_req (Or.inr (Or.inr (Or.inr hl)))
  have hst : (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  have hap : g.age p ≠ 0 := fun h0 => ((h.age0 p).1 h0) hst
  have hOp : ∀ i, g.own i = some p → i < k := fun i hi => by
    simpa [hl, ELoc.written] using h.ownW i p hi
  set m' : EMem P := { s.m with V := Function.update s.m.V k (some p) } with hm'
  set s' : ESys P := ⟨m', Function.update s.loc p (.rturn2 k)⟩ with hs'
  have e : s.step L p = s' := by simp [ESys.step, estep, hl, s', m']
  rw [e]
  have hloc' : ∀ x, x ≠ p → s'.loc x = s.loc x := fun x hx => by simp [s', hx]
  have hV'x : ∀ i x, x ≠ p → m'.V i = some x → s.m.V i = some x := fun i x hx hi => by
    by_cases hik : i = k
    · subst hik; simp [m'] at hi; exact absurd hi.symm hx
    · simpa [m', hik] using hi
  -- other processes: their requirement can only decrease
  have hothers : ∀ g' : Ghost P, g'.age = g.age →
      (∀ i x, x ≠ p → g'.own i = some x → g.own i = some x) →
      ∀ x, x ≠ p → req L s' g' x ≤ req L s g x := by
    intro g' ha ho x hx
    refine req_le_req (hloc' x hx) (fun _ => Iff.rfl) (cost_mono fun i hi => hV'x i x hx hi)
      (rsv_mono ?_)
    rintro i ⟨hi, y, hy, hwvy⟩
    refine ⟨ho i x hx hi, y, ha ▸ hy, ?_⟩
    by_cases hyp : y = p
    · subst hyp; simp [s'] at hwvy
    · rwa [hloc' y hyp] at hwvy
  -- a younger process about to overwrite `V[k]`
  set Y := ∃ y, g.age p < g.age y ∧ s.loc y = .wv k with hY
  -- the new `rsv` of `p`
  have hrsvp : ∀ g' : Ghost P, g'.age = g.age → (∀ i, i ≠ k → g'.own i = g.own i) →
      rsv L s' g' p ≤ (if Y ∧ g'.own k = some p then 2 ^ k else 0) := by
    intro g' ha ho
    split_ifs with hYo
    · refine sum_ite_le_single hk fun j hj => ?_
      by_contra hjk
      obtain ⟨hj, y, hy, hwvy⟩ := hj
      rw [ho j hjk] at hj
      have hyp : y ≠ p := by rintro rfl; rw [ha] at hy; exact lt_irrefl _ hy
      rw [hloc' y hyp] at hwvy
      rw [ha] at hy
      exact h.c2 p y j hj (by rw [hl]; exact hOp j hj) hy hwvy
    · refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_)
      split_ifs with hj
      · exfalso
        obtain ⟨hj, y, hy, hwvy⟩ := hj
        have hyp : y ≠ p := by rintro rfl; rw [ha] at hy; exact lt_irrefl _ hy
        rw [hloc' y hyp] at hwvy
        rw [ha] at hy
        by_cases hjk : j = k
        · subst hjk; exact hYo ⟨⟨y, hy, hwvy⟩, hj⟩
        · rw [ho j hjk] at hj
          exact h.c2 p y j hj (by rw [hl]; exact hOp j hj) hy hwvy
      · rfl
  -- the new `cost` of `p`
  have hcostp : cost L m' p (.rturn2 k) ≤ 2 ^ (k + 1) - 1 := by
    simpa [ELoc.written] using cost_le (L := L) m' p (.rturn2 k)
  have hcostp1 : (∃ y, g.age p < g.age y ∧ (k < (s.loc y).written L ∨ k ≤ (s.loc y).passed L)) →
      cost L m' p (.rturn2 k) ≤ 2 ^ k := by
    rintro ⟨y, hy, hwy⟩
    refine cost_le_single hk fun j _ hj2 hj3 => ?_
    simp only [ELoc.written, ELoc.clwAt, or_false] at hj2 hj3
    by_contra hjk
    have hjk' : j < k := by omega
    have hj : s.m.V j = some p := by simpa [m', hjk] using hj3
    have := h.c1 p y j hj (by rw [hl]; exact hjk') hy
    omega
  have hreq_p : ∀ g' : Ghost P, g'.age = g.age → (∀ i, i ≠ k → g'.own i = g.own i) →
      req L s' g' p = if s.m.turn = some p then 2 ^ (k + 1)
        else cost L m' p (.rturn2 k) + rsv L s' g' p := by
    intro g' _ _
    have : m'.turn = s.m.turn := rfl
    simp [req, s', this]
  by_cases hv : s.m.V k = none
  · -- (A) `V[k]` was `0`: `p` takes its `2^k` credits
    have hok : g.own k = none := (h.ownNone k).2 hv
    let g' : Ghost P := { g with cr := Function.update g.cr p (g.cr p + 2 ^ k),
                                 own := Function.update g.own k (some p) }
    have hne : ∀ i, i ≠ k → g'.own i = g.own i := fun i hi => by simp [g', hi]
    refine ⟨g', h.wv_mk hl rfl ?_ (by simp [g']) hne ?_ ?_ ?_⟩
    · intro i x hi
      by_cases hik : i = k
      · subst hik; simp [g'] at hi; exact Or.inl ⟨rfl, hi.symm⟩
      · exact Or.inr (by simpa [g', hik] using hi)
    · have hfree : free L m' = free L s.m - 2 ^ k := by
        unfold free
        rw [sum_eq_add_sub_of_eq_off (f := fun i => if s.m.V i = none then (2 : ℤ) ^ i else 0)
          (Finset.mem_range.2 hk) (fun i _ hij => by simp [m', hij])]
        simp [m', hv]; ring
      rw [hfree, sum_univ_update, ← h.cons]; ring
    · intro x
      by_cases hx : x = p
      · subst hx
        rw [hreq_p g' rfl hne]
        have hcr' : g'.cr x = g.cr x + 2 ^ k := by simp [g']
        rw [hcr']
        have hr := hrsvp g' rfl hne
        have hpow : (2 : ℤ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        by_cases h1 : s.m.turn = some x
        · rw [if_pos h1]; linarith
        · rw [if_neg h1]
          by_cases h2 : Y ∧ g'.own k = some x
          · rw [if_pos h2] at hr
            obtain ⟨y, hy, hwy⟩ := hY ▸ h2.1
            have := hcostp1 ⟨y, hy, Or.inr (by rw [hwy]; simp [ELoc.passed])⟩
            linarith
          · rw [if_neg h2] at hr; linarith
      · have hcx : g'.cr x = g.cr x := by simp [g', hx]
        rw [hcx]
        refine le_trans (hothers g' rfl (fun i y hy hi => ?_) x hx) (h.reqLe x)
        by_cases hik : i = k
        · subst hik; simp [g'] at hi; exact absurd hi.symm hy
        · simpa [g', hik] using hi
    · intro x hx; left; simp [g', hx]
  · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hv
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (fun h' => hv ((h.ownNone k).1 h'))
    have hwo : k < (s.loc o).written L := h.ownW k o ho
    have hop : o ≠ p := by rintro rfl; rw [hl] at hwo; simp [ELoc.written] at hwo
    have hsto : (s.loc o).Started := by
      refine ⟨fun h' => ?_, fun h' => ?_⟩ <;> rw [h'] at hwo <;> simp [ELoc.written] at hwo
    have hao : g.age o ≠ 0 := fun h0 => ((h.age0 o).1 h0) hsto
    by_cases hage : g.age o < g.age p
    · -- (B) transfer of `2^k` credits from the owner `o` to `p`
      have hpo : ¬ k < (s.loc o).passed L := fun hkp => h.c2 o p k ho hkp hage hl
      have hform : (s.loc o).CostForm ∨ ∃ k', s.loc o = .rturn2 k' ∧ s.m.turn ≠ some o := by
        have hwfo := h.wf o
        cases hlo : s.loc o with
        | rturn2 k' =>
          right; refine ⟨k', rfl, fun ht => ?_⟩
          exact absurd ((h.turnSome o ht).2 p) (not_le.2 hage)
        | clr a b c => left; exact Or.inl ⟨_, _, _, rfl⟩
        | clw a b c => left; exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
        | out r a w c =>
          cases r
          · left; exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
          · rw [hlo] at hwfo hpo; simp [ELoc.WF, ELoc.passed] at hwfo hpo; omega
        | _ => rw [hlo] at hwo hpo hwfo hsto <;>
            simp [ELoc.written, ELoc.passed, ELoc.WF, ELoc.Started] at hwo hpo hwfo hsto <;> omega
      let g' : Ghost P :=
        { g with cr := Function.update (Function.update g.cr o (g.cr o - 2 ^ k)) p (g.cr p + 2 ^ k),
                 own := Function.update g.own k (some p) }
      have hne : ∀ i, i ≠ k → g'.own i = g.own i := fun i hi => by simp [g', hi]
      refine ⟨g', h.wv_mk hl rfl ?_ (by simp [g']) hne ?_ ?_ ?_⟩
      · intro i x hi
        by_cases hik : i = k
        · subst hik; simp [g'] at hi; exact Or.inl ⟨rfl, hi.symm⟩
        · exact Or.inr (by simpa [g', hik] using hi)
      · have hfree : free L m' = free L s.m := by
          unfold free
          rw [sum_eq_add_sub_of_eq_off (f := fun i => if s.m.V i = none then (2 : ℤ) ^ i else 0)
            (Finset.mem_range.2 hk) (fun i _ hij => by simp [m', hij])]
          simp [m', hw]
        rw [hfree]
        simp only [g']
        rw [sum_univ_update, sum_univ_update, ← h.cons]
        simp [Function.update_of_ne hop.symm]
      · intro x
        by_cases hx : x = p
        · subst hx
          rw [hreq_p g' rfl hne]
          have hcr' : g'.cr x = g.cr x + 2 ^ k := by simp [g']
          rw [hcr']
          have hr := hrsvp g' rfl hne
          have hpow : (2 : ℤ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          by_cases h1 : s.m.turn = some x
          · rw [if_pos h1]; linarith
          · rw [if_neg h1]
            by_cases h2 : Y ∧ g'.own k = some x
            · rw [if_pos h2] at hr
              obtain ⟨y, hy, hwy⟩ := hY ▸ h2.1
              have := hcostp1 ⟨y, hy, Or.inr (by rw [hwy]; simp [ELoc.passed])⟩
              linarith
            · rw [if_neg h2] at hr; linarith
        · by_cases hxo : x = o
          · subst hxo
            have hcr' : g'.cr x = g.cr x - 2 ^ k := by simp [g', hx]
            rw [hcr']
            have hr := h.reqLe x
            rw [req_eq_costRsv hform] at hr
            have hform' : (s'.loc x).CostForm ∨ ∃ k', s'.loc x = .rturn2 k' ∧ s'.m.turn ≠ some x :=
              by rw [hloc' x hx]; exact hform
            rw [req_eq_costRsv hform', hloc' x hx]
            have h1 := cost_mono (L := L) (l := s.loc x) (fun i hi => hV'x i x hx hi)
            have h2 : rsv L s' g' x + 2 ^ k ≤ rsv L s g x := by
              unfold rsv
              refine sum_add_le_of (Finset.mem_range.2 hk) ?_ fun i _ hik => ?_
              · rw [if_neg (by simp [g', Ne.symm hx]), if_pos ⟨ho, p, hage, hl⟩]; simp
              · by_cases hc : g'.own i = some x ∧ ∃ y, g'.age x < g'.age y ∧ s'.loc y = .wv i
                · obtain ⟨hi1, y, hy, hwvy⟩ := hc
                  rw [if_pos ⟨hi1, y, hy, hwvy⟩, if_pos]
                  refine ⟨by simpa [g', hik] using hi1, y, hy, ?_⟩
                  by_cases hyp : y = p
                  · subst hyp; simp [s'] at hwvy
                  · rwa [hloc' y hyp] at hwvy
                · rw [if_neg hc]; split_ifs <;> positivity
            have : cost L m' x (s.loc x) = cost L s'.m x (s.loc x) := rfl
            linarith
          · have hcx : g'.cr x = g.cr x := by simp [g', hx, hxo]
            rw [hcx]
            refine le_trans (hothers g' rfl (fun i y hy hi => ?_) x hx) (h.reqLe x)
            by_cases hik : i = k
            · subst hik; simp [g'] at hi; exact absurd hi.symm hy
            · simpa [g', hik] using hi
      · intro x hx
        by_cases hxo : x = o
        · subst hxo; right; exact hsto
        · left; simp [g', hx, hxo]
    · -- (C) `p` is older than the owner: no credits move
      have hpo : g.age p < g.age o := by
        rcases lt_trichotomy (g.age p) (g.age o) with h1 | h1 | h1
        · exact h1
        · exact absurd (h.ageInj p o h1 hap) hop.symm
        · exact absurd h1 hage
      have hne : ∀ i, i ≠ k → g.own i = g.own i := fun _ _ => rfl
      refine ⟨g, h.wv_mk hl rfl (fun i x hi => Or.inr hi) (by rw [ho]; simp) hne ?_ ?_ ?_⟩
      · have hfree : free L m' = free L s.m := by
          unfold free
          rw [sum_eq_add_sub_of_eq_off (f := fun i => if s.m.V i = none then (2 : ℤ) ^ i else 0)
            (Finset.mem_range.2 hk) (fun i _ hij => by simp [m', hij])]
          simp [m', hw]
        rw [hfree]; exact h.cons
      · intro x
        by_cases hx : x = p
        · subst hx
          rw [hreq_p g rfl hne]
          have hnt : s.m.turn ≠ some x := fun ht =>
            absurd ((h.turnSome x ht).2 o) (not_le.2 hpo)
          rw [if_neg hnt]
          have hr := hrsvp g rfl hne
          rw [if_neg (fun h' => hop (Option.some.inj (h'.2.symm.trans ho)).symm)] at hr
          have := hcostp1 ⟨o, hpo, Or.inl hwo⟩
          linarith
        · exact le_trans (hothers g rfl (fun _ _ _ hi => hi) x hx) (h.reqLe x)
      · intro x _; left; rfl

lemma Inv.step {s : ESys P} {g : Ghost P} (h : Inv L s g) (p : P) :
    ∃ g', Inv L (s.step L p) g' := by
  cases hl : s.loc p with
  | idle =>
    refine ⟨g, ?_⟩
    have : s.step L p = s := by
      cases s with
      | mk m loc =>
        simp only at hl
        simp [ESys.step, estep, hl, Function.update_eq_self_iff]
    rw [this]; exact h
  | out r a w c =>
    refine ⟨g, ?_⟩
    have : s.step L p = s := by
      cases s with
      | mk m loc =>
        simp only at hl
        simp [ESys.step, estep, hl, Function.update_eq_self_iff]
    rw [this]; exact h
  | start => exact h.step_start hl
  | rdone k => exact h.step_rdone hl
  | rturn k => exact h.step_rturn hl
  | rv k => exact h.step_rv hl
  | wv k => exact h.step_wv hl
  | rturn2 k => exact h.step_rturn2 hl
  | clr k b j => exact h.step_clr hl
  | clw k b j => exact h.step_clw hl
  | wdone => exact h.step_wdone hl

lemma Inv.invoke {s : ESys P} {g : Ghost P} (h : Inv L s g) (p : P) :
    Inv L (s.invoke p) g := by
  unfold ESys.invoke
  split_ifs with hl
  swap; · exact h
  have hns : ¬ (s.loc p).Started := by rw [hl]; simp [ELoc.Started]
  have hap : g.age p = 0 := (h.age0 p).2 hns
  have hVp : ∀ j, s.m.V j ≠ some p := fun j hj => by
    have := (h.hold j p hj).2; simp [hl, ELoc.written] at this
  have hOp : ∀ j, g.own j ≠ some p := fun j hj => by
    have := h.ownW j p hj; simp [hl, ELoc.written] at this
  constructor
  · intro x; by_cases hx : x = p
    · subst hx; simp [ELoc.WF]
    · simpa [hx] using h.wf x
  · intro x; by_cases hx : x = p
    · subst hx; simp [hap, ELoc.Started]
    · simpa [hx] using h.age0 x
  · exact h.ageInj
  · exact h.turnSome
  · exact h.turnNone
  · intro j x hj
    have hx : x ≠ p := by rintro rfl; exact hVp j hj
    simpa [hx] using h.hold j x hj
  · exact h.ownNone
  · intro j o ho
    have hx : o ≠ p := by rintro rfl; exact hOp j ho
    simpa [hx] using h.ownW j o ho
  · intro x y j hj hpx hxy
    have hx : x ≠ p := by rintro rfl; exact hVp j hj
    by_cases hy : y = p
    · subst hy; rw [hap] at hxy; omega
    · simpa [hx, hy] using h.c1 x y j hj (by simpa [hx] using hpx) hxy
  · intro x y k hk hpx hxy
    have hx : x ≠ p := by rintro rfl; exact hOp k hk
    by_cases hy : y = p
    · subst hy; rw [hap] at hxy; omega
    · simpa [hx, hy] using h.c2 x y k hk (by simpa [hx] using hpx) hxy
  · exact h.cons
  · intro x; by_cases hx : x = p
    · subst hx; simp [req, h.unst x hns]
    · refine le_trans (req_le_req (s := s) (g := g) (by simp [hx]) (fun _ => Iff.rfl) le_rfl
        (rsv_mono ?_)) (h.reqLe x)
      rintro j ⟨hj, y, hy, hwvy⟩
      by_cases hyp : y = p
      · subst hyp; simp at hwvy
      · exact ⟨hj, y, hy, by simpa [hyp] using hwvy⟩
  · intro x hx'
    by_cases hx : x = p
    · subst hx; exact h.unst x hns
    · exact h.unst x (by simpa [hx] using hx')

/-- The initial ghost state: nobody started, one credit per process, no owners. -/
def Ghost.init (P : Type) : Ghost P := ⟨fun _ => 0, fun _ => 1, fun _ => none⟩

lemma Inv.init : Inv L (ESys.init P) (Ghost.init P) := by
  constructor
  · intro x; simp [ESys.init, ELoc.WF]
  · intro x; simp [ESys.init, Ghost.init, ELoc.Started]
  · intro x y _ h; simp [Ghost.init] at h
  · intro x h; simp [ESys.init, EMem.init] at h
  · intro _ y; rfl
  · intro j x h; simp [ESys.init, EMem.init] at h
  · intro j; simp [ESys.init, EMem.init, Ghost.init]
  · intro j o h; simp [Ghost.init] at h
  · intro x y j h; simp [ESys.init, EMem.init] at h
  · intro x y k h; simp [Ghost.init] at h
  · simp only [Ghost.init, free, ESys.init, EMem.init, ite_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, sum_pow_two_range]
    ring
  · intro x; simp [req, ESys.init, Ghost.init]
  · intro x _; rfl

/-- Every reachable state satisfies the invariant for some ghost state. -/
theorem EReach.inv {s : ESys P} (hs : EReach L s) : ∃ g, Inv L s g := by
  induction hs with
  | init => exact ⟨_, Inv.init⟩
  | step p _ ih => obtain ⟨g, hg⟩ := ih; exact hg.step p
  | invoke p _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g, hg.invoke p⟩

lemma req_elected {s : ESys P} {g : Ghost P} {x : P} (hx : (s.loc x).Elected) :
    req L s g x = 2 ^ L := by
  unfold req
  cases h : s.loc x with
  | wdone => rfl
  | out r a w c => cases r <;> simp_all [ELoc.Elected]
  | _ => simp [h, ELoc.Elected] at hx

/-- The core of **Theorem 2.4 (safety)**: if `n ≤ 2^L`, two distinct processes are never both
elected. -/
theorem Inv.elected_unique {s : ESys P} {g : Ghost P} (h : Inv L s g)
    (hn : Fintype.card P ≤ 2 ^ L) {x y : P} (hx : (s.loc x).Elected) (hy : (s.loc y).Elected) :
    x = y := by
  by_contra hxy
  have h1 : (2 : ℤ) ^ L ≤ g.cr x := (req_elected hx).symm.le.trans (h.reqLe x)
  have h2 : (2 : ℤ) ^ L ≤ g.cr y := (req_elected hy).symm.le.trans (h.reqLe y)
  have hnn : ∀ z, 0 ≤ g.cr z := fun z => (req_nonneg s g z).trans (h.reqLe z)
  have hsum : g.cr x + g.cr y ≤ ∑ z, g.cr z := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := g.cr) (Finset.subset_univ {x, y})
      (fun z _ _ => hnn z)
    rwa [Finset.sum_pair hxy] at this
  have hfree : 0 ≤ free L s.m := sum_ite_nonneg fun j => by positivity
  have hc := h.cons
  have hn' : (Fintype.card P : ℤ) ≤ 2 ^ L := by exact_mod_cast hn
  linarith

/-- **Theorem 2.4 (safety).** With `L` levels and at most `2^L` processes (the paper takes
`L = ⌈log₂ n⌉`), in every reachable state at most one process is elected (is at line 14 or has
returned `1`). -/
theorem EReach.elected_unique {s : ESys P} (hs : EReach L s) (hn : Fintype.card P ≤ 2 ^ L)
    {x y : P} (hx : (s.loc x).Elected) (hy : (s.loc y).Elected) : x = y := by
  obtain ⟨g, hg⟩ := hs.inv
  exact hg.elected_unique hn hx hy

end Steps

end Podc.CloserLookFT
