import Papers.PODC2011.RobustAtomicStorage.Model

/-!
# Non-vacuity of the round model: an atomic protocol with one object and `t = 0`

The main theorems of this folder say `¬ P.Atomic t bot` under hypotheses such as `S ≤ 4t`. To
check that `Proto.Atomic` is not an unsatisfiable predicate of the model of `Model.lean`, we exhibit
an atomic protocol for parameters outside those bounds: one object (`Obj := Unit`, so `S = 1`),
`t = 0`, any readers, any values.

The protocol `proto bot N`: messages are `Option V` (the writer sends `some v`, readers send
`none`); the object replies with its current value (the last `some v` it processed, or `bot`);
writes take one round and reads `N` rounds (any `N`; for `N = 0` reads never return); a read
returns the value replied in its first round. Main result: `atomic_one_object`.

The proof is an invariant (`Inv`) of the reachable (configuration, history) pairs relating the
history to the object's log; it contains the four properties of `AtomicHist`.
-/

namespace Podc.RobustAtomicStorage.Sanity

open Podc.RobustAtomicStorage

variable {Rd V : Type}

/-- The value stored by the object: the last `some v` in its log, `bot` if none. -/
def lastVal (bot : V) (log : List (Cl Rd × Option V)) : V :=
  log.foldl (fun acc p => p.2.getD acc) bot

/-- The value of the first reply of the first round, if any. -/
def firstRep (views : List (View Unit V)) : Option V :=
  (views.head?.bind List.head?).map Prod.snd

/-- The one-object protocol: one-round writes, `N`-round reads returning the value replied in the
first round. -/
def proto (bot : V) (N : ℕ) : Proto Unit Rd V (Option V) V where
  K := 1
  N := N
  reply _ log _ _ := lastVal bot log
  wMsg v _ _ := some v
  rMsg _ _ _ := none
  rRet _ views := (firstRep views).getD bot

/-! ### Lemmas on `Before` -/

lemma before_mem {h : List (HEv Rd V)} {a b : HEv Rd V} (hb : Before h a b) : a ∈ h ∧ b ∈ h := by
  obtain ⟨i, j, -, hi, hj⟩ := hb
  exact ⟨List.mem_of_getElem? hi, List.mem_of_getElem? hj⟩

lemma before_snoc {h : List (HEv Rd V)} {e a b : HEv Rd V} (hb : Before (h ++ [e]) a b) :
    Before h a b ∨ (a ∈ h ∧ b = e) := by
  obtain ⟨i, j, hij, hi, hj⟩ := hb
  rcases lt_trichotomy j h.length with hj' | hj' | hj'
  · left
    refine ⟨i, j, hij, ?_, ?_⟩
    · rwa [List.getElem?_append_left (by omega)] at hi
    · rwa [List.getElem?_append_left hj'] at hj
  · right
    subst hj'
    rw [List.getElem?_append_left hij] at hi
    simp at hj
    exact ⟨List.mem_of_getElem? hi, hj.symm⟩
  · rw [List.getElem?_eq_none (by simp; omega)] at hj
    simp at hj

lemma before_snoc_ne {h : List (HEv Rd V)} {e a b : HEv Rd V} (hb : Before (h ++ [e]) a b)
    (hne : b ≠ e) : Before h a b := by
  rcases before_snoc hb with h1 | ⟨-, h2⟩
  · exact h1
  · exact absurd h2 hne

/-! ### Preservation of atomicity by appending one event -/

lemma atomic_snoc_retW {bot : V} {h : List (HEv Rd V)} (hA : AtomicHist bot h) :
    AtomicHist bot (h ++ [.retW]) := by
  constructor
  · intro j x hx
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx
    rcases hA.ret_val j x hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_append_left _ h1)
  · intro j x v hx hv hb
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx hv
    exact hA.after_write j x v hx hv (before_snoc_ne hb (by simp))
  · intro j v hv hx hw hb
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx hw
    exact hA.not_before_write j v hv hx hw (before_snoc_ne hb (by simp))
  · intro j j' v x hv hx hw hb hx'
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx hw hx'
    exact hA.after_read j j' v x hv hx hw (before_snoc_ne hb (by simp)) hx'

lemma atomic_snoc_invW {bot : V} {h : List (HEv Rd V)} (hA : AtomicHist bot h) (w : V)
    (hno : ∀ v, HEv.invW v ∉ h) (hnoW : HEv.retW ∉ h) :
    AtomicHist bot (h ++ [.invW w]) := by
  have key : ∀ j v, v ≠ bot → HEv.retR j v ∉ h := by
    intro j v hv hx
    rcases hA.ret_val j v hx with h1 | h1
    · exact hv h1
    · exact hno v h1
  constructor
  · intro j x hx
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx
    rcases hA.ret_val j x hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_append_left _ h1)
  · intro j x v hx hv hb
    exact absurd (before_mem (before_snoc_ne hb (by simp))).1 hnoW
  · intro j v hv hx _ _
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx
    exact key j v hv hx
  · intro j j' v x hv hx _ _ _
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx
    exact (key j v hv hx).elim

lemma atomic_snoc_invR {bot : V} {h : List (HEv Rd V)} (hA : AtomicHist bot h) (j₀ : Rd)
    (hno : ∀ x, HEv.retR j₀ x ∉ h) : AtomicHist bot (h ++ [.invR j₀]) := by
  constructor
  · intro j x hx
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx
    rcases hA.ret_val j x hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_append_left _ h1)
  · intro j x v hx hv hb
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx hv
    rcases before_snoc hb with h1 | ⟨-, h2⟩
    · exact hA.after_write j x v hx hv h1
    · cases h2
      exact (hno x hx).elim
  · intro j v hv hx hw hb
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx hw
    exact hA.not_before_write j v hv hx hw (before_snoc_ne hb (by simp))
  · intro j j' v x hv hx hw hb hx'
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hx hw hx'
    rcases before_snoc hb with h1 | ⟨-, h2⟩
    · exact hA.after_read j j' v x hv hx hw h1 hx'
    · cases h2
      exact (hno x hx').elim

lemma atomic_snoc_retR {bot : V} {h : List (HEv Rd V)} (hA : AtomicHist bot h) (j₀ : Rd) (x₀ : V)
    (h1 : x₀ = bot ∨ HEv.invW x₀ ∈ h)
    (h2 : ∀ v, HEv.invW v ∈ h → Before h .retW (.invR j₀) → x₀ = v)
    (h4 : ∀ j v, v ≠ bot → Before h (.retR j v) (.invR j₀) → x₀ = v) :
    AtomicHist bot (h ++ [.retR j₀ x₀]) := by
  constructor
  · intro j x hx
    simp only [List.mem_append, List.mem_singleton, HEv.retR.injEq] at hx
    rcases hx with hx | ⟨rfl, rfl⟩
    · rcases hA.ret_val j x hx with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_append_left _ h1)
    · rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_append_left _ h1)
  · intro j x v hx hv hb
    simp only [List.mem_append, List.mem_singleton, HEv.retR.injEq, reduceCtorEq, or_false]
      at hx hv
    have hb' := before_snoc_ne hb (by simp)
    rcases hx with hx | ⟨rfl, rfl⟩
    · exact hA.after_write j x v hx hv hb'
    · exact h2 v hv hb'
  · intro j v hv hx hw hb
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hw
    have hb' := before_snoc_ne hb (by simp)
    exact hA.not_before_write j v hv (before_mem hb').1 hw hb'
  · intro j j' v x hv hx hw hb hx'
    simp only [List.mem_append, List.mem_singleton, HEv.retR.injEq, reduceCtorEq, or_false]
      at hw hx'
    have hb' := before_snoc_ne hb (by simp)
    rcases hx' with hx' | ⟨rfl, rfl⟩
    · exact hA.after_read j j' v x hv (before_mem hb').1 hw hb' hx'
    · exact h4 j v hv hb'

/-! ### The invariant -/

lemma lastVal_snoc (bot : V) (l : List (Cl Rd × Option V)) (p : Cl Rd × Option V) :
    lastVal bot (l ++ [p]) = p.2.getD (lastVal bot l) := by
  simp [lastVal]

lemma firstRep_nxt (p : List (View Unit V)) (q : View Unit V) :
    firstRep (p ++ [q] ++ [[]]) = firstRep (p ++ [q]) := by
  cases p <;> simp [firstRep]

lemma firstRep_snoc {p : List (View Unit V)} {q : View Unit V} {x : V}
    (h : firstRep (p ++ [q]) = some x) (a : Unit × V) : firstRep (p ++ [q ++ [a]]) = some x := by
  cases p with
  | nil => cases q <;> simp_all [firstRep]
  | cons _ _ => simpa [firstRep] using h

lemma not_before_nil {a b : HEv Rd V} : ¬ Before [] a b := by
  rintro ⟨i, j, -, hi, -⟩
  simp at hi


/-- The value replied to the first round of client `c` (if any). -/
def fr (C : Cfg Unit Rd V (Option V) V) (c : Cl Rd) : Option V :=
  firstRep (C.past c ++ [C.cur c])

/-- The invariant of reachable (configuration, history) pairs. -/
structure Inv (bot : V) (C : Cfg Unit Rd V (Option V) V) (h : List (HEv Rd V)) : Prop where
  prc_le : ∀ c, C.prc () c ≤ C.rnd c
  fresh : ∀ c, C.prc () c = 0 → C.past c = [] ∧ C.cur c = []
  logv : lastVal bot (C.log ()) = if 1 ≤ C.prc () .w then C.wv else bot
  rep : ∀ c, 1 ≤ C.prc () c → ∃ x, fr C c = some x ∧ (x = bot ∨ (1 ≤ C.prc () .w ∧ x = C.wv))
  invW_iff : ∀ v, HEv.invW v ∈ h ↔ (1 ≤ C.rnd .w ∧ v = C.wv)
  retW_mem : HEv.retW ∈ h → 1 ≤ C.prc () .w
  retR_mem : ∀ j x, HEv.retR j x ∈ h → 1 ≤ C.prc () (.r j) ∧ fr C (.r j) = some x
  afterW : ∀ j, Before h .retW (.invR j) → 1 ≤ C.prc () (.r j) → fr C (.r j) = some C.wv
  afterR : ∀ j j' v, v ≠ bot → Before h (.retR j v) (.invR j') → 1 ≤ C.prc () (.r j') →
    fr C (.r j') = some v
  atomic : AtomicHist bot h

lemma inv_init (bot : V) : Inv bot (Cfg.init bot : Cfg Unit Rd V (Option V) V) [] where
  prc_le _ := by simp [Cfg.init]
  fresh _ _ := by simp [Cfg.init]
  logv := by simp [Cfg.init, lastVal]
  rep _ h := by simp [Cfg.init] at h
  invW_iff _ := by simp [Cfg.init]
  retW_mem h := by simp at h
  retR_mem _ _ h := by simp at h
  afterW _ h := (not_before_nil h).elim
  afterR _ _ _ _ h := (not_before_nil h).elim
  atomic := ⟨by simp, by simp, by simp, by simp⟩

variable [DecidableEq Rd] {bot : V} {C : Cfg Unit Rd V (Option V) V} {h : List (HEv Rd V)}

lemma Inv.invW (I : Inv bot C h) (h0 : C.rnd .w = 0) (v : V) :
    Inv bot { C with rnd := Function.update C.rnd .w 1, wv := v } (h ++ [.invW v]) := by
  have hpw : C.prc () .w = 0 := by have := I.prc_le .w; omega
  have hnoW : ∀ v', HEv.invW v' ∉ h := fun v' hm => by simpa [h0] using (I.invW_iff v').1 hm
  have hnoR : HEv.retW ∉ h := fun hm => by simpa [hpw] using I.retW_mem hm
  exact {
    prc_le := fun c => by
      by_cases hc : c = .w
      · subst hc; simp [hpw]
      · simpa [Function.update_of_ne hc] using I.prc_le c
    fresh := I.fresh
    logv := by simpa [hpw] using I.logv
    rep := fun c hc => by
      obtain ⟨x, hx, hx'⟩ := I.rep c hc
      exact ⟨x, hx, by simpa [hpw] using hx'⟩
    invW_iff := fun v' => by
      simp only [List.mem_append, List.mem_singleton, HEv.invW.injEq, Function.update_self,
        le_refl, true_and]
      exact ⟨fun h1 => h1.resolve_left (hnoW v'), Or.inr⟩
    retW_mem := fun hm => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact I.retW_mem hm
    retR_mem := fun j x hm => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact I.retR_mem j x hm
    afterW := fun j hb => (hnoR (before_mem (before_snoc_ne hb (by simp))).1).elim
    afterR := fun j j' v hv hb => I.afterR j j' v hv (before_snoc_ne hb (by simp))
    atomic := atomic_snoc_invW I.atomic v hnoW hnoR }

lemma Inv.invR (I : Inv bot C h) (j₀ : Rd) (h0 : C.rnd (.r j₀) = 0) :
    Inv bot { C with rnd := Function.update C.rnd (.r j₀) 1 } (h ++ [.invR j₀]) := by
  have hp : C.prc () (.r j₀) = 0 := by have := I.prc_le (.r j₀); omega
  have hnoR : ∀ x, HEv.retR j₀ x ∉ h := fun x hm => by simpa [hp] using (I.retR_mem j₀ x hm).1
  exact {
    prc_le := fun c => by
      by_cases hc : c = .r j₀
      · subst hc; simp [hp]
      · simpa [Function.update_of_ne hc] using I.prc_le c
    fresh := I.fresh
    logv := I.logv
    rep := I.rep
    invW_iff := fun v' => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
      rw [Function.update_of_ne (by simp)]
      exact I.invW_iff v'
    retW_mem := fun hm => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact I.retW_mem hm
    retR_mem := fun j x hm => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact I.retR_mem j x hm
    afterW := fun j hb hj => by
      rcases before_snoc hb with h1 | ⟨-, h2⟩
      · exact I.afterW j h1 hj
      · cases h2; simp [hp] at hj
    afterR := fun j j' v hv hb hj => by
      rcases before_snoc hb with h1 | ⟨-, h2⟩
      · exact I.afterR j j' v hv h1 hj
      · cases h2; simp [hp] at hj
    atomic := atomic_snoc_invR I.atomic j₀ hnoR }

lemma Inv.dlv (N : ℕ) (I : Inv bot C h) (c : Cl Rd) (hc : C.prc () c < C.rnd c) :
    Inv bot ((proto bot N).deliver C c ()) h := by
  set C' := (proto bot N).deliver C c ()
  have hprc : ∀ c', C'.prc () c' = if c' = c then C.prc () c + 1 else C.prc () c' := by
    intro c'; simp [C', Proto.deliver, Function.update_apply]
  have hlog : C'.log () = C.log () ++ [(c, (proto bot N).msg C.wv c ((C.past c).take (C.prc () c)) ())] := by
    simp [C', Proto.deliver]
  have hfr : ∀ c', fr C' c' = if c' = c then
      firstRep (C.past c ++ [C.cur c ++ [((), lastVal bot (C.log ()))]]) else fr C c' := by
    intro c'; by_cases h' : c' = c
    · subst h'; simp [C', fr, Proto.deliver, proto]
    · simp [C', fr, Proto.deliver, proto, h']
  have hwv' : C'.wv = C.wv := rfl
  have hmono : ∀ c', C.prc () c' ≤ C'.prc () c' := by
    intro c'; rw [hprc]; split_ifs with h'
    · subst h'; omega
    · exact le_rfl
  have hy : lastVal bot (C.log ()) = bot ∨
      (1 ≤ C'.prc () .w ∧ lastVal bot (C.log ()) = C.wv) := by
    rw [I.logv]; split_ifs with h1
    · exact Or.inr ⟨le_trans h1 (hmono _), rfl⟩
    · exact Or.inl rfl
  have hold : ∀ c', 1 ≤ C.prc () c' → fr C' c' = fr C c' := by
    intro c' h1
    obtain ⟨x, hx, -⟩ := I.rep c' h1
    rw [hfr, hx]
    split_ifs with h'
    · subst h'; exact firstRep_snoc hx _
    · rfl
  have hnew : C.prc () c = 0 → fr C' c = some (lastVal bot (C.log ())) := by
    intro h0
    obtain ⟨hp, hq⟩ := I.fresh c h0
    rw [hfr]
    simp [hp, hq, firstRep]
  have hcase : ∀ c', 1 ≤ C'.prc () c' → 1 ≤ C.prc () c' ∨ (c' = c ∧ C.prc () c = 0) := by
    intro c' h1
    rw [hprc] at h1
    split_ifs at h1 with h'
    · subst h'
      by_cases h0 : C.prc () c' = 0
      · exact Or.inr ⟨rfl, h0⟩
      · left; omega
    · exact Or.inl h1
  have hwv : 1 ≤ C.prc () .w → lastVal bot (C.log ()) = C.wv := by
    intro h1; rw [I.logv]; simp [h1]
  exact {
    prc_le := fun c' => by
      show C'.prc () c' ≤ C.rnd c'
      rw [hprc]; split_ifs with h'
      · subst h'; omega
      · exact I.prc_le c'
    fresh := fun c' h0 => by
      by_cases h' : c' = c
      · rw [hprc] at h0; simp [h'] at h0
      · rw [hprc] at h0; simp only [h', ite_false] at h0
        exact ⟨(I.fresh c' h0).1, by simp [C', Proto.deliver, h', (I.fresh c' h0).2]⟩
    logv := by
      rw [hlog, lastVal_snoc]
      cases c with
      | w => simp [proto, Proto.msg, hprc, hwv']
      | r j => simpa [proto, Proto.msg, hprc, hwv'] using I.logv
    rep := fun c' h1 => by
      rcases hcase c' h1 with h2 | ⟨rfl, h0⟩
      · obtain ⟨x, hx, hx'⟩ := I.rep c' h2
        refine ⟨x, (hold c' h2).trans hx, ?_⟩
        rcases hx' with hx' | ⟨a, b⟩
        · exact Or.inl hx'
        · exact Or.inr ⟨le_trans a (hmono _), b⟩
      · exact ⟨_, hnew h0, hy⟩
    invW_iff := I.invW_iff
    retW_mem := fun hm => le_trans (I.retW_mem hm) (hmono _)
    retR_mem := fun j x hm => by
      obtain ⟨a, b⟩ := I.retR_mem j x hm
      exact ⟨le_trans a (hmono _), (hold _ a).trans b⟩
    afterW := fun j hb h1 => by
      rcases hcase _ h1 with h2 | ⟨hj, h0⟩
      · exact (hold _ h2).trans (I.afterW j hb h2)
      · subst hj
        rw [hnew h0, hwv (I.retW_mem (before_mem hb).1)]
        rfl
    afterR := fun j j' v hv hb h1 => by
      rcases hcase _ h1 with h2 | ⟨hj, h0⟩
      · exact (hold _ h2).trans (I.afterR j j' v hv hb h2)
      · obtain ⟨a, b⟩ := I.retR_mem j v (before_mem hb).1
        obtain ⟨x, hx, hx'⟩ := I.rep _ a
        rw [b] at hx
        cases hx
        obtain ⟨hw1, rfl⟩ := hx'.resolve_left hv
        subst hj
        rw [hnew h0, hwv hw1]
    atomic := I.atomic }

lemma fr_of_nxt {C C' : Cfg Unit Rd V (Option V) V} (c : Cl Rd)
    (hp : C'.past = Function.update C.past c (C.past c ++ [C.cur c]))
    (hc : C'.cur = Function.update C.cur c []) (c' : Cl Rd) : fr C' c' = fr C c' := by
  by_cases h' : c' = c
  · subst h'
    simp only [fr, hp, hc, Function.update_self]
    exact firstRep_nxt _ _
  · simp [fr, hp, hc, h']

omit [DecidableEq Rd] in
lemma prc_eq_of_nResp {c : Cl Rd} (hr : Fintype.card Unit ≤ 0 + C.nResp c) :
    C.prc () c = C.rnd c := by
  by_contra hne
  have : C.nResp c = 0 := by
    simp only [Cfg.nResp, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _; cases x; exact hne
  simp [this] at hr

/-- The last round of the writer terminates. -/
lemma Inv.nxtW (I : Inv bot C h) (hpr : C.prc () .w = C.rnd .w) (h0 : 0 < C.rnd .w) :
    Inv bot { C with
      past := Function.update C.past .w (C.past .w ++ [C.cur .w])
      cur := Function.update C.cur .w []
      done := Function.update C.done .w true } (h ++ [.retW]) := by
  have hfr := fr_of_nxt (C := C) (C' := { C with
      past := Function.update C.past .w (C.past .w ++ [C.cur .w])
      cur := Function.update C.cur .w []
      done := Function.update C.done .w true }) .w rfl rfl
  exact {
    prc_le := I.prc_le
    fresh := fun c' h0' => by
      by_cases h' : c' = .w
      · subst h'; have h2 : C.prc () .w = 0 := h0'; omega
      · simpa [h'] using I.fresh c' h0'
    logv := I.logv
    rep := fun c' h1 => by rw [hfr]; exact I.rep c' h1
    invW_iff := fun v => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
      exact I.invW_iff v
    retW_mem := fun _ => by show 1 ≤ C.prc () .w; omega
    retR_mem := fun j x hm => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      rw [hfr]; exact I.retR_mem j x hm
    afterW := fun j hb hj => by rw [hfr]; exact I.afterW j (before_snoc_ne hb (by simp)) hj
    afterR := fun j j' v hv hb hj => by
      rw [hfr]; exact I.afterR j j' v hv (before_snoc_ne hb (by simp)) hj
    atomic := atomic_snoc_retW I.atomic }

/-- The last round of a read of `j₀` terminates; it returns its first-round value `x`. -/
lemma Inv.nxtR (I : Inv bot C h) (j₀ : Rd) (hpr : C.prc () (.r j₀) = C.rnd (.r j₀))
    (h0 : 0 < C.rnd (.r j₀)) (x : V) (hx : fr C (.r j₀) = some x) :
    Inv bot { C with
      past := Function.update C.past (.r j₀) (C.past (.r j₀) ++ [C.cur (.r j₀)])
      cur := Function.update C.cur (.r j₀) []
      done := Function.update C.done (.r j₀) true } (h ++ [.retR j₀ x]) := by
  have hfr := fr_of_nxt (C := C) (C' := { C with
      past := Function.update C.past (.r j₀) (C.past (.r j₀) ++ [C.cur (.r j₀)])
      cur := Function.update C.cur (.r j₀) []
      done := Function.update C.done (.r j₀) true }) (.r j₀) rfl rfl
  have hp1 : 1 ≤ C.prc () (.r j₀) := by omega
  obtain ⟨x', hx', hxv⟩ := I.rep _ hp1
  rw [hx] at hx'
  cases hx'
  exact {
    prc_le := I.prc_le
    fresh := fun c' h0' => by
      by_cases h' : c' = .r j₀
      · subst h'; have h2 : C.prc () (.r j₀) = 0 := h0'; omega
      · simpa [h'] using I.fresh c' h0'
    logv := I.logv
    rep := fun c' h1 => by rw [hfr]; exact I.rep c' h1
    invW_iff := fun v => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
      exact I.invW_iff v
    retW_mem := fun hm => by
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact I.retW_mem hm
    retR_mem := fun j y hm => by
      simp only [List.mem_append, List.mem_singleton, HEv.retR.injEq] at hm
      rw [hfr]
      rcases hm with hm | ⟨rfl, rfl⟩
      · exact I.retR_mem j y hm
      · exact ⟨hp1, hx⟩
    afterW := fun j hb hj => by rw [hfr]; exact I.afterW j (before_snoc_ne hb (by simp)) hj
    afterR := fun j j' v hv hb hj => by
      rw [hfr]; exact I.afterR j j' v hv (before_snoc_ne hb (by simp)) hj
    atomic := by
      refine atomic_snoc_retR I.atomic j₀ x ?_ ?_ ?_
      · rcases hxv with hxv | ⟨hw, rfl⟩
        · exact Or.inl hxv
        · exact Or.inr ((I.invW_iff _).2 ⟨le_trans hw (I.prc_le _), rfl⟩)
      · intro v hv hb
        have := I.afterW j₀ hb hp1
        rw [hx] at this
        cases this
        exact ((I.invW_iff v).1 hv).2.symm
      · intro j v hv hb
        have := I.afterR j j₀ v hv hb hp1
        rw [hx] at this
        cases this
        rfl }

/-- A non-final round terminates. -/
lemma Inv.nxtMid (I : Inv bot C h) (c : Cl Rd) (hpr : C.prc () c = C.rnd c) (h0 : 0 < C.rnd c) :
    Inv bot { C with
      past := Function.update C.past c (C.past c ++ [C.cur c])
      cur := Function.update C.cur c []
      rnd := Function.update C.rnd c (C.rnd c + 1) } h := by
  have hfr := fr_of_nxt (C := C) (C' := { C with
      past := Function.update C.past c (C.past c ++ [C.cur c])
      cur := Function.update C.cur c []
      rnd := Function.update C.rnd c (C.rnd c + 1) }) c rfl rfl
  exact {
    prc_le := fun c' => by
      by_cases h' : c' = c
      · subst h'; simpa using le_trans (I.prc_le c') (Nat.le_succ _)
      · simpa [h'] using I.prc_le c'
    fresh := fun c' h0' => by
      by_cases h' : c' = c
      · subst h'; have h2 : C.prc () c' = 0 := h0'; omega
      · simpa [h'] using I.fresh c' h0'
    logv := I.logv
    rep := fun c' h1 => by rw [hfr]; exact I.rep c' h1
    invW_iff := fun v => by
      show HEv.invW v ∈ h ↔ (1 ≤ Function.update C.rnd c (C.rnd c + 1) .w ∧ v = C.wv)
      by_cases h' : c = .w
      · subst h'
        simp only [Function.update_self]
        constructor
        · intro hm; exact ⟨by omega, ((I.invW_iff v).1 hm).2⟩
        · rintro ⟨-, hv⟩; exact (I.invW_iff v).2 ⟨h0, hv⟩
      · rw [Function.update_of_ne (Ne.symm h')]; exact I.invW_iff v
    retW_mem := I.retW_mem
    retR_mem := fun j x hm => by rw [hfr]; exact I.retR_mem j x hm
    afterW := fun j hb hj => by rw [hfr]; exact I.afterW j hb hj
    afterR := fun j j' v hv hb hj => by rw [hfr]; exact I.afterR j j' v hv hb hj
    atomic := I.atomic }

variable [DecidableEq V]

/-- The invariant is preserved by every step (with `t = 0` and no malicious object). -/
lemma Inv.step (N : ℕ) (I : Inv bot C h) {e : Ev Unit Rd V (List (Cl Rd × Option V))}
    {C' : Cfg Unit Rd V (Option V) V} {es : List (HEv Rd V)}
    (hs : (proto bot N).step 0 ∅ bot C e = some (C', es)) : Inv bot C' (h ++ es) := by
  cases e with
  | invW v =>
    simp only [Proto.step] at hs
    split_ifs at hs with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact I.invW hc.1 v
  | invR j =>
    simp only [Proto.step] at hs
    split_ifs at hs with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact I.invR j hc
  | dlv c s =>
    cases s
    simp only [Proto.step] at hs
    split_ifs at hs with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simpa using I.dlv N c hc
  | nxt c =>
    simp only [Proto.step] at hs
    split_ifs at hs with hc hfin
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have hpr := prc_eq_of_nResp hc.2.2
      cases c with
      | w => exact I.nxtW hpr hc.1
      | r j =>
        obtain ⟨x, hx, -⟩ := I.rep (.r j) (by omega)
        have hret : (proto bot N).retEv C (.r j) = .retR j x := by
          show HEv.retR j ((fr C (.r j)).getD bot) = _
          rw [hx]; rfl
        rw [hret]
        exact I.nxtR j hpr hc.1 x hx
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simpa using I.nxtMid c (prc_eq_of_nResp hc.2.2) hc.1
  | forge s L => simp [Proto.step] at hs

/-- The invariant holds along every execution. -/
lemma Inv.exec (N : ℕ) (I : Inv bot C h) {σ : List (Ev Unit Rd V (List (Cl Rd × Option V)))}
    {C' : Cfg Unit Rd V (Option V) V} {h' : List (HEv Rd V)}
    (hs : (proto bot N).exec 0 ∅ bot C σ = some (C', h')) : Inv bot C' (h ++ h') := by
  induction σ generalizing C h C' h' with
  | nil =>
    simp only [Proto.exec, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simpa using I
  | cons e σ ih =>
    simp only [Proto.exec] at hs
    obtain ⟨⟨C₁, es⟩, h1, h2⟩ := Option.bind_eq_some_iff.1 hs
    obtain ⟨⟨C₂, h₂⟩, h3, h4⟩ := Option.map_eq_some_iff.1 h2
    simp only [Prod.mk.injEq] at h4
    obtain ⟨rfl, rfl⟩ := h4
    simpa using ih (I.step N h1) h3

/-- **Non-vacuity of `Proto.Atomic`.** With one object (`S = 1`) and `t = 0`, the protocol
`proto bot N` (one-round writes, `N`-round reads returning the value replied in the first round)
is an atomic register implementation, for every number `N` of read rounds (in particular for the
two- and three-round reads of the paper's theorems). -/
theorem atomic_one_object (bot : V) (N : ℕ) : (proto (Rd := Rd) bot N).Atomic 0 bot := by
  intro F hF σ C h hs
  obtain rfl : F = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hF)
  simpa using (inv_init (Rd := Rd) bot).exec N hs |>.atomic

end Podc.RobustAtomicStorage.Sanity
