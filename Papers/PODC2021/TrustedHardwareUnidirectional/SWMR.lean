import Papers.PODC2021.TrustedHardwareUnidirectional.Rounds

/-!
# Shared memory with single-writer objects implements unidirectional rounds (Claim, §3.2)

**Model.** Asynchronous shared memory; each process `p` owns one object `o_p` (a SWMR register
holding a list of `(round, message)` pairs); only `p` can modify `o_p`, everybody can read it.
Every access is one atomic step; the scheduler interleaves steps arbitrarily. Byzantine processes
(set `F`, any size) may overwrite their own object with anything at any time. Fairness: every
correct process takes infinitely many steps.

**Protocol** (the paper's, from Aguilera et al.). In round `r`, process `p`
1. appends `(r, m)` to `o_p` (one write of the whole list);
2. reads `o_q` for every `q` (one atomic read per object, in the order `ord`), recording `m'` if it
   finds some `(r, m')` in `o_q`;
3. ends round `r`.

`swmr_implements`: for every Byzantine set and every client this implements unidirectional rounds.
-/

namespace Podc.TrustedHW

namespace SWMR

variable {P V : Type} [Fintype P] [DecidableEq P]

/-- Local state of a process. -/
structure LState (P V : Type) where
  /-- Results of completed rounds. -/
  done : List (P → Option V)
  /-- `none`: about to write the next round's message; `some i`: about to read `ord[i]`. -/
  pc : Option ℕ
  /-- Messages received so far in the current round. -/
  acc : P → Option V

/-- Global configuration: the objects and the local states. -/
structure Config (P V : Type) where
  /-- `obj p`: the content of `p`'s object. -/
  obj : P → List (ℕ × V)
  /-- Local states. -/
  st : P → LState P V

variable (P) in
/-- The order in which a process reads the objects. -/
noncomputable def ord : List P := (Finset.univ : Finset P).toList

lemma mem_ord (q : P) : q ∈ ord P := by simp [ord]

open Classical in
/-- Reading round `r` from an object: some `m'` with `(r, m') ∈ o`, if any. -/
noncomputable def readObj (r : ℕ) (l : List (ℕ × V)) : Option V :=
  if h : ∃ w, (r, w) ∈ l then some h.choose else none

lemma readObj_isSome_iff (r : ℕ) (l : List (ℕ × V)) :
    (readObj r l).isSome ↔ ∃ w, (r, w) ∈ l := by
  unfold readObj; split_ifs with h <;> simp [h]

lemma mem_of_readObj_eq_some {r : ℕ} {l : List (ℕ × V)} {w : V} (h : readObj r l = some w) :
    (r, w) ∈ l := by
  unfold readObj at h; split_ifs at h with h'
  cases h; exact h'.choose_spec

/-- One step of process `p`. -/
noncomputable def pstep (cl : P → Client P V) (c : Config P V) (p : P) : Config P V :=
  match (c.st p).pc with
  | none =>
    { obj := Function.update c.obj p (c.obj p ++ [((c.st p).done.length, cl p (c.st p).done)])
      st := Function.update c.st p ⟨(c.st p).done, some 0, fun _ => none⟩ }
  | some i =>
    if h : i < (ord P).length then
      { c with st := Function.update c.st p ⟨(c.st p).done, some (i + 1),
          Function.update (c.st p).acc (ord P)[i]
            (readObj (c.st p).done.length (c.obj (ord P)[i]))⟩ }
    else
      { c with st := Function.update c.st p ⟨(c.st p).done ++ [(c.st p).acc], none, (c.st p).acc⟩ }

/-- Steps: a correct process takes its next step, or a Byzantine process overwrites its object. -/
inductive Step (F : Finset P) (cl : P → Client P V) : Config P V → Config P V → Prop
  | proc (c : Config P V) (p : P) (hp : p ∉ F) : Step F cl c (pstep cl c p)
  | byz (c : Config P V) (s : P) (hs : s ∈ F) (l : List (ℕ × V)) :
      Step F cl c { c with obj := Function.update c.obj s l }

/-- Initial configurations: empty objects, correct processes at the start of round 0. -/
def Init (F : Finset P) (c : Config P V) : Prop :=
  (∀ p, c.obj p = []) ∧ ∀ p, p ∉ F → c.st p = ⟨[], none, fun _ => none⟩

/-- Fairness: every correct process takes infinitely many steps. -/
def Fair (F : Finset P) (cl : P → Client P V) (e : ℕ → Config P V) : Prop :=
  ∀ p, p ∉ F → ∀ t, ∃ t', t ≤ t' ∧ e (t' + 1) = pstep cl (e t') p

/-- The SWMR round system. -/
abbrev system (F : Finset P) (cl : P → Client P V) : RoundSystem P V where
  Config := Config P V
  Init := Init F
  Step := Step F cl
  Fair := Fair F cl
  rounds c p := (c.st p).done

/-! ### Basic lemmas on steps -/

lemma pstep_obj_of_ne {cl : P → Client P V} {c : Config P V} {p x : P} (h : x ≠ p) :
    (pstep cl c p).obj x = c.obj x := by
  unfold pstep; split
  · simp [Function.update_of_ne h]
  · split <;> rfl

lemma pstep_st_of_ne {cl : P → Client P V} {c : Config P V} {p x : P} (h : x ≠ p) :
    (pstep cl c p).st x = c.st x := by
  unfold pstep; split
  · simp [Function.update_of_ne h]
  · split <;> simp [Function.update_of_ne h]

lemma pstep_none {cl : P → Client P V} {c : Config P V} {p : P} (h : (c.st p).pc = none) :
    pstep cl c p =
      { obj := Function.update c.obj p (c.obj p ++ [((c.st p).done.length, cl p (c.st p).done)])
        st := Function.update c.st p ⟨(c.st p).done, some 0, fun _ => none⟩ } := by
  unfold pstep; rw [h]

lemma pstep_read {cl : P → Client P V} {c : Config P V} {p : P} {i : ℕ} (h : (c.st p).pc = some i)
    (hi : i < (ord P).length) :
    pstep cl c p = { c with st := Function.update c.st p ⟨(c.st p).done, some (i + 1),
          Function.update (c.st p).acc (ord P)[i]
            (readObj (c.st p).done.length (c.obj (ord P)[i]))⟩ } := by
  unfold pstep; rw [h]; simp only; rw [dite_eq_left hi]

lemma pstep_finish {cl : P → Client P V} {c : Config P V} {p : P} {i : ℕ}
    (h : (c.st p).pc = some i) (hi : ¬ i < (ord P).length) :
    pstep cl c p =
      { c with st := Function.update c.st p ⟨(c.st p).done ++ [(c.st p).acc], none, (c.st p).acc⟩ } := by
  unfold pstep; rw [h]; simp only; rw [dite_eq_right hi]

/-! ### The invariant -/

/-- Number of rounds whose message `p` has written. -/
def written (st : LState P V) : ℕ := st.done.length + if st.pc = none then 0 else 1

/-- `p` has read `o_q` in round `r`. -/
def Rd (st : LState P V) (q : P) (r : ℕ) : Prop :=
  r < st.done.length ∨ (r = st.done.length ∧ ∃ i, st.pc = some i ∧ q ∈ (ord P).take i)

/-- What `p` obtained from `o_q` in round `r` (meaningful when `Rd st q r`). -/
def Res (st : LState P V) (q : P) (r : ℕ) : Option V :=
  if h : r < st.done.length then st.done[r] q else st.acc q

/-- The invariant of reachable configurations. -/
structure Inv (F : Finset P) (cl : P → Client P V) (c : Config P V) : Prop where
  obj_eq : ∀ p, p ∉ F →
    c.obj p = (List.range (written (c.st p))).map fun r => (r, cl p ((c.st p).done.take r))
  pc_le : ∀ p, p ∉ F → ∀ i, (c.st p).pc = some i → i ≤ (ord P).length
  found : ∀ p q, p ∉ F → q ∉ F → ∀ r w, Rd (c.st p) q r → Res (c.st p) q r = some w →
    (r, w) ∈ c.obj q
  unidir : ∀ p q, p ∉ F → q ∉ F → p ≠ q → ∀ r, Rd (c.st p) q r → Res (c.st p) q r = none →
    Rd (c.st q) p r → (Res (c.st q) p r).isSome

lemma mem_obj_iff {F : Finset P} {cl : P → Client P V} {c : Config P V} (hI : Inv F cl c) {p : P}
    (hp : p ∉ F) (r : ℕ) (w : V) :
    (r, w) ∈ c.obj p ↔ r < written (c.st p) ∧ w = cl p ((c.st p).done.take r) := by
  rw [hI.obj_eq p hp]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
  · rintro ⟨h1, rfl⟩; exact ⟨r, h1, rfl, rfl⟩

lemma lt_written_of_rd {st : LState P V} {q : P} {r : ℕ} (h : Rd st q r) : r < written st := by
  unfold written
  rcases h with h | ⟨rfl, i, hi, -⟩
  · omega
  · simp [hi]

lemma inv_init {F : Finset P} {cl : P → Client P V} {c : Config P V} (h : Init F c) :
    Inv F cl c := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun p hp => ?_, fun p hp i hi => ?_, fun p q hp hq r w hr _ => ?_,
    fun p q hp hq _ r hr _ _ => ?_⟩
  · rw [h1, h2 p hp]; simp [written]
  · rw [h2 p hp] at hi; cases hi
  · rw [h2 p hp] at hr; simp [Rd] at hr
  · rw [h2 p hp] at hr; simp [Rd] at hr


/-- Preservation when no new read happens: views are only reduced/kept, objects only grow. -/
lemma inv_of_view {F : Finset P} {cl : P → Client P V} {c c' : Config P V} (hI : Inv F cl c)
    (h1 : ∀ x, x ∉ F → ∀ q r, Rd (c'.st x) q r → Rd (c.st x) q r ∧ Res (c'.st x) q r = Res (c.st x) q r)
    (h2 : ∀ q, q ∉ F → ∀ a ∈ c.obj q, a ∈ c'.obj q)
    (h3 : ∀ p, p ∉ F →
      c'.obj p = (List.range (written (c'.st p))).map fun r => (r, cl p ((c'.st p).done.take r)))
    (h4 : ∀ p, p ∉ F → ∀ i, (c'.st p).pc = some i → i ≤ (ord P).length) : Inv F cl c' := by
  refine ⟨h3, h4, fun p q hp hq r w hr hres => ?_, fun p q hp hq hpq r hr hres hr' => ?_⟩
  · obtain ⟨hr0, he⟩ := h1 p hp q r hr
    exact h2 q hq _ (hI.found p q hp hq r w hr0 (he ▸ hres))
  · obtain ⟨hr0, he⟩ := h1 p hp q r hr
    obtain ⟨hr0', he'⟩ := h1 q hq p r hr'
    rw [he']; exact hI.unidir p q hp hq hpq r hr0 (he ▸ hres) hr0'

lemma inv_step {F : Finset P} {cl : P → Client P V} {c c' : Config P V} (hI : Inv F cl c)
    (h : Step F cl c c') : Inv F cl c' := by
  cases h with
  | byz s hs l =>
    apply inv_of_view hI
    · intro x _ q r hr; exact ⟨hr, rfl⟩
    · intro q hq a ha
      have : q ≠ s := fun h => hq (h ▸ hs)
      simpa [Function.update_of_ne this] using ha
    · intro p hp
      have : p ≠ s := fun h => hp (h ▸ hs)
      simpa [Function.update_of_ne this] using hI.obj_eq p hp
    · exact hI.pc_le
  | proc p hp =>
    cases hpc : (c.st p).pc with
    | none =>
      rw [pstep_none hpc]
      apply inv_of_view hI
      · intro x _ q r hr
        by_cases hxp : x = p
        · subst hxp
          simp only [Function.update_self] at hr ⊢
          simp only [Rd, Res] at hr ⊢
          rcases hr with hr | ⟨-, i, hi, hq⟩
          · exact ⟨Or.inl hr, by simp [hr]⟩
          · cases hi; simp at hq
        · simp only [Function.update_of_ne hxp] at hr ⊢; exact ⟨hr, trivial⟩
      · intro q _ a ha
        by_cases hqp : q = p
        · subst hqp; simp [ha]
        · simpa [Function.update_of_ne hqp] using ha
      · intro x hx
        by_cases hxp : x = p
        · subst hxp
          simp only [Function.update_self]
          rw [hI.obj_eq x hx]
          simp [written, hpc, List.range_succ]
        · simpa [Function.update_of_ne hxp] using hI.obj_eq x hx
      · intro x hx i hi
        by_cases hxp : x = p
        · subst hxp; simp at hi; omega
        · simp only [Function.update_of_ne hxp] at hi; exact hI.pc_le x hx i hi
    | some i =>
      by_cases hi : i < (ord P).length
      · rw [pstep_read hpc hi]
        set j := (ord P)[i]
        set R := (c.st p).done.length
        have hRd : ∀ q r, Rd (⟨(c.st p).done, some (i + 1),
            Function.update (c.st p).acc j (readObj R (c.obj j))⟩ : LState P V) q r →
            (Rd (c.st p) q r ∧ q ≠ j) ∨ r < R ∨ (r = R ∧ q = j) := by
          intro q r hr
          rcases hr with hr | ⟨hr, i', hi', hq⟩
          · exact Or.inr (Or.inl hr)
          · cases hi'
            rw [List.take_add_one, List.mem_append] at hq
            by_cases hqj : q = j
            · exact Or.inr (Or.inr ⟨hr, hqj⟩)
            · rcases hq with hq | hq
              · exact Or.inl ⟨Or.inr ⟨hr, i, hpc, hq⟩, hqj⟩
              · simp [List.getElem?_eq_getElem hi] at hq; exact absurd hq hqj
        have hRes : ∀ q r, q ≠ j ∨ r < R → Res (⟨(c.st p).done, some (i + 1),
            Function.update (c.st p).acc j (readObj R (c.obj j))⟩ : LState P V) q r =
            Res (c.st p) q r := by
          intro q r h
          simp only [Res]
          split_ifs with hr
          · rfl
          · rcases h with h | h
            · simp [Function.update_of_ne h]
            · exact absurd h hr
        have hRdLt : ∀ q r, r < R → Rd (c.st p) q r := fun q r h => Or.inl h
        have hResJ : Res (⟨(c.st p).done, some (i + 1),
            Function.update (c.st p).acc j (readObj R (c.obj j))⟩ : LState P V) j R =
            readObj R (c.obj j) := by
          simp [Res, R]
        refine ⟨fun x hx => ?_, fun x hx i' hi' => ?_, fun x q hx hq r w hr hres => ?_,
          fun x q hx hq hxq r hr hres hr' => ?_⟩
        · by_cases hxp : x = p
          · subst hxp; simp only [Function.update_self]; rw [hI.obj_eq x hx]; simp [written, hpc]
          · simp only [Function.update_of_ne hxp]; exact hI.obj_eq x hx
        · by_cases hxp : x = p
          · subst hxp; simp at hi'; omega
          · simp only [Function.update_of_ne hxp] at hi'; exact hI.pc_le x hx i' hi'
        · by_cases hxp : x = p
          · subst hxp
            simp only [Function.update_self] at hr hres ⊢
            rcases hRd q r hr with ⟨hr0, hqj⟩ | hr0 | ⟨rfl, rfl⟩
            · rw [hRes q r (Or.inl hqj)] at hres; exact hI.found x q hx hq r w hr0 hres
            · rw [hRes q r (Or.inr hr0)] at hres; exact hI.found x q hx hq r w (hRdLt q r hr0) hres
            · rw [hResJ] at hres; exact mem_of_readObj_eq_some hres
          · simp only [Function.update_of_ne hxp] at hr hres; exact hI.found x q hx hq r w hr hres
        · by_cases hxp : x = p
          · subst hxp
            have hqx : q ≠ x := Ne.symm hxq
            simp only [Function.update_self, Function.update_of_ne hqx] at hr hres hr' ⊢
            rcases hRd q r hr with ⟨hr0, hqj⟩ | hr0 | ⟨rfl, rfl⟩
            · rw [hRes q r (Or.inl hqj)] at hres; exact hI.unidir x q hx hq hxq r hr0 hres hr'
            · rw [hRes q r (Or.inr hr0)] at hres
              exact hI.unidir x q hx hq hxq r (hRdLt q r hr0) hres hr'
            · rw [hResJ] at hres
              have h1 := lt_written_of_rd hr'
              have h2 := (mem_obj_iff hI hq R (cl j ((c.st j).done.take R))).2 ⟨h1, rfl⟩
              have h3 := (readObj_isSome_iff R (c.obj j)).2 ⟨_, h2⟩
              rw [hres] at h3; simp at h3
          · by_cases hqp : q = p
            · subst hqp
              simp only [Function.update_self, Function.update_of_ne hxp] at hr hres hr' ⊢
              rcases hRd x r hr' with ⟨hr0, hxj⟩ | hr0 | ⟨rfl, rfl⟩
              · rw [hRes x r (Or.inl hxj)]; exact hI.unidir x q hx hq hxq r hr hres hr0
              · rw [hRes x r (Or.inr hr0)]; exact hI.unidir x q hx hq hxq r hr hres (hRdLt x r hr0)
              · rw [hResJ, readObj_isSome_iff]
                exact ⟨_, (mem_obj_iff hI hx R _).2 ⟨lt_written_of_rd hr, rfl⟩⟩
            · simp only [Function.update_of_ne hxp, Function.update_of_ne hqp] at hr hres hr' ⊢
              exact hI.unidir x q hx hq hxq r hr hres hr'
      · rw [pstep_finish hpc hi]
        have hiL : i = (ord P).length := le_antisymm (hI.pc_le p hp i hpc) (not_lt.1 hi)
        apply inv_of_view hI
        · intro x _ q r hr
          by_cases hxp : x = p
          · subst hxp
            simp only [Function.update_self] at hr ⊢
            simp only [Rd, Res, List.length_append, List.length_singleton] at hr ⊢
            rcases hr with hr | ⟨-, i', hi', -⟩
            · by_cases hr' : r < (c.st x).done.length
              · refine ⟨Or.inl hr', ?_⟩
                rw [dite_eq_left (by omega), dite_eq_left hr', List.getElem_append_left hr']
              · have hr'' : r = (c.st x).done.length := by omega
                refine ⟨Or.inr ⟨hr'', i, hpc, ?_⟩, ?_⟩
                · rw [hiL, List.take_length]; exact mem_ord q
                · subst hr''
                  rw [dite_eq_left (by omega), dite_eq_right (lt_irrefl _), List.getElem_append_right le_rfl]
                  simp
            · cases hi'
          · simp only [Function.update_of_ne hxp] at hr ⊢; exact ⟨hr, trivial⟩
        · intro q _ a ha; exact ha
        · intro x hx
          by_cases hxp : x = p
          · subst hxp
            simp only [Function.update_self]
            rw [hI.obj_eq x hx]
            simp only [written, hpc, reduceCtorEq, ite_false, List.length_append,
              List.length_singleton, ite_true]
            apply List.map_congr_left
            intro r hr
            rw [List.mem_range] at hr
            rw [List.take_append_of_le_length (by omega)]
          · simpa [Function.update_of_ne hxp] using hI.obj_eq x hx
        · intro x hx i' hi'
          by_cases hxp : x = p
          · subst hxp; simp at hi'
          · simp only [Function.update_of_ne hxp] at hi'; exact hI.pc_le x hx i' hi'

lemma inv_of_reachable {F : Finset P} {cl : P → Client P V} {c : Config P V}
    (hc : (system F cl).Reachable c) : Inv F cl c := by
  obtain ⟨c₀, h₀, hr⟩ := hc
  induction hr with
  | refl => exact inv_init h₀
  | tail _ h ih => exact inv_step ih h


/-! ### Liveness -/

/-- Progress measure of a process. -/
noncomputable def mu (st : LState P V) : ℕ :=
  st.done.length * ((ord P).length + 2) + match st.pc with
    | none => 0
    | some i => i + 1

lemma mu_pstep {F : Finset P} {cl : P → Client P V} {c : Config P V} (hI : Inv F cl c) {p : P}
    (hp : p ∉ F) : mu ((pstep cl c p).st p) = mu (c.st p) + 1 := by
  cases hpc : (c.st p).pc with
  | none => rw [pstep_none hpc]; simp [mu, hpc]
  | some i =>
    by_cases hi : i < (ord P).length
    · rw [pstep_read hpc hi]; simp [mu, hpc]; omega
    · rw [pstep_finish hpc hi]
      have := hI.pc_le p hp i hpc
      simp only [mu, hpc, Function.update_self, List.length_append, List.length_singleton]
      have : i = (ord P).length := by omega
      subst this; ring

lemma mu_step {F : Finset P} {cl : P → Client P V} {c c' : Config P V} (hI : Inv F cl c)
    (h : Step F cl c c') {p : P} (hp : p ∉ F) : mu (c.st p) ≤ mu (c'.st p) := by
  cases h with
  | byz => exact le_rfl
  | proc x hx =>
    by_cases hxp : p = x
    · subst hxp; rw [mu_pstep hI hp]; omega
    · rw [pstep_st_of_ne hxp]

lemma mu_lt (st : LState P V) (h : ∀ i, st.pc = some i → i ≤ (ord P).length) :
    mu st < (st.done.length + 1) * ((ord P).length + 2) := by
  unfold mu
  cases hpc : st.pc with
  | none => simp
  | some i => have := h i hpc; simp only; ring_nf; omega

/-! ### The theorem -/

/-- **Claim of Section 3.2**: single-writer multi-reader objects implement unidirectional
rounds, for any set `F` of Byzantine processes and any clients. -/
theorem swmr_implements (F : Finset P) (cl : P → Client P V) :
    (system F cl).ImplementsUnidirectional (· ∉ F) cl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c c' _ h p _
    show (c.st p).done <+: (c'.st p).done
    cases h with
    | byz => exact List.prefix_refl _
    | proc x hx =>
      by_cases hxp : p = x
      · subst hxp
        cases hpc : (c.st p).pc with
        | none => rw [pstep_none hpc]; simp
        | some i =>
          by_cases hi : i < (ord P).length
          · rw [pstep_read hpc hi]; simp
          · rw [pstep_finish hpc hi]; simp
      · rw [pstep_st_of_ne hxp]
  · intro c hc p q hp hq hpq r hrp hrq
    have hI := inv_of_reachable hc
    change r < (c.st p).done.length at hrp
    change r < (c.st q).done.length at hrq
    change ((c.st p).done[r] q).isSome ∨ ((c.st q).done[r] p).isSome
    have hRp : Rd (c.st p) q r := Or.inl hrp
    have hRq : Rd (c.st q) p r := Or.inl hrq
    have e1 : Res (c.st p) q r = (c.st p).done[r] q := by simp [Res, hrp]
    have e2 : Res (c.st q) p r = (c.st q).done[r] p := by simp [Res, hrq]
    by_cases h : ((c.st p).done[r] q).isSome
    · exact Or.inl h
    · right
      rw [← e2]
      refine hI.unidir p q hp hq hpq r hRp ?_ hRq
      rw [e1]; simpa using h
  · intro c hc p q hp hq r hrp w hw
    have hI := inv_of_reachable hc
    change r < (c.st p).done.length at hrp
    change (c.st p).done[r] q = some w at hw
    change r ≤ (c.st q).done.length ∧ w = cl q ((c.st q).done.take r)
    have hRes : Res (c.st p) q r = some w := by simp [Res, hrp, hw]
    have hmem := hI.found p q hp hq r w (Or.inl hrp) hRes
    obtain ⟨h1, h2⟩ := (mem_obj_iff hI hq r w).1 hmem
    refine ⟨?_, h2⟩
    unfold written at h1; split_ifs at h1 <;> omega
  · intro e he hfair p hp r
    have hI : ∀ t, Inv F cl (e t) := fun t => inv_of_reachable (he.reachable t)
    have hmono : ∀ t t', t ≤ t' → mu ((e t).st p) ≤ mu ((e t').st p) := by
      intro t t' h
      induction h with
      | refl => exact le_rfl
      | step _ ih =>
        rename_i m _
        refine ih.trans ?_
        rcases he.2 m with h | h
        · exact mu_step (hI m) h hp
        · rw [h]
    have hgrow : ∀ B, ∃ t, B ≤ mu ((e t).st p) := by
      intro B
      induction B with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ B ih =>
        obtain ⟨t, ht⟩ := ih
        obtain ⟨t', htt', he'⟩ := hfair p hp t
        refine ⟨t' + 1, ?_⟩
        rw [he', mu_pstep (hI t') hp]
        have := hmono t t' htt'
        omega
    obtain ⟨t, ht⟩ := hgrow ((r + 1) * ((ord P).length + 2))
    refine ⟨t, ?_⟩
    change r < ((e t).st p).done.length
    have h1 := mu_lt ((e t).st p) ((hI t).pc_le p hp)
    by_contra hcon
    have h2 : (((e t).st p).done.length + 1) * ((ord P).length + 2) ≤
        (r + 1) * ((ord P).length + 2) := Nat.mul_le_mul_right _ (by omega)
    omega

/-! ### Fair executions exist -/

section Fair

variable [Nonempty P] (F : Finset P) (cl : P → Client P V)

/-- The process scheduled at time `t` (round robin). -/
noncomputable def procAt (t : ℕ) : P :=
  (Fintype.equivFin P).symm ⟨t % Fintype.card P, Nat.mod_lt _ Fintype.card_pos⟩

/-- The round-robin execution (Byzantine processes stay silent). -/
noncomputable def rrExec : ℕ → Config P V
  | 0 => ⟨fun _ => [], fun _ => ⟨[], none, fun _ => none⟩⟩
  | t + 1 => if procAt (P := P) t ∈ F then rrExec t else pstep cl (rrExec t) (procAt t)

lemma rrExec_isExec : (system F cl).IsExec (rrExec F cl) := by
  refine ⟨⟨fun _ => rfl, fun _ _ => rfl⟩, fun t => ?_⟩
  show Step F cl _ (if procAt (P := P) t ∈ F then _ else _) ∨ (if procAt (P := P) t ∈ F then _ else _) = _
  split_ifs with h
  · right; rfl
  · left; exact Step.proc _ _ h

/-- **Round-robin executions are fair** (non-vacuity of the liveness requirement). -/
theorem rrExec_fair : Fair F cl (rrExec F cl) := by
  intro p hp t
  obtain ⟨τ, h1, -, h3⟩ := exists_mod_eq t (Fintype.card_pos (α := P))
    ((Fintype.equivFin P) p).isLt
  refine ⟨τ, h1, ?_⟩
  have : procAt (P := P) τ = p := by
    simp only [procAt]; rw [Equiv.symm_apply_eq]; exact Fin.ext h3
  show (if procAt (P := P) τ ∈ F then _ else _) = _
  rw [ite_eq_right (by rw [this]; exact hp), this]

end Fair

end SWMR

end Podc.TrustedHW
