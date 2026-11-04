import Papers.PODC2011.RobustAtomicStorage.Model

/-!
# Label runs and canonical interpretation

The lower-bound proofs of the paper compare many runs of an *arbitrary* protocol `P`. All of them
have the following property, which we exploit: every operation instance occurring in several runs
receives exactly the same replies in each of its terminated rounds in all of them (the instances
are numbered globally, one instance per read of the construction). We therefore run the
constructions with the *label protocol* `LP`, a concrete protocol-independent instance of the
model whose messages are labels `(instance, round)` and whose replies record the label and the
log (as labels) of the replying object. A label run that is **canonical** — each terminated round
of an instance `i` saw exactly the transcript `T (i, q)` — maps to a run of `P` with the same
schedule (`sim`): the label `(i, q)` is interpreted as the canonical message `M (i, q)` of `P`,
which is well defined (`exists_isCanon`) as soon as transcripts only mention earlier labels.

So all the indistinguishability arguments of the paper become statements about label runs, which
do not mention the protocol at all.
-/

namespace Podc.RobustAtomicStorage

variable {Obj Rd V Msg Rep Inst : Type}

/-- Labels: (operation instance, round). -/
abbrev Lab (Inst : Type) := Inst × ℕ

/-- Replies of the label protocol: the label of the message and the log of the object. -/
abbrev LRep (Rd Inst : Type) := Lab Inst × List (Cl Rd × Lab Inst)

/-- The label protocol for the instance assignment `inst` of a run. -/
def LP (K N : ℕ) (bot : V) (inst : Cl Rd → Inst) : Proto Obj Rd V (Lab Inst) (LRep Rd Inst) where
  K := K
  N := N
  reply _ log _ m := (m, log)
  wMsg _ views _ := (inst .w, views.length + 1)
  rMsg j views _ := (inst (.r j), views.length + 1)
  rRet _ _ := bot

section Interp

variable (P : Proto Obj Rd V Msg Rep) (M : Lab Inst → Obj → Msg)

/-- Interpretation of a label log at object `s`. -/
def ilog (L : List (Cl Rd × Lab Inst)) (s : Obj) : List (Cl Rd × Msg) :=
  L.map fun p => (p.1, M p.2 s)

/-- Interpretation of a label view of client `c`. -/
def iview (c : Cl Rd) (v : View Obj (LRep Rd Inst)) : View Obj Rep :=
  v.map fun e => (e.1, P.reply e.1 (ilog M e.2.2 e.1) c (M e.2.1 e.1))

variable (T : Lab Inst → View Obj (LRep Rd Inst)) (clOf : Inst → Cl Rd) (v₁ : V)

/-- The message of label `(i, q)` determined by the interpretation `M` of the earlier labels. -/
def cmsg (lab : Lab Inst) (s : Obj) : Msg :=
  P.msg v₁ (clOf lab.1)
    ((List.range (lab.2 - 1)).map fun p => iview P M (clOf lab.1) (T (lab.1, p + 1))) s

/-- `M` is the canonical interpretation of the labels for the transcripts `T`. -/
def IsCanon : Prop := ∀ lab s, M lab s = cmsg P M T clOf v₁ lab s

/-- All labels mentioned in a label view. -/
def labsV (v : View Obj (LRep Rd Inst)) : List (Lab Inst) :=
  v.flatMap fun e => e.2.1 :: e.2.2.map Prod.snd

end Interp

section Exist

variable (P : Proto Obj Rd V Msg Rep) (T : Lab Inst → View Obj (LRep Rd Inst))
  (clOf : Inst → Cl Rd) (v₁ : V)

lemma iview_congr {M M' : Lab Inst → Obj → Msg} (c : Cl Rd) (v : View Obj (LRep Rd Inst))
    (h : ∀ lab ∈ labsV v, M lab = M' lab) : iview P M c v = iview P M' c v := by
  unfold iview ilog
  apply List.map_congr_left
  intro e he
  have h1 : M e.2.1 = M' e.2.1 := h _ (by simp only [labsV, List.mem_flatMap]; exact ⟨e, he, by simp⟩)
  have h2 : e.2.2.map (fun p => (p.1, M p.2 e.1)) = e.2.2.map (fun p => (p.1, M' p.2 e.1)) := by
    apply List.map_congr_left
    intro p hp
    rw [h p.2 (by simp only [labsV, List.mem_flatMap]; exact ⟨e, he, by simp; exact Or.inr ⟨p.1, hp⟩⟩)]
  rw [h1, h2]

lemma cmsg_congr {M M' : Lab Inst → Obj → Msg} (lab : Lab Inst)
    (h : ∀ p, p + 1 < lab.2 → ∀ l ∈ labsV (T (lab.1, p + 1)), M l = M' l) :
    cmsg P M T clOf v₁ lab = cmsg P M' T clOf v₁ lab := by
  funext s
  unfold cmsg
  have : (List.range (lab.2 - 1)).map (fun p => iview P M (clOf lab.1) (T (lab.1, p + 1))) =
      (List.range (lab.2 - 1)).map (fun p => iview P M' (clOf lab.1) (T (lab.1, p + 1))) := by
    apply List.map_congr_left
    intro p hp
    simp only [List.mem_range] at hp
    exact iview_congr P _ _ (h p (by omega))
  rw [this]

/-- Iterates of the canonical-message operator. -/
def citer : ℕ → Lab Inst → Obj → Msg
  | 0 => fun lab s => P.msg v₁ (clOf lab.1) [] s
  | n + 1 => cmsg P (citer n) T clOf v₁

/-- If transcripts only mention earlier labels (w.r.t. a rank `ρ`), the canonical interpretation
exists. -/
theorem exists_isCanon (ρ : Lab Inst → ℕ)
    (hρ : ∀ i q p, p + 1 < q → ∀ l ∈ labsV (T (i, p + 1)), ρ l < ρ (i, q)) :
    ∃ M, IsCanon P M T clOf v₁ := by
  -- stabilisation: `citer (n+1) lab = citer n lab` for `ρ lab < n`
  have stab : ∀ n lab, ρ lab < n → citer P T clOf v₁ (n + 1) lab = citer P T clOf v₁ n lab := by
    intro n
    induction n with
    | zero => intro lab h; omega
    | succ n ih =>
      intro lab h
      show cmsg P (citer P T clOf v₁ (n + 1)) T clOf v₁ lab = cmsg P (citer P T clOf v₁ n) T clOf v₁ lab
      apply cmsg_congr
      intro p hp l hl
      have := hρ lab.1 lab.2 p hp l hl
      simp only [Prod.mk.eta] at this
      exact ih l (by omega)
  have stab' : ∀ lab n m, ρ lab < n → n ≤ m → citer P T clOf v₁ m lab = citer P T clOf v₁ n lab := by
    intro lab n m hn hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [stab m lab (by omega), ih]
  refine ⟨fun lab => citer P T clOf v₁ (ρ lab + 1) lab, fun lab s => ?_⟩
  show cmsg P (citer P T clOf v₁ (ρ lab)) T clOf v₁ lab s = _
  refine congrFun (cmsg_congr P T clOf v₁ lab ?_) s
  intro p hp l hl
  have := hρ lab.1 lab.2 p hp l hl
  simp only [Prod.mk.eta] at this
  exact stab' l (ρ l + 1) (ρ lab) (by omega) (by omega)

end Exist

section Sim

variable [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V]
variable (P : Proto Obj Rd V Msg Rep) (M : Lab Inst → Obj → Msg)
  (T : Lab Inst → View Obj (LRep Rd Inst)) (clOf : Inst → Cl Rd) (v₁ bot : V)
  (inst : Cl Rd → Inst)

/-- Configurations of label runs. -/
abbrev LCfg (Obj Rd V Inst : Type) := Cfg Obj Rd V (Lab Inst) (LRep Rd Inst)
/-- Events of label runs (malicious objects forge label logs). -/
abbrev LEv (Obj Rd V Inst : Type) := Ev Obj Rd V (List (Cl Rd × Lab Inst))

/-- Interpretation of a label configuration in the protocol `P`. -/
def icfg (C : LCfg Obj Rd V Inst) : Cfg Obj Rd V Msg Rep where
  log s := ilog M (C.log s) s
  rnd := C.rnd
  past c := (C.past c).map (iview P M c)
  cur c := iview P M c (C.cur c)
  prc := C.prc
  done := C.done
  wv := C.wv

/-- Interpretation of a label event. -/
def iev : LEv Obj Rd V Inst → Ev Obj Rd V (List (Cl Rd × Msg))
  | .forge s L => .forge s (ilog M L s)
  | .invW v => .invW v
  | .invR j => .invR j
  | .dlv c s => .dlv c s
  | .nxt c => .nxt c

/-- The canonical value returned by the read of instance `inst (.r j)`. -/
def cret (j : Rd) : V :=
  P.rRet j ((List.range P.N).map fun p => iview P M (.r j) (T (inst (.r j), p + 1)))

/-- Interpretation of history events: reads return their canonical values. -/
def ihist : HEv Rd V → HEv Rd V
  | .retR j _ => .retR j (cret P M T inst j)
  | e => e

/-- Invariant of label runs used by the simulation. -/
structure SInv (C : LCfg Obj Rd V Inst) : Prop where
  past : ∀ c, C.past c = (List.range (C.past c).length).map fun p => T (inst c, p + 1)
  len : ∀ c, (C.rnd c = 0 ∧ C.past c = [] ∧ C.done c = false) ∨
    (0 < C.rnd c ∧ C.done c = false ∧ (C.past c).length + 1 = C.rnd c) ∨
    (C.done c = true ∧ 0 < C.rnd c ∧ (C.past c).length = C.rnd c)
  wv : 0 < C.rnd .w → C.wv = v₁

/-- The local canonicity condition of one event: a terminated round saw the canonical transcript,
and the writer writes `v₁`. -/
def EvCanon (C : LCfg Obj Rd V Inst) : LEv Obj Rd V Inst → Prop
  | .nxt c => C.cur c = T (inst c, C.rnd c)
  | .invW v => v = v₁
  | _ => True

/-- A label run is canonical if every event satisfies `EvCanon`. -/
def Canon (t : ℕ) (F : Finset Obj) : LCfg Obj Rd V Inst → List (LEv Obj Rd V Inst) → Prop
  | _, [] => True
  | C, e :: σ => EvCanon T v₁ inst C e ∧
      ∀ p, (LP P.K P.N bot inst).step t F bot C e = some p → Canon t F p.1 σ

omit [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
lemma SInv.init : SInv T v₁ inst (Cfg.init bot : LCfg Obj Rd V Inst) :=
  ⟨fun _ => rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩, fun h => absurd h (lt_irrefl 0)⟩

omit [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
lemma icfg_init : icfg P M (Cfg.init bot : LCfg Obj Rd V Inst) = Cfg.init bot := rfl

omit [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
lemma ilog_update_fun (f : Obj → List (Cl Rd × Lab Inst)) (s : Obj) (L : List (Cl Rd × Lab Inst)) :
    (fun s' => ilog M (Function.update f s L s') s') =
      Function.update (fun s' => ilog M (f s') s') s (ilog M L s) := by
  funext s'
  by_cases h : s' = s
  · subst h; simp
  · simp [h]

omit [DecidableEq Obj] [Fintype Obj] [DecidableEq V] in
lemma iview_update_fun (f : Cl Rd → View Obj (LRep Rd Inst)) (c : Cl Rd) (v : View Obj (LRep Rd Inst)) :
    (fun c' => iview P M c' (Function.update f c v c')) =
      Function.update (fun c' => iview P M c' (f c')) c (iview P M c v) := by
  funext c'
  by_cases h : c' = c
  · subst h; simp
  · simp [h]

omit [DecidableEq Obj] [Fintype Obj] [DecidableEq V] in
lemma ipast_update_fun (f : Cl Rd → List (View Obj (LRep Rd Inst))) (c : Cl Rd)
    (v : List (View Obj (LRep Rd Inst))) :
    (fun c' => (Function.update f c v c').map (iview P M c')) =
      Function.update (fun c' => (f c').map (iview P M c')) c (v.map (iview P M c)) := by
  funext c'
  by_cases h : c' = c
  · subst h; simp
  · simp [h]

omit [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
lemma msg_r (j : Rd) (v v' : V) : P.msg v (.r j) = P.msg v' (.r j) := rfl

omit [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
/-- The canonical message of round `q` of client `c` agrees with what `P` sends. -/
lemma msg_canon (hcl : ∀ c, clOf (inst c) = c) (hM : IsCanon P M T clOf v₁)
    (C : LCfg Obj Rd V Inst) (hI : SInv T v₁ inst C) (c : Cl Rd) (s : Obj) (q : ℕ)
    (hq : 1 ≤ q) (hqr : q ≤ C.rnd c) :
    P.msg C.wv c (((C.past c).map (iview P M c)).take (q - 1)) s = M (inst c, q) s ∧
      (LP P.K P.N bot inst).msg C.wv c ((C.past c).take (q - 1)) s = (inst c, q) := by
  have hlen : q - 1 ≤ (C.past c).length := by
    rcases hI.len c with ⟨h0, -⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ <;> omega
  have htake : (C.past c).take (q - 1) = (List.range (q - 1)).map fun p => T (inst c, p + 1) := by
    rw [hI.past c, ← List.map_take, List.take_range, min_eq_left (by simpa using hlen)]
  constructor
  · rw [hM, ← List.map_take, htake]
    simp only [cmsg, hcl, List.map_map]
    rcases c with _ | j
    · rw [hI.wv (by omega)]
      rfl
    · rfl
  · rcases c with _ | j <;>
    · simp only [Proto.msg, LP, List.length_take]
      congr 1
      omega

omit [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
lemma ite_pos' {α : Type*} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

omit [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
lemma ite_neg' {α : Type*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

omit [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
lemma past_snoc (C : LCfg Obj Rd V Inst) (hI : SInv T v₁ inst C) (c : Cl Rd)
    (hc : C.cur c = T (inst c, (C.past c).length + 1)) :
    C.past c ++ [C.cur c] =
      (List.range ((C.past c).length + 1)).map fun p => T (inst c, p + 1) := by
  conv_lhs => rw [hI.past c]
  rw [hc, List.range_succ, List.map_append]
  simp

theorem sim_step (hcl : ∀ c, clOf (inst c) = c) (hM : IsCanon P M T clOf v₁)
    (t : ℕ) (F : Finset Obj) (C C' : LCfg Obj Rd V Inst) (e : LEv Obj Rd V Inst)
    (h : List (HEv Rd V)) (hI : SInv T v₁ inst C) (hc : EvCanon T v₁ inst C e)
    (hs : (LP P.K P.N bot inst).step t F bot C e = some (C', h)) :
    P.step t F bot (icfg P M C) (iev M e) = some (icfg P M C', h.map (ihist P M T inst)) ∧
      SInv T v₁ inst C' := by
  cases e with
  | invW v =>
    simp only [Proto.step, iev] at hs ⊢
    split_ifs at hs with h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    refine ⟨?_, ?_⟩
    · split_ifs with h2
      · rfl
      · exact absurd h1 h2
    · have hv : v = v₁ := hc
      refine ⟨hI.past, fun c => ?_, fun _ => hv⟩
      by_cases hcw : c = .w
      · subst hcw
        rcases hI.len .w with ⟨h0, hp, hd⟩ | ⟨h0, -⟩ | ⟨-, h0, -⟩
        · right; left; simp [hp, hd]
        · omega
        · omega
      · simpa [Function.update_of_ne hcw] using hI.len c
  | invR j =>
    simp only [Proto.step, iev] at hs ⊢
    split_ifs at hs with h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    refine ⟨?_, ?_⟩
    · split_ifs with h2
      · rfl
      · exact absurd h1 h2
    · refine ⟨hI.past, fun c => ?_, fun h => ?_⟩
      · by_cases hcw : c = .r j
        · subst hcw
          rcases hI.len (.r j) with ⟨h0, hp, hd⟩ | ⟨h0, -⟩ | ⟨-, h0, -⟩
          · right; left; simp [hp, hd]
          · omega
          · omega
        · simpa [Function.update_of_ne hcw] using hI.len c
      · exact hI.wv (by simpa using h)
  | dlv c s =>
    simp only [Proto.step, iev] at hs ⊢
    split_ifs at hs with h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    refine ⟨?_, ⟨hI.past, hI.len, hI.wv⟩⟩
    simp only [show (icfg P M C).prc s c < (icfg P M C).rnd c from h1, ↓reduceIte, List.map_nil]
    obtain ⟨hmP, hmL⟩ := msg_canon P M T clOf v₁ bot inst hcl hM C hI c s (C.prc s c + 1)
      (by omega) (by omega)
    simp only [Proto.deliver, Nat.add_sub_cancel] at hmP hmL ⊢
    simp only [icfg, hmL, hmP]
    rw [ilog_update_fun, iview_update_fun]
    simp [ilog, iview, LP]
  | nxt c =>
    have hc' : C.cur c = T (inst c, C.rnd c) := hc
    have hr : (LP (Obj := Obj) P.K P.N bot inst).rounds c = P.rounds c := by cases c <;> rfl
    simp only [Proto.step, iev, hr] at hs ⊢
    split_ifs at hs with h1 h2
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
      have hlen : (C.past c).length + 1 = C.rnd c := by
        rcases hI.len c with ⟨h0, -⟩ | ⟨-, -, h⟩ | ⟨hd, -⟩
        · omega
        · exact h
        · simp [hd] at h1
      have hsn := past_snoc T v₁ inst C hI c (by rw [hc', hlen])
      refine ⟨?_, ?_⟩
      · rw [ite_pos' (show 0 < (icfg P M C).rnd c ∧ (icfg P M C).done c = false ∧
          Fintype.card Obj ≤ t + (icfg P M C).nResp c from h1),
          ite_pos' (show (icfg P M C).rnd c = P.rounds c from h2)]
        simp only [icfg, Option.some.injEq, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [ipast_update_fun, iview_update_fun]
          simp [iview]
        · rcases c with _ | j
          · rfl
          · simp only [Proto.retEv, List.map_cons, List.map_nil, ihist, List.cons.injEq, and_true,
              HEv.retR.injEq, true_and, cret]
            have e1 : (C.past (.r j)).map (iview P M (.r j)) ++ [iview P M (.r j) (C.cur (.r j))] =
                (C.past (.r j) ++ [C.cur (.r j)]).map (iview P M (.r j)) := by simp
            have hN : (C.past (.r j)).length + 1 = P.N := hlen.trans h2
            rw [e1, hsn, List.map_map, hN]
            rfl
      · refine ⟨fun c' => ?_, fun c' => ?_, fun h => ?_⟩
        · by_cases hcc : c' = c
          · subst hcc; simp only [Function.update_self]; rw [hsn]; simp
          · simpa [Function.update_of_ne hcc] using hI.past c'
        · by_cases hcc : c' = c
          · subst hcc; right; right; simp; omega
          · simpa [Function.update_of_ne hcc] using hI.len c'
        · exact hI.wv h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
      have hlen : (C.past c).length + 1 = C.rnd c := by
        rcases hI.len c with ⟨h0, -⟩ | ⟨-, -, h⟩ | ⟨hd, -⟩
        · omega
        · exact h
        · simp [hd] at h1
      have hsn := past_snoc T v₁ inst C hI c (by rw [hc', hlen])
      refine ⟨?_, ?_⟩
      · rw [ite_pos' (show 0 < (icfg P M C).rnd c ∧ (icfg P M C).done c = false ∧
          Fintype.card Obj ≤ t + (icfg P M C).nResp c from h1),
          ite_neg' (show ¬ (icfg P M C).rnd c = P.rounds c from h2)]
        simp only [icfg, Option.some.injEq, Prod.mk.injEq, List.map_nil, and_true]
        rw [ipast_update_fun, iview_update_fun]
        simp [iview]
      · refine ⟨fun c' => ?_, fun c' => ?_, fun h => ?_⟩
        · by_cases hcc : c' = c
          · subst hcc; simp only [Function.update_self]; rw [hsn]; simp
          · simpa [Function.update_of_ne hcc] using hI.past c'
        · by_cases hcc : c' = c
          · subst hcc; right; left
            refine ⟨by simp, by simpa using h1.2.1, by simp; omega⟩
          · simpa [Function.update_of_ne hcc] using hI.len c'
        · by_cases hcc : c = .w
          · subst hcc; exact hI.wv h1.1
          · exact hI.wv (by simpa [Function.update_of_ne (Ne.symm hcc)] using h)
  | forge s L =>
    simp only [Proto.step, iev] at hs ⊢
    split_ifs at hs with h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    refine ⟨?_, ⟨hI.past, hI.len, hI.wv⟩⟩
    simp only [h1, ↓reduceIte, icfg, List.map_nil, Option.some.injEq, Prod.mk.injEq, and_true]
    congr 1
    exact (ilog_update_fun M C.log s L).symm

/-- **Simulation.** A canonical label run maps to a run of `P` with the same schedule, in which
every read returns its canonical value. -/
theorem sim (hcl : ∀ c, clOf (inst c) = c) (hM : IsCanon P M T clOf v₁) (t : ℕ) (F : Finset Obj) :
    ∀ (σ : List (LEv Obj Rd V Inst)) (C C' : LCfg Obj Rd V Inst) (h : List (HEv Rd V)),
      SInv T v₁ inst C → Canon P T v₁ bot inst t F C σ →
      (LP P.K P.N bot inst).exec t F bot C σ = some (C', h) →
      P.exec t F bot (icfg P M C) (σ.map (iev M)) = some (icfg P M C', h.map (ihist P M T inst)) := by
  intro σ
  induction σ with
  | nil =>
    intro C C' h _ _ hx
    simp only [Proto.exec, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    rfl
  | cons e σ ih =>
    intro C C' h hI hc hx
    simp only [Proto.exec] at hx
    obtain ⟨p, hp, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
    obtain ⟨hstep, hI'⟩ := sim_step P M T clOf v₁ bot inst hcl hM t F C p.1 e p.2 hI hc.1 hp
    have := ih p.1 q.1 q.2 hI' (hc.2 p hp) hq
    simp only [List.map_cons, Proto.exec, hstep, Option.bind_some, this, Option.map_some,
      List.map_append]

/-- Corollary used by the lower bounds: a canonical label run from the initial configuration
gives a run of `P` whose history is the label history with canonical return values. -/
theorem sim_init (hcl : ∀ c, clOf (inst c) = c) (hM : IsCanon P M T clOf v₁) (t : ℕ)
    (F : Finset Obj) (σ : List (LEv Obj Rd V Inst)) (C' : LCfg Obj Rd V Inst) (h : List (HEv Rd V))
    (hc : Canon P T v₁ bot inst t F (Cfg.init bot) σ)
    (hx : (LP P.K P.N bot inst).exec t F bot (Cfg.init bot) σ = some (C', h)) :
    P.exec t F bot (Cfg.init bot) (σ.map (iev M)) = some (icfg P M C', h.map (ihist P M T inst)) :=
  sim P M T clOf v₁ bot inst hcl hM t F σ _ C' h (SInv.init T v₁ bot inst) hc hx

end Sim

end Podc.RobustAtomicStorage
