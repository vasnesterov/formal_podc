import Papers.PODC2011.RobustAtomicStorage.Sim

/-!
# Checked label runs and phase lemmas

`cexec` runs the label protocol and additionally fails if a terminated round does not see its
canonical transcript (`EvCanon`). A successful `cexec` gives both a label run and its
canonicity (`cexec_spec`), hence (by `sim_init`) a run of every protocol. The phase lemmas compute
the effect of the macro-steps used in the constructions (deliveries to a list of objects, round
terminations, forging).
-/

set_option linter.unusedSectionVars false

namespace Podc.RobustAtomicStorage

open Classical

variable {Obj Rd V : Type} [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V]

/-- Instances: a client and an index (the paper's reads of the read lower bound reuse readers). -/
abbrev Inst (Rd : Type) := Cl Rd × ℕ

section
variable (K N : ℕ) (T : Lab (Inst Rd) → View Obj (LRep Rd (Inst Rd))) (v₁ bot : V)
  (inst : Cl Rd → Inst Rd) (t : ℕ) (F : Finset Obj)

/-- Label protocol of a run (`K` write rounds, `N` read rounds). -/
noncomputable abbrev LPr := (LP (Obj := Obj) K N bot inst)

/-- One checked step. -/
noncomputable def cstep (C : LCfg Obj Rd V (Inst Rd)) (e : LEv Obj Rd V (Inst Rd)) :
    Option (LCfg Obj Rd V (Inst Rd) × List (HEv Rd V)) :=
  if EvCanon T v₁ inst C e then (LPr K N bot inst).step t F bot C e else none

/-- Checked execution. -/
noncomputable def cexec (C : LCfg Obj Rd V (Inst Rd)) :
    List (LEv Obj Rd V (Inst Rd)) → Option (LCfg Obj Rd V (Inst Rd) × List (HEv Rd V))
  | [] => some (C, [])
  | e :: σ => (cstep K N T v₁ bot inst t F C e).bind fun p =>
      (cexec p.1 σ).map fun q => (q.1, p.2 ++ q.2)

lemma cexec_nil (C : LCfg Obj Rd V (Inst Rd)) : cexec K N T v₁ bot inst t F C [] = some (C, []) := rfl

lemma cexec_cons (C : LCfg Obj Rd V (Inst Rd)) (e σ) :
    cexec K N T v₁ bot inst t F C (e :: σ) = (cstep K N T v₁ bot inst t F C e).bind fun p =>
      (cexec K N T v₁ bot inst t F p.1 σ).map fun q => (q.1, p.2 ++ q.2) := rfl

lemma cexec_append (C : LCfg Obj Rd V (Inst Rd)) (σ₁ σ₂) :
    cexec K N T v₁ bot inst t F C (σ₁ ++ σ₂) = (cexec K N T v₁ bot inst t F C σ₁).bind fun p =>
      (cexec K N T v₁ bot inst t F p.1 σ₂).map fun q => (q.1, p.2 ++ q.2) := by
  induction σ₁ generalizing C with
  | nil => simp [cexec_nil]
  | cons e σ ih =>
    simp only [List.cons_append, cexec_cons, ih]
    cases cstep K N T v₁ bot inst t F C e with
    | none => rfl
    | some p =>
      simp only [Option.bind_some]
      cases cexec K N T v₁ bot inst t F p.1 σ with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.bind_some]
        cases cexec K N T v₁ bot inst t F q.1 σ₂ <;> simp

/-- Sequential composition of two successful checked executions. -/
lemma cexec_append_some {C C₁ C₂ : LCfg Obj Rd V (Inst Rd)} {σ₁ σ₂ h₁ h₂}
    (h1 : cexec K N T v₁ bot inst t F C σ₁ = some (C₁, h₁))
    (h2 : cexec K N T v₁ bot inst t F C₁ σ₂ = some (C₂, h₂)) :
    cexec K N T v₁ bot inst t F C (σ₁ ++ σ₂) = some (C₂, h₁ ++ h₂) := by
  rw [cexec_append, h1]; simp [h2]

lemma cexec_single {C C' : LCfg Obj Rd V (Inst Rd)} {e h}
    (hc : EvCanon T v₁ inst C e) (hs : (LPr K N bot inst).step t F bot C e = some (C', h)) :
    cexec K N T v₁ bot inst t F C [e] = some (C', h) := by
  simp [cexec_cons, cstep, hc, hs, cexec_nil]

/-- A successful checked execution is a canonical label run. -/
theorem cexec_spec {Msg Rep : Type} (P : Proto Obj Rd V Msg Rep) (hK : P.K = K) (hN : P.N = N) :
    ∀ (σ : List (LEv Obj Rd V (Inst Rd))) (C C' : LCfg Obj Rd V (Inst Rd)) h,
      cexec K N T v₁ bot inst t F C σ = some (C', h) →
      Canon P T v₁ bot inst t F C σ ∧ (LP P.K P.N bot inst).exec t F bot C σ = some (C', h) := by
  subst hK hN
  intro σ
  induction σ with
  | nil => intro C C' h hx; simp [cexec_nil] at hx; obtain ⟨rfl, rfl⟩ := hx; exact ⟨trivial, rfl⟩
  | cons e σ ih =>
    intro C C' h hx
    rw [cexec_cons] at hx
    obtain ⟨p, hp, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
    unfold cstep at hp
    split_ifs at hp with hc
    obtain ⟨ih1, ih2⟩ := ih p.1 q.1 q.2 hq
    refine ⟨⟨hc, fun p' hp' => ?_⟩, ?_⟩
    · rw [hp] at hp'; cases hp'; exact ih1
    · simp only [Proto.exec, hp, Option.bind_some, ih2, Option.map_some]

/-! ### Phase results -/

/-- Labels appended to the log of `s` when it processes `n` further round messages of `c`. -/
def newLabs (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (s : Obj) (n : ℕ) :
    List (Cl Rd × Lab (Inst Rd)) :=
  (List.range n).map fun p => (c, (inst c, C.prc s c + p + 1))

/-- Replies received by `c` when `s` processes `n` further round messages of `c`. -/
def ents (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (s : Obj) (n : ℕ) : View Obj (LRep Rd (Inst Rd)) :=
  (List.range n).map fun p => (s, ((inst c, C.prc s c + p + 1), C.log s ++ newLabs inst C c s p))

/-- The events: each `s ∈ xs` (in order) processes `d s` round messages of `c`. -/
def dlvs (c : Cl Rd) (xs : List Obj) (d : Obj → ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  xs.flatMap fun s => List.replicate (d s) (.dlv c s)

/-- Result of `dlvs`. -/
def dlvRes (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (xs : List Obj) (d : Obj → ℕ) :
    LCfg Obj Rd V (Inst Rd) :=
  { C with
    log := fun s => if s ∈ xs then C.log s ++ newLabs inst C c s (d s) else C.log s
    cur := Function.update C.cur c (C.cur c ++ xs.flatMap fun s => ents inst C c s (d s))
    prc := fun s c' => if s ∈ xs ∧ c' = c then C.prc s c + d s else C.prc s c' }

omit [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V] in
lemma Cfg.ext' {Msg Rep : Type} {C C' : Cfg Obj Rd V Msg Rep} (h1 : C.log = C'.log) (h2 : C.rnd = C'.rnd)
    (h3 : C.past = C'.past) (h4 : C.cur = C'.cur) (h5 : C.prc = C'.prc) (h6 : C.done = C'.done)
    (h7 : C.wv = C'.wv) : C = C' := by
  cases C; cases C'; simp_all

omit [Fintype Obj] [DecidableEq V] [DecidableEq Obj] [DecidableEq Rd] in
@[simp] lemma LP_reply (s : Obj) (L : List (Cl Rd × Lab (Inst Rd))) (c : Cl Rd) (m : Lab (Inst Rd)) :
    (LPr (Obj := Obj) K N bot inst).reply s L c m = (m, L) := rfl

lemma deliver_dlvRes (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (s : Obj) (n : ℕ)
    (hn : C.prc s c + n < C.rnd c) (hpl : C.rnd c ≤ (C.past c).length + 1) :
    (LPr K N bot inst).deliver (dlvRes inst C c [s] fun _ => n) c s =
      dlvRes inst C c [s] fun _ => n + 1 := by
  have hm : (LPr K N bot inst).msg C.wv c ((C.past c).take (C.prc s c + n)) s =
      (inst c, C.prc s c + n + 1) := by
    rcases c with _ | j <;>
    · simp only [Proto.msg, LPr, LP, List.length_take]
      congr 1; omega
  apply Cfg.ext'
  · funext s'
    by_cases hs : s' = s
    · subst hs
      simp [Proto.deliver, dlvRes, hm, newLabs, List.range_succ]
    · simp [Proto.deliver, dlvRes, hs]
  · rfl
  · rfl
  · funext c'
    by_cases hc : c' = c
    · subst hc; simp [Proto.deliver, dlvRes, hm, ents, List.range_succ, newLabs]
    · simp [Proto.deliver, dlvRes, hc]
  · funext s' c'
    by_cases hs : s' = s
    · subst hs
      by_cases hc : c' = c
      · subst hc; simp [Proto.deliver, dlvRes]; omega
      · simp [Proto.deliver, dlvRes, hc]
    · simp [Proto.deliver, dlvRes, hs]
  · rfl
  · rfl

lemma dlvRes_zero (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (s : Obj) :
    dlvRes inst C c [s] (fun _ => 0) = C := by
  apply Cfg.ext' <;> try rfl
  · funext s'; by_cases hs : s' = s <;> simp [dlvRes, hs, newLabs]
  · funext c'; by_cases hc : c' = c
    · subst hc; simp [dlvRes, ents]
    · simp [dlvRes, hc]
  · funext s' c'; by_cases hs : s' = s <;> by_cases hc : c' = c <;> simp [dlvRes, hs, hc]

lemma cexec_rep (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (s : Obj) (n : ℕ)
    (hn : C.prc s c + n ≤ C.rnd c) (hpl : C.rnd c ≤ (C.past c).length + 1) :
    cexec K N T v₁ bot inst t F C (List.replicate n (.dlv c s)) =
      some (dlvRes inst C c [s] (fun _ => n), []) := by
  induction n with
  | zero => simp [cexec_nil, dlvRes_zero]
  | succ n ih =>
    rw [List.replicate_succ', ← List.nil_append ([] : List (HEv Rd V))]
    refine cexec_append_some K N T v₁ bot inst t F (ih (by omega)) ?_
    apply cexec_single K N T v₁ bot inst t F (show EvCanon T v₁ inst _ (.dlv c s) from trivial)
    have hp : (dlvRes inst C c [s] fun _ => n).prc s c < (dlvRes inst C c [s] fun _ => n).rnd c := by
      simp [dlvRes]; omega
    simp only [Proto.step, hp, ↓reduceIte]
    rw [deliver_dlvRes K N bot inst C c s n (by omega) hpl]

lemma dlvRes_cons (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (s : Obj) (xs : List Obj)
    (hs : s ∉ xs) (d : Obj → ℕ) :
    dlvRes inst (dlvRes inst C c [s] fun _ => d s) c xs d = dlvRes inst C c (s :: xs) d := by
  apply Cfg.ext' <;> try rfl
  · funext s'
    by_cases h1 : s' = s
    · subst h1; simp [dlvRes, hs]
    · by_cases h2 : s' ∈ xs
      · simp [dlvRes, h1, h2, newLabs]
      · simp [dlvRes, h1, h2]
  · funext c'
    by_cases hc : c' = c
    · subst hc
      simp only [dlvRes, Function.update_self, List.flatMap_cons, List.append_assoc]
      congr 2
      apply List.flatMap_congr
      intro s' hs'
      have : s' ≠ s := fun h => hs (h ▸ hs')
      simp [ents, newLabs, this]
    · simp [dlvRes, hc]
  · funext s' c'
    by_cases h1 : s' = s
    · subst h1; by_cases hc : c' = c <;> simp [dlvRes, hs, hc]
    · by_cases h2 : s' ∈ xs <;> by_cases hc : c' = c <;> simp [dlvRes, h1, h2, hc]

/-- **Delivery phase.** Each `s ∈ xs` processes `d s` further round messages of `c`. -/
theorem cexec_dlvs (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (xs : List Obj) (hnd : xs.Nodup)
    (d : Obj → ℕ) (hd : ∀ s ∈ xs, C.prc s c + d s ≤ C.rnd c)
    (hpl : C.rnd c ≤ (C.past c).length + 1) :
    cexec K N T v₁ bot inst t F C (dlvs c xs d) = some (dlvRes inst C c xs d, []) := by
  induction xs generalizing C with
  | nil =>
    simp only [dlvs, List.flatMap_nil, cexec_nil]
    congr 2
    apply Cfg.ext' <;> try rfl
    · funext c'; by_cases hc : c' = c
      · subst hc; simp [dlvRes]
      · simp [dlvRes, hc]
  | cons s xs ih =>
    simp only [List.nodup_cons] at hnd
    have h1 := cexec_rep K N T v₁ bot inst t F C c s (d s) (hd s (by simp)) hpl
    have h2 := ih (dlvRes inst C c [s] fun _ => d s) hnd.2 (fun s' hs' => by
      have : s' ≠ s := fun h => hnd.1 (h ▸ hs')
      simpa [dlvRes, this] using hd s' (by simp [hs'])) (by simpa [dlvRes] using hpl)
    simp only [dlvs, List.flatMap_cons] at h2 ⊢
    rw [← List.nil_append ([] : List (HEv Rd V))]
    rw [cexec_append_some K N T v₁ bot inst t F h1 h2, dlvRes_cons inst C c s xs hnd.1 d]

/-- Result of terminating the current round of `c` (`rounds` = number of rounds of `c`). -/
def nxtRes (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (rounds : ℕ) : LCfg Obj Rd V (Inst Rd) :=
  if C.rnd c = rounds then
    { C with
      past := Function.update C.past c (C.past c ++ [C.cur c])
      cur := Function.update C.cur c []
      done := Function.update C.done c true }
  else
    { C with
      past := Function.update C.past c (C.past c ++ [C.cur c])
      cur := Function.update C.cur c []
      rnd := Function.update C.rnd c (C.rnd c + 1) }

@[simp] lemma nxtRes_log (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (r : ℕ) :
    (nxtRes C c r).log = C.log := by unfold nxtRes; split_ifs <;> rfl
@[simp] lemma nxtRes_prc (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (r : ℕ) :
    (nxtRes C c r).prc = C.prc := by unfold nxtRes; split_ifs <;> rfl
@[simp] lemma nxtRes_wv (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (r : ℕ) :
    (nxtRes C c r).wv = C.wv := by unfold nxtRes; split_ifs <;> rfl

lemma nxtRes_adv (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (r : ℕ) (h : C.rnd c ≠ r) :
    nxtRes C c r = { C with
      past := Function.update C.past c (C.past c ++ [C.cur c])
      cur := Function.update C.cur c []
      rnd := Function.update C.rnd c (C.rnd c + 1) } := by
  simp [nxtRes, h]

lemma nxtRes_done (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (r : ℕ) (h : C.rnd c = r) :
    nxtRes C c r = { C with
      past := Function.update C.past c (C.past c ++ [C.cur c])
      cur := Function.update C.cur c []
      done := Function.update C.done c true } := by
  simp [nxtRes, h]

/-- History emitted by a label `nxt`. -/
def nxtHist (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (rounds : ℕ) : List (HEv Rd V) :=
  if C.rnd c = rounds then
    [match c with
     | .w => .retW
     | .r j => .retR j bot]
  else []

/-- **Round termination.** -/
theorem cexec_nxt (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (hr : 0 < C.rnd c)
    (hd : C.done c = false) (hresp : Fintype.card Obj ≤ t + C.nResp c)
    (hcan : C.cur c = T (inst c, C.rnd c)) :
    cexec K N T v₁ bot inst t F C [.nxt c] =
      some (nxtRes C c ((LPr (Obj := Obj) K N bot inst).rounds c),
        nxtHist bot C c ((LPr (Obj := Obj) K N bot inst).rounds c)) := by
  apply cexec_single K N T v₁ bot inst t F (show EvCanon T v₁ inst C (.nxt c) from hcan)
  simp only [Proto.step, hr, hd, hresp, and_self, ↓reduceIte, nxtRes, nxtHist]
  split_ifs with h
  · rcases c with _ | j <;> rfl
  · rfl

/-- **Invocation of the write.** -/
theorem cexec_invW (C : LCfg Obj Rd V (Inst Rd)) (h0 : C.rnd .w = 0) (hb : v₁ ≠ bot) :
    cexec K N T v₁ bot inst t F C [.invW v₁] =
      some ({ C with rnd := Function.update C.rnd .w 1, wv := v₁ }, [.invW v₁]) := by
  apply cexec_single K N T v₁ bot inst t F (show EvCanon T v₁ inst C (.invW v₁) from rfl)
  simp [Proto.step, h0, hb]

/-- **Invocation of a read.** -/
theorem cexec_invR (C : LCfg Obj Rd V (Inst Rd)) (j : Rd) (h0 : C.rnd (.r j) = 0) :
    cexec K N T v₁ bot inst t F C [.invR j] =
      some ({ C with rnd := Function.update C.rnd (.r j) 1 }, [.invR j]) := by
  apply cexec_single K N T v₁ bot inst t F (show EvCanon T v₁ inst C (.invR j) from trivial)
  simp [Proto.step, h0]

/-- The events: every `s ∈ xs` forges the log `L s`. -/
def forges (xs : List Obj) (L : Obj → List (Cl Rd × Lab (Inst Rd))) : List (LEv Obj Rd V (Inst Rd)) :=
  xs.map fun s => .forge s (L s)

/-- **Forging phase.** -/
theorem cexec_forges (C : LCfg Obj Rd V (Inst Rd)) (xs : List Obj)
    (L : Obj → List (Cl Rd × Lab (Inst Rd))) (hF : ∀ s ∈ xs, s ∈ F) :
    cexec K N T v₁ bot inst t F C (forges xs L) =
      some ({ C with log := fun s => if s ∈ xs then L s else C.log s }, []) := by
  induction xs generalizing C with
  | nil => simp [forges, cexec_nil]
  | cons s xs ih =>
    have h1 : cexec K N T v₁ bot inst t F C [.forge s (L s)] =
        some ({ C with log := Function.update C.log s (L s) }, []) :=
      cexec_single K N T v₁ bot inst t F (show EvCanon T v₁ inst C (.forge s (L s)) from trivial)
        (by simp only [Proto.step, hF s (by simp), ↓reduceIte])
    have h2 := ih { C with log := Function.update C.log s (L s) }
      (fun s' hs' => hF s' (by simp [hs']))
    have h3 := cexec_append_some K N T v₁ bot inst t F h1 h2
    simp only [List.singleton_append, List.append_nil] at h3
    simp only [forges, List.map_cons] at h3 ⊢
    rw [h3]
    congr 2
    apply Cfg.ext' <;> try rfl
    funext s'
    by_cases h1 : s' = s
    · subst h1; by_cases h2 : s' ∈ xs <;> simp [h2]
    · by_cases h2 : s' ∈ xs <;> simp [h1, h2]

/-! ### Fresh clients and frame lemmas -/

/-- Client `c` has not started an operation. -/
def Fresh (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) : Prop :=
  C.rnd c = 0 ∧ C.past c = [] ∧ C.cur c = [] ∧ C.done c = false ∧ ∀ s, C.prc s c = 0

lemma fresh_init (c : Cl Rd) : Fresh (Cfg.init bot : LCfg Obj Rd V (Inst Rd)) c :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

lemma fresh_dlvRes {C : LCfg Obj Rd V (Inst Rd)} {c c' : Cl Rd} (h : Fresh C c') (hne : c' ≠ c)
    (xs : List Obj) (d : Obj → ℕ) : Fresh (dlvRes inst C c xs d) c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, ?_, h4, fun s => ?_⟩
  · simp [dlvRes, hne, h3]
  · simp [dlvRes, hne, h5]

lemma fresh_nxtRes {C : LCfg Obj Rd V (Inst Rd)} {c c' : Cl Rd} (h : Fresh C c') (hne : c' ≠ c)
    (r : ℕ) : Fresh (nxtRes C c r) c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold nxtRes; split_ifs
  · exact ⟨h1, by simp [hne, h2], by simp [hne, h3], by simp [hne, h4], h5⟩
  · exact ⟨by simp [hne, h1], by simp [hne, h2], by simp [hne, h3], h4, h5⟩

lemma fresh_log {C : LCfg Obj Rd V (Inst Rd)} {c' : Cl Rd} (h : Fresh C c')
    (L : Obj → List (Cl Rd × Lab (Inst Rd))) : Fresh { C with log := L } c' := h

lemma fresh_invR {C : LCfg Obj Rd V (Inst Rd)} {c' : Cl Rd} {j : Rd} (h : Fresh C c')
    (hne : c' ≠ .r j) : Fresh { C with rnd := Function.update C.rnd (.r j) 1 } c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by simp [hne, h1], h2, h3, h4, h5⟩

lemma fresh_invW {C : LCfg Obj Rd V (Inst Rd)} {c' : Cl Rd} (h : Fresh C c') (hne : c' ≠ .w) (v : V) :
    Fresh { C with rnd := Function.update C.rnd .w 1, wv := v } c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by simp [hne, h1], h2, h3, h4, h5⟩

/-- Enough responders: all objects outside a set of at most `t` objects replied. -/
lemma card_le_resp (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (p : Obj → Prop) [DecidablePred p]
    (hp : ∀ s, p s → C.prc s c = C.rnd c) (ht : (Finset.univ.filter fun s => ¬ p s).card ≤ t) :
    Fintype.card Obj ≤ t + C.nResp c := by
  have h1 : (Finset.univ.filter p).card + (Finset.univ.filter fun s => ¬ p s).card =
      Fintype.card Obj := by rw [Finset.card_filter_add_card_filter_not]; rfl
  have h2 : (Finset.univ.filter p).card ≤ C.nResp c := by
    apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hp s hs
  omega

/-- **A terminated round**: the objects of `xs` process `d s` messages of `c`, then `c`
terminates the round (canonically). -/
theorem cexec_round (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) (xs : List Obj) (hnd : xs.Nodup)
    (d : Obj → ℕ) (hd : ∀ s ∈ xs, C.prc s c + d s = C.rnd c)
    (hpl : (C.past c).length + 1 = C.rnd c) (hdone : C.done c = false)
    (p : Obj → Prop) [DecidablePred p] (hp : ∀ s, p s → s ∈ xs ∨ C.prc s c = C.rnd c)
    (ht : (Finset.univ.filter fun s => ¬ p s).card ≤ t)
    (hcan : C.cur c ++ xs.flatMap (fun s => ents inst C c s (d s)) = T (inst c, C.rnd c)) :
    cexec K N T v₁ bot inst t F C (dlvs c xs d ++ [.nxt c]) =
      some (nxtRes (dlvRes inst C c xs d) c ((LPr (Obj := Obj) K N bot inst).rounds c),
        nxtHist bot (dlvRes inst C c xs d) c ((LPr (Obj := Obj) K N bot inst).rounds c)) := by
  rw [← List.nil_append (nxtHist _ _ _ _)]
  refine cexec_append_some K N T v₁ bot inst t F
    (cexec_dlvs K N T v₁ bot inst t F C c xs hnd d (fun s hs => (hd s hs).le) (by omega)) ?_
  apply cexec_nxt
  · simp [dlvRes]; omega
  · simpa [dlvRes] using hdone
  · apply card_le_resp t _ c p _ ht
    intro s hs
    by_cases hx : s ∈ xs
    · simp [dlvRes, hx, hd s hx]
    · rcases hp s hs with h | h
      · exact absurd h hx
      · simp [dlvRes, hx, h]
  · simpa [dlvRes] using hcan

end

/-! ### From checked label runs to atomicity facts about an arbitrary protocol -/

section Glue

variable {Msg Rep : Type} (P : Proto Obj Rd V Msg Rep) (T : Lab (Inst Rd) → View Obj (LRep Rd (Inst Rd)))
  (M : Lab (Inst Rd) → Obj → Msg) (v₁ bot : V) (inst : Cl Rd → Inst Rd)

omit [DecidableEq Obj] [Fintype Obj] [DecidableEq V] in
lemma Before.map {h : List (HEv Rd V)} {a b : HEv Rd V} (f : HEv Rd V → HEv Rd V)
    (hb : Before h a b) : Before (h.map f) (f a) (f b) := by
  obtain ⟨i, j, hij, hi, hj⟩ := hb
  exact ⟨i, j, hij, by simp [hi], by simp [hj]⟩

/-- A successful checked label run gives an atomic history of `P` (with canonical read values). -/
theorem atomic_of_cexec (t : ℕ) (hP : P.Atomic t bot) (F : Finset Obj) (hF : F.card ≤ t)
    (hM : IsCanon P M T Prod.fst v₁) (hinst : ∀ c, (inst c).1 = c)
    (σ : List (LEv Obj Rd V (Inst Rd))) (C : LCfg Obj Rd V (Inst Rd)) (h : List (HEv Rd V))
    (hx : cexec P.K P.N T v₁ bot inst t F (Cfg.init bot) σ = some (C, h)) :
    AtomicHist bot (h.map (ihist P M T inst)) := by
  obtain ⟨hc, he⟩ := cexec_spec P.K P.N T v₁ bot inst t F P rfl rfl σ _ C h hx
  exact hP F hF _ _ _ (sim_init P M T Prod.fst v₁ bot inst hinst hM t F σ C h hc he)

variable {P M T inst bot}

omit [DecidableEq Obj] [Fintype Obj] in
/-- Atomicity (2): a read that succeeds the complete write returns the written value. -/
lemma cret_of_after_write {h : List (HEv Rd V)} (hA : AtomicHist bot (h.map (ihist P M T inst)))
    {v : V} (hw : HEv.invW v ∈ h) {j : Rd} {x : V} (hr : HEv.retR j x ∈ h)
    (hb : Before h .retW (.invR j)) : cret P M T inst j = v :=
  hA.after_write j _ v (List.mem_map_of_mem (f := ihist P M T inst) hr)
    (List.mem_map_of_mem (f := ihist P M T inst) hw) (hb.map (ihist P M T inst))

omit [DecidableEq Obj] [Fintype Obj] in
/-- Atomicity (4): a read that succeeds a read returning the written value returns it too. -/
lemma cret_of_after_read {h : List (HEv Rd V)} (hA : AtomicHist bot (h.map (ihist P M T inst)))
    {v : V} (hv : v ≠ bot) (hw : HEv.invW v ∈ h) {j j' : Rd} {x x' : V} (hr' : HEv.retR j' x' ∈ h)
    (hj' : cret P M T inst j' = v) (hr : HEv.retR j x ∈ h)
    (hb : Before h (.retR j' x') (.invR j)) : cret P M T inst j = v := by
  have := hb.map (ihist P M T inst)
  simp only [ihist, hj'] at this
  have hm := List.mem_map_of_mem (f := ihist P M T inst) hr'
  simp only [ihist, hj'] at hm
  exact hA.after_read j' j v _ hv hm
    (List.mem_map_of_mem (f := ihist P M T inst) hw) this
    (List.mem_map_of_mem (f := ihist P M T inst) hr)

omit [DecidableEq Obj] [Fintype Obj] in
/-- Atomicity (1): without a write, reads return `⊥`. -/
lemma cret_of_no_write {h : List (HEv Rd V)} (hA : AtomicHist bot (h.map (ihist P M T inst)))
    (hw : ∀ v, HEv.invW v ∉ h) {j : Rd} {x : V} (hr : HEv.retR j x ∈ h) :
    cret P M T inst j = bot := by
  rcases hA.ret_val j _ (List.mem_map_of_mem (f := ihist P M T inst) hr) with h1 | h1
  · exact h1
  · obtain ⟨e, he, hee⟩ := List.mem_map.1 h1
    cases e <;> simp [ihist] at hee
    subst hee
    exact absurd he (hw _)

end Glue

end Podc.RobustAtomicStorage
