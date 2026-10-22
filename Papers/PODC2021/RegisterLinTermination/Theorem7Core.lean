import Papers.PODC2021.RegisterLinTermination.Theorem6

/-!
# Theorem 7, deterministic core (Lemmas 15–18 and the decision bit)

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Appendix A.

## Per-process bookkeeping

`rep n p γ` replays the events `γ` of process `p` like `procRun`, but a pending operation
remembers the location it was invoked from (`Md.wait l`). The invariant `Good` relates the
location of `p` to the number of operations it has invoked/completed on each register (`cnt`),
the number of its coin flips (`cf`), and the values of some earlier responses (`Data`).
-/

namespace Podc.RegisterLinTermination.Game

open Cslib.SharedMemory List

namespace Thm7

/-- Execution mode with the location of the pending operation. -/
inductive Md where
  | run (l : Loc)
  | wait (l : Loc)

/-- One step of `p`, remembering locations. -/
def step' (n : ℕ) (p : Fin n) : Md → Ev n → Option Md
  | .run l, .inv _ x o => match code n p l with
    | .invoke x' o' _ => if x = x' ∧ o = o' then some (.wait l) else none
    | _ => none
  | .run l, .flip _ b => match code n p l with
    | .flip k => some (.run (k b))
    | _ => none
  | .run l, .noop _ => match code n p l with
    | .done => some (.run l)
    | _ => none
  | .wait l, .ret _ x' v => match code n p l with
    | .invoke x _ k => if x = x' then some (.run (k v)) else none
    | _ => none
  | _, _ => none

/-- Replay the events `γ` (of `p`). -/
def rep (n : ℕ) (p : Fin n) (γ : List (Ev n)) : Option Md :=
  γ.foldl (fun m e => m.bind (fun m => step' n p m e)) (some (.run (initLoc p)))

lemma rep_snoc {n : ℕ} (p : Fin n) (γ : List (Ev n)) (e : Ev n) :
    rep n p (γ ++ [e]) = (rep n p γ).bind (fun m => step' n p m e) := by
  simp [rep, foldl_append]

/-- Forget the location of a pending operation. -/
def toMode (n : ℕ) (p : Fin n) : Md → Mode
  | .run l => .run l
  | .wait l => match code n p l with
    | .invoke x _ k => .wait x k
    | _ => .run l

/-- A mode whose pending location really invokes an operation. -/
def WellMd (n : ℕ) (p : Fin n) : Md → Prop
  | .run _ => True
  | .wait l => ∃ x o k, code n p l = .invoke x o k

lemma step'_wellMd {n : ℕ} (p : Fin n) {md md' : Md} {e : Ev n} (h : step' n p md e = some md') :
    WellMd n p md' := by
  cases md <;> cases e <;> simp only [step'] at h <;> (try split at h) <;> (try simp at h)
  all_goals first
    | (subst h; trivial)
    | (obtain ⟨-, rfl⟩ := h; first | trivial | exact ⟨_, _, _, ‹_›⟩)

lemma step_toMode {n : ℕ} (p : Fin n) (md : Md) (hmd : WellMd n p md) (e : Ev n) :
    pstep n p (toMode n p md) e = (step' n p md e).map (toMode n p) := by
  cases md with
  | run l =>
    cases e <;> simp only [toMode, pstep, step'] <;> (try split) <;> simp_all [toMode]
  | wait l =>
    obtain ⟨x, o, k, hc⟩ := hmd
    cases e <;> simp [toMode, pstep, step', hc]

lemma foldl_toMode {n : ℕ} (p : Fin n) (γ : List (Ev n)) (md : Option Md)
    (hmd : ∀ m, md = some m → WellMd n p m) :
    γ.foldl (fun m e => m.bind (fun m => pstep n p m e)) (md.map (toMode n p)) =
      (γ.foldl (fun m e => m.bind (fun m => step' n p m e)) md).map (toMode n p) := by
  induction γ generalizing md with
  | nil => rfl
  | cons e γ ih =>
    simp only [foldl_cons]
    rw [← ih]
    · congr 1
      cases md with
      | none => rfl
      | some m => simp [step_toMode p m (hmd m rfl)]
    · intro m hm
      cases md with
      | none => simp at hm
      | some m' => simp at hm; exact step'_wellMd p hm

lemma procRun_eq_rep {n : ℕ} (p : Fin n) (α : List (Ev n)) :
    procRun p α = (rep n p (α.filter (fun e => decide (e.proc = p)))).map (toMode n p) := by
  unfold procRun rep
  rw [← foldl_toMode p _ _ (by intro m hm; cases hm; trivial)]
  rfl

/-! ## Operations, responses and coins of one process -/

/-- The operation invoked on `x` by the event, if any. -/
def Ev.invOn {n : ℕ} (x : Reg) : Ev n → Option (RWOp Val)
  | .inv _ y o => if y = x then some o else none
  | _ => none

/-- The response from `x` received at the event, if any. -/
def Ev.retOn {n : ℕ} (x : Reg) : Ev n → Option Val
  | .ret _ y v => if y = x then some v else none
  | _ => none

/-- The operations invoked on `x` in `γ`. -/
def pops {n : ℕ} (x : Reg) (γ : List (Ev n)) : List (RWOp Val) := γ.filterMap (Ev.invOn x)
/-- The responses received from `x` in `γ`. -/
def presps {n : ℕ} (x : Reg) (γ : List (Ev n)) : List Val := γ.filterMap (Ev.retOn x)
/-- The coin flips in `γ`. -/
def pcoins {n : ℕ} (γ : List (Ev n)) : List Bool := γ.filterMap Thm6.coin?

/-! ## The invariant -/

/-- Number of operations on `x` completed by `p` at location `l`. -/
def cnt {n : ℕ} (p : Fin n) : Reg → Loc → ℕ
  | .r1, .h1 j => j - 1
  | .r1, .h2 j | .r1, .h3 j _ | .r1, .h4 j | .r1, .h5 j => j
  | .c, .h1 j | .c, .h2 j | .c, .h3 j _ => if p.val = 0 then j - 1 else 0
  | .c, .h4 j | .c, .h5 j => if p.val = 0 then j else 0
  | .r2, .h1 j | .r2, .h2 j | .r2, .h3 j _ | .r2, .h4 j => 2 * (j - 1)
  | .r2, .h5 j => 2 * (j - 1) + 1
  | .r1, .q1 j => 3 * (j - 1)
  | .r1, .q2 j | .r1, .q3 j => 3 * (j - 1) + 1
  | .r1, .q4 j _ => 3 * (j - 1) + 2
  | .r1, .q5 j _ _ | .r1, .q6 j | .r1, .q7 j | .r1, .q8 j _ => 3 * j
  | .c, .q1 j | .c, .q2 j => 2 * (j - 1)
  | .c, .q3 j | .c, .q4 j _ | .c, .q5 j _ _ => 2 * (j - 1) + 1
  | .c, .q6 j | .c, .q7 j | .c, .q8 j _ => 2 * j
  | .r2, .q1 j | .r2, .q2 j | .r2, .q3 j | .r2, .q4 j _ | .r2, .q5 j _ _ | .r2, .q6 j =>
    3 * (j - 1)
  | .r2, .q7 j => 3 * (j - 1) + 1
  | .r2, .q8 j _ => 3 * (j - 1) + 2
  | _, .done => 0

/-- Number of coin flips of `p` at location `l`. -/
def cf {n : ℕ} (p : Fin n) : Loc → ℕ
  | .h1 j | .h2 j => if p.val = 0 then j - 1 else 0
  | .h3 j _ | .h4 j | .h5 j => if p.val = 0 then j else 0
  | _ => 0

/-- Host locations. -/
def _root_.Podc.RegisterLinTermination.Game.Loc.isHost : Loc → Bool
  | .h1 _ | .h2 _ | .h3 _ _ | .h4 _ | .h5 _ => true
  | _ => false

/-- Locations of `p₀` only. -/
def _root_.Podc.RegisterLinTermination.Game.Loc.isH23 : Loc → Bool
  | .h2 _ | .h3 _ _ => true
  | _ => false

/-- The register a location invokes an operation on. -/
def _root_.Podc.RegisterLinTermination.Game.Act.reg : Act → Option Reg
  | .invoke x _ _ => some x
  | _ => none

/-- `p`'s round-`j` reads of `R1` returned `[c, j]`, `[1 - c, j]` and its read of `C` returned `c`
(the test of lines 24 and 27 passed). -/
def Pass {n : ℕ} (γ : List (Ev n)) (j : ℕ) : Prop :=
  ∃ c, (presps .r1 γ)[3 * (j - 1) + 1]? = some (.pair c j) ∧
    (presps .r1 γ)[3 * (j - 1) + 2]? = some (.pair (!c) j) ∧
    (presps .c γ)[2 * (j - 1) + 1]? = some (.bit c)

/-- Facts about earlier responses recorded in a location. -/
def Data {n : ℕ} (γ : List (Ev n)) : Loc → Prop
  | .q4 j u₁ => (presps .r1 γ)[3 * (j - 1) + 1]? = some u₁
  | .q5 j u₁ u₂ => (presps .r1 γ)[3 * (j - 1) + 1]? = some u₁ ∧
      (presps .r1 γ)[3 * (j - 1) + 2]? = some u₂
  | .q6 j | .q7 j => Pass γ j
  | .q8 j k => Pass γ j ∧ ∃ v, (presps .r2 γ)[3 * (j - 1) + 1]? = some v ∧ k = v.toNat + 1
  | .h3 j b => (pcoins γ)[j - 1]? = some b
  | .h1 j => 2 ≤ j → ∃ v, (presps .r2 γ)[2 * (j - 1) - 1]? = some v ∧ ¬ v.toNat < n - 2
  | _ => True

/-- The invariant at a location `l` (with `pend x = 1` iff an operation on `x` is pending). -/
def LocOK {n : ℕ} (p : Fin n) (γ : List (Ev n)) (l : Loc) (pend : Reg → ℕ) : Prop :=
  1 ≤ l.round ∧ (p.val < 2 ↔ l.isHost) ∧ (l.isH23 → p.val = 0) ∧
    (∀ x, (pops x γ).length = cnt p x l + pend x ∧ (presps x γ).length = cnt p x l) ∧
    (pcoins γ).length = cf p l ∧ Data γ l

/-- The per-process invariant. -/
def Good {n : ℕ} (p : Fin n) (γ : List (Ev n)) : Prop :=
  ∀ md, rep n p γ = some md → match md with
    | .run l => l = .done ∨ LocOK p γ l (fun _ => 0)
    | .wait l => LocOK p γ l (fun x => if (code n p l).reg = some x then 1 else 0)

@[simp] lemma pops_snoc {n : ℕ} (x : Reg) (γ : List (Ev n)) (e : Ev n) :
    pops x (γ ++ [e]) = pops x γ ++ (Ev.invOn x e).toList := by
  cases h : Ev.invOn x e <;> simp [pops, h]

@[simp] lemma presps_snoc {n : ℕ} (x : Reg) (γ : List (Ev n)) (e : Ev n) :
    presps x (γ ++ [e]) = presps x γ ++ (Ev.retOn x e).toList := by
  cases h : Ev.retOn x e <;> simp [presps, h]

@[simp] lemma pcoins_snoc {n : ℕ} (γ : List (Ev n)) (e : Ev n) :
    pcoins (γ ++ [e]) = pcoins γ ++ (Thm6.coin? e).toList := by
  cases h : Thm6.coin? e <;> simp [pcoins, h]

lemma data_congr {n : ℕ} {γ γ' : List (Ev n)} (h : ∀ x, presps x γ' = presps x γ)
    (hc : pcoins γ' = pcoins γ) (l : Loc) : Data γ' l ↔ Data γ l := by
  cases l <;> simp [Data, Pass, h, hc]

lemma good_nil {n : ℕ} (p : Fin n) : Good p ([] : List (Ev n)) := by
  intro md hmd
  simp only [rep, foldl_nil, Option.some.injEq] at hmd
  subst hmd
  right
  unfold initLoc
  split_ifs with hp <;>
    simp [LocOK, Loc.round, Loc.isHost, Loc.isH23, hp, cnt, cf, Data, pops, presps, pcoins] <;>
    intro x <;> cases x <;> simp

lemma getElem?_snoc_len {X : Type} {l : List X} {i : ℕ} (a : X) (h : l.length = i) :
    (l ++ [a])[i]? = some a := by
  subst h; simp

lemma getElem?_snoc_lt {X : Type} {l : List X} {i : ℕ} (a : X) (h : i < l.length) :
    (l ++ [a])[i]? = l[i]? := getElem?_append_left h

lemma presps_ret_at {n : ℕ} {γ : List (Ev n)} {q : Fin n} {x : Reg} {v : Val} {i : ℕ}
    (h : (presps x γ).length = i) : (presps x (γ ++ [.ret q x v]))[i]? = some v := by
  simp [Ev.retOn, ← h]

lemma cnt_step {n : ℕ} {p q : Fin n} {γ : List (Ev n)} {x0 : Reg} {v : Val} {l l' : Loc}
    (hcnt : ∀ y, (pops y γ).length = cnt p y l + (if x0 = y then 1 else 0) ∧
      (presps y γ).length = cnt p y l)
    (h : ∀ y, cnt p y l' = cnt p y l + (if x0 = y then 1 else 0)) :
    ∀ y, (pops y (γ ++ [.ret q x0 v])).length = cnt p y l' + (fun _ => 0) y ∧
      (presps y (γ ++ [.ret q x0 v])).length = cnt p y l' := by
  intro y
  obtain ⟨h1, h2⟩ := hcnt y
  by_cases hy : x0 = y
  · subst hy; simp_all [Ev.invOn, Ev.retOn]
  · simp_all [Ev.invOn, Ev.retOn]

lemma good_snoc {n : ℕ} (p : Fin n) (γ : List (Ev n)) (e : Ev n) (h : Good p γ) :
    Good p (γ ++ [e]) := by
  intro md' hmd'
  rw [rep_snoc] at hmd'
  cases hr : rep n p γ with
  | none => simp [hr] at hmd'
  | some md =>
    rw [hr, Option.bind_some] at hmd'
    have hg := h md hr
    cases md with
    | run l =>
      rcases hg with rfl | hok
      · cases e <;> simp [step', code] at hmd'
        subst hmd'; left; rfl
      cases e with
      | inv q x o =>
        simp only [step'] at hmd'
        cases hc : code n p l <;> simp only [hc] at hmd' <;> try simp at hmd'
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hmd'
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok
        refine ⟨h1, h2, h3, fun y => ?_, by simpa [Thm6.coin?] using h5,
          (data_congr (fun y => by simp [Ev.retOn]) (by simp [Thm6.coin?]) l).2 h6⟩
        obtain ⟨h4a, h4b⟩ := h4 y
        simp only [hc, Act.reg, Option.some.injEq]
        by_cases hxy : x = y
        · subst hxy; simp [Ev.invOn, Ev.retOn, h4a, h4b]
        · simp [Ev.invOn, Ev.retOn, h4a, h4b, hxy]
      | flip q b =>
        simp only [step'] at hmd'
        cases hc : code n p l <;> simp only [hc] at hmd' <;> try simp at hmd'
        subst hmd'
        right
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok
        cases l <;> simp [code] at hc
        rename_i j
        subst hc
        have hp0 : p.val = 0 := h3 rfl
        refine ⟨h1, h2, fun _ => hp0, fun y => ?_, ?_, ?_⟩
        · obtain ⟨h4a, h4b⟩ := h4 y
          cases y <;> simp_all [cnt, Ev.invOn, Ev.retOn]
        · simp [Loc.round] at h1; simp_all [cf, Thm6.coin?]
        · simp_all [Data, cf, Thm6.coin?]
      | noop q =>
        simp only [step'] at hmd'
        cases hc : code n p l <;> simp only [hc] at hmd' <;> try simp at hmd'
        cases l <;> simp [code] at hc
        exact absurd hok.1 (by simp [Loc.round])
      | ret q x v => simp [step'] at hmd'
    | wait l =>
      cases e with
      | ret q x v =>
        simp only [step'] at hmd'
        cases hc : code n p l with
        | invoke x0 o k =>
          simp only [hc] at hmd'
          split_ifs at hmd' with hx
          cases hmd'; subst hx
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
          have hcnt : ∀ y, (pops y γ).length = cnt p y l + (if x0 = y then 1 else 0) ∧
              (presps y γ).length = cnt p y l := by
            intro y; have := h4 y; simpa [hc, Act.reg] using this
          have hco : pcoins (γ ++ [.ret q x0 v]) = pcoins γ := by simp [Thm6.coin?]
          have hpr : ∀ y, y ≠ x0 → presps y (γ ++ [.ret q x0 v]) = presps y γ := by
            intro y hy; simp [Ev.retOn, Ne.symm hy]
          have hlen := (hcnt x0).2
          show k v = .done ∨ LocOK p (γ ++ [.ret q x0 v]) (k v) (fun _ => 0)
          cases l <;> simp only [code, Act.invoke.injEq] at hc <;> (try simp at hc) <;>
            obtain ⟨rfl, rfl, rfl⟩ := hc <;> simp only [Loc.round] at h1 <;> beta_reduce
          · -- h1
            right
            split_ifs with hp
            · exact ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2, fun _ => hp,
                cnt_step hcnt (by
                  intro y; cases y <;> (try simp [cnt, hp]) <;> omega),
                by simpa [hco, cf, hp] using h5, trivial⟩
            · exact ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
                by simp [Loc.isH23], cnt_step hcnt (by
                  intro y; cases y <;> (try simp [cnt, hp]) <;> omega),
                by simpa [hco, cf, hp] using h5, trivial⟩
          · -- h3
            right
            exact ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23], cnt_step hcnt (by
                intro y; cases y <;> (try simp [cnt, h3 rfl]) <;> omega),
              by simpa [hco, cf] using h5, trivial⟩
          · -- h4
            right
            exact ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23], cnt_step hcnt (by intro y; cases y <;> simp [cnt]),
              by simpa [hco, cf] using h5, trivial⟩
          · -- h5
            split_ifs with hv
            · left; rfl
            · right
              refine ⟨by simp [Loc.round], by simpa [Loc.isHost] using h2,
                by simp [Loc.isH23], cnt_step hcnt (by
                  intro y; cases y <;> (try simp [cnt]) <;> omega),
                by simp only [hco, cf] at h5 ⊢; split_ifs at h5 ⊢ <;> omega, ?_⟩
              intro _
              refine ⟨v, ?_, hv⟩
              simp only [cnt] at hlen
              exact presps_ret_at (by omega)
          · -- q1
            right
            exact ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23], cnt_step hcnt (by intro y; cases y <;> simp [cnt]),
              by simpa [hco, cf] using h5, trivial⟩
          · -- q2
            right
            exact ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23], cnt_step hcnt (by intro y; cases y <;> simp [cnt]),
              by simpa [hco, cf] using h5, trivial⟩
          · -- q3
            right
            refine ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23], cnt_step hcnt (by intro y; cases y <;> simp [cnt]),
              by simpa [hco, cf] using h5, ?_⟩
            simp only [cnt] at hlen
            exact presps_ret_at (by omega)
          · -- q4
            right
            refine ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23],
              cnt_step hcnt (by intro y; cases y <;> (try simp [cnt]) <;> omega),
              by simpa [hco, cf] using h5, ?_, ?_⟩
            · simp only [cnt] at hlen
              simp only [Data] at h6
              simp only [presps_snoc, Ev.retOn, ite_true, Option.toList_some]
              rw [getElem?_snoc_lt _ (by omega)]; exact h6
            · simp only [cnt] at hlen
              exact presps_ret_at (by omega)
          · -- q5
            rename_i j u₁ u₂
            by_cases hp : passes j u₁ u₂ v = true
            · right
              simp only [hp, ite_true]
              refine ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
                by simp [Loc.isH23],
              cnt_step hcnt (by intro y; cases y <;> (try simp [cnt]) <;> omega),
                by simpa [hco, cf] using h5, ?_⟩
              simp only [Data] at h6 ⊢
              obtain ⟨hu₁, hu₂⟩ := h6
              unfold passes at hp
              split at hp
              · rename_i c
                simp only [decide_eq_true_eq] at hp
                obtain ⟨rfl, rfl⟩ := hp
                refine ⟨c, ?_, ?_, ?_⟩
                · rw [hpr _ (by simp)]; exact hu₁
                · rw [hpr _ (by simp)]; exact hu₂
                · simp only [cnt] at hlen
                  exact presps_ret_at (by omega)
              · simp at hp
            · left; simp [hp]
          · -- q6
            right
            refine ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23], cnt_step hcnt (by intro y; cases y <;> simp [cnt]),
              by simpa [hco, cf] using h5, ?_⟩
            simp only [Data, Pass] at h6 ⊢
            rwa [hpr _ (by simp), hpr _ (by simp)]
          · -- q7
            right
            refine ⟨by simp [Loc.round]; omega, by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23], cnt_step hcnt (by intro y; cases y <;> simp [cnt]),
              by simpa [hco, cf] using h5, ?_, v, ?_, rfl⟩
            · simp only [Data, Pass] at h6 ⊢
              rwa [hpr _ (by simp), hpr _ (by simp)]
            · simp only [cnt] at hlen
              exact presps_ret_at (by omega)
          · -- q8
            right
            exact ⟨by simp [Loc.round], by simpa [Loc.isHost] using h2,
              by simp [Loc.isH23],
              cnt_step hcnt (by intro y; cases y <;> (try simp [cnt]) <;> omega),
              by simpa [hco, cf] using h5, trivial⟩
        | _ => simp [hc] at hmd'
      | _ => simp [step'] at hmd'

lemma good (n : ℕ) (p : Fin n) (γ : List (Ev n)) : Good p γ := by
  induction γ using List.reverseRecOn with
  | nil => exact good_nil p
  | append_singleton γ e ih => exact good_snoc p γ e ih

lemma rep_wellMd {n : ℕ} (p : Fin n) (γ : List (Ev n)) {md : Md} (h : rep n p γ = some md) :
    WellMd n p md := by
  induction γ using List.reverseRecOn generalizing md with
  | nil => simp [rep] at h; subst h; trivial
  | append_singleton γ e _ =>
    rw [rep_snoc] at h
    cases hr : rep n p γ with
    | none => simp [hr] at h
    | some m => rw [hr, Option.bind_some] at h; exact step'_wellMd p h

/-! ## Time -/

/-- The events of `p` among the first `t` events of `α`. -/
def tr {n : ℕ} (α : List (Ev n)) (p : Fin n) (t : ℕ) : List (Ev n) :=
  (α.take t).filter (fun e => decide (e.proc = p))

lemma tr_succ {n : ℕ} (α : List (Ev n)) (p : Fin n) (t : ℕ) :
    tr α p (t + 1) = tr α p t ++ (α[t]?.toList.filter (fun e => decide (e.proc = p))) := by
  simp [tr, take_add_one, filter_append]

lemma tr_prefix {n : ℕ} (α : List (Ev n)) (p : Fin n) {t t' : ℕ} (h : t ≤ t') :
    tr α p t <+: tr α p t' := by
  unfold tr
  have : α.take t = (α.take t').take t := by rw [take_take, Nat.min_eq_left h]
  rw [this]
  exact (take_prefix _ _).filter _

lemma getElem?_of_prefix {X : Type} {l₁ l₂ : List X} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) : l₂[i]? = l₁[i]? := by
  obtain ⟨u, rfl⟩ := h; exact getElem?_append_left hi

lemma pops_prefix {n : ℕ} (x : Reg) {γ γ' : List (Ev n)} (h : γ <+: γ') :
    pops x γ <+: pops x γ' := h.filterMap _

lemma presps_prefix {n : ℕ} (x : Reg) {γ γ' : List (Ev n)} (h : γ <+: γ') :
    presps x γ <+: presps x γ' := h.filterMap _

lemma pcoins_prefix {n : ℕ} {γ γ' : List (Ev n)} (h : γ <+: γ') :
    pcoins γ <+: pcoins γ' := h.filterMap _

/-- First time `p` invokes its `k`-th operation on `x`. -/
lemma reach_inv {n : ℕ} {α : List (Ev n)} {p : Fin n}
    (hV : ∀ t, (rep n p (tr α p t)).isSome) {x : Reg} {k T : ℕ}
    (hk : k < (pops x (tr α p T)).length) :
    ∃ t l o kk, t < T ∧ rep n p (tr α p t) = some (.run l) ∧ code n p l = .invoke x o kk ∧
      (pops x (tr α p t)).length = k ∧ rep n p (tr α p (t + 1)) = some (.wait l) ∧
      (pops x (tr α p T))[k]? = some o := by
  classical
  have hex : ∃ t, k < (pops x (tr α p t)).length := ⟨T, hk⟩
  have h₁ : k < (pops x (tr α p (Nat.find hex))).length := Nat.find_spec hex
  have hT : Nat.find hex ≤ T := Nat.find_min' hex hk
  have h0 : Nat.find hex ≠ 0 := by
    intro h; rw [h] at h₁; simp [tr, pops] at h₁
  obtain ⟨t, ht⟩ : ∃ t, Nat.find hex = t + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ht] at h₁ hT
  have hnt : ¬ k < (pops x (tr α p t)).length := Nat.find_min hex (by omega)
  have hsome := hV (t + 1)
  rw [tr_succ] at h₁ hsome
  cases ha : α[t]? with
  | none => simp [ha] at h₁; omega
  | some e =>
    by_cases hep : e.proc = p
    · have hsplit : tr α p (t + 1) = tr α p t ++ [e] := by rw [tr_succ, ha]; simp [hep]
      simp only [ha, Option.toList_some, filter_cons, hep, decide_true, ite_true,
        filter_nil] at h₁ hsome
      rw [pops_snoc] at h₁
      rw [rep_snoc] at hsome
      cases hr : rep n p (tr α p t) with
      | none => simp [hr] at hsome
      | some md =>
        rw [hr] at hsome
        cases e with
        | inv q y o =>
          by_cases hyx : y = x
          · subst hyx
            simp only [Ev.invOn, ite_true, Option.toList_some, length_append, length_singleton]
              at h₁
            have hlen : (pops y (tr α p t)).length = k := by omega
            cases md with
            | run l =>
              simp only [Option.bind_some, step'] at hsome
              cases hc : code n p l with
              | invoke x' o' kk =>
                simp only [hc] at hsome
                split_ifs at hsome with hxo
                · obtain ⟨rfl, rfl⟩ := hxo
                  refine ⟨t, l, o, kk, by omega, hr, hc, hlen, ?_, ?_⟩
                  · rw [hsplit, rep_snoc, hr]; simp [step', hc]
                  · rw [getElem?_of_prefix (pops_prefix y (tr_prefix α p hT))
                      (by rw [hsplit, pops_snoc]; simp [Ev.invOn]; omega), hsplit, pops_snoc]
                    simp [Ev.invOn, ← hlen]
                · simp at hsome
              | _ => simp [hc] at hsome
            | wait l => simp [step'] at hsome
          · simp [Ev.invOn, hyx] at h₁; omega
        | _ => simp [Ev.invOn] at h₁; omega
    · simp [ha, hep] at h₁; omega

/-- First time `p` receives the response of its `k`-th operation on `x`. -/
lemma reach_ret {n : ℕ} {α : List (Ev n)} {p : Fin n}
    (hV : ∀ t, (rep n p (tr α p t)).isSome) {x : Reg} {k T : ℕ}
    (hk : k < (presps x (tr α p T)).length) :
    ∃ t l o kk v, t < T ∧ rep n p (tr α p t) = some (.wait l) ∧ code n p l = .invoke x o kk ∧
      (presps x (tr α p t)).length = k ∧ rep n p (tr α p (t + 1)) = some (.run (kk v)) ∧
      (presps x (tr α p T))[k]? = some v := by
  classical
  have hex : ∃ t, k < (presps x (tr α p t)).length := ⟨T, hk⟩
  have h₁ : k < (presps x (tr α p (Nat.find hex))).length := Nat.find_spec hex
  have hT : Nat.find hex ≤ T := Nat.find_min' hex hk
  have h0 : Nat.find hex ≠ 0 := by
    intro h; rw [h] at h₁; simp [tr, presps] at h₁
  obtain ⟨t, ht⟩ : ∃ t, Nat.find hex = t + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ht] at h₁ hT
  have hnt : ¬ k < (presps x (tr α p t)).length := Nat.find_min hex (by omega)
  have hsome := hV (t + 1)
  rw [tr_succ] at h₁ hsome
  cases ha : α[t]? with
  | none => simp [ha] at h₁; omega
  | some e =>
    by_cases hep : e.proc = p
    · have hsplit : tr α p (t + 1) = tr α p t ++ [e] := by rw [tr_succ, ha]; simp [hep]
      simp only [ha, Option.toList_some, filter_cons, hep, decide_true, ite_true,
        filter_nil] at h₁ hsome
      rw [presps_snoc] at h₁
      rw [rep_snoc] at hsome
      cases hr : rep n p (tr α p t) with
      | none => simp [hr] at hsome
      | some md =>
        rw [hr] at hsome
        cases e with
        | ret q y v =>
          by_cases hyx : y = x
          · subst hyx
            simp only [Ev.retOn, ite_true, Option.toList_some, length_append, length_singleton]
              at h₁
            have hlen : (presps y (tr α p t)).length = k := by omega
            cases md with
            | wait l =>
              simp only [Option.bind_some, step'] at hsome
              cases hc : code n p l with
              | invoke x' o' kk =>
                simp only [hc] at hsome
                split_ifs at hsome with hxo
                · subst hxo
                  refine ⟨t, l, o', kk, v, by omega, hr, hc, hlen, ?_, ?_⟩
                  · rw [hsplit, rep_snoc, hr]; simp [step', hc]
                  · rw [getElem?_of_prefix (presps_prefix _ (tr_prefix α p hT))
                      (by rw [hsplit, presps_snoc]; simp [Ev.retOn]; omega), hsplit, presps_snoc]
                    simp [Ev.retOn, ← hlen]
                · simp at hsome
              | _ => simp [hc] at hsome
            | run l => simp [step'] at hsome
          · simp [Ev.retOn, hyx] at h₁; omega
        | _ => simp [Ev.retOn] at h₁; omega
    · simp [ha, hep] at h₁; omega

/-! ## Histories of registers -/

lemma filterMap_filter' {X Y : Type} (f : X → Option Y) (q : X → Bool) (l : List X) :
    (l.filter q).filterMap f = l.filterMap (fun e => if q e then f e else none) := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : q a <;> simp [h, ih, filterMap_cons]

lemma toLabel_invOf {n : ℕ} (x : Reg) (p : Fin n) (e : Ev n) :
    (Ev.toLabel x e).bind (Label.invOf p) =
      if decide (e.proc = p) then Ev.invOn x e else none := by
  cases e <;> simp only [Ev.toLabel, Ev.invOn, Ev.proc] <;> split_ifs <;>
    simp_all [Label.invOf] <;> rename_i h <;>
    first | exact of_decide_eq_true h | exact of_decide_eq_false h

lemma toLabel_retOf {n : ℕ} (x : Reg) (p : Fin n) (e : Ev n) :
    (Ev.toLabel x e).bind (Label.retOf p) =
      if decide (e.proc = p) then Ev.retOn x e else none := by
  cases e <;> simp only [Ev.toLabel, Ev.retOn, Ev.proc] <;> split_ifs <;>
    simp_all [Label.retOf] <;> rename_i h <;>
    first | exact of_decide_eq_true h | exact of_decide_eq_false h

lemma opsOf_hist {n : ℕ} (x : Reg) (α : List (Ev n)) (p : Fin n) :
    opsOf (hist x α) p = pops x (α.filter (fun e => decide (e.proc = p))) := by
  rw [pops, filterMap_filter', opsOf, hist, filterMap_filterMap]
  congr 1; funext e; exact toLabel_invOf x p e

lemma respsOf_hist {n : ℕ} (x : Reg) (α : List (Ev n)) (p : Fin n) :
    respsOf (hist x α) p = presps x (α.filter (fun e => decide (e.proc = p))) := by
  rw [presps, filterMap_filter', respsOf, hist, filterMap_filterMap]
  congr 1; funext e; exact toLabel_retOf x p e

lemma hist_append {n : ℕ} (x : Reg) (α β : List (Ev n)) :
    hist x (α ++ β) = hist x α ++ hist x β := by simp [hist]

section Fixed

variable {n : ℕ} (α : List (Ev n))

/-- The `a.2`-th operation of `a.1` on `x` has been invoked among the first `t` events. -/
def Iv (x : Reg) (a : OpId (Fin n)) (t : ℕ) : Prop := a.2 < (pops x (tr α a.1 t)).length
/-- The `a.2`-th operation of `a.1` on `x` has completed among the first `t` events. -/
def Cp (x : Reg) (a : OpId (Fin n)) (t : ℕ) : Prop := a.2 < (presps x (tr α a.1 t)).length

variable {α}

lemma invoked_take_iff {x : Reg} {a : OpId (Fin n)} {t : ℕ} :
    Invoked (hist x (α.take t)) a ↔ Iv α x a t := by
  simp [Invoked, Iv, opsOf_hist, tr]

lemma completed_take_iff {x : Reg} {a : OpId (Fin n)} {t : ℕ} :
    Completed (hist x (α.take t)) a ↔ Cp α x a t := by
  simp [Completed, Cp, respsOf_hist, tr]

lemma opOf_hist {x : Reg} {a : OpId (Fin n)} :
    opOf (hist x α) a = (pops x (tr α a.1 α.length))[a.2]? := by
  simp [opOf, opsOf_hist, tr]

lemma respOf_hist {x : Reg} {a : OpId (Fin n)} :
    respOf (hist x α) a = (presps x (tr α a.1 α.length))[a.2]? := by
  simp [respOf, respsOf_hist, tr]

lemma Iv.mono {x : Reg} {a : OpId (Fin n)} {t t' : ℕ} (h : Iv α x a t) (ht : t ≤ t') :
    Iv α x a t' := lt_of_lt_of_le h (pops_prefix x (tr_prefix α a.1 ht)).length_le

lemma Cp.mono {x : Reg} {a : OpId (Fin n)} {t t' : ℕ} (h : Cp α x a t) (ht : t ≤ t') :
    Cp α x a t' := lt_of_lt_of_le h (presps_prefix x (tr_prefix α a.1 ht)).length_le

lemma Iv.of_le {x : Reg} {p : Fin n} {k k' t : ℕ} (h : Iv α x (p, k') t) (hk : k ≤ k') :
    Iv α x (p, k) t := by unfold Iv at *; simp only at *; omega

lemma Cp.of_le {x : Reg} {p : Fin n} {k k' t : ℕ} (h : Cp α x (p, k') t) (hk : k ≤ k') :
    Cp α x (p, k) t := by unfold Cp at *; simp only at *; omega

lemma lt_of_Iv {x : Reg} {a : OpId (Fin n)} {t t' : ℕ} (h : ¬ Iv α x a t)
    (h' : Iv α x a t') : t < t' := by
  by_contra hc; exact h (h'.mono (by omega))

/-- Real-time order from a time at which `a` has completed and `b` is not invoked. -/
lemma prec_of_time {x : Reg} {a b : OpId (Fin n)} {t : ℕ} (ha : Cp α x a t)
    (hb : ¬ Iv α x b t) : Precedes (hist x α) a b :=
  ⟨hist x (α.take t), hist x (α.drop t), by rw [← hist_append, take_append_drop],
    completed_take_iff.2 ha, fun h => hb (invoked_take_iff.1 h)⟩

/-- If `a` is linearized before `b`, `a` is invoked whenever `b` has completed. -/
lemma lin_time {x : Reg} {L : List (OpId (Fin n) × RWOp Val)}
    (hL : IsLinearization (hist x α) L) {a b : OpId (Fin n)}
    (hab : [a, b].Sublist (L.map Prod.fst)) {t : ℕ} (hb : Cp α x b t) : Iv α x a t := by
  by_contra h
  have := hL.realtime b a (prec_of_time hb h) (hab.subset (by simp))
  exact not_sublist_pair_both hL.nodup hab this

end Fixed

/-! ## Sublists of pairs -/

lemma pair_trans {X : Type} {l : List X} (hl : l.Nodup) {a b c : X} (h₁ : [a, b].Sublist l)
    (h₂ : [b, c].Sublist l) : [a, c].Sublist l := by
  obtain ⟨r₁, r₂, rfl, ha, hb⟩ := sublist_pair_iff.1 h₁
  obtain ⟨s₁, s₂, hs, hb', hc⟩ := sublist_pair_iff.1 h₂
  rcases append_eq_append_iff.1 hs with ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩
  · exact sublist_pair_iff.2 ⟨r₁, m ++ s₂, by simp, ha, by simp [hc]⟩
  · exfalso
    rw [nodup_append] at hl
    exact hl.2.2 b (by simp [hb']) b hb rfl

/-- In a linearization of a register, the last write before a read of a non-initial value. -/
theorem last_write {P V : Type} [DecidableEq P] {v₀ : V} {α : List (Label P (register V v₀))}
    {S : List (OpId P × RWOp V)} (hS : IsLinearization α S) {r : OpId P} {v : V}
    (hr : respOf α r = some v) (hrop : opOf α r = some .read) (hv : v ≠ v₀) :
    ∃ w, (w, RWOp.write v) ∈ S ∧ [w, r].Sublist (S.map Prod.fst) ∧
      ∀ u x, (u, RWOp.write x) ∈ S → [u, r].Sublist (S.map Prod.fst) → u ≠ w →
        [u, w].Sublist (S.map Prod.fst) := by
  have hrS : r ∈ S.map Prod.fst := hS.complete r (Completed.of_respOf_eq_some hr)
  obtain ⟨⟨r', o⟩, hy, rfl⟩ := mem_map.1 hrS
  obtain ⟨S₁, S₂, rfl⟩ := append_of_mem hy
  have ho : o = .read := by
    have := hS.op_eq _ hy; rw [hrop] at this; exact (Option.some.inj this).symm
  subst ho
  have hseq := (seqOK_append (α := α) (register V v₀).init S₁ _).1 hS.seq
  have hq : (register V v₀).runOps v₀ (S₁.map Prod.snd) = v := by
    have := hseq.2.1 v hr; simpa using this
  obtain ⟨os₁, os₂, hsplit, hnw⟩ := register_runOps_eq _ hq hv
  obtain ⟨A₁, R₁, hA, hAm, hRm⟩ := map_eq_append_iff.1 hsplit
  obtain ⟨e, R, rfl, he, hRm'⟩ := map_eq_cons_iff.1 hRm
  subst hAm hRm'
  obtain ⟨ew, ev⟩ := e
  simp only at he; subst he
  have hnd := hS.nodup
  refine ⟨ew, by rw [hA]; simp, ?_, ?_⟩
  · rw [hA]
    simp only [map_append, map_cons, append_assoc, cons_append]
    exact sublist_pair_iff.2 ⟨A₁.map Prod.fst ++ [ew], R.map Prod.fst ++ r' :: S₂.map Prod.fst,
      by simp, by simp, by simp⟩
  · intro u x hu hur hne
    rw [map_append, map_cons] at hnd hur
    have hu₁ := mem_left_of_sublist_pair hnd hur
    obtain ⟨⟨u', x'⟩, hy', rfl⟩ := mem_map.1 hu₁
    have hx' : x' = .write x := by
      have h1 := hS.op_eq _ (mem_append_left _ hy')
      have h2 := hS.op_eq _ hu
      rw [h1] at h2; exact Option.some.inj h2
    subst hx'
    rw [hA] at hy'
    rcases mem_append.1 hy' with hy' | hy'
    · rw [hA]
      simp only [map_append, map_cons, append_assoc, cons_append]
      exact sublist_pair_iff.2 ⟨A₁.map Prod.fst, ew :: (R.map Prod.fst ++ r' :: S₂.map Prod.fst),
        by simp, mem_map_of_mem hy', by simp⟩
    · rcases mem_cons.1 hy' with h | h
      · cases h; exact absurd rfl hne
      · have : (RWOp.write x : RWOp V).isWrite = false := hnw _ (mem_map.2 ⟨_, h, rfl⟩)
        simp at this

/-! ## Facts about single processes -/

section Facts

variable {n : ℕ} {α : List (Ev n)}

/-- The operation of instance `a` on `x` in `α`. -/
def opn (α : List (Ev n)) (x : Reg) (a : OpId (Fin n)) : Option (RWOp Val) :=
  (pops x (tr α a.1 α.length))[a.2]?
/-- The response of instance `a` on `x` in `α`. -/
def rsp (α : List (Ev n)) (x : Reg) (a : OpId (Fin n)) : Option Val :=
  (presps x (tr α a.1 α.length))[a.2]?

lemma tr_prefix_final (α : List (Ev n)) (p : Fin n) (t : ℕ) : tr α p t <+: tr α p α.length := by
  unfold tr; rw [take_length]; exact (take_prefix _ _).filter _

lemma Iv.final {x : Reg} {a : OpId (Fin n)} {t : ℕ} (h : Iv α x a t) : Iv α x a α.length :=
  lt_of_lt_of_le h (pops_prefix x (tr_prefix_final α a.1 t)).length_le

lemma Cp.final {x : Reg} {a : OpId (Fin n)} {t : ℕ} (h : Cp α x a t) : Cp α x a α.length :=
  lt_of_lt_of_le h (presps_prefix x (tr_prefix_final α a.1 t)).length_le

lemma rsp_of_time {x : Reg} {p : Fin n} {k t : ℕ} {v : Val}
    (h : (presps x (tr α p t))[k]? = some v) : rsp α x (p, k) = some v := by
  have hk : k < (presps x (tr α p t)).length := (List.getElem?_eq_some_iff.1 h).1
  rw [rsp, getElem?_of_prefix (presps_prefix x (tr_prefix_final α p t)) hk, h]

lemma pcoins_of_time {p : Fin n} {k t : ℕ} {b : Bool}
    (h : (pcoins (tr α p t))[k]? = some b) : (pcoins (tr α p α.length))[k]? = some b := by
  have hk : k < (pcoins (tr α p t)).length := (List.getElem?_eq_some_iff.1 h).1
  rw [getElem?_of_prefix (pcoins_prefix (tr_prefix_final α p t)) hk, h]

lemma locOK_run {p : Fin n} {γ : List (Ev n)} {l : Loc} (h : rep n p γ = some (.run l))
    (hl : l ≠ .done) : LocOK p γ l (fun _ => 0) := by
  rcases (good n p γ _ h : l = .done ∨ _) with h' | h'
  · exact absurd h' hl
  · exact h'

lemma locOK_wait {p : Fin n} {γ : List (Ev n)} {l : Loc} (h : rep n p γ = some (.wait l)) :
    LocOK p γ l (fun x => if (code n p l).reg = some x then 1 else 0) := good n p γ _ h

/-- The location from which `p` invoked its `k`-th operation on `x`. -/
lemma at_inv (hV : ∀ p t, (rep n p (tr α p t)).isSome) {p : Fin n} {x : Reg} {k : ℕ}
    (hk : Iv α x (p, k) α.length) :
    ∃ t l o kk, rep n p (tr α p t) = some (.run l) ∧ code n p l = .invoke x o kk ∧
      cnt p x l = k ∧ LocOK p (tr α p t) l (fun _ => 0) ∧ opn α x (p, k) = some o := by
  obtain ⟨t, l, o, kk, -, hr, hc, hlen, -, hop⟩ := reach_inv (hV p) hk
  have hl : l ≠ .done := by rintro rfl; simp [code] at hc
  have hok := locOK_run hr hl
  refine ⟨t, l, o, kk, hr, hc, ?_, hok, hop⟩
  have := (hok.2.2.2.1 x).1; simp only [add_zero] at this; omega

/-- The location from which `p` invoked its `k`-th operation on `x`, which has completed. -/
lemma at_ret (hV : ∀ p t, (rep n p (tr α p t)).isSome) {p : Fin n} {x : Reg} {k : ℕ}
    (hk : Cp α x (p, k) α.length) :
    ∃ t l o kk v, rep n p (tr α p t) = some (.wait l) ∧ code n p l = .invoke x o kk ∧
      cnt p x l = k ∧ rep n p (tr α p (t + 1)) = some (.run (kk v)) ∧
      rsp α x (p, k) = some v := by
  obtain ⟨t, l, o, kk, v, -, hr, hc, hlen, hr', hv⟩ := reach_ret (hV p) hk
  have hok := locOK_wait hr
  refine ⟨t, l, o, kk, v, hr, hc, ?_, hr', hv⟩
  have := (hok.2.2.2.1 x).2; omega

lemma Iv_of_opn {x : Reg} {a : OpId (Fin n)} {o : RWOp Val} (h : opn α x a = some o) :
    Iv α x a α.length := (List.getElem?_eq_some_iff.1 h).1

lemma kind_player {p : Fin n} {γ : List (Ev n)} {l : Loc} {pend : Reg → ℕ}
    (h : LocOK p γ l pend) (hp : 2 ≤ p.val) : l.isHost = false := by
  cases hl : l.isHost
  · rfl
  · have := h.2.1.2 hl; omega

lemma kind_host {p : Fin n} {γ : List (Ev n)} {l : Loc} {pend : Reg → ℕ}
    (h : LocOK p γ l pend) (hp : p.val < 2) : l.isHost = true := h.2.1.1 hp

variable (hV : ∀ p t, (rep n p (tr α p t)).isSome)
include hV

lemma player_op_r1 {q : Fin n} (hq : 2 ≤ q.val) {k : ℕ} {o : RWOp Val}
    (h : opn α .r1 (q, k) = some o) : (o = .write .bot ∨ o = .read) ∧ (k % 3 ≠ 0 → o = .read) := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, hop⟩ := at_inv hV (Iv_of_opn h)
  rw [h] at hop; cases hop
  have hkind := kind_player hok hq
  have h1 := hok.1
  cases l <;> simp [Loc.isHost] at hkind <;> simp [code] at hc <;>
    obtain ⟨rfl, -⟩ := hc <;> simp [cnt, Loc.round] at hcnt h1 ⊢ <;> omega

lemma player_op_c {q : Fin n} (hq : 2 ≤ q.val) {k : ℕ} {o : RWOp Val}
    (h : opn α .c (q, k) = some o) :
    (o = .write .bot ∨ o = .read) ∧ (k % 2 = 1 → o = .read) ∧ (k % 2 = 0 → o = .write .bot) := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, hop⟩ := at_inv hV (Iv_of_opn h)
  rw [h] at hop; cases hop
  have hkind := kind_player hok hq
  have h1 := hok.1
  cases l <;> simp [Loc.isHost] at hkind <;> simp [code] at hc <;>
    obtain ⟨rfl, -⟩ := hc <;> simp [cnt, Loc.round] at hcnt h1 ⊢ <;> omega

lemma player_op_r2 {q : Fin n} (hq : 2 ≤ q.val) {k : ℕ} {o : RWOp Val}
    (h : opn α .r2 (q, k) = some o) :
    (k % 3 = 0 → o = .write (.num 0)) ∧ (k % 3 = 1 → o = .read) ∧
      (∀ m, o = .write (.num m) → 1 ≤ m → k % 3 = 2) := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, hop⟩ := at_inv hV (Iv_of_opn h)
  rw [h] at hop; cases hop
  have hkind := kind_player hok hq
  have h1 := hok.1
  cases l <;> simp [Loc.isHost] at hkind <;> simp [code] at hc <;>
    obtain ⟨rfl, -⟩ := hc <;> simp [cnt, Loc.round] at hcnt h1 ⊢ <;> omega

lemma host_op_r1 {h : Fin n} (hh : h.val < 2) {k : ℕ} {o : RWOp Val}
    (hk : opn α .r1 (h, k) = some o) : o = .write (.pair (decide (h.val = 1)) (k + 1)) := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, hop⟩ := at_inv hV (Iv_of_opn hk)
  rw [hk] at hop; cases hop
  have hkind := kind_host hok hh
  have h1 := hok.1
  cases l <;> simp [Loc.isHost] at hkind <;> simp [code] at hc <;>
    obtain ⟨rfl, -⟩ := hc <;> simp [cnt, Loc.round] at hcnt h1 ⊢ <;> omega

lemma host_op_r2 {h : Fin n} (hh : h.val < 2) {k : ℕ} {o : RWOp Val}
    (hk : opn α .r2 (h, k) = some o) :
    (k % 2 = 1 → o = .read) ∧ (k % 2 = 0 → o = .write (.num 0)) ∧
      (∀ m, o = .write (.num m) → m = 0) := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, hop⟩ := at_inv hV (Iv_of_opn hk)
  rw [hk] at hop; cases hop
  have hkind := kind_host hok hh
  have h1 := hok.1
  cases l <;> simp [Loc.isHost] at hkind <;> simp [code] at hc <;>
    obtain ⟨rfl, -⟩ := hc <;> simp [cnt, Loc.round] at hcnt h1 ⊢ <;> omega

lemma host_op_c {h : Fin n} (hh : h.val < 2) {k : ℕ} {o : RWOp Val}
    (hk : opn α .c (h, k) = some o) :
    h.val = 0 ∧ ∃ b, o = .write (.bit b) ∧ (pcoins (tr α h α.length))[k]? = some b := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, hop⟩ := at_inv hV (Iv_of_opn hk)
  have hkind := kind_host hok hh
  obtain ⟨h1, h2, h3, -, -, h6⟩ := hok
  rw [hk] at hop; cases hop
  cases l <;> simp [Loc.isHost] at hkind <;> simp [code] at hc
  · rename_i j b
    obtain ⟨rfl, -⟩ := hc
    have hp0 : h.val = 0 := h3 rfl
    simp [cnt, hp0, Loc.round] at hcnt h1
    refine ⟨hp0, b, rfl, pcoins_of_time (t := t) ?_⟩
    simp only [Data] at h6; rw [← hcnt]; exact h6

lemma host_c_r1 {h : Fin n} (hh : h.val < 2) {k : ℕ} (hk : Iv α .c (h, k) α.length) :
    Cp α .r1 (h, k) α.length := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, hop⟩ := at_inv hV hk
  have hkind := kind_host hok hh
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hok
  have := (h4 .r1).2
  cases l <;> simp [Loc.isHost] at hkind <;> simp [code] at hc
  have hp0 : h.val = 0 := h3 rfl
  simp [cnt, hp0, Loc.round] at hcnt h1 this
  exact Cp.final (t := t) (by unfold Cp; simp only; omega)

lemma pass_of_z {q : Fin n} (hq : 2 ≤ q.val) {r : ℕ} (hk : Iv α .r2 (q, 3 * r) α.length) :
    (∃ c, rsp α .r1 (q, 3 * r + 1) = some (.pair c (r + 1)) ∧
      rsp α .r1 (q, 3 * r + 2) = some (.pair (!c) (r + 1)) ∧
      rsp α .c (q, 2 * r + 1) = some (.bit c)) ∧
    ∃ t, Cp α .r1 (q, 3 * r + 2) t ∧ Cp α .c (q, 2 * r + 1) t ∧ ¬ Iv α .r2 (q, 3 * r) t := by
  obtain ⟨t, hr, hc, hcnt, hok, -⟩ :
      ∃ t, rep n q (tr α q t) = some (.run (.q6 (r + 1))) ∧ True ∧ True ∧
        LocOK q (tr α q t) (.q6 (r + 1)) (fun _ => 0) ∧ True := by
    obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, -⟩ := at_inv hV hk
    have hkind := kind_player hok hq
    have h1 := hok.1
    cases l <;> simp [Loc.isHost] at hkind <;> simp [code] at hc <;>
      simp [cnt, Loc.round] at hcnt h1 <;> try omega
    rename_i j
    obtain rfl : j = r + 1 := by omega
    exact ⟨t, hr, trivial, trivial, locOK_run hr (by simp), trivial⟩
  obtain ⟨-, -, -, h4, -, h6⟩ := hok
  simp only [Data, Pass, Nat.add_sub_cancel] at h6
  obtain ⟨c, hc1, hc2, hc3⟩ := h6
  refine ⟨⟨c, rsp_of_time hc1, rsp_of_time hc2, rsp_of_time hc3⟩, t, ?_, ?_, ?_⟩
  · have := (h4 .r1).2; simp [cnt] at this; unfold Cp; simp only; omega
  · have := (h4 .c).2; simp [cnt] at this; unfold Cp; simp only; omega
  · have := (h4 .r2).1; simp [cnt] at this; unfold Iv; simp only; omega

lemma inc_facts {q : Fin n} (hq : 2 ≤ q.val) {r : ℕ} (hk : Iv α .r2 (q, 3 * r + 2) α.length) :
    ∃ v, rsp α .r2 (q, 3 * r + 1) = some v ∧
      opn α .r2 (q, 3 * r + 2) = some (.write (.num (v.toNat + 1))) ∧
      ∃ t, Cp α .c (q, 2 * r + 1) t ∧ Cp α .r1 (q, 3 * r + 2) t ∧ Cp α .r2 (q, 3 * r + 1) t ∧
        ¬ Iv α .r2 (q, 3 * r + 2) t := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, hok, hop⟩ := at_inv hV hk
  obtain ⟨h1, h2, -, h4, -, h6⟩ := hok
  cases l <;> simp [code] at hc <;> simp [Loc.isHost] at h2 <;> (try omega) <;>
    simp [cnt, Loc.round] at hcnt h1 <;> try omega
  rename_i j k'
  obtain rfl : j = r + 1 := by omega
  obtain ⟨rfl, -⟩ := hc
  simp only [Data, Nat.add_sub_cancel] at h6
  obtain ⟨-, v, hv, rfl⟩ := h6
  refine ⟨v, rsp_of_time hv, hop, t, ?_, ?_, ?_, ?_⟩
  · have := (h4 .c).2; simp [cnt] at this; unfold Cp; simp only; omega
  · have := (h4 .r1).2; simp [cnt] at this; unfold Cp; simp only; omega
  · have := (h4 .r2).2; simp [cnt] at this; unfold Cp; simp only; omega
  · have := (h4 .r2).1; simp [cnt] at this; unfold Iv; simp only; omega

omit hV in
lemma host_entered {h : Fin n} {r t : ℕ} (ht : rep n h (tr α h t) = some (.run (.h1 (r + 2)))) :
    (∃ v, rsp α .r2 (h, 2 * r + 1) = some v ∧ ¬ v.toNat < n - 2) ∧ Cp α .r2 (h, 2 * r + 1) t ∧
      ¬ Iv α .r1 (h, r + 1) t ∧ ¬ Iv α .c (h, r + 1) t ∧ Iv α .r1 (h, r) α.length := by
  obtain ⟨-, -, -, h4, -, h6⟩ := locOK_run ht (by simp)
  simp only [Data] at h6
  obtain ⟨v, hv, hv'⟩ := h6 (by omega)
  have e1 : 2 * (r + 2 - 1) - 1 = 2 * r + 1 := by omega
  rw [e1] at hv
  refine ⟨⟨v, rsp_of_time hv, hv'⟩, ?_, ?_, ?_, ?_⟩
  · have := (h4 .r2).2; simp [cnt] at this; unfold Cp; simp only; omega
  · have := (h4 .r1).1; simp [cnt] at this; unfold Iv; simp only; omega
  · have := (h4 .c).1; simp [cnt] at this; unfold Iv; simp only; split_ifs at this <;> omega
  · have := (h4 .r1).1; simp [cnt] at this
    exact Iv.final (t := t) (by unfold Iv; simp only; omega)

lemma host_r1_entered {h : Fin n} (hh : h.val < 2) {r : ℕ} (hk : Iv α .r1 (h, r + 1) α.length) :
    ∃ t, rep n h (tr α h t) = some (.run (.h1 (r + 2))) := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, ⟨h1, h2, -, -, -, -⟩, -⟩ := at_inv hV hk
  cases l <;> simp [code] at hc <;> simp [Loc.isHost] at h2 <;> (try omega) <;>
    simp [cnt, Loc.round] at hcnt h1
  rename_i j
  obtain rfl : j = r + 2 := by omega
  exact ⟨t, hr⟩

lemma host_r2read {h : Fin n} {r : ℕ} (hk : Iv α .r2 (h, 2 * r + 1) α.length) :
    Iv α .r1 (h, r) α.length := by
  obtain ⟨t, l, o', kk, hr, hc, hcnt, ⟨h1, h2, -, h4, -, -⟩, -⟩ := at_inv hV hk
  have := (h4 .r1).1
  cases l <;> simp [code] at hc <;> simp [cnt, Loc.round] at hcnt h1 this <;> try omega
  all_goals exact Iv.final (t := t) (by unfold Iv; simp only; omega)

lemma p0_h2 {p : Fin n} (hp : p.val = 0) {r : ℕ} (hk : Cp α .r1 (p, r) α.length) :
    ∃ t, rep n p (tr α p t) = some (.run (.h2 (r + 1))) := by
  obtain ⟨t, l, o', kk, v, hr, hc, hcnt, hr', -⟩ := at_ret hV hk
  obtain ⟨h1, h2, -, -, -, -⟩ := locOK_wait hr
  cases l <;> simp [code] at hc <;> simp [Loc.isHost] at h2 <;> (try omega) <;>
    simp [cnt, Loc.round] at hcnt h1
  rename_i j
  obtain rfl : j = r + 1 := by omega
  obtain ⟨-, rfl⟩ := hc
  exact ⟨t + 1, by simpa [hp] using hr'⟩

omit hV in
lemma player_entered {q : Fin n} {r t : ℕ} (ht : rep n q (tr α q t) = some (.run (.q1 (r + 2)))) :
    Iv α .r2 (q, 3 * r) α.length := by
  obtain ⟨-, -, -, h4, -, -⟩ := locOK_run ht (by simp)
  have := (h4 .r2).1; simp [cnt] at this
  exact Iv.final (t := t) (by unfold Iv; simp only; omega)

/-- Program order on one register. -/
lemma prog {x : Reg} {p : Fin n} {k k' : ℕ} (hk : Iv α x (p, k') α.length) (hlt : k < k') :
    Precedes (hist x α) (p, k) (p, k') := by
  obtain ⟨t, l, o, kk, -, hr, hc, hlen, -, -⟩ := reach_inv (hV p) hk
  have hl : l ≠ .done := by rintro rfl; simp [code] at hc
  have h4 := ((locOK_run hr hl).2.2.2.1 x)
  simp only [add_zero] at h4
  refine prec_of_time (t := t) ?_ ?_
  · unfold Cp; simp only; omega
  · unfold Iv; simp only; omega

end Facts

/-! ## Linearizations of the three registers -/

section Lin

variable {n : ℕ} {α : List (Ev n)} {L : Reg → List (OpId (Fin n) × RWOp Val)}

lemma completed_iff_Cp {x : Reg} {a : OpId (Fin n)} :
    Completed (hist x α) a ↔ Cp α x a α.length := by
  rw [← completed_take_iff, take_length]

lemma invoked_iff_Iv {x : Reg} {a : OpId (Fin n)} :
    Invoked (hist x α) a ↔ Iv α x a α.length := by
  rw [← invoked_take_iff, take_length]

lemma Cp_of_rsp {x : Reg} {a : OpId (Fin n)} {v : Val} (h : rsp α x a = some v) :
    Cp α x a α.length := (List.getElem?_eq_some_iff.1 h).1

lemma opn_of_Iv {x : Reg} {a : OpId (Fin n)} (h : Iv α x a α.length) :
    ∃ o, opn α x a = some o := ⟨_, List.getElem?_eq_getElem h⟩

variable (hL : ∀ x, IsLinearization (hist x α) (L x))
include hL

lemma mem_of_Cp {x : Reg} {a : OpId (Fin n)} (h : Cp α x a α.length) :
    a ∈ (L x).map Prod.fst := (hL x).complete a (completed_iff_Cp.2 h)

lemma Iv_of_mem {x : Reg} {a : OpId (Fin n)} (h : a ∈ (L x).map Prod.fst) :
    Iv α x a α.length := invoked_iff_Iv.1 ((hL x).invoked_of_mem h)

lemma opn_of_mem {x : Reg} {a : OpId (Fin n)} {o : RWOp Val} (h : (a, o) ∈ L x) :
    opn α x a = some o := by
  rw [opn, ← opOf_hist]; exact (hL x).op_eq _ h

lemma Cp_Iv {x : Reg} {a : OpId (Fin n)} (h : Cp α x a α.length) : Iv α x a α.length :=
  Iv_of_mem hL (mem_of_Cp hL h)

lemma progL (hV : ∀ p t, (rep n p (tr α p t)).isSome) {x : Reg} {p : Fin n} {k k' : ℕ}
    (hk : (p, k') ∈ (L x).map Prod.fst) (hlt : k < k') :
    [(p, k), (p, k')].Sublist ((L x).map Prod.fst) :=
  (hL x).realtime _ _ (prog hV (Iv_of_mem hL hk) hlt) hk

omit hL in
lemma kind_h1 {h : Fin n} {t j : ℕ} (ht : rep n h (tr α h t) = some (.run (.h1 j))) :
    h.val < 2 := (locOK_run ht (by simp)).2.1.2 rfl

/-- **Lemma 16** (as used): if player `q` passed round `r + 1`, every host `h` invoked its
round-`r + 1` write to `R1` before `q`'s second read of `R1` in that round returned. -/
lemma host_write_before (hV : ∀ p t, (rep n p (tr α p t)).isSome) {q h : Fin n}
    (hq : 2 ≤ q.val) (hh : h.val < 2) {r : ℕ} (hz : Iv α .r2 (q, 3 * r) α.length) {t : ℕ}
    (ht : Cp α .r1 (q, 3 * r + 2) t) : Iv α .r1 (h, r) t := by
  obtain ⟨⟨c, hc1, hc2, -⟩, -⟩ := pass_of_z hV hq hz
  have key : ∀ k, k ≤ 3 * r + 2 → 3 * r + 1 ≤ k →
      rsp α .r1 (q, k) = some (.pair (decide (h.val = 1)) (r + 1)) → Iv α .r1 (h, r) t := by
    intro k hk1 hk2 hrk
    have hcp := Cp_of_rsp hrk
    obtain ⟨o, ho⟩ := opn_of_Iv (Cp_Iv hL hcp)
    have hread : o = .read := (player_op_r1 hV hq ho).2 (by omega)
    subst hread
    have hab := (hL .r1).writer_before_read (r := (q, k)) (v := .pair (decide (h.val = 1)) (r + 1))
      (w := (h, r)) (by rw [respOf_hist]; exact hrk) (by rw [opOf_hist]; exact ho)
      (by simp [initVal])
      (by
        rintro ⟨⟨p', k'⟩, o'⟩ hy hyo
        simp only at hyo; subst hyo
        have hop := opn_of_mem hL hy
        by_cases hp' : 2 ≤ p'.val
        · rcases (player_op_r1 hV hp' hop).1 with h' | h' <;> simp at h'
        · have := host_op_r1 hV (by omega) hop
          simp only [RWOp.write.injEq, Val.pair.injEq] at this
          obtain ⟨h1, h2⟩ := this
          have : p' = h := Fin.ext (by
            by_cases e : h.val = 1 <;> by_cases e' : p'.val = 1 <;> simp_all <;> omega)
          simp only [Prod.mk.injEq]; exact ⟨this, by omega⟩)
      (mem_of_Cp hL hcp)
    exact lin_time (hL .r1) hab (ht.of_le hk1)
  by_cases hcb : decide (h.val = 1) = c
  · exact key (3 * r + 1) (by omega) le_rfl (by rw [hcb]; exact hc1)
  · exact key (3 * r + 2) le_rfl (by omega) (by
      rw [hc2]; congr 2; cases c <;> simp_all)

lemma pair_mem {x : Reg} {a : OpId (Fin n)} {o : RWOp Val} (hm : a ∈ (L x).map Prod.fst)
    (ho : opn α x a = some o) : (a, o) ∈ L x := by
  obtain ⟨⟨a', o'⟩, hy, rfl⟩ := mem_map.1 hm
  have := opn_of_mem hL hy
  rw [ho] at this; cases this; exact hy

/-- Claim 17.3/17.4: an increment of round `r' + 1` linearized before host `h`'s round-`r + 1`
read of `R2` (with `h` entering round `r + 2`) has `r' ≤ r`. -/
lemma inc_round_le (hV : ∀ p t, (rep n p (tr α p t)).isSome) {h q : Fin n} (hq : 2 ≤ q.val)
    {r r' t : ℕ} (ht : rep n h (tr α h t) = some (.run (.h1 (r + 2))))
    (hab : [(q, 3 * r' + 2), (h, 2 * r + 1)].Sublist ((L .r2).map Prod.fst)) : r' ≤ r := by
  by_contra hlt
  have hh := kind_h1 ht
  have hI : Iv α .r2 (q, 3 * r' + 2) α.length := Iv_of_mem hL (hab.subset (by simp))
  obtain ⟨v, -, -, t2, -, hc2, -, hn2⟩ := inc_facts hV hq hI
  have hw := host_write_before hL hV hq hh (hI.of_le (by omega)) hc2
  obtain ⟨-, hcp, hn1, -, -⟩ := host_entered ht
  have hIt := lin_time (hL .r2) hab hcp
  have := lt_of_Iv hn2 hIt
  exact hn1 ((hw.mono this.le).of_le (by omega))

omit hL in
lemma player_of_write_num (hV : ∀ p t, (rep n p (tr α p t)).isSome) {q : Fin n} {k m : ℕ}
    (hm : 1 ≤ m) (ho : opn α .r2 (q, k) = some (.write (.num m))) :
    2 ≤ q.val ∧ ∃ r, k = 3 * r + 2 := by
  have hq : 2 ≤ q.val := by
    by_contra hc
    have := (host_op_r2 hV (by omega) ho).2.2 m rfl
    omega
  have := (player_op_r2 hV hq ho).2.2 m rfl hm
  exact ⟨hq, k / 3, by omega⟩

/-- **Lemma 17** of the paper (in the form used): if host `h` enters round `r + 2`, then every
player's round-`r + 1` increment of `R2` (line 34) is linearized before `h`'s round-`r + 1` read of
`R2` (line 11). -/
theorem lemma17 (hV : ∀ p t, (rep n p (tr α p t)).isSome) (hn : 3 ≤ n) :
    ∀ r, ∀ h t, rep n h (tr α h t) = some (.run (.h1 (r + 2))) → ∀ q : Fin n, 2 ≤ q.val →
      [(q, 3 * r + 2), (h, 2 * r + 1)].Sublist ((L .r2).map Prod.fst) := by
  have nd := (hL .r2).nodup
  intro r
  induction r using Nat.strong_induction_on with
  | _ r IH =>
  intro h t ht
  have hh := kind_h1 ht
  obtain ⟨⟨v, hv, hvn⟩, hcp, hn1, -, hIr1⟩ := host_entered ht
  obtain ⟨m, rfl⟩ : ∃ m, v = .num m := by
    cases v <;> simp [Val.toNat] at hvn ⊢ <;> omega
  simp only [Val.toNat] at hvn
  obtain ⟨o, ho⟩ := opn_of_Iv (Cp_Iv hL (Cp_of_rsp hv))
  have hread : o = .read := (host_op_r2 hV hh ho).1 (by omega)
  subst hread
  obtain ⟨w, hwm, hwr, hprop⟩ := last_write (hL .r2) (r := (h, 2 * r + 1)) (v := .num m)
    (by rw [respOf_hist]; exact hv) (by rw [opOf_hist]; exact ho) (by simp [initVal]; omega)
  have hwo := opn_of_mem hL hwm
  obtain ⟨q', k'⟩ := w
  obtain ⟨hq', r', rfl⟩ := player_of_write_num hV (by omega) hwo
  have hle := inc_round_le hL hV hq' ht hwr
  have hrdm : (h, 2 * r + 1) ∈ (L .r2).map Prod.fst := hwr.subset (by simp)
  have hzr := progL hL hV hrdm (by omega : 2 * r < 2 * r + 1)
  have hzm : (h, 2 * r) ∈ (L .r2).map Prod.fst := hzr.subset (by simp)
  obtain ⟨oz, hoz⟩ := opn_of_Iv (Iv_of_mem hL hzm)
  have := (host_op_r2 hV hh hoz).2.1 (by omega); subst this
  have hzw := hprop (h, 2 * r) (.num 0) (pair_mem hL hzm hoz) hzr
    (by simp only [ne_eq, Prod.mk.injEq, not_and]; intro e; omega)
  have hge : r ≤ r' := by
    by_contra hlt
    obtain ⟨t', ht'⟩ := host_r1_entered hV hh (hIr1.of_le (by omega) : Iv α .r1 (h, r' + 1) _)
    have h1 := IH r' (by omega) h t' ht' q' hq'
    have h2 := progL hL hV hzm (by omega : 2 * r' + 1 < 2 * r)
    exact not_sublist_pair_both nd hzw (pair_trans nd h1 h2)
  obtain rfl : r = r' := by omega
  -- Claim 17.5: counting the increments of round `r + 1`
  have claim : ∀ k, ∀ q : Fin n, 2 ≤ q.val →
      opn α .r2 (q, 3 * r + 2) = some (.write (.num (k + 1))) →
      [(q, 3 * r + 2), (h, 2 * r + 1)].Sublist ((L .r2).map Prod.fst) →
      ∃ S : Finset (Fin n), k + 1 ≤ S.card ∧ ∀ q₂ ∈ S, 2 ≤ q₂.val ∧
        (q₂ = q ∨ [(q₂, 3 * r + 2), (q, 3 * r + 2)].Sublist ((L .r2).map Prod.fst)) := by
    intro k
    induction k with
    | zero => intro q hq _ _; exact ⟨{q}, by simp, by simp [hq]⟩
    | succ k ihk =>
      intro q hq hop hqh
      have hqm : (q, 3 * r + 2) ∈ (L .r2).map Prod.fst := hqh.subset (by simp)
      obtain ⟨u, hu, hop', -⟩ := inc_facts hV hq (Iv_of_mem hL hqm)
      rw [hop] at hop'
      simp only [Option.some.injEq, RWOp.write.injEq, Val.num.injEq] at hop'
      obtain ⟨u, rfl⟩ : ∃ u', u = .num u' := by
        cases u <;> simp [Val.toNat] at hop' ⊢
      simp only [Val.toNat] at hop'
      obtain rfl : u = k + 1 := by omega
      obtain ⟨o, ho⟩ := opn_of_Iv (Cp_Iv hL (Cp_of_rsp hu))
      have := (player_op_r2 hV hq ho).2.1 (by omega); subst this
      obtain ⟨w', hw'm, hw'r, hprop'⟩ := last_write (hL .r2) (r := (q, 3 * r + 1))
        (v := .num (k + 1)) (by rw [respOf_hist]; exact hu) (by rw [opOf_hist]; exact ho)
        (by simp [initVal])
      have hw'o := opn_of_mem hL hw'm
      obtain ⟨q₂, k₂⟩ := w'
      obtain ⟨hq₂, r₂, rfl⟩ := player_of_write_num hV (by omega) hw'o
      have hrdm' : (q, 3 * r + 1) ∈ (L .r2).map Prod.fst := hw'r.subset (by simp)
      have hzrd := progL hL hV hrdm' (by omega : 3 * r < 3 * r + 1)
      have hzm' : (q, 3 * r) ∈ (L .r2).map Prod.fst := hzrd.subset (by simp)
      obtain ⟨oz', hoz'⟩ := opn_of_Iv (Iv_of_mem hL hzm')
      have := (player_op_r2 hV hq hoz').1 (by omega); subst this
      have hzw' := hprop' (q, 3 * r) (.num 0) (pair_mem hL hzm' hoz') hzrd
        (by simp only [ne_eq, Prod.mk.injEq, not_and]; intro _; omega)
      have hrdinc := progL hL hV hqm (by omega : 3 * r + 1 < 3 * r + 2)
      have hw'q := pair_trans nd hw'r hrdinc
      have hw'h := pair_trans nd hw'q hqh
      have hle₂ := inc_round_le hL hV hq₂ ht hw'h
      have hge₂ : r ≤ r₂ := by
        by_contra hlt
        obtain ⟨t', ht'⟩ := host_r1_entered hV hh (hIr1.of_le (by omega) : Iv α .r1 (h, r₂ + 1) _)
        have h1 := IH r₂ (by omega) h t' ht' q₂ hq₂
        obtain ⟨-, hcp', hn1', -, -⟩ := host_entered ht'
        obtain ⟨-, t2, hc2, -, hn2⟩ := pass_of_z hV hq (Iv_of_mem hL hzm')
        have hw := host_write_before hL hV hq hh (Iv_of_mem hL hzm') hc2
        have hlt' := lt_of_Iv (fun hI => hn1' (hI.of_le (by omega))) hw
        have hprec := prec_of_time (hcp'.mono hlt'.le) hn2
        have h3 := (hL .r2).realtime _ _ hprec hzm'
        exact not_sublist_pair_both nd hzw' (pair_trans nd h1 h3)
      obtain rfl : r = r₂ := by omega
      have hq₂q : q₂ ≠ q := by
        rintro rfl; exact not_sublist_pair_both nd hw'q hw'q
      obtain ⟨S', hS'c, hS'⟩ := ihk q₂ hq₂ hw'o (pair_trans nd hw'q hqh)
      have hqS' : q ∉ S' := by
        intro hm
        rcases (hS' q hm).2 with h' | h'
        · exact hq₂q h'.symm
        · exact not_sublist_pair_both nd hw'q h'
      refine ⟨insert q S', by rw [Finset.card_insert_of_notMem hqS']; omega, ?_⟩
      intro q₃ hq₃
      rcases Finset.mem_insert.1 hq₃ with rfl | hq₃
      · exact ⟨hq, Or.inl rfl⟩
      · obtain ⟨hq₃', h3⟩ := hS' q₃ hq₃
        refine ⟨hq₃', Or.inr ?_⟩
        rcases h3 with rfl | h3
        · exact hw'q
        · exact pair_trans nd h3 hw'q
  obtain ⟨S, hSc, hS⟩ := claim (m - 1) q' hq' (by rw [hwo]; congr 3; omega) hwr
  intro q hq
  by_cases hqS : q ∈ S
  · rcases (hS q hqS).2 with rfl | h'
    · exact hwr
    · exact pair_trans nd h' hwr
  · exfalso
    let a0 : Fin n := ⟨0, by omega⟩
    let a1 : Fin n := ⟨1, by omega⟩
    have hsub : S ⊆ Finset.univ \ {a0, a1, q} := by
      intro q₂ hq₂
      have := (hS q₂ hq₂).1
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or]
      refine ⟨fun e => ?_, fun e => ?_, fun e => hqS (e ▸ hq₂)⟩
      · rw [e] at this; simp [a0] at this
      · rw [e] at this; simp [a1] at this
    have h3 : ({a0, a1, q} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [a1, Fin.ext_iff]; omega
      · simp [a0, a1, Fin.ext_iff]; omega
    have := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      h3] at this
    omega

/-- **Lemma 18** of the paper: if player `q` passed round `r + 1` and read `c` from `C` in that
round, then the last write before that read (in the linearization of `C`) is `p₀`'s round-`r + 1`
write, which writes `c`. -/
theorem lemma18 (hV : ∀ p t, (rep n p (tr α p t)).isSome) (hn : 3 ≤ n) :
    ∀ r, ∀ q : Fin n, 2 ≤ q.val → Iv α .r2 (q, 3 * r) α.length → ∀ c,
      rsp α .c (q, 2 * r + 1) = some (.bit c) →
      ∃ p : Fin n, p.val = 0 ∧ [(p, r), (q, 2 * r + 1)].Sublist ((L .c).map Prod.fst) ∧
        opn α .c (p, r) = some (.write (.bit c)) := by
  have nd := (hL .c).nodup
  intro r
  induction r using Nat.strong_induction_on with
  | _ r IH =>
  intro q hq hz c hc
  obtain ⟨o, ho⟩ := opn_of_Iv (Cp_Iv hL (Cp_of_rsp hc))
  have := (player_op_c hV hq ho).2.1 (by omega); subst this
  obtain ⟨w, hwm, hwr, hprop⟩ := last_write (hL .c) (r := (q, 2 * r + 1)) (v := .bit c)
    (by rw [respOf_hist]; exact hc) (by rw [opOf_hist]; exact ho) (by simp [initVal])
  have hwo := opn_of_mem hL hwm
  obtain ⟨p, k⟩ := w
  have hp : p.val < 2 := by
    by_contra hc'
    rcases (player_op_c hV (by omega) hwo).1 with h' | h' <;> simp at h'
  obtain ⟨hp0, -⟩ := host_op_c hV hp hwo
  have hrdm : (q, 2 * r + 1) ∈ (L .c).map Prod.fst := hwr.subset (by simp)
  have hzr := progL hL hV hrdm (by omega : 2 * r < 2 * r + 1)
  have hzm : (q, 2 * r) ∈ (L .c).map Prod.fst := hzr.subset (by simp)
  obtain ⟨oz, hoz⟩ := opn_of_Iv (Iv_of_mem hL hzm)
  have := (player_op_c hV hq hoz).2.2 (by omega); subst this
  have hzw := hprop (q, 2 * r) .bot (pair_mem hL hzm hoz) hzr
    (by simp only [ne_eq, Prod.mk.injEq, not_and]; intro e; subst e; omega)
  have hge : r ≤ k := by
    by_contra hlt
    obtain ⟨r₀, rfl⟩ : ∃ r₀, r = r₀ + 1 := ⟨r - 1, by omega⟩
    have hz₀ : Iv α .r2 (q, 3 * r₀) α.length := hz.of_le (by omega)
    obtain ⟨⟨c', -, -, hc'⟩, -⟩ := pass_of_z hV hq hz₀
    obtain ⟨p', hp'0, h1, -⟩ := IH r₀ (by omega) q hq hz₀ c' hc'
    have hpp : p' = p := Fin.ext (by omega)
    subst hpp
    have h2 := progL hL hV hzm (by omega : 2 * r₀ + 1 < 2 * (r₀ + 1))
    have h12 := pair_trans nd h1 h2
    rcases Nat.lt_or_ge k r₀ with hk | hk
    · have h0 := progL hL hV (h1.subset (by simp : (p', r₀) ∈ [(p', r₀), (q, 2 * r₀ + 1)])) hk
      exact not_sublist_pair_both nd hzw (pair_trans nd h0 h12)
    · obtain rfl : r₀ = k := by omega
      exact not_sublist_pair_both nd hzw h12
  have hle : k ≤ r := by
    by_contra hlt
    have hIc : Iv α .c (p, k) α.length :=
      Iv_of_mem hL (hwr.subset (by simp : (p, k) ∈ [(p, k), (q, 2 * r + 1)]))
    have hr1 := host_c_r1 hV hp hIc
    obtain ⟨th, hth⟩ := host_r1_entered hV hp
      ((Cp_Iv hL hr1).of_le (by omega) : Iv α .r1 (p, r + 1) _)
    have h17 := lemma17 hL hV hn r p th hth q hq
    obtain ⟨-, hcp, -, hnc, -⟩ := host_entered hth
    have hI := lin_time (hL .r2) h17 hcp
    obtain ⟨-, t2, -, hc2, hn2⟩ := pass_of_z hV hq hz
    have hlt2 := lt_of_Iv (fun h' => hn2 (h'.of_le (by omega))) hI
    have hnk : ¬ Iv α .c (p, k) th := fun h' => hnc (h'.of_le (by omega))
    have hprec := prec_of_time (hc2.mono hlt2.le) hnk
    have := (hL .c).realtime _ _ hprec (hwr.subset (by simp : (p, k) ∈ [(p, k), (q, 2 * r + 1)]))
    exact not_sublist_pair_both nd hwr this
  obtain rfl : r = k := by omega
  exact ⟨p, hp0, hwr, hwo⟩

/-- The writer of `[i, j]` to `R1` is host `p_i` in round `j`. -/
lemma writer_r1 (hV : ∀ p t, (rep n p (tr α p t)).isSome) {y : OpId (Fin n) × RWOp Val}
    (hy : y ∈ L .r1) {i : Bool} {j : ℕ} (hyo : y.2 = .write (.pair i j)) :
    y.1.1.val = (if i then 1 else 0) ∧ y.1.2 + 1 = j := by
  obtain ⟨⟨p, k⟩, o⟩ := y
  simp only at hyo; subst hyo
  have hop := opn_of_mem hL hy
  by_cases hp : 2 ≤ p.val
  · rcases (player_op_r1 hV hp hop).1 with h' | h' <;> simp at h'
  · have := host_op_r1 hV (by omega) hop
    simp only [RWOp.write.injEq, Val.pair.injEq] at this
    obtain ⟨h1, h2⟩ := this
    refine ⟨?_, by simp; omega⟩
    cases i <;> simp at h1 ⊢ <;> omega

lemma writer_r1_unique (hV : ∀ p t, (rep n p (tr α p t)).isSome)
    {y y' : OpId (Fin n) × RWOp Val} (hy : y ∈ L .r1) (hy' : y' ∈ L .r1) {i : Bool} {j : ℕ}
    (hyo : y.2 = .write (.pair i j)) (hyo' : y'.2 = .write (.pair i j)) : y.1 = y'.1 := by
  obtain ⟨a, b⟩ := writer_r1 hL hV hy hyo
  obtain ⟨a', b'⟩ := writer_r1 hL hV hy' hyo'
  exact Prod.ext (Fin.ext (by omega)) (by omega)

/-- `p₁`'s write of `[1, r + 1]` precedes `p₀`'s write of `[0, r + 1]` in the sequence of
writes `W`. -/
def D (n : ℕ) (r : ℕ) (W : List (OpId (Fin n) × RWOp Val)) : Prop :=
  ∃ a b, [(a, RWOp.write (.pair true (r + 1))), (b, RWOp.write (.pair false (r + 1)))].Sublist W

/-- **The decision bit.** Let `F₀` be a linearization of the history of `R1` up to a time `m₀`
at which `p₀` has completed its round-`r + 1` write and not yet flipped its coin, whose writes form
a prefix of the writes of the linearization `L .r1` of the whole run (write strong
linearizability). If some player passed round `r + 1`, then `p₀`'s round-`r + 1` coin is `true`
iff `p₁`'s write precedes `p₀`'s write among the writes of `F₀`. -/
theorem coin_decided (hV : ∀ p t, (rep n p (tr α p t)).isSome) (hn : 3 ≤ n) {p0 : Fin n}
    (hp0 : p0.val = 0) {r m₀ : ℕ} (hm₀ : rep n p0 (tr α p0 m₀) = some (.run (.h2 (r + 1))))
    {F₀ : List (OpId (Fin n) × RWOp Val)} (hF₀ : IsLinearization (hist .r1 (α.take m₀)) F₀)
    (hpre : opsFor RWOp.isWrite F₀ <+: opsFor RWOp.isWrite (L .r1))
    {q : Fin n} (hq : 2 ≤ q.val) (hz : Iv α .r2 (q, 3 * r) α.length) :
    ∃ b, (pcoins (tr α p0 α.length))[r]? = some b ∧
      (b = true ↔ D n r (opsFor RWOp.isWrite F₀)) := by
  have nd := (hL .r1).nodup
  have ndW : (opsFor RWOp.isWrite (L .r1)).Nodup := (nd.of_map _).filter _
  obtain ⟨⟨c, hc1, hc2, hc3⟩, -⟩ := pass_of_z hV hq hz
  -- the coin
  obtain ⟨p, hp, -, hpo⟩ := lemma18 hL hV hn r q hq hz c hc3
  obtain rfl : p0 = p := Fin.ext (by omega)
  obtain ⟨-, b, hb, hbc⟩ := host_op_c hV (by omega) hpo
  simp only [RWOp.write.injEq, Val.bit.injEq] at hb
  subst hb
  refine ⟨c, hbc, ?_⟩
  -- the two reads
  obtain ⟨o1, ho1⟩ := opn_of_Iv (Cp_Iv hL (Cp_of_rsp hc1))
  have := (player_op_r1 hV hq ho1).2 (by omega); subst this
  obtain ⟨o2, ho2⟩ := opn_of_Iv (Cp_Iv hL (Cp_of_rsp hc2))
  have := (player_op_r1 hV hq ho2).2 (by omega); subst this
  obtain ⟨w, hwm, hwr, -⟩ := last_write (hL .r1) (r := (q, 3 * r + 1)) (v := .pair c (r + 1))
    (by rw [respOf_hist]; exact hc1) (by rw [opOf_hist]; exact ho1) (by simp [initVal])
  obtain ⟨w₂, hw₂m, hw₂r, -⟩ := last_write (hL .r1) (r := (q, 3 * r + 2))
    (v := .pair (!c) (r + 1)) (by rw [respOf_hist]; exact hc2) (by rw [opOf_hist]; exact ho2)
    (by simp [initVal])
  have hrd := progL hL hV (hw₂r.subset (by simp : (q, 3 * r + 2) ∈ [w₂, (q, 3 * r + 2)]))
    (by omega : 3 * r + 1 < 3 * r + 2)
  have hww : w ≠ w₂ := by
    rintro rfl
    have := (writer_r1 hL hV hwm rfl).1
    have := (writer_r1 hL hV hw₂m rfl).1
    cases c <;> simp_all
  have hWW := (hL .r1).write_before_of_read (r := (q, 3 * r + 2)) (v := .pair (!c) (r + 1))
    (by rw [respOf_hist]; exact hc2) (by rw [opOf_hist]; exact ho2) (by simp [initVal])
    (w := w₂) (fun y hy hyo => writer_r1_unique hL hV hy hw₂m hyo rfl) hwm hww
    (pair_trans nd hwr hrd)
  -- `p₀`'s write is in `F₀`
  have hcp : Cp α .r1 (p0, r) m₀ := by
    have := ((locOK_run hm₀ (by simp)).2.2.2.1 .r1).2
    simp [cnt] at this; unfold Cp; simp only; omega
  have hcomp : Completed (hist .r1 (α.take m₀)) (p0, r) := completed_take_iff.2 hcp
  have hmemF := hF₀.complete _ hcomp
  obtain ⟨⟨a0, o0⟩, ha0, ha0e⟩ := mem_map.1 hmemF
  simp only at ha0e; subst ha0e
  have ho0 : o0 = .write (.pair false (r + 1)) := by
    have h1 := hF₀.op_eq _ ha0
    have h2 : opOf (hist .r1 (α.take m₀)) (p0, r) = opOf (hist .r1 α) (p0, r) := by
      conv_rhs => rw [← take_append_drop m₀ α, hist_append]
      exact (opOf_append_of_invoked (invoked_take_iff.2 (by
        unfold Iv; have := hcp; unfold Cp at this; simp only at this ⊢
        have := ((locOK_run hm₀ (by simp)).2.2.2.1 .r1).1; simp [cnt] at this; omega))).symm
    rw [h2, opOf_hist] at h1
    have := host_op_r1 hV (by omega) h1
    simpa [hp0] using this
  subst ho0
  have hW0 : ((p0, r), RWOp.write (.pair false (r + 1))) ∈ opsFor RWOp.isWrite F₀ := by
    simp [opsFor, ha0]
  constructor
  · intro hcT
    subst hcT
    refine ⟨w, w₂, ?_⟩
    simp only [Bool.not_true] at hWW hw₂m
    have hw₂0 : w₂ = (p0, r) := by
      have := writer_r1 hL hV hw₂m rfl
      obtain ⟨w₂a, w₂b⟩ := w₂
      simp only [Bool.false_eq_true, ite_false] at this
      exact Prod.ext (Fin.ext (by simp only; omega)) (by simp only; omega)
    rw [hw₂0] at hWW ⊢
    exact sublist_pair_of_prefix hpre ndW hWW hW0
  · rintro ⟨a, b, hab⟩
    have hab' := hab.trans hpre.sublist
    have hmem : ∀ y ∈ opsFor RWOp.isWrite (L .r1), y ∈ L .r1 := fun y hy => (mem_filter.1 hy).1
    have ha : (a, RWOp.write (.pair true (r + 1))) ∈ L .r1 := hmem _ (hab'.subset (by simp))
    have hb : (b, RWOp.write (.pair false (r + 1))) ∈ L .r1 := hmem _ (hab'.subset (by simp))
    by_contra hcF
    simp only [Bool.not_eq_true] at hcF
    subst hcF
    have e1 : a = w₂ := writer_r1_unique hL hV ha hw₂m rfl rfl
    have e2 : b = w := writer_r1_unique hL hV hb hwm rfl rfl
    subst e1 e2
    exact not_sublist_pair_both ndW hWW hab'

end Lin

/-! ## Runs generated by an adversary -/

section Runs

variable {n : ℕ}

lemma genRun_length (σ : List (Ev n) → Ev n) (ω : ℕ → Bool) (m : ℕ) :
    (genRun σ ω m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [genRun, ih]

lemma genRun_take (σ : List (Ev n) → Ev n) (ω : ℕ → Bool) {m M : ℕ} (h : m ≤ M) :
    (genRun σ ω M).take m = genRun σ ω m := by
  induction M with
  | zero => obtain rfl : m = 0 := by omega
            rfl
  | succ M ih =>
    rcases Nat.lt_or_ge m (M + 1) with h' | h'
    · rw [genRun, take_append_of_le_length (by rw [genRun_length]; omega), ih (by omega)]
    · obtain rfl : m = M + 1 := by omega
      rw [take_of_length_le (by rw [genRun_length])]

lemma coin?_coinify (ω : ℕ → Bool) (α : List (Ev n)) (e : Ev n) :
    Thm6.coin? (coinify ω α e) = (Thm6.coin? e).map (fun _ => ω (flipCount α)) := by
  cases e <;> rfl

lemma coins_genRun (σ : List (Ev n) → Ev n) (ω : ℕ → Bool) (m : ℕ) :
    (genRun σ ω m).filterMap Thm6.coin? = (range (flipCount (genRun σ ω m))).map ω := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [genRun]
    rw [Thm6.flipCount_eq, filterMap_append, ih]
    cases hc : Thm6.coin? (σ (genRun σ ω m)) with
    | none => simp [coin?_coinify, hc]
    | some b => simp [coin?_coinify, hc, range_succ]

/-- Two coin sequences that agree on the coins used so far generate the same run. -/
lemma genRun_congr (σ : List (Ev n) → Ev n) {ω ω' : ℕ → Bool} (m : ℕ)
    (h : ∀ k < flipCount (genRun σ ω m), ω k = ω' k) : genRun σ ω m = genRun σ ω' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hle : flipCount (genRun σ ω m) ≤ flipCount (genRun σ ω (m + 1)) := by
      rw [Thm6.flipCount_eq, Thm6.flipCount_eq, genRun, filterMap_append, length_append]; omega
    have e := ih (fun k hk => h k (by omega))
    rw [genRun, genRun, ← e]
    congr 2
    cases hσ : σ (genRun σ ω m) <;> simp only [coinify]
    rename_i p b
    rw [h]
    rw [Thm6.flipCount_eq, Thm6.flipCount_eq, genRun, filterMap_append, length_append, hσ]
    simp [coinify, Thm6.coin?]

lemma rep_of_procRun {p : Fin n} {β : List (Ev n)} {l : Loc}
    (h : procRun p β = some (.run l)) :
    rep n p (β.filter (fun e => decide (e.proc = p))) = some (.run l) := by
  rw [procRun_eq_rep] at h
  cases hr : rep n p (β.filter (fun e => decide (e.proc = p))) with
  | none => rw [hr] at h; simp at h
  | some md =>
    rw [hr] at h
    cases md with
    | run l' => simp [toMode] at h; rw [h]
    | wait l' =>
      obtain ⟨x, o, k, hc⟩ := rep_wellMd p _ hr
      simp [toMode, hc] at h

/-- Valid runs: every prefix replays. -/
lemma hV_of_valid {α : List (Ev n)} (hv : ∀ t, Valid (α.take t)) :
    ∀ p t, (rep n p (tr α p t)).isSome := by
  intro p t
  have := hv t p
  rw [procRun_eq_rep] at this
  simpa [tr] using this

/-- In a valid run only `p₀` flips coins. -/
lemma flip_proc {α : List (Ev n)} (hV : ∀ p t, (rep n p (tr α p t)).isSome) {t : ℕ} {e : Ev n}
    (he : α[t]? = some e) {b : Bool} (hb : Thm6.coin? e = some b) : e.proc.val = 0 := by
  have hs := hV e.proc (t + 1)
  rw [tr_succ, he] at hs
  simp only [Option.toList_some, filter_cons, decide_true, ite_true, filter_nil] at hs
  rw [rep_snoc] at hs
  cases hr : rep n e.proc (tr α e.proc t) with
  | none => rw [hr] at hs; simp at hs
  | some md =>
    rw [hr] at hs
    cases e with
    | flip q b' =>
      simp only [Ev.proc] at hs hr ⊢
      cases md with
      | run l =>
        simp only [Option.bind_some, step'] at hs
        cases hc : code n q l with
        | flip k =>
          have hl : l ≠ .done := by rintro rfl; simp [code] at hc
          have hok := locOK_run hr hl
          cases l <;> simp [code] at hc
          exact hok.2.2.1 rfl
        | _ => simp [hc] at hs
      | wait l => simp [step'] at hs
    | _ => simp [Thm6.coin?] at hb

/-- The coins flipped by `p₀` are all the coins of the run. -/
lemma pcoins_p0 {α : List (Ev n)} (hV : ∀ p t, (rep n p (tr α p t)).isSome) {p0 : Fin n}
    (hp0 : p0.val = 0) (t : ℕ) :
    pcoins (tr α p0 t) = (α.take t).filterMap Thm6.coin? := by
  rw [pcoins, tr, filterMap_filter']
  apply filterMap_congr
  intro e he
  cases hc : Thm6.coin? e with
  | none => simp
  | some b =>
    obtain ⟨i, hi, rfl⟩ := mem_iff_getElem.1 he
    have hi' : i < α.length := by simp at hi; omega
    rw [getElem_take] at hc ⊢
    have h0 := flip_proc hV (t := i) (getElem?_eq_getElem hi') hc
    have : α[i].proc = p0 := Fin.ext (by omega)
    simp [this]

end Runs

/-! ## At most one coin sequence keeps the game going -/

section Adversary

variable {n : ℕ} (σ : List (Ev n) → Ev n)

/-- `f` is a write strong-linearization function for `R1` along the runs of `σ`. -/
def WSLAlong (f : List (Label (Fin n) (RegObj .r1)) → List (OpId (Fin n) × RWOp Val)) : Prop :=
  ∀ ω m m', m ≤ m' → IsLinearization (hist .r1 (genRun σ ω m')) (f (hist .r1 (genRun σ ω m'))) ∧
    opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m))) <+:
      opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m')))

/-- The coin sequences for which every round is entered by some process. -/
def Forever : Set (ℕ → Bool) := {ω | ∀ J, ∃ p m, Entered p J (genRun σ ω m)}

variable {σ}

lemma hV_genRun (hvalid : ∀ ω m, Valid (genRun σ ω m)) (ω : ℕ → Bool) (M : ℕ) :
    ∀ p t, (rep n p (tr (genRun σ ω M) p t)).isSome := by
  apply hV_of_valid
  intro t
  rcases Nat.le_total t M with h | h
  · rw [genRun_take σ ω h]; exact hvalid ω t
  · rw [take_of_length_le (by rw [genRun_length]; exact h)]; exact hvalid ω M

lemma tr_genRun (ω : ℕ → Bool) {m M : ℕ} (h : m ≤ M) (p : Fin n) :
    tr (genRun σ ω M) p m = (genRun σ ω m).filter (fun e => decide (e.proc = p)) := by
  rw [tr, genRun_take σ ω h]

/-- Linearizations of the three registers in the run `genRun σ ω M` (for `R1`, the one given by
`f`). -/
noncomputable def linOf (hlin : ∀ ω m, LinRegs (genRun σ ω m))
    (f : List (Label (Fin n) (RegObj .r1)) → List (OpId (Fin n) × RWOp Val)) (ω : ℕ → Bool)
    (M : ℕ) : Reg → List (OpId (Fin n) × RWOp Val)
  | .r1 => f (hist .r1 (genRun σ ω M))
  | x => Classical.choose (hlin ω M x)

lemma linOf_spec (hlin : ∀ ω m, LinRegs (genRun σ ω m)) {f} (hf : WSLAlong σ f)
    (ω : ℕ → Bool) (M : ℕ) : ∀ x, IsLinearization (hist x (genRun σ ω M)) (linOf hlin f ω M x)
  | .r1 => (hf ω M M le_rfl).1
  | .r2 => Classical.choose_spec (hlin ω M .r2)
  | .c => Classical.choose_spec (hlin ω M .c)

variable (hn : 3 ≤ n) (hvalid : ∀ ω m, Valid (genRun σ ω m))
  (hlin : ∀ ω m, LinRegs (genRun σ ω m)) {f : List (Label (Fin n) (RegObj .r1)) →
    List (OpId (Fin n) × RWOp Val)} (hf : WSLAlong σ f)
include hn hvalid hlin hf

/-- If some process enters round `r + 2`, some player passed round `r + 1` (for a host: by
Lemma 17). -/
lemma passed_of_entered {ω : ℕ → Bool} {p : Fin n} {m r : ℕ}
    (hent : Entered p (r + 2) (genRun σ ω m)) :
    ∃ q : Fin n, 2 ≤ q.val ∧ Iv (genRun σ ω m) .r2 (q, 3 * r) (genRun σ ω m).length := by
  have hV := hV_genRun hvalid ω m
  have hL := linOf_spec hlin hf ω m
  obtain ⟨β, hβ, hproc⟩ := hent
  have hβe : β = (genRun σ ω m).take β.length := prefix_iff_eq_take.1 hβ
  have hrep : ∀ l, procRun p β = some (.run l) → rep n p (tr (genRun σ ω m) p β.length) =
      some (.run l) := by
    intro l h; rw [tr, ← hβe]; exact rep_of_procRun h
  rcases hproc with h | h
  · have ht := hrep _ h
    let q : Fin n := ⟨2, by omega⟩
    have := lemma17 hL hV hn r p _ ht q (by simp [q])
    exact ⟨q, by simp [q], ((Iv_of_mem hL (this.subset
      (by simp : (q, 3 * r + 2) ∈ [(q, 3 * r + 2), (p, 2 * r + 1)]))).of_le (by omega))⟩
  · have ht := hrep _ h
    have hq : 2 ≤ p.val := by
      by_contra hc
      have := (locOK_run ht (by simp)).2.1.1 (by omega)
      simp [Loc.isHost] at this
    exact ⟨p, hq, player_entered ht⟩

omit hn hlin hf in
lemma flipCount_of_h2 {ω : ℕ → Bool} {p0 : Fin n} (hp0 : p0.val = 0) {m₀ r : ℕ}
    (hm₀ : rep n p0 ((genRun σ ω m₀).filter (fun e => decide (e.proc = p0))) =
      some (.run (.h2 (r + 1)))) : flipCount (genRun σ ω m₀) = r := by
  have hV := hV_genRun hvalid ω m₀
  have ht : rep n p0 (tr (genRun σ ω m₀) p0 m₀) = some (.run (.h2 (r + 1))) := by
    rwa [tr_genRun ω le_rfl]
  have h5 := (locOK_run ht (by simp)).2.2.2.2.1
  rw [pcoins_p0 hV hp0, genRun_take σ ω le_rfl] at h5
  rw [Thm6.flipCount_eq, h5]; simp [cf, hp0]

lemma exists_m₀ {ω : ℕ → Bool} (hω : ω ∈ Forever σ) {p0 : Fin n} (hp0 : p0.val = 0) (r : ℕ) :
    ∃ m₀, rep n p0 ((genRun σ ω m₀).filter (fun e => decide (e.proc = p0))) =
      some (.run (.h2 (r + 1))) := by
  obtain ⟨p, m, hent⟩ := hω (r + 2)
  obtain ⟨q, hq, hz⟩ := passed_of_entered hn hvalid hlin hf hent
  have hV := hV_genRun hvalid ω m
  have hL := linOf_spec hlin hf ω m
  obtain ⟨⟨c, -, -, hc3⟩, -⟩ := pass_of_z hV hq hz
  obtain ⟨p', hp', -, hpo⟩ := lemma18 hL hV hn r q hq hz c hc3
  obtain rfl : p0 = p' := Fin.ext (by omega)
  have hr1 := host_c_r1 hV (by omega) (Iv_of_opn hpo)
  obtain ⟨t, ht⟩ := p0_h2 hV hp0 hr1
  refine ⟨min t m, ?_⟩
  have e : tr (genRun σ ω m) p0 t = tr (genRun σ ω m) p0 (min t m) := by
    unfold tr; congr 1
    rcases Nat.le_total t m with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, take_of_length_le (by rw [genRun_length]; exact h),
        take_of_length_le (by rw [genRun_length])]
  rw [← tr_genRun ω (Nat.min_le_right t m), ← e]; exact ht

/-- The coin of round `r + 1` is determined by the history up to `m₀`. -/
lemma coin_eq {ω : ℕ → Bool} (hω : ω ∈ Forever σ) {p0 : Fin n} (hp0 : p0.val = 0) {r m₀ : ℕ}
    (hm₀ : rep n p0 ((genRun σ ω m₀).filter (fun e => decide (e.proc = p0))) =
      some (.run (.h2 (r + 1)))) :
    (ω r = true ↔ D n r (opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m₀))))) := by
  obtain ⟨p, m, hent⟩ := hω (r + 2)
  obtain ⟨q, hq, hz⟩ := passed_of_entered hn hvalid hlin hf hent
  set M := m + m₀
  have hV := hV_genRun hvalid ω M
  have hL := linOf_spec hlin hf ω M
  have hzM : Iv (genRun σ ω M) .r2 (q, 3 * r) (genRun σ ω M).length := by
    apply Iv.final (t := m)
    have e1 : tr (genRun σ ω M) q m = tr (genRun σ ω m) q (genRun σ ω m).length := by
      rw [tr_genRun ω (by omega : m ≤ M), tr, take_length]
    unfold Iv at hz ⊢; rw [e1]; exact hz
  have hm₀' : rep n p0 (tr (genRun σ ω M) p0 m₀) = some (.run (.h2 (r + 1))) := by
    rwa [tr_genRun ω (by omega : m₀ ≤ M)]
  have hF₀ : IsLinearization (hist .r1 ((genRun σ ω M).take m₀))
      (f (hist .r1 (genRun σ ω m₀))) := by
    rw [genRun_take σ ω (by omega : m₀ ≤ M)]; exact (hf ω m₀ m₀ le_rfl).1
  obtain ⟨b, hb, hbD⟩ := coin_decided hL hV hn hp0 hm₀' hF₀ (hf ω m₀ M (by omega)).2 hq hzM
  rw [pcoins_p0 hV hp0, take_of_length_le le_rfl, coins_genRun] at hb
  obtain ⟨hlt, hb'⟩ := List.getElem?_eq_some_iff.1 hb
  simp only [getElem_map, getElem_range] at hb'
  rw [hb']; exact hbD

/-- **Deterministic core of Theorem 7.** Against a fixed strong adversary whose runs are valid,
have linearizable registers and a write strong-linearization function for `R1`, at most one coin
sequence makes every round be entered. -/
theorem forever_subsingleton : (Forever σ).Subsingleton := by
  intro ω hω ω' hω'
  let p0 : Fin n := ⟨0, by omega⟩
  have hp0 : p0.val = 0 := rfl
  funext r
  induction r using Nat.strong_induction_on with
  | _ r IH =>
  obtain ⟨m₀, hm₀⟩ := exists_m₀ hn hvalid hlin hf hω hp0 r
  have hfc := flipCount_of_h2 hvalid hp0 hm₀
  have he : genRun σ ω m₀ = genRun σ ω' m₀ := genRun_congr σ m₀ (fun k hk => IH k (by omega))
  have hm₀' := hm₀; rw [he] at hm₀'
  have h1 := coin_eq hn hvalid hlin hf hω hp0 hm₀
  have h2 := coin_eq hn hvalid hlin hf hω' hp0 hm₀'
  rw [he] at h1
  exact Bool.eq_iff_iff.2 (h1.trans h2.symm)

end Adversary

end Thm7

end Podc.RegisterLinTermination.Game
