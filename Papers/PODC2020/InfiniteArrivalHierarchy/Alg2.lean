import Papers.PODC2020.InfiniteArrivalHierarchy.Objects

/-!
# Algorithm 2 of Perrin–Mostéfaoui–Bonin (PODC 2020): consensus in `MA₂[consₙ⟨ℕ⟩]`

Section 5 ("No object has consensus number ∞₁¹"). Processes `p₀, p₁, …` (finitely many of
which take steps: finite arrival model `M₂`) share three infinite arrays

* `greaterId[r]`: boolean registers, initially `false` (`Obj.gid r`);
* `cons[r]`: `r`-process consensus objects `consᵣ⟨V⟩` (`Obj.cons r`), whose responses after the
  first `r` invocations are arbitrary (`junk r`);
* `adopt[r]`: registers over `Option V`, initially `⊥ = none` (`Obj.adopt r`).

Code for `pᵢ` with input `valᵢ`:
```
vᵢ ← valᵢ
for r = 0, 1, 2, … :
  if i ≥ r then greaterId[r] ← true
  else adopt[r] ← cons[r].propose(vᵢ)
  if ¬ greaterId[r] then return adopt[r]
  if adopt[r] ≠ ⊥ then vᵢ ← adopt[r]
```
Each shared access is one step (`adopt[r] ← cons[r].propose(vᵢ)` is two steps: the proposal and
the write).

## Main statements

* `count_eq`, `claim2`: Claim 2 — at most `r` invocations on `cons[r]` (exactly the number of
  processes `q < r` that proposed at round `r`), so the unspecified responses never occur;
* `agreement` (Lemma 6), `validity` (Lemma 7), `waitFree` (Lemma 5, finite arrival model);
* `alg2_solvesCons`: Algorithm 2 solves consensus for all finite schedules and wait-free in `M₂`,
  for every behaviour `junk` of the `consₙ` objects beyond their `n` first invocations;
* `round_le_of_bound`: a process never goes beyond round `N + 1` if all ids are `≤ N`.

The paper states Claim 2 and Lemmas 5–7 without proofs; the proofs here are ours.
-/

namespace Podc.InfiniteArrivalHierarchy.Alg2

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

/-- Shared objects: `greaterId[r]`, `cons[r]`, `adopt[r]`. -/
inductive Obj
  | gid (r : ℕ)
  | cons (r : ℕ)
  | adopt (r : ℕ)
  deriving DecidableEq

/-- The sequential specifications of the shared objects. -/
abbrev T (V : Type) (junk : ℕ → ℕ → V → V) : Obj → ObjSpec
  | .gid _ => register Bool false
  | .cons r => consnObj V r (junk r)
  | .adopt _ => register (Option V) none

/-- Local states of process `pᵢ` (with id `i`, current round `r`, current value `v`). -/
inductive Loc (V : Type)
  /-- About to write `greaterId[r] ← true` (`i ≥ r`). -/
  | gidW (i r : ℕ) (v : V)
  /-- About to invoke `cons[r].propose(v)` (`i < r`). -/
  | prop (i r : ℕ) (v : V)
  /-- About to write `adopt[r] ← d`, `d` the response of `cons[r]`. -/
  | adoptW (i r : ℕ) (v d : V)
  /-- About to read `greaterId[r]`. -/
  | gidR (i r : ℕ) (v : V)
  /-- Read `greaterId[r] = false`; about to read `adopt[r]` and return it. -/
  | retR (i r : ℕ) (v : V)
  /-- Read `greaterId[r] = true`; about to read `adopt[r]` and adopt it if `≠ ⊥`. -/
  | adoptR (i r : ℕ) (v : V)
  /-- Returned `w` at round `r`. -/
  | done (i r : ℕ) (w : V)

variable {V : Type} {junk : ℕ → ℕ → V → V}

namespace Loc

/-- The id of the process. -/
def id : Loc V → ℕ
  | gidW i .. | prop i .. | adoptW i .. | gidR i .. | retR i .. | adoptR i .. | done i .. => i

/-- The current round. -/
def round : Loc V → ℕ
  | gidW _ r _ | prop _ r _ | adoptW _ r _ _ | gidR _ r _ | retR _ r _ | adoptR _ r _
  | done _ r _ => r

/-- The position inside a round. -/
def phase : Loc V → ℕ
  | gidW .. => 0
  | prop .. => 0
  | adoptW .. => 1
  | gidR .. => 2
  | retR .. => 3
  | adoptR .. => 3
  | done .. => 4

/-- All values held in the local state satisfy `P`. -/
def AllVals (P : V → Prop) : Loc V → Prop
  | gidW _ _ v | prop _ _ v | gidR _ _ v | retR _ _ v | adoptR _ _ v | done _ _ v => P v
  | adoptW _ _ v d => P v ∧ P d

/-- Well-formedness: who writes `greaterId[r]` and who proposes on `cons[r]`. -/
def WF : Loc V → Prop
  | gidW i r _ => r ≤ i
  | prop i r _ | adoptW i r _ _ | retR i r _ | done i r _ => i < r
  | gidR .. | adoptR .. => True

/-- The process has read `greaterId[r] = false` (it returns at round `r`). -/
def Decided (r : ℕ) : Loc V → Prop
  | retR _ r' _ | done _ r' _ => r' = r
  | _ => False

end Loc

/-- The first state of round `r`. -/
def start (i r : ℕ) (v : V) : Loc V := if r ≤ i then .gidW i r v else .prop i r v

/-- The code of Algorithm 2: the next shared access in each local state. -/
def act (V : Type) (junk : ℕ → ℕ → V → V) : Loc V → Act (T V junk) (Loc V) V
  | .gidW i r v => .access (.gid r) (.write true) (fun _ => .gidR i r v)
  | .prop i r v => .access (.cons r) v (fun d => .adoptW i r v d)
  | .adoptW i r v d => .access (.adopt r) (.write (some d)) (fun _ => .gidR i r v)
  | .gidR i r v => .access (.gid r) .read (fun b => if b then .adoptR i r v else .retR i r v)
  | .retR i r v => .access (.adopt r) .read (fun w => .done i r (w.getD v))
  | .adoptR i r v => .access (.adopt r) .read (fun w => start i (r + 1) (w.getD v))
  | .done _ _ w => .out w

/-- Algorithm 2 (process `pᵢ` starts round `0` with `vᵢ = valᵢ`). -/
def alg2 (V : Type) (junk : ℕ → ℕ → V → V) : Alg (T V junk) ℕ V V where
  L := Loc V
  init p x := .gidW p 0 x
  act := act V junk
  mem₀
    | .gid _ => false
    | .cons _ => (0, none)
    | .adopt _ => none

/-- Configurations of Algorithm 2. -/
abbrev Conf (V : Type) (junk : ℕ → ℕ → V → V) := Cfg (alg2 V junk)

/-- The content of `greaterId[r]`. -/
def G (C : Conf V junk) (r : ℕ) : Bool := C.mem (.gid r)
/-- The state of `cons[r]` (number of invocations, decided value). -/
def K (C : Conf V junk) (r : ℕ) : ℕ × Option V := C.mem (.cons r)
/-- The content of `adopt[r]`. -/
def A (C : Conf V junk) (r : ℕ) : Option V := C.mem (.adopt r)

/-! ### Helpers: one step of each kind -/

section Steps

open Function

variable {C : Conf V junk} {p i r : ℕ} {v d : V}

private lemma upd_self_ne {o o' : Obj} (h : o' ≠ o) (m : (o : Obj) → (T V junk o).State)
    (s : (T V junk o).State) : update m o s o' = m o' := update_of_ne h _ _

lemma G_update_gid (m : (o : Obj) → (T V junk o).State) (r : ℕ) (b : Bool) :
    (fun r' => (update m (.gid r) b (.gid r') : Bool)) = update (fun r' => m (.gid r')) r b := by
  funext r'
  by_cases h : r' = r
  · subst h; simp
  · rw [upd_self_ne (by simp [h]), update_of_ne h]

lemma K_update_cons (m : (o : Obj) → (T V junk o).State) (r : ℕ) (s : ℕ × Option V) :
    (fun r' => (update m (.cons r) s (.cons r') : ℕ × Option V)) =
      update (fun r' => m (.cons r')) r s := by
  funext r'
  by_cases h : r' = r
  · subst h; simp
  · rw [upd_self_ne (by simp [h]), update_of_ne h]

lemma A_update_adopt (m : (o : Obj) → (T V junk o).State) (r : ℕ) (s : Option V) :
    (fun r' => (update m (.adopt r) s (.adopt r') : Option V)) =
      update (fun r' => m (.adopt r')) r s := by
  funext r'
  by_cases h : r' = r
  · subst h; simp
  · rw [upd_self_ne (by simp [h]), update_of_ne h]

lemma step_gidW (h : C.loc p = .gidW i r v) :
    (C.step p).loc = update C.loc p (.gidR i r v) ∧ G (C.step p) = update (G C) r true ∧
      K (C.step p) = K C ∧ A (C.step p) = A C := by
  have hact : (alg2 V junk).act (C.loc p) =
      .access (.gid r) (.write true) (fun _ => .gidR i r v) := by rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact G_update_gid C.mem r true
  · funext r'; simp only [K]; exact upd_self_ne (by simp) _ _
  · funext r'; simp only [A]; exact upd_self_ne (by simp) _ _

lemma step_prop (h : C.loc p = .prop i r v) :
    (C.step p).loc = update C.loc p
        (.adoptW i r v (if (K C r).1 < r then (K C r).2.getD v else junk r (K C r).1 v)) ∧
      G (C.step p) = G C ∧
      K (C.step p) = update (K C) r ((K C r).1 + 1, some ((K C r).2.getD v)) ∧
      A (C.step p) = A C := by
  have hact : (alg2 V junk).act (C.loc p) =
      .access (.cons r) v (fun d => .adoptW i r v d) := by rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · funext r'; simp only [G]; exact upd_self_ne (by simp) _ _
  · exact K_update_cons C.mem r _
  · funext r'; simp only [A]; exact upd_self_ne (by simp) _ _

lemma step_adoptW (h : C.loc p = .adoptW i r v d) :
    (C.step p).loc = update C.loc p (.gidR i r v) ∧ G (C.step p) = G C ∧
      K (C.step p) = K C ∧ A (C.step p) = update (A C) r (some d) := by
  have hact : (alg2 V junk).act (C.loc p) =
      .access (.adopt r) (.write (some d)) (fun _ => .gidR i r v) := by rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · funext r'; simp only [G]; exact upd_self_ne (by simp) _ _
  · funext r'; simp only [K]; exact upd_self_ne (by simp) _ _
  · exact A_update_adopt C.mem r _

lemma step_gidR (h : C.loc p = .gidR i r v) :
    (C.step p).loc = update C.loc p (if G C r then .adoptR i r v else .retR i r v) ∧
      G (C.step p) = G C ∧ K (C.step p) = K C ∧ A (C.step p) = A C := by
  have hact : (alg2 V junk).act (C.loc p) =
      .access (.gid r) .read (fun b => if b then .adoptR i r v else .retR i r v) := by
    rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show (fun r' => (update C.mem (.gid r) (C.mem (.gid r)) (.gid r') : Bool)) = _
    rw [update_eq_self]; rfl
  · funext r'; simp only [K]; exact upd_self_ne (by simp) _ _
  · funext r'; simp only [A]; exact upd_self_ne (by simp) _ _

lemma step_retR (h : C.loc p = .retR i r v) :
    (C.step p).loc = update C.loc p (.done i r ((A C r).getD v)) ∧
      G (C.step p) = G C ∧ K (C.step p) = K C ∧ A (C.step p) = A C := by
  have hact : (alg2 V junk).act (C.loc p) =
      .access (.adopt r) .read (fun w => .done i r (w.getD v)) := by rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · funext r'; simp only [G]; exact upd_self_ne (by simp) _ _
  · funext r'; simp only [K]; exact upd_self_ne (by simp) _ _
  · show (fun r' => (update C.mem (.adopt r) (C.mem (.adopt r)) (.adopt r') : Option V)) = _
    rw [update_eq_self]; rfl

lemma step_adoptR (h : C.loc p = .adoptR i r v) :
    (C.step p).loc = update C.loc p (start i (r + 1) ((A C r).getD v)) ∧
      G (C.step p) = G C ∧ K (C.step p) = K C ∧ A (C.step p) = A C := by
  have hact : (alg2 V junk).act (C.loc p) =
      .access (.adopt r) .read (fun w => start i (r + 1) (w.getD v)) := by rw [h]; rfl
  rw [Cfg.step_of_access hact]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · funext r'; simp only [G]; exact upd_self_ne (by simp) _ _
  · funext r'; simp only [K]; exact upd_self_ne (by simp) _ _
  · show (fun r' => (update C.mem (.adopt r) (C.mem (.adopt r)) (.adopt r') : Option V)) = _
    rw [update_eq_self]; rfl

lemma step_done (h : C.loc p = .done i r d) : C.step p = C :=
  Cfg.step_of_out (v := d) (by unfold Cfg.Out; rw [h]; rfl)

end Steps

/-! ### Lemmas about local states -/

section LocLemmas

@[simp] lemma start_id (i r : ℕ) (v : V) : (start i r v).id = i := by
  unfold start; split <;> rfl

@[simp] lemma start_round (i r : ℕ) (v : V) : (start i r v).round = r := by
  unfold start; split <;> rfl

@[simp] lemma start_phase (i r : ℕ) (v : V) : (start i r v).phase = 0 := by
  unfold start; split <;> rfl

@[simp] lemma start_allVals (P : V → Prop) (i r : ℕ) (v : V) :
    (start i r v).AllVals P ↔ P v := by
  unfold start; split <;> rfl

lemma start_wf (i r : ℕ) (v : V) : (start i r v).WF := by
  unfold start; split
  · assumption
  · show i < r; omega

lemma start_ne_adoptW (i r : ℕ) (v : V) (i' r' : ℕ) (v' d' : V) :
    start i r v ≠ .adoptW i' r' v' d' := by
  unfold start; split <;> nofun

lemma start_ne_gidR (i r : ℕ) (v : V) (i' r' : ℕ) (v' : V) : start i r v ≠ .gidR i' r' v' := by
  unfold start; split <;> nofun

lemma start_ne_adoptR (i r : ℕ) (v : V) (i' r' : ℕ) (v' : V) :
    start i r v ≠ .adoptR i' r' v' := by
  unfold start; split <;> nofun

lemma start_ne_done (i r : ℕ) (v : V) (i' r' : ℕ) (w : V) : start i r v ≠ .done i' r' w := by
  unfold start; split <;> nofun

lemma start_not_decided (i r : ℕ) (v : V) (r' : ℕ) : ¬ (start i r v).Decided r' := by
  unfold start; split <;> exact id

lemma Loc.AllVals.mono {P Q : V → Prop} (hPQ : ∀ v, P v → Q v) {l : Loc V}
    (h : l.AllVals P) : l.AllVals Q := by
  cases l <;> simp only [Loc.AllVals] at h ⊢ <;>
    first | exact hPQ _ h | exact ⟨hPQ _ h.1, hPQ _ h.2⟩

end LocLemmas

/-! ### The invariant -/

section Inv

open Function

/-- The process with local state `l` has invoked `cons[r].propose` (if its id is `< r`). -/
def Proposed (r : ℕ) (l : Loc V) : Prop := r < l.round ∨ (l.round = r ∧ 1 ≤ l.phase)

instance (r : ℕ) : DecidablePred (Proposed (V := V) r) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The number of processes `q < r` that have invoked `cons[r].propose`. -/
def nProp (L : ℕ → Loc V) (r : ℕ) : ℕ := ((Finset.range r).filter (fun q => Proposed r (L q))).card

lemma nProp_le (L : ℕ → Loc V) (r : ℕ) : nProp L r ≤ r :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- Once a process has read `greaterId[r] = false`, the value `d` decided by `cons[r]` is in
`adopt[r]`, it is returned by every process returning at round `r`, it is the only value held by
processes at later rounds and the only value decided by later `cons[r']`. -/
def DecInv (L : ℕ → Loc V) (k : ℕ → ℕ × Option V) (a : ℕ → Option V) (r : ℕ) : Prop :=
  ∃ d, (k r).2 = some d ∧ a r = some d ∧ (∀ q i w, L q = .done i r w → w = d) ∧
    (∀ q, r < (L q).round → (L q).AllVals (· = d)) ∧
    (∀ r', r < r' → ∀ w, (k r').2 = some w → w = d)

/-- Values that `p` may hold after the schedule `σ` (validity). -/
def Ok (x : ℕ → V) (σ : List ℕ) (p : ℕ) (v : V) : Prop := v = x p ∨ ∃ q ∈ σ, x q = v

/-- The invariant of Algorithm 2, on local states `L`, `greaterId` `g`, `cons` `k` and
`adopt` `a`. -/
structure I (x : ℕ → V) (σ : List ℕ) (L : ℕ → Loc V) (g : ℕ → Bool) (k : ℕ → ℕ × Option V)
    (a : ℕ → Option V) : Prop where
  id : ∀ p, (L p).id = p
  wf : ∀ p, (L p).WF
  adoptW_dec : ∀ p i r v d, L p = .adoptW i r v d → (k r).2 = some d
  adopt_dec : ∀ r w, a r = some w → (k r).2 = some w
  gidR_hi : ∀ p i r v, L p = .gidR i r v → r ≤ i → g r = true
  adoptR_gid : ∀ p i r v, L p = .adoptR i r v → g r = true
  round_gid : ∀ p r, r < (L p).round → g r = true
  passed : ∀ p r, (L p).id < r → (L p).round = r → 2 ≤ (L p).phase → a r ≠ none
  cons_none : ∀ r r', r < r' → g r = false → (k r').2 = none
  count : ∀ r, (k r).1 = nProp L r
  dec : ∀ r, (∃ p, (L p).Decided r) → DecInv L k a r
  valid_loc : ∀ p, (L p).AllVals (Ok x σ p)
  valid_cons : ∀ r w, (k r).2 = some w → ∃ q ∈ σ, x q = w
  gid_writer : ∀ r, g r = true → ∃ q ∈ σ, r ≤ q

variable {x : ℕ → V} {σ : List ℕ} {L : ℕ → Loc V} {g : ℕ → Bool} {k : ℕ → ℕ × Option V}
  {a : ℕ → Option V} {p i r : ℕ} {v d : V}

lemma Ok.mono {q : ℕ} {w : V} (h : Ok x σ q w) (p : ℕ) : Ok x (σ ++ [p]) q w := by
  rcases h with h | ⟨q', hq', h⟩
  · exact Or.inl h
  · exact Or.inr ⟨q', by simp [hq'], h⟩

lemma I.mono (hI : I x σ L g k a) (p : ℕ) : I x (σ ++ [p]) L g k a where
  id := hI.id
  wf := hI.wf
  adoptW_dec := hI.adoptW_dec
  adopt_dec := hI.adopt_dec
  gidR_hi := hI.gidR_hi
  adoptR_gid := hI.adoptR_gid
  round_gid := hI.round_gid
  passed := hI.passed
  cons_none := hI.cons_none
  count := hI.count
  dec := hI.dec
  valid_loc q := (hI.valid_loc q).mono fun _ h => h.mono p
  valid_cons r w h := by
    obtain ⟨q, hq, e⟩ := hI.valid_cons r w h; exact ⟨q, by simp [hq], e⟩
  gid_writer r h := by
    obtain ⟨q, hq, e⟩ := hI.gid_writer r h; exact ⟨q, by simp [hq], e⟩

lemma upd_forall {P : ℕ → Loc V → Prop} {l : Loc V} (hp : P p l) (h : ∀ q, q ≠ p → P q (L q)) :
    ∀ q, P q (update L p l q) := by
  intro q
  rcases eq_or_ne q p with rfl | hq
  · simpa using hp
  · simpa [update_of_ne hq] using h q hq

lemma exists_update_iff {P : Loc V → Prop} {l : Loc V} (h : P l ↔ P (L p)) :
    (∃ q, P (update L p l q)) ↔ ∃ q, P (L q) := by
  constructor
  · rintro ⟨q, hq⟩
    rcases eq_or_ne q p with rfl | hqp
    · exact ⟨q, h.1 (by simpa using hq)⟩
    · exact ⟨q, by simpa [update_of_ne hqp] using hq⟩
  · rintro ⟨q, hq⟩
    rcases eq_or_ne q p with rfl | hqp
    · exact ⟨q, by simpa using h.2 hq⟩
    · exact ⟨q, by simpa [update_of_ne hqp] using hq⟩

lemma nProp_update_eq {l : Loc V} {r : ℕ} (h : p < r → (Proposed r l ↔ Proposed r (L p))) :
    nProp (update L p l) r = nProp L r := by
  unfold nProp
  congr 1
  apply Finset.filter_congr
  intro q hq
  rcases eq_or_ne q p with rfl | hqp
  · simpa using h (by simpa using hq)
  · simp [update_of_ne hqp]

lemma nProp_update_succ {l : Loc V} {r : ℕ} (hp : p < r) (h0 : ¬ Proposed r (L p))
    (h1 : Proposed r l) : nProp (update L p l) r = nProp L r + 1 := by
  unfold nProp
  rw [← Finset.card_insert_of_notMem (s := (Finset.range r).filter (fun q => Proposed r (L q)))
    (a := p) (by simp [h0])]
  congr 1
  ext q
  rcases eq_or_ne q p with rfl | hqp
  · simp [hp, h1]
  · simp [hqp]

/-- `DecInv` is preserved when a process changes its local state without changing its round, its
values, and without returning. -/
lemma DecInv.frame {l : Loc V} {r : ℕ} (hD : DecInv L k a r) (hround : l.round = (L p).round)
    (hvals : ∀ P, l.AllVals P ↔ (L p).AllVals P)
    (hdone : ∀ i w, l = .done i r w → L p = .done i r w) : DecInv (update L p l) k a r := by
  obtain ⟨d, hk, ha, hdn, hv, hk'⟩ := hD
  refine ⟨d, hk, ha, ?_, ?_, hk'⟩
  · intro q i w hq
    rcases eq_or_ne q p with rfl | hqp
    · exact hdn q i w (hdone i w (by simpa using hq))
    · exact hdn q i w (by simpa [update_of_ne hqp] using hq)
  · intro q hq
    rcases eq_or_ne q p with rfl | hqp
    · simp only [update_self] at hq ⊢
      exact (hvals _).2 (hv q (hround ▸ hq))
    · simp only [update_of_ne hqp] at hq ⊢
      exact hv q hq

end Inv

/-! ### Preservation of the invariant, step by step -/

section Preservation

open Function

variable {x : ℕ → V} {σ : List ℕ} {L : ℕ → Loc V} {g : ℕ → Bool} {k : ℕ → ℕ × Option V}
  {a : ℕ → Option V} {p i r : ℕ} {v d : V}

lemma I.step_gidW (hI : I x σ L g k a) (h : L p = .gidW i r v) :
    I x (σ ++ [p]) (update L p (.gidR i r v)) (update g r true) k a := by
  have hi : i = p := by simpa [h, Loc.id] using hI.id p
  have hri : r ≤ i := by simpa [h, Loc.WF] using hI.wf p
  have hI' := hI.mono p
  have hg : ∀ r', g r' = true → update g r true r' = true := by
    intro r' h'; rcases eq_or_ne r' r with rfl | hr
    · simp
    · simp [update_of_ne hr, h']
  refine ⟨?_, ?_, ?_, hI.adopt_dec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI'.valid_cons, ?_⟩
  · exact upd_forall (P := fun q l => l.id = q) hi (fun q _ => hI.id q)
  · exact upd_forall (P := fun _ l => l.WF) trivial (fun q _ => hI.wf q)
  · exact upd_forall (P := fun _ l => ∀ i r v d, l = .adoptW i r v d → (k r).2 = some d)
      (by rintro _ _ _ _ ⟨⟩) (fun q _ => hI.adoptW_dec q)
  · exact upd_forall
      (P := fun _ l => ∀ i' r' v', l = .gidR i' r' v' → r' ≤ i' → update g r true r' = true)
      (by rintro _ _ _ ⟨⟩ -; simp)
      (fun q _ i' r' v' hq hle => hg _ (hI.gidR_hi q i' r' v' hq hle))
  · exact upd_forall
      (P := fun _ l => ∀ i' r' v', l = .adoptR i' r' v' → update g r true r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ i' r' v' hq => hg _ (hI.adoptR_gid q i' r' v' hq))
  · exact upd_forall (P := fun _ l => ∀ r', r' < l.round → update g r true r' = true)
      (fun r' hr' => hg _ (hI.round_gid p r' (by rw [h]; exact hr')))
      (fun q _ r' hr' => hg _ (hI.round_gid q r' hr'))
  · exact upd_forall
      (P := fun _ l => ∀ r', l.id < r' → l.round = r' → 2 ≤ l.phase → a r' ≠ none)
      (by intro r' h1 h2 _; simp only [Loc.id, Loc.round] at h1 h2; omega)
      (fun q _ => hI.passed q)
  · intro r1 r2 hlt hf
    apply hI.cons_none r1 r2 hlt
    rcases eq_or_ne r1 r with rfl | hr
    · simp at hf
    · simpa [update_of_ne hr] using hf
  · intro r'
    rw [hI.count r', nProp_update_eq]
    intro hp
    rw [h]; simp only [Proposed, Loc.round, Loc.phase]; omega
  · intro r' hex
    have hex' := (exists_update_iff (P := fun l => l.Decided r') (by rw [h]; exact Iff.rfl)).1 hex
    exact (hI.dec r' hex').frame (by rw [h]; rfl) (fun P => by rw [h]; exact Iff.rfl)
      (by rintro _ _ ⟨⟩)
  · exact upd_forall (P := fun q l => l.AllVals (Ok x (σ ++ [p]) q))
      (by have := hI'.valid_loc p; rw [h] at this; exact this) (fun q _ => hI'.valid_loc q)
  · intro r' hr'
    rcases eq_or_ne r' r with rfl | hr
    · exact ⟨p, by simp, hi ▸ hri⟩
    · exact hI'.gid_writer r' (by simpa [update_of_ne hr] using hr')

lemma I.count_lt (hI : I x σ L g k a) (h : L p = .prop i r v) : (k r).1 < r := by
  have hi : i = p := by simpa [h, Loc.id] using hI.id p
  have hir : i < r := by simpa [h, Loc.WF] using hI.wf p
  rw [hI.count r]
  have hsub : (Finset.range r).filter (fun q => Proposed r (L q)) ⊆ (Finset.range r).erase p := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    simp only [Finset.mem_erase, Finset.mem_range]
    refine ⟨?_, hq.1⟩
    rintro rfl
    have := hq.2
    rw [h] at this
    simp [Proposed, Loc.round, Loc.phase] at this
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp; omega), Finset.card_range] at this
  unfold nProp
  omega

lemma I.step_prop (hI : I x σ L g k a) (h : L p = .prop i r v) :
    I x (σ ++ [p]) (update L p (.adoptW i r v ((k r).2.getD v))) g
      (update k r ((k r).1 + 1, some ((k r).2.getD v))) a := by
  have hi : i = p := by simpa [h, Loc.id] using hI.id p
  have hir : i < r := by simpa [h, Loc.WF] using hI.wf p
  have hI' := hI.mono p
  have hk' : ∀ r' w, (k r').2 = some w →
      (update k r ((k r).1 + 1, some ((k r).2.getD v)) r').2 = some w := by
    intro r' w hw
    rcases eq_or_ne r' r with rfl | hr
    · simp [hw]
    · simpa [update_of_ne hr] using hw
  have hOkv : Ok x (σ ++ [p]) p v := by
    have := hI'.valid_loc p; rw [h] at this; exact this
  have hOkD : Ok x (σ ++ [p]) p ((k r).2.getD v) := by
    rcases hkr : (k r).2 with _ | w
    · simpa using hOkv
    · simp only [Option.getD_some]; exact Or.inr (hI'.valid_cons r w hkr)
  refine ⟨?_, ?_, ?_, fun r' w hw => hk' r' w (hI.adopt_dec r' w hw), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hI'.gid_writer⟩
  · exact upd_forall (P := fun q l => l.id = q) hi (fun q _ => hI.id q)
  · exact upd_forall (P := fun _ l => l.WF) hir (fun q _ => hI.wf q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v' d', l = .adoptW i' r' v' d' →
        (update k r ((k r).1 + 1, some ((k r).2.getD v)) r').2 = some d')
      (by rintro _ _ _ _ ⟨⟩; simp)
      (fun q _ i' r' v' d' hq => hk' _ _ (hI.adoptW_dec q i' r' v' d' hq))
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .gidR i' r' v' → r' ≤ i' → g r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ => hI.gidR_hi q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .adoptR i' r' v' → g r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ => hI.adoptR_gid q)
  · exact upd_forall (P := fun _ l => ∀ r', r' < l.round → g r' = true)
      (fun r' hr' => hI.round_gid p r' (by rw [h]; exact hr')) (fun q _ => hI.round_gid q)
  · exact upd_forall
      (P := fun _ l => ∀ r', l.id < r' → l.round = r' → 2 ≤ l.phase → a r' ≠ none)
      (by intro r' _ _ h2; simp [Loc.phase] at h2) (fun q _ => hI.passed q)
  · intro r1 r2 hlt hf
    rcases eq_or_ne r2 r with rfl | hr
    · exact absurd (hI.round_gid p r1 (by rw [h]; exact hlt)) (by simp [hf])
    · simpa [update_of_ne hr] using hI.cons_none r1 r2 hlt hf
  · intro r'
    rcases eq_or_ne r' r with rfl | hr
    · rw [update_self, hI.count, nProp_update_succ (hi ▸ hir)]
      · rw [h]; simp [Proposed, Loc.round, Loc.phase]
      · simp [Proposed, Loc.round, Loc.phase]
    · rw [update_of_ne hr, hI.count r', nProp_update_eq]
      intro _
      rw [h]; simp only [Proposed, Loc.round, Loc.phase]; omega
  · intro r' hex
    have hex' := (exists_update_iff (P := fun l => l.Decided r') (by rw [h]; exact Iff.rfl)).1 hex
    obtain ⟨d0, hk, ha, hdn, hv, hk2⟩ := hI.dec r' hex'
    have hD : r' < r → (k r).2.getD v = d0 := by
      intro hlt
      rcases hkr : (k r).2 with _ | w
      · have := hv p (by rw [h]; exact hlt); rw [h] at this; simpa [Loc.AllVals] using this
      · simpa using hk2 r hlt w hkr
    refine ⟨d0, hk' _ _ hk, ha, ?_, ?_, ?_⟩
    · intro q i' w hq
      rcases eq_or_ne q p with rfl | hqp
      · simp at hq
      · exact hdn q i' w (by simpa [update_of_ne hqp] using hq)
    · intro q hq
      rcases eq_or_ne q p with rfl | hqp
      · simp only [update_self] at hq ⊢
        have := hv q (by rw [h]; exact hq); rw [h] at this
        exact ⟨this, hD hq⟩
      · simp only [update_of_ne hqp] at hq ⊢; exact hv q hq
    · intro r2 hlt w hw
      rcases eq_or_ne r2 r with rfl | hr
      · simp only [update_self, Option.some.injEq] at hw
        rw [← hw]; exact hD hlt
      · exact hk2 r2 hlt w (by simpa [update_of_ne hr] using hw)
  · exact upd_forall (P := fun q l => l.AllVals (Ok x (σ ++ [p]) q)) ⟨hOkv, hOkD⟩
      (fun q _ => hI'.valid_loc q)
  · intro r2 w hw
    rcases eq_or_ne r2 r with rfl | hr
    · simp only [update_self, Option.some.injEq] at hw
      rcases hOkD with h1 | h1
      · exact ⟨p, by simp, by rw [← hw, h1]⟩
      · rw [← hw]; exact h1
    · exact hI'.valid_cons r2 w (by simpa [update_of_ne hr] using hw)

lemma I.step_adoptW (hI : I x σ L g k a) (h : L p = .adoptW i r v d) :
    I x (σ ++ [p]) (update L p (.gidR i r v)) g k (update a r (some d)) := by
  have hi : i = p := by simpa [h, Loc.id] using hI.id p
  have hir : i < r := by simpa [h, Loc.WF] using hI.wf p
  have hd := hI.adoptW_dec p i r v d h
  have hI' := hI.mono p
  have ha' : ∀ r', a r' ≠ none → update a r (some d) r' ≠ none := by
    intro r' h'; rcases eq_or_ne r' r with rfl | hr
    · simp
    · simpa [update_of_ne hr] using h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.cons_none, ?_, ?_, ?_, hI'.valid_cons,
    hI'.gid_writer⟩
  · exact upd_forall (P := fun q l => l.id = q) hi (fun q _ => hI.id q)
  · exact upd_forall (P := fun _ l => l.WF) trivial (fun q _ => hI.wf q)
  · exact upd_forall (P := fun _ l => ∀ i r v d, l = .adoptW i r v d → (k r).2 = some d)
      (by rintro _ _ _ _ ⟨⟩) (fun q _ => hI.adoptW_dec q)
  · intro r' w hw
    rcases eq_or_ne r' r with rfl | hr
    · simp only [update_self, Option.some.injEq] at hw; rw [← hw]; exact hd
    · exact hI.adopt_dec r' w (by simpa [update_of_ne hr] using hw)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .gidR i' r' v' → r' ≤ i' → g r' = true)
      (by rintro _ _ _ ⟨⟩ hle; omega) (fun q _ => hI.gidR_hi q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .adoptR i' r' v' → g r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ => hI.adoptR_gid q)
  · exact upd_forall (P := fun _ l => ∀ r', r' < l.round → g r' = true)
      (fun r' hr' => hI.round_gid p r' (by rw [h]; exact hr')) (fun q _ => hI.round_gid q)
  · exact upd_forall
      (P := fun _ l => ∀ r', l.id < r' → l.round = r' → 2 ≤ l.phase →
        update a r (some d) r' ≠ none)
      (by intro r' _ h2 _; simp only [Loc.round] at h2; subst h2; simp)
      (fun q _ r' h1 h2 h3 => ha' _ (hI.passed q r' h1 h2 h3))
  · intro r'
    rw [hI.count r', nProp_update_eq]
    intro _
    rw [h]; simp only [Proposed, Loc.round, Loc.phase]; omega
  · intro r' hex
    have hex' := (exists_update_iff (P := fun l => l.Decided r') (by rw [h]; exact Iff.rfl)).1 hex
    obtain ⟨d0, hk, ha, hdn, hv, hk2⟩ := hI.dec r' hex'
    refine ⟨d0, hk, ?_, ?_, ?_, hk2⟩
    · rcases eq_or_ne r' r with rfl | hr
      · rw [hd] at hk; simpa using hk
      · simpa [update_of_ne hr] using ha
    · intro q i' w hq
      rcases eq_or_ne q p with rfl | hqp
      · simp at hq
      · exact hdn q i' w (by simpa [update_of_ne hqp] using hq)
    · intro q hq
      rcases eq_or_ne q p with rfl | hqp
      · simp only [update_self] at hq ⊢
        have := hv q (by rw [h]; exact hq); rw [h] at this
        exact this.1
      · simp only [update_of_ne hqp] at hq ⊢; exact hv q hq
  · exact upd_forall (P := fun q l => l.AllVals (Ok x (σ ++ [p]) q))
      (by have := hI'.valid_loc p; rw [h] at this; exact this.1) (fun q _ => hI'.valid_loc q)

lemma I.step_gidR_true (hI : I x σ L g k a) (h : L p = .gidR i r v) (hg : g r = true) :
    I x (σ ++ [p]) (update L p (.adoptR i r v)) g k a := by
  have hi : i = p := by simpa [h, Loc.id] using hI.id p
  have hI' := hI.mono p
  refine ⟨?_, ?_, ?_, hI.adopt_dec, ?_, ?_, ?_, ?_, hI.cons_none, ?_, ?_, ?_, hI'.valid_cons,
    hI'.gid_writer⟩
  · exact upd_forall (P := fun q l => l.id = q) hi (fun q _ => hI.id q)
  · exact upd_forall (P := fun _ l => l.WF) trivial (fun q _ => hI.wf q)
  · exact upd_forall (P := fun _ l => ∀ i r v d, l = .adoptW i r v d → (k r).2 = some d)
      (by rintro _ _ _ _ ⟨⟩) (fun q _ => hI.adoptW_dec q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .gidR i' r' v' → r' ≤ i' → g r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ => hI.gidR_hi q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .adoptR i' r' v' → g r' = true)
      (by rintro _ _ _ ⟨⟩; exact hg) (fun q _ => hI.adoptR_gid q)
  · exact upd_forall (P := fun _ l => ∀ r', r' < l.round → g r' = true)
      (fun r' hr' => hI.round_gid p r' (by rw [h]; exact hr')) (fun q _ => hI.round_gid q)
  · exact upd_forall
      (P := fun _ l => ∀ r', l.id < r' → l.round = r' → 2 ≤ l.phase → a r' ≠ none)
      (fun r' h1 h2 _ => hI.passed p r' (by rw [h]; exact h1) (by rw [h]; exact h2)
        (by rw [h]; simp [Loc.phase]))
      (fun q _ => hI.passed q)
  · intro r'
    rw [hI.count r', nProp_update_eq]
    intro _
    rw [h]; simp only [Proposed, Loc.round, Loc.phase]; omega
  · intro r' hex
    have hex' := (exists_update_iff (P := fun l => l.Decided r') (by rw [h]; exact Iff.rfl)).1 hex
    exact (hI.dec r' hex').frame (by rw [h]; rfl) (fun P => by rw [h]; exact Iff.rfl)
      (by rintro _ _ ⟨⟩)
  · exact upd_forall (P := fun q l => l.AllVals (Ok x (σ ++ [p]) q))
      (by have := hI'.valid_loc p; rw [h] at this; exact this) (fun q _ => hI'.valid_loc q)

lemma I.step_gidR_false (hI : I x σ L g k a) (h : L p = .gidR i r v) (hg : g r = false) :
    I x (σ ++ [p]) (update L p (.retR i r v)) g k a := by
  have hi : i = p := by simpa [h, Loc.id] using hI.id p
  have hir : i < r := by
    by_contra hle
    have := hI.gidR_hi p i r v h (by omega)
    simp [hg] at this
  have hI' := hI.mono p
  refine ⟨?_, ?_, ?_, hI.adopt_dec, ?_, ?_, ?_, ?_, hI.cons_none, ?_, ?_, ?_, hI'.valid_cons,
    hI'.gid_writer⟩
  · exact upd_forall (P := fun q l => l.id = q) hi (fun q _ => hI.id q)
  · exact upd_forall (P := fun _ l => l.WF) hir (fun q _ => hI.wf q)
  · exact upd_forall (P := fun _ l => ∀ i r v d, l = .adoptW i r v d → (k r).2 = some d)
      (by rintro _ _ _ _ ⟨⟩) (fun q _ => hI.adoptW_dec q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .gidR i' r' v' → r' ≤ i' → g r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ => hI.gidR_hi q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .adoptR i' r' v' → g r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ => hI.adoptR_gid q)
  · exact upd_forall (P := fun _ l => ∀ r', r' < l.round → g r' = true)
      (fun r' hr' => hI.round_gid p r' (by rw [h]; exact hr')) (fun q _ => hI.round_gid q)
  · exact upd_forall
      (P := fun _ l => ∀ r', l.id < r' → l.round = r' → 2 ≤ l.phase → a r' ≠ none)
      (fun r' h1 h2 _ => hI.passed p r' (by rw [h]; exact h1) (by rw [h]; exact h2)
        (by rw [h]; simp [Loc.phase]))
      (fun q _ => hI.passed q)
  · intro r'
    rw [hI.count r', nProp_update_eq]
    intro _
    rw [h]; simp only [Proposed, Loc.round, Loc.phase]; omega
  · intro r' hex
    by_cases hold : ∃ q, (L q).Decided r'
    · exact (hI.dec r' hold).frame (by rw [h]; rfl) (fun P => by rw [h]; exact Iff.rfl)
        (by rintro _ _ ⟨⟩)
    · obtain ⟨q, hq⟩ := hex
      have hqp : q = p := by
        by_contra hqp
        exact hold ⟨q, by simpa [update_of_ne hqp] using hq⟩
      subst hqp
      simp only [update_self, Loc.Decided] at hq
      subst hq
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1
        (hI.passed q r (by rw [h]; exact hir) (by rw [h]; rfl) (by rw [h]; simp [Loc.phase]))
      refine ⟨w, hI.adopt_dec r w hw, hw, ?_, ?_, ?_⟩
      · intro q' i' w' hq'
        rcases eq_or_ne q' q with rfl | hqp
        · simp at hq'
        · rw [update_of_ne hqp] at hq'
          exact (hold ⟨q', by rw [hq']; rfl⟩).elim
      · intro q' hq'
        rcases eq_or_ne q' q with rfl | hqp
        · simp [Loc.round] at hq'
        · rw [update_of_ne hqp] at hq'
          have := hI.round_gid q' r hq'
          simp [hg] at this
      · intro r2 hlt w' hw'
        rw [hI.cons_none r r2 hlt hg] at hw'
        simp at hw'
  · exact upd_forall (P := fun q l => l.AllVals (Ok x (σ ++ [p]) q))
      (by have := hI'.valid_loc p; rw [h] at this; exact this) (fun q _ => hI'.valid_loc q)

lemma I.step_retR (hI : I x σ L g k a) (h : L p = .retR i r v) :
    I x (σ ++ [p]) (update L p (.done i r ((a r).getD v))) g k a := by
  have hi : i = p := by simpa [h, Loc.id] using hI.id p
  have hir : i < r := by simpa [h, Loc.WF] using hI.wf p
  have hI' := hI.mono p
  obtain ⟨d, hkd, had, -, -, -⟩ := hI.dec r ⟨p, by rw [h]; rfl⟩
  rw [had, Option.getD_some]
  refine ⟨?_, ?_, ?_, hI.adopt_dec, ?_, ?_, ?_, ?_, hI.cons_none, ?_, ?_, ?_, hI'.valid_cons,
    hI'.gid_writer⟩
  · exact upd_forall (P := fun q l => l.id = q) hi (fun q _ => hI.id q)
  · exact upd_forall (P := fun _ l => l.WF) hir (fun q _ => hI.wf q)
  · exact upd_forall (P := fun _ l => ∀ i r v d, l = .adoptW i r v d → (k r).2 = some d)
      (by rintro _ _ _ _ ⟨⟩) (fun q _ => hI.adoptW_dec q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .gidR i' r' v' → r' ≤ i' → g r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ => hI.gidR_hi q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .adoptR i' r' v' → g r' = true)
      (by rintro _ _ _ ⟨⟩) (fun q _ => hI.adoptR_gid q)
  · exact upd_forall (P := fun _ l => ∀ r', r' < l.round → g r' = true)
      (fun r' hr' => hI.round_gid p r' (by rw [h]; exact hr')) (fun q _ => hI.round_gid q)
  · exact upd_forall
      (P := fun _ l => ∀ r', l.id < r' → l.round = r' → 2 ≤ l.phase → a r' ≠ none)
      (fun r' h1 h2 _ => hI.passed p r' (by rw [h]; exact h1) (by rw [h]; exact h2)
        (by rw [h]; simp [Loc.phase]))
      (fun q _ => hI.passed q)
  · intro r'
    rw [hI.count r', nProp_update_eq]
    intro _
    rw [h]; simp only [Proposed, Loc.round, Loc.phase]; omega
  · intro r' hex
    have hex' := (exists_update_iff (P := fun l => l.Decided r') (by rw [h]; exact Iff.rfl)).1 hex
    obtain ⟨d0, hk, ha, hdn, hv, hk2⟩ := hI.dec r' hex'
    refine ⟨d0, hk, ha, ?_, ?_, hk2⟩
    · intro q i' w hq
      rcases eq_or_ne q p with rfl | hqp
      · simp only [update_self, Loc.done.injEq] at hq
        obtain ⟨-, rfl, rfl⟩ := hq
        rw [hk] at hkd; simpa using hkd.symm
      · exact hdn q i' w (by simpa [update_of_ne hqp] using hq)
    · intro q hq
      rcases eq_or_ne q p with rfl | hqp
      · simp only [update_self, Loc.round] at hq ⊢
        exact hk2 r hq d hkd
      · simp only [update_of_ne hqp] at hq ⊢; exact hv q hq
  · exact upd_forall (P := fun q l => l.AllVals (Ok x (σ ++ [p]) q))
      (Or.inr (hI'.valid_cons r d hkd)) (fun q _ => hI'.valid_loc q)

lemma I.step_adoptR (hI : I x σ L g k a) (h : L p = .adoptR i r v) :
    I x (σ ++ [p]) (update L p (start i (r + 1) ((a r).getD v))) g k a := by
  have hi : i = p := by simpa [h, Loc.id] using hI.id p
  have hg := hI.adoptR_gid p i r v h
  have hI' := hI.mono p
  refine ⟨?_, ?_, ?_, hI.adopt_dec, ?_, ?_, ?_, ?_, hI.cons_none, ?_, ?_, ?_, hI'.valid_cons,
    hI'.gid_writer⟩
  · exact upd_forall (P := fun q l => l.id = q) (by simpa using hi) (fun q _ => hI.id q)
  · exact upd_forall (P := fun _ l => l.WF) (start_wf _ _ _) (fun q _ => hI.wf q)
  · exact upd_forall (P := fun _ l => ∀ i r v d, l = .adoptW i r v d → (k r).2 = some d)
      (fun _ _ _ _ he => (start_ne_adoptW _ _ _ _ _ _ _ he).elim) (fun q _ => hI.adoptW_dec q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .gidR i' r' v' → r' ≤ i' → g r' = true)
      (fun _ _ _ he => (start_ne_gidR _ _ _ _ _ _ he).elim) (fun q _ => hI.gidR_hi q)
  · exact upd_forall (P := fun _ l => ∀ i' r' v', l = .adoptR i' r' v' → g r' = true)
      (fun _ _ _ he => (start_ne_adoptR _ _ _ _ _ _ he).elim) (fun q _ => hI.adoptR_gid q)
  · refine upd_forall (P := fun _ l => ∀ r', r' < l.round → g r' = true) ?_
      (fun q _ => hI.round_gid q)
    intro r' hr'
    simp only [start_round] at hr'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hlt | rfl
    · exact hI.round_gid p r' (by rw [h]; exact hlt)
    · exact hg
  · exact upd_forall
      (P := fun _ l => ∀ r', l.id < r' → l.round = r' → 2 ≤ l.phase → a r' ≠ none)
      (by intro r' _ _ h2; simp at h2) (fun q _ => hI.passed q)
  · intro r'
    rw [hI.count r', nProp_update_eq]
    intro _
    rw [h]; simp only [Proposed, start_round, start_phase]; simp only [Loc.round, Loc.phase]; omega
  · intro r' hex
    have hex' := (exists_update_iff (P := fun l => l.Decided r')
      (by rw [h]; exact ⟨fun h' => (start_not_decided _ _ _ _ h').elim, fun h' => h'.elim⟩)).1 hex
    obtain ⟨d0, hk, ha, hdn, hv, hk2⟩ := hI.dec r' hex'
    refine ⟨d0, hk, ha, ?_, ?_, hk2⟩
    · intro q i' w hq
      rcases eq_or_ne q p with rfl | hqp
      · simp only [update_self] at hq; exact (start_ne_done _ _ _ _ _ _ hq).elim
      · exact hdn q i' w (by simpa [update_of_ne hqp] using hq)
    · intro q hq
      rcases eq_or_ne q p with rfl | hqp
      · simp only [update_self, start_round, start_allVals] at hq ⊢
        rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hlt | rfl
        · rcases har : a r with _ | w
          · have := hv q (by rw [h]; exact hlt); rw [h] at this; simpa [Loc.AllVals] using this
          · simpa using hk2 r hlt w (hI.adopt_dec r w har)
        · simp [ha]
      · simp only [update_of_ne hqp] at hq ⊢; exact hv q hq
  · refine upd_forall (P := fun q l => l.AllVals (Ok x (σ ++ [p]) q)) ?_
      (fun q _ => hI'.valid_loc q)
    simp only [start_allVals]
    rcases har : a r with _ | w
    · have := hI'.valid_loc p; rw [h] at this; simpa [Loc.AllVals] using this
    · simp only [Option.getD_some]
      exact Or.inr (hI'.valid_cons r w (hI.adopt_dec r w har))

end Preservation

/-! ### The invariant holds in every reachable configuration -/

section Reachable

open Function

/-- The invariant of Algorithm 2 on a configuration reached by `σ` from inputs `x`. -/
def Inv (x : ℕ → V) (σ : List ℕ) (C : Conf V junk) : Prop := I x σ C.loc (G C) (K C) (A C)

lemma inv_init (x : ℕ → V) : Inv x [] ((alg2 V junk).initCfg x) := by
  refine ⟨fun p => rfl, fun p => Nat.zero_le p, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ _ => rfl, ?_, ?_,
    fun p => Or.inl rfl, ?_, ?_⟩
  · intro p i r v d h; cases h
  · intro r w h; cases h
  · intro p i r v h; cases h
  · intro p i r v h; cases h
  · intro p r h; exact absurd h (Nat.not_lt_zero r)
  · intro p r _ _ h3; exact absurd h3 (by show ¬ 2 ≤ 0; omega)
  · intro r
    show 0 = ((Finset.range r).filter (fun q => Proposed r (Loc.gidW q 0 (x q)))).card
    symm
    simp [Proposed, Loc.round, Loc.phase]
  · rintro r ⟨p, hp⟩; exact (hp : False).elim
  · intro r w h; cases h
  · intro r h; cases h

lemma Inv.step {x : ℕ → V} {σ : List ℕ} {C : Conf V junk} (hI : Inv x σ C) (p : ℕ) :
    Inv x (σ ++ [p]) (C.step p) := by
  unfold Inv at *
  cases hl : C.loc p with
  | gidW i r v =>
    obtain ⟨h1, h2, h3, h4⟩ := step_gidW hl
    rw [h1, h2, h3, h4]; exact hI.step_gidW hl
  | prop i r v =>
    obtain ⟨h1, h2, h3, h4⟩ := step_prop hl
    rw [h1, h2, h3, h4, ite_eq_left (hI.count_lt hl)]; exact hI.step_prop hl
  | adoptW i r v d =>
    obtain ⟨h1, h2, h3, h4⟩ := step_adoptW hl
    rw [h1, h2, h3, h4]; exact hI.step_adoptW hl
  | gidR i r v =>
    obtain ⟨h1, h2, h3, h4⟩ := step_gidR hl
    rw [h1, h2, h3, h4]
    cases hg : G C r
    · show I x (σ ++ [p]) (update C.loc p (Loc.retR i r v)) (G C) (K C) (A C)
      exact hI.step_gidR_false hl hg
    · show I x (σ ++ [p]) (update C.loc p (Loc.adoptR i r v)) (G C) (K C) (A C)
      exact hI.step_gidR_true hl hg
  | retR i r v =>
    obtain ⟨h1, h2, h3, h4⟩ := step_retR hl
    rw [h1, h2, h3, h4]; exact hI.step_retR hl
  | adoptR i r v =>
    obtain ⟨h1, h2, h3, h4⟩ := step_adoptR hl
    rw [h1, h2, h3, h4]; exact hI.step_adoptR hl
  | done i r w =>
    rw [step_done hl]; exact hI.mono p

/-- The invariant holds after every finite schedule. -/
theorem inv_exec (x : ℕ → V) (σ : List ℕ) : Inv x σ ((alg2 V junk).exec x σ) := by
  induction σ using List.reverseRecOn with
  | nil => exact inv_init x
  | append_singleton σ p ih => rw [Alg.exec_concat]; exact ih.step p

lemma out_iff (C : Conf V junk) (p : ℕ) (v : V) :
    C.Out p v ↔ ∃ i r, C.loc p = .done i r v := by
  unfold Cfg.Out
  cases C.loc p <;> simp [alg2, act]

end Reachable

/-! ### Claim 2 and Lemmas 5–7 -/

section Main

open Function

/-- **Claim 2** (precise form). The number of invocations of `cons[r].propose` is the number of
processes `q < r` that have proposed at round `r`. -/
theorem count_eq (x : ℕ → V) (σ : List ℕ) (r : ℕ) :
    (((alg2 V junk).exec x σ).mem (.cons r)).1 = nProp ((alg2 V junk).exec x σ).loc r :=
  (inv_exec x σ).count r

/-- **Claim 2** of [Perrin–Mostéfaoui–Bonin 2020]. For any round `r`, at most `r` invocations
of `propose` are applied to `cons[r]`. -/
theorem claim2 (x : ℕ → V) (σ : List ℕ) (r : ℕ) :
    (((alg2 V junk).exec x σ).mem (.cons r)).1 ≤ r :=
  (count_eq x σ r).trans_le (nProp_le _ r)

/-- Consequence of Claim 2: a process about to propose on `cons[r]` makes one of its first `r`
invocations, so it receives the decided value and never an unspecified (`junk`) response. -/
theorem count_lt_of_prop (x : ℕ → V) (σ : List ℕ) {p i r : ℕ} {v : V}
    (h : ((alg2 V junk).exec x σ).loc p = .prop i r v) :
    (((alg2 V junk).exec x σ).mem (.cons r)).1 < r :=
  (inv_exec x σ).count_lt h

lemma out_eq_of_le {x : ℕ → V} {σ : List ℕ} {C : Conf V junk} (hI : Inv x σ C) {p q i j r₁ r₂ : ℕ}
    {v w : V} (hp : C.loc p = .done i r₁ v) (hq : C.loc q = .done j r₂ w) (hr : r₁ ≤ r₂) :
    v = w := by
  obtain ⟨d, -, -, hdn, hv, -⟩ := hI.dec r₁ ⟨p, by rw [hp]; rfl⟩
  rw [hdn p i v hp]
  rcases hr.lt_or_eq with hlt | rfl
  · have := hv q (by rw [hq]; exact hlt); rw [hq] at this; exact this.symm
  · exact (hdn q j w hq).symm

/-- **Lemma 6** (Agreement) of [Perrin–Mostéfaoui–Bonin 2020]: all processes that decide, decide
the same value. -/
theorem agreement : Agreement (alg2 V junk) anySched := by
  intro x σ _ p _ q _ v w hv hw
  obtain ⟨i, r₁, hp⟩ := (out_iff _ p v).1 hv
  obtain ⟨j, r₂, hq⟩ := (out_iff _ q w).1 hw
  rcases le_total r₁ r₂ with hr | hr
  · exact out_eq_of_le (inv_exec x σ) hp hq hr
  · exact (out_eq_of_le (inv_exec x σ) hq hp hr).symm

/-- **Lemma 7** (Validity) of [Perrin–Mostéfaoui–Bonin 2020]: a decided value was proposed by a
process (that took a step). -/
theorem validity : Validity (alg2 V junk) anySched := by
  intro x σ _ p hp v hv
  obtain ⟨i, r, h⟩ := (out_iff _ p v).1 hv
  have := (inv_exec (junk := junk) x σ).valid_loc p
  rw [h] at this
  rcases (this : Ok x σ p v) with e | e
  · exact ⟨p, hp, e.symm⟩
  · exact e

/-- `greaterId[r]` is only written by processes with id `≥ r`: if all processes of `σ` have ids
`≤ N`, then `greaterId[N + 1]` is never set. -/
lemma gid_false_of_bound {x : ℕ → V} {σ : List ℕ} {N : ℕ} (hσ : ∀ q ∈ σ, q ≤ N) :
    G ((alg2 V junk).exec x σ) (N + 1) = false := by
  by_contra h
  obtain ⟨q, hq, hle⟩ := (inv_exec (junk := junk) x σ).gid_writer (N + 1) (by simpa using h)
  have := hσ q hq
  omega

/-- Termination bound: if all ids are `≤ N`, no process ever goes beyond round `N + 1` (where it
is smaller than the round number and nobody announces itself in `greaterId[N + 1]`). -/
theorem round_le_of_bound {x : ℕ → V} {σ : List ℕ} {N : ℕ} (hσ : ∀ q ∈ σ, q ≤ N) (p : ℕ) :
    (((alg2 V junk).exec x σ).loc p).round ≤ N + 1 := by
  by_contra h
  have := (inv_exec (junk := junk) x σ).round_gid p (N + 1) (by omega)
  rw [gid_false_of_bound hσ] at this
  exact Bool.false_ne_true this

lemma update_loc_self (C : Conf V junk) (p : ℕ) (l : Loc V) : update C.loc p l p = l :=
  update_self _ _ _

/-- Progress measure of a local state. -/
def μ (l : Loc V) : ℕ := 5 * l.round + l.phase

lemma μ_le (l : Loc V) : μ l ≤ 5 * l.round + 4 := by
  unfold μ; cases l <;> simp [Loc.phase]

/-- Each step of a process that has not returned increases its progress measure. -/
lemma μ_step (C : Conf V junk) (p : ℕ) (h : ∀ v, ¬ C.Out p v) :
    μ (C.loc p) + 1 ≤ μ ((C.step p).loc p) := by
  cases hl : C.loc p with
  | gidW i r v => rw [(step_gidW hl).1, update_loc_self]; simp [μ, Loc.round, Loc.phase]
  | prop i r v => rw [(step_prop hl).1, update_loc_self]; simp [μ, Loc.round, Loc.phase]
  | adoptW i r v d => rw [(step_adoptW hl).1, update_loc_self]; simp [μ, Loc.round, Loc.phase]
  | gidR i r v =>
    rw [(step_gidR hl).1]
    cases G C r
    · show μ (Loc.gidR i r v) + 1 ≤ μ (update C.loc p (Loc.retR i r v) p)
      rw [update_loc_self]; simp [μ, Loc.round, Loc.phase]
    · show μ (Loc.gidR i r v) + 1 ≤ μ (update C.loc p (Loc.adoptR i r v) p)
      rw [update_loc_self]; simp [μ, Loc.round, Loc.phase]
  | retR i r v => rw [(step_retR hl).1, update_loc_self]; simp [μ, Loc.round, Loc.phase]
  | adoptR i r v =>
    rw [(step_adoptR hl).1, update_loc_self]
    simp only [μ, start_round, start_phase]
    simp only [Loc.round, Loc.phase]
    omega
  | done i r w => exact absurd ((out_iff C p w).2 ⟨i, r, hl⟩) (h w)

/-- **Lemma 5** (Wait-freedom) of [Perrin–Mostéfaoui–Bonin 2020]: in the finite arrival model
`M₂`, every process that takes infinitely many steps decides. -/
theorem waitFree : WaitFree (alg2 V junk) finArrival := by
  intro x s hs p hp
  have hs' : (Set.range s).Finite := hs
  set N := hs'.toFinset.sup id
  have hbound : ∀ t, ∀ q ∈ pre s t, q ≤ N := by
    intro t q hq
    obtain ⟨u, -, rfl⟩ := mem_pre.1 hq
    exact Finset.le_sup (f := id) (hs'.mem_toFinset.2 ⟨u, rfl⟩)
  -- number of steps of `p` among the first `t`
  let c : ℕ → ℕ := fun t => (pre s t).count p
  have hc : ∀ t, c (t + 1) = c t + if s t = p then 1 else 0 := by
    intro t
    simp only [c, pre_succ, List.count_append, List.count_singleton]
    split <;> simp_all
  have hkey : ∀ t, (∃ v, ((alg2 V junk).exec x (pre s t)).Out p v) ∨
      c t ≤ μ (((alg2 V junk).exec x (pre s t)).loc p) := by
    intro t
    induction t with
    | zero => right; simp [c]
    | succ t ih =>
      rw [pre_succ, Alg.exec_concat, hc]
      by_cases hst : s t = p
      · rw [ite_eq_left hst, hst]
        by_cases hout : ∃ v, ((alg2 V junk).exec x (pre s t)).Out p v
        · obtain ⟨v, hv⟩ := hout; exact Or.inl ⟨v, hv.step p⟩
        · right
          have := μ_step _ p (fun v hv => hout ⟨v, hv⟩)
          rcases ih with ih | ih
          · exact absurd ih hout
          · omega
      · rw [ite_eq_right hst, Nat.add_zero]
        rcases ih with ⟨v, hv⟩ | ih
        · exact Or.inl ⟨v, hv.step _⟩
        · right; rwa [Cfg.step_loc_other _ (Ne.symm hst)]
  have hunb : ∀ B, ∃ t, B ≤ c t := by
    intro B
    induction B with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ B ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨u, hu, hsu⟩ := hp t
      refine ⟨u + 1, ?_⟩
      have hmono : c t ≤ c u := ((pre_prefix s hu).sublist).count_le p
      rw [hc, ite_eq_left hsu]
      omega
  obtain ⟨t, ht⟩ := hunb (5 * (N + 1) + 5)
  rcases hkey t with ⟨v, hv⟩ | h
  · exact ⟨t, v, hv⟩
  · have h1 := μ_le (((alg2 V junk).exec x (pre s t)).loc p)
    have h2 := round_le_of_bound (x := x) (junk := junk) (hbound t) p
    omega

/-- **Algorithm 2** solves consensus in `MA₂[consₙ⟨V⟩]` (Lemmas 5, 6, 7 of
[Perrin–Mostéfaoui–Bonin 2020]): agreement and validity in every finite execution (with any number
of participating processes), wait-freedom in the finite arrival model — whatever the unspecified
responses `junk` of the `consₙ` objects beyond their first `n` invocations are. -/
theorem alg2_solvesCons (V : Type) (junk : ℕ → ℕ → V → V) :
    SolvesCons (alg2 V junk) anySched finArrival :=
  ⟨agreement, validity, waitFree⟩

end Main

/-! ### Non-vacuity: a solo run of `p₀` decides its input at round `1` -/

/-- Running alone, `p₀` marks `greaterId[0]`, moves to round `1`, proposes on `cons[1]`, writes
`adopt[1]`, reads `greaterId[1] = false` and returns its input after `7` steps. -/
example (junk : ℕ → ℕ → V → V) (x : ℕ → V) :
    ((alg2 V junk).exec x (List.replicate 7 0)).Out 0 (x 0) := by
  rfl

end Podc.InfiniteArrivalHierarchy.Alg2
