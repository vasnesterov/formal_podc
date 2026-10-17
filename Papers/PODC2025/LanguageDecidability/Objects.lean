import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.DetSpec
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Complete
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.SeqLin
import Papers.PODC2025.LanguageDecidability.Characterization

/-!
# Registers and ledgers: languages that are not real-time oblivious

Castañeda, Rodríguez, *Asynchronous Fault-Tolerant Language Decidability for Runtime
Verification of Distributed Systems*, PODC 2025 (arXiv 2502.00191v3): Examples 1, 2, 4,
Definitions 2.3–2.6 and 2.9, Lemma 5.1, Corollaries 5.1–5.3 and Appendix A.

## Model

The alphabet of an object with operations `Op` and responses `Res` gives every process the
invocation alphabet `Op` and the response alphabet `Res` (`OSym`). A finite word is translated
symbol by symbol (`histOf`) into a CSLib Herlihy–Wing history on a single object (`X = Unit`).
The sequential objects are deterministic state machines (`detSpec`):

* register (Example 1): `write v : ack`, `read : val v`, initial value `0`;
* ledger (Example 2): `append r : ack`, `get : val l` (the list of appended records), initially
  empty; records are natural numbers.

Correctness conditions of a finite history `H`:

* `Linearizable` (CSLib; Herlihy–Wing, amended definition of Sela–Herlihy–Petrank);
* `SeqConsistent`: as in the text of Example 1 — responses are appended to some pending
  operations (`IsExtension`), the other pending operations are removed (`complete`), and the
  resulting operations are ordered in a legal sequential history respecting process order
  (`Equiv`); i.e. `Linearizable` without the real-time clause;
* `PermConsistent`: property (1) of Example 4 taken literally — responses are appended to `H`
  so that *all* operations complete, and *some permutation* of the operations (no process-order
  constraint) is a legal sequential history.

Languages (every finite prefix satisfies the condition): `LIN_REG`, `SC_REG` (Definitions 2.4,
2.3), `LIN_LED`, `SC_LED` (Definitions 2.6, 2.5) and `EC_LED` (Definition 2.9: property (1) as
`PermConsistent` plus property (2), eventual visibility of the appends of the prefix).

## Results

For every `n ≥ 2`:

* `not_rto_LIN_REG`, `not_rto_SC_REG`; `lemma_5_1` (`∉ WD`), `cor_5_1` (`∉ SD`);
* `not_rto_LIN_LED`, `not_rto_SC_LED`, `not_rto_EC_LED`; `cor_5_2` (`∉ SD`), `cor_5_3`
  (`∉ WD`) — all via Theorem 5.2 (`rto_of_SD`, `rto_of_WD`).

The register word is: in round `r = 1, 2, …`, `p₀` executes `write(r) : ack`, then
`p₁, …, p_{n-1}` execute `read : r`. The ledger word is the one of Appendix A: in each round
`p₀, …, p_{n-1}` append `1, …, n` and then `p_{n-1}` executes `get`, returning the list of all
appends so far. Both are sequential runs of the object (`runRec`), hence in every language.
Moving the first operation (`p₀`'s first operation) behind the rest of the first round gives a
word with a prefix whose responses cannot be explained by any sequential run (`Explained`).
-/

namespace Podc2025.LanguageDecidability.Objects

open Cslib.SharedMemory.HerlihyWing

variable {n : ℕ} {Op Res State : Type}

/-! ## Words over the alphabet of a sequential object -/

/-- Symbols for an object with operations `Op` and responses `Res`: every process has the
invocation alphabet `Op` and the response alphabet `Res`. -/
abbrev OSym (n : ℕ) (Op Res : Type) := Sym (n := n) (fun _ => Op) (fun _ => Res)

/-- ω-words for an object with operations `Op` and responses `Res`. -/
abbrev OWord (n : ℕ) (Op Res : Type) := Word (n := n) (fun _ => Op) (fun _ => Res)

/-- A symbol as a Herlihy–Wing event on the single object `()`. -/
def evOf : OSym n Op Res → Event (Fin n) Unit Op Res
  | ⟨p, .inl o⟩ => .inv p () o
  | ⟨p, .inr r⟩ => .res p () r

/-- A finite word as a Herlihy–Wing history on the single object `()`. -/
def histOf (l : List (OSym n Op Res)) : History (Fin n) Unit Op Res := l.map evOf

@[simp] lemma evOf_inl (p : Fin n) (o : Op) :
    evOf (⟨p, .inl o⟩ : OSym n Op Res) = .inv p () o := rfl

@[simp] lemma evOf_inr (p : Fin n) (r : Res) :
    evOf (⟨p, .inr r⟩ : OSym n Op Res) = .res p () r := rfl

/-! ## Correctness conditions and languages -/

/-- Sequential consistency (Lamport), as described in Example 1: responses are appended to
some pending operations of `H` (`H'` is an extension of `H`), the remaining pending operations
are removed (`complete H'`), and the resulting operations can be ordered in a legal sequential
history `S` that respects process order (`complete H'` and `S` have the same process
subhistories). This is CSLib's `Linearizable` without the real-time clause. -/
def SeqConsistent (spec : SeqSpec (Fin n) Unit Op Res) (H : History (Fin n) Unit Op Res) :
    Prop :=
  WellFormed H ∧ ∃ H', IsExtension H H' ∧ ∃ S, Legal spec S ∧
    Cslib.SharedMemory.HerlihyWing.Equiv (complete H') S

/-- Property (1) of the eventually consistent ledger (Example 4), taken literally: responses can
be appended to `H` to make all operations complete (`H'` extends `H` and every process
subhistory of `H'` is a complete sequential history `seqHist Mp`) so that some permutation `M`
of the operations of `H'` is a legal sequential history. *No process-order constraint* is
imposed: for every process `p`, the operations of `p` in `M` are those of `p` in `H'` in any
order. -/
def PermConsistent (spec : SeqSpec (Fin n) Unit Op Res) (H : History (Fin n) Unit Op Res) :
    Prop :=
  ∃ H', IsExtension H H' ∧ ∃ M : List (OpRec (Fin n) Unit Op Res), Legal spec (seqHist M) ∧
    ∀ p, ∃ Mp, restrictP H' p = seqHist Mp ∧ (M.filter (·.p = p)).Perm Mp

/-- The well-formed ω-words every finite prefix of which is linearizable. -/
def LinLang (spec : SeqSpec (Fin n) Unit Op Res) : Set (OWord n Op Res) :=
  {x | WF x ∧ ∀ k, Linearizable spec (histOf (pfx x k))}

/-- The well-formed ω-words every finite prefix of which is sequentially consistent. -/
def SCLang (spec : SeqSpec (Fin n) Unit Op Res) : Set (OWord n Op Res) :=
  {x | WF x ∧ ∀ k, SeqConsistent spec (histOf (pfx x k))}

theorem seqConsistent_of_linearizable {spec : SeqSpec (Fin n) Unit Op Res}
    {H : History (Fin n) Unit Op Res} (h : Linearizable spec H) : SeqConsistent spec H := by
  obtain ⟨hw, H', hH', S, hS, he, -⟩ := h
  exact ⟨hw, H', hH', S, hS, he⟩

theorem linLang_subset (spec : SeqSpec (Fin n) Unit Op Res) : LinLang spec ⊆ SCLang spec :=
  fun _ hx => ⟨hx.1, fun k => seqConsistent_of_linearizable (hx.2 k)⟩

/-! ## Histories explained by a sequential run -/

/-- A necessary condition for all three correctness conditions: some legal sequential run `M`
of the deterministic object uses only operations invoked in `H` and produces every response
of `H` (for the same process). -/
def Explained (init : State) (δ : State → Op → State × Res) (H : History (Fin n) Unit Op Res) :
    Prop :=
  ∃ M : List (OpRec (Fin n) Unit Op Res), runOK δ init M ∧
    (∀ e ∈ M, Event.inv e.p () e.o ∈ H) ∧
    ∀ p r, Event.res p () r ∈ H → ∃ e ∈ M, e.p = p ∧ e.r = r

lemma mem_completeAux_of_isRes {e : Event (Fin n) Unit Op Res} (he : e.isRes = true) :
    ∀ (β γ : History (Fin n) Unit Op Res), e ∈ β → e ∈ completeAux β γ
  | [], _, h => by simp at h
  | f :: β, γ, h => by
    rw [completeAux_cons]
    rcases List.mem_cons.1 h with rfl | h
    · simp [keep, he]
    · have := mem_completeAux_of_isRes he β γ h
      split_ifs
      · exact List.mem_cons_of_mem _ this
      · exact this

lemma legal_seqHist_detSpec {init : State} {δ : State → Op → State × Res}
    {M : List (OpRec (Fin n) Unit Op Res)} :
    Legal (fun _ => detSpec init δ) (seqHist M) ↔ runOK δ init M :=
  (legal_seqHist_iff_of_subsingleton ()).trans seqHist_mem_detSpec

lemma legal_detSpec {init : State} {δ : State → Op → State × Res}
    {S : History (Fin n) Unit Op Res} (h : Legal (fun _ => detSpec init δ) S) :
    ∃ M, S = seqHist M ∧ runOK δ init M := by
  have := h.2 (); rw [restrictX_of_subsingleton] at this; exact this

lemma mem_seqHist_inv {M : List (OpRec (Fin n) Unit Op Res)} {e : OpRec (Fin n) Unit Op Res}
    (he : e ∈ M) : Event.inv e.p () e.o ∈ seqHist M :=
  List.mem_flatMap.2 ⟨e, he, by simp [OpRec.events]⟩

lemma mem_seqHist_res {M : List (OpRec (Fin n) Unit Op Res)} {p : Fin n} {r : Res}
    (h : Event.res p () r ∈ seqHist M) : ∃ e ∈ M, e.p = p ∧ e.r = r := by
  obtain ⟨e, he, h⟩ := List.mem_flatMap.1 h
  simp only [OpRec.events, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
    false_or] at h
  cases h
  exact ⟨e, he, rfl, rfl⟩

theorem explained_of_seqConsistent {init : State} {δ : State → Op → State × Res}
    {H : History (Fin n) Unit Op Res} (h : SeqConsistent (fun _ => detSpec init δ) H) :
    Explained init δ H := by
  obtain ⟨-, H', ⟨R, rfl, hR, -⟩, S, hS, heq⟩ := h
  obtain ⟨M, rfl, hM⟩ := legal_detSpec hS
  refine ⟨M, hM, fun e he => ?_, fun p r hr => ?_⟩
  · have h1 : Event.inv e.p () e.o ∈ restrictP (seqHist M) e.p :=
      List.mem_filter.2 ⟨mem_seqHist_inv he, by simp⟩
    rw [← heq e.p] at h1
    have h2 := (completeAux_sublist (H ++ R) []).subset (List.mem_filter.1 h1).1
    rcases List.mem_append.1 h2 with h3 | h3
    · exact h3
    · simpa using hR _ h3
  · have h1 : Event.res p () r ∈ restrictP (complete (H ++ R)) p :=
      List.mem_filter.2 ⟨mem_completeAux_of_isRes rfl _ _ (List.mem_append_left _ hr), by simp⟩
    rw [heq p] at h1
    exact mem_seqHist_res (List.mem_filter.1 h1).1

theorem explained_of_permConsistent {init : State} {δ : State → Op → State × Res}
    {H : History (Fin n) Unit Op Res} (h : PermConsistent (fun _ => detSpec init δ) H) :
    Explained init δ H := by
  obtain ⟨H', ⟨R, rfl, hR, -⟩, M, hM, hp⟩ := h
  refine ⟨M, legal_seqHist_detSpec.1 hM, fun e he => ?_, fun p r hr => ?_⟩
  · obtain ⟨Mp, h1, h2⟩ := hp e.p
    have : e ∈ Mp := h2.subset (List.mem_filter.2 ⟨he, by simp⟩)
    have h3 : Event.inv e.p () e.o ∈ restrictP (H ++ R) e.p := h1 ▸ mem_seqHist_inv this
    rcases List.mem_append.1 (List.mem_filter.1 h3).1 with h4 | h4
    · exact h4
    · simpa using hR _ h4
  · obtain ⟨Mp, h1, h2⟩ := hp p
    have h3 : Event.res p () r ∈ restrictP (H ++ R) p :=
      List.mem_filter.2 ⟨List.mem_append_left _ hr, by simp⟩
    rw [h1] at h3
    obtain ⟨e, he, rfl, rfl⟩ := mem_seqHist_res h3
    exact ⟨e, (List.mem_filter.1 (h2.symm.subset he)).1, rfl, rfl⟩

/-! ## Sequential words -/

/-- The ω-word of the infinite sequential history `f 0, f 1, …`: the invocation of `f i` at
position `2i` and its response at position `2i + 1`. -/
def seqWord (f : ℕ → OpRec (Fin n) Unit Op Res) : OWord n Op Res := fun m =>
  if m % 2 = 0 then ⟨(f (m / 2)).p, .inl (f (m / 2)).o⟩ else ⟨(f (m / 2)).p, .inr (f (m / 2)).r⟩

/-- The first `i` operations. -/
def recs (f : ℕ → OpRec (Fin n) Unit Op Res) (i : ℕ) : List (OpRec (Fin n) Unit Op Res) :=
  (List.range i).map f

variable (f : ℕ → OpRec (Fin n) Unit Op Res)

lemma seqWord_even (i : ℕ) : seqWord f (2 * i) = ⟨(f i).p, .inl (f i).o⟩ := by
  simp [seqWord]

lemma seqWord_odd (i : ℕ) : seqWord f (2 * i + 1) = ⟨(f i).p, .inr (f i).r⟩ := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [seqWord, h1, h2]

lemma seqWord_fst (m : ℕ) : (seqWord f m).1 = (f (m / 2)).p := by
  unfold seqWord; split_ifs <;> rfl

lemma evOf_seqWord (m : ℕ) : evOf (seqWord f m) =
    if m % 2 = 0 then .inv (f (m / 2)).p () (f (m / 2)).o
    else .res (f (m / 2)).p () (f (m / 2)).r := by
  unfold seqWord; split_ifs <;> rfl

lemma recs_succ (i : ℕ) : recs f (i + 1) = recs f i ++ [f i] := by
  simp [recs, List.range_succ]

lemma pfx_succ {I O : Fin n → Type} (x : Word I O) (k : ℕ) : pfx x (k + 1) = pfx x k ++ [x k] := by
  simp [pfx, List.range_succ]

lemma histOf_pfx_seqWord (i : ℕ) :
    histOf (pfx (seqWord f) (2 * i)) = seqHist (recs f i) ∧
    histOf (pfx (seqWord f) (2 * i + 1)) =
      seqHist (recs f i) ++ [.inv (f i).p (f i).x (f i).o] := by
  induction i with
  | zero => simp [histOf, pfx, recs, seqHist, seqWord]
  | succ i ih =>
    have e1 : histOf (pfx (seqWord f) (2 * (i + 1))) = seqHist (recs f (i + 1)) := by
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, pfx_succ, histOf, List.map_append, ← histOf,
        ih.2, recs_succ, seqHist_append, seqWord_odd, seqHist_singleton]
      simp
    refine ⟨e1, ?_⟩
    rw [pfx_succ, histOf, List.map_append, ← histOf, e1, seqWord_even]
    simp

lemma isExtension_pfx_seqWord (k : ℕ) :
    IsExtension (histOf (pfx (seqWord f) k)) (seqHist (recs f ((k + 1) / 2))) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have : (2 * i + 1) / 2 = i := by omega
    rw [this, (histOf_pfx_seqWord f i).1]
    exact ⟨[], by simp, by simp, wellFormed_seqHist _⟩
  · have : (2 * i + 1 + 1) / 2 = i + 1 := by omega
    rw [this, (histOf_pfx_seqWord f i).2, recs_succ, seqHist_append, seqHist_singleton]
    refine ⟨[.res (f i).p (f i).x (f i).r], by simp, by simp, ?_⟩
    rw [← seqHist_singleton, ← seqHist_append]
    exact wellFormed_seqHist _

theorem wf_seqWord (hf : ∀ p N, ∃ i, N ≤ i ∧ (f i).p = p) : WF (seqWord f) := by
  have hev : ∀ p i, Even (LanguageDecidability.cnt (seqWord f) p (2 * i)) := by
    intro p i
    induction i with
    | zero => simp [LanguageDecidability.cnt]
    | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, cnt_succ, cnt_succ, seqWord_even, seqWord_odd]
      by_cases h : (f i).p = p
      · simp only [h, ite_true]; rw [add_assoc]; exact ih.add (by decide)
      · simp only [h, ite_false, add_zero]; exact ih
  refine ⟨fun p N => ?_, fun m => ?_⟩
  · obtain ⟨i, hi, hp⟩ := hf p N
    exact ⟨2 * i, by omega, by rw [seqWord_even]; exact hp⟩
  · obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [seqWord_even]; simpa using hev (f i).p i
    · rw [seqWord_odd, cnt_succ, seqWord_even]; simp [Nat.even_add_one, hev]

/-! ## Sequential runs of a deterministic object -/

/-- The state of the object after the first `i` operations of `ops`. -/
def runSt (init : State) (δ : State → Op → State × Res) (ops : ℕ → Op) : ℕ → State
  | 0 => init
  | i + 1 => (δ (runSt init δ ops i) (ops i)).1

/-- The `i`-th operation of the sequential run in which process `sched i` executes `ops i`. -/
def runRec (sched : ℕ → Fin n) (init : State) (δ : State → Op → State × Res) (ops : ℕ → Op)
    (i : ℕ) : OpRec (Fin n) Unit Op Res :=
  ⟨sched i, (), ops i, (δ (runSt init δ ops i) (ops i)).2⟩

lemma runOK_recs_runRec (sched : ℕ → Fin n) (init : State) (δ : State → Op → State × Res)
    (ops : ℕ → Op) (i : ℕ) :
    runOK δ init (recs (runRec sched init δ ops) i) ∧
      runState δ init (recs (runRec sched init δ ops) i) = runSt init δ ops i := by
  induction i with
  | zero => simp [recs, runState, runSt]
  | succ i ih =>
    have hs : ∀ (L : List (OpRec (Fin n) Unit Op Res)) e,
        runState δ init (L ++ [e]) = (δ (runState δ init L) e.o).1 := by
      intro L e; simp [runState]
    rw [recs_succ, runOK_append, hs, ih.2]
    exact ⟨⟨ih.1, by simp [runRec]⟩, rfl⟩

/-- A sequential run with a fair schedule belongs to the linearizability language. -/
theorem runWord_mem_linLang {sched : ℕ → Fin n} (hs : ∀ p N, ∃ i, N ≤ i ∧ sched i = p)
    (init : State) (δ : State → Op → State × Res) (ops : ℕ → Op) :
    seqWord (runRec sched init δ ops) ∈ LinLang (fun _ => detSpec init δ) :=
  ⟨wf_seqWord _ hs, fun k => Linearizable.of_isExtension (isExtension_pfx_seqWord _ k)
    (legal_seqHist_detSpec.2 (runOK_recs_runRec sched init δ ops _).1)⟩

/-! ## Refuting real-time obliviousness -/

/-- If `x ∈ L`, the first operation of `x` (positions `0, 1`) is by a process that does not
occur in the next `l` symbols, and every finite prefix of every word of `L` satisfies `Q` but
the history of these `l` symbols does not, then `L` is not real-time oblivious: the shuffle that
moves the first operation behind the `l` symbols leads out of `L`. -/
theorem not_rto_of {L : Set (OWord n Op Res)} {Q : History (Fin n) Unit Op Res → Prop}
    (hL : ∀ x ∈ L, ∀ k, Q (histOf (pfx x k))) {x : OWord n Op Res} (hx : x ∈ L) {l : ℕ}
    (hq : (x 1).1 = (x 0).1) (hb : ∀ m < l, (x (2 + m)).1 ≠ (x 0).1)
    (hbad : ¬ Q (histOf ((List.range l).map fun m => x (2 + m)))) : ¬ RTO L := by
  intro hR
  obtain ⟨b, hbdef⟩ : ∃ b, b = (List.range l).map fun m => x (2 + m) := ⟨_, rfl⟩
  rw [← hbdef] at hbad
  have hab : pfx x (2 + l) = [x 0, x 1] ++ b := by
    simp [pfx, hbdef, List.range_add, List.range_succ]
  have hproj : ∀ p, proj p (b ++ [x 0, x 1]) = proj p (pfx x (2 + l)) := by
    intro p
    rw [hab, proj_append, proj_append]
    by_cases hp : (x 0).1 = p
    · have : proj p b = [] := by
        simp only [proj, List.filter_eq_nil_iff, hbdef, List.mem_map, List.mem_range]
        rintro _ ⟨m, hm, rfl⟩; simpa [← hp] using hb m hm
      rw [this]; simp
    · have : proj p [x 0, x 1] = [] := by simp [proj, hq, hp]
      rw [this]; simp
  have h := hL _ (hR x hx (2 + l) (b ++ [x 0, x 1]) hproj) l
  have hlen : b.length = l := by simp [hbdef]
  have hpf : pfx (app (b ++ [x 0, x 1]) (shift x (2 + l))) l = b := by
    apply List.ext_getElem (by simp [hlen])
    intro m h1 h2
    simp only [pfx, List.getElem_map, List.getElem_range]
    rw [app_lt (by simp at h1 ⊢; omega)]
    simp [List.getElem_append_left h2]
  rw [hpf] at h
  exact hbad h

/-! ## The register (Example 1, Definitions 2.3, 2.4, Lemma 5.1, Corollary 5.1) -/

/-- Register invocations: `write(v)` and `read()`. -/
inductive RegOp | write (v : ℕ) | read
  deriving DecidableEq

/-- Register responses: `ack` (to a write) and `val v` (a read returning `v`). -/
inductive RegRes | ack | val (v : ℕ)
  deriving DecidableEq

/-- The sequential register (state: its current value). -/
def regδ : ℕ → RegOp → ℕ × RegRes
  | _, .write v => (v, .ack)
  | s, .read => (s, .val s)

/-- Sequential specification of the register, initial value `0`. -/
def regSpec (n : ℕ) : SeqSpec (Fin n) Unit RegOp RegRes := fun _ => detSpec 0 regδ

/-- **Definition 2.4** (linearizable register). -/
def LIN_REG (n : ℕ) : Set (OWord n RegOp RegRes) := LinLang (regSpec n)

/-- **Definition 2.3** (sequentially consistent register). -/
def SC_REG (n : ℕ) : Set (OWord n RegOp RegRes) := SCLang (regSpec n)

/-- Round-robin schedule `p₀, p₁, …, p_{n-1}, p₀, …`. -/
def regSched (hn : 2 ≤ n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ (by omega)⟩

/-- In round `r` (0-based), `p₀` writes `r + 1` and the other processes read. -/
def regOps (n i : ℕ) : RegOp := if i % n = 0 then .write (i / n + 1) else .read

/-- The word of Lemma 5.1: in round `r = 1, 2, …`, `p₀` executes `write(r) : ack`, then
`p₁, …, p_{n-1}` execute `read : r`. -/
def regWord (hn : 2 ≤ n) : OWord n RegOp RegRes := seqWord (runRec (regSched hn) 0 regδ (regOps n))

lemma regSched_fair (hn : 2 ≤ n) : ∀ p N, ∃ i, N ≤ i ∧ regSched hn i = p := by
  intro p N
  refine ⟨n * N + p, ?_, Fin.ext ?_⟩
  · have : N ≤ n * N := Nat.le_mul_of_pos_left N (by omega)
    omega
  · simp [regSched, Nat.mod_eq_of_lt p.2]

theorem regWord_mem_LIN (hn : 2 ≤ n) : regWord hn ∈ LIN_REG n :=
  runWord_mem_linLang (regSched_fair hn) 0 regδ (regOps n)

theorem regWord_mem_SC (hn : 2 ≤ n) : regWord hn ∈ SC_REG n :=
  linLang_subset _ (regWord_mem_LIN hn)

lemma reg_reads : ∀ M : List (OpRec (Fin n) Unit RegOp RegRes), runOK regδ 0 M →
    (∀ e ∈ M, e.o = .read) → ∀ e ∈ M, e.r = .val 0
  | [], _, _, e, he => by simp at he
  | e :: M, hM, hr, e', he' => by
    have h1 := hr e List.mem_cons_self
    rw [runOK_cons, h1] at hM
    rcases List.mem_cons.1 he' with rfl | he'
    · exact hM.1.symm
    · exact reg_reads M hM.2 (fun e h => hr e (List.mem_cons_of_mem _ h)) e' he'

/-- The history `read : 1` (by `p₁`) alone is not explained by any run of the register. -/
lemma not_explained_read_one (hn : 2 ≤ n) :
    ¬ Explained (n := n) 0 regδ [.inv ⟨1, by omega⟩ () .read, .res ⟨1, by omega⟩ () (.val 1)] := by
  rintro ⟨M, hM, ha, hb⟩
  obtain ⟨e, he, -, her⟩ := hb ⟨1, by omega⟩ (.val 1) (by simp)
  have := reg_reads M hM (fun e he => by have := ha e he; simp at this; exact this.2) e he
  rw [her] at this
  cases this

/-- The first four symbols of the register word: `write(1) : ack` by `p₀`, `read : 1` by
`p₁`. -/
lemma regWord_symbols (hn : 2 ≤ n) :
    (regWord hn 0).1 = ⟨0, by omega⟩ ∧ (regWord hn 1).1 = ⟨0, by omega⟩ ∧
    regWord hn 2 = ⟨⟨1, by omega⟩, .inl .read⟩ ∧ regWord hn 3 = ⟨⟨1, by omega⟩, .inr (.val 1)⟩ := by
  have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have e1 := seqWord_even (runRec (regSched hn) 0 regδ (regOps n)) 1
  have e2 := seqWord_odd (runRec (regSched hn) 0 regδ (regOps n)) 1
  simp only [Nat.mul_one, Nat.reduceAdd] at e1 e2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [regWord, seqWord_fst, runRec, regSched]
  · simp [regWord, seqWord_fst, runRec, regSched]
  · rw [regWord, e1]
    have : regSched hn 1 = ⟨1, by omega⟩ := Fin.ext h1
    simp [runRec, this, regOps, h1]
  · rw [regWord, e2]
    have : regSched hn 1 = ⟨1, by omega⟩ := Fin.ext h1
    simp [runRec, this, regOps, h1, runSt, regδ]

lemma regWord_not_rto {L : Set (OWord n RegOp RegRes)} (hn : 2 ≤ n) (hx : regWord hn ∈ L)
    (hL : ∀ x ∈ L, ∀ k, Explained 0 regδ (histOf (pfx x k))) : ¬ RTO L := by
  obtain ⟨h0, h1, h2, h3⟩ := regWord_symbols hn
  refine not_rto_of hL hx (l := 2) (by rw [h0, h1]) ?_ ?_
  · intro m hm
    interval_cases m
    · rw [h2, h0]; simp
    · rw [h3, h0]; simp
  · have : (List.range 2).map (fun m => regWord hn (2 + m)) = [regWord hn 2, regWord hn 3] := by
      simp [List.range_succ]
    rw [this, h2, h3]
    exact not_explained_read_one hn

/-- **Lemma 5.1, real-time part**: `LIN_REG` is not real-time oblivious (`n ≥ 2`). -/
theorem not_rto_LIN_REG (hn : 2 ≤ n) : ¬ RTO (LIN_REG n) :=
  regWord_not_rto hn (regWord_mem_LIN hn)
    fun _ hx k => explained_of_seqConsistent (seqConsistent_of_linearizable (hx.2 k))

/-- **Lemma 5.1, real-time part**: `SC_REG` is not real-time oblivious (`n ≥ 2`). -/
theorem not_rto_SC_REG (hn : 2 ≤ n) : ¬ RTO (SC_REG n) :=
  regWord_not_rto hn (regWord_mem_SC hn) fun _ hx k => explained_of_seqConsistent (hx.2 k)

/-- **Lemma 5.1**: `LIN_REG, SC_REG ∉ WD` (`n ≥ 2`). -/
theorem lemma_5_1 (hn : 2 ≤ n) : ¬ WD (LIN_REG n) ∧ ¬ WD (SC_REG n) :=
  ⟨fun h => not_rto_LIN_REG hn (rto_of_WD (fun _ hx => hx.1) h),
    fun h => not_rto_SC_REG hn (rto_of_WD (fun _ hx => hx.1) h)⟩

/-- **Corollary 5.1**: `LIN_REG, SC_REG ∉ SD` (`n ≥ 2`). -/
theorem cor_5_1 (hn : 2 ≤ n) : ¬ SD (LIN_REG n) ∧ ¬ SD (SC_REG n) :=
  ⟨fun h => not_rto_LIN_REG hn (rto_of_SD (fun _ hx => hx.1) h),
    fun h => not_rto_SC_REG hn (rto_of_SD (fun _ hx => hx.1) h)⟩

/-! ## The ledger (Examples 2 and 4, Definitions 2.5, 2.6, 2.9, Appendix A, Corollaries 5.2,
5.3) -/

/-- Ledger invocations: `append(r)` (records are natural numbers) and `get()`. -/
inductive LedOp | append (r : ℕ) | get
  deriving DecidableEq

/-- Ledger responses: `ack` (to an append) and `val l` (a get returning the list `l`). -/
inductive LedRes | ack | val (l : List ℕ)
  deriving DecidableEq

/-- The sequential ledger (state: the list of appended records). -/
def ledδ : List ℕ → LedOp → List ℕ × LedRes
  | s, .append r => (s ++ [r], .ack)
  | s, .get => (s, .val s)

/-- Sequential specification of the ledger, initially empty. -/
def ledSpec (n : ℕ) : SeqSpec (Fin n) Unit LedOp LedRes := fun _ => detSpec [] ledδ

/-- **Definition 2.6** (linearizable ledger). -/
def LIN_LED (n : ℕ) : Set (OWord n LedOp LedRes) := LinLang (ledSpec n)

/-- **Definition 2.5** (sequentially consistent ledger). -/
def SC_LED (n : ℕ) : Set (OWord n LedOp LedRes) := SCLang (ledSpec n)

/-- Property (2) of Example 4 for the prefix of length `k` of `x`: eventually, every `get`
returns a list that contains the record of every `append` invoked in the prefix. -/
def EventuallySees (x : OWord n LedOp LedRes) (k : ℕ) : Prop :=
  ∃ K, ∀ m, K ≤ m → ∀ l, (x m).2 = .inr (.val l) →
    ∀ j < k, ∀ r, (x j).2 = .inl (.append r) → r ∈ l

/-- **Definition 2.9** (eventually consistent ledger, Example 4): every finite prefix satisfies
property (1) (`PermConsistent`: some permutation of the completed operations, with no
process-order constraint, is a legal sequential ledger history) and property (2)
(`EventuallySees`). -/
def EC_LED (n : ℕ) : Set (OWord n LedOp LedRes) :=
  {x | WF x ∧ ∀ k, PermConsistent (ledSpec n) (histOf (pfx x k)) ∧ EventuallySees x k}

lemma mem_runSt_led (ops : ℕ → LedOp) {j r : ℕ} (hj : ops j = .append r) :
    ∀ i, j < i → r ∈ runSt [] ledδ ops i
  | 0, h => absurd h (Nat.not_lt_zero _)
  | i + 1, h => by
    simp only [runSt]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · have := mem_runSt_led ops hj i h
      cases ops i <;> simp [ledδ, this]
    · rw [hj]; simp [ledδ]

/-- Every sequential run of the ledger with a fair schedule is eventually consistent. -/
theorem runWord_mem_EC {sched : ℕ → Fin n} (hs : ∀ p N, ∃ i, N ≤ i ∧ sched i = p)
    (ops : ℕ → LedOp) : seqWord (runRec sched [] ledδ ops) ∈ EC_LED n := by
  refine ⟨wf_seqWord _ hs, fun k => ⟨?_, ?_⟩⟩
  · exact ⟨_, isExtension_pfx_seqWord _ k, _,
      legal_seqHist_detSpec.2 (runOK_recs_runRec sched [] ledδ ops _).1,
      fun p => ⟨_, restrictP_seqHist _ p, List.Perm.refl _⟩⟩
  · refine ⟨k, fun m hm l hl j hj r hr => ?_⟩
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [seqWord_even] at hl; simp at hl
    obtain ⟨i', rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [seqWord_even] at hr; rw [seqWord_odd] at hl
      simp only [runRec, Sum.inl.injEq, Sum.inr.injEq] at hl hr
      have hget : ops i = .get := by
        cases h : ops i with
        | append r' => rw [h] at hl; simp [ledδ] at hl
        | get => rfl
      rw [hget] at hl
      simp only [ledδ, LedRes.val.injEq] at hl
      have hii : i' < i := by
        rcases Nat.lt_or_ge i' i with h | h
        · exact h
        · have : i' = i := by omega
          subst this; rw [hget] at hr; cases hr
      rw [← hl]; exact mem_runSt_led ops hr i hii
    · rw [seqWord_odd] at hr; simp at hr

/-- Records appended by the first round of the Appendix A word: `pᵢ` appends `i + 1`. -/
def ledOps (n i : ℕ) : LedOp := if i % (n + 1) < n then .append (i % (n + 1) + 1) else .get

/-- Schedule of the Appendix A word: rounds of `n + 1` operations, the `i`-th operation of a
round (`i < n`) by `pᵢ`, the last one by `p_{n-1}`. -/
def ledSched (hn : 2 ≤ n) (i : ℕ) : Fin n :=
  if h : i % (n + 1) < n then ⟨i % (n + 1), h⟩ else ⟨n - 1, by omega⟩

/-- The word of Appendix A: in every round, `p₀, …, p_{n-1}` execute `append(1), …,
append(n)`, then `p_{n-1}` executes `get`, returning the list of all records appended so far. -/
def ledWord (hn : 2 ≤ n) : OWord n LedOp LedRes := seqWord (runRec (ledSched hn) [] ledδ (ledOps n))

lemma ledSched_fair (hn : 2 ≤ n) : ∀ p N, ∃ i, N ≤ i ∧ ledSched hn i = p := by
  intro p N
  have hp : ((n + 1) * N + p) % (n + 1) = p := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  refine ⟨(n + 1) * N + p, ?_, ?_⟩
  · have : N ≤ (n + 1) * N := Nat.le_mul_of_pos_left N (by omega)
    omega
  · simp only [ledSched, hp, p.2, dite_true]

theorem ledWord_mem_LIN (hn : 2 ≤ n) : ledWord hn ∈ LIN_LED n :=
  runWord_mem_linLang (ledSched_fair hn) [] ledδ (ledOps n)

theorem ledWord_mem_SC (hn : 2 ≤ n) : ledWord hn ∈ SC_LED n :=
  linLang_subset _ (ledWord_mem_LIN hn)

theorem ledWord_mem_EC (hn : 2 ≤ n) : ledWord hn ∈ EC_LED n :=
  runWord_mem_EC (ledSched_fair hn) (ledOps n)

lemma led_no_one : ∀ (M : List (OpRec (Fin n) Unit LedOp LedRes)) (s : List ℕ), 1 ∉ s →
    runOK ledδ s M → (∀ e ∈ M, e.o ≠ .append 1) → ∀ e ∈ M, ∀ l, e.r = .val l → 1 ∉ l
  | [], _, _, _, _, e, he, _, _ => by simp at he
  | e :: M, s, hs, hM, ho, e', he', l, hl => by
    rw [runOK_cons] at hM
    rcases List.mem_cons.1 he' with rfl | he'
    · cases h : e'.o with
      | append r => rw [h] at hM; simp only [ledδ] at hM; rw [← hM.1] at hl; cases hl
      | get => rw [h] at hM; simp only [ledδ] at hM; rw [← hM.1] at hl; cases hl; exact hs
    · refine led_no_one M _ ?_ hM.2 (fun e h => ho e (List.mem_cons_of_mem _ h)) e' he' l hl
      have := ho e List.mem_cons_self
      cases h : e.o with
      | append r =>
        rw [h] at this
        have : r ≠ 1 := fun h' => this (by rw [h'])
        simp [ledδ, hs, this.symm]
      | get => simpa [ledδ] using hs

/-- The prefix of the shuffled word of Appendix A: `p₁, …, p_{n-1}` append `2, …, n` and
`p_{n-1}`'s `get` returns a list containing `1`, which nobody appended. -/
lemma ledWord_not_rto {L : Set (OWord n LedOp LedRes)} (hn : 2 ≤ n) (hx : ledWord hn ∈ L)
    (hL : ∀ x ∈ L, ∀ k, Explained [] ledδ (histOf (pfx x k))) : ¬ RTO L := by
  set f := runRec (ledSched hn) [] ledδ (ledOps n) with hf
  have hfp : ∀ i, (f i).p = ledSched hn i := fun _ => rfl
  have hfo : ∀ i, (f i).o = ledOps n i := fun _ => rfl
  have h00 : ledSched hn 0 = ⟨0, by omega⟩ := by
    unfold ledSched
    split_ifs with h
    · exact Fin.ext (Nat.zero_mod _)
    · simp at h; omega
  refine not_rto_of hL hx (l := 2 * n) ?_ ?_ ?_
  · simp [ledWord, seqWord_fst]
  · intro m hm
    rw [ledWord, seqWord_fst, seqWord_fst, ← hf, hfp, hfp, h00]
    have hi : (2 + m) / 2 % (n + 1) = (2 + m) / 2 := Nat.mod_eq_of_lt (by omega)
    simp only [ledSched, hi]
    split_ifs <;> (simp only [ne_eq, Fin.ext_iff]; omega)
  · rintro ⟨M, hM, ha, hb⟩
    -- the `get` of the first round returns a list containing `1`
    have h1 : 1 ∈ runSt [] ledδ (ledOps n) n :=
      mem_runSt_led (ledOps n) (j := 0) (by simp [ledOps]; omega) n (by omega)
    have hgetn : ledOps n n = .get := by simp [ledOps]
    have hmem : Event.res (f n).p () (.val (runSt [] ledδ (ledOps n) n)) ∈
        histOf ((List.range (2 * n)).map fun m => ledWord hn (2 + m)) := by
      simp only [histOf, List.map_map, List.mem_map, List.mem_range, Function.comp_apply]
      refine ⟨2 * n - 1, by omega, ?_⟩
      rw [ledWord, evOf_seqWord, ← hf]
      have h2 : (2 + (2 * n - 1)) % 2 = 1 := by omega
      have h3 : (2 + (2 * n - 1)) / 2 = n := by omega
      simp only [h2, h3]
      simp [hf, runRec, hgetn, ledδ]
    obtain ⟨e, he, -, her⟩ := hb _ _ hmem
    refine led_no_one M [] (by simp) hM (fun e he => ?_) e he _ her h1
    obtain ⟨m, hm, hme⟩ := List.mem_map.1 (ha e he)
    obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hm
    rw [List.mem_range] at hm'
    simp only [ledWord, evOf_seqWord, ← hf] at hme
    split_ifs at hme with h2
    simp only [Event.inv.injEq] at hme
    rw [← hme.2.2, hfo]
    have hi : (2 + m) / 2 % (n + 1) = (2 + m) / 2 := Nat.mod_eq_of_lt (by omega)
    simp only [ledOps, hi]
    split_ifs
    · simp only [ne_eq, LedOp.append.injEq]; omega
    · simp

/-- **Appendix A**: `LIN_LED` is not real-time oblivious (`n ≥ 2`). -/
theorem not_rto_LIN_LED (hn : 2 ≤ n) : ¬ RTO (LIN_LED n) :=
  ledWord_not_rto hn (ledWord_mem_LIN hn)
    fun _ hx k => explained_of_seqConsistent (seqConsistent_of_linearizable (hx.2 k))

/-- **Appendix A**: `SC_LED` is not real-time oblivious (`n ≥ 2`). -/
theorem not_rto_SC_LED (hn : 2 ≤ n) : ¬ RTO (SC_LED n) :=
  ledWord_not_rto hn (ledWord_mem_SC hn) fun _ hx k => explained_of_seqConsistent (hx.2 k)

/-- **Appendix A**: `EC_LED` is not real-time oblivious (`n ≥ 2`). -/
theorem not_rto_EC_LED (hn : 2 ≤ n) : ¬ RTO (EC_LED n) :=
  ledWord_not_rto hn (ledWord_mem_EC hn) fun _ hx k => explained_of_permConsistent (hx.2 k).1

/-- **Corollary 5.2**: `LIN_LED, SC_LED, EC_LED ∉ SD` (`n ≥ 2`). -/
theorem cor_5_2 (hn : 2 ≤ n) : ¬ SD (LIN_LED n) ∧ ¬ SD (SC_LED n) ∧ ¬ SD (EC_LED n) :=
  ⟨fun h => not_rto_LIN_LED hn (rto_of_SD (fun _ hx => hx.1) h),
    fun h => not_rto_SC_LED hn (rto_of_SD (fun _ hx => hx.1) h),
    fun h => not_rto_EC_LED hn (rto_of_SD (fun _ hx => hx.1) h)⟩

/-- **Corollary 5.3**: `LIN_LED, SC_LED, EC_LED ∉ WD` (`n ≥ 2`). -/
theorem cor_5_3 (hn : 2 ≤ n) : ¬ WD (LIN_LED n) ∧ ¬ WD (SC_LED n) ∧ ¬ WD (EC_LED n) :=
  ⟨fun h => not_rto_LIN_LED hn (rto_of_WD (fun _ hx => hx.1) h),
    fun h => not_rto_SC_LED hn (rto_of_WD (fun _ hx => hx.1) h),
    fun h => not_rto_EC_LED hn (rto_of_WD (fun _ hx => hx.1) h)⟩

end Podc2025.LanguageDecidability.Objects
